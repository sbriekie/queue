import os, io, ssl, json, uuid, pytz, tempfile, threading, functools, secrets, re, imaplib
import pymysql  # TAMBAH: Import driver MySQL
from datetime import datetime, date, timedelta
from dateutil.relativedelta import relativedelta
from flask_cors import CORS
from flask_migrate import Migrate
from flask import (
    Flask, render_template, jsonify, request, Response,
    Blueprint, redirect, url_for, flash, session, g, 
    send_file, current_app, abort
)
from werkzeug.utils import secure_filename
from sqlalchemy import select, func, and_, or_, desc, text
from sqlalchemy.orm import joinedload, selectinload
from sqlalchemy.exc import OperationalError  # TAMBAH: Untuk error handling koneksi

from models import (
    db, Satker, User, Desk, KioskMenu, Ticket, Announcement, 
    Video, Chart, RowStatus, UserRole, TicketStatus, DeskService
)

pymysql.install_as_MySQLdb()  # TAMBAH: Agar SQLAlchemy mengenali PyMySQL sebagai MySQLdb

# ---------------------- CONFIG & GLOBALS ----------------------
IMAP_SERVER = 'mailhost.bps.go.id'
IMAP_PORT = 993
LOCAL_TZ = pytz.timezone('Asia/Makassar')
HEARTBEAT_TIMEOUT = 10          # Deteksi offline (10 detik)
GHOST_TIMEOUT = 60              # Auto-deactivate setelah 60 detik
CLEANUP_INTERVAL = 30           # Cek setiap 30 detik
_cleanup_thread = None
_cleanup_lock = threading.Lock()

BASE_DIR = os.path.abspath(os.path.dirname(__file__))
STATIC_DIR = os.path.join(BASE_DIR, "static")
INSTANCE_DIR = os.path.join(BASE_DIR, "instance")

# Hapus DB_PATH karena tidak lagi menggunakan SQLite
# DB_PATH = os.path.join(INSTANCE_DIR, "queue.db")

os.makedirs(STATIC_DIR, exist_ok=True)
os.makedirs(INSTANCE_DIR, exist_ok=True)

# Thread-safe locks untuk eliminasi race condition pada ticket creation
_ticket_locks = {}
_ticket_locks_lock = threading.Lock()

# Global heartbeat (thread-safe dict access sudah ditangani GIL Python)
DESK_HEARTBEAT = {}
LAST_REPLAY = {}

# ---------------------- APP INITIALIZATION ----------------------
app = Flask(__name__)
app.config["SECRET_KEY"] = os.getenv("FLASK_SECRET")
if not app.config["SECRET_KEY"]:
    raise RuntimeError("FLASK_SECRET environment variable must be set!")

# ======================= KONFIGURASI MYSQL =======================
# Baca dari Environment Variables (set di systemd service file atau /etc/environment)
DB_USER = os.getenv('DB_USER', 'queue')                 # Default: queue_user
DB_PASSWORD = os.getenv('DB_PASSWORD', 'P4ssw0rd!')     # WAJIB di-set di env
DB_HOST = os.getenv('DB_HOST', '10.75.0.20')             # Default: localhost
DB_PORT = os.getenv('DB_PORT', '3306')                  # Default: 3306
DB_NAME = os.getenv('DB_NAME', 'queue')                 # Default: queue_db

if not DB_PASSWORD:
    raise RuntimeError("DB_PASSWORD environment variable must be set!")

# Buat SQLAlchemy URI untuk MySQL dengan PyMySQL
# charset=utf8mb4 untuk support emoji dan karakter internasional
app.config["SQLALCHEMY_DATABASE_URI"] = (
    f"mysql+pymysql://{DB_USER}:{DB_PASSWORD}@{DB_HOST}:{DB_PORT}/{DB_NAME}"
    f"?charset=utf8mb4&binary_prefix=true"
)

# Konfigurasi Connection Pooling untuk stabilitas MySQL
# pool_pre_ping: Cek koneksi sebelum dipakai (menghindari "MySQL server has gone away")
# pool_recycle: Recycle koneksi setelah 1 jam (MySQL timeout default biasanya 8 jam)
app.config["SQLALCHEMY_ENGINE_OPTIONS"] = {
    "pool_pre_ping": True,
    "pool_recycle": 3600,
    "pool_size": 10,
    "max_overflow": 20,
}

app.config["SQLALCHEMY_TRACK_MODIFICATIONS"] = False
migrate = Migrate(app, db)
db.init_app(app)

CORS(app, resources={r"/api/*": {"origins": "*", "methods": ["GET", "POST", "OPTIONS"]}})

# ---------------------- HELPER FUNCTIONS ----------------------

def get_local_now():
    """Get current time in local timezone (WITA)"""
    return datetime.now(LOCAL_TZ)

def get_local_today():
    return get_local_now().date()

def get_current_session_start():
    """Get session start time (07:30 WITA)"""
    now = get_local_now()
    today = get_local_today()
    reset_time = datetime.combine(today, datetime.strptime("07:30", "%H:%M").time())
    reset_local = LOCAL_TZ.localize(reset_time)
    
    if now < reset_local:
        yesterday = today - timedelta(days=1)
        yesterday_reset = datetime.combine(yesterday, datetime.strptime("07:30", "%H:%M").time())
        return LOCAL_TZ.localize(yesterday_reset)
    return reset_local

def to_utc(dt):
    """Convert naive/aware datetime to UTC untuk query DB.
    Jika naive, diasumsikan sebagai WITA (Local)."""
    if dt is None:
        return None
    if dt.tzinfo is None:
        dt = LOCAL_TZ.localize(dt)
    return dt.astimezone(pytz.UTC)

def to_local(dt):
    """Convert UTC datetime to local timezone untuk display.
    Jika naive, diasumsikan sebagai UTC (karena data DB adalah UTC)."""
    if dt is None:
        return None
    if dt.tzinfo is None:
        # Data dari database adalah UTC naive
        dt = pytz.UTC.localize(dt)
    return dt.astimezone(LOCAL_TZ)

def is_super_admin(user=None):
    user = user or g.user
    if not user:
        return False
    return user.role == UserRole.superadmin

def get_satker_scope():
    if not g.user:
        return (request.headers.get("X-Kode-Satker") or "7500", False)
    
    if is_super_admin():
        selected = request.args.get('satker') or request.form.get('kode_satker') or g.user.kode_satker
        return (selected, True)
    else:
        return (g.user.kode_satker, False)

def active_query(model):
    """
    Generate base query dengan soft-delete filter.
    Usage: db.session.execute(active_query(Model).where(...))
    """
    return select(model).where(model.status != RowStatus.DELETED)

def get_ticket_lock(satker_code):
    """Get thread lock untuk satker tertentu (race condition prevention)"""
    with _ticket_locks_lock:
        if satker_code not in _ticket_locks:
            _ticket_locks[satker_code] = threading.Lock()
        return _ticket_locks[satker_code]

def format_duration(seconds):
    """Format detik ke readable string"""
    if seconds is None or seconds < 0:
        return "-"
    h = int(seconds // 3600)
    m = int((seconds % 3600) // 60)
    s = int(seconds % 60)
    if h > 0:
        return f"{h}j {m}m {s}d"
    if m > 0:
        return f"{m}m {s}d"
    return f"{s}d"

def imap_auth(email, pwd):
    """Autentikasi IMAP dengan timeout dan error handling"""
    try:
        ctx = ssl.create_default_context()
        ctx.set_ciphers('HIGH:!DH:!aNULL')
        with imaplib.IMAP4_SSL(IMAP_SERVER, IMAP_PORT, ssl_context=ctx, timeout=10) as M:
            M.login(email, pwd)
            return True
    except Exception:
        return False

def _tts_io(text: str) -> str:
    """Generate TTS audio file - FIXED"""
    tmp_fd, tmp_path = tempfile.mkstemp(suffix='.mp3', prefix='tts_', dir=STATIC_DIR)
    os.close(tmp_fd)
    
    try:
        # Import edge_tts di dalam fungsi untuk memastikan scope
        import edge_tts as et
        import asyncio
        
        async def _gen():
            try:
                communicate = et.Communicate(text, voice="id-ID-ArdiNeural")
                await communicate.save(tmp_path)
            except Exception as e:
                current_app.logger.error(f"Edge-TTS generation error: {e}")
                raise
        
        # Gunakan asyncio.run dengan error handling yang lebih baik
        try:
            asyncio.run(_gen())
        except RuntimeError as e:
            # Handle "event loop is already running" jika terjadi
            if "already running" in str(e):
                import nest_asyncio
                nest_asyncio.apply()
                asyncio.run(_gen())
            else:
                raise
        
        # Verifikasi file terbuat
        if not os.path.exists(tmp_path) or os.path.getsize(tmp_path) == 0:
            raise RuntimeError("TTS file generation failed or empty")
            
        return tmp_path
        
    except Exception as e:
        # Cleanup file temporary jika error
        if os.path.exists(tmp_path):
            try:
                os.remove(tmp_path)
            except:
                pass
        current_app.logger.error(f"TTS Error: {str(e)}")
        raise RuntimeError(f"Gagal generate audio: {str(e)}")

# ---------------------- CONTEXT PROCESSORS ----------------------

@app.before_request
def before_request():
    # Load user jika ada
    g.user = None
    if session.get("user_id"):
        stmt = active_query(User).where(User.id == session["user_id"])
        g.user = db.session.execute(stmt).scalar_one_or_none()
    
    # PERBAIKAN: Handle dual session mode
    if g.user:
        # Mode Admin: ambil dari user
        g.kode_satker = session.get("kode_satker", g.user.kode_satker)
        g.is_super = session.get("is_super", False)
    elif session.get('desk_id'):
        # Mode Desk Client: ambil dari session desk
        g.kode_satker = session.get('kode_satker')
        g.is_super = False
        g.desk_id = session.get('desk_id')
    else:
        # Mode Anonymous/Public
        g.kode_satker = request.headers.get("X-Kode-Satker") or "7500"
        g.is_super = False
    
    g.local_now = get_local_now
    g.local_today = get_local_today
    
@app.context_processor
def inject_globals():
    return {
        'local_now': get_local_now(),
        'local_today': get_local_today(),
        'session_start': get_current_session_start(),
        'is_super': lambda: is_super_admin()
    }

# ---------------------- DECORATORS ----------------------

def login_required(f):
    @functools.wraps(f)
    def decorated(*args, **kwargs):
        if g.user is None:
            return redirect(url_for("login", next=request.path))
        return f(*args, **kwargs)
    return decorated

def admin_required(f):
    @functools.wraps(f)
    def decorated(*args, **kwargs):
        if not g.user:
            flash("Silakan login terlebih dahulu", "danger")
            return redirect(url_for("login", next=request.path))  
        if g.user.role not in (UserRole.admin, UserRole.superadmin):
            flash("Akses ditolak. Hanya admin yang bisa mengakses.", "danger")
            return redirect(url_for("admin.dashboard"))
        return f(*args, **kwargs)
    return decorated

def superadmin_required(f):
    """Decorator khusus untuk superadmin only operations"""
    @functools.wraps(f)
    def decorated(*args, **kwargs):
        if not g.user or not is_super_admin():
            flash("Akses ditolak. Hanya superadmin.", "danger")
            return redirect(url_for("admin.dashboard"))
        return f(*args, **kwargs)
    return decorated

def csrf_check(f):
    """CSRF Protection untuk state-changing methods"""
    @functools.wraps(f)
    def decorated(*args, **kwargs):
        if request.method in ["POST", "PUT", "DELETE", "PATCH"]:
            token = session.get('csrf_token')
            req_token = request.form.get('csrf_token') or request.headers.get('X-CSRF-Token')
            if not token or token != req_token:
                flash("CSRF token mismatch", "danger")
                return redirect(request.referrer or url_for("admin.dashboard"))
        return f(*args, **kwargs)
    return decorated

def desk_client_required(f):
    """
    Decorator khusus untuk desk client.
    Membolehkan akses dari session desk yang valid, 
    atau dari session admin yang meng-assign desk.
    """
    @functools.wraps(f)
    def decorated(*args, **kwargs):
        # Cek apakah ini request dari desk client (punya desk_id)
        desk_id = session.get('desk_id')
        
        # Jika tidak ada desk_id di session, cek apakah ada di header (untuk API)
        if not desk_id and request.headers.get('X-Desk-ID'):
            try:
                desk_id = int(request.headers.get('X-Desk-ID'))
                session['desk_id'] = desk_id
            except (ValueError, TypeError):
                pass
        
        if not desk_id:
            # Untuk API, return 401 JSON
            if request.is_json or request.path.startswith('/api/'):
                return jsonify({"error": "No desk assigned", "code": "DESK_REQUIRED"}), 401
            # Untuk web, redirect ke pemilihan desk
            flash("Silakan pilih meja terlebih dahulu", "warning")
            return redirect(url_for("desk_select_page"))
        
        # Validasi desk masih aktif dan valid
        desk = db.session.get(Desk, desk_id)
        if not desk or desk.status == RowStatus.DELETED:
            session.pop('desk_id', None)
            session.pop('desk_name', None)
            if request.is_json or request.path.startswith('/api/'):
                return jsonify({"error": "Desk not found", "code": "DESK_INVALID"}), 404
            flash("Meja tidak valid, silakan pilih ulang", "danger")
            return redirect(url_for("desk_select_page"))
        
        # Set g.desk untuk akses mudah
        g.desk = desk
        g.desk_id = desk_id
        
        return f(*args, **kwargs)
    return decorated

def api_auth_or_desk(f):
    """
    Decorator untuk API yang bisa diakses oleh:
    1. User yang sudah login (admin/desk), atau
    2. Desk client dengan token/heartbeat valid
    """
    @functools.wraps(f)
    def decorated(*args, **kwargs):
        # Cek session user normal
        if g.user:
            return f(*args, **kwargs)
        
        # Cek session desk client
        if session.get('desk_id'):
            g.desk_id = session.get('desk_id')
            return f(*args, **kwargs)
        
        # Cek API key/token jika ada (untuk future enhancement)
        api_key = request.headers.get('X-API-Key')
        if api_key:
            # Validasi API key di sini jika diimplementasikan
            pass
        
        # Unauthorized
        return jsonify({
            "error": "Unauthorized",
            "message": "Session expired or invalid",
            "code": "SESSION_EXPIRED"
        }), 401
    return decorated

# ---------------------- ROUTES: AUTH ----------------------

@app.route("/", methods=["GET", "POST"])
def login():
    from datetime import datetime
    
    # Debug: Log session state
    current_app.logger.info(f"Login accessed. Method: {request.method}, Session: {dict(session)}")
    
    if request.method == "GET":
        # Clear session tapi pertahankan csrf_token dan intended URL
        old_csrf = session.get('csrf_token')
        next_url = request.args.get('next')
        
        session.clear()
        session['csrf_token'] = old_csrf or os.urandom(32).hex()
        
        if next_url:
            session['next_url'] = next_url
            current_app.logger.info(f"GET login - Intended destination: {next_url}")
        
        current_app.logger.info(f"GET login - CSRF token set: {session['csrf_token'][:8]}...")
        
        return render_template("login.html", 
                               step="username",
                               csrf_token=session['csrf_token'])

    # POST handling
    step = request.form.get("step", "username")
    form_csrf = request.form.get('csrf_token')
    session_csrf = session.get('csrf_token')
    
    current_app.logger.info(f"POST login - Step: {step}")
    
    # STEP 1: USERNAME
    if step == "username":
        username = request.form.get("username", "").strip()
        current_app.logger.info(f"Step username - Input: {username}")
        
        if not username:
            flash("Username wajib diisi", "danger")
            return redirect(url_for("login"))
        
        try:
            stmt = select(User).where(
                User.username == username,
                User.status != RowStatus.DELETED
            )
            user = db.session.execute(stmt).scalar_one_or_none()
            current_app.logger.info(f"User lookup result: {user}")
        except Exception as e:
            current_app.logger.error(f"Error looking up user: {e}")
            flash("Terjadi kesalahan sistem", "danger")
            return redirect(url_for("login"))
        
        if not user:
            flash("Username tidak terdaftar", "danger")
            return redirect(url_for("login"))
        
        session["tmp_user_id"] = user.id
        session.modified = True
        
        current_app.logger.info(f"User validated, proceeding to password step")
        
        return render_template("login.html", 
                               step="password",
                               csrf_token=session['csrf_token'])

    # STEP 2: PASSWORD
    elif step == "password":
        if not form_csrf or form_csrf != session_csrf:
            current_app.logger.error(f"CSRF mismatch!")
            flash("Session tidak valid, silakan ulangi dari awal", "danger")
            session.clear()
            return redirect(url_for("login"))
        
        tmp_user_id = session.pop("tmp_user_id", None)
        password = request.form.get("password", "")
        next_url = session.pop('next_url', None)
        
        current_app.logger.info(f"Step password - tmp_user_id: {tmp_user_id}, next_url: {next_url}")
        
        if not tmp_user_id:
            flash("Sesi habis, silakan login ulang", "danger")
            return redirect(url_for("login"))
        
        if not password:
            flash("Password wajib diisi", "danger")
            return redirect(url_for("login"))
        
        try:
            stmt = select(User).where(
                User.id == tmp_user_id,
                User.status != RowStatus.DELETED
            )
            user = db.session.execute(stmt).scalar_one_or_none()
        except Exception as e:
            current_app.logger.error(f"Error loading user for password check: {e}")
            flash("Terjadi kesalahan sistem", "danger")
            return redirect(url_for("login"))
        
        if not user:
            flash("User tidak ditemukan", "danger")
            return redirect(url_for("login"))
        
        # Verifikasi password via IMAP
        try:
            auth_result = imap_auth(user.username, password)
            current_app.logger.info(f"IMAP auth result: {auth_result}")
        except Exception as e:
            current_app.logger.error(f"IMAP auth error: {e}")
            auth_result = False
        
        if not auth_result:
            flash("Password salah", "danger")
            return redirect(url_for("login"))
        
        # SET SESSION LOGIN
        try:
            session["user_id"] = user.id
            session["kode_satker"] = user.kode_satker
            session["is_super"] = (user.role == UserRole.superadmin)
            session.modified = True
            
            current_app.logger.info(f"Session set for user {user.id}, satker {user.kode_satker}")
        except Exception as e:
            current_app.logger.error(f"Error setting session: {e}")
            flash("Gagal menyimpan sesi login", "danger")
            return redirect(url_for("login"))
        
        # UPDATE LAST LOGIN
        try:
            user.last_login = datetime.now(pytz.UTC)
            user.updated_at = datetime.now(pytz.UTC)
            db.session.commit()
            current_app.logger.info(f"Last login updated for user {user.username}: {user.last_login}")
        except Exception as e:
            db.session.rollback()
            current_app.logger.error(f"Failed to update last_login for user {user.id}: {e}")
        
        # LOGIC REDIRECT
        current_app.logger.info(f"Redirecting. Role: {user.role.value}, Next: {next_url}")
        
        try:
            if next_url:
                if next_url.startswith('/'):
                    next_path = next_url
                else:
                    next_path = '/' + next_url
                
                if '/desk' in next_path:
                    if user.role in (UserRole.superadmin, UserRole.admin, UserRole.operator):
                        return redirect(url_for("desk_client_page"))
                    else:
                        flash("Anda tidak memiliki akses ke Desk Client", "warning")
                        return redirect(url_for("admin.dashboard"))
                
                elif '/kiosk' in next_path:
                    return redirect(url_for("kiosk_page"))
                
                elif '/display' in next_path:
                    return redirect(url_for("display_page", kode_satker=user.kode_satker))
                
                elif '/admin' in next_path and user.role in (UserRole.operator, UserRole.viewer):
                    flash("Anda tidak memiliki akses ke Dashboard", "warning")
                    return redirect(url_for("desk_client_page"))
            
            # DEFAULT REDIRECT
            if user.role == UserRole.superadmin or user.role == UserRole.admin:
                return redirect(url_for("admin.dashboard"))
            elif user.role == UserRole.operator:
                return redirect(url_for("desk_client_page"))
            else:
                return redirect(url_for("display_page", kode_satker=user.kode_satker))
                
        except Exception as e:
            current_app.logger.error(f"Error during redirect: {e}")
            return redirect(url_for("admin.dashboard"))
    
    else:
        current_app.logger.warning(f"Unknown step: {step}")
        flash("Langkah tidak valid", "danger")
        return redirect(url_for("login"))
    
# ---------------------- ROUTE2 UTAMA -------------------------------------------------------------

@app.route("/display/<kode_satker>")
def display_page(kode_satker):
    """Display dengan URL simpel: /display/7500"""
    satker = db.session.get(Satker, kode_satker)
    if not satker:
        return f"Satker dengan kode {kode_satker} tidak ditemukan", 404
    
    return render_template("display.html", 
                          kode_satker=kode_satker,
                          satker_nama=satker.nama)


@app.route("/desk")
@login_required
def desk_client_page():
    """
    Halaman desk client - otomatis redirect ke sini jika akses /desk
    """
    desk_id = session.get('desk_id')
    
    if desk_id:
        desk = db.session.get(Desk, desk_id)
        if desk and desk.status != RowStatus.DELETED:
            return render_template("desk_client.html", 
                                 desk_id=desk_id,
                                 desk_name=session.get('desk_name', desk.name),
                                 kode_satker=g.kode_satker,
                                 mode="operating")
        session.pop('desk_id', None)
        session.pop('desk_name', None)
    
    # Mode 2: Belum assign, tampilkan pemilihan meja
    stmt = select(Desk).where(
        Desk.kode_satker == g.kode_satker,
        Desk.status == RowStatus.ACTIVE
    ).order_by(Desk.id)
    
    desks = db.session.execute(stmt).scalars().all()
    
    return render_template("desk_client.html",
                         desks=desks,
                         kode_satker=g.kode_satker,
                         mode="select",
                         desk_id=None,
                         desk_name=None)


@app.route("/kiosk")
@login_required
def kiosk_page():
    """Kiosk menu - otomatis redirect ke sini jika akses /kiosk"""
    stmt = active_query(KioskMenu).where(
        KioskMenu.is_active == True,
        KioskMenu.kode_satker == g.kode_satker
    ).order_by(KioskMenu.prefix)
    
    services = db.session.execute(stmt).scalars().all()
    return render_template("kiosk.html", 
                           services=services, 
                           csrf_token=session.get('csrf_token'))

# ---------------------- API'S: ALL -------------------------------------------------------------
# ---------------------- API: DISPLAY ----------------------

@app.route("/api/display/<kode_satker>")
def api_display(kode_satker):
    """API Display dengan path parameter"""
    satker = db.session.get(Satker, kode_satker)
    if not satker:
        return jsonify({"error": "Satker tidak ditemukan"}), 404
    
    now_local = get_local_now()
    now_utc = to_utc(now_local)
  
    stmt = active_query(Announcement).where(
        Announcement.kode_satker == kode_satker
    ).order_by(desc(Announcement.created_at))
    ann = db.session.execute(stmt.limit(1)).scalar_one_or_none()
    ticker = ann.text if ann else f"Selamat Datang di {satker.nama}"
    
    stmt = active_query(Video).where(
        Video.kode_satker == kode_satker
    ).order_by(desc(Video.created_at))
    video = db.session.execute(stmt.limit(1)).scalar_one_or_none()
    video_url = video.filename if video else None
    
    stmt = select(Desk).where(
        Desk.kode_satker == kode_satker,
        Desk.status == RowStatus.ACTIVE,
        Desk.is_active == True
    ).order_by(Desk.id)
    
    all_desks = db.session.execute(stmt).scalars().all()
    
    desk_status_list = []
    
    for desk in all_desks:
        is_online = False
        last_seen = None
        
        if desk.id in DESK_HEARTBEAT:
            hb_data = DESK_HEARTBEAT[desk.id]
            time_diff = (now_utc - hb_data["last_seen"]).total_seconds()
            if time_diff <= HEARTBEAT_TIMEOUT:
                is_online = True
                last_seen = hb_data["last_seen"]
        
        current_ticket = db.session.execute(
            active_query(Ticket).where(
                Ticket.desk_id == desk.id,
                Ticket.ticket_status == TicketStatus.SERVING,
                Ticket.status == RowStatus.ACTIVE
            )
        ).scalar_one_or_none()
        
        desk_status_list.append({
            "id": desk.id,
            "name": desk.name,
            "is_active": desk.is_active,
            "is_online": is_online,
            "now_serving": current_ticket.number if current_ticket else None,
            "last_seen": last_seen.isoformat() if last_seen else None,
            "kode_satker": desk.kode_satker
        })
    
    today_srv = db.session.execute(
        active_query(Ticket).where(
            Ticket.ticket_status == TicketStatus.SERVING,
            Ticket.is_skipped == False,
            Ticket.kode_satker == kode_satker
        ).order_by(desc(Ticket.called_at)).limit(1)
    ).scalar_one_or_none()
    
    session_start = get_current_session_start()
    session_start_utc = to_utc(session_start)
    
    stmt = active_query(KioskMenu).where(
        KioskMenu.is_active == True,
        KioskMenu.kode_satker == kode_satker
    ).order_by(KioskMenu.prefix)
    
    services = []
    for svc in db.session.execute(stmt).scalars():
        last_done = db.session.execute(
            active_query(Ticket).where(
                Ticket.service_id == svc.id,
                Ticket.ticket_status == TicketStatus.DONE,
                Ticket.is_skipped == False,
                Ticket.kode_satker == kode_satker,
                Ticket.called_at >= session_start_utc
            ).order_by(desc(Ticket.called_at)).limit(1)
        ).scalar_one_or_none()
        
        services.append({
            "service_name": svc.name,
            "last_ticket": last_done.number if last_done else "-",
            "last_desk": last_done.desk.name if (last_done and last_done.desk) else "-"
        })
    
    return jsonify({
        "ticker": ticker,
        "video_url": video_url,
        "now_serving": today_srv.number if today_srv else None,
        "desk_status": desk_status_list,
        "services": services,
        "server_time": now_local.strftime('%Y-%m-%d %H:%M:%S'),
        "timezone": "Asia/Makassar (WITA)",
        "kode_satker": kode_satker,
        "satker_nama": satker.nama
    })

_heartbeat_lock = threading.Lock()

def get_active_desks_from_heartbeat(kode_satker=None):
    """Get active desks dengan filter satker"""
    now = datetime.now(pytz.UTC)
    active = []
    
    for desk_id, data in list(DESK_HEARTBEAT.items()):
        if (now - data["last_seen"]).total_seconds() <= HEARTBEAT_TIMEOUT:
            desk = db.session.get(Desk, desk_id)
            if desk and desk.status != RowStatus.DELETED:
                if not kode_satker or desk.kode_satker == kode_satker:
                    current = db.session.execute(
                        active_query(Ticket).where(
                            Ticket.desk_id == desk.id,
                            Ticket.status == 'serving'
                        )
                    ).scalar_one_or_none()
                    
                    active.append({
                        "id": desk.id,
                        "name": desk.name,
                        "is_active": True,
                        "now_serving": current.number if current else "---",
                        "kode_satker": desk.kode_satker
                    })
    return active

# ---------------------- API: CHARTS FOR DISPLAY ----------------------
@app.route("/api/charts/<kode_satker>")
def api_list_charts(kode_satker):
    """List charts untuk satker tertentu: /api/charts/7500"""
    charts = db.session.execute(
        select(Chart.slug, Chart.judul)
        .where(
            Chart.kode_satker == kode_satker,
            Chart.is_deleted == False,           # Filter soft-delete
            Chart.status == RowStatus.ACTIVE     # Pastikan status aktif
        )
        .order_by(Chart.urutan, Chart.created_at)  # Urutkan berdasarkan urutan dulu
    ).all()
    
    return jsonify({
        "success": True,
        "charts": [{"slug": c.slug, "judul": c.judul} for c in charts]
    })

@app.route("/api/charts/<kode_satker>/<slug>")
def api_chart_data(kode_satker, slug):
    """Get chart data: /api/charts/7500/kemiskinan-gorontalo"""
    
    # Gunakan query_active() dari BaseModel atau filter manual
    chart = Chart.query_active().filter_by(
        kode_satker=kode_satker,
        slug=slug,
        status=RowStatus.ACTIVE
    ).first()
    
    if not chart:
        return jsonify({
            "success": False,
            "error": "Chart not found",
            "message": f"Chart {slug} untuk satker {kode_satker} tidak ditemukan."
        }), 404
    
    return jsonify({
        "success": True,
        "slug": chart.slug,
        "judul": chart.judul,
        "tipe_chart": chart.tipe_chart,
        "data_json": chart.data_json,
        "opsi_animasi": chart.opsi_animasi or {"duration": 2000, "easing": "easeOutQuart"},
        "refresh_detik": chart.refresh_detik
    })

# ---------------------- API: ROTATION (VIDEO & TICKER) ----------------------

@app.route("/api/tickers/<kode_satker>")
def api_tickers_rotation(kode_satker):
    satker = db.session.get(Satker, kode_satker)
    if not satker:
        return jsonify({"error": "Satker tidak ditemukan"}), 404

    stmt = db.select(Announcement).where(
        Announcement.kode_satker == kode_satker,
        Announcement.is_deleted == False
    ).order_by(Announcement.created_at)

    announcements = db.session.execute(stmt).scalars().all()

    if not announcements:
        return jsonify({
            "success": True,
            "kode_satker": kode_satker,
            "count": 1,
            "tickers": [f"Selamat Datang di {satker.nama}"]
        })

    return jsonify({
        "success": True,
        "kode_satker": kode_satker,
        "count": len(announcements),
        "tickers": [ann.text for ann in announcements]
    })

@app.route("/api/videos/<kode_satker>")
def api_videos_rotation(kode_satker):
    satker = db.session.get(Satker, kode_satker)
    if not satker:
        return jsonify({"error": "Satker tidak ditemukan"}), 404

    stmt = db.select(Video).where(
        Video.kode_satker == kode_satker,
        Video.is_deleted == False
    ).order_by(Video.created_at)

    videos = db.session.execute(stmt).scalars().all()

    if not videos:
        return jsonify({
            "success": True,
            "kode_satker": kode_satker,
            "count": 0,
            "videos": []
        })

    return jsonify({
        "success": True,
        "kode_satker": kode_satker,
        "count": len(videos),
        "videos": [
            {
                "id": vid.id,
                "filename": vid.filename,
                "title": getattr(vid, 'title', None)
                         or getattr(vid, 'name', f"Video {i+1}"),
                "created_at": vid.created_at.isoformat() if vid.created_at else None
            }
            for i, vid in enumerate(videos)
        ]
    })

# ---------------------- API: DESK-CLIENT -------------------------------------------------------

@app.route("/api/desks")
@api_auth_or_desk
def api_desks():
    """Return available desks dengan info layanan yang bisa dilayani"""
    try:
        kode_satker = g.kode_satker if g.user else session.get('kode_satker')
        if not kode_satker:
            return jsonify({"error": "No satker context"}), 400
        
        stmt = select(Desk).where(
            Desk.kode_satker == kode_satker,
            Desk.status == RowStatus.ACTIVE
        ).order_by(Desk.id)
        
        desks = db.session.execute(stmt).scalars().all()
        
        result = []
        for d in desks:
            services = [{
                "id": s.id,
                "name": s.name,
                "prefix": s.prefix
            } for s in d.allowed_services]
            
            is_occupied = False
            current_user = None
            if d.id in DESK_HEARTBEAT:
                last_seen = DESK_HEARTBEAT[d.id]["last_seen"]
                if (datetime.now(pytz.UTC) - last_seen).total_seconds() < 30:
                    is_occupied = True
                    current_user = DESK_HEARTBEAT[d.id].get("user")
            
            result.append({
                "id": d.id, 
                "name": d.name, 
                "is_active": d.is_active,
                "is_dedicated": d.is_dedicated,
                "services": services if d.is_dedicated else "all",
                "is_occupied": is_occupied,
                "current_user": current_user
            })
        
        return jsonify(result)
    
    except Exception as e:
        current_app.logger.error(f"Error in api_desks: {str(e)}")
        return jsonify({"error": "Failed to load desks"}), 500

@app.route('/api/desk/heartbeat', methods=['POST'])
@api_auth_or_desk
def desk_heartbeat():
    """Receive heartbeat dari desk client - MOVED TO APP LEVEL"""
    data = request.get_json() or {}
    desk_id = data.get('desk_id')
    
    if not desk_id:
        return jsonify({"success": False, "error": "desk_id required"}), 400
    
    try:
        desk_id = int(desk_id)
    except (ValueError, TypeError):
        return jsonify({"success": False, "error": "Invalid desk_id"}), 400
    
    # Update heartbeat timestamp
    DESK_HEARTBEAT[desk_id] = {
        "last_seen": datetime.utcnow(),
        "ip": request.remote_addr
    }
    
    return jsonify({
        "success": True,
        "timestamp": datetime.utcnow().isoformat()
    })

@app.route("/api/desk/assign", methods=["POST"])
@api_auth_or_desk
def api_desk_assign():
    """Assign desk to current user session"""
    try:
        data = request.get_json(silent=True) or {}
        desk_id = data.get("desk_id")
        
        if not desk_id:
            return jsonify({"error": "desk_id required"}), 400
        
        try:
            desk_id = int(desk_id)
        except (ValueError, TypeError):
            return jsonify({"error": "Invalid desk_id"}), 400
        
        kode_satker = g.kode_satker if g.user else session.get('kode_satker')
        if not kode_satker:
            return jsonify({"error": "No satker context"}), 400
        
        stmt = select(Desk).where(
            Desk.id == desk_id,
            Desk.kode_satker == kode_satker,
            Desk.status == RowStatus.ACTIVE
        )
        desk = db.session.execute(stmt).scalar_one_or_none()
        
        if not desk:
            return jsonify({"error": "Desk not found"}), 404
        
        if desk_id in DESK_HEARTBEAT:
            last_seen = DESK_HEARTBEAT[desk_id]["last_seen"]
            if (datetime.now(pytz.UTC) - last_seen).total_seconds() < 30:
                current_user = DESK_HEARTBEAT[desk_id].get("user")
                request_user = g.user.username if g.user else session.get('desk_user')
                if current_user != request_user:
                    return jsonify({"error": "Desk is currently occupied"}), 409
        
        desk.is_active = True
        desk.updated_by = g.user.username if g.user else "desk_client"
        desk.last_activity = datetime.now(pytz.UTC)
        db.session.commit()
        
        session['desk_id'] = desk_id
        session['desk_name'] = desk.name
        session['desk_paused'] = False
        session['kode_satker'] = kode_satker
        session['desk_assigned_at'] = datetime.now(pytz.UTC).isoformat()
        session['desk_user'] = g.user.username if g.user else f"desk_{desk_id}"
        
        if g.user:
            session['desk_assigned_by'] = g.user.id
        
        DESK_HEARTBEAT[desk_id] = {
            "user": session['desk_user'],
            "last_seen": datetime.now(pytz.UTC)
        }
        
        return jsonify({
            "success": True,
            "desk_id": desk_id,
            "desk_name": desk.name,
            "is_active": True,
            "session_mode": "admin" if g.user else "standalone"
        })
        
    except Exception as e:
        db.session.rollback()
        current_app.logger.error(f"Error in api_desk_assign: {str(e)}")
        return jsonify({"error": "Internal server error"}), 500

@app.route("/api/desk/release", methods=["POST"])
@desk_client_required
def api_desk_release():
    """Release desk dari session"""
    try:
        desk_id = session.get('desk_id')
        
        curr = db.session.execute(
            select(Ticket).where(
                Ticket.desk_id == desk_id,
                Ticket.ticket_status == TicketStatus.SERVING,
                Ticket.status == RowStatus.ACTIVE
            )
        ).scalar_one_or_none()
        
        if curr:
            curr.mark_completed()
            curr.updated_by = session.get('desk_user', 'system')
        
        desk = db.session.get(Desk, desk_id)
        if desk:
            desk.is_active = False
            desk.updated_by = session.get('desk_user', 'system')
        
        DESK_HEARTBEAT.pop(desk_id, None)
        
        desk_keys = ['desk_id', 'desk_name', 'desk_paused', 'desk_assigned_at', 
                     'desk_user', 'desk_assigned_by']
        for key in desk_keys:
            session.pop(key, None)
        
        db.session.commit()
        
        return jsonify({
            "success": True,
            "message": "Desk released successfully"
        })
        
    except Exception as e:
        db.session.rollback()
        current_app.logger.error(f"Error in api_desk_release: {str(e)}")
        return jsonify({"error": "Internal server error"}), 500

@app.route("/api/desk/status/<int:desk_id>", methods=["POST"])
@desk_client_required
def api_desk_status(desk_id):
    """Pause/Resume desk"""
    try:
        if session.get('desk_id') != desk_id:
            return jsonify({"error": "Not your assigned desk"}), 403
        
        kode_satker = g.kode_satker if g.user else session.get('kode_satker')
        
        stmt = select(Desk).where(
            Desk.id == desk_id,
            Desk.kode_satker == kode_satker
        )
        desk = db.session.execute(stmt).scalar_one_or_none()
        
        if not desk:
            return jsonify({"error": "Desk not found"}), 404
        
        data = request.get_json(silent=True) or {}
        paused = data.get("paused", False)
        
        if paused:
            curr = db.session.execute(
                select(Ticket).where(
                    Ticket.desk_id == desk.id,
                    Ticket.ticket_status == TicketStatus.SERVING,
                    Ticket.status == RowStatus.ACTIVE
                )
            ).scalar_one_or_none()
            
            if curr:
                curr.mark_completed()
                curr.updated_by = session.get('desk_user', 'system')
            
            desk.is_active = False
            session['desk_paused'] = True
            DESK_HEARTBEAT.pop(desk_id, None)
            status_msg = "paused"
        else:
            desk.is_active = True
            desk.last_activity = datetime.now(pytz.UTC)
            session['desk_paused'] = False
            DESK_HEARTBEAT[desk_id] = {
                "user": session.get('desk_user', 'system'),
                "last_seen": datetime.now(pytz.UTC)
            }
            status_msg = "active"
        
        desk.updated_by = session.get('desk_user', 'system')
        db.session.commit()
        
        return jsonify({
            "success": True, 
            "desk_id": desk_id, 
            "is_active": desk.is_active, 
            "status": status_msg
        })
        
    except Exception as e:
        db.session.rollback()
        current_app.logger.error(f"Error in api_desk_status: {str(e)}")
        return jsonify({"error": "Internal server error"}), 500

@app.route("/api/desk/next/<int:desk_id>", methods=["POST"])
@desk_client_required
def api_desk_next(desk_id):
    """Complete current and call next"""
    global LAST_REPLAY
    
    try:
        if session.get('desk_id') != desk_id:
            return jsonify({"error": "Not your assigned desk"}), 403
        
        if session.get('desk_paused'):
            return jsonify({"error": "Desk is paused"}), 400
        
        kode_satker = g.kode_satker if g.user else session.get('kode_satker')
        
        desk = db.session.get(Desk, desk_id)
        if not desk or desk.kode_satker != kode_satker:
            return jsonify({"error": "Desk not found"}), 404
        
        desk.last_activity = datetime.now(pytz.UTC)
        if desk_id in DESK_HEARTBEAT:
            DESK_HEARTBEAT[desk_id]["last_seen"] = datetime.now(pytz.UTC)
        
        completed_ticket = None
        curr = db.session.execute(
            select(Ticket).where(
                Ticket.desk_id == desk.id,
                Ticket.ticket_status == TicketStatus.SERVING,
                Ticket.status == RowStatus.ACTIVE
            )
        ).scalar_one_or_none()
        
        if curr:
            curr.mark_completed()
            curr.updated_by = session.get('desk_user', 'system')
            completed_ticket = {
                "number": curr.number,
                "service_duration": curr.service_duration
            }
        
        query = select(Ticket).where(
            Ticket.kode_satker == kode_satker,
            Ticket.ticket_status == TicketStatus.WAITING,
            Ticket.status == RowStatus.ACTIVE,
            Ticket.is_skipped == False
        )
        
        if desk.is_dedicated:
            allowed_ids = desk.service_ids
            if allowed_ids:
                query = query.where(Ticket.service_id.in_(allowed_ids))
            else:
                return jsonify({"error": "No services assigned to this desk"}), 400
        
        query = query.order_by(Ticket.priority.desc(), Ticket.created_at.asc())
        
        nxt = db.session.execute(query.limit(1)).scalar_one_or_none()
        
        if not nxt:
            db.session.commit()
            return jsonify({
                "message": "No waiting tickets for this desk's services",
                "completed": completed_ticket,
                "now_serving": None,
                "desk_services": [s.name for s in desk.allowed_services] if desk.is_dedicated else "all"
            })
        
        nxt.ticket_status = TicketStatus.SERVING
        nxt.desk_id = desk.id
        nxt.called_at = datetime.now(pytz.UTC)
        nxt.updated_by = session.get('desk_user', 'system')
        
        db.session.commit()
        
        LAST_REPLAY[kode_satker] = {
            "ticket": nxt.number,
            "desk": desk.name,
            "desk_id": desk_id,
            "type": "auto",  
            "kode_satker": kode_satker,
            "created": datetime.now(pytz.UTC)
        }
        
        return jsonify({
            "completed": completed_ticket,
            "now_serving": {
                "number": nxt.number,
                "ticket_id": nxt.id,
                "service_type": nxt.service.name if nxt.service else "-",
                "service_prefix": nxt.service.prefix if nxt.service else "-",
                "priority": nxt.priority
            },
            "desk": desk.name
        })
        
    except Exception as e:
        current_app.logger.error(f"Error in api_desk_next: {str(e)}")
        db.session.rollback()
        return jsonify({"error": "Internal server error"}), 500

@app.route("/api/desk/skip/<int:desk_id>", methods=["POST"])
@desk_client_required
def api_desk_skip(desk_id):
    """Skip current ticket"""
    try:
        if session.get('desk_id') != desk_id:
            return jsonify({"error": "Not your assigned desk"}), 403
        
        if session.get('desk_paused'):
            return jsonify({"error": "Desk is paused"}), 400
        
        kode_satker = g.kode_satker if g.user else session.get('kode_satker')
        
        desk = db.session.get(Desk, desk_id)
        if not desk or desk.kode_satker != kode_satker:
            return jsonify({"error": "Desk not found"}), 404
        
        desk.last_activity = datetime.now(pytz.UTC)
        if desk_id in DESK_HEARTBEAT:
            DESK_HEARTBEAT[desk_id]["last_seen"] = datetime.now(pytz.UTC)
        
        data = request.get_json(silent=True) or {}
        reason = data.get("reason", "Tidak ada alasan")
        
        curr = db.session.execute(
            select(Ticket).where(
                Ticket.desk_id == desk.id,
                Ticket.ticket_status == TicketStatus.SERVING,
                Ticket.status == RowStatus.ACTIVE
            )
        ).scalar_one_or_none()
        
        if not curr:
            return jsonify({"error": "No serving ticket to skip"}), 404
        
        curr.mark_skipped(reason=reason)
        curr.updated_by = session.get('desk_user', 'system')
        
        query = select(Ticket).where(
            Ticket.kode_satker == kode_satker,
            Ticket.ticket_status == TicketStatus.WAITING,
            Ticket.status == RowStatus.ACTIVE,
            Ticket.is_skipped == False
        )
        
        if desk.is_dedicated:
            allowed_ids = desk.service_ids
            if allowed_ids:
                query = query.where(Ticket.service_id.in_(allowed_ids))
        
        query = query.order_by(Ticket.priority.desc(), Ticket.created_at.asc())
        nxt = db.session.execute(query.limit(1)).scalar_one_or_none()
        
        result = {
            "skipped": {
                "number": curr.number,
                "reason": reason
            }
        }
        
        if nxt:
            nxt.ticket_status = TicketStatus.SERVING
            nxt.desk_id = desk.id
            nxt.called_at = datetime.now(pytz.UTC)
            nxt.updated_by = session.get('desk_user', 'system')
            result["now_serving"] = {
                "number": nxt.number,
                "ticket_id": nxt.id,
                "service_type": nxt.service.name if nxt.service else "-"
            }
        else:
            result["message"] = "No more waiting tickets"
        
        db.session.commit()
        return jsonify(result)
        
    except Exception as e:
        current_app.logger.error(f"Error in api_desk_skip: {str(e)}")
        db.session.rollback()
        return jsonify({"error": "Internal server error"}), 500

   

@app.route("/api/queue")
@api_auth_or_desk
def api_queue():
    """Get waiting queue"""
    try:
        kode_satker = g.kode_satker if g.user else session.get('kode_satker')
        if not kode_satker:
            return jsonify({"error": "No satker context"}), 400
        
        status_filter = request.args.get('status', 'waiting')
        
        query = select(Ticket).where(
            Ticket.kode_satker == kode_satker,
            Ticket.status == RowStatus.ACTIVE,
            Ticket.is_skipped == False
        )
        
        if status_filter == 'waiting':
            query = query.where(Ticket.ticket_status == TicketStatus.WAITING)
        elif status_filter == 'serving':
            query = query.where(Ticket.ticket_status == TicketStatus.SERVING)
        elif status_filter == 'all':
            query = query.where(Ticket.ticket_status.in_([TicketStatus.WAITING, TicketStatus.SERVING]))
        
        query = query.order_by(Ticket.priority.desc(), Ticket.created_at.asc())
        
        tickets = db.session.execute(query).scalars().all()
        
        result = []
        for t in tickets:
            result.append({
                "id": t.id,
                "number": t.number,
                "service_id": t.service_id,
                "service_name": t.service.name if t.service else "-",
                "service_prefix": t.service.prefix if t.service else "-",
                "priority": t.priority,
                "ticket_status": t.ticket_status.value,
                "created_at": t.created_at.isoformat() if t.created_at else None,
                "wait_time": t.total_wait_time
            })
        
        return jsonify({
            "tickets": result,
            "count": len(result),
            "timestamp": datetime.now(pytz.UTC).isoformat()
        })
        
    except Exception as e:
        current_app.logger.error(f"Error in api_queue: {str(e)}")
        return jsonify({"error": "Failed to load queue"}), 500

@app.route("/api/replay/<ticket>")
def api_replay(ticket):
    """Generate TTS audio"""
    if not ticket or not re.match(r'^[A-Za-z0-9\-]+$', ticket):
        return jsonify({"error": "Invalid ticket format"}), 400
    
    try:
        desk_name = request.args.get('desk', 'meja layanan')
        
        chars = []
        for i, c in enumerate(ticket):
            if c.isalpha():
                chars.append(c.upper())
                if i < len(ticket)-1:
                    chars.append(' ')
            else:
                chars.append(c)
                if i < len(ticket)-2:
                    chars.append(' ')
        
        ticket_spaced = ''.join(chars)
        text = f"Antrian Nomor {ticket_spaced}"
        
        import hashlib
        text_hash = hashlib.md5(text.encode()).hexdigest()
        cache_filename = f"tts_cache_{text_hash}.mp3"
        cache_path = os.path.join(current_app.static_folder or STATIC_DIR, cache_filename)
        
        if os.path.exists(cache_path) and os.path.getsize(cache_path) > 1024:
            return send_file(cache_path, mimetype="audio/mpeg", as_attachment=False)
        
        tts_path = _tts_io(text)  
        
        import shutil
        shutil.copy(tts_path, cache_path)
        
        _cleanup_old_cache()
        
        return send_file(tts_path, mimetype="audio/mpeg", as_attachment=False)
        
    except Exception as e:
        current_app.logger.error(f"TTS error for ticket {ticket}: {e}")
        return jsonify({"error": "Audio generation failed"}), 500

def _cleanup_old_cache(max_files=20):
    """Helper untuk hapus cache TTS lama"""
    try:
        cache_dir = current_app.static_folder or STATIC_DIR
        files = [f for f in os.listdir(cache_dir) if f.startswith('tts_cache_')]
        if len(files) > max_files:
            files.sort(key=lambda x: os.path.getctime(os.path.join(cache_dir, x)))
            for old_file in files[:-max_files]:
                os.remove(os.path.join(cache_dir, old_file))
    except Exception:
        pass

# ---------------------- API: KIOSK -------------------------------------------------------------

@app.route("/api/services")
@login_required
def api_services():
    stmt = active_query(KioskMenu).where(
        KioskMenu.is_active == True,
        KioskMenu.kode_satker == g.kode_satker
    ).order_by(KioskMenu.prefix)
    
    services = db.session.execute(stmt).scalars().all()
    return jsonify([{
        "id": s.id, 
        "name": s.name, 
        "prefix": s.prefix, 
        "display_name": f"{s.prefix} - {s.name}"
    } for s in services])

@app.route("/api/tickets/recent")
@login_required
def api_tickets_recent():
    try:
        limit = request.args.get('limit', 20, type=int)
        session_start_utc = to_utc(get_current_session_start())
        
        stmt = active_query(Ticket).where(
            Ticket.created_at >= session_start_utc,
            Ticket.kode_satker == g.kode_satker
        ).options(
            joinedload(Ticket.service), 
            joinedload(Ticket.desk)
        ).order_by(desc(Ticket.created_at)).limit(limit)
        
        tickets = db.session.execute(stmt).scalars().all()
        now_local = get_local_now()
        result = []
        
        for t in tickets:
            created_local = to_local(t.created_at)
            called_local = to_local(t.called_at)
            completed_local = to_local(t.completed_at)
            
            wait_duration = None
            if called_local and not t.is_skipped:
                wait_duration = (called_local - created_local).total_seconds()
            elif t.status == 'waiting':
                wait_duration = (now_local - created_local).total_seconds()
            
            service_duration = None
            if t.completed_at and t.called_at and not t.is_skipped:
                service_duration = (completed_local - called_local).total_seconds()
            elif t.status == 'serving' and called_local:
                service_duration = (now_local - called_local).total_seconds()
            
            result.append({
                'number': t.number,
                'status': t.status,
                'service_prefix': t.service.prefix if t.service else '-',
                'service_name': t.service.name if t.service else '-',
                'desk_name': t.desk.name if t.desk else None,
                'created_at': created_local.strftime('%H:%M:%S'),
                'called_at': called_local.strftime('%H:%M:%S') if called_local else None,
                'completed_at': completed_local.strftime('%H:%M:%S') if completed_local else None,
                'is_skipped': t.is_skipped,
                'wait_duration': format_duration(wait_duration),
                'service_duration': format_duration(service_duration)
            })
        return jsonify(result)
    except Exception as e:
        current_app.logger.error(f"Error in api_tickets_recent: {e}")
        return jsonify({"error": str(e)}), 500

@app.route("/api/ticket/new/<int:service_id>", methods=["POST"])
@login_required
@csrf_check
def api_new_ticket(service_id):
    """
    ATOMIC TICKET CREATION
    """
    from models import TicketStatus, RowStatus, Ticket, KioskMenu
    from sqlalchemy import select, desc
    
    lock = get_ticket_lock(g.kode_satker)
    
    with lock:
        try:
            stmt = select(KioskMenu).where(
                KioskMenu.id == service_id,
                KioskMenu.kode_satker == g.kode_satker,
                KioskMenu.is_active == True,
                KioskMenu.status == RowStatus.ACTIVE
            )
            svc = db.session.execute(stmt).scalar_one_or_none()
            
            if not svc:
                return jsonify({"error": "Layanan tidak valid atau tidak aktif"}), 400
            
            session_start_utc = to_utc(get_current_session_start())
            
            stmt = select(Ticket).where(
                Ticket.service_id == service_id,
                Ticket.kode_satker == g.kode_satker,
                Ticket.created_at >= session_start_utc,
                Ticket.status == RowStatus.ACTIVE
            ).order_by(desc(Ticket.created_at))
            
            last = db.session.execute(stmt.limit(1)).scalar_one_or_none()
            
            num = 1
            if last:
                num_str = ''.join(filter(str.isdigit, last.number))
                num = int(num_str) + 1 if num_str else 1
            
            max_attempts = 100
            for _ in range(max_attempts):
                number = f"{svc.prefix}{num:03d}"
                exists = db.session.execute(
                    select(Ticket).where(
                        Ticket.number == number,
                        Ticket.kode_satker == g.kode_satker,
                        Ticket.created_at >= session_start_utc,
                        Ticket.status == RowStatus.ACTIVE
                    ).limit(1)
                ).scalar_one_or_none()
                
                if not exists:
                    break
                num += 1
            else:
                return jsonify({"error": "Gagal generate nomor tiket unik"}), 500
            
            t = Ticket(
                number=number,
                service_id=svc.id,
                status=RowStatus.ACTIVE,
                ticket_status=TicketStatus.WAITING,
                kode_satker=g.kode_satker,
                created_by=request.remote_addr or "kiosk"
            )
            db.session.add(t)
            db.session.commit()
            
            current_app.logger.info(f"Ticket created: {number}")
            
            return jsonify({
                "success": True,
                "ticket": t.number,
                "service": svc.name,
                "created_at": get_local_now().strftime('%Y-%m-%d %H:%M:%S'),
                "timezone": "Asia/Makassar (WITA)",
                "session_start": get_current_session_start().strftime('%H:%M')
            })
            
        except Exception as e:
            db.session.rollback()
            current_app.logger.error(f"Ticket creation error: {e}")
            import traceback
            current_app.logger.error(traceback.format_exc())
            return jsonify({"error": "Gagal membuat tiket", "detail": str(e)}), 500
                
# ---------------------- ADMIN BLUEPRINT ----------------------

admin_bp = Blueprint("admin", __name__, url_prefix="/admin", template_folder="templates/admin")

# ---------------------- ADMIN DASHBOARD ----------------------

@admin_bp.route("/")
@login_required
def index():
    return redirect(url_for("admin.dashboard"))

@admin_bp.route("/dashboard")
@login_required
def dashboard():
    selected_satker = g.user.kode_satker
    satker_list = []
    
    if is_super_admin():
        stmt = active_query(Satker).order_by(Satker.nama)
        satker_list = db.session.execute(stmt).scalars().all()
        if request.args.get('satker'):
            selected_satker = request.args.get('satker')
    
    session_start = get_current_session_start()
    
    return render_template(
        "dashboard.html",
        satker_list=satker_list,
        selected_satker=selected_satker,
        session_start=session_start,
        csrf_token=session.get('csrf_token')
    )

@admin_bp.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("login"))

# ---------------------- DASHBOARD ADMIN - ANALYTICS API ----------------------

def calculate_ticket_stats(slot_tickets):
    """Helper untuk menghitung rata-rata wait dan service time"""
    wait_times = []
    service_times = []
    
    for t in slot_tickets:
        if t.called_at and t.created_at:
            wait_sec = (to_utc(t.called_at) - to_utc(t.created_at)).total_seconds()
            wait_times.append(wait_sec / 60)
        
        if t.completed_at and t.called_at:
            svc_sec = (to_utc(t.completed_at) - to_utc(t.called_at)).total_seconds()
            svc_min = svc_sec / 60
            if 0 < svc_min < 120:  # Filter outlier > 2 jam
                service_times.append(svc_min)
    
    avg_wait = sum(wait_times) / len(wait_times) if wait_times else 0
    avg_service = sum(service_times) / len(service_times) if service_times else 0
    
    return avg_wait, avg_service

@admin_bp.route('/api/analytics/summary')
@login_required
def analytics_summary():
    kode_satker, _ = get_satker_scope()
    session_start_utc = to_utc(get_current_session_start())
    
    # Base query untuk SEMUA tiket aktif dalam sesi hari ini (sama untuk semua metrik)
    base_query = Ticket.query_active().filter(
        Ticket.kode_satker == kode_satker,
        Ticket.created_at >= session_start_utc  # Filter hari ini untuk SEMUA
    )
    
    # Total: SEMUA tiket hari ini (waiting + serving + done + skipped)
    total_today = base_query.count()
    
    # Breakdown by status (semua dalam periode yang sama)
    waiting = base_query.filter_by(ticket_status=TicketStatus.WAITING).count()
    serving = base_query.filter_by(ticket_status=TicketStatus.SERVING).count()
    done = base_query.filter_by(ticket_status=TicketStatus.DONE).count()
    skipped = base_query.filter_by(ticket_status=TicketStatus.SKIPPED).count()

    # Rata-rata wait time (hanya untuk tiket hari ini yang sudah dipanggil)
    called_tickets = base_query.filter(Ticket.called_at.is_not(None)).all()
    wait_min = [(to_utc(t.called_at) - to_utc(t.created_at)).total_seconds() / 60 
                for t in called_tickets if t.called_at and t.created_at]
    avg_wait = sum(wait_min) / len(wait_min) if wait_min else 0

    # Rata-rata service time (hanya untuk tiket hari ini yang selesai)
    done_tickets = base_query.filter(
        Ticket.ticket_status == TicketStatus.DONE,
        Ticket.completed_at.is_not(None)
    ).all()
    svc_min = [(to_utc(t.completed_at) - to_utc(t.called_at)).total_seconds() / 60
               for t in done_tickets
               if t.completed_at and t.called_at and
               0 < (to_utc(t.completed_at) - to_utc(t.called_at)).total_seconds() / 60 < 120]
    avg_svc = sum(svc_min) / len(svc_min) if svc_min else 0

    # Served by desk (hanya tiket hari ini)
    served_by_desk = db.session.execute(
        select(Desk.name, func.count(Ticket.id).label('served'))
        .join(Ticket, Desk.id == Ticket.desk_id)
        .where(
            Ticket.kode_satker == kode_satker,
            Ticket.ticket_status == TicketStatus.DONE,
            Ticket.is_deleted == False,  # Soft delete
            Ticket.created_at >= session_start_utc  # Hari ini
        )
        .group_by(Desk.name)
    ).all()

    return jsonify({
        'total_today': total_today,
        'waiting_count': waiting,
        'serving_now': serving,
        'done_count': done,
        'skipped_count': skipped,
        'avg_wait_minutes': round(avg_wait, 1),
        'avg_service_minutes': round(avg_svc, 1),
        'served_by_desk': [{"desk": r.name, "served": r.served} for r in served_by_desk],
        'session_start': get_current_session_start().strftime('%Y-%m-%d %H:%M'),
        'current_time': get_local_now().strftime('%Y-%m-%d %H:%M:%S'),
        'timezone': 'Asia/Makassar (WITA, GMT+8)',
        'kode_satker': kode_satker
    })

@admin_bp.route('/api/analytics/realtime')
@login_required
def analytics_realtime():
    kode_satker, is_scoped = get_satker_scope()

    start_time = get_current_session_start()
    end_time = get_local_now()
    
    start_utc = to_utc(start_time)
    end_utc = to_utc(end_time)

    # Ambil semua tiket aktif dalam sesi
    tickets = Ticket.query_active().filter(
        Ticket.created_at >= start_utc,
        Ticket.created_at <= end_utc,
        Ticket.kode_satker == kode_satker
    ).options(joinedload(Ticket.desk), joinedload(Ticket.service)).all()

    # PERUBAHAN: Slot per 10 menit (bisa diubah ke 5 atau 1 menit)
    slot_minutes = 10
    slots = []
    cur = start_time.replace(minute=(start_time.minute // slot_minutes) * slot_minutes, second=0, microsecond=0)
    while cur <= end_time:
        slots.append(cur)
        cur += timedelta(minutes=slot_minutes)
    
    if len(slots) < 2:
        slots = [start_time, end_time]

    data = {
        'labels': [], 
        'visitor_count': [], 
        'wait_duration': [],      # Historical (sudah dipanggil)
        'wait_current': [],       # NEW: Real-time (masih menunggu)
        'service_duration': []
    }
    
    now_utc_naive = datetime.utcnow()
    
    for i in range(len(slots) - 1):
        s_start = to_utc(slots[i]).replace(tzinfo=None)
        s_end = to_utc(slots[i + 1]).replace(tzinfo=None)
        
        slot_tickets = [t for t in tickets if s_start <= t.created_at < s_end]
        
        # 1. Jumlah pengunjung
        visitor_count = len(slot_tickets)
        
        # 2. WAIT TIME - HISTORICAL (tiket yang sudah dipanggil)
        completed_waits = []
        for t in slot_tickets:
            if t.called_at and t.created_at:
                wait_min = (t.called_at - t.created_at).total_seconds() / 60
                if wait_min > 0:
                    completed_waits.append(wait_min)
        
        avg_wait_historical = sum(completed_waits) / len(completed_waits) if completed_waits else 0
        
        # 3. WAIT TIME - CURRENT/REALTIME (tiket yang masih waiting)
        # Hitung: sekarang - created_at (belum dipanggil)
        current_waits = []
        for t in slot_tickets:
            if t.ticket_status == TicketStatus.WAITING and not t.called_at and t.created_at:
                # Untuk slot terakhir, gunakan waktu sekarang
                # Untuk slot lampau yang masih ada waiting (jarang), gunakan s_end sebagai referensi
                if i == len(slots) - 2:  # Slot terakhir (aktif)
                    ref_time = now_utc_naive
                else:
                    ref_time = s_end  # Akhir slot tersebut
                
                wait_min = (ref_time - t.created_at).total_seconds() / 60
                if wait_min > 0:
                    current_waits.append(wait_min)
        
        avg_wait_current = sum(current_waits) / len(current_waits) if current_waits else 0
        
        # 4. Service time (tetap sama)
        completed_services = [
            ((t.completed_at - t.called_at).total_seconds() / 60)
            for t in slot_tickets 
            if t.completed_at and t.called_at and t.ticket_status == TicketStatus.DONE
        ]
        avg_service = sum(completed_services) / len(completed_services) if completed_services else 0

        data['labels'].append(slots[i].strftime('%H:%M'))
        data['visitor_count'].append(visitor_count)
        data['wait_duration'].append(round(avg_wait_historical, 1))
        data['wait_current'].append(round(avg_wait_current, 1))  # NEW
        data['service_duration'].append(round(avg_service, 1))

    return jsonify(data)

@admin_bp.route('/api/analytics/summary/daily')
@login_required
def analytics_summary_daily():
    if g.user.role not in (UserRole.admin, UserRole.superadmin):
        return jsonify({'error': 'Admin only'}), 403

    kode_satker, _ = get_satker_scope()
    
    now_local = get_local_now()
    start_time = now_local - timedelta(days=29)
    start_utc = to_utc(start_time)

    # Perbaikan: Gunakan query_active()
    base_query = Ticket.query_active().filter(
        Ticket.kode_satker == kode_satker,
        Ticket.created_at >= start_utc
    )
    
    total = base_query.count()
    done = base_query.filter_by(ticket_status=TicketStatus.DONE).count()
    skipped = Ticket.query_active().filter(
        Ticket.kode_satker == kode_satker,
        Ticket.ticket_status == TicketStatus.SKIPPED,
        Ticket.created_at >= start_utc
    ).count()

    # Average wait time
    called_tickets = base_query.filter(Ticket.called_at.is_not(None)).all()
    wait_min = [(to_utc(t.called_at) - to_utc(t.created_at)).total_seconds() / 60
                for t in called_tickets if t.called_at and t.created_at]
    avg_wait = sum(wait_min) / len(wait_min) if wait_min else 0

    # Average service time
    done_tickets = base_query.filter(
        Ticket.ticket_status == TicketStatus.DONE,
        Ticket.completed_at.is_not(None)
    ).all()
    svc_min = [(to_utc(t.completed_at) - to_utc(t.called_at)).total_seconds() / 60
               for t in done_tickets
               if t.completed_at and t.called_at and
               0 < (to_utc(t.completed_at) - to_utc(t.called_at)).total_seconds() / 60 < 120]
    avg_svc = sum(svc_min) / len(svc_min) if svc_min else 0

    return jsonify({
        'total_today': total,
        'waiting_count': 0,
        'serving_now': 0,
        'done_count': done,
        'skipped_count': skipped,
        'avg_wait_minutes': round(avg_wait, 1),
        'avg_service_minutes': round(avg_svc, 1),
        'period_start': start_time.strftime('%d/%m/%Y'),
        'period_end': now_local.strftime('%d/%m/%Y'),
        'is_daily_view': True
    })

@admin_bp.route('/api/analytics/daily')
@login_required
def analytics_daily():
    if g.user.role not in (UserRole.admin, UserRole.superadmin):
        return jsonify({'error': 'Admin only'}), 403

    kode_satker, _ = get_satker_scope()
    
    now_local = get_local_now()
    labels, visitor_count, wait_duration, service_duration = [], [], [], []
    
    for i in range(29, -1, -1):
        day_start = (now_local - timedelta(days=i)).replace(hour=0, minute=0, second=0, microsecond=0)
        day_end = day_start + timedelta(days=1)
        start_utc, end_utc = to_utc(day_start), to_utc(day_end)
        
        # Perbaikan: Gunakan query_active()
        day_tickets = Ticket.query_active().filter(
            Ticket.kode_satker == kode_satker,
            Ticket.created_at >= start_utc,
            Ticket.created_at < end_utc
        ).all()
        
        labels.append(day_start.strftime('%d/%m'))
        visitor_count.append(len(day_tickets))
        
        wait_times, svc_times = [], []
        for t in day_tickets:
            called_local = to_local(t.called_at) if t.called_at else None
            created_local = to_local(t.created_at) if t.created_at else None
            completed_local = to_local(t.completed_at) if t.completed_at else None
            
            if called_local and created_local and t.ticket_status in [TicketStatus.DONE, TicketStatus.SERVING, TicketStatus.SKIPPED]:
                wait_times.append((called_local - created_local).total_seconds() / 60)
            if completed_local and called_local and t.ticket_status == TicketStatus.DONE:
                svc_min = (completed_local - called_local).total_seconds() / 60
                if 0 < svc_min < 120:
                    svc_times.append(svc_min)
        
        wait_duration.append(round(sum(wait_times) / len(wait_times), 1) if wait_times else 0)
        service_duration.append(round(sum(svc_times) / len(svc_times), 1) if svc_times else 0)

    return jsonify({
        'labels': labels,
        'visitor_count': visitor_count,
        'wait_duration': wait_duration,
        'service_duration': service_duration
    })

@admin_bp.route('/api/analytics/summary/monthly')
@login_required
def analytics_summary_monthly():
    if g.user.role not in (UserRole.admin, UserRole.superadmin):
        return jsonify({'error': 'Admin only'}), 403

    kode_satker, _ = get_satker_scope()
    
    now_local = get_local_now()
    end_time = now_local.replace(day=1, hour=0, minute=0, second=0, microsecond=0) + relativedelta(months=1) - timedelta(seconds=1)
    start_time = (end_time - relativedelta(months=11)).replace(day=1, hour=0, minute=0, second=0)
    start_utc = to_utc(start_time)

    # Perbaikan: Gunakan query_active()
    base_query = Ticket.query_active().filter(
        Ticket.kode_satker == kode_satker,
        Ticket.created_at >= start_utc
    )
    
    total = base_query.count()
    done = base_query.filter_by(ticket_status=TicketStatus.DONE).count()
    skipped = Ticket.query_active().filter(
        Ticket.kode_satker == kode_satker,
        Ticket.ticket_status == TicketStatus.SKIPPED,
        Ticket.created_at >= start_utc
    ).count()

    called = base_query.filter(Ticket.called_at.is_not(None)).all()
    wait_min = [(to_utc(t.called_at) - to_utc(t.created_at)).total_seconds() / 60 for t in called if t.called_at and t.created_at]
    avg_wait = sum(wait_min) / len(wait_min) if wait_min else 0

    done_tickets = base_query.filter(Ticket.completed_at.is_not(None)).all()
    svc_min = [(to_utc(t.completed_at) - to_utc(t.called_at)).total_seconds() / 60
               for t in done_tickets
               if t.completed_at and t.called_at and
               0 < (to_utc(t.completed_at) - to_utc(t.called_at)).total_seconds() / 60 < 120]
    avg_svc = sum(svc_min) / len(svc_min) if svc_min else 0

    return jsonify({
        'total_today': total,
        'waiting_count': 0,
        'serving_now': 0,
        'done_count': done,
        'skipped_count': skipped,
        'avg_wait_minutes': round(avg_wait, 1),
        'avg_service_minutes': round(avg_svc, 1),
        'period_start': start_time.strftime('%b %Y'),
        'period_end': now_local.strftime('%b %Y'),
        'is_monthly_view': True
    })

@admin_bp.route('/api/analytics/monthly')
@login_required
def analytics_monthly():
    if g.user.role not in (UserRole.admin, UserRole.superadmin):
        return jsonify({'error': 'Admin only'}), 403

    kode_satker, _ = get_satker_scope()
    
    now_local = get_local_now()
    labels, visitor_count, wait_duration, service_duration = [], [], [], []
    
    for i in range(11, -1, -1):
        month_start = (now_local - relativedelta(months=i)).replace(day=1, hour=0, minute=0, second=0, microsecond=0)
        month_end = (month_start + relativedelta(months=1)) - timedelta(seconds=1)
        start_utc, end_utc = to_utc(month_start), to_utc(month_end)
        
        # Perbaikan: Gunakan query_active()
        month_tickets = Ticket.query_active().filter(
            Ticket.kode_satker == kode_satker,
            Ticket.created_at >= start_utc,
            Ticket.created_at <= end_utc
        ).all()
        
        labels.append(month_start.strftime('%b %Y'))
        visitor_count.append(len(month_tickets))
        
        wait_times, svc_times = [], []
        for t in month_tickets:
            if t.called_at and t.created_at and t.ticket_status in [TicketStatus.DONE, TicketStatus.SERVING]:
                wait_times.append((to_utc(t.called_at) - to_utc(t.created_at)).total_seconds() / 60)
            if t.completed_at and t.called_at and t.ticket_status == TicketStatus.DONE:
                svc_min = (to_utc(t.completed_at) - to_utc(t.called_at)).total_seconds() / 60
                if 0 < svc_min < 120:
                    svc_times.append(svc_min)
        
        wait_duration.append(round(sum(wait_times) / len(wait_times), 1) if wait_times else 0)
        service_duration.append(round(sum(svc_times) / len(svc_times), 1) if svc_times else 0)

    return jsonify({
        'labels': labels,
        'visitor_count': visitor_count,
        'wait_duration': wait_duration,
        'service_duration': service_duration
    })

DESK_PAUSED_STATUS = {}  # {desk_id: True/False}

@admin_bp.route('/api/analytics/desk-status')
@login_required
def analytics_desk_status():
    """Get real-time desk status - Auto-deactivate jika client tutup saat aktif/paused"""
    from flask import current_app
    
    kode_satker, _ = get_satker_scope()
    now_local = get_local_now()
    now_utc = to_utc(now_local)
    session_start_utc = to_utc(get_current_session_start())
    
    # Timeout: 60 detik = auto deactivate jika ghost
    HEARTBEAT_TIMEOUT = 10      # Offline detection
    GHOST_TIMEOUT = 60          # Auto deactivate setelah 60 detik
    
    desks = Desk.query.filter_by(
        kode_satker=kode_satker,
        is_deleted=False
    ).order_by(Desk.name).all()
    
    result = []
    auto_deactivated = []
    
    for desk in desks:
        is_online = False
        last_seen = None
        seconds_offline = None
        
        # Cek status paused dari global dict
        is_paused = DESK_PAUSED_STATUS.get(desk.id, False)
        
        # Cek apakah sedang melayani tiket (SERVING)
        serving_ticket = db.session.execute(
            select(Ticket).where(
                Ticket.desk_id == desk.id,
                Ticket.ticket_status == TicketStatus.SERVING,
                Ticket.is_deleted == False
            )
        ).scalar_one_or_none()
        
        is_serving = serving_ticket is not None
        
        if desk.id in DESK_HEARTBEAT:
            hb_data = DESK_HEARTBEAT[desk.id]
            last_seen = hb_data["last_seen"]
            time_diff = (now_utc - last_seen).total_seconds()
            
            if time_diff <= HEARTBEAT_TIMEOUT:
                is_online = True
            else:
                seconds_offline = int(time_diff)
                
            # GHOST DETECTION:
            # Jika offline terlalu lama DAN (paused ATAU sedang melayani tiket)
            if not is_online and seconds_offline > GHOST_TIMEOUT:
                if is_paused or is_serving:
                    # Auto-deactivate meja
                    desk.is_active = False
                    desk.updated_at = now_utc
                    db.session.add(desk)
                    
                    # Bersihkan status
                    DESK_PAUSED_STATUS.pop(desk.id, None)
                    
                    auto_deactivated.append({
                        'id': desk.id,
                        'name': desk.name,
                        'reason': 'paused' if is_paused else 'serving',
                        'offline_duration': seconds_offline
                    })
                    
                    current_app.logger.warning(
                        f"[GHOST CLEANUP] Auto-deactivated desk {desk.name} "
                        f"after {seconds_offline}s (status: {'paused' if is_paused else 'serving'})"
                    )
        else:
            # Tidak pernah ada heartbeat
            if (is_paused or is_serving) and desk.is_active:
                desk.is_active = False
                desk.updated_at = now_utc
                db.session.add(desk)
                DESK_PAUSED_STATUS.pop(desk.id, None)
                
                auto_deactivated.append({
                    'id': desk.id,
                    'name': desk.name,
                    'reason': 'no_heartbeat',
                    'offline_duration': 99999
                })
        
        # Hitung tiket selesai
        done_count = db.session.execute(
            select(func.count(Ticket.id)).where(
                Ticket.desk_id == desk.id,
                Ticket.ticket_status == TicketStatus.DONE,
                Ticket.is_deleted == False,
                Ticket.created_at >= session_start_utc
            )
        ).scalar() or 0
        
        # Status display
        status_display = 'unknown'
        if not desk.is_active:
            status_display = 'inactive'
        elif is_online and not is_paused and not is_serving:
            status_display = 'online'
        elif is_online and is_paused:
            status_display = 'paused'
        elif is_online and is_serving:
            status_display = 'serving'
        elif not is_online and (is_paused or is_serving):
            status_display = 'ghost'  # Akan segera di-deactivate
        else:
            status_display = 'offline'
        
        result.append({
            'desk_id': desk.id,
            'desk_name': desk.name,
            'is_active_db': desk.is_active,
            'is_paused': is_paused,
            'is_online': is_online,
            'is_serving': is_serving,
            'current_ticket': serving_ticket.number if serving_ticket else None,
            'status_display': status_display,
            'seconds_offline': seconds_offline,
            'served_count': done_count,
            'last_seen': last_seen.isoformat() if last_seen else None,
            'lokasi': desk.lokasi_fisik or '-',
            'was_deactivated': desk.id in [d['id'] for d in auto_deactivated]
        })
    
    if auto_deactivated:
        try:
            db.session.commit()
        except Exception as e:
            db.session.rollback()
            current_app.logger.error(f"[GHOST CLEANUP] Failed: {e}")
    
    return jsonify({
        'desks': result,
        'meta': {
            'total': len(result),
            'active_count': sum(1 for d in result if d['is_active_db']),
            'online_count': sum(1 for d in result if d['is_online']),
            'serving_count': sum(1 for d in result if d['is_serving']),
            'paused_count': sum(1 for d in result if d['is_paused']),
            'auto_deactivated': auto_deactivated
        }
    })

@admin_bp.route('/api/debug/time')
@login_required
def debug_time():
    return jsonify({
        'local_now': get_local_now().isoformat(),
        'utc_now': datetime.now(pytz.UTC).isoformat(),
        'db_sample': str(db.session.execute(select(Ticket.created_at).limit(1)).scalar()),
        'to_utc_test': to_utc(get_local_now()).isoformat(),
        'to_local_test': to_local(datetime.now(pytz.UTC)).isoformat(),
    })

# ---------------------- CRUD: ANNOUNCEMENTS ----------------------

@admin_bp.route("/announcements")
@login_required
@admin_required
def ann_list():
    selected_satker = (
        g.kode_satker
        if not is_super_admin()
        else (request.args.get('satker') or g.kode_satker)
    )

    stmt = db.select(Announcement).where(
        Announcement.kode_satker == selected_satker,
        Announcement.is_deleted == False
    ).order_by(desc(Announcement.created_at))

    anns = db.session.execute(stmt).scalars().all()

    satker_list = None
    if is_super_admin():
        stmt = db.select(Satker).where(
            Satker.is_deleted == False
        ).order_by(Satker.nama)
        satker_list = db.session.execute(stmt).scalars().all()

    current_satker = db.session.get(Satker, selected_satker)

    return render_template(
        "admin/setting_textx.html",
        anns=anns,
        is_superadmin=is_super_admin(),
        selected_satker=selected_satker,
        current_satker=current_satker,
        satker_list=satker_list,
        csrf_token=session.get('csrf_token')
    )


@admin_bp.route("/announcements/add", methods=["POST"])
@login_required
@admin_required
@csrf_check
def ann_add():
    text = request.form.get("text", "").strip()
    kode_satker = request.form.get("kode_satker", g.kode_satker) if is_super_admin() else g.kode_satker
    
    if not text:
        flash("Isi pengumuman tidak boleh kosong", "danger")
        return redirect(url_for("admin.ann_list", satker=kode_satker if is_super_admin() else None))
    
    ann = Announcement(
        text=text,
        kode_satker=kode_satker,
        created_by=g.user.username
    )
    db.session.add(ann)
    db.session.commit()
    flash("Pengumuman berhasil ditambahkan", "success")
    return redirect(url_for("admin.ann_list", satker=kode_satker if is_super_admin() else None))

@admin_bp.route("/announcements/edit/<int:ann_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def ann_edit(ann_id):
    stmt = db.select(Announcement).where(
        Announcement.id == ann_id,
        Announcement.is_deleted == False
    )

    if not is_super_admin():
        stmt = stmt.where(
            Announcement.kode_satker == g.user.kode_satker
        )

    a = db.session.execute(stmt).scalar_one_or_none()
    if not a:
        abort(404)

    new_text = request.form.get("text", "").strip()
    if not new_text:
        flash("Isi pengumuman tidak boleh kosong", "danger")
        return redirect(url_for(
            "admin.ann_list",
            satker=a.kode_satker if is_super_admin() else None
        ))

    a.text = new_text
    a.updated_by = g.user.username
    db.session.commit()

    flash("Pengumuman berhasil diperbarui", "success")
    return redirect(url_for(
        "admin.ann_list",
        satker=a.kode_satker if is_super_admin() else None
    ))

@admin_bp.route("/announcements/delete/<int:ann_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def ann_delete(ann_id):
    stmt = db.select(Announcement).where(
        Announcement.id == ann_id,
        Announcement.is_deleted == False
    )

    if not is_super_admin():
        stmt = stmt.where(
            Announcement.kode_satker == g.user.kode_satker
        )

    a = db.session.execute(stmt).scalar_one_or_none()
    if not a:
        abort(404)

    a.is_deleted = True
    a.deleted_at = datetime.utcnow()
    a.deleted_by = g.user.username

    db.session.commit()

    flash("Pengumuman berhasil dihapus", "success")
    return redirect(url_for(
        "admin.ann_list",
        satker=a.kode_satker if is_super_admin() else None
    ))

# ---------------------- CRUD: USERS ----------------------

@admin_bp.route("/users")
@login_required
@admin_required
def users_list():
    selected_satker = g.kode_satker
    
    if is_super_admin():
        selected_satker = request.args.get('satker') or g.kode_satker
    
    # Perbaikan: Gunakan query_active() dari BaseModel
    query = User.query_active()
    if not is_super_admin():
        query = query.filter_by(kode_satker=selected_satker)
    elif request.args.get('satker'):
        query = query.filter_by(kode_satker=selected_satker)
    
    users = query.order_by(desc(User.created_at)).all()
    
    satker_list = None
    if is_super_admin():
        satker_list = Satker.query_active().order_by(Satker.nama).all()
    
    current_satker = db.session.get(Satker, selected_satker)
    
    return render_template(
        "admin/setting_users.html",
        users=users,
        UserRole=UserRole,
        is_superadmin=is_super_admin(),
        selected_satker=selected_satker,
        current_satker=current_satker,
        satker_list=satker_list,
        current_user_id=g.user.id,
        csrf_token=session.get('csrf_token'),
        to_local=to_local,
        now_local=get_local_now()
    )

@admin_bp.route("/users/form", methods=["GET"])
@login_required
@admin_required
def user_form():
    user_id = request.args.get('user_id', type=int)
    user = None
    default_satker = g.kode_satker
    
    if user_id:
        # Perbaikan: Gunakan query_active()
        user = User.query_active().filter_by(id=user_id).first()
        if not user:
            abort(404)
        
        # Perbaikan: Cek ownership setelah fetch
        if not is_super_admin() and user.kode_satker != g.kode_satker:
            flash("Anda tidak bisa mengedit user dari satker lain", "danger")
            return redirect(url_for("admin.users_list"))
        
        default_satker = user.kode_satker
    
    satker_list = None
    if is_super_admin():
        satker_list = Satker.query_active().order_by(Satker.nama).all()
    
    current_satker = db.session.get(Satker, default_satker)
    
    return render_template(
        "admin/setting_user_form.html",
        user=user,
        UserRole=UserRole,
        is_superadmin=is_super_admin(),
        default_satker=default_satker,
        current_satker=current_satker,
        satker_list=satker_list,
        csrf_token=session.get('csrf_token')
    )

@admin_bp.route("/users/save", methods=["POST"])
@login_required
@admin_required
@csrf_check
def user_save():
    user_id = request.form.get('user_id', type=int)
    username = request.form.get("username", "").strip()
    role = request.form.get("role")
    kode_satker = request.form.get("kode_satker") if is_super_admin() else g.kode_satker
    
    if not username or not role:
        flash("Username dan Role wajib diisi", "danger")
        return redirect(url_for("admin.user_form", user_id=user_id) if user_id else url_for("admin.user_form"))
    
    try:
        role_enum = UserRole(role)
    except ValueError:
        flash("Role tidak valid", "danger")
        return redirect(url_for("admin.user_form", user_id=user_id) if user_id else url_for("admin.user_form"))
    
    if not is_super_admin():
        if role_enum == UserRole.superadmin:
            flash("Anda tidak memiliki izin membuat superadmin", "danger")
            return redirect(url_for("admin.user_form", user_id=user_id) if user_id else url_for("admin.user_form"))
    
    if is_super_admin() and not kode_satker:
        flash("Pilih satker untuk user ini", "danger")
        return redirect(url_for("admin.user_form", user_id=user_id) if user_id else url_for("admin.user_form"))
    
    if user_id:
        # Perbaikan: Gunakan query_active() dan cek ownership
        user = User.query_active().filter_by(id=user_id).first()
        if not user:
            abort(404)
        
        if not is_super_admin() and user.kode_satker != g.kode_satker:
            flash("Akses ditolak", "danger")
            return redirect(url_for("admin.users_list"))
        
        # Perbaikan: Cek duplikat dengan query_active()
        existing = User.query_active().filter(
            User.username == username,
            User.kode_satker == kode_satker,
            User.id != user_id
        ).first()
        
        if existing:
            flash("Username sudah digunakan di satker ini", "danger")
            return redirect(url_for("admin.user_form", user_id=user_id))
        
        user.username = username
        user.role = role_enum
        if is_super_admin():
            user.kode_satker = kode_satker
        
        user.updated_by = g.user.username
        db.session.commit()
        flash(f"User {username} berhasil diupdate", "success")
        
    else:
        # Perbaikan: Cek duplikat dengan query_active()
        existing = User.query_active().filter_by(
            username=username,
            kode_satker=kode_satker
        ).first()
        
        if existing:
            flash("Username sudah terdaftar di satker ini", "danger")
            return redirect(url_for("admin.user_form"))
        
        new_user = User(
            username=username,
            password=None,
            kode_satker=kode_satker,
            role=role_enum,
            created_by=g.user.username  # Tambahan: track created_by
        )
        db.session.add(new_user)
        db.session.commit()
        flash(f"User {username} berhasil ditambahkan", "success")
    
    redirect_url = url_for("admin.users_list")
    if is_super_admin():
        redirect_url = url_for("admin.users_list", satker=kode_satker)
    
    return redirect(redirect_url)

@admin_bp.route("/users/delete/<int:user_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def user_delete(user_id):
    # Perbaikan: Gunakan query_active()
    user = User.query_active().filter_by(id=user_id).first()
    
    if not user:
        abort(404)
    
    # Perbaikan: Cek ownership untuk non-superadmin
    if not is_super_admin() and user.kode_satker != g.kode_satker:
        flash("Akses ditolak", "danger")
        return redirect(url_for("admin.users_list"))
    
    if user.id == g.user.id:
        flash("Tidak bisa menghapus akun sendiri", "danger")
        return redirect(url_for("admin.users_list"))
    
    if user.role == UserRole.superadmin and not is_super_admin():
        flash("Hanya superadmin yang bisa menghapus superadmin lain", "danger")
        return redirect(url_for("admin.users_list"))
    
    # PERBAIKAN KRITIS: Gunakan method soft_delete() agar is_deleted=True tersimpan
    user.soft_delete(deleted_by=g.user.username)
    db.session.commit()
    
    flash(f"User {user.username} berhasil dihapus", "success")
    
    redirect_url = url_for("admin.users_list")
    if is_super_admin():
        redirect_url = url_for("admin.users_list", satker=user.kode_satker)
    
    return redirect(redirect_url)

# ---------------------- CRUD: DESKS ----------------------

@admin_bp.route("/desks")
@login_required
@admin_required
def desks_list():
    selected_satker = g.kode_satker if not is_super_admin() else (request.args.get('satker') or g.kode_satker)
    
    # Gunakan query_active() dari BaseModel
    desks = Desk.query_active().filter_by(
        kode_satker=selected_satker
    ).order_by(Desk.name).all()
    
    satker_list = None
    if is_super_admin():
        satker_list = Satker.query_active().order_by(Satker.nama).all()
    
    current_satker = db.session.get(Satker, selected_satker)
    
    return render_template(
        "admin/setting_desks.html",
        desks=desks,
        is_superadmin=is_super_admin(),
        selected_satker=selected_satker,
        current_satker=current_satker,
        satker_list=satker_list,
        csrf_token=session.get('csrf_token')
    )

@admin_bp.route("/desks/add", methods=["POST"])
@login_required
@admin_required
@csrf_check
def desk_add():
    name = request.form.get("name", "").strip()
    lokasi = request.form.get("lokasi", "").strip()
    kode_satker = request.form.get("kode_satker", g.kode_satker) if is_super_admin() else g.kode_satker
    
    if not name:
        flash("Nama meja wajib diisi", "danger")
        return redirect(url_for("admin.desks_list", satker=kode_satker if is_super_admin() else None))
    
    # Cek duplikat dengan filter is_deleted
    existing = Desk.query_active().filter_by(
        name=name,
        kode_satker=kode_satker
    ).first()
    
    if existing:
        flash(f"Meja '{name}' sudah ada di satker ini", "danger")
        return redirect(url_for("admin.desks_list", satker=kode_satker if is_super_admin() else None))
    
    desk = Desk(
        name=name,
        lokasi_fisik=lokasi or None,
        is_active=True,
        kode_satker=kode_satker,
        created_by=g.user.username
    )
    db.session.add(desk)
    db.session.commit()
    flash(f"Meja '{name}' berhasil ditambahkan", "success")
    return redirect(url_for("admin.desks_list", satker=kode_satker if is_super_admin() else None))

@admin_bp.route("/desks/toggle/<int:desk_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def desk_toggle(desk_id):
    # Gunakan query_active() dan cek ownership
    desk = Desk.query_active().filter_by(id=desk_id).first()
    
    if not desk:
        abort(404)
    
    # Cek ownership untuk non-superadmin
    if not is_super_admin() and desk.kode_satker != g.kode_satker:
        abort(403)
    
    desk.is_active = not desk.is_active
    desk.updated_by = g.user.username
    db.session.commit()
    
    status_text = "aktif" if desk.is_active else "nonaktif"
    flash(f"Meja '{desk.name}' sekarang {status_text}", "info")
    return redirect(url_for("admin.desks_list", satker=desk.kode_satker if is_super_admin() else None))

@admin_bp.route("/desks/edit/<int:desk_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def desk_edit(desk_id):
    # Gunakan query_active() 
    desk = Desk.query_active().filter_by(id=desk_id).first()
    
    if not desk:
        abort(404)
    
    # Cek ownership untuk non-superadmin
    if not is_super_admin() and desk.kode_satker != g.kode_satker:
        abort(403)
    
    new_name = request.form.get("name", "").strip()
    new_lokasi = request.form.get("lokasi", "").strip()
    
    if not new_name:
        flash("Nama meja wajib diisi", "danger")
        return redirect(url_for("admin.desks_list", satker=desk.kode_satker if is_super_admin() else None))
    
    if new_name != desk.name:
        # Cek duplikat dengan exclude diri sendiri dan filter is_deleted
        dup = Desk.query_active().filter(
            Desk.name == new_name,
            Desk.kode_satker == desk.kode_satker,
            Desk.id != desk_id
        ).first()
        
        if dup:
            flash(f"Meja '{new_name}' sudah ada", "danger")
            return redirect(url_for("admin.desks_list", satker=desk.kode_satker if is_super_admin() else None))
    
    desk.name = new_name
    desk.lokasi_fisik = new_lokasi or None
    desk.updated_by = g.user.username
    db.session.commit()
    
    flash(f"Meja '{new_name}' berhasil diupdate", "success")
    return redirect(url_for("admin.desks_list", satker=desk.kode_satker if is_super_admin() else None))

@admin_bp.route("/desks/delete/<int:desk_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def desk_delete(desk_id):
    desk = Desk.query_active().filter_by(id=desk_id).first()
    
    if not desk:
        abort(404)
    
    if not is_super_admin() and desk.kode_satker != g.kode_satker:
        abort(403)
    
    # Cek tiket aktif
    active_ticket = Ticket.query_active().filter(
        Ticket.desk_id == desk.id,
        Ticket.ticket_status.in_([TicketStatus.SERVING, TicketStatus.WAITING])
    ).first()
    
    if active_ticket:
        flash(f"Tidak bisa menghapus meja '{desk.name}' karena masih memiliki tiket aktif", "danger")
        return redirect(url_for("admin.desks_list", satker=desk.kode_satker if is_super_admin() else None))
    
    # FIX MANUAL: Set semua field soft-delete secara eksplisit
    desk.status = RowStatus.DELETED
    desk.is_deleted = True              # Set boolean True
    desk.deleted_at = datetime.utcnow()
    desk.deleted_by = g.user.username
    desk.updated_at = datetime.utcnow()
    desk.updated_by = g.user.username   # Tambahan: set updated_by juga
    
    db.session.add(desk)  # Explicit add untuk memastikan tracking
    db.session.commit()
    
    flash(f"Meja '{desk.name}' berhasil dihapus", "success")
    return redirect(url_for("admin.desks_list", satker=desk.kode_satker if is_super_admin() else None))

# ---------------------- CRUD: KIOSK MENU ----------------------

@admin_bp.route("/kiosks")
@login_required
@admin_required
def kiosk_list():
    selected_satker = g.kode_satker if not is_super_admin() else (request.args.get('satker') or g.kode_satker)
    
    # Perbaikan: Gunakan query_active() dari BaseModel
    menus = KioskMenu.query_active().filter_by(
        kode_satker=selected_satker
    ).order_by(KioskMenu.urutan, KioskMenu.name).all()
    
    satker_list = None
    if is_super_admin():
        satker_list = Satker.query_active().order_by(Satker.nama).all()
    
    current_satker = db.session.get(Satker, selected_satker)
    
    return render_template(
        "admin/setting_kiosks.html",
        menus=menus,
        is_superadmin=is_super_admin(),
        selected_satker=selected_satker,
        current_satker=current_satker,
        satker_list=satker_list,
        csrf_token=session.get('csrf_token')
    )

@admin_bp.route("/kiosks/add", methods=["POST"])
@login_required
@admin_required
@csrf_check
def kiosk_menu_add():
    name = request.form.get("name", "").strip()
    prefix = request.form.get("prefix", "").strip().upper()
    ket = request.form.get("keterangan", "").strip()
    urutan = request.form.get("urutan", 0, type=int)
    kode_satker = request.form.get("kode_satker", g.kode_satker) if is_super_admin() else g.kode_satker

    if not name or not prefix:
        flash("Nama dan prefix wajib diisi", "danger")
        return redirect(url_for("admin.kiosk_list", satker=kode_satker if is_super_admin() else None))

    # Perbaikan: Gunakan query_active() untuk cek duplikat
    existing = KioskMenu.query_active().filter_by(
        prefix=prefix,
        kode_satker=kode_satker
    ).first()
    
    if existing:
        flash(f"Prefix '{prefix}' sudah digunakan", "danger")
        return redirect(url_for("admin.kiosk_list", satker=kode_satker if is_super_admin() else None))

    menu = KioskMenu(
        name=name,
        prefix=prefix,
        keterangan=ket or None,
        urutan=urutan,
        is_active=True,
        kode_satker=kode_satker,
        created_by=g.user.username
    )
    db.session.add(menu)
    db.session.commit()

    flash(f"Layanan '{name}' berhasil ditambahkan", "success")
    return redirect(url_for("admin.kiosk_list", satker=kode_satker if is_super_admin() else None))

@admin_bp.route("/kiosks/toggle/<int:menu_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def kiosk_menu_toggle(menu_id):
    # Perbaikan: Gunakan query_active() dan cek ownership
    menu = KioskMenu.query_active().filter_by(id=menu_id).first()
    
    if not menu:
        abort(404)
    
    # Cek ownership untuk non-superadmin
    if not is_super_admin() and menu.kode_satker != g.kode_satker:
        abort(403)

    menu.is_active = not menu.is_active
    menu.updated_by = g.user.username
    db.session.commit()

    flash(f"Layanan '{menu.name}' sekarang {'aktif' if menu.is_active else 'nonaktif'}", "info")
    return redirect(url_for("admin.kiosk_list", satker=menu.kode_satker if is_super_admin() else None))

@admin_bp.route("/kiosks/edit/<int:menu_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def kiosk_menu_edit(menu_id):
    # Perbaikan: Gunakan query_active() 
    menu = KioskMenu.query_active().filter_by(id=menu_id).first()
    
    if not menu:
        abort(404)
    
    # Cek ownership untuk non-superadmin
    if not is_super_admin() and menu.kode_satker != g.kode_satker:
        abort(403)

    new_name = request.form.get("name", "").strip()
    new_prefix = request.form.get("prefix", "").strip().upper()
    ket = request.form.get("keterangan", "").strip()
    urutan = request.form.get("urutan", 0, type=int)

    if not new_name or not new_prefix:
        flash("Nama dan prefix wajib diisi", "danger")
        return redirect(url_for("admin.kiosk_list", satker=menu.kode_satker if is_super_admin() else None))

    if new_prefix != menu.prefix:
        # Perbaikan: Cek duplikat dengan filter is_deleted
        dup = KioskMenu.query_active().filter(
            KioskMenu.prefix == new_prefix,
            KioskMenu.kode_satker == menu.kode_satker,
            KioskMenu.id != menu_id
        ).first()
        
        if dup:
            flash(f"Prefix '{new_prefix}' sudah digunakan", "danger")
            return redirect(url_for("admin.kiosk_list", satker=menu.kode_satker if is_super_admin() else None))

    menu.name = new_name
    menu.prefix = new_prefix
    menu.keterangan = ket or None
    menu.urutan = urutan
    menu.updated_by = g.user.username
    db.session.commit()

    flash(f"Layanan '{new_name}' berhasil diupdate", "success")
    return redirect(url_for("admin.kiosk_list", satker=menu.kode_satker if is_super_admin() else None))

@admin_bp.route("/kiosks/delete/<int:menu_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def kiosk_menu_delete(menu_id):
    # Perbaikan: Gunakan query_active() 
    menu = KioskMenu.query_active().filter_by(id=menu_id).first()
    
    if not menu:
        abort(404)
    
    # Cek ownership untuk non-superadmin
    if not is_super_admin() and menu.kode_satker != g.kode_satker:
        abort(403)

    # Cek tiket aktif dengan query_active()
    active_ticket = Ticket.query_active().filter(
        Ticket.service_id == menu.id,
        Ticket.ticket_status.in_([TicketStatus.SERVING, TicketStatus.WAITING])
    ).first()

    if active_ticket:
        flash(f"Tidak bisa menghapus layanan '{menu.name}' karena masih memiliki tiket aktif", "danger")
        return redirect(url_for("admin.kiosk_list", satker=menu.kode_satker if is_super_admin() else None))

    # PERBAIKAN KRITIS: Gunakan method soft_delete() agar is_deleted=True tersimpan
    menu.soft_delete(deleted_by=g.user.username)
    db.session.commit()

    flash(f"Layanan '{menu.name}' berhasil dihapus", "success")
    return redirect(url_for("admin.kiosk_list", satker=menu.kode_satker if is_super_admin() else None))

# ---------------------- CRUD: VIDEOS ----------------------

@admin_bp.route("/videos")
@login_required
@admin_required
def video_list():
    selected_satker = g.kode_satker if not is_super_admin() else (request.args.get('satker') or g.kode_satker)

    stmt = active_query(Video).where(
        Video.kode_satker == selected_satker
    ).order_by(desc(Video.created_at))
    
    videos = db.session.execute(stmt).scalars().all()

    satker_list = None
    if is_super_admin():
        satker_list = db.session.execute(
            active_query(Satker).order_by(Satker.nama)
        ).scalars().all()

    current_satker = db.session.get(Satker, selected_satker)

    return render_template(
        "admin/setting_videos.html",
        videos=videos,
        is_superadmin=is_super_admin(),
        selected_satker=selected_satker,
        current_satker=current_satker,
        satker_list=satker_list,
        csrf_token=session.get('csrf_token')
    )

@admin_bp.route("/videos/add", methods=["POST"])
@login_required
@admin_required
@csrf_check
def video_add():
    url = request.form.get("url", "").strip()
    kode_satker = request.form.get("kode_satker", g.kode_satker) if is_super_admin() else g.kode_satker

    if not url:
        flash("URL video wajib diisi", "danger")
        return redirect(url_for("admin.video_list", satker=kode_satker if is_super_admin() else None))

    video = Video(
        filename=url,
        kode_satker=kode_satker,
        created_by=g.user.username
    )
    db.session.add(video)
    db.session.commit()

    flash("Video berhasil ditambahkan", "success")
    return redirect(url_for("admin.video_list", satker=kode_satker if is_super_admin() else None))

@admin_bp.route("/videos/edit/<int:video_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def video_edit(video_id):
    stmt = active_query(Video).where(Video.id == video_id)
    if not is_super_admin():
        stmt = stmt.where(Video.kode_satker == g.kode_satker)

    video = db.session.execute(stmt).scalar_one_or_none()
    if not video:
        abort(404)

    new_url = request.form.get("url", "").strip()
    if not new_url:
        flash("URL video tidak boleh kosong", "danger")
        return redirect(url_for("admin.video_list", satker=video.kode_satker if is_super_admin() else None))

    video.filename = new_url
    video.updated_by = g.user.username
    db.session.commit()

    flash("Video berhasil diperbarui", "success")
    return redirect(url_for("admin.video_list", satker=video.kode_satker if is_super_admin() else None))

@admin_bp.route("/videos/delete/<int:video_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def video_delete(video_id):
    stmt = active_query(Video).where(Video.id == video_id)
    if not is_super_admin():
        stmt = stmt.where(Video.kode_satker == g.kode_satker)

    video = db.session.execute(stmt).scalar_one_or_none()
    if not video:
        abort(404)

    video.status = RowStatus.DELETED
    video.updated_by = g.user.username
    db.session.commit()

    flash("Video berhasil dihapus", "success")
    return redirect(url_for("admin.video_list", satker=video.kode_satker if is_super_admin() else None))

# ---------------------- CRUD: CHARTS ----------------------

def get_active_query(model):
    """Helper untuk query aktif (tidak dihapus)"""
    return db.select(model).where(model.is_deleted == False)

@admin_bp.route("/charts")
@login_required
@admin_required
def chart_list():
    selected_satker = g.kode_satker if not is_super_admin() else (request.args.get('satker') or g.kode_satker)
    
    # Gunakan query_active() dari BaseModel atau filter manual
    charts = Chart.query_active().filter_by(
        kode_satker=selected_satker
    ).order_by(desc(Chart.created_at)).all()
    
    # Atau pakai SQLAlchemy 2.0 style:
    # stmt = select(Chart).where(
    #     Chart.kode_satker == selected_satker,
    #     Chart.is_deleted == False,
    #     Chart.status == RowStatus.ACTIVE
    # ).order_by(desc(Chart.created_at))
    # charts = db.session.execute(stmt).scalars().all()
    
    satker_list = None
    if is_super_admin():
        satker_list = Satker.query_active().order_by(Satker.nama).all()
    
    current_satker = db.session.get(Satker, selected_satker)
    
    chart_types = ['line', 'bar', 'radar', 'pie', 'doughnut', 'polarArea', 'bubble', 'scatter']
    
    return render_template(
        "admin/setting_charts.html",
        charts=charts,
        chart_types=chart_types,
        is_superadmin=is_super_admin(),
        selected_satker=selected_satker,
        current_satker=current_satker,
        satker_list=satker_list,
        csrf_token=session.get('csrf_token')
    )

@admin_bp.route("/charts/add", methods=["POST"])
@login_required
@admin_required
@csrf_check
def chart_add():
    try:
        judul = request.form.get("judul", "").strip()
        slug = request.form.get("slug", "").strip()
        tipe_chart = request.form.get("tipe_chart", "line")
        data_json_str = request.form.get("data_json", "{}").strip()
        opsi_animasi_str = request.form.get("opsi_animasi", "{}").strip()
        refresh_detik = request.form.get("refresh_detik", "60")
        kode_satker = request.form.get("kode_satker", g.kode_satker) if is_super_admin() else g.kode_satker
        
        if not judul or not slug:
            flash("Judul dan Slug wajib diisi", "danger")
            return redirect(url_for("admin.chart_list", satker=kode_satker if is_super_admin() else None))
        
        if not re.match(r'^[a-z0-9-]+$', slug):
            flash("Slug hanya boleh huruf kecil, angka, dan dash", "danger")
            return redirect(url_for("admin.chart_list", satker=kode_satker if is_super_admin() else None))
        
        # Cek existing dengan filter is_deleted
        existing = Chart.query_active().filter_by(
            kode_satker=kode_satker,
            slug=slug
        ).first()
        
        if existing:
            flash(f"Slug '{slug}' sudah digunakan untuk satker ini", "danger")
            return redirect(url_for("admin.chart_list", satker=kode_satker if is_super_admin() else None))
        
        try:
            data_json = json.loads(data_json_str) if data_json_str else {"labels": [], "datasets": []}
            opsi_animasi = json.loads(opsi_animasi_str) if opsi_animasi_str else {"duration": 2000, "easing": "easeOutQuart"}
        except json.JSONDecodeError as e:
            flash(f"Format JSON tidak valid: {str(e)}", "danger")
            return redirect(url_for("admin.chart_list", satker=kode_satker if is_super_admin() else None))
        
        chart = Chart(
            slug=slug,
            judul=judul,
            tipe_chart=tipe_chart,
            data_json=data_json,
            opsi_animasi=opsi_animasi,
            refresh_detik=int(refresh_detik) if refresh_detik else 60,
            kode_satker=kode_satker,
            created_by=g.user.username  # Set created_by
        )
        db.session.add(chart)
        db.session.commit()
        flash("Chart berhasil ditambahkan", "success")
        
    except Exception as e:
        db.session.rollback()
        flash(f"Error menambahkan chart: {str(e)}", "danger")
    
    return redirect(url_for("admin.chart_list", satker=kode_satker if is_super_admin() else None))

@admin_bp.route("/charts/edit/<int:chart_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def chart_edit(chart_id):
    try:
        # Ambil chart dengan filter is_deleted dan ownership
        chart = Chart.query_active().filter_by(id=chart_id).first()
        
        if not chart:
            abort(404)
            
        # Cek ownership untuk non-superadmin
        if not is_super_admin() and chart.kode_satker != g.user.kode_satker:
            abort(403)
        
        chart.judul = request.form.get("judul", chart.judul).strip()
        chart.tipe_chart = request.form.get("tipe_chart", chart.tipe_chart)
        chart.refresh_detik = int(request.form.get("refresh_detik", chart.refresh_detik))
        
        try:
            data_json_str = request.form.get("data_json", "{}").strip()
            opsi_animasi_str = request.form.get("opsi_animasi", "{}").strip()
            
            if data_json_str:
                chart.data_json = json.loads(data_json_str)
            if opsi_animasi_str:
                chart.opsi_animasi = json.loads(opsi_animasi_str)
                
        except json.JSONDecodeError as e:
            flash(f"Format JSON tidak valid: {str(e)}", "danger")
            return redirect(url_for("admin.chart_list", satker=chart.kode_satker if is_super_admin() else None))
        
        new_slug = request.form.get("slug", chart.slug).strip()
        if new_slug != chart.slug:
            existing = Chart.query_active().filter(
                Chart.kode_satker == chart.kode_satker,
                Chart.slug == new_slug,
                Chart.id != chart_id
            ).first()
            
            if existing:
                flash("Slug sudah digunakan oleh chart lain", "danger")
                return redirect(url_for("admin.chart_list", satker=chart.kode_satker if is_super_admin() else None))
            chart.slug = new_slug
        
        chart.updated_by = g.user.username
        db.session.commit()
        flash("Chart berhasil diperbarui", "success")
        
    except Exception as e:
        db.session.rollback()
        flash(f"Error memperbarui chart: {str(e)}", "danger")
    
    return redirect(url_for("admin.chart_list", satker=chart.kode_satker if is_super_admin() else None))

@admin_bp.route("/charts/delete/<int:chart_id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def chart_delete(chart_id):
    # Ambil chart dengan ownership check
    chart = Chart.query_active().filter_by(id=chart_id).first()
    
    if not chart:
        abort(404)
    
    # Cek ownership untuk non-superadmin
    if not is_super_admin() and chart.kode_satker != g.user.kode_satker:
        abort(403)
    
    # Gunakan method soft_delete() dari BaseModel untuk konsistensi
    chart.soft_delete(deleted_by=g.user.username)
    db.session.commit()
    
    flash("Chart berhasil dihapus", "success")
    return redirect(url_for("admin.chart_list", satker=chart.kode_satker if is_super_admin() else None))

@admin_bp.route("/charts/preview/<slug>")
@login_required
@admin_required
def chart_preview(slug):
    """Preview chart data"""
    kode_satker = g.user.kode_satker if not is_super_admin() else request.args.get('satker', g.user.kode_satker)
    
    chart = Chart.query_active().filter_by(
        kode_satker=kode_satker,
        slug=slug
    ).first()
    
    if not chart:
        return jsonify({"error": "Chart not found"}), 404
    
    return jsonify({
        "success": True,
        "chart": {
            "slug": chart.slug,
            "judul": chart.judul,
            "tipe_chart": chart.tipe_chart,
            "data_json": chart.data_json,
            "opsi_animasi": chart.opsi_animasi,
            "refresh_detik": chart.refresh_detik
        }
    })

# ---------------------- CRUD: TICKETS ----------------------

@admin_bp.route("/tickets")
@login_required
def tickets_list():
    if is_super_admin():
        selected_satker = request.args.get("satker", g.kode_satker)
    else:
        selected_satker = g.kode_satker

    # Perbaikan: Gunakan query_active() untuk filter is_deleted=False
    # Tetap gunakan joinedload untuk eager loading
    tickets = Ticket.query_active().filter_by(
        kode_satker=selected_satker
    ).options(
        joinedload(Ticket.service),
        joinedload(Ticket.desk)
    ).order_by(desc(Ticket.created_at)).all()
    
    # Alternatif dengan SQLAlchemy 2.0 style (jika prefer):
    # stmt = select(Ticket).where(
    #     Ticket.kode_satker == selected_satker,
    #     Ticket.is_deleted == False,  # <-- TAMBAHKAN INI
    #     Ticket.status == RowStatus.ACTIVE
    # ).options(
    #     joinedload(Ticket.service),
    #     joinedload(Ticket.desk)
    # ).order_by(desc(Ticket.created_at))
    # tickets = db.session.execute(stmt).scalars().all()
    
    now_local = get_local_now()
    ticket_data = []
    stats = {'total': 0, 'waiting': 0, 'serving': 0, 'done': 0, 'skipped': 0}
    
    for t in tickets:
        created_local = to_local(t.created_at)
        called_local = to_local(t.called_at)
        completed_local = to_local(t.completed_at)
        ticket_status_value = t.ticket_status.value if t.ticket_status else 'unknown'

        wait_duration = None
        if called_local and not t.is_skipped:
            wait_duration = (called_local - created_local).total_seconds()
        elif t.ticket_status == TicketStatus.WAITING:
            wait_duration = (now_local - created_local).total_seconds()

        service_duration = None
        if t.completed_at and t.called_at and not t.is_skipped:
            service_duration = (completed_local - called_local).total_seconds()
        elif t.ticket_status == TicketStatus.SERVING and called_local:
            service_duration = (now_local - called_local).total_seconds()

        stats['total'] += 1
        if ticket_status_value in stats:
            stats[ticket_status_value] += 1
        if t.is_skipped:
            stats['skipped'] += 1

        ticket_data.append({
            'id': t.id,
            'number': t.number,
            'service_name': t.service.name if t.service else '-',
            'desk_name': t.desk.name if t.desk else '-',
            'status': ticket_status_value,
            'is_skipped': t.is_skipped,
            'wait_display': format_duration(wait_duration),
            'service_display': format_duration(service_duration),
            'created_formatted': created_local.strftime('%d/%m %H:%M') if created_local else '-',
            'created_at': t.created_at.isoformat() if t.created_at else None
        })

    if request.args.get('ajax') == '1':
        return jsonify({
            'tickets': ticket_data,
            'stats': stats,
            'current_time': now_local.strftime('%H:%M:%S')
        })

    satker_list = None
    if is_super_admin():
        # Perbaikan: Gunakan query_active()
        satker_list = Satker.query_active().order_by(Satker.nama).all()
    
    current_satker = db.session.get(Satker, selected_satker)

    return render_template(
        "admin/tickets.html",
        ticket_data=ticket_data,
        now_local=now_local,
        session_start=get_current_session_start(),
        is_super=is_super_admin(),
        satker_list=satker_list,
        current_satker=current_satker,
        selected_satker=selected_satker,
        stats=stats,
        csrf_token=session.get('csrf_token')
    )

@admin_bp.route("/tickets/skip/<int:id>", methods=["POST"])
@login_required
@csrf_check
def ticket_skip(id):
    if g.user.role not in (UserRole.admin, UserRole.superadmin):
        flash("Hanya admin yang bisa skip tiket", "warning")
        return redirect(url_for("admin.tickets_list"))

    # Perbaikan: Gunakan query_active() untuk memastikan tiket aktif
    t = Ticket.query_active().filter_by(
        id=id,
        kode_satker=g.kode_satker
    ).first()
    
    if not t:
        abort(404)
    
    if t.ticket_status in [TicketStatus.DONE, TicketStatus.SKIPPED]:
        flash("Tiket sudah selesai atau sudah di-skip", "warning")
        return redirect(url_for("admin.tickets_list", satker=g.kode_satker))
    
    reason = request.form.get("reason", "Dilakukan admin")
    t.mark_skipped(reason=reason)
    t.updated_by = g.user.username
    db.session.commit()
    flash(f"Tiket {t.number} di-skip", "info")
    return redirect(url_for("admin.tickets_list", satker=g.kode_satker))

@admin_bp.route("/tickets/delete/<int:id>", methods=["POST"])
@login_required
@admin_required
@csrf_check
def ticket_delete(id):
    if g.user.role != UserRole.admin and not is_super_admin():
        flash("Hanya admin yang bisa hapus tiket", "warning")
        return redirect(url_for("admin.tickets_list"))

    # Perbaikan: Gunakan query_active() 
    t = Ticket.query_active().filter_by(
        id=id,
        kode_satker=g.kode_satker
    ).first()
    
    if not t:
        abort(404)
    
    if t.ticket_status in [TicketStatus.SERVING, TicketStatus.WAITING]:
        flash(f"Tidak bisa menghapus tiket {t.number} karena masih dalam status {t.ticket_status.value}. Selesaikan atau skip terlebih dahulu.", "danger")
        return redirect(url_for("admin.tickets_list", satker=g.kode_satker))
    
    # SUDAH BENAR: Gunakan soft_delete()
    t.soft_delete(deleted_by=g.user.username)
    db.session.commit()
    flash(f"Tiket {t.number} dihapus", "warning")
    return redirect(url_for("admin.tickets_list", satker=g.kode_satker))

# ---------------------- INITIALIZATION ----------------------

def check_db_connection():
    """Cek apakah koneksi MySQL berhasil"""
    try:
        with app.app_context():
            db.session.execute(text('SELECT 1'))
        return True
    except OperationalError as e:
        print(f"[ERROR] Cannot connect to MySQL: {e}")
        return False

def init_db(dev_reset=False):
    with app.app_context():
        if dev_reset:
            print("[WARNING] Dropping all tables...")
            db.drop_all()
        
        db.create_all()
        print("[INFO] Database tables initialized")
        
        # Perbaikan: Gunakan Satker.kode_satker (bukan Satker.id)
        # atau gunakan func.count('*') untuk count semua rows
        try:
            satker_count = db.session.execute(select(func.count(Satker.kode_satker))).scalar()
        except AttributeError:
            # Fallback jika kode_satker juga tidak ada (jarang terjadi)
            satker_count = db.session.execute(select(func.count()).select_from(Satker)).scalar()
        
        if satker_count == 0:
            print("[INFO] Seeding initial data...")
            
            satker_list = [
                ("7500", "BPS Provinsi Gorontalo"),
                ("7501", "BPS Kabupaten Boalemo"),
                ("7502", "BPS Kabupaten Gorontalo"),
                ("7503", "BPS Kabupaten Pohuwato"),
                ("7504", "BPS Kabupaten Bone Bolango"),
                ("7505", "BPS Kabupaten Gorontalo Utara"),
                ("7571", "BPS Kota Gorontalo")
            ]
            
            for kode, nama in satker_list:
                satker = Satker(kode_satker=kode, nama=nama)
                db.session.add(satker)
            
            db.session.commit()
            
            # Helper function untuk cek existing data
            def get_active(cls, filter_col, filter_val, kode_satker_val):
                return db.session.execute(
                    select(cls).where(
                        cls.status != RowStatus.DELETED,
                        filter_col == filter_val,
                        cls.kode_satker == kode_satker_val
                    )
                ).scalar_one_or_none()
            
            for kode, nama in satker_list:
                # Admin default
                if not get_active(User, User.username, f"admin{kode}", kode):
                    db.session.add(User(
                        username=f"admin{kode}",
                        kode_satker=kode,
                        role=UserRole.admin
                    ))
                
                # superadmin untuk 7500
                if kode == "7500":
                    for username in ["fitra", "assel"]:
                        if not get_active(User, User.username, username, kode):
                            db.session.add(User(
                                username=username,
                                kode_satker=kode,
                                role=UserRole.superadmin
                            ))
                
                # Desks
                for name, active in [("PPID", True), 
                                     ("PST-1", True), 
                                     ("PST-2", True), 
                                     ("PENGADUAN", False)]:
                    if not get_active(Desk, Desk.name, name, kode):
                        db.session.add(Desk(
                            name=name,
                            is_active=active,
                            kode_satker=kode
                        ))
                
                # Kiosk Menu
                menu_items = [
                    ("A", "Layanan Perpustakaan"),
                    ("B", "Konsultasi Statistik"),
                    ("C", "Penjualan Produk"),
                    ("D", "Rekomendasi Kegiatan"),
                    ("E", "Layanan Lainnya")
                ]
                for prefix, menu_name in menu_items:
                    if not get_active(KioskMenu, KioskMenu.prefix, prefix, kode):
                        db.session.add(KioskMenu(
                            name=menu_name,
                            prefix=prefix,
                            is_active=True,
                            kode_satker=kode,
                            urutan=ord(prefix) - ord('A')
                        ))
                
                # Announcement
                existing_ann = db.session.execute(
                    select(Announcement).where(
                        Announcement.kode_satker == kode,
                        Announcement.is_deleted == False
                    )
                ).scalar_one_or_none()
                
                if not existing_ann:
                    db.session.add(Announcement(
                        text=f"Selamat datang di Pelayanan Statistik Terpadu {nama}, silahkan ambil nomor antrian terlebih dahulu...",
                        kode_satker=kode
                    ))
                
                # Charts
                for i in range(1, 6):
                    existing_chart = db.session.execute(
                        select(Chart).where(
                            Chart.slug == f"grafik{i}",
                            Chart.kode_satker == kode
                        )
                    ).scalar_one_or_none()
                    
                    if not existing_chart:
                        db.session.add(Chart(
                            slug=f"grafik{i}",
                            judul=f"Grafik {i}",
                            data_json={"labels": [], "datasets": []},
                            tipe_chart="bar",
                            urutan=i,
                            kode_satker=kode
                        ))
            
            db.session.commit()
            print("[INFO] Seeding completed")
        else:
            print(f"[INFO] Database already has {satker_count} satker(s), skipping seed")

# ---------------------- MAIN ----------------------
app.register_blueprint(admin_bp)

if __name__ == "__main__":
    print("[INFO] Starting Queue Management System...")
    
    # Check koneksi database terlebih dahulu
    if not check_db_connection():
        print("[FATAL] Cannot start without database connection!")
        exit(1)
    
    # Inisialisasi DB jika diperlukan
    init_db(dev_reset=False)
    
    os.environ['TZ'] = 'Asia/Makassar'
    
    print(f"[INFO] Server time: {get_local_now().strftime('%Y-%m-%d %H:%M:%S')} WITA (GMT+8)")
    print(f"[INFO] Database type: MySQL")
    print(f"[INFO] Connected to: {DB_HOST}:{DB_PORT}/{DB_NAME}")
    
    # Production: jangan gunakan debug=True
    # Gunakan 0.0.0.0 agar bisa diakses dari luar
    app.run(host="0.0.0.0", port=8080, debug=False, threaded=True)