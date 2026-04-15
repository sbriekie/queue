import os
import enum
from datetime import datetime
from uuid import uuid4
from flask_sqlalchemy import SQLAlchemy
from flask import url_for

db = SQLAlchemy()

# ---------------------- ENUM ----------------------
class RowStatus(enum.Enum):
    ACTIVE   = "A"
    INACTIVE = "I"
    DELETED  = "D"

class UserRole(enum.Enum):
    admin   = "admin"
    operator= "operator"
    viewer  = "viewer"
    superadmin = "superadmin"

class TicketStatus(enum.Enum):  # Dipisah dari RowStatus
    WAITING  = "waiting"
    SERVING  = "serving"
    DONE     = "done"
    SKIPPED  = "skipped"

# ---------------------- BASE MIXIN ----------------------
class BaseModel(db.Model):
    __abstract__ = True
    
    uuid        = db.Column(db.String(36), default=lambda: str(uuid4()), unique=True)
    status      = db.Column(db.Enum(RowStatus), default=RowStatus.ACTIVE, nullable=False)
    created_at  = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    updated_at  = db.Column(db.DateTime, onupdate=datetime.utcnow)
    created_by  = db.Column(db.String(50))      # <-- TAMBAHKAN BARIS INI
    updated_by  = db.Column(db.String(50))      # Sudah ada
    deleted_at  = db.Column(db.DateTime, nullable=True)
    deleted_by  = db.Column(db.String(50), nullable=True)
    is_deleted  = db.Column(db.Boolean, default=False, nullable=False)
    # Query class untuk auto-filter soft deleted
    @classmethod
    def query_active(cls):
        """Query hanya record yang aktif (tidak dihapus)"""
        return cls.query.filter_by(is_deleted=False)

    @classmethod
    def query_with_deleted(cls):
        """Query semua record termasuk yang dihapus"""
        return cls.query

    @classmethod
    def query_deleted_only(cls):
        """Query hanya record yang dihapus"""
        return cls.query.filter_by(is_deleted=True)

    def soft_delete(self, deleted_by=None):
        """Soft delete record"""
        self.status = RowStatus.DELETED
        self.is_deleted = True
        self.deleted_at = datetime.utcnow()
        self.deleted_by = deleted_by
        self.updated_at = datetime.utcnow()
        db.session.add(self)
        return self

    def restore(self, restored_by=None):
        """Restore soft deleted record"""
        self.status = RowStatus.ACTIVE
        self.is_deleted = False
        self.deleted_at = None
        self.deleted_by = None
        self.updated_at = datetime.utcnow()
        self.updated_by = restored_by
        db.session.add(self)
        return self

    def hard_delete(self):
        """Hard delete permanen dari database"""
        db.session.delete(self)
        return self

# ---------------------- SATKER ----------------------
class Satker(BaseModel):  # Sekarang inherit dari BaseModel
    __tablename__ = "satker"
    
    kode_satker     = db.Column(db.String(6), primary_key=True)
    nama            = db.Column(db.String(120), nullable=False)
    alamat          = db.Column(db.Text)
    logo_url        = db.Column(db.String(500))
    warna_primer    = db.Column(db.String(7), default="#003366")
    warna_sekunder  = db.Column(db.String(7), default="#FFFFFF")
    # Kolom BaseModel: uuid, status, created_at, updated_at, updated_by, 
    #                  deleted_at, deleted_by, is_deleted (otomatis)

    def __repr__(self):
        return f"<Satker {self.kode_satker} {self.nama}>"

# ---------------------- USER ----------------------
class User(BaseModel):
    __tablename__ = "users"
    
    id          = db.Column(db.Integer, primary_key=True)
    username    = db.Column(db.String(80), nullable=False)
    password    = db.Column(db.String(120), nullable=True)
    kode_satker = db.Column(db.String(6), db.ForeignKey("satker.kode_satker"), nullable=False)
    role        = db.Column(db.Enum(UserRole), default=UserRole.operator)
    last_login  = db.Column(db.DateTime)
    
    # relations
    satker      = db.relationship("Satker", backref=db.backref("users", lazy=True))
    
    def __repr__(self):
        return f"<User {self.username} {self.kode_satker}>"

# ---------------------- DESK ----------------------
class Desk(BaseModel):
    __tablename__ = "desks"
    
    id          = db.Column(db.Integer, primary_key=True)
    name        = db.Column(db.String(100), nullable=False)
    is_active   = db.Column(db.Boolean, default=True)
    is_paused   = db.Column(db.Boolean, default=False)
    lokasi_fisik= db.Column(db.String(100))
    kode_satker = db.Column(db.String(6), db.ForeignKey("satker.kode_satker"), nullable=False)
    
    # Tambahan: flag apakah meja dedicated atau general
    is_dedicated = db.Column(db.Boolean, default=False)  # True = hanya layanan tertentu
    
    satker      = db.relationship("Satker", backref=db.backref("desks", lazy=True))
    
    @property
    def allowed_services(self):
        """Return list of KioskMenu yang bisa dilayani meja ini"""
        if not self.is_dedicated:
            # General desk: semua layanan aktif di satker
            return KioskMenu.query.filter_by(
                kode_satker=self.kode_satker,
                status=RowStatus.ACTIVE,
                is_active=True
            ).all()
        # Dedicated desk: hanya yang di-assign
        return [ds.service for ds in self.desk_services if ds.service.status == RowStatus.ACTIVE]
    
    @property
    def service_ids(self):
        """Return list of service IDs untuk filtering query"""
        if not self.is_dedicated:
            return None  # Signal: semua layanan
        return [ds.service_id for ds in self.desk_services]
    
    def can_serve(self, service_id):
        """Cek apakah meja bisa melayani service_id tertentu"""
        if not self.is_dedicated:
            return True
        return any(ds.service_id == service_id for ds in self.desk_services)
    
    def __repr__(self):
        return f"<Desk {self.name} {'[DEDICATED]' if self.is_dedicated else '[GENERAL]'}>"
    
# ---------------------- DESK SERVICES (Junction Table) ----------------------
class DeskService(db.Model):
    __tablename__ = "desk_services"
    
    id          = db.Column(db.Integer, primary_key=True)
    desk_id     = db.Column(db.Integer, db.ForeignKey("desks.id", ondelete="CASCADE"), nullable=False)
    service_id  = db.Column(db.Integer, db.ForeignKey("kiosk_menu.id", ondelete="CASCADE"), nullable=False)
    is_primary  = db.Column(db.Boolean, default=False)  # Layanan utama (prioritas)
    
    # Unique constraint: 1 layanan hanya 1 entry per desk
    __table_args__ = (db.UniqueConstraint('desk_id', 'service_id'),)
    
    # Relations
    desk        = db.relationship("Desk", backref=db.backref("desk_services", lazy=True, cascade="all, delete-orphan"))
    service     = db.relationship("KioskMenu", backref=db.backref("desk_assignments", lazy=True))

# ---------------------- KIOSK MENU ----------------------
class KioskMenu(BaseModel):
    __tablename__ = "kiosk_menu"
    
    id          = db.Column(db.Integer, primary_key=True)
    name        = db.Column(db.String(100), nullable=False)
    prefix      = db.Column(db.String(5), nullable=False)
    is_active   = db.Column(db.Boolean, default=True)  # Operational status
    keterangan  = db.Column(db.Text)
    urutan      = db.Column(db.Integer, default=0)
    kode_satker = db.Column(db.String(6), db.ForeignKey("satker.kode_satker"), nullable=False)
    
    satker      = db.relationship("Satker", backref=db.backref("kiosk_menus", lazy=True))

    def __repr__(self):
        return f"<KioskMenu {self.prefix} {self.name}>"

# ---------------------- TICKET ----------------------
class Ticket(BaseModel):
    __tablename__ = "tickets"
    
    id              = db.Column(db.Integer, primary_key=True)
    number          = db.Column(db.String(10), nullable=False)
    status          = db.Column(db.Enum(RowStatus), default=RowStatus.ACTIVE)
    ticket_status   = db.Column(db.Enum(TicketStatus), default=TicketStatus.WAITING)
    created_at      = db.Column(db.DateTime, default=datetime.utcnow)  # Override untuk ticket specific
    called_at       = db.Column(db.DateTime)
    completed_at    = db.Column(db.DateTime)
    is_skipped      = db.Column(db.Boolean, default=False)
    skipped_at      = db.Column(db.DateTime)
    skip_reason     = db.Column(db.String(200))
    priority        = db.Column(db.Integer, default=0)  # 0 normal, 1 VIP
    created_by      = db.Column(db.String(50))  # kiosk id / ip
    
    # FK
    service_id      = db.Column(db.Integer, db.ForeignKey("kiosk_menu.id"), nullable=False)
    desk_id         = db.Column(db.Integer, db.ForeignKey("desks.id", ondelete="SET NULL"))
    kode_satker     = db.Column(db.String(6), db.ForeignKey("satker.kode_satker"), nullable=False)
    
    # relations
    service         = db.relationship("KioskMenu", backref=db.backref("tickets", lazy=True))
    desk            = db.relationship("Desk", backref=db.backref("tickets", lazy=True))
    satker          = db.relationship("Satker", backref=db.backref("tickets", lazy=True))

    # methods
    def mark_completed(self):
        self.ticket_status = TicketStatus.DONE
        self.completed_at = datetime.utcnow()
        self.is_skipped = False
        db.session.add(self)

    def mark_skipped(self, reason=None):
        self.ticket_status = TicketStatus.SKIPPED
        self.is_skipped = True
        self.skipped_at = datetime.utcnow()
        self.skip_reason = reason
        db.session.add(self)

    def call(self):
        """Panggil ticket ke desk"""
        self.ticket_status = TicketStatus.SERVING
        self.called_at = datetime.utcnow()
        db.session.add(self)

    @property
    def service_duration(self):
        if self.called_at and self.completed_at:
            return (self.completed_at - self.called_at).total_seconds()
        return None

    @property
    def total_wait_time(self):
        if self.created_at and self.called_at:
            return (self.called_at - self.created_at).total_seconds()
        return None

    def __repr__(self):
        return f"<Ticket {self.number} {self.ticket_status.value}>"

# ---------------------- ANNOUNCEMENT ----------------------
class Announcement(BaseModel):
    __tablename__ = "announcements"
    
    id              = db.Column(db.Integer, primary_key=True)
    text            = db.Column(db.String(500), nullable=False)
    tipe            = db.Column(db.String(30), default="text")  # text/html/markdown
    tanggal_tampil  = db.Column(db.Date)
    tanggal_akhir   = db.Column(db.Date)
    kode_satker     = db.Column(db.String(6), db.ForeignKey("satker.kode_satker"), nullable=False)
    
    satker          = db.relationship("Satker", backref=db.backref("announcements", lazy=True))

    def __repr__(self):
        return f"<Announcement {self.text[:20]}>"

# ---------------------- VIDEO ----------------------
class Video(BaseModel):
    __tablename__ = "videos"
    
    id = db.Column(db.Integer, primary_key=True)
    filename = db.Column(db.String(500), nullable=False)  # URL video
    kode_satker = db.Column(db.String(10), db.ForeignKey('satker.kode_satker'), nullable=False)
    status = db.Column(db.Enum(RowStatus), default=RowStatus.ACTIVE)
    
    # TAMBAHKAN INI JIKA INGIN AUDIT TRAIL:
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    created_by = db.Column(db.String(100))
    updated_at = db.Column(db.DateTime, onupdate=datetime.utcnow)
    updated_by = db.Column(db.String(100))

    @property
    def url(self):
        if self.filename.startswith("http"):
            return self.filename
        return url_for("static", filename=f"videos/{self.filename}", _external=True)

    def __repr__(self):
        return f"<Video {self.filename}>"

# ---------------------- CHART ----------------------
class Chart(BaseModel):
    __tablename__ = "charts"
    
    id              = db.Column(db.Integer, primary_key=True)
    slug            = db.Column(db.String(50), nullable=False)
    judul           = db.Column(db.String(200), nullable=False)  # Tambah nullable=False jika memang required
    data_json       = db.Column(db.JSON, nullable=False, default=dict)
    tipe_chart      = db.Column(db.String(30), default="bar")
    opsi_animasi    = db.Column(db.JSON, default=dict)
    refresh_detik   = db.Column(db.Integer, default=300)
    urutan          = db.Column(db.Integer, default=0)
    kode_satker     = db.Column(db.String(6), db.ForeignKey("satker.kode_satker"), nullable=False)
    status          = db.Column(db.Enum(RowStatus), default=RowStatus.ACTIVE)
    created_at      = db.Column(db.DateTime, default=datetime.utcnow)
    updated_at      = db.Column(db.DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    updated_by      = db.Column(db.String(50))
    
    satker          = db.relationship("Satker", backref=db.backref("charts", lazy=True))
    
    __table_args__ = (db.UniqueConstraint('kode_satker', 'slug'),)