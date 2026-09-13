from flask import Flask, request, jsonify, session, redirect, url_for, render_template, Response
from functools import wraps
from dotenv import load_dotenv
load_dotenv()
from pymongo import MongoClient
from bson import ObjectId, errors as bson_errors
from datetime import datetime, timezone, timedelta
from werkzeug.security import generate_password_hash, check_password_hash
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from PIL import Image
from email.message import EmailMessage
import bleach, atexit, os, logging, secrets, re, io, hashlib, smtplib, json

app = Flask(__name__)

# -- SESSION REMINDER SCHEDULER ------------------------------------------------------------------
try:
    from apscheduler.schedulers.background import BackgroundScheduler
    _scheduler = BackgroundScheduler(daemon=True)
    _scheduler_available = True
except ImportError:
    _scheduler = None
    _scheduler_available = False
_secret_key = os.environ.get('SECRET_KEY')
if not _secret_key:
    raise RuntimeError('SECRET_KEY environment variable is not set')
app.secret_key = _secret_key

app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE='Lax',
    SESSION_COOKIE_SECURE=os.environ.get('FLASK_ENV') == 'production',
    PERMANENT_SESSION_LIFETIME=timedelta(hours=4),
    MAX_CONTENT_LENGTH=10 * 1024 * 1024,  # 10 MB upload limit
)

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

limiter = Limiter(key_func=get_remote_address, app=app, default_limits=[])

@app.after_request
def set_security_headers(response):
    response.headers['X-Content-Type-Options'] = 'nosniff'
    response.headers['X-Frame-Options'] = 'SAMEORIGIN'
    response.headers['X-XSS-Protection'] = '1; mode=block'
    response.headers['Referrer-Policy'] = 'strict-origin-when-cross-origin'
    response.headers['Content-Security-Policy'] = (
        "default-src 'self'; "
        "script-src 'self' 'unsafe-inline' https://cdnjs.cloudflare.com https://fonts.googleapis.com https://www.googletagmanager.com https://cdn.jsdelivr.net; "
        "style-src 'self' 'unsafe-inline' https://cdnjs.cloudflare.com https://fonts.googleapis.com https://fonts.gstatic.com; "
        "font-src 'self' data: https://cdnjs.cloudflare.com https://fonts.gstatic.com; "
        "img-src 'self' data: blob: https:; "
        "frame-src https://www.youtube.com https://www.youtube-nocookie.com https://calendly.com https://maps.google.com https://maps.app.goo.gl https://www.google.com/maps/; "
        "connect-src 'self' https://cdn.jsdelivr.net;"
    )
    return response

ADMIN_USERNAME = os.environ.get('ADMIN_USERNAME')
_admin_password = os.environ.get('ADMIN_PASSWORD')
if not ADMIN_USERNAME or not _admin_password:
    raise RuntimeError('ADMIN_USERNAME and ADMIN_PASSWORD environment variables must be set')
ADMIN_PASSWORD_HASH = generate_password_hash(_admin_password)
del _admin_password

def login_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not session.get('logged_in'):
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated

_IST = timedelta(hours=5, minutes=30)

def to_ist(dt):
    """Convert UTC datetime to IST and format with AM/PM."""
    if not dt:
        return ''
    if isinstance(dt, str):
        for fmt in ('%Y-%m-%d %H:%M', '%Y-%m-%dT%H:%M:%S', '%Y-%m-%dT%H:%M:%S.%f'):
            try:
                dt = datetime.strptime(dt[:19], fmt[:len(fmt)])
                break
            except ValueError:
                continue
        else:
            return dt  # return as-is if unparseable
    if not isinstance(dt, datetime):
        return str(dt)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    ist = dt + _IST
    return ist.strftime('%d %b %Y, %I:%M %p')

def safe_oid(oid):
    try:
        return ObjectId(oid)
    except (bson_errors.InvalidId, TypeError):
        return None

def s(text, max_len=2000):
    return bleach.clean(str(text), tags=[], strip=True)[:max_len]

_YT_ID = re.compile(
    r'(?:youtube(?:-nocookie)?\.com/(?:watch\?(?:.*&)?v=|embed/|shorts/)|youtu\.be/)([A-Za-z0-9_-]{11})'
)
LEAD_STAGES = ('new', 'contacted', 'consult_booked', 'signed', 'lost')

def youtube_embed(url):
    if not url:
        return ''
    m = _YT_ID.search(str(url).strip())
    if not m:
        return ''
    return f'https://www.youtube.com/embed/{m.group(1)}'

def _exercise_video_index():
    by_id, by_name = {}, {}
    if exercises_col is None:
        return by_id, by_name
    for e in exercises_col.find({}, {'name': 1, 'video_url': 1}):
        embed = youtube_embed(e.get('video_url', ''))
        if not embed:
            continue
        by_id[str(e['_id'])] = embed
        name = (e.get('name') or '').strip().lower()
        if name:
            by_name[name] = embed
    return by_id, by_name

def _hash_token(token):
    return hashlib.sha256(token.encode('utf-8')).hexdigest()

def _send_whatsapp(message):
    """Send WhatsApp notification to trainer via CallMeBot (free)."""
    cfg = get_config() if config_col is not None else {}
    phone  = (cfg.get('callmebot_phone') or '').strip().replace(' ', '').replace('+', '')
    apikey = (cfg.get('callmebot_apikey') or '').strip()
    if not phone or not apikey:
        return False
    try:
        import urllib.request, urllib.parse
        params = urllib.parse.urlencode({'phone': phone, 'text': message, 'apikey': apikey})
        url = f'https://api.callmebot.com/whatsapp.php?{params}'
        with urllib.request.urlopen(url, timeout=8) as r:
            return r.status == 200
    except Exception as e:
        logger.warning('WhatsApp notify failed: %s', e)
        return False

def _send_email(to_addr, subject, body):
    host = (os.environ.get('MAIL_SERVER') or '').strip()
    if not host or not to_addr:
        return False
    try:
        port = int(os.environ.get('MAIL_PORT', '587'))
    except ValueError:
        port = 587
    user = os.environ.get('MAIL_USERNAME', '')
    password = os.environ.get('MAIL_PASSWORD', '')
    from_addr = os.environ.get('MAIL_FROM', user or 'noreply@localhost')
    use_tls = os.environ.get('MAIL_USE_TLS', 'true').lower() == 'true'
    msg = EmailMessage()
    msg['Subject'] = subject
    msg['From'] = from_addr
    msg['To'] = to_addr
    msg.set_content(body)
    try:
        with smtplib.SMTP(host, port, timeout=12) as smtp:
            if use_tls:
                smtp.starttls()
            if user:
                smtp.login(user, password)
            smtp.send_message(msg)
        return True
    except Exception as e:
        logger.warning('Email send failed: %s', e)
        return False

def _issue_reset_token(user):
    token = secrets.token_urlsafe(32)
    users_col.update_one({'_id': user['_id']}, {'$set': {
        'reset_token_hash': _hash_token(token),
        'reset_token_expires': datetime.now(timezone.utc) + timedelta(hours=1),
    }})
    return token

def _reset_url(token):
    return url_for('reset_password', token=token, _external=True)

def _ist_today():
    return (datetime.now(timezone.utc) + _IST).date()

def _is_trained_log(log):
    return (log.get('steps') or 0) > 0 or (log.get('calories_burned') or 0) > 0

def _compute_adherence(cid):
    trained = set()
    if db is not None:
        for log in db['daily_log'].find({'client_id': cid}, {'date': 1, 'steps': 1, 'calories_burned': 1}):
            if log.get('date') and _is_trained_log(log):
                trained.add(str(log['date'])[:10])
    if sessions_col is not None:
        week_ago = datetime.now(timezone.utc) - timedelta(days=21)
        for sess in sessions_col.find({
            'client_id': cid,
            'status': {'$in': ['confirmed', 'completed']},
            'datetime': {'$gte': week_ago},
        }, {'datetime': 1}):
            dt = sess.get('datetime')
            if not dt:
                continue
            if getattr(dt, 'tzinfo', None) is None:
                dt = dt.replace(tzinfo=timezone.utc)
            trained.add((dt + _IST).strftime('%Y-%m-%d'))
    today = _ist_today()
    week_dates = [(today - timedelta(days=i)).strftime('%Y-%m-%d') for i in range(7)]
    trained_week = sum(1 for d in week_dates if d in trained)
    today_str = today.strftime('%Y-%m-%d')
    yesterday_str = (today - timedelta(days=1)).strftime('%Y-%m-%d')
    streak = 0
    if today_str in trained:
        start = today
    elif yesterday_str in trained:
        start = today - timedelta(days=1)
    else:
        start = None
    if start:
        d = start
        while d.strftime('%Y-%m-%d') in trained:
            streak += 1
            d -= timedelta(days=1)
    return {
        'trained_this_week': trained_week,
        'streak': streak,
        'adherence': round(trained_week / 7 * 100),
    }

def _pdf_canvas(filename, draw_fn):
    from reportlab.lib.pagesizes import A4
    from reportlab.pdfgen import canvas as pdfcanvas
    buf = io.BytesIO()
    c = pdfcanvas.Canvas(buf, pagesize=A4)
    draw_fn(c)
    c.save()
    buf.seek(0)
    safe_name = re.sub(r'[^A-Za-z0-9._-]+', '_', filename)[:80]
    return Response(
        buf.getvalue(),
        mimetype='application/pdf',
        headers={'Content-Disposition': f'attachment; filename="{safe_name}"'},
    )

def _pdf_header(c, title, subtitle=''):
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.colors import HexColor
    w, h = A4
    c.setFillColor(HexColor('#ffffff'))
    c.rect(0, 0, w, h, fill=1, stroke=0)
    c.setFillColor(HexColor('#111111'))
    c.rect(0, h - 80, w, 80, fill=1, stroke=0)
    c.setFillColor(HexColor('#e8ff00'))
    c.rect(0, h - 80, 5, 80, fill=1, stroke=0)
    c.setFillColor(HexColor('#e8ff00'))
    c.setFont('Helvetica-Bold', 20)
    c.drawString(22, h - 32, 'Sahil Panwar')
    c.setFillColor(HexColor('#aaaaaa'))
    c.setFont('Helvetica', 9)
    c.drawString(22, h - 50, 'Personal Training & Nutrition Coaching')
    c.setFillColor(HexColor('#ffffff'))
    c.setFont('Helvetica-Bold', 16)
    c.drawRightString(w - 22, h - 34, title.upper())
    if subtitle:
        c.setFillColor(HexColor('#aaaaaa'))
        c.setFont('Helvetica', 9)
        c.drawRightString(w - 22, h - 50, subtitle[:60])
    return w, h

def _pdf_wrap(c, text, x, y, max_width, font='Helvetica', size=10, leading=14, color='#333333'):
    from reportlab.lib.colors import HexColor
    from reportlab.pdfbase.pdfmetrics import stringWidth
    c.setFont(font, size)
    c.setFillColor(HexColor(color))
    words = (text or '').split()
    line = ''
    for word in words:
        trial = (line + ' ' + word).strip()
        if stringWidth(trial, font, size) <= max_width:
            line = trial
        else:
            c.drawString(x, y, line)
            y -= leading
            line = word
            if y < 48:
                c.showPage()
                y = 780
                c.setFont(font, size)
                c.setFillColor(HexColor(color))
    if line:
        c.drawString(x, y, line)
        y -= leading
    return y

# ── MONGODB ───────────────────────────────────────────────────────────────────
MONGO_URI     = os.environ.get('MONGO_URI', '')
MONGO_DB_NAME = os.environ.get('MONGO_DB_NAME', 'sahil_fitness')

try:
    mongo_client   = MongoClient(MONGO_URI, serverSelectionTimeoutMS=5000)
    mongo_client.admin.command('ping')
    db             = mongo_client[MONGO_DB_NAME]
    config_col     = db['site_config']
    services_col   = db['services']
    testimonials_col = db['testimonials']
    transforms_col = db['transformations']
    blogs_col        = db['blog_posts']
    faqs_col         = db['faqs']
    certs_col        = db['certifications']
    leads_col        = db['leads']
    visits_col       = db['visits']
    gallery_col      = db['gallery']
    users_col        = db['users']
    exercises_col    = db['exercises']
    programs_col     = db['programs']
    checkins_col     = db['check_ins']
    messages_col     = db['messages']
    sessions_col     = db['sessions_book']
    measurements_col = db['measurements']
    payments_col     = db['payments']
    announcements_col= db['announcements']
    push_subs_col    = db['push_subscriptions']
    tips_col         = db['daily_tips']
    goals_col        = db['client_goals']
    report_cards_col = db['report_cards']
    supplements_col  = db['supplements']
    logger.info("MongoDB connected")
except Exception as e:
    logger.error(f"MongoDB failed: {e}")
    mongo_client = None
    db = config_col = services_col = testimonials_col = transforms_col = None
    blogs_col = faqs_col = certs_col = leads_col = visits_col = gallery_col = None
    users_col = exercises_col = programs_col = checkins_col = None
    messages_col = sessions_col = measurements_col = payments_col = announcements_col = None
    push_subs_col = tips_col = goals_col = report_cards_col = supplements_col = None

atexit.register(lambda: mongo_client.close() if mongo_client else None)

def _send_session_reminders():
    """Send email reminders for sessions starting in ~24 hours."""
    if sessions_col is None or users_col is None:
        return
    window_start = datetime.now(timezone.utc) + timedelta(hours=23)
    window_end   = datetime.now(timezone.utc) + timedelta(hours=25)
    upcoming = sessions_col.find({
        'status': {'$in': ['confirmed', 'pending']},
        'datetime': {'$gte': window_start, '$lte': window_end},
        'reminder_sent': {'$ne': True},
    })
    for sess in upcoming:
        user = users_col.find_one({'_id': safe_oid(sess.get('client_id', ''))}, {'email': 1, 'name': 1})
        if not user or not user.get('email'):
            continue
        dt_ist = to_ist(sess.get('datetime'))
        sent = _send_email(
            user['email'],
            'Reminder: Your training session tomorrow',
            f"Hi {user.get('name', 'there')},\n\n"
            f"This is a reminder that your {sess.get('session_type','session')} is scheduled for:\n"
            f"{dt_ist}\n\n"
            f"{('Notes: ' + sess['notes']) if sess.get('notes') else ''}\n\n"
            "See you soon!\n� Sahil Panwar"
        )
        if sent:
            sessions_col.update_one({'_id': sess['_id']}, {'$set': {'reminder_sent': True}})
            logger.info('Reminder sent to %s for session %s', user['email'], sess['_id'])
        else:
            logger.warning('Reminder skipped for session %s (email not configured or send failed)', sess['_id'])

# Only start scheduler in the main process (not in gunicorn worker forks)
if _scheduler_available and _scheduler is not None and os.environ.get('SERVER_SOFTWARE', '').startswith('gunicorn') is False:
    _scheduler.add_job(_send_session_reminders, 'interval', hours=1, id='session_reminders')
    _scheduler.start()
    atexit.register(lambda: _scheduler.shutdown(wait=False) if _scheduler.running else None)

# ── SEED ──────────────────────────────────────────────────────────────────────
def seed():
    if config_col is None:
        return
    if config_col.find_one({'_id': 'main'}):
        return
    config_col.insert_one({
        '_id': 'main',
        'hero_name': 'Sahil Panwar',
        'hero_tagline': 'Transform Your Body. Transform Your Life.',
        'hero_cta': 'Book Free Consultation',
        'hero_image': '',
        'stat_years': '5+',
        'stat_clients': '200+',
        'stat_transformations': '150+',
        'about_bio': 'Certified fitness trainer passionate about helping people achieve their goals.',
        'about_video': '',
        'contact_email': 'sahil@example.com',
        'contact_phone': '+91 9999999999',
        'contact_whatsapp': '+91 9999999999',
        'contact_address': 'New Delhi, India',
        'contact_hours': 'Mon–Sat: 6am–9pm',
        'contact_maps_embed': '',
        'social_instagram': '',
        'social_youtube': '',
        'social_facebook': '',
        'calendly_url': '',
        'lead_magnet_title': 'Free 7-Day Workout Plan',
        'lead_magnet_pdf': '',
        'newsletter_active': True,
        'callmebot_phone': '',
        'callmebot_apikey': '',
        'seo_title': 'Sahil Panwar — Personal Fitness Trainer',
        'seo_desc': 'Transform your body with expert personal training by Sahil Panwar.',
    })
    logger.info("Seeded site_config")

seed()

# ── VISITOR LOGGING ───────────────────────────────────────────────────────────
SKIP = {'/static', '/api', '/favicon'}

@app.before_request
def log_visit():
    if visits_col is None:
        return
    if any(request.path.startswith(p) for p in SKIP):
        return
    visits_col.insert_one({
        'ip':   request.headers.get('X-Forwarded-For', request.remote_addr).split(',')[0].strip()[:45],
        'path': request.path[:200],
        'ua':   request.headers.get('User-Agent', '')[:200],
        'ref':  request.headers.get('Referer', '')[:300],
        'ts':   datetime.now(timezone.utc),
    })

# ── PUBLIC PAGES ──────────────────────────────────────────────────────────────
def get_config():
    return (config_col.find_one({'_id': 'main'}, {'_id': 0}) or {}) if config_col is not None else {}

@app.context_processor
def inject_globals():
    return {'now': datetime.now(timezone.utc), 'cfg': get_config()}

@app.route('/')
def index():
    cfg   = get_config()
    tests = list(testimonials_col.find({'active': True}).sort('order', 1)) if testimonials_col is not None else []
    svcs  = list(services_col.find({}).sort('order', 1)) if services_col is not None else []
    trans = list(transforms_col.find({}).sort('order', 1)) if transforms_col is not None else []
    for t in tests: t['_id'] = str(t['_id'])
    for s in svcs:  s['_id'] = str(s['_id'])
    for t in trans: t['_id'] = str(t['_id'])
    return render_template('index.html', cfg=cfg, testimonials=tests, services=svcs, transformations=trans)

@app.route('/about')
def about():
    cfg   = get_config()
    if cfg.get('about_video'):
        cfg['about_video'] = youtube_embed(cfg['about_video'])
    certs = list(certs_col.find({}).sort('order', 1)) if certs_col is not None else []
    imgs  = list(gallery_col.find({'type': 'about'}).sort('order', 1)) if gallery_col is not None else []
    for c in certs: c['_id'] = str(c['_id'])
    for i in imgs:  i['_id'] = str(i['_id'])
    return render_template('about.html', cfg=cfg, certs=certs, gallery=imgs)

@app.route('/services')
def services():
    cfg  = get_config()
    svcs = list(services_col.find({}).sort('order', 1)) if services_col is not None else []
    faqs = list(faqs_col.find({'section': 'services'}).sort('order', 1)) if faqs_col is not None else []
    for s in svcs: s['_id'] = str(s['_id'])
    for f in faqs: f['_id'] = str(f['_id'])
    return render_template('services.html', cfg=cfg, services=svcs, faqs=faqs)

@app.route('/transformations')
def transformations():
    cfg    = get_config()
    goal   = request.args.get('goal', '')
    query  = {'goal': goal} if goal else {}
    items  = list(transforms_col.find(query).sort('order', 1)) if transforms_col is not None else []
    for i in items: i['_id'] = str(i['_id'])
    return render_template('transformations.html', cfg=cfg, items=items, active_goal=goal)

@app.route('/blog')
def blog():
    cfg   = get_config()
    tag   = request.args.get('tag', '')
    query = {'published': True, 'tags': tag} if tag else {'published': True}
    posts = list(blogs_col.find(query).sort('date', -1)) if blogs_col is not None else []
    for p in posts:
        p['_id']  = str(p['_id'])
        p['date'] = p['date'].strftime('%d %b %Y') if p.get('date') else ''
    return render_template('blog.html', cfg=cfg, posts=posts, active_tag=tag)

@app.route('/blog/<post_id>')
def blog_post(post_id):
    cfg = get_config()
    oid = safe_oid(post_id)
    if not oid:
        return redirect(url_for('blog'))
    post = blogs_col.find_one({'_id': oid}) if blogs_col is not None else None
    if not post:
        return redirect(url_for('blog'))
    post['_id']  = str(post['_id'])
    post['date'] = post['date'].strftime('%d %b %Y') if post.get('date') else ''
    return render_template('blog_post.html', cfg=cfg, post=post)

_maps_embed_cache = {}

def _maps_embed_url(url):
    """Resolve any Google Maps URL to the keyless embeddable /maps/embed form."""
    if not url:
        return ''
    url = url.strip()
    if url in _maps_embed_cache:
        return _maps_embed_cache[url]
    result = _resolve_maps_embed(url)
    _maps_embed_cache[url] = result
    return result

def _resolve_maps_embed(url):
    if not url:
        return ''
    # If user pasted the full iframe HTML, extract the src
    m = re.search(r'src="(https://[^"]+)"', url)
    if m:
        url = m.group(1)
    if '/maps/embed' in url:
        return url
    # Follow short links to get the real URL (GET follows redirects, HEAD may not)
    if 'maps.app.goo.gl' in url or 'goo.gl' in url or 'maps.google' in url:
        try:
            import urllib.request
            req = urllib.request.Request(
                url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=8) as r:
                url = r.url
        except Exception as e:
            logger.warning('Maps URL resolve failed: %s', e)
    # Extract pb= parameter and build keyless embed URL
    m = re.search(r'[?&](pb=[^&\s]+)', url)
    if m:
        return f'https://www.google.com/maps/embed?{m.group(1)}'
    # Extract @lat,lng,zoom
    m = re.search(r'@(-?[\d.]+),(-?[\d.]+),([\d.]+)z', url)
    if m:
        lat, lng, zoom = m.group(1), m.group(2), m.group(3)
        return (
            f'https://www.google.com/maps/embed?pb=!1m14!1m12!1m3!1d10000'
            f'!2d{lng}!3d{lat}!2m3!1f0!2f0!3f0!3m2!1i1024!2i768!4f{zoom}'
            f'!5e0!3m2!1sen!2sin!4v0'
        )
    logger.warning('Could not convert maps URL to embed: %s', url)
    return ''

@app.route('/contact')
def contact():
    cfg  = get_config()
    if cfg.get('contact_maps_embed'):
        cfg['contact_maps_embed'] = _maps_embed_url(cfg['contact_maps_embed'])
    faqs = list(faqs_col.find({'section': {'$in': ['contact', 'general']}}).sort('order', 1)) if faqs_col is not None else []
    for f in faqs: f['_id'] = str(f['_id'])
    return render_template('contact.html', cfg=cfg, faqs=faqs)

@app.route('/gallery')
def gallery():
    cfg   = get_config()
    items = list(gallery_col.find({}).sort('order', 1)) if gallery_col is not None else []
    for i in items:
        i['_id'] = str(i['_id'])
        if i.get('media_type') == 'video' and i.get('video_url'):
            i['video_embed'] = youtube_embed(i['video_url'])
    return render_template('gallery.html', cfg=cfg, images=items)

# ── AUTH ──────────────────────────────────────────────────────────────────────
@app.route('/login', methods=['GET', 'POST'])
@limiter.limit('10 per minute')
def login():
    error = None
    if request.method == 'POST':
        u = request.form.get('username', '').strip()
        p = request.form.get('password', '')
        if u == ADMIN_USERNAME and check_password_hash(ADMIN_PASSWORD_HASH, p):
            session.permanent = True
            session['logged_in'] = True
            return redirect(url_for('admin'))
        error = 'Invalid credentials'
    return render_template('login.html', error=error)

@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('login'))

@app.route('/admin')
@login_required
def admin():
    return render_template('admin.html')

# ── CLIENT AUTH ───────────────────────────────────────────────────────────────
def client_login_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not session.get('client_id'):
            return redirect(url_for('client_login'))
        return f(*args, **kwargs)
    return decorated

@app.route('/register', methods=['GET', 'POST'])
@limiter.limit('5 per hour')
def register():
    if session.get('client_id'):
        return redirect(url_for('client_dashboard'))
    error = None
    if request.method == 'POST':
        name     = s(request.form.get('name', '').strip(), 100)
        email    = s(request.form.get('email', '').strip().lower(), 200)
        password = request.form.get('password', '')
        if not name or not email or not password:
            error = 'All fields are required'
        elif len(password) < 6:
            error = 'Password must be at least 6 characters'
        elif users_col is None:
            error = 'Service unavailable'
        elif users_col.find_one({'email': email}):
            error = 'Email already registered'
        else:
            users_col.insert_one({
                'name':     name,
                'email':    email,
                'password': generate_password_hash(password),
                'role':     'client',
                'active':   True,
                'joined':   datetime.now(timezone.utc),
            })
            _send_whatsapp(f"New client registered: {name} ({email})")
            _send_email(
                email,
                'Welcome to Sahil Panwar!',
                f'Hi {name},\n\nWelcome aboard! Your client account has been created.\n\n'
                f'Login here: {url_for("client_login", _external=True)}\n\n'
                'Your trainer will be in touch soon.\n\u2014 Sahil Panwar'
            )
            return redirect(url_for('client_login', registered='1'))
    return render_template('register.html', error=error)

@app.route('/client/login', methods=['GET', 'POST'])
@limiter.limit('10 per minute')
def client_login():
    if session.get('client_id'):
        return redirect(url_for('client_dashboard'))
    error = None
    if request.method == 'POST':
        email    = s(request.form.get('email', '').strip().lower(), 200)
        password = request.form.get('password', '')
        user     = users_col.find_one({'email': email, 'role': 'client'}) if users_col is not None else None
        if user and user.get('active') and check_password_hash(user['password'], password):
            session.permanent = True
            session['client_id']   = str(user['_id'])
            session['client_name'] = user['name']
            return redirect(url_for('client_dashboard'))
        error = 'Invalid email or password'
    registered = request.args.get('registered')
    reset_ok = request.args.get('reset')
    return render_template('client_login.html', error=error, registered=registered, reset_ok=reset_ok)

@app.route('/client/forgot-password', methods=['GET', 'POST'])
@limiter.limit('5 per hour')
def forgot_password():
    sent = False
    if request.method == 'POST':
        email = s(request.form.get('email', '').strip().lower(), 200)
        sent = True
        if email and users_col is not None:
            user = users_col.find_one({'email': email, 'role': 'client', 'active': True})
            if user:
                token = _issue_reset_token(user)
                link = _reset_url(token)
                _send_email(
                    user['email'],
                    'Reset your training portal password',
                    f'Hi {user.get("name", "there")},\n\n'
                    f'Use this link to reset your password (valid for 1 hour):\n{link}\n\n'
                    'If you did not request this, you can ignore this email.\n'
                )
    return render_template('forgot_password.html', sent=sent)

@app.route('/client/reset-password/<token>', methods=['GET', 'POST'])
@limiter.limit('10 per hour')
def reset_password(token):
    if users_col is None:
        return render_template('reset_password.html', error='Service unavailable', token=token)
    token_hash = _hash_token(token)
    user = users_col.find_one({
        'role': 'client',
        'reset_token_hash': token_hash,
        'reset_token_expires': {'$gt': datetime.now(timezone.utc)},
    })
    if not user:
        return render_template('reset_password.html', error='This reset link is invalid or has expired.', token=token, invalid=True)
    error = None
    if request.method == 'POST':
        password = request.form.get('password', '')
        confirm  = request.form.get('confirm', '')
        if len(password) < 6:
            error = 'Password must be at least 6 characters'
        elif password != confirm:
            error = 'Passwords do not match'
        else:
            users_col.update_one({'_id': user['_id']}, {'$set': {
                'password': generate_password_hash(password),
            }, '$unset': {
                'reset_token_hash': '',
                'reset_token_expires': '',
            }})
            return redirect(url_for('client_login', reset='1'))
    return render_template('reset_password.html', error=error, token=token)

@app.route('/client/logout')
def client_logout():
    session.pop('client_id', None)
    session.pop('client_name', None)
    return redirect(url_for('client_login'))

@app.route('/client/dashboard')
@client_login_required
def client_dashboard():
    cfg  = get_config()
    user = users_col.find_one({'_id': safe_oid(session['client_id'])}) if users_col is not None else None
    if not user:
        session.pop('client_id', None)
        return redirect(url_for('client_login'))
    user['_id'] = str(user['_id'])
    return render_template('client_dashboard.html', cfg=cfg, user=user)

# ── PUBLIC APIs ───────────────────────────────────────────────────────────────
@app.route('/api/contact', methods=['POST'])
@limiter.limit('5 per hour')
def submit_contact():
    if leads_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    name  = s(d.get('name', ''),    100)
    email = s(d.get('email', ''),   200)
    goal  = s(d.get('goal', ''),    200)
    msg   = s(d.get('message', ''), 2000)
    phone = s(d.get('phone', ''),   20)
    if not name or not email or not msg:
        return jsonify({'error': 'Name, email and message required'}), 400
    leads_col.insert_one({
        'name': name, 'email': email, 'goal': goal,
        'message': msg, 'phone': phone, 'type': 'contact',
        'stage': 'new', 'read': False, 'date': datetime.now(timezone.utc)
    })
    _send_whatsapp(
        f"New enquiry from {name}\nPhone: {phone or 'N/A'}\nEmail: {email}\nGoal: {goal or 'N/A'}\nMsg: {msg[:200]}"
    )
    return jsonify({'status': 'sent'})

@app.route('/api/newsletter', methods=['POST'])
@limiter.limit('3 per hour')
def newsletter_signup():
    if leads_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    cfg = get_config()
    if not cfg.get('newsletter_active', True):
        return jsonify({'error': 'Newsletter signups are currently disabled'}), 403
    email = s((request.json or {}).get('email', ''), 200)
    if not email or '@' not in email:
        return jsonify({'error': 'Valid email required'}), 400
    if leads_col.find_one({'email': email, 'type': 'newsletter'}):
        return jsonify({'status': 'already_subscribed'})
    leads_col.insert_one({'email': email, 'type': 'newsletter', 'date': datetime.now(timezone.utc)})
    return jsonify({'status': 'subscribed'})

@app.route('/api/testimonials')
def get_testimonials():
    if testimonials_col is None:
        return jsonify([]), 500
    items = list(testimonials_col.find({'active': True}, {'_id': 0}).sort('order', 1))
    return jsonify(items)

@app.route('/api/services')
def get_services():
    if services_col is None:
        return jsonify([]), 500
    items = list(services_col.find({}, {'_id': 0}).sort('order', 1))
    return jsonify(items)

@app.route('/api/blogs')
def get_blogs():
    if blogs_col is None:
        return jsonify([]), 500
    items = list(blogs_col.find({'published': True}).sort('date', -1).limit(20))
    for i in items:
        i['_id']  = str(i['_id'])
        i['date'] = i['date'].strftime('%d %b %Y') if i.get('date') else ''
        i.pop('body', None)
    return jsonify(items)

# ── ADMIN API — CONFIG ────────────────────────────────────────────────────────
@app.route('/api/admin/config', methods=['GET'])
@login_required
def admin_get_config():
    return jsonify(get_config())

@app.route('/api/admin/config', methods=['POST'])
@login_required
def admin_update_config():
    if config_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    allowed = {
        'hero_name','hero_tagline','hero_cta','hero_image',
        'stat_years','stat_clients','stat_transformations',
        'about_bio','about_photo','about_video',
        'contact_email','contact_phone','contact_whatsapp',
        'contact_address','contact_hours','contact_maps_embed',
        'social_instagram','social_youtube','social_facebook',
        'calendly_url','lead_magnet_title','lead_magnet_pdf',
        'newsletter_active','seo_title','seo_desc',
        'callmebot_phone','callmebot_apikey'
    }
    update = {k: s(str(v), 2000) if isinstance(v, str) else v for k, v in d.items() if k in allowed}
    if not update:
        return jsonify({'error': 'Nothing to update'}), 400
    config_col.update_one({'_id': 'main'}, {'$set': update}, upsert=True)
    return jsonify({'status': 'updated'})

# ── ADMIN API — SERVICES ──────────────────────────────────────────────────────
@app.route('/api/admin/services', methods=['GET'])
@login_required
def admin_get_services():
    if services_col is None:
        return jsonify([]), 500
    items = list(services_col.find({}).sort('order', 1))
    for i in items: i['_id'] = str(i['_id'])
    return jsonify(items)

@app.route('/api/admin/services', methods=['POST'])
@login_required
def admin_add_service():
    if services_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    title = s(d.get('title', ''), 200)
    if not title:
        return jsonify({'error': 'title required'}), 400
    top   = services_col.find_one(sort=[('order', -1)])
    order = (top['order'] + 1) if top else 0
    result = services_col.insert_one({
        'title':    title,
        'subtitle': s(d.get('subtitle', ''), 300),
        'price':    s(d.get('price', ''), 100),
        'features': [s(f, 200) for f in d.get('features', []) if f][:20],
        'badge':    s(d.get('badge', ''), 50),
        'cta':      s(d.get('cta', 'Get Started'), 100),
        'order':    order,
    })
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/services/<sid>', methods=['PUT'])
@login_required
def admin_update_service(sid):
    if services_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(sid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d = request.json or {}
    services_col.update_one({'_id': oid}, {'$set': {
        'title':    s(d.get('title', ''), 200),
        'subtitle': s(d.get('subtitle', ''), 300),
        'price':    s(d.get('price', ''), 100),
        'features': [s(f, 200) for f in d.get('features', []) if f][:20],
        'badge':    s(d.get('badge', ''), 50),
        'cta':      s(d.get('cta', 'Get Started'), 100),
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/services/<sid>', methods=['DELETE'])
@login_required
def admin_delete_service(sid):
    if services_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(sid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    services_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── ADMIN API — TESTIMONIALS ──────────────────────────────────────────────────
@app.route('/api/admin/testimonials', methods=['GET'])
@login_required
def admin_get_testimonials():
    if testimonials_col is None:
        return jsonify([]), 500
    items = list(testimonials_col.find({}).sort('order', 1))
    for i in items: i['_id'] = str(i['_id'])
    return jsonify(items)

@app.route('/api/admin/testimonials', methods=['POST'])
@login_required
def admin_add_testimonial():
    if testimonials_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    name = s(d.get('name', ''), 100)
    text = s(d.get('text', ''), 1000)
    if not name or not text:
        return jsonify({'error': 'name and text required'}), 400
    top   = testimonials_col.find_one(sort=[('order', -1)])
    order = (top['order'] + 1) if top else 0
    result = testimonials_col.insert_one({
        'name':   name,
        'text':   text,
        'rating': max(1, min(5, int(d.get('rating', 5)))),
        'goal':   s(d.get('goal', ''), 100),
        'photo':  s(d.get('photo', ''), 500),
        'active': bool(d.get('active', True)),
        'order':  order,
    })
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/testimonials/<tid>', methods=['PUT'])
@login_required
def admin_update_testimonial(tid):
    if testimonials_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(tid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d = request.json or {}
    testimonials_col.update_one({'_id': oid}, {'$set': {
        'name':   s(d.get('name', ''), 100),
        'text':   s(d.get('text', ''), 1000),
        'rating': max(1, min(5, int(d.get('rating', 5)))),
        'goal':   s(d.get('goal', ''), 100),
        'photo':  s(d.get('photo', ''), 500),
        'active': bool(d.get('active', True)),
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/testimonials/<tid>', methods=['DELETE'])
@login_required
def admin_delete_testimonial(tid):
    if testimonials_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(tid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    testimonials_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── ADMIN API — TRANSFORMATIONS ───────────────────────────────────────────────
@app.route('/api/admin/transformations', methods=['GET'])
@login_required
def admin_get_transforms():
    if transforms_col is None:
        return jsonify([]), 500
    items = list(transforms_col.find({}).sort('order', 1))
    for i in items: i['_id'] = str(i['_id'])
    return jsonify(items)

@app.route('/api/admin/transformations', methods=['POST'])
@login_required
def admin_add_transform():
    if transforms_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    before = s(d.get('before_img', ''), 500)
    after  = s(d.get('after_img', ''), 500)
    if not before or not after:
        return jsonify({'error': 'before_img and after_img required'}), 400
    top   = transforms_col.find_one(sort=[('order', -1)])
    order = (top['order'] + 1) if top else 0
    result = transforms_col.insert_one({
        'before_img':  before,
        'after_img':   after,
        'client_name': s(d.get('client_name', ''), 100),
        'goal':        s(d.get('goal', ''), 100),
        'timeframe':   s(d.get('timeframe', ''), 100),
        'program':     s(d.get('program', ''), 200),
        'story':       s(d.get('story', ''), 1000),
        'order':       order,
    })
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/transformations/<tid>', methods=['PUT'])
@login_required
def admin_update_transform(tid):
    if transforms_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(tid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d = request.json or {}
    transforms_col.update_one({'_id': oid}, {'$set': {
        'before_img':  s(d.get('before_img', ''), 500),
        'after_img':   s(d.get('after_img', ''), 500),
        'client_name': s(d.get('client_name', ''), 100),
        'goal':        s(d.get('goal', ''), 100),
        'timeframe':   s(d.get('timeframe', ''), 100),
        'program':     s(d.get('program', ''), 200),
        'story':       s(d.get('story', ''), 1000),
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/transformations/<tid>', methods=['DELETE'])
@login_required
def admin_delete_transform(tid):
    if transforms_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(tid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    transforms_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── ADMIN API — BLOG ──────────────────────────────────────────────────────────
@app.route('/api/admin/blogs', methods=['GET'])
@login_required
def admin_get_blogs():
    if blogs_col is None:
        return jsonify([]), 500
    items = list(blogs_col.find({}).sort('date', -1))
    for i in items:
        i['_id']  = str(i['_id'])
        i['date'] = i['date'].strftime('%d %b %Y') if i.get('date') else ''
    return jsonify(items)

@app.route('/api/admin/blogs', methods=['POST'])
@login_required
def admin_add_blog():
    if blogs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d     = request.json or {}
    title = s(d.get('title', ''), 200)
    body  = s(d.get('body', ''), 10000)
    if not title or not body:
        return jsonify({'error': 'title and body required'}), 400
    result = blogs_col.insert_one({
        'title':     title,
        'excerpt':   s(d.get('excerpt', ''), 400),
        'body':      body,
        'thumb':     s(d.get('thumb', ''), 500),
        'tags':      [s(t, 50) for t in d.get('tags', []) if t][:10],
        'category':  s(d.get('category', ''), 100),
        'published': bool(d.get('published', False)),
        'date':      datetime.now(timezone.utc),
    })
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/blogs/<bid>', methods=['PUT'])
@login_required
def admin_update_blog(bid):
    if blogs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(bid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d = request.json or {}
    blogs_col.update_one({'_id': oid}, {'$set': {
        'title':     s(d.get('title', ''), 200),
        'excerpt':   s(d.get('excerpt', ''), 400),
        'body':      s(d.get('body', ''), 10000),
        'thumb':     s(d.get('thumb', ''), 500),
        'tags':      [s(t, 50) for t in d.get('tags', []) if t][:10],
        'category':  s(d.get('category', ''), 100),
        'published': bool(d.get('published', False)),
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/blogs/<bid>', methods=['DELETE'])
@login_required
def admin_delete_blog(bid):
    if blogs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(bid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    blogs_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── ADMIN API — FAQs ──────────────────────────────────────────────────────────
@app.route('/api/admin/faqs', methods=['GET'])
@login_required
def admin_get_faqs():
    if faqs_col is None:
        return jsonify([]), 500
    items = list(faqs_col.find({}).sort('order', 1))
    for i in items: i['_id'] = str(i['_id'])
    return jsonify(items)

@app.route('/api/admin/faqs', methods=['POST'])
@login_required
def admin_add_faq():
    if faqs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    q = s(d.get('question', ''), 300)
    a = s(d.get('answer', ''), 1000)
    if not q or not a:
        return jsonify({'error': 'question and answer required'}), 400
    top   = faqs_col.find_one(sort=[('order', -1)])
    order = (top['order'] + 1) if top else 0
    result = faqs_col.insert_one({
        'question': q, 'answer': a,
        'section':  s(d.get('section', 'general'), 50),
        'order':    order,
    })
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/faqs/<fid>', methods=['PUT'])
@login_required
def admin_update_faq(fid):
    if faqs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(fid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d = request.json or {}
    faqs_col.update_one({'_id': oid}, {'$set': {
        'question': s(d.get('question', ''), 300),
        'answer':   s(d.get('answer', ''), 1000),
        'section':  s(d.get('section', 'general'), 50),
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/faqs/<fid>', methods=['DELETE'])
@login_required
def admin_delete_faq(fid):
    if faqs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(fid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    faqs_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── ADMIN API — CERTIFICATIONS ────────────────────────────────────────────────
@app.route('/api/admin/certs', methods=['GET'])
@login_required
def admin_get_certs():
    if certs_col is None:
        return jsonify([]), 500
    items = list(certs_col.find({}).sort('order', 1))
    for i in items: i['_id'] = str(i['_id'])
    return jsonify(items)

@app.route('/api/admin/certs', methods=['POST'])
@login_required
def admin_add_cert():
    if certs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d    = request.json or {}
    name = s(d.get('name', ''), 200)
    if not name:
        return jsonify({'error': 'name required'}), 400
    top   = certs_col.find_one(sort=[('order', -1)])
    order = (top['order'] + 1) if top else 0
    result = certs_col.insert_one({
        'name':  name,
        'org':   s(d.get('org', ''), 200),
        'year':  s(d.get('year', ''), 10),
        'badge': s(d.get('badge', ''), 500),
        'order': order,
    })
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/certs/<cid>', methods=['PUT'])
@login_required
def admin_update_cert(cid):
    if certs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(cid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d = request.json or {}
    certs_col.update_one({'_id': oid}, {'$set': {
        'name':  s(d.get('name', ''), 200),
        'org':   s(d.get('org', ''), 200),
        'year':  s(d.get('year', ''), 10),
        'badge': s(d.get('badge', ''), 500),
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/certs/<cid>', methods=['DELETE'])
@login_required
def admin_delete_cert(cid):
    if certs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(cid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    certs_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── ADMIN API — GALLERY ───────────────────────────────────────────────────────
@app.route('/api/admin/gallery', methods=['GET'])
@login_required
def admin_get_gallery():
    if gallery_col is None:
        return jsonify([]), 500
    items = list(gallery_col.find({}).sort('order', 1))
    for i in items: i['_id'] = str(i['_id'])
    return jsonify(items)

@app.route('/api/admin/gallery', methods=['POST'])
@login_required
def admin_add_gallery():
    if gallery_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d          = request.json or {}
    media_type = s(d.get('media_type', 'image'), 10)
    if media_type == 'video':
        video_url = s(d.get('video_url', ''), 500)
        if not video_url:
            return jsonify({'error': 'video_url required'}), 400
        url = ''
    else:
        url = s(d.get('url', ''), 500)
        if not url:
            return jsonify({'error': 'url required'}), 400
        video_url = ''
    top   = gallery_col.find_one(sort=[('order', -1)])
    order = (top['order'] + 1) if top else 0
    result = gallery_col.insert_one({
        'url':        url,
        'video_url':  video_url,
        'media_type': media_type,
        'caption':    s(d.get('caption', ''), 200),
        'type':       s(d.get('type', 'general'), 50),
        'order':      order,
    })
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/gallery/<gid>', methods=['PUT'])
@login_required
def admin_update_gallery(gid):
    if gallery_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(gid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d = request.json or {}
    gallery_col.update_one({'_id': oid}, {'$set': {
        'caption':   s(d.get('caption', ''), 200),
        'type':      s(d.get('type', 'general'), 50),
        'video_url': s(d.get('video_url', ''), 500),
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/gallery/<gid>', methods=['DELETE'])
@login_required
def admin_delete_gallery(gid):
    if gallery_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(gid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    gallery_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── ADMIN API — LEADS & VISITS ────────────────────────────────────────────────
@app.route('/api/admin/leads')
@login_required
def admin_get_leads():
    if leads_col is None:
        return jsonify([]), 500
    items = list(leads_col.find({}).sort('date', -1))
    for i in items:
        i['_id']  = str(i['_id'])
        i['date'] = to_ist(i.get('date'))
        if i.get('type') == 'contact':
            i['stage'] = i.get('stage') if i.get('stage') in LEAD_STAGES else 'new'
    return jsonify(items)

@app.route('/api/admin/leads/<lid>/stage', methods=['POST'])
@login_required
def admin_set_lead_stage(lid):
    if leads_col is None:
        return jsonify({}), 500
    oid = safe_oid(lid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    stage = s((request.json or {}).get('stage', ''), 30)
    if stage not in LEAD_STAGES:
        return jsonify({'error': 'Invalid stage'}), 400
    leads_col.update_one({'_id': oid}, {'$set': {'stage': stage, 'read': True}})
    return jsonify({'status': 'ok', 'stage': stage})

@app.route('/api/admin/leads/<lid>/read', methods=['POST'])
@login_required
def admin_mark_lead_read(lid):
    if leads_col is None:
        return jsonify({}), 500
    oid = safe_oid(lid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    leads_col.update_one({'_id': oid}, {'$set': {'read': True}})
    return jsonify({'status': 'ok'})

@app.route('/api/admin/leads/<lid>', methods=['DELETE'])
@login_required
def admin_delete_lead(lid):
    if leads_col is None:
        return jsonify({}), 500
    oid = safe_oid(lid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    leads_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

@app.route('/api/admin/visits/stats')
@login_required
def admin_visit_stats():
    if visits_col is None:
        return jsonify({}), 500
    today = datetime.now(timezone.utc).replace(hour=0, minute=0, second=0, microsecond=0)
    return jsonify({
        'total':      visits_col.count_documents({}),
        'today':      visits_col.count_documents({'ts': {'$gte': today}}),
        'week':       visits_col.count_documents({'ts': {'$gte': today - timedelta(days=7)}}),
        'unique_ips': len(visits_col.distinct('ip')),
        'clients':    users_col.count_documents({'role': 'client'}) if users_col is not None else 0,
        'checkins_pending': checkins_col.count_documents({'reviewed': False}) if checkins_col is not None else 0,
    })

# ── CLIENT API — STATS ───────────────────────────────────────────────────────
@app.route('/api/client/stats')
@client_login_required
def client_stats():
    cid = session['client_id']
    checkin_count  = checkins_col.count_documents({'client_id': cid}) if checkins_col is not None else 0
    latest = measurements_col.find_one({'client_id': cid, 'weight': {'$exists': True}}, sort=[('date', -1)]) if measurements_col is not None else None
    latest_weight  = latest['weight'] if latest else None
    pending_feedback = checkins_col.count_documents({'client_id': cid, 'reviewed': True, 'feedback': {'$ne': ''}, 'feedback_seen': {'$ne': True}}) if checkins_col is not None else 0
    adherence = _compute_adherence(cid)
    return jsonify({
        'checkins':        checkin_count,
        'latest_weight':   latest_weight,
        'new_feedback':    pending_feedback,
        **adherence,
    })

# ── CLIENT API — CHECK-INS ───────────────────────────────────────────────────
@app.route('/api/client/checkins', methods=['GET'])
@client_login_required
def client_get_checkins():
    if checkins_col is None:
        return jsonify([]), 500
    items = list(checkins_col.find({'client_id': session['client_id']}).sort('date', -1))
    for i in items:
        i['_id']  = str(i['_id'])
        i['date'] = (i['date'].replace(tzinfo=timezone.utc) + _IST).strftime('%d %b %Y') if i.get('date') else ''
    # mark all reviewed feedback as seen
    checkins_col.update_many(
        {'client_id': session['client_id'], 'reviewed': True, 'feedback': {'$ne': ''}, 'feedback_seen': {'$ne': True}},
        {'$set': {'feedback_seen': True}}
    )
    return jsonify(items)

@app.route('/api/client/checkins', methods=['POST'])
@client_login_required
@limiter.limit('5 per day')
def client_submit_checkin():
    if checkins_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    weight = d.get('weight', '')
    notes  = s(d.get('notes', ''), 1000)
    try:
        energy    = max(1, min(10, int(d.get('energy', 5))))
        sleep     = max(1, min(10, int(d.get('sleep', 5))))
        adherence = max(1, min(10, int(d.get('adherence', 5))))
    except (ValueError, TypeError):
        return jsonify({'error': 'Invalid rating values'}), 400
    result = checkins_col.insert_one({
        'client_id':   session['client_id'],
        'client_name': session.get('client_name', ''),
        'weight':      s(str(weight), 20),
        'energy':      energy,
        'sleep':       sleep,
        'adherence':   adherence,
        'notes':       notes,
        'feedback':    '',
        'reviewed':    False,
        'date':        datetime.now(timezone.utc),
    })
    return jsonify({'status': 'submitted', '_id': str(result.inserted_id)})

# ── ADMIN API — CHECK-INS ─────────────────────────────────────────────────────
@app.route('/api/admin/checkins', methods=['GET'])
@login_required
def admin_get_checkins():
    if checkins_col is None:
        return jsonify([]), 500
    items = list(checkins_col.find({}).sort('date', -1))
    for i in items:
        i['_id']  = str(i['_id'])
        i['date'] = to_ist(i.get('date'))
    return jsonify(items)

@app.route('/api/admin/checkins/<cid>/feedback', methods=['POST'])
@login_required
def admin_checkin_feedback(cid):
    if checkins_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(cid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    feedback = s((request.json or {}).get('feedback', ''), 1000)
    checkins_col.update_one({'_id': oid}, {'$set': {'feedback': feedback, 'reviewed': True}})
    checkin_doc = checkins_col.find_one({'_id': oid}) if checkins_col is not None else None
    if checkin_doc and feedback and users_col is not None:
        fb_client = users_col.find_one({'_id': safe_oid(checkin_doc.get('client_id', ''))}, {'email': 1, 'name': 1})
        if fb_client and fb_client.get('email'):
            _send_email(
                fb_client['email'],
                'Your trainer left feedback on your check-in',
                f'Hi {fb_client.get("name", "there")},\n\n'
                f'Your trainer reviewed your check-in and left feedback:\n\n"{feedback}"\n\n'
                f'Login to view: {url_for("client_dashboard", _external=True)}\n\u2014 Sahil Panwar'
            )
    return jsonify({'status': 'ok'})

@app.route('/api/admin/checkins/<cid>', methods=['DELETE'])
@login_required
def admin_delete_checkin(cid):
    if checkins_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(cid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    checkins_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── CLIENT API — MESSAGES ───────────────────────────────────────────────────
@app.route('/api/client/messages', methods=['GET'])
@client_login_required
def client_get_messages():
    if messages_col is None:
        return jsonify([]), 500
    cid = session['client_id']
    # mark all trainer messages as read by client
    messages_col.update_many(
        {'client_id': cid, 'sender': 'trainer', 'read_by_client': False},
        {'$set': {'read_by_client': True}}
    )
    items = list(messages_col.find({'client_id': cid}).sort('date', 1))
    for i in items:
        i['_id']  = str(i['_id'])
        i['date'] = to_ist(i.get('date'))
    return jsonify(items)

@app.route('/api/client/messages/unread_count')
@client_login_required
def client_unread_message_count():
    if messages_col is None:
        return jsonify({'count': 0})
    count = messages_col.count_documents({
        'client_id': session['client_id'],
        'sender': 'trainer',
        'read_by_client': False,
    })
    return jsonify({'count': count})

@app.route('/api/client/messages', methods=['POST'])
@client_login_required
@limiter.limit('30 per hour')
def client_send_message():
    if messages_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    image_url = None
    if request.content_type and 'multipart' in request.content_type:
        text = s((request.form.get('text') or ''), 2000)
        file = request.files.get('file')
        if file:
            image_url, err = _handle_upload(file)
            if err:
                return jsonify({'error': err}), 400
    else:
        text = s((request.json or {}).get('text', ''), 2000)
    if not text and not image_url:
        return jsonify({'error': 'Message cannot be empty'}), 400
    result = messages_col.insert_one({
        'client_id':       session['client_id'],
        'client_name':     session.get('client_name', ''),
        'sender':          'client',
        'text':            text,
        'image_url':       image_url,
        'date':            datetime.now(timezone.utc),
        'read_by_trainer': False,
        'read_by_client':  True,
    })
    return jsonify({'status': 'sent', '_id': str(result.inserted_id)})

# ── ADMIN API — MESSAGES ───────────────────────────────────────────────────
@app.route('/api/admin/messages')
@login_required
def admin_get_message_threads():
    if messages_col is None:
        return jsonify([]), 500
    # get latest message per client
    pipeline = [
        {'$sort': {'date': -1}},
        {'$group': {
            '_id': '$client_id',
            'client_name':  {'$first': '$client_name'},
            'last_message': {'$first': '$text'},
            'last_date':    {'$first': '$date'},
            'unread':       {'$sum': {'$cond': [{'$eq': ['$read_by_trainer', False]}, 1, 0]}},
        }},
        {'$sort': {'last_date': -1}}
    ]
    threads = list(messages_col.aggregate(pipeline))
    for t in threads:
        t['last_date'] = to_ist(t.get('last_date'))
    return jsonify(threads)

@app.route('/api/admin/messages/<client_id>')
@login_required
def admin_get_thread(client_id):
    if messages_col is None:
        return jsonify([]), 500
    messages_col.update_many(
        {'client_id': client_id, 'read_by_trainer': False},
        {'$set': {'read_by_trainer': True}}
    )
    # mark trainer messages as read by client when client opens their thread
    # (admin opening thread = trainer side, not client side � no change needed here)
    items = list(messages_col.find({'client_id': client_id}).sort('date', 1))
    for i in items:
        i['_id']  = str(i['_id'])
        i['date'] = to_ist(i.get('date'))
    return jsonify(items)

@app.route('/api/admin/messages/<client_id>', methods=['POST'])
@login_required
def admin_reply_message(client_id):
    if messages_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    image_url = None
    if request.content_type and 'multipart' in request.content_type:
        text = s((request.form.get('text') or ''), 2000)
        file = request.files.get('file')
        if file:
            image_url, err = _handle_upload(file)
            if err:
                return jsonify({'error': err}), 400
    else:
        text = s((request.json or {}).get('text', ''), 2000)
    if not text and not image_url:
        return jsonify({'error': 'Message cannot be empty'}), 400
    client = users_col.find_one({'_id': safe_oid(client_id)}) if users_col is not None else None
    result = messages_col.insert_one({
        'client_id':      client_id,
        'client_name':    client['name'] if client else '',
        'sender':         'trainer',
        'text':           text,
        'image_url':      image_url,
        'date':           datetime.now(timezone.utc),
        'read_by_trainer': True,
        'read_by_client':  False,
    })
    if client and client.get('email') and text:
        _send_email(
            client['email'],
            'New message from your trainer \u2014 Sahil Panwar',
            f'Hi {client.get("name", "there")},\n\n'
            f'Your trainer sent you a message:\n\n"{text[:300]}"\n\n'
            f'Login to reply: {url_for("client_dashboard", _external=True)}\n\u2014 Sahil Panwar'
        )
    return jsonify({'status': 'sent', '_id': str(result.inserted_id)})

@app.route('/api/client/messages/<mid>', methods=['DELETE'])
@client_login_required
def client_delete_message(mid):
    if messages_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(mid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    messages_col.delete_one({'_id': oid, 'client_id': session['client_id'], 'sender': 'client'})
    return jsonify({'status': 'deleted'})

@app.route('/api/admin/messages/msg/<mid>', methods=['DELETE'])
@login_required
def admin_delete_message(mid):
    if messages_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(mid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    messages_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── CLIENT API — PROGRESS TRACKING ─────────────────────────────────────────
@app.route('/api/client/progress', methods=['GET'])
@client_login_required
def client_get_progress():
    if measurements_col is None:
        return jsonify([]), 500
    items = list(measurements_col.find({'client_id': session['client_id']}).sort('date', -1).limit(60))
    for i in items:
        i['_id']  = str(i['_id'])
        i['date'] = (i['date'].replace(tzinfo=timezone.utc) + _IST).strftime('%d %b %Y') if i.get('date') else ''
    return jsonify(items)

@app.route('/api/client/progress', methods=['POST'])
@client_login_required
def client_log_progress():
    if measurements_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    entry = {
        'client_id':   session['client_id'],
        'client_name': session.get('client_name', ''),
        'date':        datetime.now(timezone.utc),
        'notes':       s(d.get('notes', ''), 500),
    }
    for field in ['weight', 'chest', 'waist', 'hips', 'arms', 'thighs', 'body_fat']:
        val = d.get(field, '')
        if val != '' and val is not None:
            try:
                entry[field] = round(float(val), 1)
            except (ValueError, TypeError):
                pass
    if len(entry) <= 4:
        return jsonify({'error': 'At least one measurement required'}), 400
    result = measurements_col.insert_one(entry)
    return jsonify({'status': 'logged', '_id': str(result.inserted_id)})

@app.route('/api/client/progress/<pid>', methods=['DELETE'])
@client_login_required
def client_delete_progress(pid):
    if measurements_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    measurements_col.delete_one({'_id': oid, 'client_id': session['client_id']})
    return jsonify({'status': 'deleted'})

# ── ADMIN API — EXERCISES ────────────────────────────────────────────────────
@app.route('/api/admin/exercises', methods=['GET'])
@login_required
def admin_get_exercises():
    if exercises_col is None:
        return jsonify([]), 500
    items = list(exercises_col.find({}).sort('name', 1))
    for i in items: i['_id'] = str(i['_id'])
    return jsonify(items)

@app.route('/api/admin/exercises', methods=['POST'])
@login_required
def admin_add_exercise():
    if exercises_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d    = request.json or {}
    name = s(d.get('name', ''), 200)
    if not name:
        return jsonify({'error': 'name required'}), 400
    result = exercises_col.insert_one({
        'name':        name,
        'muscle':      s(d.get('muscle', ''), 100),
        'equipment':   s(d.get('equipment', ''), 100),
        'description': s(d.get('description', ''), 1000),
        'video_url':   s(d.get('video_url', ''), 500),
        'difficulty':  s(d.get('difficulty', 'intermediate'), 50),
    })
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/exercises/<eid>', methods=['PUT'])
@login_required
def admin_update_exercise(eid):
    if exercises_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(eid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d = request.json or {}
    exercises_col.update_one({'_id': oid}, {'$set': {
        'name':        s(d.get('name', ''), 200),
        'muscle':      s(d.get('muscle', ''), 100),
        'equipment':   s(d.get('equipment', ''), 100),
        'description': s(d.get('description', ''), 1000),
        'video_url':   s(d.get('video_url', ''), 500),
        'difficulty':  s(d.get('difficulty', 'intermediate'), 50),
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/exercises/<eid>', methods=['DELETE'])
@login_required
def admin_delete_exercise(eid):
    if exercises_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(eid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    exercises_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── ADMIN API — WORKOUT PROGRAMS ──────────────────────────────────────────────
@app.route('/api/admin/programs', methods=['GET'])
@login_required
def admin_get_programs():
    if programs_col is None:
        return jsonify([]), 500
    items = list(programs_col.find({}).sort('created', -1))
    for i in items:
        i['_id']     = str(i['_id'])
        i['created'] = i['created'].strftime('%d %b %Y') if i.get('created') else ''
    return jsonify(items)

@app.route('/api/admin/programs', methods=['POST'])
@login_required
def admin_add_program():
    if programs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d    = request.json or {}
    name = s(d.get('name', ''), 200)
    if not name:
        return jsonify({'error': 'name required'}), 400
    # days: list of {day_label, exercises: [{exercise_id, sets, reps, weight, rest, notes}]}
    days = []
    for day in d.get('days', []):
        exs = []
        for ex in day.get('exercises', []):
            exs.append({
                'exercise_id':   s(str(ex.get('exercise_id', '')), 50),
                'exercise_name': s(ex.get('exercise_name', ''), 200),
                'sets':  s(str(ex.get('sets', '')), 20),
                'reps':  s(str(ex.get('reps', '')), 20),
                'weight': s(str(ex.get('weight', '')), 20),
                'rest':  s(str(ex.get('rest', '')), 20),
                'notes': s(ex.get('notes', ''), 300),
            })
        days.append({'day_label': s(day.get('day_label', ''), 100), 'exercises': exs})
    result = programs_col.insert_one({
        'name':        name,
        'description': s(d.get('description', ''), 500),
        'days':        days,
        'created':     datetime.now(timezone.utc),
    })
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/programs/<pid>', methods=['PUT'])
@login_required
def admin_update_program(pid):
    if programs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d    = request.json or {}
    name = s(d.get('name', ''), 200)
    if not name:
        return jsonify({'error': 'name required'}), 400
    days = []
    for day in d.get('days', []):
        exs = []
        for ex in day.get('exercises', []):
            exs.append({
                'exercise_id':   s(str(ex.get('exercise_id', '')), 50),
                'exercise_name': s(ex.get('exercise_name', ''), 200),
                'sets':  s(str(ex.get('sets', '')), 20),
                'reps':  s(str(ex.get('reps', '')), 20),
                'weight': s(str(ex.get('weight', '')), 20),
                'rest':  s(str(ex.get('rest', '')), 20),
                'notes': s(ex.get('notes', ''), 300),
            })
        days.append({'day_label': s(day.get('day_label', ''), 100), 'exercises': exs})
    programs_col.update_one({'_id': oid}, {'$set': {
        'name': name,
        'description': s(d.get('description', ''), 500),
        'days': days,
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/programs/<pid>', methods=['DELETE'])
@login_required
def admin_delete_program(pid):
    if programs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    programs_col.delete_one({'_id': oid})
    if users_col is not None:
        users_col.update_many(
            {'assigned_program_id': str(oid)},
            {'$unset': {'assigned_program_id': '', 'assigned_program_name': ''}}
        )
    return jsonify({'status': 'deleted'})

@app.route('/api/admin/programs/<pid>/assign', methods=['POST'])
@login_required
def admin_assign_program(pid):
    if users_col is None or programs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    client_id = s((request.json or {}).get('client_id', ''), 50)
    if not client_id:
        return jsonify({'error': 'client_id required'}), 400
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid program id'}), 400
    program = programs_col.find_one({'_id': oid})
    if not program:
        return jsonify({'error': 'Program not found'}), 404
    users_col.update_one(
        {'_id': safe_oid(client_id)},
        {'$set': {'assigned_program_id': str(oid), 'assigned_program_name': program['name']}}
    )
    prog_client = users_col.find_one({'_id': safe_oid(client_id)}, {'email': 1, 'name': 1})
    if prog_client and prog_client.get('email'):
        _send_email(
            prog_client['email'],
            'New workout program assigned \u2014 Sahil Panwar',
            f'Hi {prog_client.get("name", "there")},\n\n'
            f'Your trainer assigned you a new workout program: "{program["name"]}"\n\n'
            f'Login to view: {url_for("client_dashboard", _external=True)}\n\u2014 Sahil Panwar'
        )
    return jsonify({'status': 'assigned'})

# ── CLIENT API — WORKOUT PROGRAM ──────────────────────────────────────────────
@app.route('/api/client/program')
@client_login_required
def client_get_program():
    if users_col is None or programs_col is None:
        return jsonify({}), 500
    user = users_col.find_one({'_id': safe_oid(session['client_id'])})
    if not user or not user.get('assigned_program_id'):
        return jsonify({})
    oid = safe_oid(user['assigned_program_id'])
    program = programs_col.find_one({'_id': oid}) if oid else None
    if not program:
        return jsonify({})
    program['_id'] = str(program['_id'])
    program.pop('created', None)
    by_id, by_name = _exercise_video_index()
    for day in program.get('days') or []:
        for ex in day.get('exercises') or []:
            embed = by_id.get(ex.get('exercise_id', '')) or by_name.get((ex.get('exercise_name') or '').strip().lower(), '')
            if embed:
                ex['video_embed'] = embed
    return jsonify(program)

# ── ADMIN API — NUTRITION ────────────────────────────────────────────────────
@app.route('/api/admin/meal_plans', methods=['GET'])
@login_required
def admin_get_meal_plans():
    if db is None:
        return jsonify([]), 500
    items = list(db['meal_plans'].find({}).sort('created', -1))
    for i in items:
        i['_id']     = str(i['_id'])
        i['created'] = i['created'].strftime('%d %b %Y') if i.get('created') else ''
    return jsonify(items)

@app.route('/api/admin/meal_plans', methods=['POST'])
@login_required
def admin_add_meal_plan():
    if db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d    = request.json or {}
    name = s(d.get('name', ''), 200)
    if not name:
        return jsonify({'error': 'name required'}), 400
    meals = []
    for meal in d.get('meals', []):
        items_list = []
        for item in meal.get('items', []):
            items_list.append({
                'name':     s(item.get('name', ''), 200),
                'amount':   s(item.get('amount', ''), 100),
                'calories': s(str(item.get('calories', '')), 20),
                'protein':  s(str(item.get('protein', '')), 20),
                'carbs':    s(str(item.get('carbs', '')), 20),
                'fats':     s(str(item.get('fats', '')), 20),
            })
        meals.append({'meal_label': s(meal.get('meal_label', ''), 100), 'items': items_list})
    macros = d.get('macros', {})
    result = db['meal_plans'].insert_one({
        'name':        name,
        'description': s(d.get('description', ''), 500),
        'meals':       meals,
        'macros': {
            'calories': s(str(macros.get('calories', '')), 20),
            'protein':  s(str(macros.get('protein', '')), 20),
            'carbs':    s(str(macros.get('carbs', '')), 20),
            'fats':     s(str(macros.get('fats', '')), 20),
        },
        'created': datetime.now(timezone.utc),
    })
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/meal_plans/<pid>', methods=['PUT'])
@login_required
def admin_update_meal_plan(pid):
    if db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d    = request.json or {}
    name = s(d.get('name', ''), 200)
    if not name:
        return jsonify({'error': 'name required'}), 400
    meals = []
    for meal in d.get('meals', []):
        items_list = []
        for item in meal.get('items', []):
            items_list.append({
                'name':     s(item.get('name', ''), 200),
                'amount':   s(item.get('amount', ''), 100),
                'calories': s(str(item.get('calories', '')), 20),
                'protein':  s(str(item.get('protein', '')), 20),
                'carbs':    s(str(item.get('carbs', '')), 20),
                'fats':     s(str(item.get('fats', '')), 20),
            })
        meals.append({'meal_label': s(meal.get('meal_label', ''), 100), 'items': items_list})
    macros = d.get('macros', {})
    db['meal_plans'].update_one({'_id': oid}, {'$set': {
        'name':        name,
        'description': s(d.get('description', ''), 500),
        'meals':       meals,
        'macros': {
            'calories': s(str(macros.get('calories', '')), 20),
            'protein':  s(str(macros.get('protein', '')), 20),
            'carbs':    s(str(macros.get('carbs', '')), 20),
            'fats':     s(str(macros.get('fats', '')), 20),
        },
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/meal_plans/<pid>', methods=['DELETE'])
@login_required
def admin_delete_meal_plan(pid):
    if db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    db['meal_plans'].delete_one({'_id': oid})
    if users_col is not None:
        users_col.update_many(
            {'assigned_meal_plan_id': str(oid)},
            {'$unset': {'assigned_meal_plan_id': '', 'assigned_meal_plan_name': ''}}
        )
    return jsonify({'status': 'deleted'})

@app.route('/api/admin/meal_plans/<pid>/assign', methods=['POST'])
@login_required
def admin_assign_meal_plan(pid):
    if users_col is None or db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    client_id = s((request.json or {}).get('client_id', ''), 50)
    if not client_id:
        return jsonify({'error': 'client_id required'}), 400
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    plan = db['meal_plans'].find_one({'_id': oid})
    if not plan:
        return jsonify({'error': 'Plan not found'}), 404
    users_col.update_one(
        {'_id': safe_oid(client_id)},
        {'$set': {'assigned_meal_plan_id': str(oid), 'assigned_meal_plan_name': plan['name']}}
    )
    meal_client = users_col.find_one({'_id': safe_oid(client_id)}, {'email': 1, 'name': 1})
    if meal_client and meal_client.get('email'):
        _send_email(
            meal_client['email'],
            'New meal plan assigned \u2014 Sahil Panwar',
            f'Hi {meal_client.get("name", "there")},\n\n'
            f'Your trainer assigned you a new meal plan: "{plan["name"]}"\n\n'
            f'Login to view: {url_for("client_dashboard", _external=True)}\n\u2014 Sahil Panwar'
        )
    return jsonify({'status': 'assigned'})

# ── CLIENT API — NUTRITION ────────────────────────────────────────────────────
@app.route('/api/client/meal_plan')
@client_login_required
def client_get_meal_plan():
    if users_col is None or db is None:
        return jsonify({}), 500
    user = users_col.find_one({'_id': safe_oid(session['client_id'])})
    if not user or not user.get('assigned_meal_plan_id'):
        return jsonify({})
    oid  = safe_oid(user['assigned_meal_plan_id'])
    plan = db['meal_plans'].find_one({'_id': oid}) if oid else None
    if not plan:
        return jsonify({})
    plan['_id'] = str(plan['_id'])
    plan.pop('created', None)
    return jsonify(plan)

def _assigned_program(user):
    oid = safe_oid(user.get('assigned_program_id'))
    return programs_col.find_one({'_id': oid}) if oid and programs_col is not None else None

def _assigned_meal_plan(user):
    if db is None:
        return None
    oid = safe_oid(user.get('assigned_meal_plan_id'))
    return db['meal_plans'].find_one({'_id': oid}) if oid else None

@app.route('/api/lead_magnet_pdf')
def lead_magnet_pdf_redirect():
    cfg = get_config()
    pdf_url = cfg.get('lead_magnet_pdf', '').strip()
    if not pdf_url:
        return jsonify({'error': 'Not available'}), 404
    return redirect(pdf_url)

@app.route('/api/client/program/pdf')
@client_login_required
def client_program_pdf():
    user = users_col.find_one({'_id': safe_oid(session['client_id'])}) if users_col is not None else None
    program = _assigned_program(user) if user else None
    if not program:
        return jsonify({'error': 'No program assigned'}), 404
    client_name = (user or {}).get('name', 'Client')

    def draw(c):
        from reportlab.lib.pagesizes import A4
        from reportlab.lib.colors import HexColor
        w, h = _pdf_header(c, program.get('name') or 'Workout Program', client_name)
        y = h - 100
        desc = program.get('description') or ''
        if desc:
            y = _pdf_wrap(c, desc, 36, y, w - 72, size=10, color='#555555')
            y -= 6
        for day in program.get('days') or []:
            if y < 90:
                c.showPage()
                y = h - 50
            c.setFillColor(HexColor('#e8ff00'))
            c.setFont('Helvetica-Bold', 12)
            c.drawString(36, y, (day.get('day_label') or 'Day')[:60])
            y -= 18
            for ex in day.get('exercises') or []:
                if y < 60:
                    c.showPage()
                    y = h - 50
                name = ex.get('exercise_name') or 'Exercise'
                bits = [b for b in [
                    f"{ex.get('sets')} sets" if ex.get('sets') else '',
                    f"{ex.get('reps')} reps" if ex.get('reps') else '',
                    f"{ex.get('weight')} kg" if ex.get('weight') else '',
                    f"rest {ex.get('rest')}" if ex.get('rest') else '',
                ] if b]
                line = name + (('  �  ' + ', '.join(bits)) if bits else '')
                y = _pdf_wrap(c, line, 48, y, w - 84, font='Helvetica-Bold', size=10, color='#111111')
                if ex.get('notes'):
                    y = _pdf_wrap(c, ex['notes'], 48, y, w - 84, size=9, color='#666666')
            y -= 8
        c.setFillColor(HexColor('#999999'))
        c.setFont('Helvetica', 8)
        c.drawString(36, 28, 'For gym use � Sahil Panwar')

    return _pdf_canvas((program.get('name') or 'workout') + '.pdf', draw)

@app.route('/api/client/meal_plan/pdf')
@client_login_required
def client_meal_plan_pdf():
    user = users_col.find_one({'_id': safe_oid(session['client_id'])}) if users_col is not None else None
    plan = _assigned_meal_plan(user) if user else None
    if not plan:
        return jsonify({'error': 'No meal plan assigned'}), 404
    client_name = (user or {}).get('name', 'Client')

    def draw(c):
        from reportlab.lib.pagesizes import A4
        from reportlab.lib.colors import HexColor
        w, h = _pdf_header(c, plan.get('name') or 'Meal Plan', client_name)
        y = h - 100
        macros = plan.get('macros') or {}
        macro_line = '  �  '.join([b for b in [
            f"{macros.get('calories')} kcal" if macros.get('calories') else '',
            f"P {macros.get('protein')}g" if macros.get('protein') else '',
            f"C {macros.get('carbs')}g" if macros.get('carbs') else '',
            f"F {macros.get('fats')}g" if macros.get('fats') else '',
        ] if b])
        if macro_line:
            y = _pdf_wrap(c, macro_line, 36, y, w - 72, font='Helvetica-Bold', size=11, color='#333333')
            y -= 4
        if plan.get('description'):
            y = _pdf_wrap(c, plan['description'], 36, y, w - 72, size=10, color='#555555')
            y -= 6
        for meal in plan.get('meals') or []:
            if y < 90:
                c.showPage()
                y = h - 50
            c.setFillColor(HexColor('#e8ff00'))
            c.setFont('Helvetica-Bold', 12)
            c.drawString(36, y, (meal.get('meal_label') or 'Meal')[:60])
            y -= 16
            for item in meal.get('items') or []:
                if y < 60:
                    c.showPage()
                    y = h - 50
                name = item.get('name') or 'Food'
                if item.get('amount'):
                    name += f" ({item['amount']})"
                bits = [b for b in [
                    f"{item.get('calories')} kcal" if item.get('calories') else '',
                    f"P{item.get('protein')}g" if item.get('protein') else '',
                    f"C{item.get('carbs')}g" if item.get('carbs') else '',
                    f"F{item.get('fats')}g" if item.get('fats') else '',
                ] if b]
                line = name + (('  �  ' + ', '.join(bits)) if bits else '')
                y = _pdf_wrap(c, line, 48, y, w - 84, size=10, color='#111111')
            y -= 8
        c.setFillColor(HexColor('#999999'))
        c.setFont('Helvetica', 8)
        c.drawString(36, 28, 'For gym use � Sahil Panwar')

    return _pdf_canvas((plan.get('name') or 'meal-plan') + '.pdf', draw)

@app.route('/api/client/water', methods=['GET'])
@client_login_required
def client_get_water():
    if db is None:
        return jsonify({'glasses': 0}), 500
    today = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    rec   = db['water_log'].find_one({'client_id': session['client_id'], 'date': today})
    return jsonify({'glasses': rec['glasses'] if rec else 0})

@app.route('/api/client/water', methods=['POST'])
@client_login_required
def client_log_water():
    if db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    try:
        glasses = max(0, min(20, int((request.json or {}).get('glasses', 0))))
    except (ValueError, TypeError):
        return jsonify({'error': 'Invalid value'}), 400
    today = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    db['water_log'].update_one(
        {'client_id': session['client_id'], 'date': today},
        {'$set': {'glasses': glasses, 'client_id': session['client_id'], 'date': today}},
        upsert=True
    )
    return jsonify({'status': 'ok', 'glasses': glasses})

# ── ADMIN API — CLIENT PROGRESS ───────────────────────────────────────────────
@app.route('/api/admin/clients')
@login_required
def admin_get_clients():
    if users_col is None:
        return jsonify([]), 500
    items = list(users_col.find({'role': 'client'}, {'password': 0}).sort('joined', -1))
    for i in items:
        i['_id']    = str(i['_id'])
        i['joined'] = i['joined'].strftime('%d %b %Y') if i.get('joined') else ''
    return jsonify(items)

@app.route('/api/admin/clients/<cid>/active', methods=['POST'])
@login_required
def admin_set_client_active(cid):
    if users_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(cid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    active = bool((request.json or {}).get('active', True))
    users_col.update_one({'_id': oid, 'role': 'client'}, {'$set': {'active': active}})
    return jsonify({'status': 'updated', 'active': active})

@app.route('/api/admin/clients/<cid>/gender', methods=['POST'])
@login_required
def admin_set_client_gender(cid):
    if users_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(cid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    gender = s((request.json or {}).get('gender', ''), 10)
    if gender not in ('male', 'female'):
        return jsonify({'error': 'Invalid gender'}), 400
    users_col.update_one({'_id': oid}, {'$set': {'gender': gender}})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/clients/<cid>/reset-link', methods=['POST'])
@login_required
def admin_client_reset_link(cid):
    if users_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(cid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    user = users_col.find_one({'_id': oid, 'role': 'client'})
    if not user:
        return jsonify({'error': 'Client not found'}), 404
    token = _issue_reset_token(user)
    link = _reset_url(token)
    emailed = _send_email(
        user.get('email', ''),
        'Reset your training portal password',
        f'Hi {user.get("name", "there")},\n\n'
        f'Your trainer generated a password reset link (valid for 1 hour):\n{link}\n'
    )
    return jsonify({'url': link, 'emailed': emailed})

@app.route('/api/admin/clients/<cid>/password', methods=['POST'])
@login_required
def admin_set_client_password(cid):
    if users_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(cid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    password = (request.json or {}).get('password', '')
    if len(password) < 6:
        return jsonify({'error': 'Password must be at least 6 characters'}), 400
    users_col.update_one({'_id': oid, 'role': 'client'}, {'$set': {
        'password': generate_password_hash(password),
    }, '$unset': {
        'reset_token_hash': '',
        'reset_token_expires': '',
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/clients/<cid>/progress')
@login_required
def admin_client_progress(cid):
    if measurements_col is None:
        return jsonify([]), 500
    items = list(measurements_col.find({'client_id': cid}).sort('date', -1).limit(60))
    for i in items:
        i['_id']  = str(i['_id'])
        i['date'] = i['date'].strftime('%d %b %Y') if i.get('date') else ''
    return jsonify(items)

# ── CLIENT API — SESSION BOOKING ────────────────────────────────────────────
@app.route('/api/client/sessions', methods=['GET'])
@client_login_required
def client_get_sessions():
    if sessions_col is None:
        return jsonify([]), 500
    items = list(sessions_col.find({'client_id': session['client_id']}).sort('datetime', -1))
    for i in items:
        i['_id'] = str(i['_id'])
        i['datetime'] = to_ist(i.get('datetime'))
    return jsonify(items)

@app.route('/api/client/sessions', methods=['POST'])
@client_login_required
@limiter.limit('10 per day')
def client_book_session():
    if sessions_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    date_str = s(d.get('date', ''), 20)
    time_str = s(d.get('time', ''), 10)
    stype    = s(d.get('session_type', 'In-Person'), 100)
    notes    = s(d.get('notes', ''), 500)
    if not date_str or not time_str:
        return jsonify({'error': 'Date and time required'}), 400
    try:
        dt = datetime.strptime(f'{date_str} {time_str}', '%Y-%m-%d %H:%M')
        dt = dt.replace(tzinfo=timezone.utc)
    except ValueError:
        return jsonify({'error': 'Invalid date/time format'}), 400
    result = sessions_col.insert_one({
        'client_id':    session['client_id'],
        'client_name':  session.get('client_name', ''),
        'datetime':     dt,
        'session_type': stype,
        'notes':        notes,
        'status':       'pending',
        'created':      datetime.now(timezone.utc),
    })
    return jsonify({'status': 'booked', '_id': str(result.inserted_id)})

@app.route('/api/client/sessions/<sid>', methods=['DELETE'])
@client_login_required
def client_cancel_session(sid):
    if sessions_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(sid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    sessions_col.delete_one({'_id': oid, 'client_id': session['client_id']})
    return jsonify({'status': 'cancelled'})

# ── ADMIN API — SESSIONS ──────────────────────────────────────────────────────
@app.route('/api/admin/sessions', methods=['POST'])
@login_required
def admin_create_session():
    if sessions_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    date_str    = s(d.get('date', ''), 20)
    time_str    = s(d.get('time', ''), 10)
    stype       = s(d.get('session_type', 'In-Person'), 100)
    notes       = s(d.get('notes', ''), 500)
    client_name = s(d.get('client_name', 'Walk-in'), 200)
    status      = s(d.get('status', 'confirmed'), 20)
    if status not in ('confirmed', 'pending', 'completed'):
        status = 'confirmed'
    if not date_str or not time_str:
        return jsonify({'error': 'Date and time required'}), 400
    try:
        dt = datetime.strptime(f'{date_str} {time_str}', '%Y-%m-%d %H:%M')
        dt = dt.replace(tzinfo=timezone.utc)
    except ValueError:
        return jsonify({'error': 'Invalid date/time format'}), 400
    result = sessions_col.insert_one({
        'client_id':     None,
        'client_name':   client_name,
        'datetime':      dt,
        'session_type':  stype,
        'notes':         notes,
        'status':        status,
        'created':       datetime.now(timezone.utc),
        'admin_created': True,
    })
    return jsonify({'status': 'created', '_id': str(result.inserted_id)})

@app.route('/api/admin/sessions')
@login_required
def admin_get_sessions():
    if sessions_col is None:
        return jsonify([]), 500
    items = list(sessions_col.find({}).sort('created', -1))
    for i in items:
        i['_id']      = str(i['_id'])
        try:
            i['datetime'] = to_ist(i.get('datetime'))
        except Exception:
            i['datetime'] = str(i.get('datetime', ''))
    return jsonify(items)

@app.route('/api/admin/sessions/<sid>', methods=['POST'])
@login_required
def admin_update_session_status(sid):
    if sessions_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(sid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    status_val = s((request.json or {}).get('status', ''), 20)
    if status_val not in ('confirmed', 'cancelled', 'pending', 'completed'):
        return jsonify({'error': 'Invalid status'}), 400
    sessions_col.update_one({'_id': oid}, {'$set': {'status': status_val}})
    sess_doc = sessions_col.find_one({'_id': oid})
    if sess_doc and users_col is not None:
        sess_client = users_col.find_one({'_id': safe_oid(sess_doc.get('client_id', ''))}, {'email': 1, 'name': 1})
        if sess_client and sess_client.get('email'):
            dt_ist = to_ist(sess_doc.get('datetime'))
            _send_email(
                sess_client['email'],
                f'Your session has been {status_val} \u2014 Sahil Panwar',
                f'Hi {sess_client.get("name", "there")},\n\n'
                f'Your {sess_doc.get("session_type", "session")} scheduled for {dt_ist} has been {status_val}.\n\n'
                f'Login to view: {url_for("client_dashboard", _external=True)}\n\u2014 Sahil Panwar'
            )
    return jsonify({'status': 'updated'})

@app.route('/api/admin/sessions/<sid>', methods=['DELETE'])
@login_required
def admin_delete_session(sid):
    if sessions_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(sid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    sessions_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── ADMIN API — PAYMENTS / INVOICES ─────────────────────────────────────────
@app.route('/api/admin/invoices', methods=['GET'])
@login_required
def admin_get_invoices():
    if payments_col is None:
        return jsonify([]), 200
    docs = list(payments_col.find({}).sort('created', -1))
    for d in docs:
        d['_id'] = str(d['_id'])
    return jsonify(docs)

@app.route('/api/admin/invoices', methods=['POST'])
@login_required
def admin_create_invoice():
    if payments_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    b = request.json or {}
    client_id   = s(b.get('client_id', ''), 100)
    client_name = s(b.get('client_name', ''), 200)
    amount      = b.get('amount', 0)
    description = s(b.get('description', ''), 500)
    due_date    = s(b.get('due_date', ''), 20)
    if not client_id or not amount:
        return jsonify({'error': 'client_id and amount required'}), 400
    doc = {
        'client_id':   client_id,
        'client_name': client_name,
        'amount':      float(amount),
        'description': description,
        'due_date':    due_date,
        'status':      'unpaid',
        'created':     datetime.now(timezone.utc).strftime('%Y-%m-%d'),
    }
    result = payments_col.insert_one(doc)
    doc['_id'] = str(result.inserted_id)
    if users_col is not None:
        inv_client = users_col.find_one({'_id': safe_oid(client_id)}, {'email': 1, 'name': 1})
        if inv_client and inv_client.get('email'):
            _send_email(
                inv_client['email'],
                'New invoice from Sahil Panwar',
                f'Hi {inv_client.get("name", "there")},\n\n'
                f'A new invoice has been raised:\n\n'
                'Description: ' + (description or '�') + '\nAmount: Rs.' + f'{float(amount):.2f}' + '\nDue: ' + (due_date or '�') + '\n\n'
                f'Login to view: {url_for("client_dashboard", _external=True)}\n\u2014 Sahil Panwar'
            )
    return jsonify(doc), 201

@app.route('/api/admin/invoices/<iid>/mark_paid', methods=['POST'])
@login_required
def admin_mark_paid(iid):
    if payments_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(iid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    b = request.json or {}
    payments_col.update_one({'_id': oid}, {'$set': {
        'status':          'paid',
        'paid_date':       datetime.now(timezone.utc).strftime('%Y-%m-%d'),
        'payment_method':  s(b.get('method', 'UPI'), 50),
        'transaction_ref': s(b.get('ref', ''), 200),
    }})
    paid_inv = payments_col.find_one({'_id': oid})
    if paid_inv and users_col is not None:
        paid_client = users_col.find_one({'_id': safe_oid(paid_inv.get('client_id', ''))}, {'email': 1, 'name': 1})
        if paid_client and paid_client.get('email'):
            _send_email(
                paid_client['email'],
                'Payment confirmed \u2014 Sahil Panwar',
                f'Hi {paid_client.get("name", "there")},\n\n'
                f'Your payment of Rs.{paid_inv.get("amount", 0):.2f} has been received. Thank you!\n\n'
                'Method: ' + b.get('method', 'UPI') + '\nRef: ' + (b.get('ref') or '�') + '\n\n'
                f'Login to view receipt: {url_for("client_dashboard", _external=True)}\n\u2014 Sahil Panwar'
            )
    return jsonify({'status': 'updated'})

@app.route('/api/admin/invoices/<iid>', methods=['DELETE'])
@login_required
def admin_delete_invoice(iid):
    if payments_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(iid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    payments_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

# ── CLIENT API — SELF PROGRESS PHOTOS ────────────────────────────────────────
@app.route('/api/client/progress_photos', methods=['GET'])
@client_login_required
def client_get_progress_photos():
    if db is None:
        return jsonify([]), 500
    items = list(db['client_self_photos'].find({'client_id': session['client_id']}).sort('date', -1))
    for i in items:
        i['_id'] = str(i['_id'])
        i['date'] = to_ist(i.get('date'))
    return jsonify(items)

@app.route('/api/client/progress_photos', methods=['POST'])
@client_login_required
@limiter.limit('30 per hour')
def client_upload_progress_photo():
    if db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    url, err = _handle_upload(request.files.get('file'))
    if err:
        return jsonify({'error': err}), 400
    caption = s((request.form.get('caption') or ''), 200)
    db['client_self_photos'].insert_one({
        'client_id': session['client_id'],
        'url': url,
        'caption': caption,
        'date': datetime.now(timezone.utc),
    })
    return jsonify({'status': 'uploaded', 'url': url})

@app.route('/api/client/progress_photos/<pid>', methods=['DELETE'])
@client_login_required
def client_delete_progress_photo(pid):
    if db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    db['client_self_photos'].delete_one({'_id': oid, 'client_id': session['client_id']})
    return jsonify({'status': 'deleted'})

# ── CLIENT API — INVOICES ─────────────────────────────────────────────────────
@app.route('/api/client/invoices', methods=['GET'])
@client_login_required
def client_get_invoices():
    if payments_col is None:
        return jsonify([]), 200
    cid  = session.get('client_id')
    docs = list(payments_col.find({'client_id': cid}).sort('created', -1))
    for d in docs:
        d['_id'] = str(d['_id'])
    return jsonify(docs)

# ── RUN ───────────────────────────────────────────────────────────────────────

@app.route('/api/client/profile/avatar', methods=['POST'])
@client_login_required
@limiter.limit('10 per hour')
def client_upload_avatar():
    if users_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    url, err = _handle_upload(request.files.get('file'))
    if err:
        return jsonify({'error': err}), 400
    users_col.update_one({'_id': safe_oid(session['client_id'])}, {'$set': {'avatar_url': url}})
    return jsonify({'url': url})

@app.route('/api/client/profile', methods=['POST'])
@client_login_required
def client_update_profile():
    if users_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    gender = s(d.get('gender', ''), 10)
    if gender not in ('male', 'female'):
        return jsonify({'error': 'Invalid gender'}), 400
    users_col.update_one({'_id': safe_oid(session['client_id'])}, {'$set': {'gender': gender}})
    return jsonify({'status': 'updated'})

# -- CLIENT API � FITNESS PROFILE ---------------------------------------------
@app.route('/api/client/fitness_profile', methods=['GET'])
@client_login_required
def client_get_fitness_profile():
    if users_col is None:
        return jsonify({}), 500
    doc = users_col.find_one({'_id': safe_oid(session['client_id'])}, {'fitness_profile': 1})
    return jsonify(doc.get('fitness_profile', {}) if doc else {})

@app.route('/api/client/fitness_profile', methods=['POST'])
@client_login_required
def client_save_fitness_profile():
    if users_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    try:
        height = round(float(d.get('height', 0)), 1)
        age    = int(d.get('age', 0))
        weight = round(float(d.get('weight', 0)), 1)
    except (ValueError, TypeError):
        return jsonify({'error': 'Invalid numbers'}), 400
    activity = s(d.get('activity', 'moderate'), 20)
    if activity not in ('sedentary','light','moderate','active','very_active'):
        activity = 'moderate'
    goal = s(d.get('goal', 'maintain'), 20)
    if goal not in ('lose','gain','maintain'):
        goal = 'maintain'
    profile = {
        'height':          height,
        'age':             age,
        'weight':          weight,
        'activity':        activity,
        'goal':            goal,
        'target_weight':   round(float(d.get('target_weight', weight)), 1),
        'weekly_goal_kg':  round(float(d.get('weekly_goal_kg', 0.5)), 2),
    }
    users_col.update_one({'_id': safe_oid(session['client_id'])}, {'$set': {'fitness_profile': profile}})
    return jsonify({'status': 'saved', 'profile': profile})

# -- CLIENT API � WORKOUT COMPLETION LOG -------------------------------------
@app.route('/api/client/workout_log', methods=['GET'])
@client_login_required
def client_get_workout_log():
    if db is None:
        return jsonify([]), 500
    items = list(db['workout_log'].find({'client_id': session['client_id']}).sort('date', -1).limit(60))
    for i in items:
        i['_id'] = str(i['_id'])
    return jsonify(items)

@app.route('/api/client/workout_log', methods=['POST'])
@client_login_required
def client_log_workout():
    if db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    date_str = s(d.get('date', ''), 12) or datetime.now(timezone.utc).strftime('%Y-%m-%d')
    program_id   = s(d.get('program_id', ''), 50)
    day_label    = s(d.get('day_label', ''), 100)
    notes        = s(d.get('notes', ''), 500)
    db['workout_log'].update_one(
        {'client_id': session['client_id'], 'date': date_str, 'day_label': day_label},
        {'$set': {
            'client_id':  session['client_id'],
            'date':       date_str,
            'program_id': program_id,
            'day_label':  day_label,
            'notes':      notes,
            'updated':    datetime.now(timezone.utc),
        }},
        upsert=True
    )
    return jsonify({'status': 'logged'})

# -- CLIENT API � DAILY LOG ----------------------------------------------------
@app.route('/api/client/daily_log', methods=['GET'])
@client_login_required
def client_get_daily_log():
    if db is None:
        return jsonify([]), 500
    items = list(db['daily_log'].find({'client_id': session['client_id']}).sort('date', -1).limit(30))
    for i in items:
        i['_id'] = str(i['_id'])
    return jsonify(items)

@app.route('/api/client/daily_log', methods=['POST'])
@client_login_required
@limiter.limit('10 per hour')
def client_save_daily_log():
    if db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    date_str = s(d.get('date', ''), 12)
    if not date_str:
        date_str = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    try:
        steps    = max(0, int(d.get('steps', 0)))
        cal_in   = max(0, int(d.get('calories_in', 0)))
        cal_burn = max(0, int(d.get('calories_burned', 0)))
        water    = max(0, min(20, int(d.get('water', 0))))
        weight   = round(float(d.get('weight', 0)), 1) if d.get('weight') else None
    except (ValueError, TypeError):
        return jsonify({'error': 'Invalid values'}), 400
    db['daily_log'].update_one(
        {'client_id': session['client_id'], 'date': date_str},
        {'$set': {
            'client_id':       session['client_id'],
            'date':            date_str,
            'steps':           steps,
            'calories_in':     cal_in,
            'calories_burned': cal_burn,
            'water':           water,
            'weight':          weight,
            'updated':         datetime.now(timezone.utc),
        }},
        upsert=True
    )
    return jsonify({'status': 'saved'})

@app.route('/api/client/daily_log/<date_str>', methods=['DELETE'])
@client_login_required
def client_delete_daily_log(date_str):
    if db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    db['daily_log'].delete_one({'client_id': session['client_id'], 'date': date_str})
    return jsonify({'status': 'deleted'})

# -- ADMIN API � INACTIVE CLIENTS (registered before /<cid> routes) ----------
@app.route('/api/admin/clients/inactive')
@login_required
def admin_inactive_clients_early():
    if users_col is None or checkins_col is None:
        return jsonify([]), 500
    clients = list(users_col.find({'role': 'client', 'active': True}, {'password': 0, 'reset_token_hash': 0, 'reset_token_expires': 0}))
    cutoff = datetime.now(timezone.utc) - timedelta(days=7)
    pipeline = [
        {'$sort': {'date': -1}},
        {'$group': {'_id': '$client_id', 'last_date': {'$first': '$date'}}}
    ]
    last_checkins = {r['_id']: r['last_date'] for r in checkins_col.aggregate(pipeline)}
    inactive = []
    for c in clients:
        cid = str(c['_id'])
        last = last_checkins.get(cid)
        if last is not None and last.tzinfo is None:
            last = last.replace(tzinfo=timezone.utc)
        if last is None or last < cutoff:
            days_ago = (datetime.now(timezone.utc) - last).days if last else None
            inactive.append({
                '_id': cid,
                'name': c.get('name', ''),
                'email': c.get('email', ''),
                'days_since_checkin': days_ago,
                'never_checked_in': last is None,
            })
    return jsonify(inactive)

# -- ADMIN API � CLIENT NOTES ------------------------------------------------
@app.route('/api/admin/clients/<cid>/notes', methods=['POST'])
@login_required
def admin_set_client_notes(cid):
    if users_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(cid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    notes = s((request.json or {}).get('notes', ''), 2000)
    users_col.update_one({'_id': oid}, {'$set': {'trainer_notes': notes}})
    return jsonify({'status': 'saved'})

# -- ADMIN API � REVENUE STATS -------------------------------------------------
@app.route('/api/admin/invoices/stats')
@login_required
def admin_invoice_stats():
    if payments_col is None:
        return jsonify({}), 500
    from calendar import monthrange
    now = datetime.now(timezone.utc)
    month_str = now.strftime('%Y-%m')
    all_invoices = list(payments_col.find({}))
    total_collected = sum(i['amount'] for i in all_invoices if i.get('status') == 'paid')
    total_outstanding = sum(i['amount'] for i in all_invoices if i.get('status') == 'unpaid')
    month_collected = sum(
        i['amount'] for i in all_invoices
        if i.get('status') == 'paid' and (i.get('paid_date') or '').startswith(month_str)
    )
    unpaid_count = sum(1 for i in all_invoices if i.get('status') == 'unpaid')
    return jsonify({
        'total_collected':   round(total_collected, 2),
        'total_outstanding': round(total_outstanding, 2),
        'month_collected':   round(month_collected, 2),
        'unpaid_count':      unpaid_count,
    })

# -- CLIENT API � INVOICE PDF --------------------------------------------------
@app.route('/api/client/invoices/<iid>/pdf')
@client_login_required
def client_invoice_pdf(iid):
    if payments_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(iid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    inv = payments_col.find_one({'_id': oid, 'client_id': session['client_id']})
    if not inv:
        return jsonify({'error': 'Invoice not found'}), 404

    def draw(c):
        from reportlab.lib.pagesizes import A4
        from reportlab.lib.colors import HexColor

        w, h = _pdf_header(c, 'Invoice', inv.get('client_name', 'Client'))

        inv_id = str(inv['_id'])[-8:].upper()
        status = (inv.get('status') or 'unpaid').upper()
        amount = float(inv.get('amount', 0))
        status_color = '#16a34a' if status == 'PAID' else '#ea580c'

        y = h - 105
        c.setFillColor(HexColor('#111111'))
        c.setFont('Helvetica-Bold', 12)
        c.drawString(36, y, 'Invoice  #INV-' + inv_id)
        badge_w = 58
        c.setFillColor(HexColor(status_color))
        c.roundRect(w - 36 - badge_w, y - 5, badge_w, 18, 4, fill=1, stroke=0)
        c.setFillColor(HexColor('#ffffff'))
        c.setFont('Helvetica-Bold', 9)
        c.drawCentredString(w - 36 - badge_w / 2, y + 1, status)
        y -= 24

        c.setStrokeColor(HexColor('#e5e7eb'))
        c.setLineWidth(0.5)
        c.line(36, y, w - 36, y)
        y -= 20

        col2_x = w / 2 + 10
        c.setFillColor(HexColor('#6b7280'))
        c.setFont('Helvetica-Bold', 8)
        c.drawString(36, y, 'BILL TO')
        c.drawString(col2_x, y, 'INVOICE DETAILS')
        y -= 16

        c.setFillColor(HexColor('#111111'))
        c.setFont('Helvetica-Bold', 12)
        c.drawString(36, y, inv.get('client_name') or 'Client')
        c.setFillColor(HexColor('#374151'))
        c.setFont('Helvetica', 10)
        c.drawString(col2_x, y, 'Date Issued:')
        c.setFont('Helvetica-Bold', 10)
        c.drawString(col2_x + 85, y, inv.get('created') or '-')
        y -= 16

        c.setFillColor(HexColor('#374151'))
        c.setFont('Helvetica', 10)
        c.drawString(col2_x, y, 'Due Date:')
        c.setFont('Helvetica-Bold', 10)
        c.drawString(col2_x + 85, y, inv.get('due_date') or '-')
        y -= 30

        c.setStrokeColor(HexColor('#e5e7eb'))
        c.line(36, y, w - 36, y)
        y -= 16

        c.setFillColor(HexColor('#f3f4f6'))
        c.rect(36, y - 6, w - 72, 22, fill=1, stroke=0)
        c.setFillColor(HexColor('#374151'))
        c.setFont('Helvetica-Bold', 9)
        c.drawString(46, y + 4, 'DESCRIPTION')
        c.drawRightString(w - 46, y + 4, 'AMOUNT')
        y -= 22

        desc = inv.get('description') or 'Coaching Services'
        c.setFillColor(HexColor('#111111'))
        c.setFont('Helvetica', 10)
        c.drawString(46, y, desc[:70])
        c.setFont('Helvetica-Bold', 10)
        c.drawRightString(w - 46, y, 'Rs. {:,.2f}'.format(amount))
        y -= 14
        c.setStrokeColor(HexColor('#e5e7eb'))
        c.setLineWidth(0.3)
        c.line(36, y, w - 36, y)
        y -= 30

        c.setFillColor(HexColor('#111111'))
        c.rect(w - 200, y - 22, 164, 38, fill=1, stroke=0)
        c.setFillColor(HexColor('#9ca3af'))
        c.setFont('Helvetica', 9)
        c.drawString(w - 192, y + 6, 'TOTAL AMOUNT')
        c.setFillColor(HexColor('#e8ff00'))
        c.setFont('Helvetica-Bold', 16)
        c.drawString(w - 192, y - 12, 'Rs. {:,.2f}'.format(amount))
        y -= 60

        if inv.get('paid_date'):
            c.setFillColor(HexColor('#f0fdf4'))
            c.roundRect(36, y - 8, w - 72, 30, 4, fill=1, stroke=0)
            c.setStrokeColor(HexColor('#86efac'))
            c.setLineWidth(0.5)
            c.roundRect(36, y - 8, w - 72, 30, 4, fill=0, stroke=1)
            c.setFillColor(HexColor('#166534'))
            c.setFont('Helvetica-Bold', 9)
            c.drawString(46, y + 10, 'PAYMENT RECEIVED')
            c.setFont('Helvetica', 9)
            method = inv.get('payment_method') or 'UPI'
            ref = inv.get('transaction_ref') or '-'
            c.drawString(46, y - 2, 'Date: {}   Method: {}   Ref: {}'.format(inv.get('paid_date'), method, ref))

        c.setStrokeColor(HexColor('#e5e7eb'))
        c.setLineWidth(0.5)
        c.line(36, 60, w - 36, 60)
        c.setFillColor(HexColor('#9ca3af'))
        c.setFont('Helvetica', 8)
        c.drawString(36, 46, 'Thank you for your trust in Sahil Panwar.')
        c.drawRightString(w - 36, 46, 'This is a computer-generated receipt.')

    filename = f"invoice-{str(inv['_id'])[-6:]}.pdf"
    return _pdf_canvas(filename, draw)

# -- ADMIN API � LEAD NOTES ----------------------------------------------------
@app.route('/api/admin/leads/<lid>/notes', methods=['POST'])
@login_required
def admin_set_lead_notes(lid):
    if leads_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(lid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    notes = s((request.json or {}).get('notes', ''), 2000)
    leads_col.update_one({'_id': oid}, {'$set': {'notes': notes}})
    return jsonify({'status': 'saved'})

# -- ADMIN API � ANNOUNCEMENTS -----------------------------------------------
@app.route('/api/admin/announcements', methods=['GET'])
@login_required
def admin_get_announcements():
    if announcements_col is None:
        return jsonify([]), 500
    items = list(announcements_col.find({}).sort('created', -1))
    for i in items:
        i['_id'] = str(i['_id'])
        i['created'] = to_ist(i.get('created'))
    return jsonify(items)

@app.route('/api/admin/announcements', methods=['POST'])
@login_required
def admin_add_announcement():
    if announcements_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    title = s(d.get('title', ''), 200)
    body  = s(d.get('body', ''), 2000)
    if not title:
        return jsonify({'error': 'title required'}), 400
    result = announcements_col.insert_one({
        'title':   title,
        'body':    body,
        'type':    s(d.get('type', 'info'), 20),
        'active':  bool(d.get('active', True)),
        'created': datetime.now(timezone.utc),
    })
    if bool(d.get('active', True)) and users_col is not None:
        for ann_u in users_col.find({'role': 'client', 'active': True}, {'email': 1, 'name': 1}):
            if ann_u.get('email'):
                _send_email(
                    ann_u['email'],
                    f'Announcement: {title}',
                    f'Hi {ann_u.get("name", "there")},\n\n{title}\n\n{body}\n\n'
                    f'Login to view: {url_for("client_dashboard", _external=True)}\n\u2014 Sahil Panwar'
                )
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/announcements/<aid>', methods=['PUT'])
@login_required
def admin_update_announcement(aid):
    if announcements_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(aid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d = request.json or {}
    announcements_col.update_one({'_id': oid}, {'$set': {
        'title':  s(d.get('title', ''), 200),
        'body':   s(d.get('body', ''), 2000),
        'type':   s(d.get('type', 'info'), 20),
        'active': bool(d.get('active', True)),
    }})
    return jsonify({'status': 'updated'})

@app.route('/api/admin/announcements/<aid>', methods=['DELETE'])
@login_required
def admin_delete_announcement(aid):
    if announcements_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(aid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    announcements_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

@app.route('/api/client/announcements')
@client_login_required
def client_get_announcements():
    if announcements_col is None:
        return jsonify([]), 500
    items = list(announcements_col.find({'active': True}).sort('created', -1).limit(10))
    for i in items:
        i['_id'] = str(i['_id'])
        i['created'] = to_ist(i.get('created'))
    return jsonify(items)

# -- ADMIN � CLIENT DETAIL PAGE -----------------------------------------------
@app.route('/admin/client/<cid>')
@login_required
def admin_client_detail(cid):
    if users_col is None:
        return redirect(url_for('admin'))
    oid = safe_oid(cid)
    if not oid:
        return redirect(url_for('admin'))
    client = users_col.find_one({'_id': oid, 'role': 'client'}, {'password': 0, 'reset_token_hash': 0, 'reset_token_expires': 0})
    if not client:
        return redirect(url_for('admin'))
    client['_id'] = str(client['_id'])
    client['joined'] = client['joined'].strftime('%d %b %Y') if client.get('joined') else ''
    return render_template('admin_client_detail.html', client=client)

# -- MUSCLE MAP ---------------------------------------------------------------
@app.route('/muscle-map')
@client_login_required
def muscle_map():
    user = users_col.find_one({'_id': safe_oid(session['client_id'])}, {'gender': 1}) if users_col is not None else None
    gender = (user or {}).get('gender', 'male')
    return render_template('muscle_map.html', gender=gender)

@app.route('/api/client/muscle-assignments')
@client_login_required
def client_get_muscle_assignments():
    if users_col is None:
        return jsonify([]), 200
    cid = session.get('client_id')
    doc = users_col.find_one({'_id': safe_oid(cid)}, {'muscle_assignments': 1})
    assignments = doc.get('muscle_assignments', []) if doc else []
    _, by_name = _exercise_video_index()
    for a in assignments:
        for ex in a.get('exercises') or []:
            embed = youtube_embed(ex.get('video_url', '')) or by_name.get((ex.get('name') or '').strip().lower(), '')
            if embed:
                ex['video_embed'] = embed
    return jsonify(assignments)

@app.route('/api/admin/muscle-assignments/<client_id>', methods=['GET'])
@login_required
def admin_get_muscle_assignments(client_id):
    if users_col is None:
        return jsonify([]), 200
    oid = safe_oid(client_id)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    doc = users_col.find_one({'_id': oid}, {'muscle_assignments': 1})
    return jsonify(doc.get('muscle_assignments', []) if doc else [])

@app.route('/api/admin/muscle-assignments/<client_id>', methods=['POST'])
@login_required
def admin_save_muscle_assignments(client_id):
    if users_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(client_id)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    assignments = (request.json or {}).get('assignments', [])
    clean = []
    for a in assignments[:50]:
        muscle = s(a.get('muscle', ''), 100)
        day    = s(a.get('day', ''), 20)
        exercises = []
        for ex in (a.get('exercises') or [])[:20]:
            exercises.append({
                'name': s(ex.get('name', ''), 200),
                'sets': s(str(ex.get('sets', '')), 10),
                'reps': s(str(ex.get('reps', '')), 10),
                'notes': s(ex.get('notes', ''), 300),
                'video_url': s(ex.get('video_url', ''), 500),
            })
        clean.append({'muscle': muscle, 'day': day, 'exercises': exercises})
    users_col.update_one({'_id': oid}, {'$set': {'muscle_assignments': clean}})
    return jsonify({'status': 'saved'})

# ── IMAGE UPLOAD ─────────────────────────────────────────────────────────────
ALLOWED_MIME = {'image/jpeg', 'image/png', 'image/webp', 'image/gif'}
MAX_UPLOAD_BYTES = 5 * 1024 * 1024  # 5 MB

try:
    images_col = db['images']
    images_col.create_index('image_id', unique=True)
    community_col = db['community_posts']
except Exception:
    images_col = None
    community_col = None

def _compress_image(data, mime):
    ext = 'png' if mime == 'image/png' else 'jpeg'
    img = Image.open(io.BytesIO(data))
    has_alpha = img.mode in ('RGBA', 'LA') or (img.mode == 'P' and 'transparency' in img.info)
    w, h = img.size
    if max(w, h) > 1080:
        ratio = 1080 / max(w, h)
        img = img.resize((int(w * ratio), int(h * ratio)), Image.LANCZOS)
    buf = io.BytesIO()
    if has_alpha or ext == 'png':
        img.convert('RGBA').save(buf, format='PNG', optimize=True)
        return buf.getvalue(), 'image/png'
    img.convert('RGB').save(buf, format='JPEG', quality=82, optimize=True)
    return buf.getvalue(), 'image/jpeg'

def _handle_upload(file):
    if not file or not file.filename:
        return None, 'No file'
    if file.mimetype not in ALLOWED_MIME:
        return None, 'Invalid file type'
    data = file.read(MAX_UPLOAD_BYTES + 1)
    if len(data) > MAX_UPLOAD_BYTES:
        return None, 'File too large (max 5 MB)'
    if images_col is None:
        return None, 'DB unavailable'
    data, mime = _compress_image(data, file.mimetype)
    image_id = secrets.token_hex(8)
    images_col.insert_one({
        'image_id': image_id,
        'data': data,
        'mime': mime,
    })
    return f'/api/img/{image_id}', None

@app.route('/api/img/<image_id>')
def serve_image(image_id):
    if images_col is None:
        return '', 503
    doc = images_col.find_one({'image_id': image_id}, {'data': 1, 'mime': 1, '_id': 0})
    if not doc:
        return '', 404
    from flask import Response
    return Response(doc['data'], content_type=doc['mime'],
                    headers={'Cache-Control': 'public, max-age=31536000'})

@app.route('/api/upload', methods=['POST'])
@login_required
@limiter.limit('60 per hour')
def admin_upload_image():
    url, err = _handle_upload(request.files.get('file'))
    if err:
        return jsonify({'error': err}), 400
    return jsonify({'url': url})

@app.route('/api/client/upload', methods=['POST'])
@client_login_required
@limiter.limit('20 per hour')
def client_upload_image():
    url, err = _handle_upload(request.files.get('file'))
    if err:
        return jsonify({'error': err}), 400
    return jsonify({'url': url})

# -- PWA MANIFEST -------------------------------------------------------------
@app.route('/manifest.json')
def pwa_manifest():
    return app.send_static_file('manifest.json')

@app.route('/sw.js')
def service_worker():
    resp = app.send_static_file('sw.js')
    resp.headers['Service-Worker-Allowed'] = '/'
    resp.headers['Cache-Control'] = 'no-cache'
    return resp

# -- PUSH NOTIFICATIONS --------------------------------------------------------
@app.route('/api/client/push/subscribe', methods=['POST'])
@client_login_required
def client_push_subscribe():
    if push_subs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    sub = request.json or {}
    if not sub.get('endpoint'):
        return jsonify({'error': 'Invalid subscription'}), 400
    cid = session['client_id']
    push_subs_col.update_one(
        {'client_id': cid, 'endpoint': sub['endpoint']},
        {'$set': {'client_id': cid, 'subscription': sub, 'endpoint': sub['endpoint'], 'updated': datetime.now(timezone.utc)}},
        upsert=True
    )
    return jsonify({'status': 'subscribed'})

@app.route('/api/client/push/unsubscribe', methods=['POST'])
@client_login_required
def client_push_unsubscribe():
    if push_subs_col is None:
        return jsonify({'ok': True})
    endpoint = (request.json or {}).get('endpoint', '')
    push_subs_col.delete_many({'client_id': session['client_id'], 'endpoint': endpoint})
    return jsonify({'status': 'unsubscribed'})

@app.route('/api/admin/push/subscribe', methods=['POST'])
@login_required
def admin_push_subscribe():
    if push_subs_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    sub = request.json or {}
    if not sub.get('endpoint'):
        return jsonify({'error': 'Invalid subscription'}), 400
    push_subs_col.update_one(
        {'client_id': 'admin', 'endpoint': sub['endpoint']},
        {'$set': {'client_id': 'admin', 'subscription': sub, 'endpoint': sub['endpoint'], 'updated': datetime.now(timezone.utc)}},
        upsert=True
    )
    return jsonify({'status': 'subscribed'})

def _push_notify(client_id, title, body, url='/client/dashboard', tag='spf'):
    """Send Web Push notification to a client (or 'admin') via pywebpush if available."""
    if push_subs_col is None:
        return
    try:
        from pywebpush import webpush, WebPushException
        vapid_private = os.environ.get('VAPID_PRIVATE_KEY', '')
        vapid_email   = os.environ.get('VAPID_EMAIL', 'mailto:admin@example.com')
        if not vapid_private:
            return
        subs = list(push_subs_col.find({'client_id': client_id}))
        payload = json.dumps({'title': title, 'body': body, 'url': url, 'tag': tag})
        for doc in subs:
            try:
                webpush(
                    subscription_info=doc['subscription'],
                    data=payload,
                    vapid_private_key=vapid_private,
                    vapid_claims={'sub': vapid_email},
                )
            except WebPushException as ex:
                if ex.response and ex.response.status_code in (404, 410):
                    push_subs_col.delete_one({'_id': doc['_id']})
                else:
                    logger.warning('Push failed: %s', ex)
    except ImportError:
        pass
    except Exception as e:
        logger.warning('Push notify error: %s', e)

@app.route('/api/admin/push/send', methods=['POST'])
@login_required
def admin_send_push():
    """Admin sends push to one client or all clients."""
    d = request.json or {}
    title   = s(d.get('title', 'Sahil Panwar'), 100)
    body    = s(d.get('body', ''), 200)
    cid     = d.get('client_id', 'all')
    url     = s(d.get('url', '/client/dashboard'), 200)
    if cid == 'all':
        if users_col is not None:
            for u in users_col.find({'role': 'client', 'active': True}, {'_id': 1}):
                _push_notify(str(u['_id']), title, body, url)
    else:
        _push_notify(cid, title, body, url)
    return jsonify({'status': 'sent'})

@app.route('/api/admin/vapid_public_key')
@login_required
def admin_vapid_public_key():
    return jsonify({'key': os.environ.get('VAPID_PUBLIC_KEY', '')})

@app.route('/api/client/vapid_public_key')
@client_login_required
def client_vapid_public_key():
    return jsonify({'key': os.environ.get('VAPID_PUBLIC_KEY', '')})

# -- DAILY TIPS ----------------------------------------------------------------
@app.route('/api/admin/tips', methods=['GET'])
@login_required
def admin_get_tips():
    if tips_col is None:
        return jsonify([]), 500
    items = list(tips_col.find({}).sort('date', -1).limit(50))
    for i in items:
        i['_id'] = str(i['_id'])
        i['date'] = to_ist(i.get('date'))
    return jsonify(items)

@app.route('/api/admin/tips', methods=['POST'])
@login_required
def admin_add_tip():
    if tips_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    text = s(d.get('text', ''), 500)
    if not text:
        return jsonify({'error': 'text required'}), 400
    result = tips_col.insert_one({
        'text':     text,
        'category': s(d.get('category', 'general'), 50),
        'date':     datetime.now(timezone.utc),
    })
    # push to all clients
    if users_col is not None:
        for u in users_col.find({'role': 'client', 'active': True}, {'_id': 1}):
            _push_notify(str(u['_id']), '?? Daily Tip', text[:80], '/client/dashboard', 'tip')
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/admin/tips/<tid>', methods=['DELETE'])
@login_required
def admin_delete_tip(tid):
    if tips_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(tid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    tips_col.delete_one({'_id': oid})
    return jsonify({'status': 'deleted'})

@app.route('/api/client/tips')
@client_login_required
def client_get_tips():
    if tips_col is None:
        return jsonify([]), 200
    items = list(tips_col.find({}).sort('date', -1).limit(10))
    for i in items:
        i['_id'] = str(i['_id'])
        i['date'] = to_ist(i.get('date'))
    return jsonify(items)

# -- GOALS ---------------------------------------------------------------------
@app.route('/api/client/goals', methods=['GET'])
@client_login_required
def client_get_goals():
    if goals_col is None:
        return jsonify([]), 200
    items = list(goals_col.find({'client_id': session['client_id']}).sort('created', -1))
    for i in items:
        i['_id'] = str(i['_id'])
        i['created'] = to_ist(i.get('created'))
    return jsonify(items)

@app.route('/api/client/goals', methods=['POST'])
@client_login_required
def client_set_goal():
    if goals_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    title = s(d.get('title', ''), 200)
    if not title:
        return jsonify({'error': 'title required'}), 400
    result = goals_col.insert_one({
        'client_id':   session['client_id'],
        'client_name': session.get('client_name', ''),
        'title':       title,
        'description': s(d.get('description', ''), 500),
        'target_date': s(d.get('target_date', ''), 20),
        'status':      'pending',
        'approved':    False,
        'progress':    0,
        'created':     datetime.now(timezone.utc),
    })
    # notify admin
    _push_notify('admin', '?? New Client Goal', f"{session.get('client_name','')} set a goal: {title[:60]}", '/admin', 'goal')
    return jsonify({'status': 'added', '_id': str(result.inserted_id)})

@app.route('/api/client/goals/<gid>', methods=['DELETE'])
@client_login_required
def client_delete_goal(gid):
    if goals_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(gid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    goals_col.delete_one({'_id': oid, 'client_id': session['client_id']})
    return jsonify({'status': 'deleted'})

@app.route('/api/admin/goals', methods=['GET'])
@login_required
def admin_get_goals():
    if goals_col is None:
        return jsonify([]), 200
    items = list(goals_col.find({}).sort('created', -1))
    for i in items:
        i['_id'] = str(i['_id'])
        i['created'] = to_ist(i.get('created'))
    return jsonify(items)

@app.route('/api/admin/goals/<gid>', methods=['POST'])
@login_required
def admin_update_goal(gid):
    if goals_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(gid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    d = request.json or {}
    update = {}
    if 'approved' in d:
        update['approved'] = bool(d['approved'])
        update['status'] = 'approved' if d['approved'] else 'rejected'
    if 'progress' in d:
        try:
            update['progress'] = max(0, min(100, int(d['progress'])))
        except (ValueError, TypeError):
            pass
    if 'trainer_note' in d:
        update['trainer_note'] = s(d['trainer_note'], 500)
    if not update:
        return jsonify({'error': 'Nothing to update'}), 400
    goal = goals_col.find_one({'_id': oid})
    goals_col.update_one({'_id': oid}, {'$set': update})
    if goal and 'approved' in d:
        msg = '? Goal approved!' if d['approved'] else '? Goal needs revision'
        _push_notify(goal['client_id'], msg, goal.get('title', '')[:80], '/client/dashboard', 'goal')
        if users_col is not None:
            goal_client = users_col.find_one({'_id': safe_oid(goal['client_id'])}, {'email': 1, 'name': 1})
            if goal_client and goal_client.get('email'):
                status_word = 'approved' if d['approved'] else 'needs revision'
                note = update.get('trainer_note', '')
                _send_email(
                    goal_client['email'],
                    f'Your goal has been {status_word} \u2014 Sahil Panwar',
                    f'Hi {goal_client.get("name", "there")},\n\n'
                    f'Your goal "{goal.get("title", "")}" has been {status_word}.\n\n'
                    + (f'Trainer note: {note}\n\n' if note else '') +
                    f'Login to view: {url_for("client_dashboard", _external=True)}\n\u2014 Sahil Panwar'
                )
    return jsonify({'status': 'updated'})

# -- REPORT CARDS --------------------------------------------------------------
@app.route('/api/admin/report_cards', methods=['POST'])
@login_required
def admin_create_report_card():
    if report_cards_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    d = request.json or {}
    client_id = s(d.get('client_id', ''), 50)
    if not client_id:
        return jsonify({'error': 'client_id required'}), 400
    client = users_col.find_one({'_id': safe_oid(client_id)}) if users_col else None
    result = report_cards_col.insert_one({
        'client_id':    client_id,
        'client_name':  client['name'] if client else '',
        'week_of':      s(d.get('week_of', ''), 20),
        'score':        max(1, min(10, int(d.get('score', 7)))),
        'consistency':  max(1, min(10, int(d.get('consistency', 7)))),
        'nutrition':    max(1, min(10, int(d.get('nutrition', 7)))),
        'progress':     max(1, min(10, int(d.get('progress', 7)))),
        'comment':      s(d.get('comment', ''), 1000),
        'created':      datetime.now(timezone.utc),
    })
    _push_notify(client_id, '?? Weekly Report Card', 'Your trainer sent your weekly report!', '/client/dashboard', 'report')
    if client and client.get('email'):
        _send_email(
            client['email'],
            'Your weekly report card is ready \u2014 Sahil Panwar',
            f'Hi {client.get("name", "there")},\n\n'
            f'Your trainer sent your weekly report card:\n\n'
            f'Overall Score:  {d.get("score", 7)}/10\n'
            f'Consistency:    {d.get("consistency", 7)}/10\n'
            f'Nutrition:      {d.get("nutrition", 7)}/10\n'
            f'Progress:       {d.get("progress", 7)}/10\n\n'
            + (f'Comment: {d.get("comment")}\n\n' if d.get('comment') else '') +
            f'Login to view: {url_for("client_dashboard", _external=True)}\n\u2014 Sahil Panwar'
        )
    return jsonify({'status': 'created', '_id': str(result.inserted_id)})

@app.route('/api/admin/report_cards', methods=['GET'])
@login_required
def admin_get_report_cards():
    if report_cards_col is None:
        return jsonify([]), 200
    items = list(report_cards_col.find({}).sort('created', -1).limit(100))
    for i in items:
        i['_id'] = str(i['_id'])
        i['created'] = to_ist(i.get('created'))
    return jsonify(items)

@app.route('/api/client/report_cards', methods=['GET'])
@client_login_required
def client_get_report_cards():
    if report_cards_col is None:
        return jsonify([]), 200
    items = list(report_cards_col.find({'client_id': session['client_id']}).sort('created', -1).limit(20))
    for i in items:
        i['_id'] = str(i['_id'])
        i['created'] = to_ist(i.get('created'))
    return jsonify(items)

# -- CHECKIN REACTIONS ---------------------------------------------------------
@app.route('/api/admin/checkins/<cid>/reaction', methods=['POST'])
@login_required
def admin_checkin_reaction(cid):
    if checkins_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(cid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    reaction = s((request.json or {}).get('reaction', ''), 10)
    VALID = ['??','??','??','??','??','?']
    if reaction not in VALID:
        return jsonify({'error': 'Invalid reaction'}), 400
    checkin = checkins_col.find_one({'_id': oid})
    checkins_col.update_one({'_id': oid}, {'$set': {'reaction': reaction, 'reviewed': True}})
    if checkin:
        _push_notify(checkin['client_id'], f'{reaction} Trainer reacted to your check-in!',
                     'Keep it up!', '/client/dashboard', 'reaction')
    return jsonify({'status': 'ok', 'reaction': reaction})

# -- SUPPLEMENTS ---------------------------------------------------------------
@app.route('/api/admin/supplements/<client_id>', methods=['GET'])
@login_required
def admin_get_supplements(client_id):
    if supplements_col is None:
        return jsonify([]), 200
    items = list(supplements_col.find({'client_id': client_id}))
    for i in items:
        i['_id'] = str(i['_id'])
    return jsonify(items)

@app.route('/api/admin/supplements/<client_id>', methods=['POST'])
@login_required
def admin_save_supplements(client_id):
    if supplements_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    items = (request.json or {}).get('supplements', [])
    clean = []
    for item in items[:20]:
        clean.append({
            'name':   s(item.get('name', ''), 100),
            'dose':   s(item.get('dose', ''), 50),
            'timing': s(item.get('timing', ''), 100),
        })
    supplements_col.delete_many({'client_id': client_id})
    if clean:
        for c in clean:
            c['client_id'] = client_id
        supplements_col.insert_many(clean)
    return jsonify({'status': 'saved'})

@app.route('/api/client/supplements', methods=['GET'])
@client_login_required
def client_get_supplements():
    if supplements_col is None:
        return jsonify([]), 200
    items = list(supplements_col.find({'client_id': session['client_id']}, {'_id': 0, 'client_id': 0}))
    return jsonify(items)

# -- PERSONAL RECORDS (auto-computed) -----------------------------------------
@app.route('/api/client/personal_records')
@client_login_required
def client_personal_records():
    if db is None:
        return jsonify([]), 200
    cid = session['client_id']
    logs = list(db['workout_log'].find({'client_id': cid}))
    # also scan muscle assignments for exercise names
    records = {}
    if users_col is not None:
        doc = users_col.find_one({'_id': safe_oid(cid)}, {'muscle_assignments': 1})
        assignments = (doc or {}).get('muscle_assignments', [])
        for a in assignments:
            for ex in (a.get('exercises') or []):
                name = (ex.get('name') or '').strip()
                if name and ex.get('sets') and ex.get('reps'):
                    key = name.lower()
                    if key not in records:
                        records[key] = {'name': name, 'sets': ex.get('sets'), 'reps': ex.get('reps'), 'source': 'assigned'}
    # scan daily logs for weight PRs
    weight_logs = list(db['daily_log'].find({'client_id': cid, 'weight': {'$exists': True, '$ne': None}}).sort('date', 1))
    if weight_logs:
        best = max(weight_logs, key=lambda x: x.get('weight') or 0)
        records['_weight_pr'] = {'name': 'Heaviest Logged Weight', 'value': best.get('weight'), 'date': best.get('date'), 'source': 'log'}
    return jsonify(list(records.values())[:30])

# -- BADGES / MILESTONES -------------------------------------------------------
@app.route('/api/client/badges')
@client_login_required
def client_get_badges():
    if db is None or checkins_col is None:
        return jsonify([]), 200
    cid = session['client_id']
    badges = []
    checkin_count = checkins_col.count_documents({'client_id': cid})
    log_count = db['daily_log'].count_documents({'client_id': cid})
    photo_count = db['client_self_photos'].count_documents({'client_id': cid}) if db is not None else 0
    # compute streak
    adherence = _compute_adherence(cid)
    streak = adherence.get('streak', 0)

    BADGE_DEFS = [
        ('first_checkin',  '??', 'First Check-In',    'Submitted your first check-in',         checkin_count >= 1),
        ('checkin_5',      '??', '5 Check-Ins',        'Submitted 5 check-ins',                  checkin_count >= 5),
        ('checkin_10',     '??', '10 Check-Ins',       'Submitted 10 check-ins',                 checkin_count >= 10),
        ('first_log',      '??', 'First Log',          'Logged your first training day',         log_count >= 1),
        ('log_7',          '??', '7-Day Streak',       'Trained 7 days in a row',                streak >= 7),
        ('log_30',         '??', '30-Day Streak',      'Trained 30 days in a row',               streak >= 30),
        ('first_photo',    '??', 'Progress Photo',     'Uploaded your first progress photo',     photo_count >= 1),
        ('photo_4',        '??', 'Photo Journey',      'Uploaded 4 progress photos',             photo_count >= 4),
        ('log_14',         '?', '2-Week Streak',      'Trained 14 days in a row',               streak >= 14),
    ]
    for bid, icon, name, desc, earned in BADGE_DEFS:
        badges.append({'id': bid, 'icon': icon, 'name': name, 'desc': desc, 'earned': earned})
    return jsonify(badges)

# -- MEAL CHECKLIST ------------------------------------------------------------
@app.route('/api/client/meal_checklist', methods=['GET'])
@client_login_required
def client_get_meal_checklist():
    if db is None:
        return jsonify({}), 200
    today = (datetime.now(timezone.utc) + _IST).strftime('%Y-%m-%d')
    doc = db['meal_checklist'].find_one({'client_id': session['client_id'], 'date': today})
    return jsonify({'checked': (doc or {}).get('checked', [])})

@app.route('/api/client/meal_checklist', methods=['POST'])
@client_login_required
def client_save_meal_checklist():
    if db is None:
        return jsonify({'error': 'DB unavailable'}), 500
    checked = (request.json or {}).get('checked', [])
    today = (datetime.now(timezone.utc) + _IST).strftime('%Y-%m-%d')
    db['meal_checklist'].update_one(
        {'client_id': session['client_id'], 'date': today},
        {'$set': {'client_id': session['client_id'], 'date': today, 'checked': checked}},
        upsert=True
    )
    return jsonify({'status': 'saved'})

# ── COMMUNITY ────────────────────────────────────────────────────────────────
@app.route('/community')
def community():
    cfg = get_config()
    member_count = users_col.count_documents({'role': 'client', 'active': True}) if users_col is not None else 0
    # grab up to 12 members with avatars for the avatar wall
    members = list(users_col.find(
        {'role': 'client', 'active': True},
        {'name': 1, 'avatar_url': 1}
    ).limit(12)) if users_col is not None else []
    for m in members:
        m['_id'] = str(m['_id'])
    return render_template('community.html', cfg=cfg, member_count=member_count, members=members)

@app.route('/api/community/posts', methods=['GET'])
def community_get_posts():
    if community_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    try:
        skip = max(0, int(request.args.get('skip', 0)))
    except (ValueError, TypeError):
        skip = 0
    try:
        posts = list(community_col.find({}).sort('created', -1).skip(skip).limit(10))
        cid = session.get('client_id', '')
        for p in posts:
            p['_id'] = str(p['_id'])
            p['created'] = to_ist(p.get('created'))
            p['liked'] = cid in (p.get('likes') or [])
            p['like_count'] = len(p.get('likes') or [])
            p.pop('likes', None)
            for c in p.get('comments') or []:
                c['_id'] = str(c['_id'])
                c['created'] = to_ist(c.get('created'))
        return jsonify(posts)
    except Exception as e:
        logger.error('community_get_posts error: %s', e)
        return jsonify({'error': 'Server error'}), 500

@app.route('/api/community/posts', methods=['POST'])
@client_login_required
@limiter.limit('20 per hour')
def community_create_post():
    if community_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    # support both multipart (with image) and plain JSON
    if request.content_type and 'multipart' in request.content_type:
        text = s((request.form.get('text') or ''), 1000)
        image_url = None
        file = request.files.get('image')
        if file and file.filename:
            image_url, err = _handle_upload(file)
            if err:
                return jsonify({'error': err}), 400
    else:
        text = s((request.json or {}).get('text', ''), 1000)
        image_url = None
    if not text and not image_url:
        return jsonify({'error': 'Post cannot be empty'}), 400
    cid = session['client_id']
    user = users_col.find_one({'_id': safe_oid(cid)}, {'name': 1, 'avatar_url': 1}) if users_col else None
    result = community_col.insert_one({
        'client_id':   cid,
        'author_name': (user or {}).get('name', session.get('client_name', 'Member')),
        'avatar_url':  (user or {}).get('avatar_url', ''),
        'text':        text,
        'image_url':   image_url,
        'likes':       [],
        'comments':    [],
        'created':     datetime.now(timezone.utc),
    })
    return jsonify({'status': 'posted', '_id': str(result.inserted_id)})

@app.route('/api/community/posts/<pid>/like', methods=['POST'])
@client_login_required
def community_like_post(pid):
    if community_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    cid = session['client_id']
    post = community_col.find_one({'_id': oid}, {'likes': 1})
    if not post:
        return jsonify({'error': 'Not found'}), 404
    likes = post.get('likes') or []
    if cid in likes:
        community_col.update_one({'_id': oid}, {'$pull': {'likes': cid}})
        liked = False
        count = len(likes) - 1
    else:
        community_col.update_one({'_id': oid}, {'$addToSet': {'likes': cid}})
        liked = True
        count = len(likes) + 1
    return jsonify({'liked': liked, 'like_count': count})

@app.route('/api/community/posts/<pid>/comments', methods=['POST'])
@client_login_required
@limiter.limit('30 per hour')
def community_add_comment(pid):
    if community_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    text = s((request.json or {}).get('text', ''), 500)
    if not text:
        return jsonify({'error': 'Comment cannot be empty'}), 400
    cid = session['client_id']
    user = users_col.find_one({'_id': safe_oid(cid)}, {'name': 1, 'avatar_url': 1}) if users_col else None
    comment = {
        '_id':         ObjectId(),
        'client_id':   cid,
        'author_name': (user or {}).get('name', session.get('client_name', 'Member')),
        'avatar_url':  (user or {}).get('avatar_url', ''),
        'text':        text,
        'created':     datetime.now(timezone.utc),
    }
    community_col.update_one({'_id': oid}, {'$push': {'comments': comment}})
    comment['_id'] = str(comment['_id'])
    comment['created'] = to_ist(comment['created'])
    return jsonify({'status': 'commented', 'comment': comment})

@app.route('/api/community/posts/<pid>', methods=['DELETE'])
@client_login_required
def community_delete_post(pid):
    if community_col is None:
        return jsonify({'error': 'DB unavailable'}), 500
    oid = safe_oid(pid)
    if not oid:
        return jsonify({'error': 'Invalid id'}), 400
    community_col.delete_one({'_id': oid, 'client_id': session['client_id']})
    return jsonify({'status': 'deleted'})

if __name__ == '__main__':
    port = int(os.environ.get('PORT', 5000))
    is_production = os.environ.get('FLASK_ENV') == 'production'
    debug = (not is_production) and os.environ.get('FLASK_DEBUG', 'false').lower() == 'true'
    app.run(host='0.0.0.0', port=port, debug=debug)
