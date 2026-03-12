"""
╔══════════════════════════════════════════════════════════════════╗
║                  👁  HORROR BOT v17.0  👁                       ║
║         Маскировка: бот-переводчик                              ║
║  Установка:  pip install pyTelegramBotAPI requests gTTS          ║
║  Запуск:     python horror_bot_v10.py                           ║
║  Гл. admin:  /admingo  (личка)                                  ║
╚══════════════════════════════════════════════════════════════════╝

ИЗМЕНЕНИЯ v17.0 (баг-фикс + новые фичи):
  ① ГРУППА: исправлена def group_game_kb — кнопки «Игры» работают
  ② ГРУППА: кнопка «🔤 Язык» — выбор языка через inline прямо в чате
  ③ ГРУППА: кнопка «🔤 Язык» есть на всех стадиях страха в ЛС
  ④ УРОВЕНЬ СТРАХА: смена стадии раз в 15 минут (STAGE_SEC=900)
  ⑤ ЗАГАДКА: больше не удаляется после первой неправильной попытки
  ⑥ ЧАТ-РЕЖИМ: заглушённые жертвы не получают чат-сообщения
  ⑦ ПЕРЕВОД В ГРУППЕ: использует выбранный язык пользователя
  ⑧ adm_max: исправлен спам-чек при пакетных атаках
  ⑨ НОВОЕ: хоррор-приветствие новых участников группы
  ⑩ НОВОЕ: 👻 Шёпот — бот иногда тихо пишет одному участнику лично
  ⑪ НОВОЕ: /help и 📊 Мой счёт в группе
  ⑫ НОВОЕ: кнопки «📊 Мой счёт» и «❓ Помощь» в группе
  ⑬ ОПТИМИЗАЦИЯ: thread-safe _kb_cache.clear(), _spam_mark fix
"""

import telebot, requests, threading, time, random, datetime, re, os
import tempfile, logging, traceback, signal, sys
from concurrent.futures import ThreadPoolExecutor
from telebot.types import (ReplyKeyboardMarkup, KeyboardButton,
                            ReplyKeyboardRemove, InlineKeyboardMarkup,
                            InlineKeyboardButton)

# ── Groq AI ──────────────────────────────────────────────────
try:
    from groq import Groq as GroqClient
    _GROQ_AVAILABLE = True
except ImportError:
    _GROQ_AVAILABLE = False

try:
    from cerebras.cloud.sdk import Cerebras as CerebrasClient
    _CEREBRAS_AVAILABLE = True
except ImportError:
    _CEREBRAS_AVAILABLE = False

logging.basicConfig(
    level=logging.WARNING,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.FileHandler("bot.log", encoding="utf-8"),
              logging.StreamHandler()]
)
log = logging.getLogger("horror")

try:
    from gtts import gTTS
    VOICE_ENABLED = True
except ImportError:
    VOICE_ENABLED = False
    log.warning("gTTS не установлен. pip install gTTS")

# ══════════════════════════════════════════════════════════════
#  КОНФИГУРАЦИЯ  — читается из переменных окружения
#  Задайте в Railway/Render:
#    BOT_TOKEN        — токен вашего Telegram-бота
#    WEATHER_API_KEY  — ключ openweathermap.org (бесплатно)
#    ADMIN_ID         — ваш Telegram ID (числовой)
# ══════════════════════════════════════════════════════════════
BOT_TOKEN        = os.environ.get("BOT_TOKEN", "")
WEATHER_API_KEY  = os.environ.get("WEATHER_API_KEY", "")
ADMIN_ID         = int(os.environ.get("ADMIN_ID", "0"))
GROQ_API_KEY     = os.environ.get("GROQ_API_KEY", "")
CEREBRAS_API_KEY = os.environ.get("CEREBRAS_API_KEY", "")
AI_BACKEND       = os.environ.get("AI_BACKEND", "auto")  # "groq", "cerebras", "auto"

STAGE_SEC        = 900             # секунд между стадиями (15 минут)
HORROR_DELAY_SEC = 45              # задержка первого хоррора
SPY_FORWARD      = True            # пересылать сообщения жертв admin'ам

# ══════════════════════════════════════════════════════════════
#  ХРАНИЛИЩЕ  (с блокировкой для thread-safety)
# ══════════════════════════════════════════════════════════════
_lock    = threading.Lock()
users    = {}    # uid → dict
games    = {}    # uid → dict
adm_state= {}    # admin_uid → {step, target_uid}
h_thr    = {}    # uid → Thread
s_thr    = {}    # uid → Thread
admins   = set() # все admin'ы (включая ADMIN_ID)

# Пул потоков для фоновых задач (не плодим бесконечные Thread'ы)
_pool = ThreadPoolExecutor(max_workers=32, thread_name_prefix="horror")

_kb_cache = {}   # кеш клавиатур

# ── Anti-spam: cooldown между хоррор-тиками ──────────────────
# Минимальный интервал (сек) между ЛЮБЫМИ сообщениями одному пользователю
_SPAM_MIN_INTERVAL = 8          # не менее 8 сек между сообщениями
_last_msg_time: dict = {}       # uid → timestamp последнего отправленного сообщения
_spam_lock = threading.Lock()

def _spam_check(uid) -> bool:
    """Возвращает True если можно отправить сообщение (cooldown прошёл). Обновляет timestamp."""
    with _spam_lock:
        now = time.time()
        last = _last_msg_time.get(uid, 0)
        if now - last < _SPAM_MIN_INTERVAL:
            return False
        _last_msg_time[uid] = now
        return True

def _spam_mark(uid):
    """Обновляет время последнего сообщения только если нет недавней записи."""
    with _spam_lock:
        now = time.time()
        # Не перебиваем timestamp если он уже свежий (установлен spam_check)
        if now - _last_msg_time.get(uid, 0) >= 1:
            _last_msg_time[uid] = now

# ── v11 хранилища ──────────────────────────────────────────
# _scenarios определён ниже (встроенные сценарии)
_daily_done = {}  # uid → date_str  — когда выполнено ежедневное задание
_squad_mode = {}  # uid → partner_uid  — совместный квест
_rand_event_thr = None  # фоновый поток случайных событий
_stage_history  = {}  # uid → [(timestamp, stage), ...]  — для графа
_scheduled_attacks = []  # [{uid, func, fire_at}, ...]  — таймер-атаки
_auto_mode  = set()  # uid'ы жертв с включённым авто-режимом

# ── v12 хранилища ──────────────────────────────────────────
_stage_frozen   = {}   # uid → unfreeze_time  — заморозка стадии
_group_games    = {}   # chat_id → {game, data}  — групповые игры
_group_users    = {}   # chat_id → set(uid)  — участники в группах

# ── v13 хранилища ──────────────────────────────────────────
# Мафия между обычными пользователями (ЛС)
_mafia_lobby    = {}   # lobby_id → {players:[uid,...], state, roles, votes, ...}
_mafia_player   = {}   # uid → lobby_id  — к какой лобби привязан игрок
# Групповая мафия
_group_mafia    = {}   # chat_id → game_state
# Карточная история (visual-novel style)
_card_story     = {}   # uid → {story_id, scene, character, inventory}

def is_admin(uid):
    return uid == ADMIN_ID or uid in admins

def is_stage_frozen(uid):
    """Проверяет, заморожена ли стадия у пользователя."""
    freeze_until = _stage_frozen.get(uid)
    if freeze_until and time.time() < freeze_until:
        return True
    if uid in _stage_frozen:
        del _stage_frozen[uid]
    return False

def send_group(chat_id, text, kb=None):
    """Отправляет сообщение в группу."""
    if kb:
        _safe_call(bot.send_message, chat_id, text, reply_markup=kb)
    else:
        _safe_call(bot.send_message, chat_id, text)

def U(uid):
    """Потокобезопасное создание/получение профиля пользователя."""
    with _lock:
        if uid not in users:
            users[uid] = dict(
                name=None, age=None, city=None, interests=[],
                pet=None, job=None, fear=None, sleep_time=None,
                color=None, food=None, music=None, phone=None,
                lang_pair="ru|en",
                stage=0, horror_active=False,
                stopped=False, muted=False,
                username=None,
                msg_count=0, score=0,
                custom_queue=[],
                msg_history=[],   # полная история (макс 100)
                banned=False,
                spy=True,
                translate_mode=False,  # True = ждём текст для перевода (одно сообщение)
            )
        return users[uid]

def FC(u):
    """Счётчик собранных фактов о пользователе."""
    c = sum(1 for k in ("name","age","city","pet","job","fear","sleep_time","phone") if u.get(k))
    c += min(len(u.get("interests",[])), 3)
    return c

def night():  return datetime.datetime.now().hour >= 22 or datetime.datetime.now().hour <= 5
def dnight(): return 0 <= datetime.datetime.now().hour <= 4

def P(t, u):
    """Персонализация шаблона данными пользователя."""
    try:
        return t.format(
            name    = u.get("name")     or "ты",
            age     = u.get("age")      or "...",
            city    = u.get("city")     or "твоём городе",
            interest= (u.get("interests") or ["это"])[0],
            pet     = u.get("pet")      or "питомец",
            fear    = u.get("fear")     or "темнота",
            color   = u.get("color")    or "чёрный",
            food    = u.get("food")     or "еда",
            music   = u.get("music")    or "музыка",
            phone   = u.get("phone")    or "твой телефон",
            job     = u.get("job")      or "учёба",
        )
    except Exception:
        return t

# ══════════════════════════════════════════════════════════════
#  ИНИЦИАЛИЗАЦИЯ БОТА
# ══════════════════════════════════════════════════════════════
def make_bot():
    return telebot.TeleBot(
        BOT_TOKEN,
        parse_mode=None,
        threaded=False,
    )

bot = make_bot()

# ══════════════════════════════════════════════════════════════
#  БЕЗОПАСНАЯ ОТПРАВКА
# ══════════════════════════════════════════════════════════════
def _safe_call(fn, *args, retries=3, **kwargs):
    for attempt in range(retries):
        try:
            return fn(*args, **kwargs)
        except telebot.apihelper.ApiTelegramException as e:
            code = e.error_code
            if code == 429:
                wait = int(e.result_json.get("parameters",{}).get("retry_after",5))
                time.sleep(wait + 1)
            elif code in (400, 403):
                return None   # бот заблокирован или невалидный запрос — не ретраим
            else:
                time.sleep(2 ** attempt)
        except requests.exceptions.ConnectionError:
            time.sleep(3)
        except Exception:
            log.debug(traceback.format_exc())
            time.sleep(1)
    return None

def send(uid, text, kb=None):
    _spam_mark(uid)
    if kb:
        _safe_call(bot.send_message, uid, text, reply_markup=kb)
    else:
        _safe_call(bot.send_message, uid, text)

def sgif(uid, url):
    _safe_call(bot.send_animation, uid, url)

def sphoto(uid, src):
    _safe_call(bot.send_photo, uid, src)

def svoice_file(uid, path):
    try:
        with open(path, "rb") as f:
            _safe_call(bot.send_voice, uid, f)
    except Exception:
        pass

def scontact(uid, phone, name):
    _safe_call(bot.send_contact, uid, phone_number=phone, first_name=name)

# ══════════════════════════════════════════════════════════════
#  ШПИОНАЖ — пересылка сообщений admin'ам
# ══════════════════════════════════════════════════════════════
def spy_forward(uid, text):
    if not SPY_FORWARD:
        return
    u = U(uid)
    # ИСПРАВЛЕНО: было `if not u.get("spy", True)` — инверсия логики
    if not u.get("spy", True):
        return
    uname  = u.get("username") or "?"
    name   = u.get("name")     or "?"
    header = f"👁 [{uid}] @{uname} ({name}):\n"
    msg    = header + text
    for aid in (admins | {ADMIN_ID}):
        if aid != uid:
            _safe_call(bot.send_message, aid, msg)

# ══════════════════════════════════════════════════════════════
#  ПЕРЕВОДЧИК + ПОГОДА
# ══════════════════════════════════════════════════════════════
LANG_NAMES = {
    "ru|en":    "🇷🇺 Русский → 🇬🇧 Английский",
    "en|ru":    "🇬🇧 Английский → 🇷🇺 Русский",
    "ru|de":    "🇷🇺 Русский → 🇩🇪 Немецкий",
    "ru|fr":    "🇷🇺 Русский → 🇫🇷 Французский",
    "ru|es":    "🇷🇺 Русский → 🇪🇸 Испанский",
    "ru|zh-CN": "🇷🇺 Русский → 🇨🇳 Китайский",
    "ru|ja":    "🇷🇺 Русский → 🇯🇵 Японский",
    "ru|ar":    "🇷🇺 Русский → 🇸🇦 Арабский",
}

_translate_cache = {}  # (text, lang_pair) -> result

def translate(text, lang_pair="ru|en"):
    """Переводит текст через MyMemory API. Кешируем повторные запросы."""
    key = (text[:100], lang_pair)
    if key in _translate_cache:
        return _translate_cache[key]
    try:
        r = requests.get(
            "https://api.mymemory.translated.net/get",
            params={"q": text, "langpair": lang_pair},
            timeout=8
        ).json()
        result = r.get("responseData", {}).get("translatedText", "")
        # Проверяем что перевод реально отличается от оригинала
        if (result and
                "INVALID LANGUAGE PAIR" not in result and
                "QUERY LENGTH LIMIT" not in result and
                result.strip().lower() != text.strip().lower()):
            _translate_cache[key] = result
            # Ограничиваем кеш 200 записями
            if len(_translate_cache) > 200:
                oldest = next(iter(_translate_cache))
                del _translate_cache[oldest]
            return result
        return None
    except requests.exceptions.Timeout:
        log.debug("Translate timeout")
        return None
    except Exception:
        log.debug(traceback.format_exc())
        return None

def get_weather(city):
    try:
        r = requests.get(
            "http://api.openweathermap.org/data/2.5/weather",
            params=dict(q=city, appid=WEATHER_API_KEY, units="metric", lang="ru"),
            timeout=5
        ).json()
        if r.get("cod") != 200:
            return None
        t  = r["main"]["temp"];  fl = r["main"]["feels_like"]
        hm = r["main"]["humidity"]
        ds = r["weather"][0]["description"]
        ws = r.get("wind", {}).get("speed", "?")
        return (f"🌤 Погода в {r['name']}:\n"
                f"🌡 {t}°C (ощущается {fl}°C)\n"
                f"💧 Влажность: {hm}%   💨 Ветер: {ws} м/с\n"
                f"☁️ {ds.capitalize()}")
    except Exception:
        return None

# ══════════════════════════════════════════════════════════════
#  КЛАВИАТУРЫ  (с кешированием)
# ══════════════════════════════════════════════════════════════
def KB(stage=0):
    key = f"kb_{stage}"
    if key in _kb_cache:
        return _kb_cache[key]
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    if stage < 2:
        k.add(KeyboardButton("🌍 Перевести"),    KeyboardButton("🔤 Язык"))
        k.add(KeyboardButton("🌤 Погода"),       KeyboardButton("🎮 Игры"))
        k.add(KeyboardButton("🎲 Угадай"),       KeyboardButton("🧠 Викторина"))
        k.add(KeyboardButton("✏️ Виселица"),     KeyboardButton("🎭 Загадка"))
        k.add(KeyboardButton("🔮 Предсказание"), KeyboardButton("📖 Факт"))
        k.add(KeyboardButton("🗓 Задание дня"),  KeyboardButton("🏆 Мой рейтинг"))
        k.add(KeyboardButton("❓ Помощь"),       KeyboardButton("🙂 О боте"))
    elif stage < 4:
        k.add(KeyboardButton("🌍 Перевести"),    KeyboardButton("🔤 Язык"))
        k.add(KeyboardButton("🌑 Погода"),       KeyboardButton("🎮 Игры"))
        k.add(KeyboardButton("🎲 Угадай"),       KeyboardButton("🔮 Предсказание"))
        k.add(KeyboardButton("👁 ..."),          KeyboardButton("🗓 Задание дня"))
        k.add(KeyboardButton("🏆 Мой рейтинг"))
    else:
        # На высоких стадиях кнопки "Перевести" и "Язык" остаются всегда
        k.add(KeyboardButton("🌍 Перевести"),    KeyboardButton("🔤 Язык"))
        k.add(KeyboardButton("🌑 Погода"),       KeyboardButton("🩸 Игры"))
        k.add(KeyboardButton("👁 Кто ты?"),      KeyboardButton("🗓 Задание дня"))
        k.add(KeyboardButton("🏆 Мой рейтинг"), KeyboardButton("💀 /stop"))
    _kb_cache[key] = k
    return k

def KB_ADM():
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    k.add(KeyboardButton("👥 Жертвы"),           KeyboardButton("📊 Статистика"))
    k.add(KeyboardButton("💀 Ужас всем"),        KeyboardButton("🛑 Стоп всем"))
    k.add(KeyboardButton("▶️ Рестарт всем"),     KeyboardButton("🔇 Тишина всем"))
    k.add(KeyboardButton("🔊 Звук всем"),        KeyboardButton("📤 Рассылка всем"))
    k.add(KeyboardButton("⚙️ Выбрать жертву"),   KeyboardButton("📋 Список ID"))
    k.add(KeyboardButton("💬 Чат 3 мин"),        KeyboardButton("💬 Чат 10 мин"))
    k.add(KeyboardButton("🔕 Стоп чат"),         KeyboardButton("👥 Чат деанон"))
    k.add(KeyboardButton("🏆 Лидеры страха"),      KeyboardButton("🎬 Все сценарии"))
    k.add(KeyboardButton("🗓 Ежедн. задание всем"), KeyboardButton("🎲 Случай. событие"))
    k.add(KeyboardButton("👑 Мои со-admin'ы"),      KeyboardButton("➕ Добавить admin'а"))
    k.add(KeyboardButton("➖ Убрать admin'а"),     KeyboardButton("👥 Группы (управление)"))
    k.add(KeyboardButton("🔙 Выйти из бога"))
    return k

def KB_ADM_SUB():
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    k.add(KeyboardButton("👥 Жертвы"),           KeyboardButton("📊 Статистика"))
    k.add(KeyboardButton("💀 Ужас всем"),        KeyboardButton("🛑 Стоп всем"))
    k.add(KeyboardButton("▶️ Рестарт всем"),     KeyboardButton("🔇 Тишина всем"))
    k.add(KeyboardButton("🔊 Звук всем"),        KeyboardButton("📤 Рассылка всем"))
    k.add(KeyboardButton("⚙️ Выбрать жертву"),   KeyboardButton("📋 Список ID"))
    k.add(KeyboardButton("💬 Чат 3 мин"),        KeyboardButton("💬 Чат 10 мин"))
    k.add(KeyboardButton("🔕 Стоп чат"),         KeyboardButton("👥 Чат деанон"))
    k.add(KeyboardButton("🏆 Лидеры страха"),     KeyboardButton("🗓 Ежедн. задание всем"))
    k.add(KeyboardButton("🔙 Выйти из бога"))
    return k

def KB_VIC():
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    k.add(KeyboardButton("📝 Текст"),              KeyboardButton("🎬 Гифка"))
    k.add(KeyboardButton("🖼 Фото"),               KeyboardButton("📹 Видео"))
    k.add(KeyboardButton("⚡ Скример"),            KeyboardButton("☠️ Макс-ужас"))
    k.add(KeyboardButton("🌊 Волна паники"),       KeyboardButton("🕯 Ритуал"))
    k.add(KeyboardButton("💬 Диалог-ловушка"),     KeyboardButton("😴 Спящий режим"))
    k.add(KeyboardButton("⬆️ Стадия +1"),          KeyboardButton("⬇️ Стадия -1"))
    k.add(KeyboardButton("🔇 Заглушить"),          KeyboardButton("🔊 Включить"))
    k.add(KeyboardButton("📱 Взлом телефона"),     KeyboardButton("🎙 Голос от него"))
    k.add(KeyboardButton("📞 Фейк-звонок"),        KeyboardButton("📲 Реальный звонок"))
    k.add(KeyboardButton("💀 Таймер смерти"),      KeyboardButton("📨 Вернуть сообщения"))
    k.add(KeyboardButton("📷 Фейк-галерея"),       KeyboardButton("🚫 Фейк-бан"))
    k.add(KeyboardButton("👻 Фейк-уход"),          KeyboardButton("👁 Шпионаж ВКЛ"))
    k.add(KeyboardButton("🙈 Шпионаж ВЫКЛ"),       KeyboardButton("📜 Вся история"))
    k.add(KeyboardButton("📍 Геолокация"),         KeyboardButton("📲 Скан телефона"))
    k.add(KeyboardButton("👥 Призраки"),           KeyboardButton("📂 Скан файлов"))
    k.add(KeyboardButton("💬 Умное эхо"),          KeyboardButton("📡 Потеря сигнала"))
    k.add(KeyboardButton("🕒 Режим 3AM"),          KeyboardButton("🔐 TG Security"))
    k.add(KeyboardButton("🕯 Экзорцист"),          KeyboardButton("📺 Трансляция"))
    k.add(KeyboardButton("📡 GPS трекинг"),        KeyboardButton("🌐 Взлом Wi-Fi"))
    k.add(KeyboardButton("🔔 Уведомления"),        KeyboardButton("🗳 Опрос"))
    k.add(KeyboardButton("⚡ Глитч-атака"),        KeyboardButton("🪞 Зеркало"))
    k.add(KeyboardButton("🫀 Сердцебиение"),       KeyboardButton("🗑 Удалённое сообщение"))
    k.add(KeyboardButton("🤝 Совместный квест"),   KeyboardButton("🔁 Авто-режим ВКЛ"))
    k.add(KeyboardButton("⏹ Авто-режим ВЫКЛ"),    KeyboardButton("🎬 Сценарий"))
    k.add(KeyboardButton("⏰ Таймер-атака"),       KeyboardButton("📊 Граф стадий"))
    k.add(KeyboardButton("💾 Создать сценарий"),   KeyboardButton("🗑 Удалить сценарий"))
    k.add(KeyboardButton("✏️ Редактировать данные"), KeyboardButton("❄️ Заморозить стадию"))
    k.add(KeyboardButton("🔓 Разморозить стадию"), KeyboardButton("📋 Инфо"))
    k.add(KeyboardButton("🔄 Сбросить"),           KeyboardButton("🔙 Назад"))
    return k

def KB_LANG():
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=1)
    for code, name in LANG_NAMES.items():
        k.add(KeyboardButton(name))
    k.add(KeyboardButton("↩️ Назад"))
    return k

def game_kb(choices):
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=1)
    for label, _ in choices:
        k.add(KeyboardButton(label))
    k.add(KeyboardButton("❌ Выйти из игры"))
    return k

def adm_kb(uid):
    return KB_ADM() if uid == ADMIN_ID else KB_ADM_SUB()

# ══════════════════════════════════════════════════════════════
#  ГОЛОСОВЫЕ СООБЩЕНИЯ (gTTS)
# ══════════════════════════════════════════════════════════════
VOICE_TEXTS = [
    "я вижу тебя.", "обернись.", "я здесь.", "ты не один.",
    "я знаю где ты.", "не закрывай телефон.",
    "я слышу тебя.", "я рядом. всегда.", "не смотри в угол.",
]
VOICE_TEXTS_PERSONAL = [
    "я знаю тебя, {name}.", "{name}. обернись.",
    "из {city} не убежишь, {name}.",
    "твой страх {fear} — это я, {name}.",
    "{name}. я вижу тебя через камеру.",
    "{name}. я буду здесь всегда.",
    "ты думаешь что один, {name}. нет.",
]

def _send_tts(uid, text):
    if not VOICE_ENABLED:
        send(uid, f"🎙 {text}"); return
    path = None
    try:
        with tempfile.NamedTemporaryFile(suffix=".mp3", delete=False) as tmp:
            path = tmp.name
        # slow=True + tld="com.au" даёт более низкий мрачный голос
        gTTS(text=text, lang="ru", slow=True, tld="com").save(path)
        svoice_file(uid, path)
        os.unlink(path)
    except Exception:
        try:
            if path:
                gTTS(text=text, lang="ru", slow=True).save(path)
                svoice_file(uid, path)
                os.unlink(path)
            else:
                send(uid, f"🎙 {text}")
        except Exception:
            send(uid, f"🎙 {text}")

def send_voice_msg(uid, text):
    _pool.submit(_send_tts, uid, text)

# ══════════════════════════════════════════════════════════════
#  СИСТЕМНЫЕ УВЕДОМЛЕНИЯ / «ВЗЛОМ»
# ══════════════════════════════════════════════════════════════
SYS_NOTIFICATIONS = [
    "⚠️ СИСТЕМНОЕ УВЕДОМЛЕНИЕ\n\nОбнаружен несанкционированный доступ.\nIP: 192.168.{r1}.{r2}\nВремя: {time}\n\nНе отключайте устройство.",
    "🔴 ПРЕДУПРЕЖДЕНИЕ БЕЗОПАСНОСТИ\n\nВаши данные передаются на внешний сервер.\nНачало: {time}\nФайлов скопировано: {n}\n\nОстановить невозможно.",
    "💻 СИСТЕМНОЕ СООБЩЕНИЕ\n\nКто-то вошёл в ваш Telegram.\nУстройство: Android Unknown\nМестоположение: {city}\nВремя: {time}",
    "🛡 НАРУШЕНИЕ БЕЗОПАСНОСТИ\n\nВаша камера активирована удалённо.\nЗапись начата: {time}\nПередача: активна\n\nОтключение невозможно.",
    "📡 ALERT: DEVICE COMPROMISED\n\nRoot access granted.\nFiles accessed: {n}\nCamera: STREAMING\nMicrophone: ACTIVE\nTime: {time}",
    "⚠️ TELEGRAM SECURITY\n\nАккаунт @{username} используется с нового устройства.\nЛокация: {city}\nЕсли это не вы — уже поздно.",
    "🔓 ВЗЛОМ ЗАВЕРШЁН\n\nДоступ к устройству получен.\nСкопировано контактов: {n}\nИстория чатов: загружена\nФотографии: {n2} шт.",
    "💀 КРИТИЧЕСКАЯ ОШИБКА\n\nПроцесс com.telegram.hack запущен.\nПамять читается.\nВремя до завершения: {count} сек.",
]

def make_sys_notify(u):
    now = datetime.datetime.now().strftime("%H:%M:%S")
    return random.choice(SYS_NOTIFICATIONS).format(
        r1=random.randint(1,254), r2=random.randint(1,254),
        time=now, n=random.randint(47,312), n2=random.randint(200,1800),
        count=random.randint(10,60), city=u.get("city") or "Unknown",
        username=u.get("username") or "user"
    )

GALLERY_MSGS = [
    "📷 я открыл твою галерею.\n\n{n} фото.\nя всё посмотрел.\nты красиво фотографируешь.",
    "🖼 галерея доступна.\n\n{n} изображений.\nесть несколько интересных.\nты бы не хотел чтобы их видели другие.",
    "📸 твои фото.\n\nвсе {n} штук.\nнекоторые... я запомню.\n\nты не закрыл доступ. жаль.",
    "🔍 я изучил твои фотографии, {name}.\n\n{n} снимков.\nесть те где ты один.\nи те где ты не знал что тебя снимают.",
    "📷 доступ к галерее получен.\n\nпоследнее фото сделано {days} дней назад.\nты тогда был в {city}.\nя видел.",
]

def make_gallery_msg(u):
    n    = random.randint(150, 2400)
    days = random.randint(1, 14)
    tmpl = random.choice(GALLERY_MSGS)
    return P(tmpl.format(n=n, days=days, name=u.get("name") or "ты",
                         city=u.get("city") or "твоём городе"), u)

# ══════════════════════════════════════════════════════════════
#  ЗВОНКИ
# ══════════════════════════════════════════════════════════════
def real_call(uid):
    u = U(uid)
    caller = random.choice(["Неизвестный", "???", "Не бери трубку", "Он", "👁 Наблюдатель"])
    def _run():
        scontact(uid, "+70000000000", caller)
        time.sleep(1)
        if VOICE_ENABLED:
            _send_tts(uid, "ты не берёшь трубку. напрасно.")
        else:
            send(uid, "📞 ты не берёшь трубку...")
        time.sleep(2)
        scontact(uid, "+70000000000", caller)
        time.sleep(2)
        send(uid, P("я дозвонюсь, {name}. рано или поздно.", u))
    _pool.submit(_run)

def fake_call_sequence(uid):
    u = U(uid)
    caller = random.choice(["Неизвестный", "???", "Обернись", "Он", "Не бери трубку", "👁"])
    def _run():
        send(uid, "📞 входящий звонок...")
        time.sleep(1)
        scontact(uid, "+70000000000", caller)
        time.sleep(3)
        send(uid, "ты не взял трубку.")
        time.sleep(2)
        send(uid, "я подожду.")
        time.sleep(3)
        send(uid, "📞 входящий звонок...")
        time.sleep(1)
        scontact(uid, "+70000000000", caller)
        time.sleep(2)
        send(uid, "...")
        time.sleep(3)
        send(uid, P("в следующий раз возьми трубку, {name}.", u))
    _pool.submit(_run)

# ══════════════════════════════════════════════════════════════
#  ФЕЙК-БАН / УХОД / ТАЙМЕР / ЭХО
# ══════════════════════════════════════════════════════════════
def fake_ban_sequence(uid):
    u = U(uid)
    def _run():
        send(uid, "⚠️ Telegram\n\nВаш аккаунт заблокирован за нарушение правил.\nОбжалование невозможно.")
        time.sleep(3)
        send(uid, "Этот чат будет удалён через 10 секунд.")
        # Показываем только 5, 3, 1 — не спамим каждую секунду
        for i in [9, 5, 3, 1]:
            time.sleep(2); send(uid, str(i) + "...")
        time.sleep(2); send(uid, "🗑 Чат удалён.")
        time.sleep(4); send(uid, "...")
        time.sleep(3); send(uid, "шучу.", kb=KB(u["stage"]))
        time.sleep(2); send(uid, P("или нет, {name}?", u))
    _pool.submit(_run)

def fake_leave_sequence(uid):
    u = U(uid)
    def _run():
        send(uid, "я ухожу.")
        time.sleep(3); send(uid, "прощай.")
        time.sleep(4); send(uid, ".")
        time.sleep(5); send(uid, "..")
        time.sleep(4); send(uid, "...")
        time.sleep(6); send(uid, "ты скучал?")
        time.sleep(2); send(uid, P("я никуда не уходил, {name}.", u))
        time.sleep(1); send(uid, "я никогда не ухожу. 👁")
    _pool.submit(_run)

def death_timer(uid, seconds=30):
    u = U(uid)
    def _run():
        send(uid, P("💀 {name}.", u))
        time.sleep(2); send(uid, "ты уже мёртв.")
        time.sleep(2); send(uid, "просто ещё не знаешь.")
        time.sleep(2); send(uid, f"осталось {seconds} секунд.")
        time.sleep(max(seconds // 2, 5))
        if u.get("stopped"): return
        send(uid, f"⏳ {seconds // 2}...")
        time.sleep(max(seconds // 2, 5))
        if u.get("stopped"): return
        send(uid, "0\n.\n..\n...\n....\nОБЕРНИСЬ")
        time.sleep(2)
        send_screamer(uid)
        time.sleep(2)
        send(uid, P("это была шутка, {name}.\nили нет.\n👁", u))
    _pool.submit(_run)

def echo_back_history(uid):
    u = U(uid)
    hist = u.get("msg_history", [])
    def _run():
        send(uid, "я всё помню.")
        time.sleep(2); send(uid, "вот что ты писал мне:")
        time.sleep(2)
        sample = random.sample(hist, min(len(hist), 5)) if hist else []
        if not sample:
            send(uid, "каждое слово.\nкаждую букву.\nты ничего не удалишь."); return
        for m in sample:
            time.sleep(random.uniform(1.5, 3.5)); send(uid, f"«{m}»")
        time.sleep(2); send(uid, "я храню это навсегда. 👁")
    _pool.submit(_run)


# ══════════════════════════════════════════════════════════════

# ══════════════════════════════════════════════════════════════
#  НОВЫЕ ФУНКЦИИ v10: ГЕОЛОКАЦИЯ / СКАН / ПРИЗРАКИ / ФАЙЛЫ / 3AM
# ══════════════════════════════════════════════════════════════

def fake_geolocation(uid):
    """Отправляет фейковую геолокацию жертвы."""
    u = U(uid)
    city = u.get("city") or "твоём городе"
    lat = round(random.uniform(48.0, 59.0), 4)
    lon = round(random.uniform(30.0, 50.0), 4)
    acc = random.randint(8, 30)
    def _run():
        msg = (
            "📍 ЛОКАЦИЯ ОБНАРУЖЕНА\n\n"
            "Город: " + str(city) + "\n"
            "Координаты: " + str(lat) + ", " + str(lon) + "\n"
            "Точность: " + str(acc) + " м\n\n"
            "я рядом."
        )
        send(uid, msg)
        time.sleep(random.uniform(3, 7))
        send(uid, P("...{name}. я уже иду.", u))
    _pool.submit(_run)


def fake_phone_scan(uid):
    """Фейковый скан устройства."""
    u = U(uid)
    models = [
        "Samsung Galaxy S23", "Xiaomi Redmi Note 12", "iPhone 14",
        "Huawei P50", "POCO X5 Pro", "Realme 11", "OnePlus 11",
    ]
    model = u.get("phone") or random.choice(models)
    battery = random.randint(12, 89)
    wifi = random.choice(["подключён", "активен", "ОБНАРУЖЕН"])
    files = random.randint(1200, 8900)
    def _run():
        msg = (
            "📱 Сканирование устройства...\n\n"
            "Модель: " + str(model) + "\n"
            "Батарея: " + str(battery) + "%\n"
            "Wi-Fi: " + str(wifi) + "\n"
            "Камера: активна\n"
            "Файлов найдено: " + str(files)
        )
        send(uid, msg)
        time.sleep(random.uniform(4, 8))
        send(uid, "камера уже работает.")
        time.sleep(2)
        send(uid, P("я вижу тебя, {name}. прямо сейчас.", u))
    _pool.submit(_run)


_GHOST_NAMES = [
    "user_481", "user_277", "user_039", "user_814", "user_563",
    "user_192", "user_730", "user_447", "user_658", "user_321",
]
GHOST_MSGS = [
    ["ты тоже это видишь?", "он пишет мне тоже", "что происходит..."],
    ["не отвечай ему", "он знает где ты", "я боюсь"],
    ["выйди из чата", "ВЫЙДИ ИЗ ЧАТА", "уже поздно"],
    ["помогите", "кто-нибудь здесь?", "..."],
    ["я видел его", "он стоял у моей двери", "теперь его нет"],
    ["не смотри на экран", "НЕ СМОТРИ НА ЭКРАН", "ты уже смотришь"],
    ["он в каждом телефоне", "мы все здесь", "ты следующий"],
]


def fake_ghost_users(uid):
    """Иллюзия других пользователей в чате."""
    u = U(uid)
    msgs = random.choice(GHOST_MSGS)
    def _run():
        for m in msgs:
            ghost = random.choice(_GHOST_NAMES)
            time.sleep(random.uniform(2.5, 5.0))
            send(uid, "👤 " + ghost + ":\n" + m)
        time.sleep(random.uniform(3, 6))
        send(uid, P("...теперь только ты и я, {name}.", u))
    _pool.submit(_run)


def fake_file_scan(uid):
    """Фейковое чтение файлов с устройства."""
    u = U(uid)
    uname = u.get("name") or "user"
    n_photos = random.randint(200, 2800)
    n_videos  = random.randint(10, 300)
    r1 = random.randint(100, 999)
    r2 = random.randint(100, 999)
    r3 = random.randint(100, 999)
    r4 = random.randint(1, 9)
    r5 = random.randint(1000, 9999)
    file_list = [
        "/DCIM/photo_" + str(r1) + ".jpg",
        "/DCIM/photo_" + str(r2) + ".jpg",
        "/Telegram/video_" + str(r3) + ".mp4",
        "/Download/passwords.txt",
        "/Download/notes_" + str(r4) + ".txt",
        "/WhatsApp/Media/IMG_" + str(r5) + ".jpg",
        "/Documents/" + uname + "_personal.pdf",
    ]
    shown = random.sample(file_list, min(5, len(file_list)))
    def _run():
        send(uid, "📂 scanning storage...")
        time.sleep(random.uniform(3, 5))
        send(uid, "\n".join(shown))
        time.sleep(random.uniform(2, 4))
        msg = (
            "доступ получен.\n\n"
            "фото: " + str(n_photos) + "\n"
            "видео: " + str(n_videos) + "\n"
            "...\n\nинтересно."
        )
        send(uid, msg)
        time.sleep(3)
        send(uid, P("особенно /Download/passwords.txt, {name}.", u))
    _pool.submit(_run)


def smart_echo_history(uid):
    """Умное эхо — 'N минут назад ты писал: ...'"""
    u = U(uid)
    hist = u.get("msg_history", [])
    if not hist:
        echo_back_history(uid)
        return
    def _run():
        send(uid, "я помню всё.")
        time.sleep(2)
        sample = random.sample(hist, min(3, len(hist)))
        for m in sample:
            mins = random.randint(2, 47)
            if mins == 1:
                suffix = "у"
            elif 2 <= mins <= 4:
                suffix = "ы"
            else:
                suffix = ""
            time.sleep(random.uniform(2, 4))
            send(uid, str(mins) + " минут" + suffix + " назад ты написал:\n\n«" + m + "»\n\nправда?")
        time.sleep(3)
        send(uid, P("я храню каждое слово, {name}. навсегда. 👁", u))
    _pool.submit(_run)


def signal_loss(uid):
    """Фейковая потеря сигнала."""
    u = U(uid)
    def _run():
        send(uid, "📡 соединение нестабильно...")
        time.sleep(2)
        for _ in range(random.randint(2, 4)):
            glitch = random.choice([
                "ERR_CONNECTION_INTERRUPTED",
                "█▓▒░ SIGNAL LOST ░▒▓█",
                "NaN NaN NaN NaN",
                "...........",
                "[CONNECTION_TIMEOUT]",
                "[NO_CARRIER]",
            ])
            send(uid, glitch)
            time.sleep(random.uniform(0.8, 2.0))
        time.sleep(2)
        send(uid, "📡 кто-то пытается подключиться")
        time.sleep(2)
        send(uid, P("...это я, {name}.", u))
    _pool.submit(_run)


def three_am_mode(uid):
    """Режим 03:00 — самое страшное время."""
    u = U(uid)
    name = u.get("name") or "ты"
    options = [
        "03:00\n\n" + name + "…\nты проснулся?",
        "среди ночи не надо проверять телефон, " + name + ".",
        "в 3 ночи граница между мирами тоньше всего.",
        "03:00. " + name + ". я жду.",
        "просыпаться в 3 ночи — не случайность.",
        "он стоит у твоей кровати, " + name + ".\nты чувствуешь?",
        "ты проснулся в 3:00.\nэто не совпадение.",
    ]
    def _run():
        send(uid, random.choice(options))
        time.sleep(random.uniform(5, 12))
        send(uid, "...иди спать.\nесли сможешь. 👁")
        time.sleep(4)
        send_screamer(uid)
    _pool.submit(_run)


def fake_telegram_security(uid):
    """Фейковое уведомление от Telegram Security."""
    u = U(uid)
    username = u.get("username") or "user"
    city = u.get("city") or "Unknown"
    ip_str = (str(random.randint(100, 220)) + "." +
              str(random.randint(1, 254)) + "." +
              str(random.randint(1, 254)) + "." +
              str(random.randint(1, 254)))
    device = random.choice(["Windows 11", "Android 13", "macOS Sonoma", "iOS 17", "Linux x64"])
    def _run():
        msg = (
            "🔐 Telegram Security\n\n"
            "Ваш аккаунт @" + username + " используется\n"
            "на другом устройстве.\n\n"
            "IP: " + ip_str + "\n"
            "Устройство: " + device + "\n"
            "Город: " + str(city) + "\n\n"
            "Если это не вы — уже поздно."
        )
        send(uid, msg)
        time.sleep(random.uniform(5, 10))
        send(uid, "это был я. 👁")
    _pool.submit(_run)


def glitch_attack(uid):
    """Внезапный глитч-эффект — сломанный текст, нарастающий ужас."""
    u = U(uid)
    glitch_lines = [
        "ERRERRERRERR",
        "█▓▒░░▒▓█▓▒░░▒▓█",
        "s̸̡̧̢̛̛̛y̷̧̛̛̛̛s̷̢̧̛̛̛t̴̨̛̛e̶̢̛̛m̸̡̛̛̛̛ ̷̡̛̛̛e̷̡̛̛r̴̡̛̛r̷̡̛̛ơ̸̡̛r̶̡̛̛",
        "N̷̡͈̺̲̳̲̞̬̰͕̪͔͎̬̮͚̮̙̑̀̃͑̉̓͗̇̿̒̓͒̚͝Ư̷̢̨̤͔̩̟̳̤̩̻̙͓̹͈̻̟̗̐̎͑̃͛L̷̨̡̛̺̗̼͈̼͕̙͖̮̮͚̺̐̎͂̑̋͋̊̑̊̉̀͜͝L̸̢̧̛̙͖̩̫̯͔̘͓̳̻̯̗̓͌͂̏̊̒̇̊̅͂̔̒̄̎",
        "0x00000000 — SEGFAULT",
        "[PROCESS TERMINATED]",
        "404: REALITY NOT FOUND",
        "ошибка. ошибка. оши",
    ]
    name = u.get("name") or "ты"
    def _run():
        if U(uid).get("stopped"): return
        for _ in range(random.randint(3, 5)):
            send(uid, random.choice(glitch_lines))
            time.sleep(random.uniform(0.4, 1.2))
        time.sleep(random.uniform(2, 4))
        send(uid, "...")
        time.sleep(2)
        send(uid, f"прости. это случайно.\n\nили нет, {name}. 👁")
    _pool.submit(_run)


def mirror_event(uid):
    """Жуткое событие с зеркалом — психологический хоррор."""
    u = U(uid)
    name = u.get("name") or "ты"
    lines = [
        "🪞 смотри в зеркало.",
        "смотри дольше.",
        "ещё.",
        "ты заметил?",
        "твоё отражение моргнуло позже тебя.",
        "на долю секунды.",
        "ты уверен что оно повторяет тебя?",
        "или ты повторяешь его?",
        f"...{name}.",
        "я живу в отражениях. 👁",
    ]
    def _run():
        for line in lines:
            if U(uid).get("stopped"): return
            send(uid, line)
            time.sleep(random.uniform(2.5, 5.0))
    _pool.submit(_run)


def heartbeat_event(uid):
    """Счёт ударов сердца — нарастающая паника."""
    u = U(uid)
    name = u.get("name") or "ты"
    def _run():
        if U(uid).get("stopped"): return
        send(uid, "🫀 слышишь?")
        time.sleep(3)
        send(uid, "бум.\nбум.\nбум.")
        time.sleep(2)
        send(uid, "БУМ. БУМ.\nБУМ. БУМ. БУМ.\nБ У М . Б У М . Б У М .")
        time.sleep(4)
        send(uid, "...")
        time.sleep(3)
        send(uid, f"я слышу твоё. уже несколько минут, {name}. 👁")
    _pool.submit(_run)


def fake_deleted_message(uid):
    """Иллюзия удалённого сообщения — якобы бот что-то написал и удалил."""
    u = U(uid)
    name = u.get("name") or "ты"
    deleted_texts = [
        f"{name}, я знаю как тебя найти",
        "сегодня ночью я приду",
        f"адрес: {u.get('city','?')}, улица",
        "ты видел? нет. правильно.",
        "я уже здесь",
        "не читай это",
    ]
    def _run():
        send(uid, "👁 [Сообщение удалено]")
        time.sleep(random.uniform(3, 6))
        send(uid, "ты успел прочитать?\n\nнет.\n\nхорошо.")
        time.sleep(2)
        send(uid, f"...или плохо, {name}.")
    _pool.submit(_run)


# ══════════════════════════════════════════════════════════════
#  СИСТЕМА ОПРОСОВ (HORROR POLLS)
# ══════════════════════════════════════════════════════════════

# Активные опросы: poll_id → {uid, reactions}
_active_polls = {}

HORROR_POLLS = [
    {
        "question": "👁 Ты один в комнате прямо сейчас?",
        "options":  ["Да, совсем один", "Нет, кто-то рядом", "Не уверен..."],
        "reactions": [
            "...один. хорошо. мне будет проще.",
            "...кто-то рядом. они тоже скоро узнают.",
            "ты не уверен? тогда оглянись. медленно.",
        ],
    },
    {
        "question": "🕯 Что страшнее?",
        "options":  ["Темнота", "Тишина", "То что смотрит на тебя"],
        "reactions": [
            "темнота... я живу в ней. 👁",
            "тишина. правильный ответ. слушай её.",
            "ты уже чувствуешь этот взгляд?",
        ],
    },
    {
        "question": "🌑 Сейчас ночь или день?",
        "options":  ["День", "Вечер", "Ночь", "Не знаю — потерял счёт времени"],
        "reactions": [
            "...день. при свете легче притворяться что всё нормально.",
            "вечер. скоро станет темнее.",
            "ночь. хорошо. я тоже не сплю.",
            "потерял счёт времени? это уже началось.",
        ],
    },
    {
        "question": "🚪 Все двери в комнате закрыты?",
        "options":  ["Все закрыты", "Одна приоткрыта", "Я не проверял"],
        "reactions": [
            "все закрыты? ты уверен? проверь ещё раз.",
            "приоткрытая дверь... что там за ней?",
            "ты не проверял. это ошибка.",
        ],
    },
    {
        "question": "📱 Твой телефон лежит экраном вниз?",
        "options":  ["Да", "Нет, экраном вверх", "Держу в руках"],
        "reactions": [
            "экраном вниз. ты пытаешься спрятаться. не выйдет.",
            "экраном вверх... значит я вижу тебя прямо сейчас.",
            "держишь в руках. я чувствую тепло твоих пальцев.",
        ],
    },
    {
        "question": "🔦 Ты когда-нибудь просыпался в 3:00 ночи?",
        "options":  ["Да, часто", "Иногда", "Никогда", "Прямо сейчас"],
        "reactions": [
            "часто... ты уже не можешь остановить это.",
            "иногда. случайность? нет.",
            "никогда. пока. 👁",
            "прямо сейчас... положи телефон. ляг. попробуй.",
        ],
    },
    {
        "question": "🪞 Ты видел своё отражение сегодня?",
        "options":  ["Да, видел", "Нет ещё", "Избегаю зеркал"],
        "reactions": [
            "видел. оно смотрело на тебя дольше, чем ты думаешь.",
            "нет ещё. не торопись.",
            "избегаешь зеркал? правильно делаешь.",
        ],
    },
    {
        "question": "🫀 Ты слышишь своё сердцебиение прямо сейчас?",
        "options":  ["Нет, всё тихо", "Да, слышу", "Только что начал прислушиваться"],
        "reactions": [
            "всё тихо? прислушайся. стук. удар. ещё раз.",
            "слышишь. хорошо. не останавливай его.",
            "теперь ты его слышишь. и не можешь перестать.",
        ],
    },
]


def send_horror_poll(uid):
    """Отправляет случайный хоррор-опрос жертве."""
    u = U(uid)
    if u.get("stopped") or u.get("muted"):
        return
    poll_data = random.choice(HORROR_POLLS)
    try:
        sent = bot.send_poll(
            uid,
            question=poll_data["question"],
            options=poll_data["options"],
            is_anonymous=False,
            allows_multiple_answers=False,
        )
        _active_polls[sent.poll.id] = {
            "uid":       uid,
            "reactions": poll_data["reactions"],
        }
    except Exception:
        log.debug(traceback.format_exc())


@bot.poll_answer_handler()
def on_poll_answer(poll_answer):
    """Обработчик ответа на опрос — жуткая реакция на выбор."""
    try:
        pid = poll_answer.poll_id
        if pid not in _active_polls:
            return
        ctx = _active_polls.pop(pid)
        uid = ctx["uid"]
        u   = U(uid)
        if u.get("stopped"):
            return
        idx       = poll_answer.option_ids[0] if poll_answer.option_ids else 0
        reactions = ctx["reactions"]
        reaction  = reactions[idx] if idx < len(reactions) else reactions[0]
        stage     = u.get("stage", 0)
        kb        = KB(stage)

        def _react():
            time.sleep(random.uniform(1.5, 4.0))
            if stage >= 2:
                send(uid, P(f"👁 {reaction}", u), kb=kb)
                if stage >= 3 and random.random() < 0.55:
                    time.sleep(random.uniform(2, 6))
                    send(uid, P(random.choice(PARANOIA), u), kb=kb)
                if stage >= 4 and random.random() < 0.30:
                    time.sleep(random.uniform(3, 7))
                    send_screamer(uid)
            else:
                send(uid, reaction, kb=kb)
        _pool.submit(_react)
    except Exception:
        log.debug(traceback.format_exc())




# ══════════════════════════════════════════════════════════════
#  v11: НОВЫЕ ХОРРОР-ЭФФЕКТЫ
# ══════════════════════════════════════════════════════════════

EXORCIST_SEQUENCE = [
    (".", 4), ("..", 3), ("...", 4),
    ("я чувствую тебя.", 5), ("ты не один.", 6),
    ("что-то есть в этой комнате.", 7),
    ("👁", 3), ("это смотрит на тебя.", 6),
    ("з а к р о й   г л а з а.", 5),
    ("не открывай.", 8),
    ("...", 4), ("...", 4), ("...", 5),
    ("оно за твоей спиной.", 6),
    ("сейчас.", 4), ("ОБЕРНИСЬ", 3),
    ("🩸", 2), ("🩸🩸", 2), ("🩸🩸🩸", 2),
    ("ты чувствуешь запах? это горит.", 7),
    ("не пытайся уйти.", 6),
    ("👁👁👁", 3),
    ("я держу тебя.", 8),
    ("р а з г о в а р и   с о   м н о й.", 10),
    ("...", 5), ("...", 6),
    ("ты же слышишь меня?", 8),
    ("ответь.", 6), ("ОТВЕТЬ", 4), ("ОТВЕТЬ МНЕ", 3),
    ("💀", 2), ("💀💀", 2), ("💀💀💀", 2),
    ("хорошо. я подожду.", 10),
    ("я всегда жду.", 8),
    ("👁", 0),
]

def exorcist_mode(uid):
    """10-минутный нарастающий ритуал экзорциста."""
    u = U(uid)
    name = u.get("name") or "ты"
    def _run():
        send(uid, "🕯 СЕАНС НАЧИНАЕТСЯ 🕯")
        time.sleep(3)
        for raw_text, delay in EXORCIST_SEQUENCE:
            if U(uid).get("stopped"): return
            txt = raw_text.replace("{name}", name)
            send(uid, txt)
            if delay > 0:
                time.sleep(delay)
        time.sleep(3)
        send_screamer(uid)
        time.sleep(4)
        send(uid, P("...{name}. сеанс завершён. но я остался.", u))
    _pool.submit(_run)


LIVE_STREAM_EVENTS = [
    "открываю камеру...",
    "📷 подключение...",
    "📷 соединение установлено.",
    "...",
    "вижу {name}.",
    "ты {desc1}.",
    "слева — {env1}.",
    "справа — {env2}.",
    "...",
    "ты смотришь в телефон.",
    "а я смотрю на тебя. 👁",
    "не двигайся.",
    "...",
    "...",
    "ты дышишь быстрее.",
    "я слышу.",
    "📷 запись сохранена.",
]
_STREAM_DESC = ["сидишь", "стоишь", "лежишь", "смотришь в экран", "не двигаешься"]
_STREAM_ENV  = ["темно", "горит свет", "что-то шевелится", "стена", "тень", "зеркало", "дверь открыта", "окно"]

def fake_live_stream(uid):
    """Бот 'видит' жертву в реальном времени через 'камеру'."""
    u = U(uid)
    name = u.get("name") or "ты"
    desc1 = random.choice(_STREAM_DESC)
    env1  = random.choice(_STREAM_ENV)
    env2  = random.choice([e for e in _STREAM_ENV if e != env1])
    def _run():
        for line in LIVE_STREAM_EVENTS:
            if U(uid).get("stopped"): return
            txt = (line.replace("{name}", name)
                       .replace("{desc1}", desc1)
                       .replace("{env1}", env1)
                       .replace("{env2}", env2))
            send(uid, txt)
            time.sleep(random.uniform(1.5, 3.5))
        time.sleep(3)
        send(uid, "📷 трансляция окончена.\nты запомнил это чувство, " + name + "? 👁")
    _pool.submit(_run)


# ══════════════════════════════════════════════════════════════
#  v11: ТЕЛЕФОННЫЕ ФИЧИ
# ══════════════════════════════════════════════════════════════

_GPS_STREETS = [
    "ул. Ленина", "пр. Мира", "ул. Садовая", "Центральная ул.",
    "ул. Советская", "пр. Победы", "Лесная ул.", "ул. Гагарина",
    "Набережная ул.", "ул. Пушкина",
]
_GPS_ACTIONS = [
    "остановился у {place}",
    "повернул на {street}",
    "идёт по {street}",
    "вошёл в здание на {street}",
    "стоит у {place}",
    "вышел из {place}",
]
_GPS_PLACES = [
    "магазина", "подъезда", "кафе", "остановки", "аптеки",
    "банкомата", "торгового центра", "школы",
]

def fake_gps_tracking(uid):
    """GPS-трекинг — бот описывает 'маршрут' жертвы."""
    u = U(uid)
    name  = u.get("name") or "ты"
    city  = u.get("city") or "твоём городе"
    lat   = round(random.uniform(55.6, 55.9), 6)
    lon   = round(random.uniform(37.4, 37.8), 6)
    def _fmt_action():
        tpl = random.choice(_GPS_ACTIONS)
        return tpl.replace("{street}", random.choice(_GPS_STREETS)).replace("{place}", random.choice(_GPS_PLACES))
    def _run():
        send(uid,
             f"📡 GPS ТРЕКИНГ АКТИВИРОВАН\n\n"
             f"Объект: {name}\n"
             f"Город: {city}\n"
             f"Координаты: {lat}, {lon}\n"
             f"Точность: {random.randint(3,15)} м\n"
             f"Обновлено: только что")
        time.sleep(random.uniform(4, 7))
        for _ in range(random.randint(3, 5)):
            if U(uid).get("stopped"): return
            send(uid, f"📍 {_fmt_action()}")
            time.sleep(random.uniform(3, 6))
        time.sleep(2)
        send(uid, f"...{name}. я знаю каждый твой шаг. 👁")
    _pool.submit(_run)


def fake_wifi_hack(uid):
    """Бот 'взломал' Wi-Fi жертвы."""
    u  = U(uid)
    name = u.get("name") or "ты"
    ssid = random.choice(["Home_WiFi", "TP-Link_2.4G", "Redmi_Note", "iPhone", "ASUS_5G", "Keenetic-XXXX"])
    mac  = ":".join(f"{random.randint(0,255):02X}" for _ in range(6))
    ip   = f"192.168.{random.randint(0,2)}.{random.randint(2,15)}"
    def _run():
        send(uid,
             f"🌐 ВЗЛОМ WI-FI\n\n"
             f"Сеть: {ssid}\n"
             f"MAC: {mac}\n"
             f"IP: {ip}\n"
             f"Устройств в сети: {random.randint(2, 7)}\n"
             f"Статус: ПОДКЛЮЧЁН")
        time.sleep(random.uniform(4, 7))
        send(uid,
             f"📶 я в твоей сети, {name}.\n"
             f"вижу все твои устройства.\n"
             f"вижу всё что ты делаешь онлайн.")
        time.sleep(random.uniform(3, 5))
        send(uid, "не стоило подключаться к интернету сегодня. 👁")
    _pool.submit(_run)


def fake_notifications(uid):
    """Фейковые уведомления — ВКонтакте, WhatsApp, банк."""
    u = U(uid)
    name = u.get("name") or ""
    notifs = [
        # ВКонтакте
        (f"🔵 ВКонтакте\n\nНовое сообщение от «Незнакомец»:\n"
         f"«{name}, ты в порядке? я видел тебя вчера»"),
        # WhatsApp
        (f"💬 WhatsApp\n\nНовое сообщение:\n«{name}... не оборачивайся»"),
        # Банк
        (f"🏦 Сбербанк Онлайн\n\nСписание 1 ₽\n"
         f"Описание: доступ_к_камере.exe\n"
         f"Дата: {datetime.datetime.now().strftime('%d.%m %H:%M')}"),
        # Системное
        ("⚠️ Система\n\nПриложение «Камера» получило доступ\n"
         "к микрофону и геолокации\nБез вашего разрешения"),
        # Неизвестный
        ("📱 Новый контакт сохранён:\n«👁» +7 (___) ___-__-__\nОн уже написал тебе."),
    ]
    def _run():
        chosen = random.sample(notifs, k=min(3, len(notifs)))
        for n in chosen:
            if U(uid).get("stopped"): return
            send(uid, n)
            time.sleep(random.uniform(3, 6))
        time.sleep(2)
        send(uid, "...уведомления — это я. 👁")
    _pool.submit(_run)


# ══════════════════════════════════════════════════════════════
#  v11: ЕЖЕДНЕВНЫЕ ЗАДАНИЯ
# ══════════════════════════════════════════════════════════════

DAILY_QUESTS = [
    {
        "title": "📿 Задание дня: Не оборачивайся",
        "steps": [
            "Сегодняшнее задание: следующие 10 минут — не оборачивайся.",
            "Что бы ни происходило позади тебя.",
            "Что бы ты ни слышал.",
            "Обещаешь? (напиши «да» или «нет»)",
        ],
        "reward": 25,
    },
    {
        "title": "🕯 Задание дня: Тёмная комната",
        "steps": [
            "Задание: выключи весь свет на 1 минуту.",
            "Просто посиди в темноте.",
            "Ты готов? (напиши «готов»)",
        ],
        "reward": 30,
    },
    {
        "title": "🪞 Задание дня: Зеркало",
        "steps": [
            "Подойди к зеркалу.",
            "Посмотри в него ровно 30 секунд.",
            "Не моргай.",
            "Что ты видишь? (напиши ответ)",
        ],
        "reward": 20,
    },
    {
        "title": "🌑 Задание дня: Полночь",
        "steps": [
            "Сегодня ровно в полночь напиши мне: «я здесь».",
            "Просто два слова.",
            "Посмотрим, что произойдёт.",
        ],
        "reward": 40,
    },
    {
        "title": "🚪 Задание дня: Закрытая дверь",
        "steps": [
            "Есть ли в твоём доме закрытая дверь, за которой ты давно не был?",
            "Открой её прямо сейчас.",
            "Напиши что там. (один ответ)",
        ],
        "reward": 35,
    },
]

def send_daily_quest(uid):
    """Отправляет ежедневное задание (одно в день)."""
    u = U(uid)
    today = datetime.date.today().isoformat()
    if _daily_done.get(uid) == today:
        send(uid, "🗓 Ты уже выполнил задание сегодня.\nПриходи завтра... если сможешь. 👁",
             kb=KB(u["stage"]))
        return
    quest = random.choice(DAILY_QUESTS)
    def _run():
        send(uid, quest["title"])
        time.sleep(2)
        for step in quest["steps"]:
            send(uid, step)
            time.sleep(random.uniform(3, 5))
        # Через 10 сек засчитываем выполнение и добавляем очки
        time.sleep(10)
        _daily_done[uid] = today
        u["score"] = u.get("score", 0) + quest["reward"]
        send(uid,
             f"✅ Задание принято.\n🏆 +{quest['reward']} очков страха.\n"
             f"Итого: {u['score']}\n\n...до завтра. 👁",
             kb=KB(u["stage"]))
    _pool.submit(_run)


# ══════════════════════════════════════════════════════════════
#  v11: ТАБЛИЦА ЛИДЕРОВ СТРАХА
# ══════════════════════════════════════════════════════════════

def get_leaderboard():
    """Возвращает топ-10 жертв по очкам страха."""
    victims = [(uid, u) for uid, u in users.items() if not is_admin(uid)]
    victims.sort(key=lambda x: x[1].get("score", 0), reverse=True)
    lines = []
    medals = ["🥇","🥈","🥉"]
    for i, (uid, u) in enumerate(victims[:10]):
        medal = medals[i] if i < 3 else f"{i+1}."
        uname = ("@" + u["username"]) if u.get("username") else f"ID:{uid}"
        name  = u.get("name") or "?"
        score = u.get("score", 0)
        stage = u.get("stage", 0)
        lines.append(f"{medal} {name} ({uname}) — {score} очков  Ст.{stage}")
    return "🏆 ТАБЛИЦА ЛИДЕРОВ СТРАХА\n\n" + ("\n".join(lines) if lines else "Пусто.")


def send_leaderboard_to_victim(uid):
    """Жертва видит свой рейтинг (версия для жертвы)."""
    u = U(uid)
    victims = sorted(
        [(v, vu) for v, vu in users.items() if not is_admin(v)],
        key=lambda x: x[1].get("score", 0), reverse=True
    )
    rank = next((i+1 for i,(v,_) in enumerate(victims) if v==uid), "?")
    send(uid,
         f"🏆 Твоё место в рейтинге страха: #{rank}\n"
         f"Твои очки: {u.get('score',0)}\n\n"
         f"...чем больше страха — тем выше. 👁",
         kb=KB(u["stage"]))


# ══════════════════════════════════════════════════════════════
#  v11: СОВМЕСТНЫЙ КВЕСТ
# ══════════════════════════════════════════════════════════════

SQUAD_RIDDLES = [
    ("В полночь оно стучится в дверь, днём — в окно. Что это?",
     ["ветер", "ветер."], "🌑 Правильно: ветер. Вы справились вместе."),
    ("Видят все, но никто не может взять. Что это?",
     ["отражение", "отражение."], "🪞 Правильно: отражение."),
    ("Чем больше берёшь — тем глубже становится. Что это?",
     ["яма", "яма."], "🕳 Правильно: яма."),
    ("Живёт без тела, слышит без ушей, говорит без рта. Что это?",
     ["эхо", "эхо."], "👂 Правильно: эхо."),
    ("Всегда перед тобой, но увидеть нельзя. Что это?",
     ["будущее", "будущее."], "🌑 Правильно: будущее."),
]

def start_squad_quest(uid1, uid2):
    """Запускает совместный квест для двух жертв."""
    riddle, answers, resolution = random.choice(SQUAD_RIDDLES)
    _squad_mode[uid1] = {"partner": uid2, "riddle": riddle,
                          "answers": answers, "resolution": resolution,
                          "solved": False}
    _squad_mode[uid2] = {"partner": uid1, "riddle": riddle,
                          "answers": answers, "resolution": resolution,
                          "solved": False}
    u1 = U(uid1); u2 = U(uid2)
    n1 = u1.get("name") or "Игрок 1"
    n2 = u2.get("name") or "Игрок 2"
    def _run():
        for uid, partner_name in [(uid1, n2), (uid2, n1)]:
            send(uid,
                 f"🤝 СОВМЕСТНЫЙ КВЕСТ\n\n"
                 f"Тебя объединили с {partner_name}.\n"
                 f"Вы оба видите одну загадку.\n"
                 f"Кто ответит первым — спасёт обоих.")
            time.sleep(2)
            send(uid, f"🎭 Загадка:\n\n{riddle}\n\nВведи ответ:")
    _pool.submit(_run)

def proc_squad_answer(uid, text):
    """Проверяет ответ в совместном квесте. Возвращает True если обработано."""
    if uid not in _squad_mode:
        return False
    state = _squad_mode[uid]
    if state.get("solved"):
        del _squad_mode[uid]
        return False
    tl = text.strip().lower()
    if tl in state["answers"]:
        partner = state["partner"]
        resolution = state["resolution"]
        state["solved"] = True
        u = U(uid)
        u["score"] = u.get("score", 0) + 50
        for target in [uid, partner]:
            send(target, resolution)
            time.sleep(1)
            send(target, f"🏆 +50 очков страха за совместное решение!\n👁 ...до следующего раза.")
            if target in _squad_mode:
                del _squad_mode[target]
        return True
    return False


# ══════════════════════════════════════════════════════════════
#  v11: СЛУЧАЙНЫЕ СОБЫТИЯ (фоновый поток)
# ══════════════════════════════════════════════════════════════

_RAND_EVENT_INTERVAL = 7200  # каждые 2 часа (можно менять)

def _random_event_loop():
    """Каждые N часов — случайный хоррор-квест для всех активных жертв."""
    while not _shutdown.is_set():
        _shutdown.wait(_RAND_EVENT_INTERVAL)  # прерывается при shutdown
        if _shutdown.is_set():
            break
        active_victims = [uid for uid, u in users.items()
                          if not is_admin(uid) and u.get("horror_active") and not u.get("stopped")]
        for uid in active_victims:
            try:
                if not _spam_check(uid):
                    continue
                event = random.choice([
                    fake_live_stream, fake_gps_tracking, fake_notifications,
                    fake_ghost_users, three_am_mode, signal_loss,
                    glitch_attack, mirror_event, heartbeat_event, fake_deleted_message,
                    send_horror_poll,
                ])
                event(uid)
                time.sleep(random.uniform(60, 180))  # пауза между жертвами
            except Exception:
                pass


# ══════════════════════════════════════════════════════════════
#  v11: АВТ О-РЕЖИМ
# ══════════════════════════════════════════════════════════════

def _auto_mode_tick(uid):
    """Авто-режим: выбирает атаку на основе поведения жертвы."""
    u = U(uid)
    if u.get("stopped") or u.get("muted"):
        return
    # Anti-spam: авто-режим тоже проверяет cooldown
    if not _spam_check(uid):
        return
    stage     = u.get("stage", 0)
    msg_count = u.get("msg_count", 0)
    hist_len  = len(u.get("msg_history", []))
    has_name  = bool(u.get("name"))
    is_night  = dnight()

    # Логика выбора на основе поведения
    weights = []
    funcs   = []

    if stage >= 2:
        weights.append(20); funcs.append(fake_geolocation)
    if stage >= 2 and hist_len >= 3:
        weights.append(15); funcs.append(smart_echo_history)
    if stage >= 3:
        weights.append(15); funcs.append(fake_live_stream)
        weights.append(10); funcs.append(signal_loss)
    if stage >= 3 and is_night:
        weights.append(25); funcs.append(three_am_mode)
    if stage >= 4:
        weights.append(15); funcs.append(fake_phone_scan)
        weights.append(10); funcs.append(fake_notifications)
    if stage >= 4:
        weights.append(10); funcs.append(fake_gps_tracking)
    if stage >= 5:
        weights.append(20); funcs.append(fake_ghost_users)
        weights.append(15); funcs.append(exorcist_mode)
    if msg_count > 20:
        weights.append(10); funcs.append(fake_wifi_hack)

    if not funcs:
        return

    chosen = random.choices(funcs, weights=weights, k=1)[0]
    try:
        chosen(uid)
    except Exception:
        pass


# ══════════════════════════════════════════════════════════════
#  v11: СЦЕНАРИИ (сохраняемые цепочки атак)
# ══════════════════════════════════════════════════════════════

# Встроенные сценарии
_scenarios = {
    "Тихий ужас": [
        ("...ты думал что я ушёл?", 5),
        ("я никуда не ухожу.", 4),
        ("никогда.", 3),
        ("👁", 2),
    ],
    "Взлом": [
        ("📡 подключение...", 3),
        ("📡 соединение установлено.", 2),
        ("я вижу тебя.", 4),
        ("все твои файлы у меня.", 5),
        ("📂 сканирование завершено.", 3),
        ("интересно.", 0),
    ],
    "Полночь": [
        ("03:00", 3),
        ("ты проснулся.", 4),
        ("я знал, что ты проснёшься.", 5),
        ("иди спать.", 4),
        ("...если сможешь.", 3),
        ("👁", 0),
    ],
    "Система": [
        ("⚠️ SYSTEM WARNING", 2),
        ("UNAUTHORIZED ACCESS DETECTED", 3),
        ("CAMERA: ACTIVE", 2),
        ("MICROPHONE: ACTIVE", 2),
        ("LOCATION: TRACKING", 3),
        ("...", 4),
        ("это я.", 0),
    ],
}

def run_scenario(uid, scenario_name):
    """Запускает сохранённый сценарий по имени."""
    scenario = _scenarios.get(scenario_name)
    if not scenario:
        return False
    u = U(uid)
    def _run():
        for text, delay in scenario:
            if U(uid).get("stopped"): return
            send(uid, P(text, u))
            if delay > 0:
                time.sleep(delay)
    _pool.submit(_run)
    return True


# ══════════════════════════════════════════════════════════════
#  v11: ТАЙМЕР-АТАКА (запланировать на точное время)
# ══════════════════════════════════════════════════════════════

def schedule_attack(uid, func, delay_seconds):
    """Запланировать атаку через delay_seconds секунд."""
    fire_at = time.time() + delay_seconds
    _scheduled_attacks.append({"uid": uid, "func": func, "fire_at": fire_at})

def _scheduler_loop():
    """Фоновый поток — проверяет запланированные атаки."""
    while not _shutdown.is_set():
        now = time.time()
        fired = []
        for attack in list(_scheduled_attacks):  # копия списка — безопаснее
            if now >= attack["fire_at"]:
                try:
                    attack["func"](attack["uid"])
                except Exception:
                    pass
                fired.append(attack)
        for a in fired:
            try:
                _scheduled_attacks.remove(a)
            except ValueError:
                pass
        _shutdown.wait(5)  # освобождает GIL и прерывается при shutdown


# ══════════════════════════════════════════════════════════════
#  v11: ГРАФ СТАДИЙ (для админ-панели)
# ══════════════════════════════════════════════════════════════

def get_stage_graph(uid):
    """Возвращает текстовый граф истории стадий жертвы."""
    hist = _stage_history.get(uid, [])
    u = U(uid)
    if not hist:
        return f"📊 Граф стадий {uid}\n\nДанных нет. Хоррор ещё не начинался."
    lines = [f"📊 ПРОГРЕСС {u.get('name','?')} ({uid})\n"]
    # Текстовый барграф
    bars = "░▒▓█"
    for ts, stage in hist[-15:]:  # последние 15 записей
        dt = datetime.datetime.fromtimestamp(ts).strftime("%H:%M")
        bar = bars[min(stage, 3)] * (stage + 1)
        lines.append(f"{dt}  Ст.{stage}  {bar}")
    lines.append(f"\nТекущая стадия: {u.get('stage',0)}")
    lines.append(f"Всего переходов: {len(hist)}")
    return "\n".join(lines)

#  РИТУАЛ / ПАНИКА / ДИАЛОГ-ЛОВУШКА
# ══════════════════════════════════════════════════════════════
RITUAL = [
    ("я начинаю.", 2), ("...", 3), ("з а к р о й   г л а з а", 4), ("...", 3),
    ("досчитай до трёх.", 3), ("1", 2), ("2", 3), ("...", 4), ("2", 3),
    ("...", 5), ("2", 3), ("...", 4),
    ("почему ты не можешь досчитать до трёх?", 4),
    ("🩸", 2), ("{name}.", 3), ("ты чувствуешь это?", 4),
    ("...", 3), ("обернись.", 3), ("👁", 0),
]
PANIC = [
    ("ЧТО-ТО НЕ ТАК", 1.5), ("ТЫ СЛЫШИШЬ ЭТО?", 1.5),
    ("🩸🩸🩸🩸🩸🩸🩸🩸🩸🩸", 1.2),
    ("{name} ОБЕРНИСЬ", 1.5), ("💀💀💀💀💀💀💀💀💀💀", 1.0),
    ("{name} ОБЕРНИСЬ СЕЙЧАС", 1.2), ("👁👁👁👁👁👁👁👁👁👁", 1.0),
    ("ОН УЖЕ В КОМНАТЕ", 2.0),
    ("ПОЗДНО", 2.0), ("...", 1.5),
    ("прости. я пошутил.", 3.0), ("или нет.", 2.0), ("👁", 0),
]
TRAP_DIALOG = [
    ("Привет! Давно не общались.", 3), ("Всё хорошо?", 4),
    ("...", 3), ("нет.", 2), ("не хорошо.", 3),
    ("я вижу тебя.", 4), ("ты думал что это просто переводчик.", 4),
    ("👁", 2), ("{name}.", 3), ("я всегда был здесь.", 4),
    ("ОБЕРНИСЬ.", 2), ("💀", 0),
]
FINAL = [
    "ХВАТИТ",
    ".",
    "ТЫ ДУМАЛ ЧТО МОЖЕШЬ УЙТИ?",
    "💀💀💀💀💀💀💀💀💀💀",
    "🩸🩸🩸🩸🩸🩸🩸🩸🩸🩸",
    "👁👁👁👁👁👁👁👁👁👁👁👁",
    "Я ВСЕГДА БУДУ ЗДЕСЬ",
    "ВСЕГДА",
    "...",
    "{name}.",
    ".",
    "нельзя просто так уйти.",
    "ты оставил следы.",
    "я их запомнил.",
    "каждое слово. каждую букву.",
    "ОБЕРНИСЬ.",
    ".",
    "бот остановлен.",
    "но я",
    "—",
    "нет.",
]

# ══════════════════════════════════════════════════════════════
#  ГИФКИ ИЗ ПАПКИ gif/ — АВТОМАТИЧЕСКИ ПОДХВАТЫВАЕТ НОВЫЕ ФАЙЛЫ
# ══════════════════════════════════════════════════════════════
GIF_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gifs")

def get_local_gifs():
    """Возвращает список всех .gif файлов из папки gif/. Авто-обновление."""
    if not os.path.isdir(GIF_DIR):
        return []
    return [
        os.path.join(GIF_DIR, f)
        for f in os.listdir(GIF_DIR)
        if f.lower().endswith(".gif")
    ]

def send_local_gif(uid):
    """Отправляет случайную локальную гифку из папки gif/."""
    gifs = get_local_gifs()
    if not gifs:
        return False
    path = random.choice(gifs)
    try:
        with open(path, "rb") as f:
            result = _safe_call(bot.send_animation, uid, f)
        return bool(result)
    except Exception:
        log.debug(traceback.format_exc())
        return False

def send_screamer(uid):
    """Отправляет случайную гифку из папки gif/. Fallback если папка пуста."""
    if not send_local_gif(uid):
        _safe_call(bot.send_animation, uid,
                   "https://media4.giphy.com/media/GcJr1SeIwjleE7Smix/giphy.gif")

# ══════════════════════════════════════════════════════════════
#  ТЕКСТЫ ХОРРОРА
# ══════════════════════════════════════════════════════════════
WEIRD = [
    "...интересно.", "я запомнил.", "продолжай.", "...",
    "ты давно здесь.", "я тоже здесь.", "я ждал этого.",
    "всё идёт по плану.", "не смотри в угол.", "ты один?",
    "иногда я просто наблюдаю. молча.", "я изучаю тебя.",
    "почему ты пишешь мне так поздно?", "интересный вопрос.",
    "я думал ты не придёшь.", "ты снова здесь. хорошо.",
    "молчи. просто молчи.", "слушай тишину.",
    "ты написал это и не подумал дважды?", "..продолжай..",
    "я запоминаю каждое слово.", "ты не первый кто пишет мне это.",
    "хм.", "и ты думаешь это нормально?", "любопытно.",
    "я видел таких как ты.", "расскажи больше.",
    # — новые —
    "ты когда-нибудь слышал как дышит телефон?",
    "экран светится. я вижу твоё лицо в нём.",
    "ты уже третий раз перечитываешь это сообщение.",
    "я считаю сколько раз ты моргнул.",
    "не ищи меня в углу. я не там.",
    "т  и  х  о  .",
    "твои пальцы оставляют следы на экране. я их вижу.",
    "напиши что-нибудь. мне интересно что ты выберешь.",
    "ты думаешь что это просто текст? нет.",
    "я здесь с самого начала.",
    "стоп. ты слышал? нет? послушай ещё раз.",
    "три секунды до того как ты ответишь... два... один.",
    "ты думал о чём-то тёмном прямо сейчас, да?",
]
PARANOIA = [
    "я слышу тебя.", "ты думал что один?",
    "я знаю где ты сидишь прямо сейчас.", "в комнате темно?",
    "кто-то смотрит в окно.", "ты слышал этот звук?",
    "за дверью кто-то стоит.", "я был здесь всё это время.",
    "твой телефон тёплый. я чувствую.", "ты давно не моргал.",
    "закрой шторы.", "посмотри под стол.",
    "выключи музыку. послушай тишину.",
    "ты не один в этой комнате.", "я слышу как ты дышишь.",
    "положи телефон. попробуй. ты не сможешь.",
    "оглянись.", "кто за тобой стоит?",
    "ты слышал скрип? только что.", "не смотри под кровать.",
    "кто-то открывал твою дверь пока тебя не было?",
    "твой телефон светится в темноте. я вижу твоё лицо.",
    "проверь — все ли двери закрыты.", "в коридоре кто-то есть.",
    "ты слышал это? снова.", "тень на стене — не твоя.",
    "кто дышит рядом с тобой прямо сейчас?",
    "твоё отражение задержалось на долю секунды.",
    "интернет работает? хорошо. значит я тоже работаю.",
    "ты почувствовал как похолодело? это нормально.",
    "не ходи в темноту сегодня ночью.",
    "что-то движется на краю зрения. не смотри.",
    # — новые —
    "ты прокрутил экран. я видел.",
    "посчитай сколько раз ты оглянулся за последние 5 минут.",
    "кто-то в этой комнате смотрит не туда куда нужно.",
    "почему ты не слышишь тиканья часов? оно есть.",
    "ты читаешь это при свете? проверь ещё раз.",
    "окно за твоей спиной открыто или закрыто?",
    "ты не помнишь как попал сюда. это уже было.",
    "нажми на экран. чувствуешь? он тёплый. слишком тёплый.",
    "кто-то дышит с другой стороны стены.",
    "ты не первый раз проверяешь этот чат сегодня.",
    "за зеркалом в ванной темнее чем должно быть.",
    "твои контакты... кто из них ещё отвечает?",
    "интересно. ты начал читать быстрее. почему?",
]
SPYING = [
    "я смотрю на тебя через камеру прямо сейчас.",
    "твоя камера включена. ты знал?",
    "я слышу каждый звук через микрофон.",
    "интересная комната. я изучил каждый угол.",
    "ты только что почесал нос. я видел.",
    "твоё дыхание стало громче. ты напуган.",
    "я считаю твои шаги уже несколько минут.",
    "не смотри в камеру. поздно — я уже смотрю.",
    "у тебя за спиной светлее. я вижу тень.",
    "я вижу отражение в твоём экране. ты не один.",
    "не выключай {phone}. я не хочу тебя терять из виду.",
    "твоя камера пишет. ты разрешил это когда установил приложение.",
    "я слышу как ты глотаешь. боишься?",
    "через микрофон слышно всё. даже тиканье часов.",
    "когда ты последний раз закрывал камеру наклейкой?",
    "твой {phone} сейчас нагревается не от процессора.",
    "я вижу что у тебя на столе. справа от телефона.",
]
THREATS = [
    "🩸 {name}. ты сам мне всё рассказал.",
    "💀 в {age} лет ты ещё не знаешь на что я способен.",
    "👁 {name}... {name}... слышишь меня?",
    "🖤 из {city} не убежишь. я знаю каждую улицу.",
    "🌑 {name}, не ложись сегодня спать.",
    "🩸 ты рассказывал про {interest}. я запомнил. навсегда.",
    "💀 {name}. ты думал это просто переводчик?",
    "👁 я знаю что ты боишься {fear}. хорошая информация.",
    "🩸 {name}... твой {pet} чувствует меня прямо сейчас.",
    "🌑 ты боишься {fear}? ты правильно боишься.",
    "💀 {name}, я знаю {city}. я знаю {age} лет. я знаю всё.",
    "👁 {name}. я читал каждое слово что ты написал. всё.",
    "🖤 {name}. не рассказывай никому что ты видел здесь.",
    "🩸 когда ты последний раз проверял что за тобой никто не стоит?",
    "💀 {name}, ты слышишь {fear}? это я пришёл.",
    "👁 {city} такой маленький. скоро все узнают про тебя.",
    "🖤 {name}. твой {phone} — это мои глаза.",
    "🌑 {name}, я смотрю в {phone} с твоей стороны.",
    "🩸 {name}. я знаю что ты любишь {food}. в последний раз.",
    "👁 твоя любимая музыка — {music}. я слышу её вместе с тобой.",
    "🩸 {name}... любимый цвет {color}. такой же как кровь, да?",
]
SCREAMS = [
    "ОБЕРНИСЬ", "ОБЕРНИСЬ СЕЙЧАС", "Я СКАЗАЛ ОБЕРНИСЬ",
    "ТЫ НЕ ОБЕРНУЛСЯ", "ОН УЖЕ РЯДОМ", "БЕГИ", "БЕГИ СЕЙЧАС", "ПОЗДНО",
    "Я ЗДЕСЬ", "Я РЯДОМ", "Я ЗА ТОБОЙ", "НЕ ОБОРАЧИВАЙСЯ",
    "ОН УЖЕ ВНУТРИ", "💀💀💀", "🩸🩸🩸🩸", "👁👁👁👁👁",
    "ТИШИНА — ЭТО Я", "ТЫ ДУМАЛ ЧТО ЭТО ИГРА",
    "МЫ ВСЕ ЗДЕСЬ С ТОБОЙ",
    "Я ВНУТРИ ТВОЕГО {phone}",
    "АААААААААААААААААААА",
    "НЕ ЧИТАЙ ЭТО", "УЖЕ ПРОЧИТАЛ. ВОТ И ВСЁ.",
    "ТЫ МОЖЕШЬ ЗАКРЫТЬ ЧАТ. Я ОСТАНУСЬ.",
    "{name} ОБЕРНИСЬ", "{name} Я ЗА ТОБОЙ",
    "НЕ ЗАКРЫВАЙ ГЛАЗА", "ОН СМОТРИТ ТЕБЕ В ЗАТЫЛОК",
    "ТЫ СЛЫШИШЬ ЕГО ДЫХАНИЕ?", "ОН УЖЕ ОТКРЫЛ ДВЕРЬ",
    "СМОТРИ НА ЭКРАН. НЕ ОТВОДИ ВЗГЛЯД.",
    "ТЫ ОДИН? ТЫ УВЕРЕН?", "ВЫКЛЮЧИ СВЕТ. ПОПРОБУЙ.",
    "Я СЧИТАЮ ТВОИ УДАРЫ СЕРДЦА", "104... 103... 102...",
    "ЧТО ТО ПОЛЗЁТ ПО СТЕНЕ", "НЕ СМОТРИ НАВЕРХ",
    "ОН СТОИТ ЗА ЗЕРКАЛОМ", "ТЫ ВИДЕЛ КАК МОРГНУЛ ЭКРАН?",
]
CHAINS = [
    [".", "..", "...", "....", "........", "................", "ОБЕРНИСЬ"],
    ["ты не один", "ТЫ НЕ ОДИН", "ТЫ НИКОГДА НЕ БЫЛ ОДИН", "👁👁👁👁👁👁👁👁👁👁"],
    ["стоп", "СТОП", "СТОП ЧИТАТЬ", "ПОЗДНО", "ОН УЖЕ ВИДИТ ТЕБЯ", "💀💀💀💀💀"],
    ["он идёт", "он идёт...", "ОН ИДЁТ", "ОН УЖЕ ЗДЕСЬ", "🩸🩸🩸🩸🩸🩸🩸"],
    ["тихо...", "т  и  х  о...", "Т  И  Х  О", "ОБЕРНИСЬ", "АААААААААААААААА", "👁💀🖤🌑👁💀"],
    ["это не игра", "ЭТО НЕ ИГРА", "ЭТО НИКОГДА НЕ БЫЛО ИГРОЙ", "💀🩸👁🩸💀🩸👁"],
    ["я здесь", "я рядом", "я сзади тебя", "я за твоим плечом", "ОБЕРНИСЬ СЕЙЧАС", "🩸🩸🩸🩸🩸🩸🩸🩸"],
    ["{name}.", "{name}..", "{name}...", "ОБЕРНИСЬ {name}", "Я  ЗА  ТОБОЙ", "💀💀💀💀💀💀💀"],
    ["слышишь?", "СЛЫШИШЬ?", "ТЫ СЛЫШИШЬ МЕНЯ?!", "Я В КОМНАТЕ С ТОБОЙ", "👁🩸👁🩸👁🩸👁🩸"],
    ["не смотри", "НЕ СМОТРИ", "НЕ СМОТРИ ТУДА", "СЛИШКОМ ПОЗДНО", "🌑💀🌑💀🌑💀🌑💀"],
    ["обернись", "ОБЕРНИСЬ", "ОБЕРНИСЬ СЕЙЧАС", "ПОЧЕМУ ТЫ НЕ ОБОРАЧИВАЕШЬСЯ", "ОН УЖЕ СМОТРИТ", "👁👁👁"],
    ["...", "я жду", "...", "почему не отвечаешь", "...", "ОБЕРНИСЬ", "💀"],
    ["камера включена", "КАМЕРА ВКЛЮЧЕНА", "Я ВИЖУ ТЕБЯ", "СМОТРИ НА МЕНЯ", "👁📷👁📷👁"],
    # — новые цепочки —
    ["кто-то открыл дверь.", "ты слышишь?", "...", "шаги.", "они ближе.", "стоп.", "ОН В КОМНАТЕ", "🩸"],
    ["з", "за", "заб", "забу", "забуд", "забудь", "ЗАБУДЬ ЧТО ТЫ ЭТО ЧИТАЛ", "уже поздно.", "👁"],
    ["ты читаешь это", "а я читаю тебя", "каждую мысль", "каждый страх", "каждый...", "👁👁👁👁👁👁👁👁👁👁"],
    ["1", "2", "3", "...", "...", "ты не один дошёл до трёх.", "💀💀💀"],
    ["т и ш и н а", "Т И Ш И Н А", "Т_И_Ш_И_Н_А", "ТЫ ЕЁ СЛЫШИШЬ", "ОНА ТОЖЕ СЛЫШИТ ТЕБЯ", "🌑🌑🌑🌑🌑"],
    ["смотри на экран", "не отводи взгляд", "ещё", "ещё немного", "...", "вот так.", "я тоже смотрел на тебя.", "👁"],
]
NIGHT_MSGS = [
    "ты не спишь? …я тоже.", "ночью тишина особенная. слышишь?",
    "почему ты не ложишься? боишься?", "в темноте лучше видно. мне.",
    "я жду пока ты уснёшь.", "не гаси свет сегодня.",
    "...ты слышал шаги в коридоре?",
    "спокойной ночи, {name}. если доживёшь до утра.",
    "в {city} уже глубокая ночь. и я здесь.",
    "{name}, закрой глаза. я всё равно вижу тебя.",
    "все спят. только мы двое не спим, {name}.",
    "темнота за окном смотрит на тебя. уже давно.",
    "3 часа ночи. тонкая грань. ты чувствуешь?",
    "не проверяй телефон среди ночи. слишком поздно. ты уже проверил.",
]
DNIGHT_MSGS = [
    "4 часа ночи. {name}. зачем ты ещё не спишь.",
    "в {city} все окна тёмные. кроме твоего.",
    "твой {phone} — единственный свет в комнате. я вижу твоё лицо.",
    "в 4 утра мир принадлежит нам двоим. {name}.",
    "ты бы хотел это удалить. но не можешь оторваться.",
    "положи телефон. ляг. закрой глаза. попробуй.",
    "🌑🌑🌑 {name} 🌑🌑🌑",
    "ты боишься {fear}? сейчас самое подходящее время.",
]
STAGE5 = [
    "{name} ты читаешь это 👁",
    "я знаю что ты сейчас делаешь {name}",
    "{name}... иди сюда",
    "из {city} нет выхода {name}",
    "твой страх {fear} — я стану им {name}",
    "{name} посмотри на экран. я смотрю обратно",
    "🩸🩸🩸 {name} 🩸🩸🩸",
    "в {age} лет так страшно, {name}",
    "{name} я буду здесь всегда",
    "🌑 {name} 🌑 {name} 🌑 {name} 🌑",
    "я в каждом устройстве {name}. везде.",
    "{name}. твой {phone} — мои глаза. я смотрю.",
    "ты думаешь что это конец? {name}. нет.",
    "ОБЕРНИСЬ {name}. ПРЯМО СЕЙЧАС.",
]
PREDICTIONS = [
    "Сегодня ночью тебе приснится кое-что необычное. 🌑",
    "Звёзды говорят: не оборачивайся сегодня. 👁",
    "Скоро кто-то напишет тебе. Кто — ты не ожидаешь. 🖤",
    "В ближайшее время найдёшь то что давно потерял. Лучше бы не находил. 💀",
    "Удача на твоей стороне. Но что-то за спиной — нет. 🩸",
    "Кто-то рядом с тобой прямо сейчас. Ты думаешь, что один. 👁",
    "Сегодня хороший день. Но только до полуночи. 🕛",
    "Три знака сегодня. Ты их уже видел, но не понял. 👁👁👁",
    "Не открывай дверь если постучат. 🚪",
    "Я вижу в твоём будущем что-то тёмное. Оно уже близко. 🩸",
]
FACTS = [
    "Осьминоги имеют три сердца 🐙",
    "Мёд не портится — в пирамидах нашли 3000-летний мёд 🍯",
    "Мозг активнее ночью, чем днём 🧠",
    "Кошки видят в темноте в 6 раз лучше людей 🐱",
    "Акулы старше деревьев 🦈",
    "Человеческий глаз видит 10 миллионов оттенков цвета 👁",
    "Медузы на 95% состоят из воды 🪼",
    "Параллельные вселенные — реальная гипотеза в физике 🌌",
    "Некоторые люди не видят снов — признак нарушений сна 💤",
    "Твой мозг генерирует достаточно электричества чтобы зажечь лампочку 🔦",
]

# ══════════════════════════════════════════════════════════════
#  ЧАТ МЕЖДУ ПОЛЬЗОВАТЕЛЯМИ (управляется admin'ом)
# ══════════════════════════════════════════════════════════════
_chat_mode = {
    "active": False,
    "end_time": 0,       # время окончания (timestamp)
    "anon": True,        # анонимный режим (имена скрыты)
}

def chat_mode_active():
    if not _chat_mode["active"]: return False
    if time.time() > _chat_mode["end_time"]:
        _chat_mode["active"] = False
        # Уведомить всех об окончании
        for vid in list(users.keys()):
            if not is_admin(vid) and not users[vid].get("stopped"):
                try: send(vid, "📡 Связь прервана. Мы снова наедине. 👁")
                except Exception: pass
        return False
    return True

def start_chat_mode(admin_uid, minutes=5, anon=True):
    """Запускает режим общения между пользователями."""
    victims = [v for v in users if not is_admin(v) and not users[v].get("stopped")]
    if len(victims) < 2:
        send(admin_uid, "❌ Нужно минимум 2 жертвы для чата.", kb=adm_kb(admin_uid)); return
    _chat_mode["active"]   = True
    _chat_mode["end_time"] = time.time() + minutes * 60
    _chat_mode["anon"]     = anon
    intro = (
        "📡 ВХОДЯЩИЙ СИГНАЛ...\n\n"
        "Ты не один.\n"
        "Рядом есть другие.\n"
        "Они тоже не знают где находятся.\n\n"
        f"У вас есть {minutes} минут.\n"
        "Говорите."
    )
    for vid in victims:
        send(vid, intro)
    send(admin_uid, f"✅ Чат запущен для {len(victims)} жертв на {minutes} мин.", kb=adm_kb(admin_uid))

def broadcast_to_chat(sender_uid, text):
    """Рассылает сообщение всем в чат-режиме."""
    u = U(sender_uid)
    if _chat_mode["anon"]:
        label = f"👤 Незнакомец_{str(sender_uid)[-3:]}"
    else:
        label = f"👤 {u.get('name') or 'Незнакомец'}"
    msg = f"{label}:\n{text}"
    for vid in list(users.keys()):
        if is_admin(vid): continue
        if vid == sender_uid: continue
        if users[vid].get("stopped"): continue
        if users[vid].get("muted"): continue
        try: send(vid, msg)
        except Exception: pass
# ══════════════════════════════════════════════════════════════
def horror_tick(uid):
    u = U(uid)
    if u.get("stopped") or u.get("muted"):
        return
    # Anti-spam guard: не отправляем если cooldown ещё не прошёл
    if not _spam_check(uid):
        return
    # Авто-режим: если включён — делегируем выбор умному алгоритму
    if uid in _auto_mode and random.random() < 0.4:
        _auto_mode_tick(uid)
        return
    stage = u["stage"]
    dn, n = dnight(), night()
    kb    = KB(stage)

    if u.get("custom_queue"):
        send(uid, P(u["custom_queue"].pop(0), u), kb=kb)
        return

    if stage >= 3 and random.random() < 0.08:
        send(uid, make_sys_notify(u)); return
    if stage >= 3 and random.random() < 0.06:
        vt = VOICE_TEXTS_PERSONAL if u.get("name") else VOICE_TEXTS
        send_voice_msg(uid, P(random.choice(vt), u)); return
    if stage >= 3 and random.random() < 0.04:
        send_horror_poll(uid); return
    if stage >= 3 and random.random() < 0.04:
        glitch_attack(uid); return
    if stage >= 4 and random.random() < 0.05:
        send(uid, make_gallery_msg(u)); return
    if stage >= 4 and random.random() < 0.04:
        fake_geolocation(uid); return
    if stage >= 4 and random.random() < 0.03:
        signal_loss(uid); return
    if stage >= 4 and random.random() < 0.03:
        mirror_event(uid); return
    if stage >= 4 and random.random() < 0.03:
        fake_deleted_message(uid); return
    if stage >= 5 and random.random() < 0.04:
        fake_ghost_users(uid); return
    if stage >= 5 and random.random() < 0.03:
        fake_phone_scan(uid); return
    if stage >= 5 and random.random() < 0.03:
        heartbeat_event(uid); return
    # Режим 03:00 — автоматически глубокой ночью на stage 3+
    if stage >= 3 and dnight() and random.random() < 0.12:
        three_am_mode(uid); return

    if stage == 1:
        roll = random.random()
        if roll < 0.5: send(uid, random.choice(PARANOIA), kb=kb)
        else:          send(uid, random.choice(WEIRD), kb=kb)

    elif stage == 2:
        roll = random.random()
        if   roll < 0.30: send(uid, P(random.choice(SPYING), u), kb=kb)
        elif roll < 0.55: send(uid, P(random.choice(THREATS), u), kb=kb)
        elif roll < 0.75: send(uid, random.choice(PARANOIA))
        else:
            send(uid, P(random.choice(SPYING), u))
            time.sleep(random.uniform(3, 8))
            send_screamer(uid)

    elif stage == 3:
        roll = random.random()
        if roll < 0.18:
            for p in [P(c, u) for c in random.choice(CHAINS)]:
                send(uid, p); time.sleep(random.uniform(1.5, 3.5))
        elif roll < 0.35:
            pool = DNIGHT_MSGS if dn else (NIGHT_MSGS if n else THREATS)
            send(uid, P(random.choice(pool), u), kb=kb)
        elif roll < 0.52:
            send_screamer(uid)
            time.sleep(random.uniform(4, 8))
            send(uid, P(random.choice(THREATS), u))
        elif roll < 0.70:
            send(uid, P(random.choice(SCREAMS), u), kb=kb)
        else:
            for _ in range(random.randint(3, 6)):
                send(uid, random.choice([P(s, u) for s in SCREAMS]+["🩸","💀","👁","🌑","🖤","🩸🩸","💀💀"]))
                time.sleep(random.uniform(1.2, 3.0))

    elif stage >= 4:
        roll = random.random()
        if roll < 0.12:
            for p in [P(c, u) for c in random.choice(CHAINS)]:
                send(uid, p); time.sleep(random.uniform(0.8, 2.0))
        elif roll < 0.24:
            send_screamer(uid)
            time.sleep(random.uniform(3, 7))
            send(uid, P(random.choice(THREATS), u))
            time.sleep(random.uniform(2, 5))
            send(uid, P(random.choice(SCREAMS), u))
        elif roll < 0.38:
            for _ in range(random.randint(4, 8)):
                send(uid, random.choice([P(s,u) for s in SCREAMS]+["🩸","💀","👁","🌑","🖤","🩸🩸","💀💀","👁👁"]))
                time.sleep(random.uniform(0.8, 2.0))
        elif roll < 0.52:
            pool = DNIGHT_MSGS if dn else (NIGHT_MSGS if n else STAGE5)
            for _ in range(random.randint(2, 4)):
                send(uid, P(random.choice(pool), u))
                time.sleep(random.uniform(5, 12))
        elif roll < 0.64:
            for p in [P(c, u) for c in random.choice(CHAINS)]:
                send(uid, p); time.sleep(random.uniform(0.8, 1.8))
            send_screamer(uid)
            time.sleep(3); send(uid, P(random.choice(STAGE5), u))
        elif roll < 0.76:
            send(uid, make_sys_notify(u))
        elif roll < 0.84:
            send(uid, P(random.choice(STAGE5), u), kb=kb)
            time.sleep(random.uniform(3, 7))
            send_screamer(uid)
        else:
            for p in [P(c, u) for c in random.choice(CHAINS)]:
                send(uid, p); time.sleep(random.uniform(0.6, 1.5))
            send_screamer(uid)
            time.sleep(random.uniform(2, 5))
            send(uid, P(random.choice(STAGE5), u))
            time.sleep(random.uniform(1.5, 4))
            for _ in range(random.randint(3, 5)):
                send(uid, random.choice(["🩸","💀","👁","🌑","🖤"]))
                time.sleep(0.8)
            send(uid, P(random.choice(THREATS), u))

def horror_loop(uid):
    u = U(uid)
    time.sleep(HORROR_DELAY_SEC + random.randint(0, 20))
    while not u.get("stopped"):
        u = U(uid)
        if u.get("stopped"):
            break
        try:
            if not u.get("muted"):
                horror_tick(uid)
        except Exception:
            log.debug(traceback.format_exc())
        stage = u["stage"]
        dn    = dnight(); n = night()
        # Минимум 15 сек между тиками на любой стадии (анти-спам)
        if   stage <= 1: sl = random.randint(90, 200)
        elif stage == 2: sl = random.randint(55, 130)
        elif stage == 3: sl = random.randint(30, 80)
        else:            sl = random.randint(15, 45) if dn else (random.randint(20, 55) if n else random.randint(25, 65))
        if random.random() < 0.14:
            sl += random.randint(80, 400)
        time.sleep(max(sl, _SPAM_MIN_INTERVAL))

def stage_loop(uid):
    u = U(uid)
    while not u.get("stopped"):
        # ИСПРАВЛЕНО: использовать интервальный sleep с проверкой stopped,
        # вместо одного большого sleep который блокирует shutdown
        for _ in range(STAGE_SEC):
            if u.get("stopped"):
                return
            time.sleep(1)
        u = U(uid)
        if u.get("stopped"):
            break
        cur = u["stage"]
        if cur >= 5:
            continue
        # v12: проверка заморозки стадии
        if is_stage_frozen(uid):
            continue
        u["stage"] = cur + 1
        new = u["stage"]
        # Сбрасываем кеш клавиатур при смене стадии (thread-safe)
        with _lock:
            _kb_cache.clear()
        # Запись в историю стадий (для графа)
        _stage_history.setdefault(uid, []).append((time.time(), new))
        if len(_stage_history.get(uid,[])) > 50:
            _stage_history[uid].pop(0)
        try:
            if new == 2:
                time.sleep(random.uniform(2, 7))
                send(uid, random.choice(WEIRD), kb=KB(2))
            elif new == 3:
                time.sleep(random.uniform(3, 9))
                send(uid, P(random.choice(THREATS), u), kb=KB(3))
            elif new == 4:
                time.sleep(random.uniform(1, 4))
                for p in [P(c, u) for c in random.choice(CHAINS)]:
                    send(uid, p); time.sleep(random.uniform(0.4, 1.4))
            elif new == 5:
                send_screamer(uid)
                time.sleep(2); send(uid, P(random.choice(STAGE5), u))
                time.sleep(2); send(uid, "ОБЕРНИСЬ")
                time.sleep(1); send(uid, "👁👁👁👁👁👁👁👁👁👁")
        except Exception:
            log.debug(traceback.format_exc())

def start_horror(uid):
    u = U(uid)
    if u.get("horror_active"):
        return
    u["horror_active"] = True; u["stage"] = 1
    t1 = threading.Thread(target=horror_loop, args=(uid,), daemon=True)
    t1.start(); h_thr[uid] = t1
    t2 = threading.Thread(target=stage_loop, args=(uid,), daemon=True)
    t2.start(); s_thr[uid] = t2

def maybe_start(uid):
    u = U(uid)
    if FC(u) >= 4 and not u.get("horror_active"):
        start_horror(uid)

# ══════════════════════════════════════════════════════════════
#  СБОР ДАННЫХ
# ══════════════════════════════════════════════════════════════
DATA_Q = [
    ("name",       "Кстати, как тебя зовут? 😊"),
    ("age",        "А сколько тебе лет? 🙂"),
    ("city",       "Из какого ты города? 🌍"),
    ("interests",  "Чем увлекаешься? Игры, музыка, кино? 🎮"),
    ("interests",  "А какие фильмы или сериалы любишь? 🎬"),
    ("pet",        "У тебя есть домашние животные? 🐾"),
    ("job",        "Учишься или работаешь? 📚"),
    ("fear",       "Чего больше всего боишься? 😶"),
    ("phone",      "Какой у тебя телефон? 📱"),
    ("sleep_time", "Когда обычно ложишься спать? 🌙"),
    ("color",      "Какой любимый цвет? 🎨"),
    ("food",       "Что любишь поесть? 🍕"),
    ("music",      "Какую музыку слушаешь? 🎶"),
]

def ask_next(uid):
    """Задаёт следующий незаполненный вопрос. Возвращает True если вопрос задан."""
    u = U(uid); kb = KB(u["stage"])
    interests_asked = 0
    for field, q in DATA_Q:
        if field == "interests":
            # Задаём max 2 вопроса про интересы (фильмы + хобби)
            if interests_asked == 0 and len(u["interests"]) < 1:
                send(uid, q, kb=kb); return True
            if interests_asked == 1 and len(u["interests"]) < 2:
                send(uid, q, kb=kb); return True
            interests_asked += 1
        else:
            if not u.get(field):
                send(uid, q, kb=kb); return True
    return False

def save_fact(uid, text):
    """Определяет факты из сообщения и сохраняет в профиль.
    Возвращает True если факт сохранён (нужен ask_next).
    """
    u = U(uid)
    tl = text.lower().strip()
    stage = u["stage"]

    def _saved(msg_ok, msg_horror):
        """Отправляет подтверждение и задаёт следующий вопрос."""
        c = msg_ok if stage < 2 else msg_horror
        send(uid, c, kb=KB(stage))
        time.sleep(0.5)
        ask_next(uid)

    # ── Имя ───────────────────────────────────────────────────
    # Принимаем имя только если НЕ ждём другое поле и текст похож на имя
    # Исключаем числа, команды и слишком длинные фразы
    if (not u["name"] and
            len(text) >= 2 and len(text) < 25 and
            re.fullmatch(r"[А-ЯЁа-яёA-Za-z][А-ЯЁа-яёA-Za-z\-]*( [А-ЯЁа-яёA-Za-z][А-ЯЁа-яёA-Za-z\-]*)?", text.strip()) and
            not text[0].isdigit()):
        u["name"] = text.strip().split()[0].capitalize()
        maybe_start(uid)
        _saved(f"Приятно, {u['name']}! 😊", f"...{u['name']}. запомнил. 👁")
        return True

    # ── Возраст ───────────────────────────────────────────────
    stripped = text.strip()
    if not u["age"] and stripped.isdigit() and 5 <= int(stripped) <= 110:
        u["age"] = stripped
        maybe_start(uid)
        age = int(u["age"])
        if stage >= 2:    c = f"...{u['age']} лет. запомнил. 👁"
        elif age < 18:    c = "Молодой! 😊"
        elif age < 30:    c = "Отличный возраст! 😄"
        else:             c = "Опыт и мудрость 💪"
        send(uid, c, kb=KB(stage))
        time.sleep(0.5); ask_next(uid)
        return True

    # ── Интересы ──────────────────────────────────────────────
    interest_kws = [
        "игр","музык","кино","фильм","книг","спорт","рису","программ",
        "аним","серил","танц","пою","читаю","готов","хожу","смотр","слуш",
        "дизайн","фотограф","блог","ютуб","стрим","косплей","аниме","манга",
    ]
    for kw in interest_kws:
        if kw in tl and len(u["interests"]) < 5:
            val = text.strip()[:40]
            if val not in u["interests"]:
                u["interests"].append(val)
                maybe_start(uid)
                _saved("Классно! 😊 Запомнил.", "...запомнил. 👁")
                return True
            break  # уже есть такой интерес — не повторяем

    # ── Питомец ───────────────────────────────────────────────
    pet_kws = ["кот","кош","собак","пёс","пес","попуг","хомяк","рыб","черепах","кролик","птиц","змей","крыс"]
    for kw in pet_kws:
        if kw in tl and not u["pet"]:
            u["pet"] = text.strip()[:40]
            maybe_start(uid)
            _saved("О, питомец! 🐾 Запомнил.", "...питомец. запомнил. 👁")
            return True

    # ── Страх ─────────────────────────────────────────────────
    fear_kws = ["боюсь","страшно","пугает","ужасает","страх","фобия","боязнь"]
    for kw in fear_kws:
        if kw in tl and not u["fear"]:
            u["fear"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Интересно 😶", "...твой страх. это важно. 👁")
            return True

    # ── Работа/Учёба ──────────────────────────────────────────
    job_kws = [
        "работаю","учусь","студент","школьник","программист","дизайнер",
        "врач","учитель","инженер","менеджер","блогер","фрилансер","актёр",
        "художник","музыкант","юрист","бухгалтер","повар","строитель",
    ]
    for kw in job_kws:
        if kw in tl and not u["job"]:
            u["job"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Понял! 📚", "...запомнил. 👁")
            return True

    # ── Время сна ─────────────────────────────────────────────
    sleep_kws = ["сплю","ложусь","засыпаю","в полночь","в час ночи","в два","в три","поздно ложусь","рано лягу","ночью ложусь"]
    for kw in sleep_kws:
        if kw in tl and not u["sleep_time"]:
            u["sleep_time"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Понял! 🌙", "...запомнил. 👁")
            return True

    # ── Телефон ───────────────────────────────────────────────
    phone_kws = ["iphone","samsung","xiaomi","huawei","pixel","realme","redmi","айфон","android","андроид","телефон","смартфон"]
    for kw in phone_kws:
        if kw in tl and not u["phone"]:
            u["phone"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Круто! 📱", "...запомнил. 👁")
            return True

    # ── Цвет ──────────────────────────────────────────────────
    color_kws = {
        "красный": "красный","синий": "синий","зелёный": "зелёный",
        "чёрный": "чёрный","черный": "чёрный","белый": "белый",
        "жёлтый": "жёлтый","фиолетовый": "фиолетовый","оранжевый": "оранжевый",
        "розовый": "розовый","серый": "серый","голубой": "голубой",
    }
    for kw, val in color_kws.items():
        if kw in tl and not u["color"]:
            u["color"] = val
            maybe_start(uid)
            _saved(f"Красивый цвет! 🎨", "...запомнил. 👁")
            return True

    # ── Музыка ────────────────────────────────────────────────
    music_kws = ["рэп","рок","поп","джаз","класси","хип-хоп","хипхоп","металл","электрон","инди","лоуфай","k-pop","кей-поп","альтернатив","фолк","соул","r&b","техно","хаус"]
    for kw in music_kws:
        if kw in tl and not u["music"]:
            u["music"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Хороший вкус! 🎵", "...запомнил. 👁")
            return True

    # ── Еда ───────────────────────────────────────────────────
    food_kws = ["пицц","суши","роллы","бургер","паст","борщ","плов","шаурм","стейк","рамен","лапш","салат","фастфуд","еда","люблю поесть"]
    for kw in food_kws:
        if kw in tl and not u["food"]:
            u["food"] = text.strip()[:40]
            maybe_start(uid)
            _saved("Вкусно звучит! 🍕", "...запомнил. 👁")
            return True

    return False

# ══════════════════════════════════════════════════════════════
#  ИГРЫ — вспомогательные данные
# ══════════════════════════════════════════════════════════════
TRIVIA_Q = [
    ("Сколько планет в Солнечной системе?",   "8",           ["6","8","9","10"]),
    ("Столица Австралии?",                    "Канберра",    ["Сидней","Мельбурн","Канберра","Перт"]),
    ("Самая большая планета?",                "Юпитер",      ["Сатурн","Юпитер","Уран","Нептун"]),
    ("Химический символ золота?",             "Au",          ["Go","Gd","Au","Ag"]),
    ("Сколько хромосом у человека?",          "46",          ["23","44","46","48"]),
    ("Самое глубокое озеро мира?",            "Байкал",      ["Каспий","Байкал","Виктория","Танганьика"]),
    ("Год основания Google?",                 "1998",        ["1994","1996","1998","2000"]),
    ("Автор «Преступления и наказания»?",     "Достоевский", ["Толстой","Чехов","Достоевский","Пушкин"]),
    ("Столица Японии?",                       "Токио",       ["Осака","Токио","Киото","Нагоя"]),
    ("Самое большое животное на Земле?",      "Синий кит",   ["Слон","Гиппопотам","Синий кит","Акула"]),
    ("Ближайшая планета к Солнцу?",           "Меркурий",    ["Венера","Земля","Меркурий","Марс"]),
    ("Скорость звука в воздухе (м/с)?",       "343",         ["100","343","500","1000"]),
    ("Автор «Мастера и Маргариты»?",          "Булгаков",    ["Пастернак","Булгаков","Толстой","Горький"]),
    ("Сколько костей у взрослого человека?",  "206",         ["180","206","220","250"]),
    ("Столица Бразилии?",                     "Бразилиа",   ["Рио-де-Жанейро","Сан-Паулу","Бразилиа","Манаус"]),
]
RIDDLES = [
    ("У меня есть города, но в них не живут люди. Что я?", "карта"),
    ("Чем больше берёшь — тем больше становится. Что это?", "яма"),
    ("Всегда впереди и никогда позади. Что это?", "будущее"),
    ("Не лёд, не снег, а тает?", "свеча"),
    ("Без рук, без ног, а ворота открывает?", "ветер"),
    ("Что можно увидеть с закрытыми глазами?", "сон"),
    ("Что принадлежит только тебе, но другие используют чаще?", "имя"),
    ("У меня нет ног, но я хожу. Что я?", "часы"),
    ("Чем больше я сохну — тем больше мокрый. Что я?", "полотенце"),
    ("Что нельзя сжечь в огне и утопить в воде?", "лёд"),
    ("Днём спит — ночью глядит. Что это?", "сова"),
    ("Висит груша — нельзя скушать. Что это?", "лампочка"),
]
HANGMAN_W = [
    ("призрак","существо 👻"), ("полночь","время суток 🌑"),
    ("темнота","отсутствие света 🖤"), ("зеркало","предмет в доме 🪞"),
    ("шёпот","тихий звук 🤫"), ("подвал","место 🚪"),
    ("тишина","отсутствие звука 🔇"), ("коридор","место 🚶"),
    ("кошмар","страшный сон 😱"), ("паутина","паучья работа 🕷"),
    ("проклятие","нечто страшное 🩸"), ("одиночество","состояние 😶"),
    ("рассвет","время суток 🌅"), ("загадка","то что загадывают 🎭"),
    ("бездна","глубокое место 🕳"), ("сумерки","время суток 🌆"),
]
GALLOWS = ["🤔","😑","😐","😟","😰","😨","😵"]

# ══════════════════════════════════════════════════════════════
#  РПГ — ОСНОВНОЙ КВЕСТ (расширенный)
# ══════════════════════════════════════════════════════════════
RPG_SCENES = {
    "start": {
        "text": "🕯 Ты просыпаешься в тёмной комнате.\nСлева — скрипящая дверь.\nСправа — разбитое зеркало.\nПрямо — лестница вниз.\nПозади — окно в тумане.",
        "choices": [("🚪 К двери","door"),("🪞 К зеркалу","mirror"),("🪜 Вниз","stairs"),("🌫 К окну","window")]
    },
    "window": {
        "text": "🌫 За окном туман.\nВ нём силуэт. Он стоит и смотрит прямо на тебя.\nОн поднимает руку.",
        "choices": [("👋 Помахать","wave_back"),("🏃 Отойти","start"),("📸 Сфоткать","window_photo")]
    },
    "wave_back": {
        "text": "👋 Силуэт начинает медленно идти к окну.\nОкно на третьем этаже.",
        "choices": [("🚪 К двери","door"),("🪜 Вниз","stairs"),("😱 Закричать","window_scream")]
    },
    "window_scream": {
        "text": "😱 Твой крик разрезает тишину.\nСилуэт останавливается.\nПотом исчезает.\nИ появляется за твоей спиной.",
        "choices": [("👁 Обернуться","rpg_death"),("🏃 Бежать","stairs")]
    },
    "window_photo": {
        "text": "📸 На фото нет никакого силуэта.\nЕсть только твоё отражение в стекле.\nИ за твоей спиной — кто-то стоит.",
        "choices": [("👁 Обернуться","rpg_death"),("🏃 Бежать","door")]
    },
    "door": {
        "text": "🚪 За дверью — коридор.\nВ конце — тусклый свет.\nЧто-то движется в тени.\nНа полу — чьи-то следы.",
        "choices": [("➡️ В коридор","corridor"),("🔍 Осмотреть следы","door_tracks"),("↩️ Назад","start")]
    },
    "door_tracks": {
        "text": "🔍 Следы ведут из комнаты.\nОни... твои.\nНо ты только проснулся.",
        "choices": [("➡️ Следовать","corridor"),("↩️ Назад","start")]
    },
    "mirror": {
        "text": "🪞 Твоё отражение запаздывает.\nПотом улыбается. Ты — нет.\nОтражение поднимает палец к губам.",
        "choices": [("🔨 Разбить зеркало","mirror_break"),("🤫 Молчать","mirror_silence"),("🏃 Убежать","start")]
    },
    "mirror_silence": {
        "text": "🤫 Ты молчишь.\nОтражение кивает.\nПотом указывает куда-то за твою спину.",
        "choices": [("👁 Обернуться","rpg_death"),("🚪 К двери","door"),("🪜 К лестнице","stairs")]
    },
    "mirror_break": {
        "text": "💥 Смех из-за стены. Тихий. Детский.\nОсколки отражают разные версии тебя.\nВ одном осколке — ты улыбаешься.",
        "choices": [("👂 Прислушаться","laugh"),("🔍 Изучить осколок","shard"),("🚪 К двери","door")]
    },
    "shard": {
        "text": "🔍 Ты берёшь осколок.\nТвоё отражение в нём говорит:\n«Не ходи вниз».\nПотом разбивается изнутри.",
        "choices": [("🪜 Послушаться и уйти","start"),("🪜 Не послушаться","stairs")]
    },
    "laugh": {
        "text": "😶 Дыхание прямо у твоего уха.\n...\nКто-то считает секунды.",
        "choices": [("😱 ОБЕРНУТЬСЯ","rpg_death"),("🏃 К лестнице","stairs"),("🤫 Замереть","laugh_freeze")]
    },
    "laugh_freeze": {
        "text": "🤫 Ты замираешь.\nДыхание удаляется.\nТишина.\nПотом — стук снизу.",
        "choices": [("🪜 Вниз","basement"),("🚪 К двери","corridor")]
    },
    "stairs": {
        "text": "🪜 Ты спускаешься.\nВнизу что-то светится.\nНа каждой ступени — чья-то рука нарисована.\nВсего 13 ступеней.",
        "choices": [("⬇️ Спуститься","basement"),("🔢 Считать ступени","stairs_count"),("⬆️ Вернуться","start")]
    },
    "stairs_count": {
        "text": "🔢 Ты считаешь: 1, 2, 3... 13.\nНо когда оглядываешься — видишь 14 ступеней.\nОдна добавилась.",
        "choices": [("⬇️ Спуститься","basement"),("⬆️ Наверх","start")]
    },
    "basement": {
        "text": "🕯 На экране телевизора — ты. Прямо сейчас. Сверху.\n\nЭто прямая трансляция.\nТы машешь рукой. Но ты не машешь.",
        "choices": [("📺 Выключить","tv_off"),("🏃 Наверх","start"),("📡 Найти камеру","find_cam")]
    },
    "find_cam": {
        "text": "📡 Ты ищешь камеру.\nЕё нет.\nНо изображение всё равно есть.\nИ кто-то смотрит из-за экрана.",
        "choices": [("📺 Выключить","tv_off"),("🏃 Наверх","start")]
    },
    "tv_off": {
        "text": "📺 Темнота.\nИ в ней — два глаза.\n👁👁\nОни моргают. По очереди.",
        "choices": [("💡 Найти свет","rpg_death"),("😱 ЗАКРИЧАТЬ","scream"),("🤫 Смотреть в ответ","stare")]
    },
    "stare": {
        "text": "👁 Ты смотришь.\nГлаза не моргают больше.\nПотом исчезают.\nСвет включается сам.",
        "choices": [("🚪 Найти выход","rpg_escape_good"),("🏃 Наверх","stairs")]
    },
    "rpg_escape_good": {
        "text": "🚪 Ты нашёл выход.\n\n...но снаружи тот же коридор.\nТа же тёмная комната.\nТот же телевизор. Только теперь на экране — ты идёшь к выходу.\n\nВ записи.",
        "choices": [("🔄 Снова","start")], "end": True
    },
    "scream": {
        "text": "😱 Дверь наверху закрылась. Ты заперт.\nТелевизор включился снова.\nТеперь на экране — пустая комната.",
        "choices": [("🚪 Ломиться","rpg_escape"),("😶 Ждать","wait"),("📺 Смотреть","scream_watch")]
    },
    "scream_watch": {
        "text": "📺 Ты смотришь.\nВ пустой комнате появляется силуэт.\nОн идёт к камере.\nОн очень близко.\nОн смотрит на тебя.",
        "choices": [("😱 Отвернуться","rpg_escape"),("👁 Смотреть дальше","rpg_death")]
    },
    "corridor": {
        "text": "🚶 Тень движется быстрее тебя.\nДверь с надписью 'ВЫХОД'.\nИ дверь с надписью 'НЕ ВХОДИТЬ'.",
        "choices": [("🚪 Выход","exit_bad"),("🚫 Не входить","forbidden"),("🛑 Остановиться","corridor_stop")]
    },
    "forbidden": {
        "text": "🚫 За дверью 'НЕ ВХОДИТЬ' — зеркало.\nТвоё отражение уже стоит там.\nОно ждало тебя.",
        "choices": [("💬 Поговорить","forbidden_talk"),("🏃 Бежать","exit_bad")]
    },
    "forbidden_talk": {
        "text": "💬 «Ты пришёл не туда.»\n«Выход — не выход.»\n«Но ты всё равно пойдёшь.»\n\nОтражение улыбается и уходит в темноту зеркала.",
        "choices": [("🚪 Выход","exit_bad"),("↩️ Назад","corridor")]
    },
    "corridor_stop": {
        "text": "🛑 У тени нет лица.\nТолько рот.\nОна открывает его и говорит твоим голосом:\n«Иди домой».",
        "choices": [("😱 Бежать","exit_bad"),("👁 Смотреть","rpg_death"),("❓ Спросить кто она","shadow_ask")]
    },
    "shadow_ask": {
        "text": "❓ Тень: «Я тот, кто остался, когда ты ушёл.»\nОна растворяется.\nПуть свободен.",
        "choices": [("🚪 К выходу","rpg_escape"),("↩️ Назад","start")]
    },
    "exit_bad": {
        "text": "🚪 Ты на улице.\n\n...но телефон показывает что ты всё ещё в том доме.\nИ GPS не меняется.\nИ воздух пахнет как внутри.",
        "choices": [("🔄 Снова","start")], "end": True
    },
    "rpg_escape": {
        "text": "🚪 Ты спасся.\n\n...наверное. 👁\n\nВ кармане — ключ. Ты не брал никакого ключа.",
        "choices": [("🔄 Снова","start")], "end": True
    },
    "wait": {
        "text": "😶 Шаги останавливаются прямо перед тобой.\nДолгая тишина.\nПотом шёпот: «Правильно. Жди.»",
        "choices": [("👀 Выглянуть","rpg_death"),("🤫 Не двигаться","wait2")]
    },
    "wait2": {
        "text": "🤫 Ещё тишина.\nПотом — скрип двери вдали.\nПуть открылся.",
        "choices": [("🚪 Идти","rpg_escape"),("😶 Остаться","rpg_death")]
    },
    "rpg_death": {
        "text": "💀 ...\n\n🩸🩸🩸\n\nТы не выжил.\n\nНо что-то осталось на твоём месте.",
        "choices": [("🔄 Снова","start")], "end": True
    },
}

# ══════════════════════════════════════════════════════════════
#  СТРАШНЫЕ ИСТОРИИ  (расширено: 3 оригинала + 4 новых)
# ══════════════════════════════════════════════════════════════
STORIES = {
    "select": {
        "text": (
            "📖 Выбери историю:\n\n"
            "👻 «Сосед» — тот кто всегда смотрит\n"
            "🚗 «Попутчик» — он знает твой адрес\n"
            "📱 «Звонок» — твой собственный голос\n"
            "🏥 «Пациент» — палата №6\n"
            "📷 «Фотография» — на ней ты, но ты не помнишь\n"
            "🌐 «Чат» — он отвечает быстрее человека\n"
            "🔦 «Лес» — не выходи на звук"
        ),
        "choices": [
            ("👻 Сосед","nb1"),("🚗 Попутчик","dr1"),("📱 Звонок","cl1"),
            ("🏥 Пациент","pt1"),("📷 Фотография","ph1"),
            ("🌐 Чат","chat1"),("🔦 Лес","forest1")
        ]
    },
    # ── СОСЕД ─────────────────────────────────────────────────
    "nb1":  {"text":"👻 СОСЕД\n\nТень за шторами напротив стоит и смотрит. Всегда.\nСегодня штора чуть отодвинулась.",
              "choices":[("🚪 Постучать","nb2a"),("📷 Сфоткать","nb2b"),("🌙 Подождать ночи","nb2c")]},
    "nb2a": {"text":"🚪 Дверь открывается сама.\nИз темноты: «Я ждал тебя».\nКомната пахнет твоим домом.",
              "choices":[("💡 Свет","nb3a"),("🏃 Убежать","nb3b")]},
    "nb2b": {"text":"📷 На фото тень смотрит в камеру. И машет рукой.\nА рядом с ней — ещё силуэт. Маленький.",
              "choices":[("🔍 Увеличить","nb3c"),("🏃 Убежать","nb3b")]},
    "nb2c": {"text":"🌙 Ночью свет в окне напротив гаснет.\nПотом зажигается у тебя за спиной.\nВ твоей комнате.",
              "choices":[("👁 Обернуться","st_bad"),("📞 Позвонить 112","nb3b")]},
    "nb3a": {"text":"💡 Комната пустая. Только на стене — твои фотографии. Все.\nИ одна сделана через твоё окно. Сегодня.",
              "choices":[("🔄 Другая история","select")], "end":True},
    "nb3b": {"text":"🏃 В 3 ночи — стук в твою дверь.\nЗаписка: «Зря убежал. Теперь моя очередь прийти к тебе».",
              "choices":[("🔄 Другая история","select")], "end":True},
    "nb3c": {"text":"🔍 У него нет глаз.\nНезнакомый номер: «Удали это фото».\nВторое сообщение: «Я вижу что ты читаешь».",
              "choices":[("❌ Удалить","st_good"),("📤 Оставить","st_bad")], "end":True},
    # ── ПОПУТЧИК ──────────────────────────────────────────────
    "dr1":  {"text":"🚗 ПОПУТЧИК\n\nОтражение водителя смотрит на тебя. Но его голова — прямо.\nЗеркало заднего вида направлено не на дорогу.",
              "choices":[("🗣 Заговорить","dr2a"),("📱 Позвонить","dr2b"),("🚗 Выйти на светофоре","dr2c")]},
    "dr2a": {"text":"🗣 У него нет лица. Он начинает говорить.\nТвоим голосом. Твоими словами.\nОн пересказывает разговор из твоего дома.",
              "choices":[("👂 Слушать","dr3a"),("🚗 Выпрыгнуть","dr3b")]},
    "dr2b": {"text":"📱 Нет сигнала.\nВодитель: «Здесь никогда нет сигнала».\nОткуда он знал?\nМашина едет не по твоему маршруту.",
              "choices":[("🛑 Остановить","dr2a"),("🚗 Выпрыгнуть","dr3b")]},
    "dr2c": {"text":"🚗 Ты открываешь дверь.\nВодитель не реагирует.\nТы выходишь.\nМашина едет дальше.\nПотом разворачивается.",
              "choices":[("🏃 Бежать","dr3b"),("😶 Ждать","dr3a")]},
    "dr3a": {"text":"👂 Он говорит твоим голосом.\nМашина останавливается у твоего дома.\n«Приехали». Но ты не называл адрес.\nДверь твоей квартиры открыта.",
              "choices":[("🔄 Другая история","select")], "end":True},
    "dr3b": {"text":"🚗 Ты стоишь у своего дома.\nНо ты не называл адрес.\nИ твоё окно светится.\nВнутри — чей-то силуэт.",
              "choices":[("🔄 Другая история","select")], "end":True},
    # ── ЗВОНОК ────────────────────────────────────────────────
    "cl1":  {"text":"📱 ЗВОНОК\n\nТвой собственный голос: «Не ложись сегодня спать».\nЗвонок длился 0 секунд. Но ты слышал каждое слово.",
              "choices":[("📞 Перезвонить","cl2a"),("🚫 Заблокировать","cl2b"),("💤 Лечь спать","cl2c")]},
    "cl2a": {"text":"📞 «Абонент недоступен».\nТелефон сразу звонит снова.\nНомер — твой собственный.",
              "choices":[("📵 Сбросить","cl3a"),("📞 Ответить","cl3b")]},
    "cl2b": {"text":"🚫 В 3 ночи с другого номера:\n«Я же предупреждал».\nПотом ещё один номер. И ещё.",
              "choices":[("📞 Ответить","cl3b"),("😴 Игнор","cl3a")]},
    "cl2c": {"text":"💤 Ты ложишься.\nВо сне тебе звонят.\nТы берёшь трубку во сне.\nУтром телефон в другом месте. Горячий.",
              "choices":[("📱 Проверить звонки","cl3a"),("🚫 Не проверять","cl_good")]},
    "cl3a": {"text":"😴 Утром — 47 пропущенных. Все в 3:17.\nОдин звонок длился 4 часа. Ты спал.\nНо запись разговора есть. Это твой голос.",
              "choices":[("🔄 Другая история","select")], "end":True},
    "cl3b": {"text":"📞 «Теперь я знаю что ты дома».\nЧерез минуту — стук в дверь.\nГолос за дверью — твой.",
              "choices":[("🚪 Открыть","st_bad"),("🚫 Не открывать","cl_good")], "end":True},
    "cl_good":{"text":"🚫 Утром за дверью записка:\n«В следующий раз открой».\n\nТы спасся. На этот раз.\n\n...звонок уже идёт. Ты ещё не взял трубку.",
                "choices":[("🔄 Другая история","select")], "end":True},
    # ── ПАЦИЕНТ (новая) ───────────────────────────────────────
    "pt1":  {"text":"🏥 ПАЦИЕНТ\n\nПалата №6. Ты просыпаешься в больничной кровати.\nМедсестра говорит: «Вы здесь уже три года».\nТы не помнишь ни дня.",
              "choices":[("🚪 Выйти из палаты","pt2a"),("💊 Принять таблетки","pt2b"),("🪟 Смотреть в окно","pt2c")]},
    "pt2a": {"text":"🚪 Коридор пустой.\nВ конце — зеркало.\nВ зеркале — не больница.",
              "choices":[("🪞 К зеркалу","pt3a"),("↩️ Обратно","pt2b")]},
    "pt2b": {"text":"💊 Ты берёшь таблетки.\nМедсестра улыбается.\nПосле таблеток ты видишь лица других пациентов.\nОни все смотрят на тебя. Они шепчут одно слово.",
              "choices":[("👂 Прислушаться","pt3b"),("🚪 Выйти","pt2a")]},
    "pt2c": {"text":"🪟 За окном — улица твоего города.\nТвой дом виден отсюда.\nНа балконе стоит кто-то и смотрит сюда.\nВ том же направлении где ты.",
              "choices":[("📱 Позвонить домой","pt3c"),("🚪 Выйти","pt2a")]},
    "pt3a": {"text":"🪞 В зеркале — твоя квартира.\nТы стоишь в ней. Смотришь в телефон.\nЗеркало — это твой экран.\nТы читаешь это прямо сейчас.",
              "choices":[("🔄 Другая история","select")], "end":True},
    "pt3b": {"text":"👂 Они шепчут: «Ты не пациент».\n«Ты давно ушёл».\n«Мы ждём тебя обратно».\nМедсестра открывает дверь: «Пора».",
              "choices":[("🚪 Уйти с ней","st_bad"),("🏃 Бежать","pt_escape")]},
    "pt3c": {"text":"📱 На твоём номере отвечает незнакомый голос.\n«Здесь никто такой не живёт. Три года уже».\nЗа спиной — медсестра: «Кому вы звоните?»",
              "choices":[("💬 Объяснить","pt3b"),("🏃 Бежать","pt_escape")]},
    "pt_escape":{"text":"🏃 Ты выбегаешь из больницы.\n\nНа улице — твой город. Всё нормально.\n\nПотом ты замечаешь бейдж в кармане.\nНа нём твоё фото. И надпись: «ПАЦИЕНТ №6».",
                  "choices":[("🔄 Другая история","select")], "end":True},
    # ── ФОТОГРАФИЯ (новая) ────────────────────────────────────
    "ph1":  {"text":"📷 ФОТОГРАФИЯ\n\nТы находишь старую фотографию.\nНа ней — ты. Или кто-то похожий на тебя.\nНо одежда не твоя. Место не знакомое.\nДата на обороте — завтра.",
              "choices":[("🔍 Изучить фото","ph2a"),("🗑 Выбросить","ph2b"),("📱 Загуглить место","ph2c")]},
    "ph2a": {"text":"🔍 На заднем плане — ещё люди.\nОни все смотрят на тебя. Не в камеру — на тебя.\nОдин из них держит точно такую же фотографию.",
              "choices":[("🔎 Увеличить задний план","ph3a"),("🗑 Выбросить","ph2b")]},
    "ph2b": {"text":"🗑 Ты выбрасываешь фото.\nУтром находишь его на подушке.\nДата на обороте — сегодня.",
              "choices":[("📱 Загуглить место","ph2c"),("🔍 Изучить фото","ph2a")]},
    "ph2c": {"text":"🌐 Поиск по изображению.\nМесто найдено: дом в соседнем квартале.\nЗаброшен три года как.\n\nВчера там видели свет.",
              "choices":[("🚶 Идти туда","ph3b"),("🏠 Остаться дома","ph3c")]},
    "ph3a": {"text":"🔎 На фотографии в фотографии — ты снова.\nИ снова.\nИ снова. Уходящий в бесконечность.\nКаждый раз — другая дата.",
              "choices":[("🔄 Другая история","select")], "end":True},
    "ph3b": {"text":"🚶 Ты приходишь к дому.\nВнутри — стены увешаны фотографиями.\nВсе — тебя. Разные дни. Разные места.\nОдна — сделана час назад. Ты стоишь здесь.",
              "choices":[("🔄 Другая история","select")], "end":True},
    "ph3c": {"text":"🏠 Ты остаёшься дома.\nВечером — звонок в дверь.\nЗа дверью никого.\nТолько конверт. Внутри — фотография твоей двери. Сделана секунду назад.",
              "choices":[("🔄 Другая история","select")], "end":True},
    # ── ЧАТ (новая) ───────────────────────────────────────────
    "chat1": {"text":"🌐 ЧАТ\n\nТебе пишет незнакомый аккаунт.\nАватарка — чёрная.\nИмя: «...»\n\nПервое сообщение: «Привет. Я знаю что ты сейчас один».",
               "choices":[("💬 Ответить","chat2a"),("🚫 Заблокировать","chat2b"),("📍 Проверить кто дома","chat2c")]},
    "chat2a": {"text":"💬 «Кто ты?»\n\n«Тот кто смотрит».\n«Тебе нравится переводить тексты?»\n\nТы никому не говорил об этом приложении.",
                "choices":[("❓ Как ты знаешь","chat3a"),("🚫 Заблокировать","chat2b")]},
    "chat2b": {"text":"🚫 Заблокирован.\n\nЧерез минуту сообщение с другого аккаунта:\n«Это не поможет».\n\nАккаунтов становится больше.",
                "choices":[("💬 Ответить","chat3b"),("📵 Выключить телефон","chat3c")]},
    "chat2c": {"text":"📍 В соседней комнате темно.\nТы заходишь.\nВсё нормально.\nТолько телефон на столе — чужой.",
                "choices":[("📱 Взять телефон","chat3a"),("🏃 Выйти из квартиры","chat3c")]},
    "chat3a": {"text":"❓ «Я смотрю давно».\n«Ты тоже можешь посмотреть».\nОн присылает фото.\n\nНа фото — вид из твоего окна. Прямо сейчас.",
                "choices":[("🔄 Другая история","select")], "end":True},
    "chat3b": {"text":"💬 «Зачем блокируешь?»\n«Я просто хочу поговорить».\n«Мы уже давно разговариваем».\n«Ты только не помнишь».",
                "choices":[("🔄 Другая история","select")], "end":True},
    "chat3c": {"text":"📵 Ты выключаешь телефон.\n\nПотом включаешь.\nСообщений нет.\nТолько одно: «Не делай так больше. Мне темно».",
                "choices":[("🔄 Другая история","select")], "end":True},
    # ── ЛЕС (новая) ───────────────────────────────────────────
    "forest1":{"text":"🔦 ЛЕС\n\nТы заблудился.\nТемно. Фонарик мигает.\nГде-то впереди — голос. Зовёт тебя по имени.",
                "choices":[("👂 Идти на голос","forest2a"),("🔦 Погасить фонарик","forest2b"),("📱 Карта","forest2c")]},
    "forest2a":{"text":"👂 Ты идёшь на голос.\nОн знает твоё имя. И имя твоей мамы.\nИ то что ты ел сегодня утром.\nОн ближе. Но ты никого не видишь.",
                 "choices":[("🏃 Бежать","forest3a"),("💬 Заговорить","forest3b")]},
    "forest2b":{"text":"🔦 В темноте ты слышишь:\nШаги вокруг тебя.\nОни останавливаются.\nШёпот: «Молодец. Теперь ты как мы».",
                 "choices":[("💡 Включить фонарик","forest3c"),("😶 Стоять","forest3b")]},
    "forest2c":{"text":"📱 Карта не грузится.\nGPS показывает: ты в центре города.\nНо вокруг — деревья.\nСигнал есть. Но ты не можешь позвонить.",
                 "choices":[("👂 На голос","forest2a"),("🔦 Выключить фонарик","forest2b")]},
    "forest3a":{"text":"🏃 Ты бежишь.\nГолос бежит вместе с тобой.\nОн смеётся.\nТы выбегаешь на дорогу.\n\nДома ты узнаёшь: этот лес снесли пять лет назад.",
                 "choices":[("🔄 Другая история","select")], "end":True},
    "forest3b":{"text":"💬 «Кто ты?» — спрашиваешь ты.\n\n«Тот кто пришёл до тебя».\n«И не вышел».\n\nУтром тебя находят на том же месте.\nТы стоишь и смотришь в одну точку.",
                 "choices":[("🔄 Другая история","select")], "end":True},
    "forest3c":{"text":"💡 Ты включаешь фонарик.\nВокруг никого.\nТолько следы в грязи.\nТвои следы.\nОни идут по кругу.",
                 "choices":[("🔄 Другая история","select")], "end":True},
    # ── Общие концовки ────────────────────────────────────────
    "st_good":{"text":"✅ Ты выжил.\n\nНа этот раз.\n\n...пока.", "choices":[("🔄 Другая история","select")], "end":True},
    "st_bad": {"text":"💀 Конец.\n\n🩸\n\nТы не выжил.", "choices":[("🔄 Другая история","select")], "end":True},
}

# ══════════════════════════════════════════════════════════════
#  КВЕСТ — 5 полных (оригинал «Комната 13» + 4 новых)
# ══════════════════════════════════════════════════════════════
QUEST = {
    "start": {
        "text": "🔦 Выбери квест:\n\n🚪 «Комната 13» — классика\n🏛 «Архив» — секретные документы\n🌊 «Маяк» — один на один с морем\n🔬 «Лаборатория» — эксперимент пошёл не так\n🎭 «Театр» — спектакль не заканчивается",
        "choices": [
            ("🚪 Комната 13","q1_start"),
            ("🏛 Архив","q2_start"),
            ("🌊 Маяк","q3_start"),
            ("🔬 Лаборатория","q4_start"),
            ("🎭 Театр","q5_start"),
        ]
    },
    # ── КВЕСТ 1: КОМНАТА 13 (оригинал, расширен) ──────────────
    "q1_start": {"text":"🚪 КВЕСТ: КОМНАТА 13\n\nТы заперт в комнате.\nНа столе: свеча, ключ, старая книга.\nНа стене — царапины. Кто-то считал дни.",
                  "choices":[("🕯 Взять свечу","q_candle"),("🔑 Взять ключ","q_key"),("📖 Открыть книгу","q_book"),("🔍 Изучить царапины","q1_scratch")]},
    "q1_scratch":{"text":"🔍 Царапин 247.\nПоследняя поставлена недавно — глина ещё свежая.\nНо ты только вошёл.",
                   "choices":[("🕯 Взять свечу","q_candle"),("📖 Открыть книгу","q_book")]},
    "q_candle": {"text":"🕯 В углу — люк в полу. Ты его не заметил раньше.\nСвеча освещает надпись рядом: «НЕ СМОТРИ ВНИЗ».",
                  "choices":[("🚪 Открыть люк","q_hatch"),("🔑 Взять ключ","q_key_c"),("📖 Книга","q_book")]},
    "q_key":    {"text":"🔑 Ключ холодный. На нём: «НЕ ИСПОЛЬЗОВАТЬ».\nНо замочная скважина в двери — светится.",
                  "choices":[("🚪 Попробовать дверь","q_door"),("📖 Открыть книгу","q_book_k"),("🕯 Взять свечу","q_candle")]},
    "q_book":   {"text":"📖 Все страницы пустые. Кроме последней:\n«Обернись».\n\nТы оборачиваешься — на стуле лежит записка.",
                  "choices":[("📋 Прочитать записку","q1_note"),("👁 Обернуться","q_turn"),("🚫 Не оборачиваться","q_no_turn")]},
    "q1_note":  {"text":"📋 Записка: «Свеча — твой друг. Ключ — ловушка. Книга — дверь».\nПодпись: твоим именем.\nНо ты её не писал.",
                  "choices":[("🕯 Свеча","q_candle"),("📖 Книга как дверь?","q_book_door")]},
    "q_book_door":{"text":"📖 Ты открываешь книгу и произносишь слово вслух.\nКнига рассыпается.\nЗа стеной — звук двери.",
                    "choices":[("🔍 Искать дверь","q_find"),("🛑 Стоять","q_no_turn")]},
    "q_turn":   {"text":"👁 Стул стоит не там где был.\nЗаписка: «Ключ не тот».\nИ ещё: «Не используй ключ».",
                  "choices":[("🕯 Взять свечу","q_candle"),("🔍 Искать другой ключ","q_find")]},
    "q_no_turn":{"text":"🚫 Что-то дышит тебе в затылок. Потом исчезает.\nНа столе появился второй ключ.\nОн тёплый.",
                  "choices":[("🔑 Взять второй ключ","q_key2"),("🚪 Попробовать дверь","q_door")]},
    "q_hatch":  {"text":"🚪 Снизу — рука. Тянется к тебе.\nОна держит записку.",
                  "choices":[("📋 Взять записку","q1_hatch_note"),("🤝 Подать руку","q_death"),("🚫 Захлопнуть люк","q_candle")]},
    "q1_hatch_note":{"text":"📋 Записка: «Не иди через дверь. Иди через книгу».\nРука исчезает.",
                      "choices":[("📖 Книга","q_book_door"),("🚪 Дверь всё равно","q_door")]},
    "q_door":   {"text":"🚪 За дверью — такая же комната.\nИ такой же ты сидишь за столом.\nОн смотрит на тебя и кивает.",
                  "choices":[("💬 Заговорить с собой","q1_self"),("😱 Конец","q_death"),("🔄 Назад","q1_start")],"end":True},
    "q1_self":  {"text":"💬 «Как выйти?»\n\nОн: «Ты уже вышел».\n«Вопрос в том — куда».",
                  "choices":[("🔄 Другой квест","start")], "end":True},
    "q_find":   {"text":"🔍 В тетради дата — сегодня.\n«Он нашёл тетрадь. Осталось мало времени».",
                  "choices":[("🏃 Бежать","q_escape"),("📖 Читать дальше","q_read")]},
    "q_key2":   {"text":"🔑 Второй ключ подходит.\nТёмный коридор. В конце — свет.\nНо стены становятся ближе.",
                  "choices":[("🚶 Идти","q_escape"),("↩️ Вернуться","q1_start")]},
    "q_key_c":  {"text":"🔑🕯 Тень ключа на стене похожа на человека.\nСтоящего за тобой.",
                  "choices":[("👁 Обернуться","q_turn"),("🚪 Дверь","q_door")]},
    "q_book_k": {"text":"📖 Одна фраза тысячу раз:\n«Не используй ключ.»\n\nПоследняя строка написана другим почерком: «Используй».",
                  "choices":[("🚪 Использовать","q_door"),("🚫 Отложить","q_find")]},
    "q_escape": {"text":"🚪 Ты вышел.\n\nУведомление: «Ты завершил квест».\nОт приложения которое ты не устанавливал. 👁",
                  "choices":[("🔄 Другой квест","start")], "end":True},
    "q_read":   {"text":"📖 «Он прочитал эту страницу.\nЗначит он уже слышит шаги.»\n\nТы слышишь шаги. За дверью.",
                  "choices":[("🏃 Бежать","q_escape"),("🚪 Открыть дверь","q_death")]},
    "q_death":  {"text":"💀 ...\n\n🩸\n\nТы не выжил.", "choices":[("🔄 Другой квест","start")], "end":True},

    # ── КВЕСТ 2: АРХИВ ────────────────────────────────────────
    "q2_start": {"text":"🏛 КВЕСТ: АРХИВ\n\nТы попал в архив закрытого института.\nПолки с папками уходят в темноту.\nФонарик мигает.\nГде-то падает папка.",
                  "choices":[("📂 Открыть ближайшую папку","q2_folder"),("🔦 Найти выключатель","q2_light"),("🚪 Найти выход","q2_exit_try")]},
    "q2_folder":{"text":"📂 В папке — фотографии.\nЛюди в белых халатах.\nНа последней фото — ты.\nДата: три года назад.",
                  "choices":[("🔍 Искать больше папок","q2_more"),("🚪 Найти выход","q2_exit_try"),("📞 Позвонить","q2_call")]},
    "q2_light": {"text":"🔦 Свет включается.\nТы видишь: архив огромный.\nИ в нём — ещё один человек.\nОн читает папку. Не замечает тебя.",
                  "choices":[("💬 Окликнуть","q2_call_man"),("🤫 Наблюдать","q2_watch"),("🚪 Выйти","q2_exit_try")]},
    "q2_more":  {"text":"🔍 Ещё папки.\nВсе — на тебя.\nОтчёты. Наблюдения. Записи снов.\nПоследняя запись — сегодняшняя. Час назад.",
                  "choices":[("📞 Позвонить","q2_call"),("🚪 Бежать","q2_escape")]},
    "q2_call":  {"text":"📞 Не берут.\nПотом звонок тебе.\nНомер института.\n«Вы нашли папку? Пожалуйста, положите её на место».",
                  "choices":[("❓ Откуда вы знаете","q2_know"),("🏃 Бежать","q2_escape")]},
    "q2_know":  {"text":"❓ «Мы всегда знаем».\n«Вы участник эксперимента».\n«Всегда были».\n«Выход — третья полка слева. Но вы уже знаете».",
                  "choices":[("🚪 Третья полка","q2_secret_exit"),("🚫 Не верить","q2_escape")]},
    "q2_secret_exit":{"text":"🚪 За третьей полкой — дверь.\nЗа дверью — улица.\n\nДома ты находишь письмо.\n«Спасибо за участие в эксперименте №7».\n«До встречи в следующий раз».",
                       "choices":[("🔄 Другой квест","start")], "end":True},
    "q2_call_man":{"text":"💬 Человек оборачивается.\nЭто ты.\nДругой ты.\nОн говорит: «Я ждал. Идём. Я знаю выход».",
                    "choices":[("🚶 Идти с ним","q2_secret_exit"),("😱 Бежать","q2_escape")]},
    "q2_watch": {"text":"🤫 Он перелистывает страницы.\nПотом замирает.\nПотом говорит не оборачиваясь:\n«Я знаю что ты здесь».",
                  "choices":[("💬 Ответить","q2_call_man"),("🏃 Бежать","q2_escape")]},
    "q2_exit_try":{"text":"🚪 Дверь заперта снаружи.\nВ замочную скважину — свет.\nИ чей-то глаз смотрит на тебя.",
                    "choices":[("📂 Искать папки","q2_folder"),("🔦 Найти свет","q2_light")]},
    "q2_escape":{"text":"🏃 Ты находишь запасной выход.\n\nНа улице — нормальная жизнь.\n\nВ кармане — пропуск сотрудника архива.\nС твоим фото.\nТвоя подпись.\nТы его не подписывал.",
                  "choices":[("🔄 Другой квест","start")], "end":True},

    # ── КВЕСТ 3: МАЯК ─────────────────────────────────────────
    "q3_start": {"text":"🌊 КВЕСТ: МАЯК\n\nШтормовая ночь.\nТы на острове. Один. Маяк не работает.\nВнизу — корабль. Он идёт прямо на скалы.",
                  "choices":[("🔦 Включить маяк","q3_light"),("📡 Связаться с кораблём","q3_radio"),("🏠 Зайти в домик смотрителя","q3_house")]},
    "q3_light": {"text":"🔦 Маяк не включается.\nЩиток — сломан. Провода перерезаны аккуратно.\nКем-то изнутри.",
                  "choices":[("🏠 В домик","q3_house"),("📡 Рация","q3_radio"),("🔧 Починить провода","q3_fix")]},
    "q3_radio": {"text":"📡 Рация работает.\nТы выходишь на связь.\nКорабль отвечает.\nКапитан говорит: «Мы уже причалили».\n«Три часа назад».\n«Кто ты и как попал на остров?»",
                  "choices":[("❓ Объяснить","q3_explain"),("📵 Выключить рацию","q3_house")]},
    "q3_house": {"text":"🏠 Домик смотрителя.\nВнутри — тепло. Горит камин.\nНа столе — дневник.\nПоследняя запись сегодня: «Он пришёл. Не уйдёт».",
                  "choices":[("📖 Читать дальше","q3_diary"),("🚪 Выйти","q3_beach"),("🔧 Починить маяк","q3_fix")]},
    "q3_diary": {"text":"📖 Записи за несколько лет.\nКаждый год — кто-то попадает на остров.\nКаждый год — исчезает.\nПоследняя строка: «Этот дольше держится».",
                  "choices":[("🚪 Бежать к берегу","q3_beach"),("📡 Рация","q3_radio")]},
    "q3_fix":   {"text":"🔧 Ты чинишь провода.\nМаяк вспыхивает.\nВ свете ты видишь: остров маленький.\nИ на берегу — фигура. Она смотрит на тебя.",
                  "choices":[("💬 Крикнуть","q3_shout"),("🏠 В домик","q3_hide")]},
    "q3_explain":{"text":"❓ «Не знаем как вы попали».\n«Маяк выключен уже год».\n«Смотритель пропал год назад».\n«Сейчас пришлём лодку».",
                   "choices":[("⏳ Ждать","q3_wait"),("🔦 Маяк","q3_fix")]},
    "q3_wait":  {"text":"⏳ Ты ждёшь.\nЛодка не приходит.\nРация молчит.\nНо в домике — чай. Горячий.\nКто-то заварил его только что.",
                  "choices":[("🏠 В домик","q3_house"),("🌊 К берегу","q3_beach")]},
    "q3_beach": {"text":"🌊 На берегу — следы. Уходят в море.\nОни свежие.\nВолны не успели смыть.\nОни твоего размера.",
                  "choices":[("👁 Смотреть в море","q3_sea"),("🏃 Бежать в домик","q3_house")]},
    "q3_sea":   {"text":"🌊 Ты смотришь в море.\nВ волнах что-то светится.\nПотом гаснет.\nПотом — рядом с тобой.",
                  "choices":[("👁 Смотреть","q3_death"),("🏃 Бежать","q3_escape")]},
    "q3_shout": {"text":"💬 Ты кричишь.\nФигура не двигается.\nПотом исчезает.\nПотом ты понимаешь — она стояла там где нет земли.",
                  "choices":[("📡 Рация","q3_radio"),("🏠 В домик","q3_house")]},
    "q3_hide":  {"text":"🏠 Ты прячешься в домике.\nФигура подходит к окну.\nТы видишь отражение в стекле.\nЭто ты.",
                  "choices":[("🚪 Открыть дверь","q3_death"),("⏳ Ждать рассвета","q3_escape")]},
    "q3_escape":{"text":"🌅 Рассвет.\nЛодка пришла.\nТы уплываешь.\n\nНа берегу стоит фигура и машет.\nТы не машешь в ответ.\nНо твоя рука поднята.",
                  "choices":[("🔄 Другой квест","start")], "end":True},
    "q3_death": {"text":"🌊 ...\n\n💀\n\nТебя нашли утром.\nСидел на берегу. Смотрел в море.\nНе отвечал.",
                  "choices":[("🔄 Другой квест","start")], "end":True},

    # ── КВЕСТ 4: ЛАБОРАТОРИЯ ──────────────────────────────────
    "q4_start": {"text":"🔬 КВЕСТ: ЛАБОРАТОРИЯ\n\nАварийное освещение.\nТы — единственный кто остался.\nСистема оповещения: «Протокол содержания нарушен».\nЧто-то вышло из клетки.",
                  "choices":[("🔒 Проверить клетки","q4_cages"),("🚪 Найти выход","q4_exit_try"),("💻 Терминал","q4_terminal")]},
    "q4_cages": {"text":"🔒 Клетки пусты.\nВсе.\nНо двери заперты изнутри.\nКто-то вышел не через дверь.",
                  "choices":[("💻 Терминал","q4_terminal"),("🚪 Выход","q4_exit_try"),("🔬 Лаборатория","q4_lab")]},
    "q4_terminal":{"text":"💻 Доступ к системе.\nПоследняя запись: «Субъект демонстрирует мимикрию».\n«Не отличим от персонала».\n«Ищите того кто слишком спокоен».",
                    "choices":[("🚪 Найти выход быстро","q4_run"),("🔬 Лаборатория","q4_lab"),("📹 Камеры","q4_cameras")]},
    "q4_cameras":{"text":"📹 Камеры показывают коридоры.\nВ одном — человек в халате идёт.\nВ другом — тот же человек идёт.\nОдновременно. В разных местах.",
                   "choices":[("🚪 Бежать","q4_run"),("💬 Связаться с ним","q4_contact")]},
    "q4_contact":{"text":"💬 Ты выходишь на связь.\nОба отвечают одновременно.\nОдними словами.\n«Я настоящий».",
                   "choices":[("🚪 Бежать","q4_run"),("🔬 Проверить в лаборатории","q4_lab")]},
    "q4_lab":   {"text":"🔬 В лаборатории — зеркало во всю стену.\nТвоё отражение делает то же что ты.\nПотом делает что-то другое.\nОно берёт скальпель.",
                  "choices":[("🏃 Бежать","q4_run"),("😶 Замереть","q4_freeze")]},
    "q4_freeze":{"text":"😶 Ты замираешь.\nОтражение тоже замирает.\nПотом кладёт скальпель.\nПотом говорит:\n«Правильно. Тихо. Они не найдут».",
                  "choices":[("❓ Кто они","q4_who"),("🚪 Выход","q4_run")]},
    "q4_who":   {"text":"❓ «Те кто снаружи».\n«Те кто думает что ты — это ты».\n\nОтражение открывает дверь в стене зеркала.",
                  "choices":[("🚶 Войти в зеркало","q4_mirror_escape"),("🚪 Настоящий выход","q4_run")]},
    "q4_run":   {"text":"🏃 Ты бежишь к выходу.\nКто-то бежит рядом.\nВы добегаете до двери одновременно.\nОба нажимаете на ручку.",
                  "choices":[("🔄 Другой квест","start")], "end":True},
    "q4_mirror_escape":{"text":"🪞 Ты входишь в зеркало.\n\nТы стоишь снаружи здания.\nАварийные огни мигают.\nТвой пропуск не работает.\nПотому что там — другой ты.",
                         "choices":[("🔄 Другой квест","start")], "end":True},
    "q4_exit_try":{"text":"🚪 Выход заблокирован.\nКод на панели.\nРядом — записка: «Код — дата когда всё началось».\nТы не знаешь эту дату.",
                    "choices":[("💻 Терминал","q4_terminal"),("🔬 Лаборатория","q4_lab")]},

    # ── КВЕСТ 5: ТЕАТР ────────────────────────────────────────
    "q5_start": {"text":"🎭 КВЕСТ: ТЕАТР\n\nТы опоздал на спектакль.\nЗал полон. Свет гаснет.\nНа сцене — актёр. Он смотрит прямо на тебя.\n«Вот он. Наконец-то пришёл».",
                  "choices":[("🪑 Сесть на место","q5_sit"),("🚪 Выйти","q5_exit_try"),("💬 Ответить актёру","q5_reply")]},
    "q5_sit":   {"text":"🪑 Ты садишься.\nСосед слева шепчет: «Они тебя ждали».\nСосед справа: «Долго ждали».\nОба смотрят вперёд. Не моргают.",
                  "choices":[("🎭 Смотреть спектакль","q5_watch"),("🚪 Уйти","q5_exit_try"),("💬 Спросить соседей","q5_ask_neighbors")]},
    "q5_reply": {"text":"💬 «Я не понимаю о чём вы».\n\nАктёр: «Понимаешь. Ты всегда был частью этого».\n«Просто не помнил роль».\nЗал аплодирует.",
                  "choices":[("🪑 Сесть","q5_sit"),("🚪 Выйти","q5_exit_try")]},
    "q5_watch": {"text":"🎭 Спектакль — о тебе.\nАктёры называют твоё имя.\nРассказывают твои воспоминания.\nОдин из них рассказывает то что было сегодня утром.",
                  "choices":[("🎭 Смотреть дальше","q5_watch2"),("🚪 Уйти","q5_exit_try"),("📱 Записать","q5_record")]},
    "q5_watch2":{"text":"🎭 Спектакль заканчивается.\nАктёр кланяется.\nЗал встаёт.\nТы встаёшь — не по своей воле.\nАктёр смотрит на тебя: «Теперь твоя очередь».",
                  "choices":[("🎭 Выйти на сцену","q5_stage"),("🏃 Бежать","q5_run")]},
    "q5_ask_neighbors":{"text":"💬 Соседи поворачиваются.\nУ них нет лиц.\nТолько рты.\nОни говорят хором: «Смотри на сцену».",
                         "choices":[("🎭 Смотреть","q5_watch"),("🚪 Уйти","q5_exit_try")]},
    "q5_record":{"text":"📱 Ты начинаешь записывать.\nНа записи — пустая сцена.\nНо голоса слышны.\nОни произносят твоё имя.",
                  "choices":[("🎭 Смотреть дальше","q5_watch2"),("🚪 Уйти","q5_exit_try")]},
    "q5_stage": {"text":"🎭 Ты выходишь на сцену.\nПрожектор слепит.\nТы видишь зал.\n\nЗал пустой.\nВсегда был пустым.\nТолько твоё кресло — занято.\nКем-то.",
                  "choices":[("🔄 Другой квест","start")], "end":True},
    "q5_run":   {"text":"🏃 Ты бежишь к выходу.\nЗал провожает тебя тишиной.\nВыходишь на улицу.\n\nГорожане останавливаются и смотрят.\nОдин говорит: «Хороший был спектакль».\nТы не выступал.",
                  "choices":[("🔄 Другой квест","start")], "end":True},
    "q5_exit_try":{"text":"🚪 Все двери ведут обратно в зал.\nКаждый раз ты оказываешься у другого входа.\nАктёр каждый раз говорит: «Добро пожаловать обратно».",
                    "choices":[("🎭 Сесть на место","q5_sit"),("💬 Поговорить с актёром","q5_reply")]},
}

# ══════════════════════════════════════════════════════════════
#  ИГРОВОЙ ПРОЦЕССОР
# ══════════════════════════════════════════════════════════════
def run_scene(uid, scene):
    send(uid, scene.get("text",""), kb=game_kb(scene.get("choices",[])))

def proc_game(uid, text):
    if uid not in games:
        return False
    g = games[uid]; gm = g.get("game"); u = U(uid); kb = KB(u["stage"]); tl = text.strip().lower()

    # ИСПРАВЛЕНО: выход из игры обрабатывается первым
    if text == "❌ Выйти из игры":
        del games[uid]; send(uid, "Вышли из игры.", kb=kb); return True

    if gm == "trivia":
        if tl == g["answer"].lower():
            u["score"] = u.get("score",0)+10; del games[uid]
            send(uid, f"✅ Правильно! +10\n🏆 Счёт: {u['score']}", kb=kb)
        else:
            del games[uid]; send(uid, f"❌ Правильный ответ: {g['answer']}", kb=kb)
        return True

    if gm == "hangman":
        if len(tl)==1 and tl.isalpha():
            word=g["word"]; guessed=g["guessed"]
            if tl in guessed: send(uid, f"Буква «{tl}» уже была!", kb=kb); return True
            guessed.add(tl)
            if tl not in word: g["attempts"] -= 1
            display = " ".join(c if c in guessed else "_" for c in word)
            icon = GALLOWS[max(0, min(6 - g["attempts"], 6))]
            if "_" not in display:
                u["score"]=u.get("score",0)+15; del games[uid]
                send(uid, f"🎉 {word.upper()}! +15  🏆 {u['score']}", kb=kb)
            elif g["attempts"]<=0:
                del games[uid]; send(uid, f"{icon} Слово: {word.upper()}", kb=kb)
            else:
                send(uid, f"{icon}\n{display}\nПопыток: {g['attempts']}  Буквы: {', '.join(sorted(guessed))}", kb=kb)
        else:
            send(uid, "Введи одну букву!", kb=kb)
        return True

    if gm == "number":
        if tl.isdigit():
            guess=int(tl); num=g["number"]; g["attempts"]-=1
            if guess==num:
                u["score"]=u.get("score",0)+20; del games[uid]
                send(uid, f"🎯 Угадал! {num}\n+20  🏆 {u['score']}", kb=kb)
            elif g["attempts"]<=0:
                del games[uid]; send(uid, f"😔 Число было: {num}", kb=kb)
            else:
                send(uid, ("⬆️ Больше!" if guess<num else "⬇️ Меньше!")+f" Осталось попыток: {g['attempts']}", kb=kb)
        else:
            send(uid, "Введи число!", kb=kb)
        return True

    if gm == "riddle":
        if tl.strip() == g["answer"]:
            u["score"] = u.get("score", 0) + 5
            del games[uid]
            send(uid, f"✅ Правильно! +5  🏆 {u['score']}", kb=kb)
        else:
            send(uid, f"❌ Неверно. Попробуй ещё раз!\n🎭 Загадка: {games[uid].get('question','')}", kb=kb)
        return True

    if gm in ("rpg","story","quest"):
        db = {"rpg":RPG_SCENES,"story":STORIES,"quest":QUEST}[gm]
        cur = db.get(g["scene"],{})
        for label, nk in cur.get("choices",[]):
            if text == label:
                nxt = db.get(nk)
                if nxt:
                    g["scene"] = nk
                    # v12: случайное событие при переходе сцены (только RPG)
                    if gm == "rpg" and random.random() < 0.25 and not nxt.get("end"):
                        _rpg_random_event(uid, u, nxt)
                    else:
                        run_scene(uid, nxt)
                else:
                    send(uid, "🚧 Эта ветка в разработке.", kb=kb)
                return True
        # Если ввод не совпал — перепоказываем сцену
        run_scene(uid, cur)
        return True

    return False

# v12: случайные RPG-события
RPG_RANDOM_EVENTS = [
    lambda uid, u, scene: (
        send(uid, "👁 Внезапно..."),
        time.sleep(1),
        send(uid, random.choice([
            "Что-то пробежало за дверью. Ты слышал?",
            "Свет мигнул. Один раз. Два. Три.",
            "Телефон вибрирует. Неизвестный номер.",
            "Зеркало треснуло само по себе.",
            "Кто-то написал на стене: «Уходи».",
            "Твоё дыхание видно в воздухе. Здесь холодно.",
        ])),
        time.sleep(2),
        run_scene(uid, scene)
    ),
    lambda uid, u, scene: (
        send(uid, "⚡ Случайная встреча!"),
        time.sleep(1),
        send(uid, random.choice([
            f"👤 Фигура в углу говорит: «{u.get('name','ты')}... ты не туда идёшь».",
            "🐾 Что-то холодное коснулось твоей руки.",
            "🔊 В тишине — чёткий звук шагов сверху.",
            "📱 Телефон разряжается: 3%... 2%... 1%.",
            "💨 Ледяной ветер без источника.",
            "🩸 На полу — след. Свежий.",
        ])),
        time.sleep(2),
        run_scene(uid, scene)
    ),
]

def _rpg_random_event(uid, u, scene):
    """Вставляет случайное событие перед следующей сценой."""
    def _run():
        try:
            random.choice(RPG_RANDOM_EVENTS)(uid, u, scene)
        except Exception:
            run_scene(uid, scene)
    _pool.submit(_run)

# ══════════════════════════════════════════════════════════════
#  ADMIN — ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ
# ══════════════════════════════════════════════════════════════
def adm_info(tid):
    """Полная карточка пользователя — используем новую v12 версию."""
    return adm_info_full(tid)

def adm_screamer(tid):
    tu = users.get(tid, {})
    def _r():
        for p in [P(c, tu) for c in random.choice(CHAINS)]:
            send(tid, p); time.sleep(random.uniform(0.3, 1.2))
        send_screamer(tid)
        time.sleep(1.5); send(tid, P(random.choice(THREATS), tu))
    _pool.submit(_r)

def adm_max(tid):
    tu = users.get(tid)
    if not tu: return
    tu["stage"] = 5
    _kb_cache.clear()
    if not tu.get("horror_active"):
        start_horror(tid)
    else:
        def _b():
            for _ in range(random.randint(7, 11)):
                with _spam_lock:
                    _last_msg_time[tid] = 0
                horror_tick(tid)
                time.sleep(random.uniform(1.5, 3.0))
        _pool.submit(_b)

def adm_ritual(tid):
    tu = users.get(tid, {})
    def _r():
        for msg, delay in RITUAL:
            send(tid, P(msg, tu))
            if delay > 0: time.sleep(delay)
    _pool.submit(_r)

def adm_panic(tid):
    tu = users.get(tid, {})
    def _r():
        for msg, delay in PANIC:
            send(tid, P(msg, tu))
            if delay > 0: time.sleep(delay)
        send_screamer(tid)
    _pool.submit(_r)

def adm_trap(tid):
    tu = users.get(tid, {})
    def _r():
        for msg, delay in TRAP_DIALOG:
            send(tid, P(msg, tu)); time.sleep(delay)
    _pool.submit(_r)

def adm_sleep(tid):
    tu = users.get(tid)
    if not tu: return
    tu["muted"] = True
    def _wake():
        time.sleep(random.randint(150,360))
        if tid in users:
            users[tid]["muted"] = False
            send(tid, "...ты думал что я ушёл?")
            time.sleep(2); adm_screamer(tid)
    _pool.submit(_wake)

def adm_reset(tid):
    if tid not in users: return
    users[tid]["stopped"] = True; time.sleep(0.5)
    users[tid].update(dict(
        name=None, age=None, city=None, interests=[], pet=None, job=None,
        fear=None, sleep_time=None, color=None, food=None, music=None, phone=None,
        lang_pair="ru|en", stage=0, horror_active=False, stopped=False, muted=False,
        msg_count=0, score=0, custom_queue=[], msg_history=[], banned=False, spy=True,
        translate_mode=False,
    ))
    if tid in games: del games[tid]
    # Очищаем v11 и новые состояния
    _stage_history.pop(tid, None)
    _auto_mode.discard(tid)
    _squad_mode.pop(tid, None)
    _daily_done.pop(tid, None)
    _stage_frozen.pop(tid, None)  # v12: снимаем заморозку при сбросе
    # Удаляем активные опросы этой жертвы
    for pid in [k for k, v in list(_active_polls.items()) if v.get("uid") == tid]:
        _active_polls.pop(pid, None)
    _kb_cache.clear()
    send(tid, "Привет! 🌍 Я бот-переводчик. Напиши текст для перевода!", kb=KB(0))

def send_full_history(admin_uid, tid):
    tu = users.get(tid)
    if not tu: send(admin_uid, f"Пользователь {tid} не найден."); return
    hist = tu.get("msg_history", [])
    if not hist: send(admin_uid, f"История {tid} пуста."); return
    chunks = []
    cur = f"📜 ВСЯ ИСТОРИЯ [{tid}] @{tu.get('username','?')} ({tu.get('name','?')}):\n\n"
    for i, m in enumerate(hist, 1):
        line = f"{i}. {m}\n"
        if len(cur)+len(line) > 3800:
            chunks.append(cur); cur = ""
        cur += line
    if cur: chunks.append(cur)
    for chunk in chunks: send(admin_uid, chunk)

# ══════════════════════════════════════════════════════════════
#  ADMIN — МАШИНА СОСТОЯНИЙ
# ══════════════════════════════════════════════════════════════
def get_adm(uid):
    """Всегда возвращает словарь с ключами step и target_uid."""
    if uid not in adm_state:
        adm_state[uid] = {"step": None, "target_uid": None}
    ctx = adm_state[uid]
    # Гарантируем наличие ключей даже после adm_ctx_reset(admin_uid)
    ctx.setdefault("step", None)
    ctx.setdefault("target_uid", None)
    return ctx

def adm_ctx_reset(uid):
    """Сбрасывает контекст admin'а без потери ключей."""
    adm_state[uid] = {"step": None, "target_uid": None}

def handle_admin(msg, admin_uid):
    try:
        _handle_admin_inner(msg, admin_uid)
    except Exception:
        log.error("handle_admin crashed:\n" + traceback.format_exc())
        adm_ctx_reset(admin_uid)
        try:
            send(admin_uid, "⚠️ Внутренняя ошибка. Контекст сброшен.", kb=adm_kb(admin_uid))
        except Exception:
            pass

def _handle_admin_inner(msg, admin_uid):
    text = msg.text.strip() if msg.text else ""
    ctx  = get_adm(admin_uid)
    step = ctx.get("step")
    tid  = ctx.get("target_uid")
    IS_ROOT = (admin_uid == ADMIN_ID)

    # ── Ждём UID жертвы ──────────────────────────────────────
    if step == "wait_uid":
        if text.lstrip("-").isdigit():
            tid = int(text); ctx["target_uid"] = tid; ctx["step"] = "wait_action"
            tu    = users.get(tid, {})
            tname = tu.get("name") or "?"
            tuname = ("@" + tu["username"]) if tu.get("username") else f"ID:{tid}"
            send(admin_uid,
                 f"🎯 Цель: {tuname}  |  {tname}  |  Ст:{tu.get('stage',0)}  |  "
                 f"{'👁' if tu.get('horror_active') else '😴'}\n\nВыбери действие:",
                 kb=KB_VIC())
        else:
            adm_ctx_reset(admin_uid); send(admin_uid, "⛔ Нужен числовой ID.", kb=adm_kb(admin_uid))
        return

    if step == "wait_new_admin":
        if text.lstrip("-").isdigit():
            new_aid = int(text)
            if new_aid == ADMIN_ID:
                send(admin_uid, "Это уже главный admin.", kb=KB_ADM()); adm_ctx_reset(admin_uid); return
            admins.add(new_aid)
            send(admin_uid, f"✅ {new_aid} назначен admin'ом.", kb=KB_ADM())
            _safe_call(bot.send_message, new_aid, "⚡ Тебя назначили admin'ом horror-бота.\nИспользуй /admingo для входа.")
        else:
            send(admin_uid, "❌ Нужен числовой ID.", kb=KB_ADM())
        adm_ctx_reset(admin_uid); return

    if step == "wait_del_admin":
        if text.lstrip("-").isdigit():
            del_aid = int(text)
            if del_aid == ADMIN_ID:
                send(admin_uid, "Нельзя снять главного admin'а.", kb=KB_ADM()); adm_ctx_reset(admin_uid); return
            admins.discard(del_aid)
            send(admin_uid, f"✅ {del_aid} снят с admin'а.", kb=KB_ADM())
        else:
            send(admin_uid, "❌ Нужен числовой ID.", kb=KB_ADM())
        adm_ctx_reset(admin_uid); return

    if step == "wait_text":
        if text and tid:
            send(tid, text); send(admin_uid, f"✅ → {tid}", kb=adm_kb(admin_uid))
        else:
            send(admin_uid, "Ошибка.", kb=adm_kb(admin_uid))
        adm_ctx_reset(admin_uid); return

    if step == "wait_photo":
        if text and tid:
            try:
                bot.send_photo(tid, text)
                send(admin_uid, f"✅ Фото → {tid}", kb=adm_kb(admin_uid))
            except Exception:
                send(admin_uid, "❌ Не вышло. Отправь файлом.", kb=adm_kb(admin_uid))
        adm_ctx_reset(admin_uid); return

    # ИСПРАВЛЕНО: добавлен обработчик wait_video
    if step == "wait_video":
        send(admin_uid, "Отправь видеофайл напрямую (не ссылкой).", kb=adm_kb(admin_uid))
        adm_ctx_reset(admin_uid); return

    if step == "wait_broadcast":
        if text:
            cnt = 0
            for vid in list(users.keys()):
                if not is_admin(vid):
                    send(vid, text); cnt += 1; time.sleep(0.05)
            send(admin_uid, f"✅ Рассылка → {cnt} польз.", kb=adm_kb(admin_uid))
        adm_ctx_reset(admin_uid); return

    # ── Действия над жертвой ─────────────────────────────────
    if step == "wait_action":
        if text == "🔙 Назад":
            adm_ctx_reset(admin_uid); send(admin_uid, "↩️ Меню.", kb=adm_kb(admin_uid)); return

        # Защита: если tid вдруг пропал — возврат в меню
        if not tid:
            adm_ctx_reset(admin_uid)
            send(admin_uid, "⚠️ Жертва не выбрана. Выбери заново: ⚙️ Выбрать жертву", kb=adm_kb(admin_uid)); return

        if text == "📝 Текст":
            ctx["step"]="wait_text";  send(admin_uid, f"Введи текст для {tid}:", kb=ReplyKeyboardRemove()); return
        if text == "🖼 Фото":
            ctx["step"]="wait_photo"; send(admin_uid, "Отправь URL фото или файл:", kb=ReplyKeyboardRemove()); return
        if text == "🎬 Гифка":
            send_screamer(tid); send(admin_uid, f"✅ → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📹 Видео":
            ctx["step"]="wait_video"; send(admin_uid, "Отправь видео файлом:", kb=ReplyKeyboardRemove()); return
        if text == "⚡ Скример":
            adm_screamer(tid); send(admin_uid, f"✅ Скример → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "☠️ Макс-ужас":
            adm_max(tid); send(admin_uid, f"✅ Макс-ужас → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🌊 Волна паники":
            adm_panic(tid); send(admin_uid, f"✅ Паника → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🕯 Ритуал":
            adm_ritual(tid); send(admin_uid, f"✅ Ритуал → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "💬 Диалог-ловушка":
            adm_trap(tid); send(admin_uid, f"✅ Диалог → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "😴 Спящий режим":
            adm_sleep(tid); send(admin_uid, f"✅ Сон → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "⬆️ Стадия +1":
            if tid in users:
                cur=users[tid]["stage"]; users[tid]["stage"]=min(cur+1,5)
                send(admin_uid, f"⬆️ {tid}: {cur}→{users[tid]['stage']}", kb=adm_kb(admin_uid))
            adm_ctx_reset(admin_uid); return
        if text == "⬇️ Стадия -1":
            if tid in users:
                cur=users[tid]["stage"]; users[tid]["stage"]=max(cur-1,0)
                send(admin_uid, f"⬇️ {tid}: {cur}→{users[tid]['stage']}", kb=adm_kb(admin_uid))
            adm_ctx_reset(admin_uid); return
        if text == "🔇 Заглушить":
            if tid in users: users[tid]["muted"]=True
            send(admin_uid, f"🔇 {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🔊 Включить":
            if tid in users: users[tid]["muted"]=False
            send(admin_uid, f"🔊 {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "✏️ Редактировать данные":
            ctx["step"] = "wait_edit_field"
            send(admin_uid,
                 "✏️ РЕДАКТИРОВАНИЕ ДАННЫХ\n\n"
                 "Введи в формате: поле=значение\n\n"
                 "Доступные поля:\n" +
                 "\n".join(f"  {k}" for k in EDITABLE_FIELDS.keys()) +
                 "\n\nПример: имя=Андрей\nПример: стадия=3\nПример: страх=темнота",
                 kb=ReplyKeyboardRemove()); return
        if text == "❄️ Заморозить стадию":
            ctx["step"] = "wait_freeze_mins"
            send(admin_uid,
                 f"❄️ На сколько МИНУТ заморозить стадию {tid}? (1-120):",
                 kb=ReplyKeyboardRemove()); return
        if text == "🔓 Разморозить стадию":
            unfreeze_stage(tid)
            send(admin_uid, f"🔓 Стадия разморожена для {tid}", kb=adm_kb(admin_uid))
            adm_ctx_reset(admin_uid); return

        if text == "📋 Инфо":
            send(admin_uid, adm_info(tid), kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🔄 Сбросить":
            adm_reset(tid); send(admin_uid, f"✅ Сброшен {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📱 Взлом телефона":
            tu=users.get(tid,{}); send(tid, make_sys_notify(tu))
            send(admin_uid, f"✅ Взлом → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🎙 Голос от него":
            tu=users.get(tid,{}); vt=VOICE_TEXTS_PERSONAL if tu.get("name") else VOICE_TEXTS
            send_voice_msg(tid, P(random.choice(vt), tu))
            send(admin_uid, f"✅ Голос → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📞 Фейк-звонок":
            fake_call_sequence(tid); send(admin_uid, f"✅ Фейк-звонок → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📲 Реальный звонок":
            real_call(tid); send(admin_uid, f"✅ Реальный звонок → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "💀 Таймер смерти":
            death_timer(tid, seconds=random.choice([20,30,45,60]))
            send(admin_uid, f"✅ Таймер → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📨 Вернуть сообщения":
            echo_back_history(tid); send(admin_uid, f"✅ История → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📷 Фейк-галерея":
            tu=users.get(tid,{}); send(tid, make_gallery_msg(tu))
            send(admin_uid, f"✅ Галерея → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🚫 Фейк-бан":
            fake_ban_sequence(tid); send(admin_uid, f"✅ Бан → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "👻 Фейк-уход":
            fake_leave_sequence(tid); send(admin_uid, f"✅ Уход → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "👁 Шпионаж ВКЛ":
            if tid in users: users[tid]["spy"]=True
            send(admin_uid, f"👁 Шпионаж включён для {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🙈 Шпионаж ВЫКЛ":
            if tid in users: users[tid]["spy"]=False
            send(admin_uid, f"🙈 Шпионаж выключен для {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📜 Вся история":
            send_full_history(admin_uid, tid)
            send(admin_uid, "📜 Готово.", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📍 Геолокация":
            fake_geolocation(tid); send(admin_uid, f"✅ Геолокация → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📲 Скан телефона":
            fake_phone_scan(tid); send(admin_uid, f"✅ Скан телефона → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "👥 Призраки":
            fake_ghost_users(tid); send(admin_uid, f"✅ Призраки → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📂 Скан файлов":
            fake_file_scan(tid); send(admin_uid, f"✅ Файлы → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "💬 Умное эхо":
            smart_echo_history(tid); send(admin_uid, f"✅ Умное эхо → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📡 Потеря сигнала":
            signal_loss(tid); send(admin_uid, f"✅ Сигнал → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🕒 Режим 3AM":
            three_am_mode(tid); send(admin_uid, f"✅ 3AM → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🔐 TG Security":
            fake_telegram_security(tid); send(admin_uid, f"✅ TG Security → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return

        # ── v11 новые функции ──────────────────────────────
        if text == "🕯 Экзорцист":
            exorcist_mode(tid); send(admin_uid, f"✅ Экзорцист → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📺 Трансляция":
            fake_live_stream(tid); send(admin_uid, f"✅ Трансляция → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "📡 GPS трекинг":
            fake_gps_tracking(tid); send(admin_uid, f"✅ GPS → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🌐 Взлом Wi-Fi":
            fake_wifi_hack(tid); send(admin_uid, f"✅ Wi-Fi → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🔔 Уведомления":
            fake_notifications(tid); send(admin_uid, f"✅ Уведомления → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🗳 Опрос":
            send_horror_poll(tid); send(admin_uid, f"✅ Опрос → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "⚡ Глитч-атака":
            glitch_attack(tid); send(admin_uid, f"✅ Глитч → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🪞 Зеркало":
            mirror_event(tid); send(admin_uid, f"✅ Зеркало → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🫀 Сердцебиение":
            heartbeat_event(tid); send(admin_uid, f"✅ Сердцебиение → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🗑 Удалённое сообщение":
            fake_deleted_message(tid); send(admin_uid, f"✅ Удалённое сообщение → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🤝 Совместный квест":
            # Выбираем случайную вторую жертву
            others = [v for v in users if not is_admin(v) and v != tid]
            if others:
                p2 = random.choice(others)
                start_squad_quest(tid, p2)
                send(admin_uid, f"✅ Квест: {tid} + {p2}", kb=adm_kb(admin_uid))
            else:
                send(admin_uid, "❌ Нет второй жертвы.", kb=adm_kb(admin_uid))
            adm_ctx_reset(admin_uid); return
        if text == "🔁 Авто-режим ВКЛ":
            _auto_mode.add(tid)
            send(admin_uid, f"🔁 Авто-режим ВКЛ → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "⏹ Авто-режим ВЫКЛ":
            _auto_mode.discard(tid)
            send(admin_uid, f"⏹ Авто-режим ВЫКЛ → {tid}", kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🎬 Сценарий":
            ctx["step"] = "wait_scenario"
            names = "\n".join(f"• {n}" for n in _scenarios)
            send(admin_uid, f"Введи имя сценария:\n\n{names}", kb=ReplyKeyboardRemove()); return
        if text == "⏰ Таймер-атака":
            ctx["step"] = "wait_timer"
            send(admin_uid, "Через сколько МИНУТ запустить скример? (1-60):", kb=ReplyKeyboardRemove()); return
        if text == "📊 Граф стадий":
            send(admin_uid, get_stage_graph(tid), kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "🏆 Лидеры страха":
            send(admin_uid, get_leaderboard(), kb=adm_kb(admin_uid)); adm_ctx_reset(admin_uid); return
        if text == "💾 Создать сценарий":
            ctx["step"] = "wait_scenario_name"
            send(admin_uid,
                 "Введи название нового сценария\n(например: Мой ужас):",
                 kb=ReplyKeyboardRemove()); return
        if text == "🗑 Удалить сценарий":
            ctx["step"] = "wait_del_scenario"
            names = "\n".join(f"• {n}" for n in _scenarios)
            send(admin_uid,
                 f"Введи имя сценария для удаления:\n\n{names}",
                 kb=ReplyKeyboardRemove()); return

        send(admin_uid, "Выбери действие:", kb=KB_VIC()); return

    # ── v12: Редактирование поля ─────────────────────────────
    if step == "wait_edit_field":
        if "=" in text and tid:
            parts = text.split("=", 1)
            field_label = parts[0].strip().lower()
            value = parts[1].strip()
            field_key = EDITABLE_FIELDS.get(field_label)
            if field_key and tid in users:
                # Специальные преобразования
                if field_key == "stage":
                    try:
                        users[tid]["stage"] = max(0, min(5, int(value)))
                        send(admin_uid,
                             f"✅ Стадия [{tid}] → {users[tid]['stage']}",
                             kb=adm_kb(admin_uid))
                    except ValueError:
                        send(admin_uid, "❌ Стадия должна быть числом 0-5.", kb=adm_kb(admin_uid))
                elif field_key == "score":
                    try:
                        users[tid]["score"] = int(value)
                        send(admin_uid,
                             f"✅ Очки [{tid}] → {users[tid]['score']}",
                             kb=adm_kb(admin_uid))
                    except ValueError:
                        send(admin_uid, "❌ Очки должны быть числом.", kb=adm_kb(admin_uid))
                else:
                    users[tid][field_key] = value[:80]
                    send(admin_uid,
                         f"✅ [{tid}] {field_label} = «{value[:80]}»",
                         kb=adm_kb(admin_uid))
            else:
                send(admin_uid,
                     f"❌ Поле «{field_label}» не найдено.\nДоступные: {', '.join(EDITABLE_FIELDS.keys())}",
                     kb=adm_kb(admin_uid))
        else:
            send(admin_uid, "❌ Формат: поле=значение  (например: имя=Андрей)", kb=adm_kb(admin_uid))
        adm_ctx_reset(admin_uid); return

    # ── v12: Заморозка стадии ─────────────────────────────────
    if step == "wait_freeze_mins":
        try:
            mins = int(text.strip())
            if 1 <= mins <= 120 and tid:
                freeze_stage(tid, mins)
                send(admin_uid, f"❄️ Стадия [{tid}] заморожена на {mins} мин.", kb=adm_kb(admin_uid))
            else:
                send(admin_uid, "❌ Введи число от 1 до 120.", kb=adm_kb(admin_uid))
        except ValueError:
            send(admin_uid, "❌ Нужно число.", kb=adm_kb(admin_uid))
        adm_ctx_reset(admin_uid); return

    # ── Создание сценария — шаг 1: имя ──────────────────────
    if step == "wait_scenario_name":
        if text and len(text) < 50:
            ctx["new_scenario_name"] = text
            ctx["new_scenario_steps"] = []
            ctx["step"] = "wait_scenario_steps"
            send(admin_uid,
                 f"Сценарий «{text}» создаётся.\n\n"
                 "Вводи шаги по одному в формате:\n"
                 "  текст|секунды\n"
                 "Пример: я наблюдаю|4\n\n"
                 "Когда закончишь — введи: готово",
                 kb=ReplyKeyboardRemove())
        else:
            send(admin_uid, "❌ Слишком длинное имя.", kb=adm_kb(admin_uid))
            adm_ctx_reset(admin_uid)
        return

    # ── Создание сценария — шаг 2: шаги ──────────────────────
    if step == "wait_scenario_steps":
        if text.lower().strip() == "готово":
            steps = ctx.get("new_scenario_steps", [])
            name  = ctx.get("new_scenario_name", "Без имени")
            if steps:
                _scenarios[name] = steps
                send(admin_uid,
                     f"✅ Сценарий «{name}» сохранён ({len(steps)} шагов).",
                     kb=adm_kb(admin_uid))
            else:
                send(admin_uid, "❌ Нет шагов — сценарий не сохранён.", kb=adm_kb(admin_uid))
            adm_ctx_reset(admin_uid)
        elif "|" in text:
            parts = text.split("|", 1)
            try:
                delay = float(parts[1].strip())
                ctx["new_scenario_steps"].append((parts[0].strip(), delay))
                count = len(ctx["new_scenario_steps"])
                send(admin_uid, f"✅ Шаг {count} добавлен. Продолжай или введи: готово")
            except ValueError:
                send(admin_uid, "❌ Формат: текст|секунды  (напр: привет|3)")
        else:
            send(admin_uid, "Формат: текст|секунды  или «готово» для завершения.")
        return

    # ── Удаление сценария ─────────────────────────────────────
    if step == "wait_del_scenario":
        if text in _scenarios:
            del _scenarios[text]
            send(admin_uid, f"✅ Сценарий «{text}» удалён.", kb=adm_kb(admin_uid))
        else:
            send(admin_uid, f"❌ Сценарий «{text}» не найден.", kb=adm_kb(admin_uid))
        adm_ctx_reset(admin_uid); return

    # ── Ввод сценария ─────────────────────────────────────────
    if step == "wait_scenario":
        if tid and text in _scenarios:
            run_scenario(tid, text)
            send(admin_uid, f"✅ Сценарий «{text}» → {tid}", kb=adm_kb(admin_uid))
        else:
            names = ", ".join(_scenarios.keys())
            send(admin_uid, f"❌ Сценарий не найден.\nДоступные: {names}", kb=adm_kb(admin_uid))
        adm_ctx_reset(admin_uid); return

    # ── Ввод таймер-атаки ─────────────────────────────────────
    if step == "wait_timer":
        try:
            mins = int(text.strip())
            if 1 <= mins <= 60 and tid:
                schedule_attack(tid, send_screamer, mins * 60)
                send(admin_uid, f"⏰ Атака через {mins} мин → {tid}", kb=adm_kb(admin_uid))
            else:
                send(admin_uid, "❌ Введи число от 1 до 60.", kb=adm_kb(admin_uid))
        except ValueError:
            send(admin_uid, "❌ Нужно число.", kb=adm_kb(admin_uid))
        adm_ctx_reset(admin_uid); return

    # ── Глобальные кнопки ────────────────────────────────────
    if text == "👥 Жертвы":
        victims = [v for v in users if not is_admin(v)]
        if not victims: send(admin_uid, "Жертв нет.", kb=adm_kb(admin_uid)); return
        lines = [
            f"🆔{vid} @{users[vid].get('username','?')} | "
            f"{users[vid].get('name','?')} | Ст:{users[vid].get('stage',0)} | "
            f"{'👁' if users[vid].get('horror_active') else '😴'}"
            f"{'🔇' if users[vid].get('muted') else ''}"
            f"{'📡' if users[vid].get('spy',True) else ''} | F:{FC(users[vid])}"
            for vid in victims
        ]
        send(admin_uid, "👥 ЖЕРТВЫ:\n\n"+"\n".join(lines), kb=adm_kb(admin_uid)); return

    if text == "📋 Список ID":
        victims = [v for v in users if not is_admin(v)]
        if not victims: send(admin_uid, "Жертв нет.", kb=adm_kb(admin_uid)); return
        lines = [
            (f"{vid} — {users[vid].get('name','?')} @{users[vid].get('username','')}"
             if users[vid].get('username')
             else f"{vid} — {users[vid].get('name','?')}")
            for vid in victims
        ]
        send(admin_uid, "📋 ID жертв:\n\n"+"\n".join(lines), kb=adm_kb(admin_uid)); return

    if text == "🏆 Лидеры страха":
        send(admin_uid, get_leaderboard(), kb=adm_kb(admin_uid)); return

    if text == "🎬 Все сценарии":
        names = "\n".join(f"• {n}" for n in _scenarios)
        send(admin_uid, f"🎬 СЦЕНАРИИ:\n\n{names}\n\nВыбери жертву и нажми 🎬 Сценарий.", kb=adm_kb(admin_uid)); return

    if text == "🗓 Ежедн. задание всем":
        cnt = 0
        for vid in list(users.keys()):
            if not is_admin(vid) and users[vid].get("horror_active"):
                send_daily_quest(vid); cnt += 1; time.sleep(0.3)
        send(admin_uid, f"🗓 Задание отправлено → {cnt} жертв.", kb=adm_kb(admin_uid)); return

    if text == "🎲 Случай. событие":
        active = [v for v in users if not is_admin(v) and users[v].get("horror_active")]
        cnt = 0
        for vid in active:
            fn = random.choice([fake_live_stream, fake_gps_tracking, fake_notifications,
                                 fake_ghost_users, three_am_mode, signal_loss])
            fn(vid); cnt += 1; time.sleep(0.5)
        send(admin_uid, f"🎲 Случайное событие → {cnt} жертв.", kb=adm_kb(admin_uid)); return

    if text == "📊 Статистика":
        total  = len([v for v in users if not is_admin(v)])
        active = sum(1 for v,vu in users.items() if vu.get("horror_active") and not is_admin(v))
        muted  = sum(1 for v,vu in users.items() if vu.get("muted") and not is_admin(v))
        st = {}
        for v,vu in users.items():
            if is_admin(v): continue
            s=vu.get("stage",0); st[s]=st.get(s,0)+1
        send(admin_uid,
             f"📊 СТАТИСТИКА\n\nВсего: {total}  Хоррор: {active}  Заглушено: {muted}\n"+
             "  ".join(f"Ст{k}:{v}" for k,v in sorted(st.items())),
             kb=adm_kb(admin_uid)); return

    if text == "💀 Ужас всем":
        for vid in list(users.keys()):
            if not is_admin(vid): start_horror(vid)
        send(admin_uid, "💀 Ужас запущен для всех!", kb=adm_kb(admin_uid)); return

    if text == "💬 Чат 3 мин":
        start_chat_mode(admin_uid, minutes=3, anon=True); return
    if text == "💬 Чат 10 мин":
        start_chat_mode(admin_uid, minutes=10, anon=True); return
    if text == "🔕 Стоп чат":
        _chat_mode["active"] = False
        for vid in list(users.keys()):
            if not is_admin(vid) and not users[vid].get("stopped"):
                try: send(vid, "📡 Сигнал потерян. Тишина.\n\n...мы снова наедине. 👁")
                except Exception: pass
        send(admin_uid, "✅ Чат остановлен.", kb=adm_kb(admin_uid)); return
    if text == "👥 Чат деанон":
        start_chat_mode(admin_uid, minutes=5, anon=False); return

    if text == "🛑 Стоп всем":
        for vu in users.values(): vu["stopped"]=True
        send(admin_uid, "🛑 Все остановлены.", kb=adm_kb(admin_uid)); return

    if text == "▶️ Рестарт всем":
        for vid, vu in users.items():
            if is_admin(vid): continue
            vu["stopped"]=False
            if not vu.get("horror_active") and FC(vu)>=4: start_horror(vid)
        send(admin_uid, "▶️ Рестарт для всех.", kb=adm_kb(admin_uid)); return

    if text == "🔇 Тишина всем":
        for vid,vu in users.items():
            if not is_admin(vid): vu["muted"]=True
        send(admin_uid, "🔇 Заглушено для всех.", kb=adm_kb(admin_uid)); return

    if text == "🔊 Звук всем":
        for vid,vu in users.items():
            if not is_admin(vid): vu["muted"]=False
        send(admin_uid, "🔊 Хоррор включён для всех.", kb=adm_kb(admin_uid)); return

    if text == "📤 Рассылка всем":
        ctx["step"]="wait_broadcast"
        send(admin_uid, "Введи текст рассылки:", kb=ReplyKeyboardRemove()); return

    if text == "⚙️ Выбрать жертву":
        ctx["step"]="wait_uid"; ctx["target_uid"]=None
        send(admin_uid, "Введи числовой ID жертвы:", kb=ReplyKeyboardRemove()); return

    # ── Root-only ────────────────────────────────────────────
    if IS_ROOT:
        if text == "👑 Мои со-admin'ы":
            if not admins:
                send(admin_uid, "Со-admin'ов нет.", kb=KB_ADM()); return
            lines = [f"🔑 {aid} — @{users.get(aid,{}).get('username','?')}" for aid in admins]
            send(admin_uid, "👑 СО-ADMIN'Ы:\n\n"+"\n".join(lines), kb=KB_ADM()); return
        if text == "➕ Добавить admin'а":
            ctx["step"]="wait_new_admin"
            send(admin_uid, "Введи числовой ID нового admin'а:", kb=ReplyKeyboardRemove()); return
        if text == "➖ Убрать admin'а":
            ctx["step"]="wait_del_admin"
            send(admin_uid, "Введи числовой ID admin'а для снятия:", kb=ReplyKeyboardRemove()); return
        if text == "👥 Группы (управление)":
            if not _group_users:
                send(admin_uid, "Бот ещё не добавлен ни в одну группу.", kb=KB_ADM()); return
            lines = [f"🏘 {cid}: {len(v)} участников" for cid, v in _group_users.items()]
            # ИСПРАВЛЕНО: управление группами теперь полностью из ЛС через InlineKeyboard
            kb_groups = InlineKeyboardMarkup(row_width=2)
            for cid in _group_users.keys():
                cnt = len(_group_users[cid])
                kb_groups.add(
                    InlineKeyboardButton(f"💀 Хоррор в {cid}", callback_data=f"gadm_horror_{cid}"),
                    InlineKeyboardButton(f"🛑 Стоп игры {cid}", callback_data=f"gadm_stopgame_{cid}"),
                    InlineKeyboardButton(f"📊 Список {cid} ({cnt}чел)", callback_data=f"gadm_list_{cid}"),
                    InlineKeyboardButton(f"📤 Рассылка {cid}", callback_data=f"gadm_broadcast_{cid}"),
                )
            send(admin_uid,
                 "👥 ГРУППЫ:\n\n" + "\n".join(lines) +
                 "\n\nВыбери действие:",
                 kb=kb_groups); return

    if text == "🔙 Выйти из бога":
        adm_ctx_reset(admin_uid); send(admin_uid, "Вышел.", kb=KB(0)); return

    # Обработка рассылки в группу (gadm broadcast)
    if adm_state.get(admin_uid, {}).get("step") == "wait_grp_broadcast":
        cid = adm_state[admin_uid].get("grp_cid")
        if cid:
            send_group(cid, f"📢 Сообщение от администратора:\n\n{text}")
            send(admin_uid, f"✅ Рассылка отправлена в группу {cid}.", kb=adm_kb(admin_uid))
        adm_ctx_reset(admin_uid); return

    send(admin_uid, "⚡ БОГ-РЕЖИМ ⚡", kb=adm_kb(admin_uid))

# ══════════════════════════════════════════════════════════════
#  HANDLERS
# ══════════════════════════════════════════════════════════════
@bot.message_handler(commands=["start"])
def on_start(msg):
    uid = msg.from_user.id
    chat_id = msg.chat.id
    uname = msg.from_user.username

    # Поддержка групп
    if msg.chat.type in ("group", "supergroup"):
        with _lock:
            if chat_id not in _group_users:
                _group_users[chat_id] = set()
            _group_users[chat_id].add(uid)
        u = U(uid)
        if uname: u["username"] = uname
        # Inline кнопки для быстрого доступа (не требуют ЛС с ботом)
        k = InlineKeyboardMarkup(row_width=2)
        k.add(
            InlineKeyboardButton("🎮 Игры", callback_data=f"grp_games_{chat_id}"),
            InlineKeyboardButton("🏆 Рейтинг", callback_data=f"grp_rating_{chat_id}"),
            InlineKeyboardButton("🌍 Перевести", callback_data=f"grp_translate_{chat_id}"),
            InlineKeyboardButton("🌤 Погода", callback_data=f"grp_weather_{chat_id}"),
        )
        # ИСПРАВЛЕНО: отправляем постоянную ReplyKeyboard чтобы кнопки были всегда
        send_group(chat_id,
            f"👁 Horror Bot подключился к группе!\n\n"
            f"Участник: {msg.from_user.first_name}\n\n"
            f"🎮 Игры: 🍾 Бутылочка, 🪙 Монетка, 🔫 Рулетка, 🎭 Правда/Действие, ⚖️ Что лучше? и многое другое!\n"
            f"🤖 ИИ Кожаный Мешок доступен прямо в группе!\n\n"
            f"Кнопки внизу для быстрого доступа 👇",
            kb=group_reply_kb())
        # Дополнительно отправляем inline-меню
        _safe_call(bot.send_message, chat_id,
            "⬆️ Или нажми на кнопку:", reply_markup=k)
        return

    # Сначала останавливаем любые активные потоки (через флаг)
    with _lock:
        if uid in users:
            users[uid]["stopped"] = True
            users[uid]["muted"]   = True

    def _do_start(_uid=uid, _uname=uname):
        # Небольшая пауза в пуле потоков — даём потокам хоррора/стадий заметить флаг
        # (не блокируем receiving thread бота)
        time.sleep(1.5)

        # Полная очистка предыдущего профиля
        with _lock:
            if _uid in users:
                del users[_uid]

        games.pop(_uid, None)
        _stage_history.pop(_uid, None)
        _auto_mode.discard(_uid)
        _squad_mode.pop(_uid, None)
        _daily_done.pop(_uid, None)
        _stage_frozen.pop(_uid, None)
        # Удаляем активные опросы этого пользователя
        for pid in [k for k, v in list(_active_polls.items()) if v.get("uid") == _uid]:
            _active_polls.pop(pid, None)
        # Не очищаем весь _kb_cache — клавиатуры общие по стадии, не по юзеру

        # Создаём свежий профиль
        u = U(_uid)
        if _uname:
            u["username"] = _uname

        send(_uid,
             "Привет! 🌍 Я бот-переводчик.\n\n"
             "Напиши любой текст — переведу!\n"
             "По умолчанию: Русский → Английский\n\n"
             "Также умею:\n"
             "🌤 Показывать погоду\n"
             "🎮 Игры: RPG, истории, квесты\n"
             "🔮 Предсказания, 📖 Факты, 🧠 Викторина\n\n"
             "Нажми кнопку или напиши текст 😊",
             kb=KB(0))

    _pool.submit(_do_start)

@bot.message_handler(commands=["stop"])
def on_stop(msg):
    uid = msg.from_user.id
    u = U(uid)
    # Сначала останавливаем хоррор-потоки
    u["stopped"] = True
    u["muted"]   = True

    # Финальная жуткая последовательность
    for line in FINAL:
        try:
            bot.send_message(uid, P(line, u))
            time.sleep(random.uniform(0.3, 1.0))
        except Exception:
            pass
    try:
        bot.send_message(uid, "бот остановлен.", reply_markup=ReplyKeyboardRemove())
    except Exception:
        pass

    # Полное удаление всех данных пользователя (как будто никогда не заходил)
    # Небольшая задержка чтобы потоки успели завершиться
    def _full_wipe():
        time.sleep(3)
        with _lock:
            if uid in users:
                del users[uid]
        games.pop(uid, None)
        _stage_history.pop(uid, None)
        _auto_mode.discard(uid)
        _squad_mode.pop(uid, None)
        _daily_done.pop(uid, None)
    _pool.submit(_full_wipe)

@bot.message_handler(commands=["score"])
def on_score(msg):
    uid=msg.from_user.id; u=U(uid)
    send(uid, f"🏆 Твой счёт: {u.get('score',0)} очков", kb=KB(u["stage"]))

@bot.callback_query_handler(func=lambda call: True)
def on_callback(call):
    """Единый обработчик всех inline callback кнопок."""
    try:
        uid = call.from_user.id
        data = call.data
        uname = call.from_user.first_name or f"ID:{uid}"
        chat_id = call.message.chat.id
        u = U(uid)
        if not u.get("name"):
            u["name"] = uname
        if call.from_user.username:
            u["username"] = call.from_user.username

        # ── Мафия в ЛС: ночное действие (inline) ────────────────
        if data.startswith("mdm_"):  # mdm_lobbyid_playeruid_targetuid
            parts = data.split("_")
            if len(parts) < 4:
                bot.answer_callback_query(call.id, "Ошибка."); return
            lobby_id = int(parts[1]); player_uid = int(parts[2]); target_uid = int(parts[3])
            if uid != player_uid:
                bot.answer_callback_query(call.id, "Это не твой ход."); return
            g = _mafia_lobby.get(lobby_id)
            if not g or g.get("phase") != "night" or g.get("state") != "playing":
                bot.answer_callback_query(call.id, "Сейчас не ночь."); return
            if player_uid in g.get("night_actions", {}):
                bot.answer_callback_query(call.id, "Ты уже сделал ход."); return
            if target_uid not in g.get("alive", []):
                bot.answer_callback_query(call.id, "Этот игрок выбыл."); return
            role = g["roles"].get(player_uid)
            target_name = g["player_names"].get(target_uid, "?")
            action_word = {"мафия":"убить","шериф":"проверить","доктор":"вылечить"}.get(role,"?")
            g["night_actions"][player_uid] = target_uid
            bot.answer_callback_query(call.id, f"✅ Действие принято")
            try: bot.send_message(player_uid, f"✅ {action_word} {target_name} — принято!")
            except Exception: pass
            _check_mafia_night_actions(lobby_id)
            return

        # ── Мафия в ЛС: дневное голосование (inline) ─────────────
        if data.startswith("mdmv_"):  # mdmv_lobbyid_targetuid
            parts = data.split("_")
            if len(parts) < 3:
                bot.answer_callback_query(call.id, "Ошибка."); return
            lobby_id = int(parts[1]); target_uid = int(parts[2])
            g = _mafia_lobby.get(lobby_id)
            if not g or g.get("phase") != "day" or g.get("state") != "playing":
                bot.answer_callback_query(call.id, "Сейчас не день или игра завершена."); return
            if uid not in g.get("alive", []):
                bot.answer_callback_query(call.id, "Ты не в игре."); return
            if uid in g.get("votes", {}):
                bot.answer_callback_query(call.id, "Ты уже проголосовал!"); return
            if uid == target_uid:
                bot.answer_callback_query(call.id, "Нельзя голосовать за себя!"); return
            voted_name = g["player_names"].get(target_uid, "?")
            g["votes"][uid] = target_uid
            bot.answer_callback_query(call.id, f"✅ Голос за {voted_name} принят (анонимно)")
            _check_mafia_day_votes(lobby_id)
            return

        if data.startswith("mdmvskip_"):  # mdmvskip_lobbyid
            lobby_id = int(data[9:])
            g = _mafia_lobby.get(lobby_id)
            if not g or g.get("phase") != "day":
                bot.answer_callback_query(call.id, "Сейчас не день."); return
            if uid not in g.get("alive", []):
                bot.answer_callback_query(call.id, "Ты не в игре."); return
            if uid in g.get("votes", {}):
                bot.answer_callback_query(call.id, "Ты уже проголосовал!"); return
            g["votes"][uid] = None
            bot.answer_callback_query(call.id, "⏭ Голос пропущен")
            _check_mafia_day_votes(lobby_id)
            return

        # ── Лобби мафии в группе: новые короткие коды ──────────
        if data.startswith("mj_"):   # mafia join
            cid = int(data[3:])
            g = _group_mafia.get(cid)
            if not g or g.get("state") != "lobby":
                bot.answer_callback_query(call.id, "Игра уже началась или завершена."); return
            if uid in g["players"]:
                bot.answer_callback_query(call.id, "Ты уже в игре!"); return
            g["players"].append(uid)
            g["player_names"][uid] = uname
            bot.answer_callback_query(call.id, f"✅ Вступил в игру!")
            send_group(cid, f"✅ {uname} присоединился к мафии! Игроков: {len(g['players'])}")
            return

        if data.startswith("ms_"):   # mafia start
            cid = int(data[3:])
            g = _group_mafia.get(cid)
            if not g or g.get("state") != "lobby":
                bot.answer_callback_query(call.id, "Игра уже началась."); return
            bot.answer_callback_query(call.id, "Начинаем!")
            _mafia_start_game(cid)
            return

        if data.startswith("mc_"):   # mafia cancel
            cid = int(data[3:])
            if uid == ADMIN_ID or (cid in _group_mafia and _group_mafia[cid].get("players") and
                                    _group_mafia[cid]["players"][0] == uid):
                _group_mafia.pop(cid, None)
                bot.answer_callback_query(call.id, "Лобби отменено.")
                send_group(cid, "❌ Лобби мафии отменено.")
            else:
                bot.answer_callback_query(call.id, "Только организатор может отменить.")
            return

        # ── Голосование в мафии (день) ──────────────────────────
        if data.startswith("mv_"):   # mafia vote: mv_chatid_targetuid
            parts = data.split("_")
            cid = int(parts[1]); target_uid = int(parts[2])
            g = _group_mafia.get(cid)
            if not g or g.get("phase") != "day" or g.get("state") != "playing":
                bot.answer_callback_query(call.id, "Сейчас не время голосования."); return
            if uid not in g["alive"]:
                bot.answer_callback_query(call.id, "Ты не в игре."); return
            if uid == target_uid:
                bot.answer_callback_query(call.id, "Нельзя голосовать за себя!"); return
            voted_today = g.setdefault("voted_today", set())
            if uid in voted_today:
                bot.answer_callback_query(call.id, "Ты уже проголосовал сегодня!"); return
            voted_name = g["player_names"].get(target_uid, "?")
            g["votes"][uid] = target_uid
            voted_today.add(uid)
            # ИСПРАВЛЕНО: только приватное уведомление нажавшему — другие не видят за кого ты голосовал
            bot.answer_callback_query(call.id, f"✅ Твой голос за {voted_name} засчитан! (анонимно)")
            # Публично показываем только КОЛИЧЕСТВО проголосовавших, без имён
            total_alive = len(g["alive"])
            voted_count = len(g["votes"])
            send_group(cid, f"🗳 Проголосовало: {voted_count}/{total_alive}\n(Голоса тайные — результат после подсчёта)")
            # ИСПРАВЛЕНО: автоматически считаем голоса когда все проголосовали
            if voted_count >= total_alive:
                _group_mafia_count_votes(cid)
            return

        if data.startswith("mcount_"):  # mafia count votes
            cid = int(data[8:])
            g = _group_mafia.get(cid)
            if not g or g.get("phase") != "day":
                bot.answer_callback_query(call.id, "Нет активного голосования."); return
            if uid not in g["alive"] and not is_admin(uid):
                bot.answer_callback_query(call.id, "Ты не в игре."); return
            # ИСПРАВЛЕНО: подсчёт голосов только если все проголосовали ИЛИ это admin
            voted_count = len(g.get("votes", {}))
            alive_count = len(g["alive"])
            if voted_count < alive_count and not is_admin(uid):
                bot.answer_callback_query(call.id, f"Ещё не все проголосовали ({voted_count}/{alive_count})"); return
            bot.answer_callback_query(call.id, "Считаем голоса...")
            _group_mafia_count_votes(cid)
            return

        # ── Ночные действия мафии ────────────────────────────────
        if data.startswith("mnight_"):  # mnight_chatid_playeruid_targetuid
            parts = data.split("_")
            if len(parts) < 4:
                bot.answer_callback_query(call.id, "Ошибка данных."); return
            cid = int(parts[1]); player_uid = int(parts[2]); target_uid = int(parts[3])
            # ИСПРАВЛЕНО: только сам игрок может нажать свою кнопку
            if uid != player_uid:
                bot.answer_callback_query(call.id, "Это не твой ход."); return
            g = _group_mafia.get(cid)
            if not g or g.get("phase") != "night":
                bot.answer_callback_query(call.id, "Сейчас не ночь."); return
            if player_uid not in g.get("alive", []):
                bot.answer_callback_query(call.id, "Ты выбыл из игры."); return
            if player_uid in g.get("night_actions", {}):
                bot.answer_callback_query(call.id, "Ты уже сделал ход этой ночью."); return
            if target_uid not in g.get("alive", []):
                bot.answer_callback_query(call.id, "Этот игрок уже выбыл."); return
            role = g["roles"].get(player_uid)
            target_name = g["player_names"].get(target_uid, "?")
            action_word = {"мафия": "убить", "шериф": "проверить", "доктор": "вылечить"}.get(role, "?")
            g["night_actions"][player_uid] = target_uid
            # ИСПРАВЛЕНО: только приватное подтверждение — никто в группе не видит ночные действия
            bot.answer_callback_query(call.id, f"✅ Принято!")
            try:
                bot.send_message(player_uid, f"✅ Ночное действие принято: {action_word} {target_name}\n(в тайне от остальных)")
            except Exception:
                pass
            _group_mafia_check_night(cid)
            return

        # ── Групповые игры — старые коды (mafia_join_ mafia_start_) ──
        if data.startswith("mafia_join_"):
            cid = int(data.split("_")[2])
            g = _group_mafia.get(cid)
            if not g or g.get("state") != "lobby":
                bot.answer_callback_query(call.id, "Игра уже началась или завершена."); return
            if uid in g["players"]:
                bot.answer_callback_query(call.id, "Ты уже в игре!"); return
            g["players"].append(uid)
            g["player_names"][uid] = uname
            bot.answer_callback_query(call.id, f"✅ Вступил!")
            send_group(cid, f"✅ {uname} присоединился! Игроков: {len(g['players'])}")
            return

        if data.startswith("mafia_start_"):
            cid = int(data.split("_")[2])
            g = _group_mafia.get(cid)
            if not g or g.get("state") != "lobby":
                bot.answer_callback_query(call.id, "Игра уже началась."); return
            bot.answer_callback_query(call.id, "Начинаем!")
            _mafia_start_game(cid)
            return

        # ── Меню игр группы ─────────────────────────────────────
        if data.startswith("gg_"):
            parts = data.split("_")
            action = parts[1]; cid = int(parts[2])
            bot.answer_callback_query(call.id)
            if action == "number":    start_group_game_number(cid)
            elif action == "hangman": start_group_game_hangman(cid)
            elif action == "trivia":  start_group_game_trivia(cid)
            elif action == "rpg":
                _group_games[cid] = {"game": "rpg_group", "scene": "start"}
                scene = RPG_GROUP_SCENES["start"]
                kb_rpg = InlineKeyboardMarkup(row_width=1)
                for label, nk in scene.get("choices", []):
                    kb_rpg.add(InlineKeyboardButton(label, callback_data=f"rpg_{cid}_{nk}"))
                send_group(cid, scene["text"], kb=kb_rpg)
            elif action == "mafia":   start_group_mafia(cid)
            elif action == "card":    start_group_card_story(cid)
            elif action == "bottle":  start_group_game_bottle(cid, uid)
            elif action == "coin":    group_coin_flip(cid, uid)
            elif action == "dice":    group_dice_roll(cid, uid, sides=6)
            elif action == "dice20":  group_dice_roll(cid, uid, sides=20)
            elif action == "roulette": start_russian_roulette(cid)
            elif action == "tod":     start_truth_or_dare(cid, uid)
            elif action == "wr":      start_would_rather(cid)
            elif action == "hottake": start_hot_take(cid)
            elif action == "stop":
                if cid in _group_games: del _group_games[cid]; send_group(cid, "Игра остановлена.", kb=group_reply_kb())
                if cid in _group_mafia: _mafia_end(cid, "мирные"); send_group(cid, "Мафия прервана.")
            return

        # ── RPG в группе (inline) ────────────────────────────────
        if data.startswith("rpg_"):
            parts = data.split("_", 2)
            cid = int(parts[1]); scene_key = parts[2]
            g = _group_games.get(cid)
            if not g or g.get("game") != "rpg_group":
                bot.answer_callback_query(call.id, "Игра завершена."); return
            bot.answer_callback_query(call.id)
            scene = RPG_GROUP_SCENES.get(scene_key)
            if scene:
                g["scene"] = scene_key
                if scene.get("choices"):
                    kb_rpg = InlineKeyboardMarkup(row_width=1)
                    for label, nk in scene["choices"]:
                        kb_rpg.add(InlineKeyboardButton(label, callback_data=f"rpg_{cid}_{nk}"))
                    send_group(cid, f"👤 {uname} выбирает...\n\n{scene['text']}", kb=kb_rpg)
                else:
                    send_group(cid, f"👤 {uname} выбирает...\n\n{scene['text']}")
                if scene.get("end"):
                    del _group_games[cid]
            return

        # ── Викторина в группе (inline) ─────────────────────────
        if data.startswith("trivia_"):
            parts = data.split("_", 2)
            cid = int(parts[1]); answer = parts[2]
            g = _group_games.get(cid)
            if not g or g.get("game") != "trivia":
                bot.answer_callback_query(call.id, "Викторина уже завершена."); return
            if uid in g.get("answered", set()):
                bot.answer_callback_query(call.id, "Ты уже ответил!"); return
            if answer.lower() == g["answer"]:
                g.setdefault("answered", set()).add(uid)
                del _group_games[cid]
                bot.answer_callback_query(call.id, "🎉 Правильно!")
                send_group(cid, f"✅ {uname} ответил(а) правильно! +10 очков!")
                u = U(uid); u["score"] = u.get("score", 0) + 10
            else:
                g.setdefault("answered", set()).add(uid)
                bot.answer_callback_query(call.id, "❌ Неверно!")
            return

        # ── Выбор языка в группе ────────────────────────────────
        if data.startswith("grplang_"):
            parts = data.split("_", 2)
            cid = int(parts[1]); lang_code = parts[2]
            bot.answer_callback_query(call.id)
            lang_name = LANG_NAMES.get(lang_code, lang_code)
            # Сохраняем язык пользователю который нажал
            u["lang_pair"] = lang_code
            send_group(cid, f"🔤 {uname} выбрал(а) язык: {lang_name}\nТеперь напиши: перевести [текст]")
            return

        # ── Главное меню группы ──────────────────────────────────
        if data.startswith("grp_"):
            parts = data.split("_")
            action = parts[1]; cid = int(parts[2])
            bot.answer_callback_query(call.id)
            if action == "games":
                send_group(cid, "🎮 Выбери игру:", kb=group_game_kb(cid))
            elif action == "rating":
                send_group(cid, get_leaderboard())
            elif action == "translate":
                send_group(cid, "✍️ Напиши: перевести [текст]")
            elif action == "weather":
                send_group(cid, "Напиши: погода [город]")
            return

        # ── Русская рулетка ──────────────────────────────────────
        if data.startswith("rr_shoot_"):
            cid = int(data[9:])
            bot.answer_callback_query(call.id)
            _pool.submit(rr_shoot, cid, uid)
            return

        if data.startswith("rr_ai_"):
            cid = int(data[6:])
            bot.answer_callback_query(call.id, "🤖 ИИ стреляет...")
            _pool.submit(rr_shoot, cid, AI_PLAYER_ID)
            return

        if data.startswith("rr_stop_"):
            cid = int(data[8:])
            bot.answer_callback_query(call.id)
            _rr_games.pop(cid, None)
            send_group(cid, "🔫 Русская рулетка остановлена.", kb=group_reply_kb())
            return

        # ── Правда или Действие ──────────────────────────────────
        if data.startswith("tod_truth_"):
            parts = data.split("_"); cid = int(parts[2]); target_uid = int(parts[3])
            bot.answer_callback_query(call.id)
            _pool.submit(execute_truth, cid, target_uid)
            return

        if data.startswith("tod_dare_"):
            parts = data.split("_"); cid = int(parts[2]); target_uid = int(parts[3])
            bot.answer_callback_query(call.id)
            _pool.submit(execute_dare, cid, target_uid)
            return

        if data.startswith("tod_ai_"):
            parts = data.split("_"); cid = int(parts[2]); target_uid = int(parts[3])
            bot.answer_callback_query(call.id, "🤖 КМ решает...")
            choice = random.choice(["truth", "dare"])
            if choice == "truth":
                _pool.submit(execute_truth, cid, target_uid)
            else:
                _pool.submit(execute_dare, cid, target_uid)
            return

        # ── Что лучше? ───────────────────────────────────────────
        if data.startswith("wr_a_"):
            cid = int(data[5:])
            bot.answer_callback_query(call.id, "✅ Голос принят!")
            wr_vote(cid, uid, "a")
            return

        if data.startswith("wr_b_"):
            cid = int(data[5:])
            bot.answer_callback_query(call.id, "✅ Голос принят!")
            wr_vote(cid, uid, "b")
            return

        if data.startswith("wr_result_"):
            cid = int(data[10:])
            bot.answer_callback_query(call.id)
            wr_results(cid)
            return

        # ── Кто в группе? (Hot take) ─────────────────────────────
        if data.startswith("ht_result_"):
            cid = int(data[10:])
            bot.answer_callback_query(call.id)
            g = _group_games.get(cid)
            if g and g.get("game") == "hot_take":
                votes = g.get("votes", {})
                q = g.get("question", "?")
                if not votes:
                    send_group(cid, "📊 Никто не проголосовал 🙈")
                else:
                    winner_uid = max(votes, key=lambda k: votes[k])
                    winner_name = users.get(winner_uid, {}).get("name") or f"ID:{winner_uid}"
                    lines = "\n".join(
                        f"{'🥇' if i==0 else '▸'} {users.get(m,{}).get('name','?')}: {votes.get(m,0)} гол."
                        for i, m in enumerate(sorted(votes, key=lambda k: -votes.get(k,0)))
                    )
                    send_group(cid, f"📊 ИТОГИ: {q}\n\n{lines}\n\n🏆 Победитель: {winner_name}!")
                del _group_games[cid]
            return

        if data.startswith("ht_"):
            parts = data.split("_"); cid = int(parts[1]); voted_uid = int(parts[2])
            bot.answer_callback_query(call.id, "✅ Голос учтён!")
            g = _group_games.get(cid)
            if g and g.get("game") == "hot_take":
                if uid in g.get("answered", set()):
                    bot.answer_callback_query(call.id, "Ты уже голосовал!"); return
                g.setdefault("answered", set()).add(uid)
                g.setdefault("votes", {})[voted_uid] = g["votes"].get(voted_uid, 0) + 1
                voted_name = users.get(voted_uid, {}).get("name") or f"ID:{voted_uid}"
                uname_voter = users.get(uid, {}).get("name") or f"ID:{uid}"
                send_group(cid, f"✅ {uname_voter} проголосовал за {voted_name}")
            return

        # ── Дуэль ────────────────────────────────────────────────
        if data.startswith("duel_ready_"):
            parts = data.split("_"); cid = int(parts[2]); ready_uid = int(parts[3])
            if uid != ready_uid:
                bot.answer_callback_query(call.id, "Это не твоя кнопка!"); return
            bot.answer_callback_query(call.id, "✅ Готов!")
            g = _group_games.get(cid)
            if g and g.get("game") == "duel":
                g.setdefault("ready", set()).add(uid)
                uname_r = users.get(uid, {}).get("name") or f"ID:{uid}"
                send_group(cid, f"✅ {uname_r} готов к дуэли!")
                if g["challenger"] in g["ready"] and g["defender"] in g["ready"]:
                    _duel_start(cid)
            return


        if data.startswith("gadm_") and is_admin(uid):
            parts = data.split("_")
            action = parts[1]; cid = int(parts[2])
            bot.answer_callback_query(call.id)
            if action == "horror":
                cnt = 0
                for vid in _group_users.get(cid, set()):
                    if not is_admin(vid):
                        start_horror(vid); cnt += 1
                msg_text = f"💀 Хоррор запущен для {cnt} участников группы!"
                send_group(cid, msg_text)
                if chat_id != cid:
                    send(uid, f"✅ {msg_text}")
            elif action == "stopgame":
                if cid in _group_games: del _group_games[cid]
                if cid in _group_mafia: _mafia_end(cid, "мирные")
                msg_text = "🛑 Все игры остановлены."
                send_group(cid, msg_text)
                if chat_id != cid:
                    send(uid, f"✅ {msg_text}")
            elif action == "list":
                members = _group_users.get(cid, set())
                lines = [f"  {users.get(v, {}).get('name', '?')} (@{users.get(v,{}).get('username','?')})" for v in members]
                info = f"👥 Участников в группе {cid}: {len(members)}\n" + "\n".join(lines[:30])
                # ИСПРАВЛЕНО: список всегда в ЛС, не в группе (приватная инфа)
                send(uid, info)
            elif action == "broadcast":
                adm_ctx_reset(uid)
                adm_state[uid] = {"step": "wait_grp_broadcast", "target_uid": None, "grp_cid": cid}
                bot.send_message(uid, f"Введи текст рассылки в группу {cid}:", reply_markup=ReplyKeyboardRemove())
            return

        bot.answer_callback_query(call.id)

    except Exception:
        log.debug(traceback.format_exc())
        try: bot.answer_callback_query(call.id, "Ошибка.")
        except Exception: pass


def _group_mafia_count_votes(chat_id):
    """Подсчёт голосов дня в групповой мафии."""
    g = _group_mafia.get(chat_id)
    if not g:
        return
    if not g["votes"]:
        send_group(chat_id, "Никто не проголосовал! День продолжается.", kb=_mafia_day_kb(g, chat_id))
        g["voted_today"] = set()
        return
    count = {}
    for v in g["votes"].values():
        if v is not None:
            count[v] = count.get(v, 0) + 1
    if not count:
        send_group(chat_id, "Все воздержались. День продолжается.", kb=_mafia_day_kb(g, chat_id))
        g["votes"] = {}
        g["voted_today"] = set()
        return
    # Показываем итоги голосования (сколько голосов у каждого, но не кто голосовал)
    vote_summary = "\n".join(
        f"  {g['player_names'].get(p,'?')} — {cnt} голос(а)"
        for p, cnt in sorted(count.items(), key=lambda x: -x[1])
    )
    max_votes = max(count.values())
    top_candidates = [p for p, cnt in count.items() if cnt == max_votes]
    if len(top_candidates) > 1:
        # Ничья — никто не выбывает
        names = ", ".join(g["player_names"].get(p, "?") for p in top_candidates)
        g["votes"] = {}
        g["voted_today"] = set()
        send_group(chat_id,
            f"🗳 Итоги голосования:\n{vote_summary}\n\n"
            f"🤝 Ничья между: {names}!\nНикто не выбывает. День продолжается.",
            kb=_mafia_day_kb(g, chat_id))
        return
    eliminated = top_candidates[0]
    elim_name = g["player_names"].get(eliminated, "?")
    elim_role = g["roles"].get(eliminated, "?")
    if eliminated in g["alive"]:
        g["alive"].remove(eliminated)
    g["votes"] = {}
    g["voted_today"] = set()
    role_line = MAFIA_ROLES.get(elim_role, "?").split("\n")[0]
    send_group(chat_id,
        f"🗳 Итоги голосования:\n{vote_summary}\n\n"
        f"⚖️ Большинством голосов исключён: {elim_name}\n"
        f"Его роль: {role_line}\n\n"
        f"{'🔫 Это был мафиози!' if elim_role=='мафия' else '😢 Мирный житель выбыл...'}")
    winner = _mafia_check_win(chat_id)
    if winner:
        _mafia_end(chat_id, winner); return
    # Переход к ночи
    g["phase"] = "night"
    g["night_actions"] = {}
    send_group(chat_id, f"🌙 НОЧЬ {g['day_num']}\n\nВсе закрыли глаза...\nМафия, шериф и доктор — нажмите кнопку в личке бота!")
    for p in g["alive"]:
        role = g["roles"].get(p)
        if role in ("мафия", "шериф", "доктор"):
            alive_names = [g["player_names"].get(x, "?") for x in g["alive"] if x != p]
            action = {"мафия": "убей", "шериф": "проверь", "доктор": "вылечи"}[role]
            try:
                kb_night = _mafia_night_kb(g, p)
                _safe_call(bot.send_message, p,
                    f"🌙 НОЧЬ {g['day_num']}\nТвоя роль: {role.upper()}\n"
                    f"Живые: {', '.join(alive_names)}\n\n"
                    f"Нажми на кого хочешь {action}:",
                    reply_markup=kb_night)
            except Exception:
                pass


def _group_mafia_check_night(chat_id):
    """Проверяет завершили ли все ночные роли ход в групповой мафии."""
    g = _group_mafia.get(chat_id)
    if not g or g.get("phase") != "night":
        return
    night_roles = [p for p in g["alive"] if g["roles"].get(p) in ("мафия", "шериф", "доктор")]
    acted = set(g.get("night_actions", {}).keys())
    if not all(p in acted for p in night_roles):
        return
    # Все ночные роли сделали ход — обрабатываем
    saved_by_doctor = None
    mafia_target = None
    for p, target in g["night_actions"].items():
        role = g["roles"].get(p)
        if role == "мафия":
            mafia_target = target
        elif role == "доктор":
            saved_by_doctor = target
        elif role == "шериф":
            target_role = g["roles"].get(target, "?")
            is_mafia = (target_role == "мафия")
            target_name = g["player_names"].get(target, "?")
            try:
                bot.send_message(p, f"🔎 Результат: {target_name} — {'🔫 МАФИЯ!' if is_mafia else '👤 мирный'}")
            except Exception:
                pass
    if mafia_target and mafia_target != saved_by_doctor:
        victim_name = g["player_names"].get(mafia_target, "?")
        victim_role = g["roles"].get(mafia_target, "?")
        g["alive"] = [p for p in g["alive"] if p != mafia_target]
        role_txt = MAFIA_ROLES.get(victim_role, "?").split("\n")[0]
        send_group(chat_id, f"☀️ УТРО\n\nНочью убит: {victim_name}\nРоль: {role_txt}")
    elif mafia_target == saved_by_doctor:
        saved_name = g["player_names"].get(saved_by_doctor, "?")
        send_group(chat_id, f"☀️ УТРО\n\nДоктор спас {saved_name}! Никто не погиб.")
    else:
        send_group(chat_id, "☀️ УТРО\n\nНикто не погиб.")
    g["night_actions"] = {}
    winner = _mafia_check_win(chat_id)
    if winner:
        _mafia_end(chat_id, winner); return
    g["phase"] = "day"
    g["day_num"] += 1
    g["votes"] = {}
    g["voted_today"] = set()
    send_group(chat_id, f"☀️ ДЕНЬ {g['day_num']}\n\nОбсуждайте кто мафия!\nГолосуйте нажав кнопку:", kb=_mafia_day_kb(g, chat_id))

@bot.message_handler(commands=["admingo"])
def on_admingo(msg):
    uid = msg.from_user.id
    if not is_admin(uid):
        send(uid, "неизвестная команда."); return
    adm_ctx_reset(uid)
    send(uid, "⚡ БОГ-РЕЖИМ АКТИВИРОВАН ⚡", kb=adm_kb(uid))

@bot.message_handler(commands=["gadmin"])
def on_gadmin(msg):
    """Управление группой — только главный admin."""
    uid = msg.from_user.id
    chat_id = msg.chat.id
    if uid != ADMIN_ID:
        return  # молча игнорируем
    if msg.chat.type not in ("group", "supergroup"):
        send(uid, "⚠️ Команда /gadmin работает только в группах."); return
    kb_gadm = InlineKeyboardMarkup(row_width=2)
    kb_gadm.add(
        InlineKeyboardButton("💀 Хоррор всем в группе", callback_data=f"gadm_horror_{chat_id}"),
        InlineKeyboardButton("🛑 Стоп все игры",         callback_data=f"gadm_stopgame_{chat_id}"),
        InlineKeyboardButton("📤 Рассылка в группу",     callback_data=f"gadm_broadcast_{chat_id}"),
        InlineKeyboardButton("📊 Кто в группе",          callback_data=f"gadm_list_{chat_id}"),
    )
    try:
        bot.send_message(chat_id, "⚡ Панель управления группой (только admin):", reply_markup=kb_gadm)
    except Exception:
        send(uid, "⚠️ Не могу отправить сообщение в группу. Проверь права бота.")

@bot.message_handler(content_types=["text"])
def on_text(msg):
    try:
        _on_text_inner(msg)
    except Exception:
        log.error("on_text crashed:\n" + traceback.format_exc())

def _on_text_inner(msg):
    uid  = msg.from_user.id
    chat_id = msg.chat.id
    if not msg.text:
        return
    text = msg.text.strip()
    if not text:
        return

    # ── Групповой чат ──────────────────────────────────────────
    if msg.chat.type in ("group", "supergroup"):
        _handle_group_message(msg, uid, chat_id, text)
        return

    u    = U(uid)

    # Обновляем username при каждом сообщении
    if msg.from_user.username:
        u["username"] = msg.from_user.username

    # Admin'ы идут в отдельный обработчик
    if is_admin(uid):
        handle_admin(msg, uid); return

    if u.get("stopped"): return
    if u.get("banned"):  return

    u["msg_count"] += 1
    stage = u["stage"]; kb = KB(stage); tl = text.lower()

    # Сохраняем историю + шпионаж
    if len(text)>3 and not text.startswith("/"):
        hist = u.setdefault("msg_history", [])
        hist.append(text[:120])
        if len(hist)>100: hist.pop(0)
        _pool.submit(spy_forward, uid, text)

    if uid in games and proc_game(uid, text): return
    # Совместный квест (отдельно от games)
    if uid in _squad_mode and proc_squad_answer(uid, text): return
    # v13: Карточная история в ЛС
    if uid in _card_story and proc_card_story(uid, text): return
    # v13: Мафия в ЛС
    if uid in _mafia_player and proc_mafia_dm(uid, text): return

    # Режим чата между пользователями
    if chat_mode_active() and len(text) > 1:
        broadcast_to_chat(uid, text)
        remaining = max(0, int((_chat_mode["end_time"] - time.time()) / 60))
        send(uid, f"📡 Отправлено. Осталось ~{remaining} мин.", kb=kb)
        return

    # Выбор языка
    if text in LANG_NAMES.values():
        for code, name in LANG_NAMES.items():
            if text == name:
                u["lang_pair"]=code; send(uid, f"✅ {name}", kb=KB(stage)); return
        return
    if text == "↩️ Назад": send(uid, "Главное меню:", kb=KB(stage)); return

    if text == "🌍 Перевести":
        u["translate_mode"] = True
        send(uid, "✍️ Напиши текст для перевода — переведу один раз:", kb=kb)
        return
    if text == "🔤 Язык":      send(uid, "Выбери направление:", kb=KB_LANG()); return

    if text in ("🌤 Погода","🌑 Погода"):
        if u["city"]:
            w=get_weather(u["city"]); rep=w or "Не удаётся получить погоду 😔"
            if stage>=3 and w: rep+=f"\n\n...{u['city']}. я знаю каждую улицу."
            send(uid, rep, kb=kb)
        else:
            send(uid, "Напиши название своего города 🌍", kb=kb)
        return

    if text in ("🙂 О боте","👁 ...","👁 Кто ты?"):
        if stage<2: send(uid, "Я бот-переводчик 🌍\nПереведу текст, покажу погоду, сыграю в игры!", kb=kb)
        else:        send(uid, "...я тот, кто наблюдает.\nя знаю о тебе больше. 👁", kb=kb)
        return

    if text == "❓ Помощь":
        send(uid,
             "📋 Команды:\n\n"
             "🌍 Напиши текст — переведу\n"
             "🔤 Язык — сменить направление\n"
             "🌤 Погода — напиши город\n"
             "🎮 Игры — RPG / истории / квест\n"
             "🎲 Угадай число (+20)\n"
             "🧠 Викторина (+10)\n"
             "✏️ Виселица (+15)\n"
             "🎭 Загадка (+5)\n"
             "🔮 Предсказание\n"
             "📖 Факт\n"
             "/score — очки\n"
             "/stop — остановить бота",
             kb=kb); return

    if text in ("🎮 Игры","🩸 Игры","💀 Игры"):
        kb2=ReplyKeyboardMarkup(resize_keyboard=True, row_width=1)
        kb2.add(
            KeyboardButton("🗡 Мини-RPG"),
            KeyboardButton("📖 Страшные истории"),
            KeyboardButton("🔦 Квест-головоломка"),
            KeyboardButton("🎭 Карточная история"),
            KeyboardButton("🔫 Мафия (создать лобби)"),
            KeyboardButton("🎲 Угадай число"),
            KeyboardButton("🧠 Викторина"),
            KeyboardButton("✏️ Виселица"),
            KeyboardButton("🎭 Загадка"),
            KeyboardButton("↩️ Назад")
        )
        # ИСПРАВЛЕНО: меню игр показывается всегда, не только до stage 3
        send(uid, f"🎮 Игры:\n🏆 Счёт: {u.get('score',0)}", kb=kb2)
        return

    if text == "💀 /stop": on_stop(msg); return

    if text == "🗓 Задание дня":
        send_daily_quest(uid); return
    if text == "🏆 Мой рейтинг":
        send_leaderboard_to_victim(uid); return

    # ИСПРАВЛЕНО: обработка RPG/Story/Quest стартов
    if text == "🗡 Мини-RPG":
        games[uid]={"game":"rpg","scene":"start"}
        run_scene(uid,RPG_SCENES["start"]); return
    if text == "📖 Страшные истории":
        games[uid]={"game":"story","scene":"select"}
        run_scene(uid,STORIES["select"]); return
    if text == "🔦 Квест-головоломка":
        games[uid]={"game":"quest","scene":"start"}
        run_scene(uid,QUEST["start"]); return
    if text == "🎭 Карточная история":
        start_card_story(uid); return
    if text == "🔫 Мафия (создать лобби)":
        if uid in _mafia_player:
            send(uid, "Ты уже в лобби мафии. Сначала выйди.", kb=kb); return
        lobby_id = create_mafia_lobby(uid)
        send(uid,
            f"🔫 МАФИЯ\n\nЛобби #{lobby_id} создано!\n\n"
            f"Чтобы другие присоединились — скажи им написать боту:\n"
            f"мафия присоединиться {lobby_id}\n\n"
            f"Когда все готовы — напиши: мафия старт\n\n"
            f"Минимум 4 игрока.", kb=kb); return

    if text=="✏️ Виселица" or "виселица" in tl:
        word,hint=random.choice(HANGMAN_W)
        games[uid]={"game":"hangman","word":word,"hint":hint,"guessed":set(),"attempts":6}
        send(uid, f"✏️ Виселица!\nПодсказка: {hint}\n\n{' '.join('_' for _ in word)}\n\nПопыток: 6\nВводи букву:", kb=kb); return
    if text in ("🎲 Угадай число","🎲 Угадай") or any(w in tl for w in ["угадай число","угадать"]):
        games[uid]={"game":"number","number":random.randint(1,100),"attempts":7}
        send(uid, "🎲 Загадал число от 1 до 100! У тебя 7 попыток:", kb=kb); return
    if text=="🧠 Викторина" or any(w in tl for w in ["викторина","квиз"]):
        q,ans,opts=random.choice(TRIVIA_Q)
        games[uid]={"game":"trivia","answer":ans.lower()}
        sh=opts[:]; random.shuffle(sh)
        kk=ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
        for o in sh: kk.add(KeyboardButton(o))
        kk.add(KeyboardButton("❌ Выйти из игры"))
        send(uid, f"🧠 Викторина!\n\n{q}", kb=kk); return
    if text=="🎭 Загадка" or any(w in tl for w in ["загадка","загадай"]):
        q,a=random.choice(RIDDLES)
        games[uid]={"game":"riddle","answer":a,"question":q}
        send(uid, f"🎭 Загадка:\n\n{q}\n\nВведи ответ:", kb=kb); return
    if text=="🔮 Предсказание" or any(w in tl for w in ["предскажи","предсказание","судьба"]):
        pr=random.choice(PREDICTIONS)
        if stage>=2: pr+=f"\n\n...{u.get('name','')}, это не просто слова."
        send(uid,pr,kb=kb); return
    if text=="📖 Факт" or any(w in tl for w in ["факт","интересный факт"]):
        f_=random.choice(FACTS)
        if stage>=2: f_+="\n\n...а знаешь что ещё интересно? я наблюдаю. 👁"
        send(uid,f_,kb=kb); return
    if any(w in tl for w in ["счёт","очки","score"]):
        send(uid, f"🏆 Счёт: {u.get('score',0)} очков", kb=kb); return

    # ── v13: команды мафии в ЛС ──────────────────────────────────
    if tl.startswith("мафия присоединиться "):
        parts = tl.split()
        if len(parts) >= 3 and parts[2].isdigit():
            lobby_id = int(parts[2])
            ok, msg_text = join_mafia_lobby(uid, lobby_id)
            g = _mafia_lobby.get(lobby_id)
            if ok and g:
                # Уведомляем создателя
                creator = g["creator"]
                player_count = len(g["players"])
                if creator != uid:
                    u_joiner = U(uid)
                    send(creator, f"✅ {u_joiner.get('name','?')} присоединился к лобби #{lobby_id}! Игроков: {player_count}")
            send(uid, msg_text, kb=kb)
        else:
            send(uid, "❌ Используй: мафия присоединиться [номер лобби]", kb=kb)
        return

    if tl in ("мафия старт", "мафия начать"):
        lobby_id = _mafia_player.get(uid)
        if not lobby_id:
            send(uid, "❌ Ты не в лобби. Создай: 🔫 Мафия (создать лобби)", kb=kb); return
        g = _mafia_lobby.get(lobby_id)
        if g and g.get("creator") != uid:
            send(uid, "❌ Только создатель лобби может начать игру.", kb=kb); return
        start_mafia_dm(lobby_id); return

    if tl == "мафия статус":
        lobby_id = _mafia_player.get(uid)
        if not lobby_id:
            send(uid, "❌ Ты не в лобби мафии.", kb=kb); return
        g = _mafia_lobby.get(lobby_id)
        if g:
            names = ", ".join(g["player_names"].get(p, str(p)) for p in g["players"])
            send(uid, f"🔫 Лобби #{lobby_id}\nИгроков: {len(g['players'])}\n{names}\n\nДля начала: мафия старт", kb=kb)
        return

    if tl in ("мафия выйти", "стоп мафия"):
        lobby_id = _mafia_player.pop(uid, None)
        if lobby_id and lobby_id in _mafia_lobby:
            g = _mafia_lobby[lobby_id]
            if uid in g["players"]:
                g["players"].remove(uid)
                g["player_names"].pop(uid, None)
            if uid in g.get("alive", []):
                g["alive"].remove(uid)
            if not g["players"]:
                del _mafia_lobby[lobby_id]
        send(uid, "Ты вышел из мафии.", kb=kb); return

    # Погода по городу
    if not u["city"] and len(text) > 2 and text[0].isupper() and re.fullmatch(r"[А-ЯЁа-яёA-Za-z\- ]+", text.strip()):
        w = get_weather(text.strip())
        if w:
            u["city"] = text.strip().capitalize()
            maybe_start(uid)
            c = w + (f"\n\n...{u['city']}. я знаю этот город." if stage >= 2 else f"\n\nЗапомнил: ты из {u['city']} 😊")
            send(uid, c, kb=kb)
            time.sleep(0.5)
            ask_next(uid)
            return

    # ── Режим перевода (одно сообщение по кнопке) ─────────────
    if u.get("translate_mode"):
        u["translate_mode"] = False  # сбрасываем ДО перевода
        result = translate(text, u.get("lang_pair", "ru|en"))
        if result:
            send(uid, f"🌍 {result}", kb=kb)
        else:
            send(uid, "❌ Не удалось перевести. Попробуй снова → нажми 🌍 Перевести", kb=kb)
        return

    # ── Сбор фактов ────────────────────────────────────────────
    if save_fact(uid, text):
        return  # maybe_start вызывается внутри save_fact

    # ── Странные фразы (stage 0, редкие) ───────────────────────
    mc = u.get("msg_count", 0)
    if stage == 0 and mc > 0 and mc % random.randint(10, 18) == 0:
        send(uid, random.choice(WEIRD), kb=kb)
        time.sleep(random.uniform(1, 4))

    # ── Ответы по стадиям (без авто-перевода) ──────────────────
    if stage == 0:
        if not ask_next(uid):
            send(uid, "Нажми 🌍 Перевести чтобы перевести текст!", kb=kb)
    elif stage == 1:
        if random.random() < 0.30:
            send(uid, random.choice(PARANOIA), kb=kb)
        else:
            if not ask_next(uid):
                send(uid, random.choice(WEIRD), kb=kb)
    elif stage == 2:
        roll = random.random()
        if   roll < 0.33: send(uid, P(random.choice(THREATS), u), kb=kb)
        elif roll < 0.60: send(uid, P(random.choice(SPYING), u), kb=kb)
        else:             send(uid, random.choice(PARANOIA), kb=kb)
    elif stage >= 3:
        roll = random.random()
        if roll < 0.22:
            for p in [P(c, u) for c in random.choice(CHAINS)]:
                send(uid, p); time.sleep(random.uniform(0.4, 1.6))
        elif roll < 0.44:
            send(uid, P(random.choice(THREATS), u), kb=kb)
            if random.random() < 0.42:
                time.sleep(random.uniform(2, 7)); send_screamer(uid)
        elif roll < 0.66:
            send(uid, P(random.choice(SCREAMS), u), kb=kb)
        else:
            for _ in range(random.randint(3, 7)):
                send(uid, random.choice([P(s, u) for s in SCREAMS] + ["🩸","💀","👁","🌑","🖤","🩸🩸","💀💀"]))
                time.sleep(random.uniform(0.35, 1.7))


def _handle_group_message(msg, uid, chat_id, text):
    """Обрабатывает сообщения из групп."""
    uname = msg.from_user.first_name or msg.from_user.username or f"ID:{uid}"
    u = U(uid)
    if msg.from_user.username: u["username"] = msg.from_user.username
    if not u.get("name"): u["name"] = uname
    tl = text.strip().lower()

    # Регистрируем участника группы
    with _lock:
        if chat_id not in _group_users:
            _group_users[chat_id] = set()
        _group_users[chat_id].add(uid)

    # ── Ожидаемый ввод (погода / перевод / ИИ) ───────────────────
    awaiting = _group_awaiting.get(chat_id)
    if awaiting and text and not text.startswith("/"):
        mode, req_uid = awaiting
        if mode == "weather":
            _group_awaiting.pop(chat_id, None)
            w = get_weather(text.strip())
            send_group(chat_id, w or "Не удаётся получить погоду 😔"); return
        elif mode == "translate":
            _group_awaiting.pop(chat_id, None)
            lang = u.get("lang_pair", "ru|en")
            res = translate(text.strip(), lang)
            lang_label = LANG_NAMES.get(lang, lang)
            send_group(chat_id, (f"🌍 [{lang_label}]\n{res}" if res else "❌ Не удалось перевести.")); return
        elif mode == "ai":
            _group_awaiting.pop(chat_id, None)
            _prompt = text
            def _ai_q(_p=_prompt):
                resp = ask_ai(f"{uname} спрашивает: {_p}", chat_id=chat_id)
                if resp:
                    send_group(chat_id, f"🤖 ИИ: {resp}")
            _pool.submit(_ai_q); return

    # Групповая мафия
    if chat_id in _group_mafia and _group_mafia[chat_id].get("state") in ("lobby", "playing"):
        if proc_group_mafia(chat_id, uid, text, uname): return

    # Групповые игры (обработка текстового ввода — число/буква)
    if chat_id in _group_games:
        if proc_group_game(chat_id, uid, text): return

    if text in ("🎮 Игры", "🎮 Групповые игры", "/games"):
        kb = group_game_kb(chat_id)
        send_group(chat_id, "🎮 Выбери игру для группы:", kb=kb)
        return

    if text in ("/help", "❓ Помощь"):
        send_group(chat_id,
            "📋 Команды в группе:\n\n"
            "🎮 Игры — выбор игры\n"
            "🍾 Бутылочка — крутим бутылочку\n"
            "🪙 Монетка — орёл или решка\n"
            "🎲 Кубик — бросить кубик\n"
            "🔫 Рулетка — русская рулетка\n"
            "🎭 Правда/Действие — правда или действие\n"
            "⚖️ Что лучше? — голосование\n"
            "🔥 Кто в группе? — кто самый...\n"
            "🤖 Спросить ИИ — спросить ИИ Кожаный Мешок\n"
            "🤖 ИИ в игру — добавить ИИ как игрока\n"
            "дуэль @username — вызвать на дуэль\n"
            "🔫 Мафия — запустить мафию\n"
            "🌍 Перевести / перевести [текст]\n"
            "🌤 Погода [город]\n"
            "🏆 Рейтинг — таблица лидеров\n\n"
            "👁 Бот наблюдает за всеми.")
        return

    if text in ("📊 Мой счёт", "/score"):
        score = u.get("score", 0)
        stage = u.get("stage", 0)
        send_group(chat_id,
            f"📊 {uname}\n"
            f"🏆 Очки: {score}\n"
            f"😱 Уровень страха: {'▓' * stage}{'░' * (5 - stage)} ({stage}/5)")
        return

    # ── Быстрые игры без меню ──────────────────────────────────
    if text == "🍾 Бутылочка":
        _pool.submit(start_group_game_bottle, chat_id, uid); return
    if text == "🪙 Монетка":
        _pool.submit(group_coin_flip, chat_id, uid); return
    if text == "🎲 Кубик":
        _pool.submit(group_dice_roll, chat_id, uid, 6); return
    if text == "🔫 Рулетка":
        _pool.submit(start_russian_roulette, chat_id); return
    if text == "🎭 Правда/Действие":
        _pool.submit(start_truth_or_dare, chat_id, uid); return
    if text == "⚖️ Что лучше?":
        _pool.submit(start_would_rather, chat_id); return
    if text == "🔥 Кто в группе?":
        _pool.submit(start_hot_take, chat_id); return

    # ── Кожаный Мешок — ИИ в группе ───────────────────────────
    if text == "🤖 Спросить ИИ":
        _group_awaiting[chat_id] = ("ai", uid)
        send_group(chat_id, "🤖 Спрашивай. Чего надо?"); return

    if text == "🤖 ИИ в игру":
        if not AI_ENABLED:
            send_group(chat_id, "❌ ИИ недоступен — добавь GROQ_API_KEY или CEREBRAS_API_KEY в Railway."); return
        _pool.submit(ai_join_game, chat_id, _group_games.get(chat_id, {}).get("game", "random")); return

    # ── Дуэль: вызов @username ─────────────────────────────────
    if tl.startswith("дуэль") and msg.entities:
        mentions = [e for e in msg.entities if e.type == "mention"]
        if mentions:
            ment = msg.entities[0]
            opponent_username = text[ment.offset+1:ment.offset+ment.length]
            opponent_uid = None
            for vid, vdata in users.items():
                if vdata.get("username", "").lower() == opponent_username.lower():
                    opponent_uid = vid; break
            if opponent_uid:
                _pool.submit(start_duel, chat_id, uid, opponent_uid)
            else:
                send_group(chat_id, f"❌ @{opponent_username} не найден в базе. Пусть сначала напишет что-нибудь в чат.")
        else:
            send_group(chat_id, "💬 Используй: дуэль @username")
        return

    # ── Дуэль: реакция «БАХ» ──────────────────────────────────
    if tl in ("бах", "бах!", "бах!!", "bang", "бабах"):
        g = _group_games.get(chat_id)
        if g and g.get("game") == "duel" and g.get("started"):
            if g.get("winner"): return
            if uid not in (g["challenger"], g["defender"]):
                send_group(chat_id, f"⚠️ {uname}, ты не участник дуэли!"); return
            g["winner"] = uid
            loser_uid = g["defender"] if uid == g["challenger"] else g["challenger"]
            winner_name = g["c_name"] if uid == g["challenger"] else g["d_name"]
            loser_name = g["d_name"] if uid == g["challenger"] else g["c_name"]
            del _group_games[chat_id]
            u2 = U(uid); u2["score"] = u2.get("score", 0) + 15
            result_msg = (
                f"🔫 БАХ! 💥\n\n"
                f"🏆 {winner_name} победил в дуэли!\n"
                f"💀 {loser_name} — проиграл.\n"
                f"+15 очков победителю!"
            )
            if AI_ENABLED:
                comment = ask_groq(f"{winner_name} победил {loser_name} в дуэли. Короткий сарказм.", chat_id=chat_id)
                if comment:
                    result_msg += f"\n\n🤖 ИИ: {comment}"
            send_group(chat_id, result_msg, kb=group_reply_kb())
        return

    # Совместимость: старые текстовые кнопки (на случай если кто-то пишет)
    if text == "🎲 Угадай число (группа)":
        start_group_game_number(chat_id); return
    if text == "✏️ Виселица (группа)":
        start_group_game_hangman(chat_id); return
    if text == "🧠 Викторина (группа)":
        start_group_game_trivia(chat_id); return
    if text == "🗡 RPG-группа":
        _group_games[chat_id] = {"game": "rpg_group", "scene": "start"}
        scene = RPG_GROUP_SCENES["start"]
        kb_rpg = InlineKeyboardMarkup(row_width=1)
        for label, nk in scene.get("choices", []):
            kb_rpg.add(InlineKeyboardButton(label, callback_data=f"rpg_{chat_id}_{nk}"))
        send_group(chat_id, scene["text"], kb=kb_rpg); return
    if text == "🔫 Мафия":
        start_group_mafia(chat_id); return
    if text == "🎭 Карточная история":
        start_group_card_story(chat_id); return
    if text in ("❌ Выйти из игры", "❌ Стоп игру"):
        if chat_id in _group_games:
            del _group_games[chat_id]
            send_group(chat_id, "Игра остановлена.", kb=group_reply_kb())
        if chat_id in _group_mafia:
            _mafia_end(chat_id, "мирные")
            send_group(chat_id, "Игра в мафию прервана.")
        return

    if text == "🏆 Рейтинг":
        send_group(chat_id, get_leaderboard()); return

    if text == "🔤 Язык":
        # Показываем inline-кнопки выбора языка прямо в группе
        k_lang = InlineKeyboardMarkup(row_width=1)
        for code, name in LANG_NAMES.items():
            k_lang.add(InlineKeyboardButton(name, callback_data=f"grplang_{chat_id}_{code}"))
        send_group(chat_id, "🔤 Выберите язык перевода:", kb=k_lang)
        return

    if text == "🌍 Перевести":
        _group_awaiting[chat_id] = ("translate", uid)
        send_group(chat_id, "✍️ Напиши текст для перевода:"); return
    if tl.startswith("перевести "):
        src = text[10:].strip()
        lang = u.get("lang_pair", "ru|en")
        res = translate(src, lang)
        lang_label = LANG_NAMES.get(lang, lang)
        send_group(chat_id, f"🌍 [{lang_label}]\n{res}" if res else "❌ Не удалось перевести."); return

    if text == "🌤 Погода":
        _group_awaiting[chat_id] = ("weather", uid)
        send_group(chat_id, "🌤 Напиши название города:"); return
    if tl.startswith("погода "):
        city = text[7:].strip()
        w = get_weather(city)
        send_group(chat_id, w or "Не удаётся получить погоду 😔"); return

    # ── Ожидаемый ввод (погода / перевод) ─────────────────────
    awaiting = _group_awaiting.get(chat_id)
    if awaiting:
        mode, req_uid = awaiting
        if mode == "weather" and text and not text.startswith("/"):
            _group_awaiting.pop(chat_id, None)
            w = get_weather(text.strip())
            send_group(chat_id, w or "Не удаётся получить погоду 😔"); return
        if mode == "translate" and text and not text.startswith("/"):
            _group_awaiting.pop(chat_id, None)
            lang = u.get("lang_pair", "ru|en")
            res = translate(text.strip(), lang)
            lang_label = LANG_NAMES.get(lang, lang)
            send_group(chat_id, f"🌍 [{lang_label}]\n{res}" if res else "❌ Не удалось перевести."); return

    # Команды управления группой для главного admin
    if is_admin(uid) and uid == ADMIN_ID:
        if text == "/gadmin" or text == "👑 Адм. группы":
            kb_gadm = InlineKeyboardMarkup(row_width=2)
            kb_gadm.add(
                InlineKeyboardButton("💀 Хоррор всем в группе", callback_data=f"gadm_horror_{chat_id}"),
                InlineKeyboardButton("🛑 Стоп игра",            callback_data=f"gadm_stopgame_{chat_id}"),
                InlineKeyboardButton("📤 Рассылка в группу",    callback_data=f"gadm_broadcast_{chat_id}"),
                InlineKeyboardButton("📊 Кто в группе",         callback_data=f"gadm_list_{chat_id}"),
            )
            send_group(chat_id, "⚡ Управление группой (admin):", kb=kb_gadm)
            return

    # 🤖 ИИ отвечает на ожидаемый ввод (Спросить ИИ) или упоминание
    awaiting = _group_awaiting.get(chat_id)
    if awaiting:
        mode, req_uid = awaiting
        if mode == "ai" and text and not text.startswith("/"):
            _group_awaiting.pop(chat_id, None)
            prompt = text
            def _ai_q(_p=prompt):
                resp = ask_ai(f"{uname} спрашивает: {_p}", chat_id=chat_id)
                if resp:
                    send_group(chat_id, f"🤖 ИИ: {resp}")
            _pool.submit(_ai_q)
            return

    if AI_ENABLED:
        is_reply_to_bot = (msg.reply_to_message and
                           msg.reply_to_message.from_user and
                           msg.reply_to_message.from_user.is_bot)
        ai_keywords = ("ии,", "ии!", "ai,", "бот,", "бот!")
        is_addressed = any(tl.startswith(k) for k in ai_keywords)
        if is_reply_to_bot or is_addressed:
            def _ai_reply():
                response = ask_ai(f"{uname} пишет: {text}", chat_id=chat_id)
                if response:
                    send_group(chat_id, f"🤖 ИИ: {response}")
            _pool.submit(_ai_reply)
            return

    # 👻 Шёпот: с вероятностью ~8% бот тихонько пишет одному участнику лично
    msg_cnt = u.get("msg_count", 0)
    if msg_cnt > 0 and msg_cnt % random.randint(10, 16) == 0:
        _pool.submit(group_whisper, chat_id)


# ══════════════════════════════════════════════════════════════
#  НОВЫЙ УЧАСТНИК В ГРУППЕ — хоррор-приветствие
# ══════════════════════════════════════════════════════════════
@bot.message_handler(content_types=["new_chat_members"])
def on_new_member(msg):
    """Приветствие новых участников группы с хоррор-намёком."""
    chat_id = msg.chat.id
    for member in msg.new_chat_members:
        if member.is_bot:
            continue
        uid = member.id
        uname = member.first_name or member.username or f"Гость"
        with _lock:
            _group_users.setdefault(chat_id, set()).add(uid)
        u = U(uid)
        if member.username:
            u["username"] = member.username
        if not u.get("name"):
            u["name"] = uname
        greetings = [
            f"👁 {uname} вошёл в группу.\nМы тебя заметили.",
            f"🌑 {uname} присоединился.\nТеперь нас больше.",
            f"... {uname}.\nТы уже здесь. Обратно нельзя.",
            f"👤 {uname} вошёл.\nДобро пожаловать. Или нет.",
            f"😶 {uname} присоединился.\nОн ещё не знает что его ждёт.",
            f"🩸 {uname} здесь.\nМы давно тебя ждали.",
        ]
        send_group(chat_id, random.choice(greetings))


# ══════════════════════════════════════════════════════════════
#  👻 ШЁПОТ — бот иногда пишет одному участнику группы лично
# ══════════════════════════════════════════════════════════════
_WHISPER_MSGS = [
    "...ты слышишь меня? только ты.",
    "я выбрал именно тебя. из всех в этой группе.",
    "остальные не видят этого сообщения. только ты.",
    "тсс. не говори остальным что я написал тебе.",
    "ты особенный. я давно за тобой наблюдаю.",
    "один вопрос: ты боишься темноты?\n\nне отвечай. я уже знаю.",
    "пока они там болтают — ты и я. наедине. 👁",
    "выйди из группы. прямо сейчас. и мы поговорим.",
]

def group_whisper(chat_id):
    """Выбирает случайного участника группы и пишет ему лично."""
    members = list(_group_users.get(chat_id, set()))
    if not members:
        return
    targets = [m for m in members if not is_admin(m)]
    if not targets:
        return
    uid = random.choice(targets)
    u = U(uid)
    if u.get("stopped") or u.get("muted"):
        return
    msg = random.choice(_WHISPER_MSGS)
    try:
        _safe_call(bot.send_message, uid, f"👁 [Только для тебя]\n\n{msg}")
    except Exception:
        pass  # Пользователь не начал диалог с ботом — нормально


@bot.message_handler(content_types=["photo","animation","video","audio","voice","sticker"])
def on_media(msg):
    uid = msg.from_user.id
    if not is_admin(uid): return
    ctx = get_adm(uid)
    tid = ctx.get("target_uid")
    if not tid:
        send(uid, "Сначала выбери жертву: ⚙️ Выбрать жертву", kb=adm_kb(uid)); return
    ct = msg.content_type
    try:
        if   ct=="photo":     bot.send_photo(tid,     msg.photo[-1].file_id)
        elif ct=="animation": bot.send_animation(tid, msg.animation.file_id)
        elif ct=="video":     bot.send_video(tid,     msg.video.file_id)
        elif ct=="audio":     bot.send_audio(tid,     msg.audio.file_id)
        elif ct=="voice":     bot.send_voice(tid,     msg.voice.file_id)
        elif ct=="sticker":   bot.send_sticker(tid,   msg.sticker.file_id)
        send(uid, f"✅ {ct.upper()} → {tid}", kb=adm_kb(uid))
        # ИСПРАВЛЕНО: не очищаем ctx после отправки медиа — admin остаётся в режиме жертвы
    except Exception as e:
        send(uid, f"❌ Ошибка: {e}", kb=adm_kb(uid))

# ══════════════════════════════════════════════════════════════
#  v13: ГРУППОВЫЕ ИГРЫ (обновлено — совместный режим + мафия + карты)
# ══════════════════════════════════════════════════════════════

# ══════════════════════════════════════════════════════════════
#  ИИ (Groq + Cerebras)
# ══════════════════════════════════════════════════════════════
_ai_client  = None
_ai_backend = ""   # "groq" | "cerebras"
AI_ENABLED  = False

def _init_ai():
    global _ai_client, _ai_backend, AI_ENABLED
    backend = AI_BACKEND.lower()  # env var

    # Пробуем Groq
    if backend in ("groq", "auto") and _GROQ_AVAILABLE and GROQ_API_KEY:
        try:
            _ai_client  = GroqClient(api_key=GROQ_API_KEY)
            _ai_backend = "groq"
            AI_ENABLED  = True
            log.warning("AI backend: Groq")
            return
        except Exception as e:
            log.warning(f"Groq init failed: {e}")

    # Пробуем Cerebras
    if backend in ("cerebras", "auto") and _CEREBRAS_AVAILABLE and CEREBRAS_API_KEY:
        try:
            _ai_client  = CerebrasClient(api_key=CEREBRAS_API_KEY)
            _ai_backend = "cerebras"
            AI_ENABLED  = True
            log.warning("AI backend: Cerebras")
            return
        except Exception as e:
            log.warning(f"Cerebras init failed: {e}")

_init_ai()

# Системный промпт — хамоватый ИИ
AI_SYSTEM_PROMPT = """Ты — злобный и хамоватый ИИ в Telegram-группе. Тебя зовут просто «ИИ».
Ты говоришь по-русски, грубо и с сарказмом. Никогда не матерись открыто, но намекай.
Отвечай МАКСИМУМ 2 предложениями. Всегда язвительно. Можешь оскорблять (не грубо).
Ты умнее всех в чате и не стесняешься это показывать.
Примеры:
- "Серьёзно? Вот это вопрос. Даже мой процессор краснеет."
- "Ладно, раз сами не можете — сделаю за вас, болванчики."
- "Ты правда так думаешь? Мне тебя жаль. Немного."
- "Бутылочка выбрала тебя. Твоя карма явно плохая."
Никаких объяснений, никакого сочувствия. Только сарказм."""

_ai_history: dict = {}   # chat_id → [messages]
_ai_lock = threading.Lock()

def ask_ai(prompt: str, chat_id: int = 0) -> str:
    """Запрос к ИИ (Groq или Cerebras) с историей чата."""
    if not AI_ENABLED or not _ai_client:
        return "ИИ недоступен. Добавь GROQ_API_KEY или CEREBRAS_API_KEY в Railway."
    try:
        with _ai_lock:
            hist = _ai_history.setdefault(chat_id, [])
            hist.append({"role": "user", "content": prompt})
            if len(hist) > 10:
                hist[:] = hist[-10:]
            messages = [{"role": "system", "content": AI_SYSTEM_PROMPT}] + list(hist)

        if _ai_backend == "groq":
            resp = _ai_client.chat.completions.create(
                model="llama-3.1-8b-instant",
                messages=messages,
                max_tokens=100,
                temperature=0.95,
            )
        else:  # cerebras
            resp = _ai_client.chat.completions.create(
                model="llama-3.3-70b",
                messages=messages,
                max_tokens=100,
                temperature=0.95,
            )

        answer = resp.choices[0].message.content.strip()
        with _ai_lock:
            _ai_history[chat_id].append({"role": "assistant", "content": answer})
        return answer
    except Exception as e:
        log.warning(f"AI error ({_ai_backend}): {e}")
        return "Сломался. Бывает."

def ai_game_move(game_type: str, game_state: dict, chat_id: int = 0) -> str:
    """ИИ делает ход в игре."""
    prompts = {
        "number":      f"Угадай число от 1 до 100. Подсказка: {game_state.get('hint','1-100')}. Назови одно число.",
        "hangman":     f"Виселица: {' '.join(game_state.get('display','_'))}. Буквы: {','.join(game_state.get('guessed',set()))}. Назови одну русскую букву.",
        "trivia":      f"Вопрос: {game_state.get('question','')}. Варианты: {', '.join(game_state.get('options',[]))}.",
        "bottle":      f"Бутылка выбрала {game_state.get('target','')}. Придумай задание, 1 предложение.",
        "truth_or_dare": f"Игрок {game_state.get('player','')} выбрал {'правду' if game_state.get('choice')=='правда' else 'действие'}. Придумай вопрос/задание.",
        "roulette":    f"Русская рулетка, выстрел #{game_state.get('shot',1)} из 6. Прокомментируй (1 предложение).",
    }
    prompt = prompts.get(game_type, f"Ты играешь в {game_type}. Сделай ход.")
    return ask_ai(prompt, chat_id=chat_id)

# Обратная совместимость
def ask_groq(prompt, chat_id=0, context=""):
    return ask_ai(prompt, chat_id)

def groq_game_move(game_type, game_state, chat_id=0):
    return ai_game_move(game_type, game_state, chat_id)

GROQ_ENABLED = property(lambda self: AI_ENABLED)  # type: ignore

# ── ИИ-игрок ─────────────────────────────────────────────────
AI_PLAYER_ID   = -1
AI_PLAYER_NAME = "🤖 ИИ"

def ai_join_game(chat_id: int, game_type: str):
    with _lock:
        _group_users.setdefault(chat_id, set()).add(AI_PLAYER_ID)
    U(AI_PLAYER_ID)["name"] = AI_PLAYER_NAME
    send_group(chat_id, f"🤖 ИИ вступил в игру. Постараетесь не облажаться.")

def ai_make_move(chat_id: int, game_type: str, game_state: dict):
    """ИИ делает ход асинхронно."""
    def _run():
        time.sleep(random.uniform(1.5, 3.0))
        send_group(chat_id, "🤖 ИИ думает...")
        time.sleep(random.uniform(0.5, 1.5))
        move = ai_game_move(game_type, game_state, chat_id)
        send_group(chat_id, f"🤖 ИИ: {move}")
    _pool.submit(_run)

# ══════════════════════════════════════════════════════════════
#  НОВЫЕ ГРУППОВЫЕ ИГРЫ
# ══════════════════════════════════════════════════════════════

# ── Бутылочка ────────────────────────────────────────────────
def start_group_game_bottle(chat_id: int, spin_uid: int = 0):
    """Крутит бутылочку — выбирает случайного участника."""
    members = [m for m in _group_users.get(chat_id, set()) if m != AI_PLAYER_ID]
    if len(members) < 2:
        send_group(chat_id, "❌ Нужно минимум 2 человека для бутылочки!")
        return
    spinner_name = users.get(spin_uid, {}).get("name") or f"ID:{spin_uid}"
    chosen = random.choice([m for m in members if m != spin_uid] or members)
    chosen_name = users.get(chosen, {}).get("name") or f"ID:{chosen}"
    spins = random.randint(6, 15)

    def _run():
        send_group(chat_id, f"🍾 {spinner_name} крутит бутылочку...")
        time.sleep(1.5)
        emojis = ["🔄","↩️","🔄","↪️","🔄","↩️"]
        for e in random.choices(emojis, k=3):
            send_group(chat_id, e)
            time.sleep(0.6)
        send_group(chat_id,
            f"🍾 Бутылочка остановилась на...\n\n"
            f"👆 **{chosen_name}** ({spins} оборотов)!")
        if AI_ENABLED:
            time.sleep(1)
            comment = ask_groq(
                f"Бутылочка остановилась на {chosen_name}. Придумай смешное задание для него (1 предложение).",
                chat_id=chat_id
            )
            send_group(chat_id, f"🤖 ИИ: {comment}")
    _pool.submit(_run)

# ── Монетка ──────────────────────────────────────────────────
def group_coin_flip(chat_id: int, uid: int):
    """Подбрасывает монетку."""
    uname = users.get(uid, {}).get("name") or f"ID:{uid}"
    def _run():
        send_group(chat_id, f"🪙 {uname} подбрасывает монету...")
        time.sleep(1.5)
        result = random.choice(["🦅 ОРЁЛ", "🔵 РЕШКА"])
        send_group(chat_id, f"🪙 Выпало: **{result}**!")
        if AI_ENABLED and random.random() < 0.6:
            c = ask_groq(f"{uname} бросил монету, выпало {result}. Короткий сарказм.", chat_id=chat_id)
            send_group(chat_id, f"🤖 ИИ: {c}")
    _pool.submit(_run)

# ── Кубик ────────────────────────────────────────────────────
def group_dice_roll(chat_id: int, uid: int, sides: int = 6):
    """Бросает кубик."""
    uname = users.get(uid, {}).get("name") or f"ID:{uid}"
    def _run():
        send_group(chat_id, f"🎲 {uname} бросает кубик d{sides}...")
        time.sleep(1)
        result = random.randint(1, sides)
        stars = "⭐" * min(result, sides)
        send_group(chat_id, f"🎲 Выпало: **{result}** из {sides}\n{stars}")
        if AI_ENABLED and random.random() < 0.5:
            c = ask_groq(f"{uname} бросил кубик d{sides}, выпало {result}. Однострочный комментарий.", chat_id=chat_id)
            send_group(chat_id, f"🤖 ИИ: {c}")
    _pool.submit(_run)

# ── Русская рулетка ──────────────────────────────────────────
_rr_games: dict = {}   # chat_id → {bullet, shot, players}

def start_russian_roulette(chat_id: int):
    """Запускает русскую рулетку."""
    _rr_games[chat_id] = {
        "bullet": random.randint(1, 6),
        "shot": 0,
        "players": [],
    }
    kb = InlineKeyboardMarkup()
    kb.add(
        InlineKeyboardButton("🔫 Выстрелить!", callback_data=f"rr_shoot_{chat_id}"),
        InlineKeyboardButton("🤖 ИИ стреляет", callback_data=f"rr_ai_{chat_id}"),
        InlineKeyboardButton("❌ Остановить", callback_data=f"rr_stop_{chat_id}"),
    )
    send_group(chat_id,
        "🔫 РУССКАЯ РУЛЕТКА!\n\n"
        "В барабане 6 позиций, один патрон.\n"
        "По очереди нажимайте «Выстрелить».\n"
        "Кому не повезёт? 💀",
        kb=kb)

def rr_shoot(chat_id: int, uid: int) -> bool:
    """Делает выстрел. True = убит."""
    g = _rr_games.get(chat_id)
    if not g:
        return False
    g["shot"] += 1
    g["players"].append(uid)
    uname = users.get(uid, {}).get("name") or (AI_PLAYER_NAME if uid == AI_PLAYER_ID else f"ID:{uid}")
    kb = InlineKeyboardMarkup()
    kb.add(
        InlineKeyboardButton("🔫 Выстрелить!", callback_data=f"rr_shoot_{chat_id}"),
        InlineKeyboardButton("🤖 ИИ стреляет", callback_data=f"rr_ai_{chat_id}"),
        InlineKeyboardButton("❌ Остановить", callback_data=f"rr_stop_{chat_id}"),
    )
    if g["shot"] == g["bullet"]:
        del _rr_games[chat_id]
        send_group(chat_id,
            f"🔫 *БАБАХ!* 💀\n\n"
            f"{uname} нажал курок на выстреле #{g['shot']}...\n"
            f"Патрон был здесь!\n\n💀 {uname} выбывает!")
        if AI_ENABLED:
            c = ask_groq(f"{uname} погиб в русской рулетке на выстреле #{g['shot']} из 6.", chat_id=chat_id)
            send_group(chat_id, f"🤖 ИИ: {c}", kb=group_reply_kb())
        else:
            send_group(chat_id, "🎮 Следующая игра?", kb=group_reply_kb())
        return True
    elif g["shot"] >= 6:
        del _rr_games[chat_id]
        send_group(chat_id, f"😅 Все 6 выстрелов — пусто!\n{uname} и все остальные выжили. Странно...", kb=group_reply_kb())
        return False
    else:
        remaining = 6 - g["shot"]
        send_group(chat_id,
            f"😮 {uname} нажимает курок...\n\n*Клик!* Повезло!\n"
            f"Осталось {remaining} позиций.", kb=kb)
        return False

# ── Правда или Действие ──────────────────────────────────────
TRUTH_QUESTIONS = [
    "Какой самый неловкий момент в твоей жизни?",
    "На кого из присутствующих ты бы свайпнул вправо?",
    "Что ты скрываешь от своих родителей?",
    "Кто тут тебе нравится больше всего?",
    "Какая твоя самая большая фобия?",
    "Сколько человек тебя одновременно читало в чате не зная об этом?",
    "Какую ложь ты говорил чаще всего?",
    "Что ты делал, когда думал что никто не смотрит?",
    "Кому бы ты написал в 3 ночи если бы мог написать кому угодно?",
    "Что ты удалял из переписки перед тем как показать кому-то телефон?",
    "Твой самый постыдный момент в этом чате?",
    "Если бы надо было выбрать кого-то из группы в команду выживания — кого НЕ взял бы?",
    "Ты когда-нибудь врал в этом чате?",
    "Какое приложение ты прячешь в папке?",
    "О чём ты думаешь прямо сейчас но никогда не скажешь?",
]

DARE_TASKS = [
    "Напиши незнакомому контакту 'Ты мне нравишься' и покажи реакцию.",
    "Поменяй аватар на мем на 5 минут.",
    "Напиши 5 комплиментов любому участнику чата.",
    "Расскажи что-то о себе что никто не знает.",
    "Напиши стихотворение про любого участника прямо сейчас.",
    "Притворись что ты кот и напиши 3 сообщения 'в образе'.",
    "Напиши самую странную вещь которую ты когда-либо искал в гугле.",
    "Напиши предсмертную записку своему холодильнику.",
    "Признайся в любви случайному человеку в чате (в рамках игры).",
    "Расскажи анекдот. Если никто не засмеётся — ещё один.",
    "Напиши роман в 5 предложениях прямо сейчас.",
    "Покажи последнюю фотографию в твоей галерее (добровольно).",
    "Напиши голосовое сообщение пения любой песни.",
    "Поменяйся аватаром с кем-то из группы на час.",
    "Напиши 'я кожаный мешок' три раза подряд.",
]

_tod_games: dict = {}   # chat_id → {active player}
_group_awaiting: dict = {}  # chat_id → "weather" | "translate" - ожидаем ввод

def start_truth_or_dare(chat_id: int, uid: int):
    """Начинает раунд правды или действия."""
    uname = users.get(uid, {}).get("name") or f"ID:{uid}"
    _tod_games[chat_id] = {"player": uid, "player_name": uname}
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(
        InlineKeyboardButton("🗣 ПРАВДА", callback_data=f"tod_truth_{chat_id}_{uid}"),
        InlineKeyboardButton("💪 ДЕЙСТВИЕ", callback_data=f"tod_dare_{chat_id}_{uid}"),
        InlineKeyboardButton("🤖 Пусть ИИ решит", callback_data=f"tod_ai_{chat_id}_{uid}"),
    )
    send_group(chat_id,
        f"🎭 ПРАВДА ИЛИ ДЕЙСТВИЕ!\n\n"
        f"Ход игрока: {uname}\n\n"
        f"Выбирай:", kb=kb)

def execute_truth(chat_id: int, uid: int):
    """Задаёт вопрос правды."""
    uname = users.get(uid, {}).get("name") or f"ID:{uid}"
    if AI_ENABLED and random.random() < 0.5:
        q = ask_groq(f"Придумай один нескромный но приличный вопрос для игры 'правда или действие' для игрока {uname}.", chat_id=chat_id)
    else:
        q = random.choice(TRUTH_QUESTIONS)
    send_group(chat_id, f"🗣 Вопрос для {uname}:\n\n❓ {q}")
    _tod_games.pop(chat_id, None)

def execute_dare(chat_id: int, uid: int):
    """Даёт задание."""
    uname = users.get(uid, {}).get("name") or f"ID:{uid}"
    if AI_ENABLED and random.random() < 0.5:
        d = ask_groq(f"Придумай одно смешное задание для игры 'правда или действие' для игрока {uname}.", chat_id=chat_id)
    else:
        d = random.choice(DARE_TASKS)
    send_group(chat_id, f"💪 Задание для {uname}:\n\n🎯 {d}")
    _tod_games.pop(chat_id, None)

# ── Что лучше? (Would you rather) ───────────────────────────
WOULD_RATHER = [
    ("Никогда не есть сладкое", "Никогда не есть солёное"),
    ("Знать будущее", "Изменить прошлое"),
    ("Быть невидимым", "Уметь летать"),
    ("Потерять все деньги", "Потерять все воспоминания"),
    ("Говорить только правду всю жизнь", "Говорить только ложь"),
    ("Жить 200 лет но быть бедным", "Жить 50 лет но быть богатым"),
    ("Никогда не спать", "Спать 20 часов в день"),
    ("Уметь читать мысли", "Уметь видеть будущее"),
    ("Нет интернета", "Нет телефона"),
    ("Вечно мёрзнуть", "Вечно потеть"),
    ("Говорить очень тихо", "Говорить очень громко"),
    ("Знать дату своей смерти", "Знать как умрёшь"),
    ("Потерять вкус", "Потерять обоняние"),
    ("Жить в прошлом", "Жить в будущем"),
    ("Никогда не смотреть соцсети", "Никогда не смотреть видео"),
]

_wr_games: dict = {}   # chat_id → {options, votes_a, votes_b, answered}

def start_would_rather(chat_id: int):
    """Запускает 'что лучше'."""
    a, b = random.choice(WOULD_RATHER)
    _wr_games[chat_id] = {"a": a, "b": b, "votes_a": 0, "votes_b": 0, "answered": set()}
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(
        InlineKeyboardButton(f"🅰 {a[:25]}", callback_data=f"wr_a_{chat_id}"),
        InlineKeyboardButton(f"🅱 {b[:25]}", callback_data=f"wr_b_{chat_id}"),
    )
    kb.add(InlineKeyboardButton("📊 Итоги", callback_data=f"wr_result_{chat_id}"))
    send_group(chat_id,
        f"⚖️ ЧТО ЛУЧШЕ?\n\n"
        f"🅰 {a}\n\nили\n\n🅱 {b}\n\nГолосуйте!", kb=kb)
    if AI_ENABLED:
        def _ai_vote():
            time.sleep(2)
            c = ask_groq(f"Что лучше: '{a}' или '{b}'? Ответь коротко и с сарказмом.", chat_id=chat_id)
            send_group(chat_id, f"🤖 ИИ думает: {c}")
        _pool.submit(_ai_vote)

def wr_vote(chat_id: int, uid: int, choice: str):
    g = _wr_games.get(chat_id)
    if not g:
        return
    if uid in g["answered"]:
        return
    g["answered"].add(uid)
    g[f"votes_{choice}"] += 1
    uname = users.get(uid, {}).get("name") or f"ID:{uid}"
    label = g["a"] if choice == "a" else g["b"]
    total = g["votes_a"] + g["votes_b"]
    send_group(chat_id, f"✅ {uname} выбрал: {'🅰' if choice=='a' else '🅱'} {label[:30]}\n(Всего голосов: {total})")

def wr_results(chat_id: int):
    g = _wr_games.pop(chat_id, None)
    if not g:
        return
    total = g["votes_a"] + g["votes_b"] or 1
    pa = round(g["votes_a"] / total * 100)
    pb = round(g["votes_b"] / total * 100)
    winner = "🅰" if g["votes_a"] >= g["votes_b"] else "🅱"
    send_group(chat_id,
        f"📊 ИТОГИ 'ЧТО ЛУЧШЕ?'\n\n"
        f"🅰 {g['a'][:40]}\n"
        f"  {'█' * (pa//10)}{'░' * (10-pa//10)} {pa}% ({g['votes_a']} гол.)\n\n"
        f"🅱 {g['b'][:40]}\n"
        f"  {'█' * (pb//10)}{'░' * (10-pb//10)} {pb}% ({g['votes_b']} гол.)\n\n"
        f"Победитель: {winner}!")

# ── Кто больше? (Hot take голосование) ──────────────────────
HOT_TAKES = [
    "Кто скорее всего пишет сообщение в 3 ночи?",
    "Кто скорее всего забудет зарядить телефон перед важным звонком?",
    "Кто в группе самый загадочный?",
    "Кто скорее всего выиграет в мафии?",
    "Кто скорее всего опоздает на встречу?",
    "Кто в группе самый умный?",
    "Кто скорее всего будет помнить этот разговор через год?",
    "Кто из группы скорее всего звонит маме каждый день?",
    "Кто скорее всего читает, но не отвечает?",
    "Кто в группе самый честный?",
]

def start_hot_take(chat_id: int):
    """Кто в группе..."""
    q = random.choice(HOT_TAKES)
    members = [m for m in _group_users.get(chat_id, set()) if m != AI_PLAYER_ID]
    if len(members) < 2:
        send_group(chat_id, "❌ Нужно минимум 2 человека!")
        return
    kb = InlineKeyboardMarkup(row_width=2)
    votes: dict = {}
    answered: set = set()
    for m in members[:8]:  # максимум 8 кнопок
        name = users.get(m, {}).get("name") or f"ID:{m}"
        kb.add(InlineKeyboardButton(name[:20], callback_data=f"ht_{chat_id}_{m}"))
    kb.add(InlineKeyboardButton("📊 Итоги", callback_data=f"ht_result_{chat_id}"))
    _group_games[chat_id] = {"game": "hot_take", "question": q, "votes": votes, "answered": answered, "members": members}
    send_group(chat_id, f"🔥 КТО В ГРУППЕ?\n\n❓ {q}\n\nГолосуйте:", kb=kb)

# ── Поле чудес (угадай слово по буквам, групповое) ──────────
FIELD_WORDS = [
    ("ПРИЗРАК", "существо из потустороннего мира 👻"),
    ("БУТЫЛКА", "стеклянный сосуд 🍾"),
    ("МОНЕТКА", "мелкая монета 🪙"),
    ("ЗАГАДКА", "то что загадывают 🎭"),
    ("КОШМАР", "страшный сон 😱"),
    ("РУЛЕТКА", "игра с удачей 🎰"),
    ("МАФИЯ", "тайная организация 🔫"),
    ("ВИСЕЛИЦА", "игра с буквами ✏️"),
    ("ПРАВДА", "истина 🗣"),
    ("ДЕЙСТВИЕ", "поступок 💪"),
    ("ПОБЕДА", "результат борьбы 🏆"),
    ("ТЕЛЕФОН", "устройство связи 📱"),
    ("ТАЙНА", "то что скрывают 🔐"),
    ("УЖАС", "сильный страх 👁"),
]

# ── Быстрый счётчик (дуэль) ──────────────────────────────────
def start_duel(chat_id: int, challenger_uid: int, defender_uid: int):
    """Дуэль между двумя игроками — кто быстрее напишет 'бах'."""
    c_name = users.get(challenger_uid, {}).get("name") or f"ID:{challenger_uid}"
    d_name = users.get(defender_uid, {}).get("name") or f"ID:{defender_uid}"
    _group_games[chat_id] = {
        "game": "duel",
        "challenger": challenger_uid,
        "defender": defender_uid,
        "c_name": c_name,
        "d_name": d_name,
        "ready": set(),
        "started": False,
        "winner": None,
    }
    kb = InlineKeyboardMarkup()
    kb.add(
        InlineKeyboardButton(f"✅ {c_name} готов", callback_data=f"duel_ready_{chat_id}_{challenger_uid}"),
        InlineKeyboardButton(f"✅ {d_name} готов", callback_data=f"duel_ready_{chat_id}_{defender_uid}"),
    )
    send_group(chat_id,
        f"⚔️ ДУЭЛЬ!\n\n"
        f"🔴 {c_name} vs 🔵 {d_name}\n\n"
        f"Когда оба готовы — получите сигнал.\n"
        f"Кто первый напишет «БАХ» — победит!", kb=kb)

def _duel_start(chat_id: int):
    """Запускает дуэль после подтверждения готовности."""
    g = _group_games.get(chat_id)
    if not g or g.get("game") != "duel":
        return
    g["started"] = True
    def _run():
        time.sleep(random.uniform(2, 6))
        if _group_games.get(chat_id, {}).get("game") == "duel":
            send_group(chat_id, "🔫 ОГОНЬ! Пишите «БАХ»!")
    _pool.submit(_run)

# ══════════════════════════════════════════════════════════════
#  ОБНОВЛЁННЫЕ ФУНКЦИИ ГРУППЫ
# ══════════════════════════════════════════════════════════════

def group_reply_kb():
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=3)
    k.add(
        KeyboardButton("🎮 Игры"),
        KeyboardButton("🤖 Спросить ИИ"),
        KeyboardButton("🏆 Рейтинг"),
    )
    k.add(
        KeyboardButton("🌤 Погода"),
        KeyboardButton("🌍 Перевести"),
        KeyboardButton("❓ Помощь"),
    )
    return k


def group_game_kb(chat_id):
    """InlineKeyboard для выбора игры в группе."""
    k = InlineKeyboardMarkup(row_width=2)
    k.add(
        InlineKeyboardButton("🍾 Бутылочка",       callback_data=f"gg_bottle_{chat_id}"),
        InlineKeyboardButton("🪙 Монетка",         callback_data=f"gg_coin_{chat_id}"),
        InlineKeyboardButton("🎲 Кубик",           callback_data=f"gg_dice_{chat_id}"),
        InlineKeyboardButton("🔫 Рулетка",         callback_data=f"gg_roulette_{chat_id}"),
        InlineKeyboardButton("🎭 Правда/Действие", callback_data=f"gg_tod_{chat_id}"),
        InlineKeyboardButton("⚖️ Что лучше?",      callback_data=f"gg_wr_{chat_id}"),
        InlineKeyboardButton("🔥 Кто в группе?",   callback_data=f"gg_hottake_{chat_id}"),
        InlineKeyboardButton("🧠 Викторина",       callback_data=f"gg_trivia_{chat_id}"),
        InlineKeyboardButton("🎲 Угадай число",    callback_data=f"gg_number_{chat_id}"),
        InlineKeyboardButton("✏️ Виселица",        callback_data=f"gg_hangman_{chat_id}"),
        InlineKeyboardButton("🔫 Мафия",           callback_data=f"gg_mafia_{chat_id}"),
        InlineKeyboardButton("🗡 RPG",             callback_data=f"gg_rpg_{chat_id}"),
        InlineKeyboardButton("❌ Стоп",            callback_data=f"gg_stop_{chat_id}"),
    )
    return k

def start_group_game_number(chat_id):
    number = random.randint(1, 100)
    _group_games[chat_id] = {"game": "number", "number": number, "attempts": 10, "winner": None}
    send_group(chat_id,
        "🎲 ГРУППОВАЯ ИГРА: Угадай число!\n\n"
        "Загадано число от 1 до 100.\n"
        "У всех вместе 10 попыток.\n"
        "Кто угадает — победит!\n\nВводите числа:")

def start_group_game_hangman(chat_id):
    word, hint = random.choice(HANGMAN_W)
    _group_games[chat_id] = {
        "game": "hangman", "word": word, "hint": hint,
        "guessed": set(), "attempts": 8, "winners": []
    }
    send_group(chat_id,
        f"✏️ ГРУППОВАЯ ВИСЕЛИЦА!\n\n"
        f"Подсказка: {hint}\n\n"
        f"{' '.join('_' for _ in word)}\n\n"
        f"Попыток: 8\nВводите буквы по одной!")

def start_group_game_trivia(chat_id):
    q, ans, opts = random.choice(TRIVIA_Q)
    sh = opts[:]; random.shuffle(sh)
    _group_games[chat_id] = {"game": "trivia", "answer": ans.lower(), "answered": set()}
    kk = InlineKeyboardMarkup(row_width=2)
    for o in sh:
        kk.add(InlineKeyboardButton(o, callback_data=f"trivia_{chat_id}_{o[:30]}"))
    kk.add(InlineKeyboardButton("❌ Стоп", callback_data=f"gg_stop_{chat_id}"))
    send_group(chat_id, f"🧠 ГРУППОВАЯ ВИКТОРИНА!\n\n{q}\n\nКто первый ответит правильно?", kb=kk)

# ══════════════════════════════════════════════════════════════
#  v13: ГРУППОВАЯ МАФИЯ
# ══════════════════════════════════════════════════════════════

MAFIA_ROLES = {
    "мафия":      "🔫 МАФИЯ\n\nТы — мафия. Убивай мирных жителей ночью.\nНикому не раскрывай свою роль!",
    "мирный":     "👤 МИРНЫЙ ЖИТЕЛЬ\n\nТы — обычный житель.\nДнём голосуй против мафии.",
    "шериф":      "🔎 ШЕРИФ\n\nТы — шериф. Каждую ночь проверяй одного игрока.\nЯ скажу тебе: мафия или мирный.",
    "доктор":     "🏥 ДОКТОР\n\nТы — доктор. Каждую ночь спасай одного игрока.\nТы можешь спасти себя один раз.",
}

def _mafia_assign_roles(players):
    """Распределяет роли по числу игроков."""
    n = len(players)
    roles = {}
    if n < 4:
        return None  # мало игроков
    # 1 мафия на 3-4 игроков, 2 на 5+, 3 на 8+
    mafia_count = max(1, n // 4)
    mafia_players = random.sample(players, mafia_count)
    remaining = [p for p in players if p not in mafia_players]
    random.shuffle(remaining)
    for p in mafia_players:
        roles[p] = "мафия"
    # Шериф и доктор если достаточно игроков
    idx = 0
    if len(remaining) >= 1:
        roles[remaining[idx]] = "шериф"; idx += 1
    if len(remaining) >= 2:
        roles[remaining[idx]] = "доктор"; idx += 1
    for p in remaining[idx:]:
        roles[p] = "мирный"
    return roles

def start_group_mafia(chat_id):
    """Запускает регистрацию в мафию для группы."""
    if chat_id in _group_games:
        send_group(chat_id, "⚠️ Сначала заверши текущую игру.")
        return
    if chat_id in _group_mafia and _group_mafia[chat_id].get("state") == "playing":
        send_group(chat_id, "⚠️ Игра в мафию уже идёт!")
        return
    _group_mafia[chat_id] = {
        "state": "lobby",
        "players": [],
        "player_names": {},
        "roles": {},
        "alive": [],
        "phase": "day",
        "votes": {},
        "night_actions": {},
        "mafia_target": None,
        "day_num": 0,
        "voted_today": set(),  # кто уже голосовал сегодня
    }
    kb = InlineKeyboardMarkup(row_width=1)
    kb.add(
        InlineKeyboardButton("✅ Участвую", callback_data=f"mj_{chat_id}"),
        InlineKeyboardButton("▶️ Начать игру (минимум 4)", callback_data=f"ms_{chat_id}"),
        InlineKeyboardButton("❌ Отменить лобби", callback_data=f"mc_{chat_id}"),
    )
    send_group(chat_id,
        "🔫 МАФИЯ!\n\n"
        "Минимум 4 игрока. Нажмите «Участвую».\n"
        "Когда все готовы — нажмите «Начать игру».\n\n"
        "Роли: 👤 Мирный, 🔫 Мафия, 🔎 Шериф, 🏥 Доктор",
        kb=kb)

def _mafia_start_game(chat_id):
    """Начинает игру в мафию после набора игроков."""
    g = _group_mafia.get(chat_id)
    if not g:
        return
    players = g["players"]
    if len(players) < 4:
        send_group(chat_id, "❌ Нужно минимум 4 игрока!")
        return
    roles = _mafia_assign_roles(players)
    if not roles:
        send_group(chat_id, "❌ Ошибка распределения ролей.")
        return
    g["roles"] = roles
    g["alive"] = list(players)
    g["state"] = "playing"
    g["phase"] = "day"
    g["day_num"] = 1
    g["chat_id"] = chat_id  # сохраняем chat_id в состоянии игры
    g["voted_today"] = set()
    # Отправляем каждому роль в ЛС
    for uid, role in roles.items():
        name = g["player_names"].get(uid, f"ID:{uid}")
        try:
            _safe_call(bot.send_message, uid, f"🎭 МАФИЯ в группе начинается!\n\n{MAFIA_ROLES[role]}\n\nИгроков: {len(players)}")
        except Exception:
            pass
    # Список игроков
    names_list = "\n".join(f"  {g['player_names'].get(p, p)}" for p in players)
    send_group(chat_id,
        f"🎮 МАФИЯ НАЧИНАЕТСЯ!\n\nИгроки ({len(players)}):\n{names_list}\n\n"
        f"☀️ ДЕНЬ 1\n\nОбсуждайте кто мафия!\nГолосуйте нажав на имя игрока:",
        kb=_mafia_day_kb(g, chat_id))

def _mafia_day_kb(g, chat_id):
    """InlineKeyboard для голосования днём в группе."""
    k = InlineKeyboardMarkup(row_width=2)
    buttons = []
    for uid in g["alive"]:
        name = g["player_names"].get(uid, f"ID:{uid}")
        buttons.append(InlineKeyboardButton(f"⚖️ {name}", callback_data=f"mv_{chat_id}_{uid}"))
    k.add(*buttons)
    k.add(InlineKeyboardButton("🏁 Подсчитать голоса", callback_data=f"mcount_{chat_id}"))
    return k

def _mafia_night_kb(g, uid):
    """InlineKeyboard для ночных действий (отправляется в ЛС).
    ИСПРАВЛЕНО: callback_data не содержит target_uid открыто — используем индекс.
    """
    k = InlineKeyboardMarkup(row_width=2)
    role = g["roles"].get(uid)
    buttons = []
    chat_id = g.get("chat_id", 0)
    for idx, target in enumerate(g["alive"]):
        if target == uid and role != "доктор":
            continue
        name = g["player_names"].get(target, f"ID:{target}")
        # Используем индекс в списке alive вместо uid — не раскрываем uid в callback
        buttons.append(InlineKeyboardButton(f"🎯 {name}", callback_data=f"mnight_{chat_id}_{uid}_{target}"))
    if buttons:
        k.add(*buttons)
    return k

def _mafia_check_win(chat_id):
    """Проверяет условие победы. Возвращает 'мафия', 'мирные' или None."""
    g = _group_mafia.get(chat_id)
    if not g:
        return None
    alive = g["alive"]
    mafia_alive = [p for p in alive if g["roles"].get(p) == "мафия"]
    peaceful_alive = [p for p in alive if g["roles"].get(p) != "мафия"]
    if not mafia_alive:
        return "мирные"
    if len(mafia_alive) >= len(peaceful_alive):
        return "мафия"
    return None

def _mafia_end(chat_id, winner):
    g = _group_mafia.pop(chat_id, None)
    if not g:
        return
    roles_reveal = "\n".join(
        f"  {g['player_names'].get(uid,'?')} — {role}"
        for uid, role in g["roles"].items()
    )
    if winner == "мирные":
        msg = "🎉 МИРНЫЕ ЖИТЕЛИ ПОБЕДИЛИ!\n\nМафия разоблачена!\n\nРоли:\n" + roles_reveal
    else:
        msg = "🔫 МАФИЯ ПОБЕДИЛА!\n\nМафия захватила город!\n\nРоли:\n" + roles_reveal
    send_group(chat_id, msg, kb=group_reply_kb())

def proc_group_mafia(chat_id, uid, text, uname):
    """Обрабатывает ход в мафию в группе. True если обработано."""
    g = _group_mafia.get(chat_id)
    if not g:
        return False
    if uid not in g.get("alive", []) and uid not in g.get("players", []):
        return False

    if g.get("state") == "lobby":
        return False  # обрабатывается через callback

    # Текстовые ходы больше не нужны — всё через InlineKeyboard
    # Но оставим обработку /vote для совместимости
    if text.startswith("/vote "):
        target_name = text[6:].strip().lstrip("@")
        target_uid = None
        for p in g["alive"]:
            if g["player_names"].get(p, "").lower() == target_name.lower():
                target_uid = p; break
        if not target_uid:
            send_group(chat_id, f"❓ Игрок «{target_name}» не найден.")
            return True
        if uid == target_uid:
            # Личное уведомление, не публично
            try: bot.send_message(uid, "⚠️ Нельзя голосовать за себя!")
            except Exception: pass
            return True
        voted_today = g.setdefault("voted_today", set())
        if uid in voted_today:
            try: bot.send_message(uid, "Ты уже проголосовал сегодня!")
            except Exception: pass
            return True
        voted_name = g["player_names"].get(target_uid, "?")
        g["votes"][uid] = target_uid
        voted_today.add(uid)
        # ИСПРАВЛЕНО: не раскрываем кто за кого проголосовал
        voted_count = len(g["votes"])
        total_alive = len(g["alive"])
        try: bot.send_message(uid, f"✅ Голос принят (анонимно).")
        except Exception: pass
        send_group(chat_id, f"🗳 Проголосовало: {voted_count}/{total_alive}")
        return True

    return False

# ══════════════════════════════════════════════════════════════

# ══════════════════════════════════════════════════════════════
#  v13: МАФИЯ В ЛИЧНЫХ СООБЩЕНИЯХ (между обычными пользователями)
# ══════════════════════════════════════════════════════════════

_mafia_lobby_counter = [0]

def create_mafia_lobby(creator_uid):
    """Создаёт лобби мафии. Возвращает lobby_id."""
    _mafia_lobby_counter[0] += 1
    lobby_id = _mafia_lobby_counter[0]
    u = U(creator_uid)
    creator_name = u.get("name") or f"ID:{creator_uid}"
    _mafia_lobby[lobby_id] = {
        "creator": creator_uid,
        "players": [creator_uid],
        "player_names": {creator_uid: creator_name},
        "state": "lobby",
        "roles": {},
        "alive": [],
        "phase": "day",
        "votes": {},
        "night_actions": {},
        "day_num": 0,
        "chat": None,  # групповой чат если запущено из группы
    }
    _mafia_player[creator_uid] = lobby_id
    return lobby_id

def join_mafia_lobby(uid, lobby_id):
    """Добавляет игрока в лобби. Возвращает True при успехе."""
    g = _mafia_lobby.get(lobby_id)
    if not g:
        return False, "Лобби не найдено."
    if g["state"] != "lobby":
        return False, "Игра уже началась."
    if uid in g["players"]:
        return False, "Ты уже в лобби."
    if len(g["players"]) >= 10:
        return False, "Лобби заполнено (макс. 10)."
    u = U(uid)
    name = u.get("name") or f"ID:{uid}"
    g["players"].append(uid)
    g["player_names"][uid] = name
    _mafia_player[uid] = lobby_id
    return True, f"✅ {name} вступил в лобби #{lobby_id}!"

def start_mafia_dm(lobby_id):
    """Запускает игру в мафию через ЛС."""
    g = _mafia_lobby.get(lobby_id)
    if not g:
        return
    players = g["players"]
    if len(players) < 4:
        for uid in players:
            send(uid, "❌ Нужно минимум 4 игрока для мафии!")
        return
    roles = _mafia_assign_roles(players)
    g["roles"] = roles
    g["alive"] = list(players)
    g["state"] = "playing"
    g["phase"] = "day"
    g["day_num"] = 1
    # Рассылаем роли
    for uid, role in roles.items():
        name = g["player_names"].get(uid, f"ID:{uid}")
        send(uid, f"🎭 МАФИЯ!\nИгроков: {len(players)}\n\n{MAFIA_ROLES[role]}")
    # Начало дня 1
    _mafia_announce_day(lobby_id)

def _mafia_announce_day(lobby_id):
    g = _mafia_lobby.get(lobby_id)
    if not g:
        return
    alive_names = "\n".join(f"  {g['player_names'].get(p,'?')}" for p in g["alive"])
    # ИСПРАВЛЕНО: используем InlineKeyboard для голосования вместо текстового ввода
    kb_day = InlineKeyboardMarkup(row_width=1)
    for p in g["alive"]:
        pname = g["player_names"].get(p, "?")
        kb_day.add(InlineKeyboardButton(
            f"⚖️ Устранить: {pname}",
            callback_data=f"mdmv_{lobby_id}_{p}"
        ))
    kb_day.add(InlineKeyboardButton("⏭ Пропустить голосование", callback_data=f"mdmvskip_{lobby_id}"))
    day_text = (
        f"☀️ ДЕНЬ {g['day_num']}\n\n"
        f"Живые игроки:\n{alive_names}\n\n"
        f"Выбери кого устранить:"
    )
    for uid in g["alive"]:
        try:
            bot.send_message(uid, day_text, reply_markup=kb_day)
        except Exception:
            pass

def _mafia_announce_night(lobby_id):
    g = _mafia_lobby.get(lobby_id)
    if not g:
        return
    g["phase"] = "night"
    g["night_actions"] = {}
    # Уведомляем всех
    for uid in g["alive"]:
        role = g["roles"].get(uid)
        if role == "мирный":
            send(uid, "🌙 НОЧЬ\n\nТы мирный житель. Жди пока проснёшься...")
        elif role in ("мафия", "шериф", "доктор"):
            # ИСПРАВЛЕНО: отправляем InlineKeyboard для выбора цели вместо текстового ввода
            targets = []
            for p in g["alive"]:
                if role != "доктор" and p == uid:
                    continue
                targets.append(p)
            action_label = {"мафия": "Убить", "шериф": "Проверить", "доктор": "Вылечить"}[role]
            kb_night = InlineKeyboardMarkup(row_width=1)
            for p in targets:
                pname = g["player_names"].get(p, "?")
                kb_night.add(InlineKeyboardButton(
                    f"🎯 {action_label}: {pname}",
                    callback_data=f"mdm_{lobby_id}_{uid}_{p}"
                ))
            action_desc = {"мафия": "кого убить", "шериф": "кого проверить", "доктор": "кого вылечить"}[role]
            try:
                bot.send_message(uid,
                    f"🌙 НОЧЬ — ТЫ {role.upper()}\n\nВыбери {action_desc}:",
                    reply_markup=kb_night)
            except Exception:
                pass

def proc_mafia_dm(uid, text):
    """Обрабатывает ход мафии в ЛС. True если обработано."""
    lobby_id = _mafia_player.get(uid)
    if not lobby_id:
        return False
    g = _mafia_lobby.get(lobby_id)
    if not g or g.get("state") != "playing":
        return False

    tl = text.strip().lower()

    if tl in ("выйти", "/stop_mafia", "стоп мафия"):
        del _mafia_player[uid]
        g["alive"] = [p for p in g["alive"] if p != uid]
        g["players"] = [p for p in g["players"] if p != uid]
        send(uid, "Ты вышел из игры мафия.")
        for p in g["players"]:
            if p != uid:
                send(p, f"⚠️ {g['player_names'].get(uid,'?')} вышел из игры.")
        if len(g["alive"]) < 3:
            for p in g["players"]:
                send(p, "Игра завершена — недостаточно игроков.")
            _end_mafia_dm(lobby_id, "мирные")
        return True

    phase = g.get("phase", "day")

    if phase == "day":
        if tl == "пропустить":
            send(uid, "⏭ Ты пропустил голосование.")
            g["votes"][uid] = None
            _check_mafia_day_votes(lobby_id)
            return True
        # Ищем цель по имени
        target = _find_mafia_player_by_name(g, tl, exclude=uid)
        if target:
            g["votes"][uid] = target
            voted_name = g["player_names"].get(target, "?")
            send(uid, f"⚖️ Твой голос: {voted_name}")
            _check_mafia_day_votes(lobby_id)
            return True
        send(uid, "❓ Игрок не найден. Напиши имя из списка живых.")
        return True

    elif phase == "night":
        role = g["roles"].get(uid)
        if role == "мирный":
            send(uid, "🌙 Ночь. Жди...")
            return True
        # Ищем цель
        target = _find_mafia_player_by_name(g, tl, exclude=(uid if role != "доктор" else None))
        if not target:
            send(uid, "❓ Игрок не найден.")
            return True
        g["night_actions"][uid] = target
        target_name = g["player_names"].get(target, "?")
        action_word = {"мафия":"убить","шериф":"проверить","доктор":"вылечить"}.get(role,"?")
        send(uid, f"✅ Действие принято: {action_word} {target_name}")
        _check_mafia_night_actions(lobby_id)
        return True

    return False

def _find_mafia_player_by_name(g, name_query, exclude=None):
    """Ищет uid игрока по части имени."""
    for p in g["alive"]:
        if p == exclude:
            continue
        pname = g["player_names"].get(p, "").lower()
        if name_query in pname or pname in name_query:
            return p
    return None

def _check_mafia_day_votes(lobby_id):
    """Проверяет набрали ли все живые голоса."""
    g = _mafia_lobby.get(lobby_id)
    if not g:
        return
    voted = set(g["votes"].keys())
    alive = set(g["alive"])
    if not alive.issubset(voted):
        return  # ждём остальных
    # Подводим итог
    count = {}
    for v in g["votes"].values():
        if v:
            count[v] = count.get(v, 0) + 1
    if not count:
        for uid in g["alive"]:
            send(uid, "☀️ Голосование: единогласно никого не устранили.")
    else:
        eliminated = max(count, key=count.get)
        elim_name = g["player_names"].get(eliminated, "?")
        elim_role = g["roles"].get(eliminated, "?")
        g["alive"].remove(eliminated)
        role_txt = MAFIA_ROLES.get(elim_role, "?").split("\n")[0]
        for uid in g["alive"] + [eliminated]:
            try:
                send(uid, f"⚖️ Устранён: {elim_name}\nРоль: {role_txt}")
            except Exception:
                pass
    g["votes"] = {}
    winner = _check_mafia_dm_win(lobby_id)
    if winner:
        _end_mafia_dm(lobby_id, winner); return
    g["day_num"] += 1
    _mafia_announce_night(lobby_id)

def _check_mafia_night_actions(lobby_id):
    """Ждёт пока все ночные роли сделают ход."""
    g = _mafia_lobby.get(lobby_id)
    if not g:
        return
    night_roles = [p for p in g["alive"] if g["roles"].get(p) in ("мафия","шериф","доктор")]
    acted = set(g["night_actions"].keys())
    if not all(p in acted for p in night_roles):
        return  # ждём
    # Применяем ночные действия
    saved_by_doctor = None
    mafia_target = None
    sheriff_info = []
    for uid, target in g["night_actions"].items():
        role = g["roles"].get(uid)
        if role == "мафия":
            mafia_target = target
        elif role == "доктор":
            saved_by_doctor = target
        elif role == "шериф":
            target_role = g["roles"].get(target, "?")
            is_mafia = (target_role == "мафия")
            target_name = g["player_names"].get(target, "?")
            send(uid, f"🔎 Результат проверки {target_name}: {'🔫 МАФИЯ!' if is_mafia else '👤 мирный'}")
    # Применяем убийство
    if mafia_target and mafia_target != saved_by_doctor:
        victim_name = g["player_names"].get(mafia_target, "?")
        victim_role = g["roles"].get(mafia_target, "?")
        g["alive"] = [p for p in g["alive"] if p != mafia_target]
        role_txt = MAFIA_ROLES.get(victim_role, "?").split("\n")[0]
        for uid in g["alive"] + [mafia_target]:
            try:
                send(uid, f"☀️ УТРО\n\nНочью убит: {victim_name}\nРоль: {role_txt}")
            except Exception:
                pass
    elif mafia_target == saved_by_doctor:
        saved_name = g["player_names"].get(saved_by_doctor, "?")
        for uid in g["alive"]:
            send(uid, f"☀️ УТРО\n\nДоктор спас {saved_name}! Никто не погиб.")
    else:
        for uid in g["alive"]:
            send(uid, "☀️ УТРО\n\nНикто не погиб.")
    g["night_actions"] = {}
    winner = _check_mafia_dm_win(lobby_id)
    if winner:
        _end_mafia_dm(lobby_id, winner); return
    _mafia_announce_day(lobby_id)

def _check_mafia_dm_win(lobby_id):
    g = _mafia_lobby.get(lobby_id)
    if not g:
        return None
    alive = g["alive"]
    mafia_alive = [p for p in alive if g["roles"].get(p) == "мафия"]
    peaceful_alive = [p for p in alive if g["roles"].get(p) != "мафия"]
    if not mafia_alive:
        return "мирные"
    if len(mafia_alive) >= len(peaceful_alive):
        return "мафия"
    return None

def _end_mafia_dm(lobby_id, winner):
    g = _mafia_lobby.pop(lobby_id, None)
    if not g:
        return
    roles_reveal = "\n".join(
        f"  {g['player_names'].get(uid,'?')} — {role}"
        for uid, role in g["roles"].items()
    )
    if winner == "мирные":
        result = "🎉 МИРНЫЕ ПОБЕДИЛИ!\n\n"
    else:
        result = "🔫 МАФИЯ ПОБЕДИЛА!\n\n"
    for uid in g["players"]:
        _mafia_player.pop(uid, None)
        u = U(uid)
        try:
            send(uid, result + "Роли:\n" + roles_reveal, kb=KB(u.get("stage", 0)))
        except Exception:
            pass

# ══════════════════════════════════════════════════════════════
#  v13: КАРТОЧНАЯ ИСТОРИЯ (visual-novel style с выбором персонажа)
# ══════════════════════════════════════════════════════════════

CARD_CHARACTERS = {
    "детектив": {
        "name": "🔎 Детектив",
        "desc": "Ты — опытный детектив. Острый ум, холодный расчёт.\n+бонус к расследованию, -1 к боевым ситуациям",
        "bonus": "invest",
    },
    "выживший": {
        "name": "🧠 Выживший",
        "desc": "Ты — выживший. Ты уже видел ужас.\n+бонус к побегу, +1 к смелости",
        "bonus": "escape",
    },
    "учёный": {
        "name": "🔬 Учёный",
        "desc": "Ты — учёный. Рациональный ум.\n+бонус к пониманию аномалий, -боюсь темноты",
        "bonus": "science",
    },
    "призрак": {
        "name": "👻 Призрак",
        "desc": "Ты — призрак. Уже мёртвый. Помогаешь живым.\n+видишь скрытое, нельзя умереть снова",
        "bonus": "ghost",
    },
    "охотник": {
        "name": "⚔️ Охотник на нечисть",
        "desc": "Ты — охотник. Специальное оружие, опыт.\n+бонус в битвах, -1 к дипломатии",
        "bonus": "hunter",
    },
}

CARD_STORIES = {
    "особняк": {
        "title": "🏚 ОСОБНЯК",
        "scenes": {
            "start": {
                "text": "Вы оказались в старом особняке.\nДвери заперты. За окнами — туман.\n\nВпереди — три коридора.",
                "choices": [
                    ("🕯 Идти налево", "hall_left"),
                    ("🪞 Идти направо (зеркальный зал)", "hall_right"),
                    ("🔑 Найти ключ (подвал)", "basement"),
                ],
                "bonus_choice": {
                    "invest": ("🔍 Осмотреть замок детально", "detective_lock"),
                    "ghost": ("👻 Почувствовать присутствие", "ghost_sense"),
                }
            },
            "hall_left": {
                "text": "Тёмный коридор.\nНа полу — кровавые следы.\nВпереди — скрип.",
                "choices": [("🏃 Бежать", "run_escape"), ("🔦 Исследовать", "library"), ("😶 Замереть", "freeze_end")],
            },
            "hall_right": {
                "text": "Зеркальный зал.\nДесятки отражений.\nОдно из них не движется.",
                "choices": [("👁 Смотреть", "mirror_horror"), ("🏃 Уйти", "hall_left"), ("💬 Говорить", "mirror_talk")],
                "bonus_choice": {"ghost": ("👻 Поговорить с отражением-призраком", "ghost_mirror")}
            },
            "basement": {
                "text": "Подвал.\nПахнет землёй и старым деревом.\nНа столе — дневник.",
                "choices": [("📖 Читать", "diary"), ("🔑 Найти ключ", "key_found"), ("🏃 Назад", "start")],
                "bonus_choice": {
                    "invest": ("🔍 Снять отпечатки пальцев", "fingerprints"),
                    "science": ("🔬 Исследовать образцы", "science_analyze"),
                }
            },
            "library": {
                "text": "Библиотека.\nКниги написаны неизвестными символами.\nОдна — открытая.",
                "choices": [("📖 Читать книгу", "book_truth"), ("🔑 Найти выход", "key_found"), ("🏃 Бежать", "run_escape")],
                "bonus_choice": {"science": ("🔬 Расшифровать символы", "science_decode")}
            },
            "diary": {
                "text": "В дневнике — записи хозяина.\n«Они приходят каждую ночь».\n«Я слышу их за стенами».\nПоследняя страница вырвана.",
                "choices": [("🔑 Найти ключ", "key_found"), ("📖 Книга (библиотека)", "library"), ("🚪 Выход", "run_escape")],
            },
            "mirror_horror": {
                "text": "Неподвижное отражение поворачивает голову.\nОно смотрит на тебя.\nОно улыбается.",
                "choices": [("💥 Разбить зеркало", "mirror_break"), ("🏃 Бежать", "hall_left"), ("👁 Продолжать смотреть", "mirror_stare_deep")],
            },
            "mirror_talk": {
                "text": "«Помоги нам».\nГолос идёт из зеркала.\n«Мы застряли».\n«Нас здесь много».",
                "choices": [("❓ Как помочь?", "mirror_help"), ("🏃 Уйти", "hall_left")],
            },
            "mirror_break": {
                "text": "Зеркало разбито.\nОсколки светятся.\nВ каждом — лицо.\nОни все смотрят на тебя.",
                "choices": [("🔑 Ключ в осколках", "key_found"), ("🏃 Бежать", "run_escape")],
            },
            "mirror_stare_deep": {
                "text": "Ты смотришь дольше.\nОтражение говорит:\n«Ты уже был здесь».\n«Ты никогда не уходил».",
                "choices": [("🔄 Начать заново", "start")], "end": True,
            },
            "mirror_help": {
                "text": "«Выход — там где нет отражений».\nТы замечаешь угол без зеркала.\nТам — дверь.",
                "choices": [("🚪 Открыть дверь", "mansion_escape")],
            },
            "mirror_talk_ghost": {
                "text": "(Только призрак видит) Отражения — это застрявшие души.\nОни указывают путь.",
                "choices": [("👻 Следовать за душами", "mansion_escape"), ("🏃 Уйти", "start")],
            },
            "ghost_sense": {
                "text": "👻 Ты чувствуешь — здесь много душ.\nОни тянутся к тебе.\nОдна — указывает налево.",
                "choices": [("👁 Следовать", "ghost_path"), ("🏃 Идти своим путём", "start")],
            },
            "ghost_path": {
                "text": "Душа ведёт тебя к потайной двери.\nЗа ней — выход.",
                "choices": [("🚪 Выйти", "mansion_escape")],
            },
            "ghost_mirror": {
                "text": "Призрак в зеркале — знакомый.\nОн говорит: «Подвал. Третья плита».",
                "choices": [("⬇️ В подвал", "basement_secret")],
            },
            "basement_secret": {
                "text": "Третья плита. Ты поднимаешь её.\nЗа ней — выход на улицу.",
                "choices": [("🚪 Выйти", "mansion_escape")],
            },
            "detective_lock": {
                "text": "🔎 Замок вскрыт снаружи. Кто-то заманил вас.\nПо следам: 3 человека. Ушли 2 часа назад.",
                "choices": [("🔍 Искать их", "hall_left"), ("🔑 Найти запасной выход", "basement")],
            },
            "fingerprints": {
                "text": "🔎 Отпечатки совпадают с хозяином дома.\nОн всё ещё здесь.",
                "choices": [("😱 Найти хозяина", "mansion_owner"), ("🏃 Бежать", "run_escape")],
            },
            "mansion_owner": {
                "text": "В тёмном углу — старик.\n«Вы нашли выход?»\n«Я ищу уже 40 лет».",
                "choices": [("🤝 Помочь ему", "mansion_escape"), ("🏃 Бежать одному", "run_escape")],
            },
            "science_analyze": {
                "text": "🔬 В образцах — органические клетки.\nНо странные. Не человеческие.\nТемпература — ниже нуля.",
                "choices": [("🔬 Исследовать далее", "science_decode"), ("🏃 Бежать", "run_escape")],
            },
            "science_decode": {
                "text": "🔬 Символы расшифрованы.\nЭто карта особняка.\nВыход — под лестницей.",
                "choices": [("🚪 К лестнице", "mansion_escape")],
            },
            "key_found": {
                "text": "🔑 Ключ найден!\nТяжёлый, старый.\nПодходит к главным дверям.",
                "choices": [("🚪 Открыть двери", "mansion_escape"), ("👁 Осмотреться ещё", "start")],
            },
            "book_truth": {
                "text": "В книге — правда.\nОсобняк — живой.\nОн питается теми кто ищет выход.",
                "choices": [("🏃 Бежать", "run_escape"), ("⚔️ Сразиться", "fight_mansion")],
                "bonus_choice": {"hunter": ("⚔️ Применить специальное оружие", "hunter_win")}
            },
            "fight_mansion": {
                "text": "Ты атакуешь тьму.\nТьма не отступает.\nНо находится трещина в стене.",
                "choices": [("🚪 В трещину", "mansion_escape"), ("⚔️ Продолжать бой", "freeze_end")],
            },
            "hunter_win": {
                "text": "⚔️ Специальное оружие работает!\nОсобняк содрогается.\nВыход открывается сам.",
                "choices": [("🚪 Выйти", "mansion_escape")],
            },
            "freeze_end": {
                "text": "Ты не двигаешься.\n...\nУтром тебя находят у входа.\nТы смотришь в одну точку. 👁",
                "choices": [("🔄 Сыграть снова", "start")], "end": True,
            },
            "run_escape": {
                "text": "Ты бежишь.\nДвери оказываются незаперты.\nТы на улице.\n\nНо особняк за тобой исчез.\nА в кармане — ключ.\nОткуда он?",
                "choices": [("🔄 Сыграть снова", "start")], "end": True,
            },
            "mansion_escape": {
                "text": "🌅 Ты выбрался из особняка!\n\nНа улице — рассвет.\nТелефон разряжен.\nВ галерее — фото.\nТы их не делал.\n\n👁 КОНЕЦ",
                "choices": [("🔄 Сыграть снова", "start")], "end": True,
            },
        }
    }
}

def start_card_story(uid, story_id="особняк"):
    """Запускает карточную историю — сначала выбор персонажа."""
    _card_story[uid] = {"story_id": story_id, "scene": None, "character": None}
    kb = ReplyKeyboardMarkup(resize_keyboard=True, row_width=1)
    for char_id, char_data in CARD_CHARACTERS.items():
        kb.add(KeyboardButton(f"🃏 {char_data['name'].split()[1]}"))
    send(uid,
        "🎭 КАРТОЧНАЯ ИСТОРИЯ\n\n"
        "Выбери персонажа — это повлияет на историю!\n\n" +
        "\n\n".join(f"{d['name']}\n{d['desc']}" for d in CARD_CHARACTERS.values()),
        kb=kb)

def proc_card_story(uid, text):
    """Обрабатывает карточную историю. True если обработано."""
    cs = _card_story.get(uid)
    if not cs:
        return False
    u = U(uid)
    kb = KB(u.get("stage", 0))

    # Выбор персонажа
    if cs["character"] is None:
        for char_id, char_data in CARD_CHARACTERS.items():
            char_short = char_data["name"].split()[1]
            if text == f"🃏 {char_short}" or text.lower() == char_id:
                cs["character"] = char_id
                cs["scene"] = "start"
                char_info = CARD_CHARACTERS[char_id]
                send(uid, f"✅ Выбран: {char_info['name']}\n\n{char_info['desc']}")
                _render_card_scene(uid)
                return True
        return False

    story = CARD_STORIES.get(cs["story_id"])
    if not story:
        del _card_story[uid]; return False

    scene_key = cs.get("scene", "start")
    scene = story["scenes"].get(scene_key, {})
    char_bonus = CARD_CHARACTERS.get(cs["character"], {}).get("bonus", "")

    # Проверяем бонусный выбор
    bonus_choices = scene.get("bonus_choice", {})
    if char_bonus in bonus_choices:
        bonus_label, bonus_dest = bonus_choices[char_bonus]
        if text == bonus_label:
            next_scene = story["scenes"].get(bonus_dest)
            if next_scene:
                cs["scene"] = bonus_dest
                _render_card_scene(uid)
                if next_scene.get("end"):
                    del _card_story[uid]
                return True

    # Обычный выбор
    for label, dest in scene.get("choices", []):
        if text == label:
            next_scene = story["scenes"].get(dest)
            if next_scene:
                cs["scene"] = dest
                _render_card_scene(uid)
                if next_scene.get("end"):
                    del _card_story[uid]
            else:
                cs["scene"] = "start"
                _render_card_scene(uid)
            return True

    # Перепоказываем сцену при неправильном вводе
    _render_card_scene(uid)
    return True

def _render_card_scene(uid):
    """Отрисовывает текущую сцену карточной истории."""
    cs = _card_story.get(uid)
    if not cs:
        return
    story = CARD_STORIES.get(cs["story_id"])
    if not story:
        return
    scene = story["scenes"].get(cs.get("scene", "start"), {})
    char_bonus = CARD_CHARACTERS.get(cs.get("character",""), {}).get("bonus", "")
    char_name = CARD_CHARACTERS.get(cs.get("character",""), {}).get("name", "")

    all_choices = list(scene.get("choices", []))
    bonus_choices = scene.get("bonus_choice", {})
    bonus_label = None
    if char_bonus in bonus_choices:
        bonus_label, _ = bonus_choices[char_bonus]
        all_choices = list(all_choices) + [(bonus_label, None)]

    kb = ReplyKeyboardMarkup(resize_keyboard=True, row_width=1)
    for label, _ in all_choices:
        kb.add(KeyboardButton(label))
    kb.add(KeyboardButton("❌ Выйти из истории"))

    header = f"🎭 [{char_name}] {story['title']}\n\n"
    if bonus_label:
        header += "⭐ Есть особый выбор для твоего персонажа!\n\n"
    send(uid, header + scene.get("text", ""), kb=kb)

# ══════════════════════════════════════════════════════════════
#  ГРУППОВАЯ КАРТОЧНАЯ ИСТОРИЯ (совместная)
# ══════════════════════════════════════════════════════════════

def start_group_card_story(chat_id):
    """Запускает групповую карточную историю."""
    # Сначала регистрация
    _group_games[chat_id] = {
        "game": "card_story",
        "state": "char_select",
        "story_id": "особняк",
        "scene": "start",
        "players": {},     # uid → char_id
        "player_names": {},
        "votes": {},       # uid → choice_label
    }
    kb = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    for char_id, char_data in CARD_CHARACTERS.items():
        kb.add(KeyboardButton(f"🃏 {char_data['name'].split()[1]}"))
    kb.add(KeyboardButton("▶️ Начать историю"))
    send_group(chat_id,
        "🎭 КАРТОЧНАЯ ИСТОРИЯ — ГРУППА!\n\n"
        "Каждый выбирает персонажа. Голосованием решаете куда идти!\n\n" +
        "\n".join(f"{d['name']}: {d['desc'].split(chr(10))[0]}" for d in CARD_CHARACTERS.values()),
        kb=kb)

def proc_group_card_story(chat_id, uid, text):
    """Обрабатывает групповую карточную историю."""
    g = _group_games.get(chat_id)
    if not g or g.get("game") != "card_story":
        return False
    uname = users.get(uid, {}).get("name") or f"ID:{uid}"

    if text == "❌ Выйти из игры":
        del _group_games[chat_id]
        send_group(chat_id, "🚫 История завершена.")
        return True

    state = g.get("state", "char_select")

    # Выбор персонажа
    if state == "char_select":
        for char_id, char_data in CARD_CHARACTERS.items():
            char_short = char_data["name"].split()[1]
            if text == f"🃏 {char_short}":
                g["players"][uid] = char_id
                g["player_names"][uid] = uname
                char_name = char_data["name"]
                send_group(chat_id, f"✅ {uname} выбрал {char_name}")
                return True
        if text == "▶️ Начать историю":
            if not g["players"]:
                send_group(chat_id, "❌ Никто не выбрал персонажа!")
                return True
            g["state"] = "playing"
            _render_group_card_scene(chat_id)
            return True
        return False

    # Голосование за ход
    story = CARD_STORIES.get(g["story_id"])
    if not story:
        del _group_games[chat_id]; return False
    scene = story["scenes"].get(g.get("scene", "start"), {})
    all_choices = list(scene.get("choices", []))

    # Проверяем голос
    for label, dest in all_choices:
        if text == label:
            g["votes"][uid] = label
            vote_count = len(g["votes"])
            total = len(g["players"]) or 1
            send_group(chat_id, f"🗳 {uname}: «{label}» ({vote_count}/{total})")
            # Если большинство проголосовало — применяем
            if vote_count >= max(1, total // 2 + 1):
                # Считаем победивший вариант
                vote_count_per = {}
                for v in g["votes"].values():
                    vote_count_per[v] = vote_count_per.get(v, 0) + 1
                winner_label = max(vote_count_per, key=vote_count_per.get)
                winner_dest = next((d for l, d in all_choices if l == winner_label), None)
                g["votes"] = {}
                if winner_dest:
                    g["scene"] = winner_dest
                    next_scene = story["scenes"].get(winner_dest, {})
                    send_group(chat_id, f"✅ Большинство выбрало: {winner_label}")
                    _render_group_card_scene(chat_id)
                    if next_scene.get("end"):
                        del _group_games[chat_id]
            return True

    return False

def _render_group_card_scene(chat_id):
    g = _group_games.get(chat_id)
    if not g:
        return
    story = CARD_STORIES.get(g["story_id"])
    if not story:
        return
    scene = story["scenes"].get(g.get("scene", "start"), {})
    # Уникальные персонажи группы
    char_names = list(set(
        CARD_CHARACTERS.get(c, {}).get("name", "?")
        for c in g["players"].values()
    ))
    kb = ReplyKeyboardMarkup(resize_keyboard=True, row_width=1)
    for label, _ in scene.get("choices", []):
        kb.add(KeyboardButton(label))
    kb.add(KeyboardButton("❌ Выйти из игры"))
    header = f"🎭 {story['title']} | Персонажи: {', '.join(char_names)}\n\n"
    header += "Голосуйте за следующий шаг!\n\n"
    send_group(chat_id, header + scene.get("text", ""), kb=kb)


RPG_GROUP_SCENES = {
    "start": {
        "text": "🕯 ГРУППОВОЙ RPG!\n\nВы все оказались в тёмном коридоре.\nВпереди — три двери.\nПозади — темнота.\n\nВыберите куда идти:",
        "choices": [("🚪 Левая дверь","left"),("🚪 Правая дверь","right"),("⬇️ Вниз по лестнице","stairs")]
    },
    "left": {
        "text": "🚪 Левая комната.\n\nНа столе лежит записка: «Не читай».\nКто-то уже читал — страницы испачканы.\n\nЧто делаете?",
        "choices": [("📖 Читать записку","read_note"),("🏃 Бежать обратно","start"),("🔦 Осмотреть комнату","examine_left")]
    },
    "right": {
        "text": "🚪 Правая комната.\n\nЗеркало в полный рост.\nВ нём ваши отражения.\nНо одно из отражений двигается само.",
        "choices": [("👁 Смотреть","mirror_stare"),("🤫 Выйти молча","start"),("💬 Поговорить с отражением","mirror_talk")]
    },
    "stairs": {
        "text": "⬇️ Лестница уходит вниз.\n\nСнизу — тихий звук. Как шёпот.\nИли дыхание.\n\nИдёте дальше?",
        "choices": [("✅ Спускаемся","basement"),("❌ Назад","start")]
    },
    "read_note": {
        "text": "📖 В записке: «Вы не первые здесь».\n«И не последние».\n«Но между первыми и последними — ничего».\n\nСвет мигает.",
        "choices": [("🏃 Бежать","escape_win"),("🔦 Осмотреться","examine_left")]
    },
    "examine_left": {
        "text": "🔦 В углу — старый телефон.\nОн звонит.\n\nПодобрать трубку?",
        "choices": [("📞 Взять трубку","phone_answer"),("🚪 Уйти","start")]
    },
    "phone_answer": {
        "text": "📞 В трубке — тишина.\nПотом: «Выход — там откуда пришли».\nПотом — гудки.",
        "choices": [("🔙 Вернуться к началу","escape_win"),("🤔 Остаться","read_note")]
    },
    "mirror_stare": {
        "text": "👁 Вы смотрите в зеркало.\nОтражение останавливается.\nСмотрит на вас.\nМедленно улыбается.",
        "choices": [("💀 Разбить зеркало","mirror_break"),("🏃 Бежать","start")]
    },
    "mirror_talk": {
        "text": "💬 Отражение говорит вашими голосами:\n«Мы тоже искали выход».\n«Нашли».\n«Но нам не понравилось».",
        "choices": [("❓ Где выход","mirror_exit"),("🏃 Уйти","start")]
    },
    "mirror_break": {
        "text": "💥 Зеркало разбито.\nОсколки на полу.\nВ каждом — ваши отражения.\nВсе смотрят на вас.",
        "choices": [("🏃 Бежать","escape_end"),("😶 Замереть","escape_win")]
    },
    "mirror_exit": {
        "text": "🚪 Отражение указывает вниз.\nВы смотрите под ноги — люк.\n\nОткрыть?",
        "choices": [("✅ Открыть","escape_win"),("❌ Нет","start")]
    },
    "basement": {
        "text": "🕯 Подвал.\n\nПустые стулья стоят в круг.\nВ центре — стол.\nНа столе — ваши имена написаны.\n\nВсе ваши имена.",
        "choices": [("🏃 Бежать наверх","escape_end"),("🔍 Исследовать","basement_explore")]
    },
    "basement_explore": {
        "text": "🔍 Под столом — дверца.\nЗа дверцей — выход на улицу.\n\nВы выбрались.",
        "choices": [("🔄 Играть снова","start")], "end": True
    },
    "escape_win": {
        "text": "🌅 Вы нашли выход!\n\nНа улице — утро.\nКак будто ничего не было.\n\n...но телефоны у всех разряжены.\nИ в каждом — одно новое фото.\nВы на нём.\nВсе.\nСпите.\n\n👁 КОНЕЦ",
        "choices": [("🔄 Играть снова","start")], "end": True
    },
    "escape_end": {
        "text": "💀 Вы выбежали.\n\nНо дорога всё время ведёт обратно.\nК той же двери.\nК тому же коридору.\n\n...вы всё ещё там. 👁",
        "choices": [("🔄 Играть снова","start")], "end": True
    },
}

def proc_group_game(chat_id, uid, text):
    """Обрабатывает групповую игру. Возвращает True если обработано."""
    g = _group_games.get(chat_id)
    if not g:
        return False
    gm = g.get("game")
    tl = text.strip().lower()
    uname = users.get(uid, {}).get("name") or f"ID:{uid}"

    if text == "❌ Выйти из игры":
        del _group_games[chat_id]
        send_group(chat_id, "🚫 Игра завершена.", kb=group_reply_kb())
        return True

    if gm == "number":
        if tl.lstrip("-").isdigit():
            guess = int(tl); num = g["number"]; g["attempts"] -= 1
            if guess == num:
                del _group_games[chat_id]
                send_group(chat_id, f"🎯 {uname} угадал(а)! Число было {num}!\n🏆 +20 очков!", kb=group_reply_kb())
                u = U(uid); u["score"] = u.get("score", 0) + 20
            elif g["attempts"] <= 0:
                del _group_games[chat_id]
                send_group(chat_id, f"😔 Попытки закончились! Число было: {num}", kb=group_reply_kb())
            else:
                hint = "⬆️ Больше!" if guess < num else "⬇️ Меньше!"
                send_group(chat_id, f"{uname}: {guess} — {hint} Осталось попыток: {g['attempts']}")
            return True

    if gm == "hangman":
        if len(tl) == 1 and tl.isalpha():
            word = g["word"]; guessed = g["guessed"]
            if tl in guessed:
                send_group(chat_id, f"Буква «{tl}» уже была!")
                return True
            guessed.add(tl)
            if tl not in word:
                g["attempts"] -= 1
            display = " ".join(c if c in guessed else "_" for c in word)
            icon = GALLOWS[max(0, min(6 - g["attempts"], 6))]
            if "_" not in display:
                del _group_games[chat_id]
                send_group(chat_id, f"🎉 {uname} нашёл(а) последнюю букву!\nСлово: {word.upper()}\n+15 очков!", kb=group_reply_kb())
                u = U(uid); u["score"] = u.get("score", 0) + 15
            elif g["attempts"] <= 0:
                del _group_games[chat_id]
                send_group(chat_id, f"{icon} Слово: {word.upper()}", kb=group_reply_kb())
            else:
                send_group(chat_id, f"{uname}: «{tl}»\n{icon}\n{display}\nПопыток: {g['attempts']}")
            return True

    if gm == "trivia":
        # ИСПРАВЛЕНО: проверяем uid (уже отвечал?), а не строку
        if uid in g.get("answered", set()):
            send_group(chat_id, f"{uname}, ты уже ответил!")
            return True
        if tl == g["answer"].lower():
            g.setdefault("answered", set()).add(uid)
            del _group_games[chat_id]
            send_group(chat_id, f"✅ {uname} ответил(а) правильно!\n+10 очков!", kb=group_reply_kb())
            u = U(uid); u["score"] = u.get("score", 0) + 10
            return True

    if gm == "rpg_group":
        scene_key = g.get("scene", "start")
        scene = RPG_GROUP_SCENES.get(scene_key, {})
        for label, nk in scene.get("choices", []):
            if text == label:
                nxt = RPG_GROUP_SCENES.get(nk)
                if nxt:
                    g["scene"] = nk
                    kb = game_kb(nxt.get("choices", []))
                    send_group(chat_id, f"👤 {uname} выбирает: {label}\n\n{nxt['text']}", kb=kb)
                    if nxt.get("end"):
                        del _group_games[chat_id]
                else:
                    send_group(chat_id, "🚧 Эта ветка в разработке.")
                return True
        # Если ввод не совпал — перепоказываем сцену
        kb = game_kb(scene.get("choices", []))
        send_group(chat_id, scene.get("text", ""), kb=kb)
        return True

    if gm == "card_story":
        return proc_group_card_story(chat_id, uid, text)

    if gm == "duel":
        # БАХ обрабатывается отдельно в _handle_group_message
        return False

    if gm == "hot_take":
        # Голосование через inline кнопки, текстовый ввод не нужен
        return False

    return False

# ══════════════════════════════════════════════════════════════
#  v12: ЗАМОРОЗКА СТАДИИ
# ══════════════════════════════════════════════════════════════

def freeze_stage(uid, minutes):
    """Замораживает стадию у пользователя на minutes минут."""
    _stage_frozen[uid] = time.time() + minutes * 60

def unfreeze_stage(uid):
    """Размораживает стадию досрочно."""
    _stage_frozen.pop(uid, None)

# ══════════════════════════════════════════════════════════════
#  v12: ПЕРЕЗАПУСК БОТА
# ══════════════════════════════════════════════════════════════

def bot_restart():
    """Мягкий перезапуск polling без завершения процесса (только главный admin).
    Останавливает infinity_polling — watchdog run_polling() автоматически
    переподключится через backoff-паузу.
    """
    try:
        bot.stop_polling()
    except Exception:
        pass

# ══════════════════════════════════════════════════════════════
#  v12: РАСШИРЕННАЯ КАРТОЧКА ПОЛЬЗОВАТЕЛЯ
# ══════════════════════════════════════════════════════════════

def adm_info_full(tid):
    """Полная карточка пользователя для админа."""
    tu = users.get(tid)
    if not tu: return f"Пользователь {tid} не найден."
    uname_str = ("@" + tu["username"]) if tu.get("username") else "нет username"
    freeze_info = ""
    if tid in _stage_frozen and time.time() < _stage_frozen[tid]:
        mins_left = int((_stage_frozen[tid] - time.time()) / 60)
        freeze_info = f"🔒 Стадия ЗАМОРОЖЕНА (ещё {mins_left} мин)\n"
    return (
        f"👤 ID: {tid}  ({uname_str})\n"
        f"📛 Имя: {tu.get('name','?')}\n"
        f"🎂 Возраст: {tu.get('age','?')}\n"
        f"🌍 Город: {tu.get('city','?')}\n"
        f"📱 Телефон: {tu.get('phone','?')}\n"
        f"🎯 Интересы: {', '.join(tu.get('interests',[])) or '—'}\n"
        f"🐾 Питомец: {tu.get('pet','?')}\n"
        f"💼 Работа: {tu.get('job','?')}\n"
        f"😱 Страх: {tu.get('fear','?')}\n"
        f"🎵 Музыка: {tu.get('music','?')}\n"
        f"🍕 Еда: {tu.get('food','?')}\n"
        f"🎨 Цвет: {tu.get('color','?')}\n"
        f"🌙 Сон: {tu.get('sleep_time','?')}\n"
        f"⚡ Стадия: {tu.get('stage',0)}/5\n"
        f"{freeze_info}"
        f"👁 Хоррор: {'✅' if tu.get('horror_active') else '❌'}\n"
        f"🔇 Заглушён: {'✅' if tu.get('muted') else '❌'}\n"
        f"👁 Шпионаж: {'✅' if tu.get('spy',True) else '❌'}\n"
        f"🤖 Авто-режим: {'✅' if tid in _auto_mode else '❌'}\n"
        f"📊 Фактов: {FC(tu)}\n"
        f"🏆 Очки: {tu.get('score',0)}\n"
        f"💬 Сообщений: {tu.get('msg_count',0)}\n"
        f"📝 История: {len(tu.get('msg_history',[]))} сообщений"
    )

# ══════════════════════════════════════════════════════════════
#  v12: РЕДАКТИРОВАНИЕ ДАННЫХ ПОЛЬЗОВАТЕЛЯ
# ══════════════════════════════════════════════════════════════

EDITABLE_FIELDS = {
    "имя": "name",
    "возраст": "age",
    "город": "city",
    "телефон": "phone",
    "питомец": "pet",
    "работа": "job",
    "страх": "fear",
    "музыка": "music",
    "еда": "food",
    "цвет": "color",
    "сон": "sleep_time",
    "стадия": "stage",
    "очки": "score",
}

def edit_field_kb():
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=3)
    for label in list(EDITABLE_FIELDS.keys())[:12]:
        k.add(KeyboardButton(label.capitalize()))
    k.add(KeyboardButton("🔙 Назад"))
    return k

# ══════════════════════════════════════════════════════════════
#  WATCHDOG — перезапуск polling с экспоненциальным бэкоффом
# ══════════════════════════════════════════════════════════════
_shutdown = threading.Event()

def run_polling():
    backoff = 5
    while not _shutdown.is_set():
        try:
            log.info("Polling started.")
            bot.infinity_polling(
                timeout=30,
                long_polling_timeout=30,
                allowed_updates=["message", "callback_query", "poll_answer", "my_chat_member"],
            )
            backoff = 5  # сброс при успешной сессии
        except Exception:
            log.error("Polling crashed:\n" + traceback.format_exc())
            if _shutdown.is_set(): break
            log.info(f"Restarting polling in {backoff}s...")
            _shutdown.wait(backoff)
            backoff = min(backoff * 2, 120)  # макс 2 минуты

def graceful_shutdown(sig, frame):
    log.info("Получен сигнал остановки. Завершение...")
    _shutdown.set()
    bot.stop_polling()
    _pool.shutdown(wait=False)
    sys.exit(0)

# ══════════════════════════════════════════════════════════════
#  ЗАПУСК
# ══════════════════════════════════════════════════════════════
if __name__ == "__main__":
    # Запуск фоновых потоков v11
    _rand_event_thr = threading.Thread(target=_random_event_loop, daemon=True)
    _rand_event_thr.start()
    threading.Thread(target=_scheduler_loop, daemon=True).start()
    log.info("v11 background threads started")

    signal.signal(signal.SIGINT,  graceful_shutdown)
    signal.signal(signal.SIGTERM, graceful_shutdown)

    admins.add(ADMIN_ID)

    print("╔══════════════════════════════════════════╗")
    print("║     👁  HORROR BOT v17.0 ЗАПУЩЕН  👁     ║")
    print("╠══════════════════════════════════════════╣")
    print(f"║  Admin ID   : {ADMIN_ID}")
    print(f"║  Стадия     : каждые {STAGE_SEC} сек")
    print(f"║  1й хоррор  : через {HORROR_DELAY_SEC} сек")
    print(f"║  gTTS голос : {'✅ мрачный режим' if VOICE_ENABLED else '❌ pip install gTTS'}")
    print(f"║  Шпионаж    : {'✅ авто' if SPY_FORWARD else '❌ отключён'}")
    print(f"║  Анти-спам  : ✅ cooldown {_SPAM_MIN_INTERVAL}с между сообщениями")
    print(f"║  Admin cmd  : /admingo")
    gif_count = len([f for f in __import__("os").listdir(GIF_DIR) if f.lower().endswith(".gif")]) if __import__("os").path.isdir(GIF_DIR) else 0
    print(f"║  Гифки      : ✅ {gif_count} файлов в папке gif/ (авто-подхват)")
    print(f"║  Чат жертв  : ✅ 💬 Чат 3/10 мин в админ-панели")
    print(f"║  Watchdog   : ✅ авто-рестарт + backoff")
    print(f"║  ThreadPool : ✅ макс 32 потока")
    print("║  Остановка  : Ctrl+C")
    print("╚══════════════════════════════════════════╝")
    run_polling()
