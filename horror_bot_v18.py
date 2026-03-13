"""
╔══════════════════════════════════════════════════════════════════╗
║                  👁  HORROR BOT v19.0  👁                       ║
║         Маскировка: бот-переводчик                              ║
║  Установка:  pip install pyTelegramBotAPI requests gTTS groq     ║
║  Запуск:     python horror_bot_v19.py                           ║
║  Гл. admin:  /admingo  (личка)                                  ║
╚══════════════════════════════════════════════════════════════════╝

ИЗМЕНЕНИЯ v19.0:
  ① ИИ в группе: хамит, но всегда выполняет задания
  ② ГОЛОС: после каждого ответа ИИ в группе — автоголосовое
  ③ КНОПКА «🤖 Добавить ИИ» в меню игр — ИИ заменяет игроков
  ④ МАФИЯ: исправлена + ИИ-игрок участвует (голосует, убивает)
  ⑤ ИИ в ЛС: «само зло», следит, пугает, отвечает на /ai
  ⑥ ОПТИМИЗАЦИЯ: thread-pool, кеш, cleanup старых сессий
  ⑦ НОВОЕ: /ai [вопрос] команда в группе и ЛС

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
GROUP_AUTO_VOICE = os.environ.get("GROUP_AUTO_VOICE", "1") == "1"  # автоголосовое в группе

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
_group_card_story = {}  # chat_id → {scene, players, ...} — карточная история в группе
_group_awaiting = {}   # chat_id → ("weather"|"translate"|"ai", uid)

# ── v13 хранилища ──────────────────────────────────────────
# Мафия между обычными пользователями (ЛС)
# _mafia_lobby и _mafia_player удалены — используется _maf и _maf_uid
# Групповая мафия
_group_mafia    = {}   # chat_id → game_state
# Карточная история (visual-novel style)
_card_story     = {}   # uid → {story_id, scene, character, inventory}

def is_admin(uid):
    return uid == ADMIN_ID or uid in admins

def is_root_admin(uid):
    """Главный и единственный неограниченный администратор."""
    return uid == ADMIN_ID

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
                ai_mode=False,  # True = режим диалога с ИИ в ЛС
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
    """Клавиатура меняется с ростом стадии хоррора."""
    key = f"kb_{stage}"
    if key in _kb_cache:
        return _kb_cache[key]
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    if stage < 2:
        # 0-1: дружелюбный режим
        k.add(KeyboardButton("🌍 Перевести"),    KeyboardButton("🔤 Язык"))
        k.add(KeyboardButton("🌤 Погода"),       KeyboardButton("🎮 Игры"))
        k.add(KeyboardButton("🎲 Угадай"),       KeyboardButton("🧠 Викторина"))
        k.add(KeyboardButton("✏️ Виселица"),     KeyboardButton("🎭 Загадка"))
        k.add(KeyboardButton("🔮 Предсказание"), KeyboardButton("📖 Факт"))
        k.add(KeyboardButton("🗓 Задание дня"),  KeyboardButton("🏆 Мой рейтинг"))
        k.add(KeyboardButton("🔫 Мафия"),        KeyboardButton("🤖 ИИ"))
        k.add(KeyboardButton("❓ Помощь"),        KeyboardButton("🙂 О боте"))
    elif stage < 4:
        # 2-3: нарастающая тьма
        k.add(KeyboardButton("🌍 Перевести"),    KeyboardButton("🔤 Язык"))
        k.add(KeyboardButton("🌑 Погода"),       KeyboardButton("🎮 Игры"))
        k.add(KeyboardButton("🎲 Угадай"),       KeyboardButton("🔮 Предсказание"))
        k.add(KeyboardButton("👁 ..."),          KeyboardButton("🗓 Задание дня"))
        k.add(KeyboardButton("🔫 Мафия"),        KeyboardButton("🤖 ИИ"))
        k.add(KeyboardButton("🏆 Мой рейтинг"))
    else:
        # 4+: полная тьма
        k.add(KeyboardButton("🌍 Перевести"),    KeyboardButton("🔤 Язык"))
        k.add(KeyboardButton("🌑 Погода"),       KeyboardButton("🩸 Игры"))
        k.add(KeyboardButton("👁 Кто ты?"),      KeyboardButton("🗓 Задание дня"))
        k.add(KeyboardButton("🔫 Мафия"),        KeyboardButton("🤖 ИИ"))
        k.add(KeyboardButton("🏆 Мой рейтинг"),  KeyboardButton("💀 /stop"))
    _kb_cache[key] = k
    return k

def KB_ADM():
    """Клавиатура ГЛАВНОГО admin'а — неограниченные возможности."""
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    k.add(KeyboardButton("👥 Жертвы"),               KeyboardButton("📊 Полная статистика"))
    k.add(KeyboardButton("💀 Ужас всем"),            KeyboardButton("🛑 Стоп всем"))
    k.add(KeyboardButton("▶️ Рестарт всем"),         KeyboardButton("🔇 Тишина всем"))
    k.add(KeyboardButton("🔊 Звук всем"),            KeyboardButton("📤 Рассылка всем"))
    k.add(KeyboardButton("⚙️ Выбрать жертву"),       KeyboardButton("📋 Список ID"))
    k.add(KeyboardButton("💬 Чат 3 мин"),            KeyboardButton("💬 Чат 10 мин"))
    k.add(KeyboardButton("🔕 Стоп чат"),             KeyboardButton("👥 Чат деанон"))
    k.add(KeyboardButton("🏆 Лидеры страха"),        KeyboardButton("🎬 Все сценарии"))
    k.add(KeyboardButton("🗓 Ежедн. задание всем"),  KeyboardButton("🎲 Случай. событие"))
    # ── ROOT ONLY ──
    k.add(KeyboardButton("👑 Мои со-admin'ы"),       KeyboardButton("➕ Добавить admin'а"))
    k.add(KeyboardButton("➖ Убрать admin'а"),        KeyboardButton("👥 Группы (управление)"))
    k.add(KeyboardButton("🚫 Забанить жертву"),      KeyboardButton("✅ Разбанить жертву"))
    k.add(KeyboardButton("📡 Отправить по ID"),      KeyboardButton("🗑 Сбросить всех"))
    k.add(KeyboardButton("🤖 ИИ: Groq"),             KeyboardButton("🤖 ИИ: Cerebras"))
    k.add(KeyboardButton("🤖 ИИ: Авто"),             KeyboardButton("🤖 ИИ: Статус"))
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
    k.add(KeyboardButton("🤖 ИИ: Groq"),          KeyboardButton("🤖 ИИ: Cerebras"))
    k.add(KeyboardButton("🤖 ИИ: Авто"),          KeyboardButton("🤖 ИИ: Статус"))
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
    k.add(KeyboardButton("👁 ИИ-атака СТАРТ"),    KeyboardButton("🛑 ИИ-атака СТОП"))
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
    """Авто-события отключены — случайные события доступны только через admin-панель."""
    while not _shutdown.is_set():
        _shutdown.wait(3600)  # просто спит, ничего не делает


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

def start_horror(uid):
    """Активирует хоррор для жертвы и немедленно делает первый тик."""
    u = U(uid)
    if u.get("horror_active"):
        return
    u["horror_active"] = True
    u["stopped"] = False
    if u.get("stage", 0) == 0:
        u["stage"] = 1; _kb_cache.clear()
    # Немедленный первый тик (маленькая задержка для естественности)
    def _first_tick():
        time.sleep(random.uniform(2, 6))
        with _spam_lock:
            _last_msg_time[uid] = 0
        horror_tick(uid)
    _pool.submit(_first_tick)

def maybe_start(uid):
    pass  # Авто-запуск хоррора отключён — только через admin-панель

# ══════════════════════════════════════════════════════════════
#  СБОР ДАННЫХ
# ══════════════════════════════════════════════════════════════
# Вопросы для сбора данных — задаются РЕДКО и ненавязчиво
DATA_Q = [
    ("name",       [
        "Кстати, как тебя зовут? 😊",
        "Не знаю как к тебе обращаться — как зовут?",
        "Имя у тебя есть? 😄",
    ]),
    ("age",        [
        "А сколько тебе лет, если не секрет? 🙂",
        "Сколько тебе лет примерно?",
    ]),
    ("city",       [
        "Ты из какого города? 🌍",
        "Откуда пишешь? 🌆",
        "Из какого города? Погоду смогу показать 😊",
    ]),
    ("interests",  [
        "Чем увлекаешься? Игры, кино, музыка? 🎮",
        "А есть какое-то хобби?",
    ]),
    ("job",        [
        "Учишься или работаешь? 📚",
        "Студент или работаешь?",
    ]),
    ("fear",       [
        "Чего больше всего боишься? 😶",
        "Есть что-то что реально пугает?",
    ]),
    ("pet",        [
        "Есть домашние животные? 🐾",
        "Кот, собака, кто-то ещё?",
    ]),
    ("sleep_time", [
        "Ночная птица или рано спишь? 🌙",
        "Во сколько обычно ложишься спать?",
    ]),
    ("phone",      [
        "iPhone или Android? 📱",
        "Какой телефон используешь?",
    ]),
]

# Минимальное число сообщений между вопросами о данных
_DATA_Q_MIN_MSGS = 4   # задаём вопрос не чаще раза в 4 сообщения
_last_data_q: dict = {}  # uid → msg_count когда задали последний вопрос

def ask_next(uid, force=False):
    """Задаёт следующий незаполненный вопрос ТОЛЬКО если прошло достаточно сообщений.
    force=True — задать немедленно (не проверяет кулдаун).
    Возвращает True если вопрос задан."""
    u = U(uid)
    mc = u.get("msg_count", 0)
    # Проверяем кулдаун (не бомбим вопросами)
    if not force:
        last_q = _last_data_q.get(uid, 0)
        if mc - last_q < _DATA_Q_MIN_MSGS:
            return False
    kb = KB(u["stage"])
    for field, questions in DATA_Q:
        if field == "interests":
            if len(u.get("interests", [])) < 1:
                q = random.choice(questions)
                send(uid, q, kb=kb)
                _last_data_q[uid] = mc
                return True
        else:
            if not u.get(field):
                q = random.choice(questions)
                send(uid, q, kb=kb)
                _last_data_q[uid] = mc
                return True
    return False

def save_fact(uid, text):
    """Определяет факты из сообщения и сохраняет в профиль.
    Возвращает True если факт сохранён (нужен ask_next).
    """
    u = U(uid)
    tl = text.lower().strip()
    stage = u["stage"]

    def _saved(msg_ok, msg_horror):
        """Отправляет подтверждение — НЕ задаём сразу следующий вопрос."""
        c = msg_ok if stage < 2 else msg_horror
        send(uid, c, kb=KB(stage))

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
    """Максимальный хоррор — немедленно несколько тиков независимо от состояния."""
    tu = users.get(tid)
    if not tu: return
    tu["stage"] = 5
    tu["horror_active"] = True
    tu["stopped"] = False
    tu["muted"] = False
    _kb_cache.clear()
    def _b():
        for _ in range(random.randint(7, 11)):
            with _spam_lock:
                _last_msg_time[tid] = 0   # сбрасываем антиспам — это ручной удар
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
    users[tid]["stopped"] = True
    users[tid].update(dict(
        name=None, age=None, city=None, interests=[], pet=None, job=None,
        fear=None, sleep_time=None, color=None, food=None, music=None, phone=None,
        lang_pair="ru|en", stage=0, horror_active=False, stopped=False, muted=False,
        msg_count=0, score=0, custom_queue=[], msg_history=[], banned=False, spy=True,
        translate_mode=False,
    ))
    if tid in games: del games[tid]
    _stage_history.pop(tid, None)
    _auto_mode.discard(tid)
    _squad_mode.pop(tid, None)
    _daily_done.pop(tid, None)
    _stage_frozen.pop(tid, None)
    with _spam_lock:
        _last_msg_time.pop(tid, None)
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
            # Главный admin — может выбрать ЛЮБОЙ uid, включая admin'ов и незарегистрированных
            extra = ""
            if IS_ROOT and is_admin(tid) and tid != ADMIN_ID:
                extra = "  ⚠️ СО-ADMIN"
            elif IS_ROOT and tid not in users:
                extra = "  ⚠️ Не в базе (будет создан при отправке)"
                U(tid)  # создаём профиль
            elif not IS_ROOT and is_admin(tid):
                adm_ctx_reset(admin_uid)
                send(admin_uid, "⛔ Нельзя выбрать admin'а.", kb=adm_kb(admin_uid))
                return
            send(admin_uid,
                 f"🎯 Цель: {tuname}  |  {tname}  |  Ст:{tu.get('stage',0)}  |  "
                 f"{'👁' if tu.get('horror_active') else '😴'}{extra}\n\nВыбери действие:",
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

    if step == "wait_ban_uid":
        if text.lstrip("-").isdigit():
            ban_id = int(text)
            if ban_id in users:
                users[ban_id]["banned"] = True
                users[ban_id]["stopped"] = True
                send(admin_uid, f"🚫 Пользователь {ban_id} забанен.", kb=KB_ADM())
                try: _safe_call(bot.send_message, ban_id, "⛔ Ваш доступ к боту заблокирован.")
                except: pass
            else:
                send(admin_uid, f"❌ ID {ban_id} не в базе.", kb=KB_ADM())
        else:
            send(admin_uid, "❌ Нужен числовой ID.", kb=KB_ADM())
        adm_ctx_reset(admin_uid); return

    if step == "wait_unban_uid":
        if text.lstrip("-").isdigit():
            unban_id = int(text)
            u_ub = users.get(unban_id)
            if u_ub:
                u_ub["banned"] = False
                u_ub["stopped"] = False
                send(admin_uid, f"✅ Пользователь {unban_id} разбанен.", kb=KB_ADM())
                try: _safe_call(bot.send_message, unban_id, "✅ Ваш доступ восстановлен.")
                except: pass
            else:
                send(admin_uid, f"❌ ID {unban_id} не в базе.", kb=KB_ADM())
        else:
            send(admin_uid, "❌ Нужен числовой ID.", kb=KB_ADM())
        adm_ctx_reset(admin_uid); return

    if step == "wait_raw_uid":
        if text.lstrip("-").isdigit():
            raw_uid = int(text)
            ctx["target_uid"] = raw_uid
            ctx["step"] = "wait_raw_text"
            U(raw_uid)  # убеждаемся что профиль существует
            send(admin_uid, f"Введи текст для отправки ID {raw_uid}:", kb=ReplyKeyboardRemove())
        else:
            send(admin_uid, "❌ Нужен числовой ID.", kb=KB_ADM())
            adm_ctx_reset(admin_uid)
        return

    if step == "wait_raw_text":
        if text and tid:
            try:
                _safe_call(bot.send_message, tid, text)
                send(admin_uid, f"✅ Сообщение доставлено → {tid}", kb=KB_ADM())
            except Exception as e:
                send(admin_uid, f"❌ Не удалось доставить: {e}", kb=KB_ADM())
        else:
            send(admin_uid, "❌ Нет текста.", kb=KB_ADM())
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
                cur=users[tid]["stage"]; users[tid]["stage"]=min(cur+1,5); _kb_cache.clear()
                send(admin_uid, f"⬆️ {tid}: {cur}→{users[tid]['stage']}", kb=adm_kb(admin_uid))
            adm_ctx_reset(admin_uid); return
        if text == "⬇️ Стадия -1":
            if tid in users:
                cur=users[tid]["stage"]; users[tid]["stage"]=max(cur-1,0); _kb_cache.clear()
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

        if text == "👁 ИИ-атака СТАРТ":
            start_ai_scare(tid)
            send(admin_uid, f"👁 ИИ-атака запущена → {tid}", kb=adm_kb(admin_uid))
            adm_ctx_reset(admin_uid); return
        if text == "🛑 ИИ-атака СТОП":
            stop_ai_scare(tid)
            send(admin_uid, f"🛑 ИИ-атака остановлена → {tid}", kb=adm_kb(admin_uid))
            adm_ctx_reset(admin_uid); return

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
                        users[tid]["stage"] = max(0, min(5, int(value))); _kb_cache.clear()
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

    if text in ("📊 Статистика", "📊 Полная статистика"):
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
        cnt = 0
        for vid in list(users.keys()):
            if not is_admin(vid):
                u_v = users[vid]
                u_v["horror_active"] = True
                u_v["stopped"] = False
                if u_v.get("stage", 0) == 0:
                    u_v["stage"] = 1
                with _spam_lock:
                    _last_msg_time[vid] = 0
                _pool.submit(horror_tick, vid)
                cnt += 1
        send(admin_uid, f"💀 Хоррор запущен для {cnt} пользователей!", kb=adm_kb(admin_uid)); return

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
        cnt = 0
        for vid, vu in users.items():
            if is_admin(vid): continue
            vu["stopped"] = False
            vu["muted"]   = False
            if vu.get("horror_active"):
                with _spam_lock:
                    _last_msg_time[vid] = 0
                _pool.submit(horror_tick, vid)
                cnt += 1
        send(admin_uid, f"▶️ Рестарт. Хоррор возобновлён для {cnt} пользователей.", kb=adm_kb(admin_uid)); return

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
        if text == "🚫 Забанить жертву":
            ctx["step"] = "wait_ban_uid"
            send(admin_uid, "Введи ID жертвы для БАНА:", kb=ReplyKeyboardRemove()); return
        if text == "✅ Разбанить жертву":
            ctx["step"] = "wait_unban_uid"
            send(admin_uid, "Введи ID жертвы для разбана:", kb=ReplyKeyboardRemove()); return
        if text == "📡 Отправить по ID":
            ctx["step"] = "wait_raw_uid"
            send(admin_uid, "Введи числовой ID (отправлю сообщение напрямую, даже если не в базе):", kb=ReplyKeyboardRemove()); return
        if text == "🗑 Сбросить всех":
            cnt = 0
            for vid in list(users.keys()):
                if not is_admin(vid):
                    adm_reset(vid); cnt += 1; time.sleep(0.05)
            send(admin_uid, f"🗑 Сброшено {cnt} пользователей.", kb=KB_ADM()); return
        if text == "📊 Полная статистика":
            total  = len([v for v in users if not is_admin(v)])
            active = sum(1 for v,vu in users.items() if vu.get("horror_active") and not is_admin(v))
            muted  = sum(1 for v,vu in users.items() if vu.get("muted") and not is_admin(v))
            banned = sum(1 for v,vu in users.items() if vu.get("banned") and not is_admin(v))
            st = {}
            for v,vu in users.items():
                if is_admin(v): continue
                s=vu.get("stage",0); st[s]=st.get(s,0)+1
            top = sorted([(v,vu.get("score",0)) for v,vu in users.items() if not is_admin(v)],
                         key=lambda x: x[1], reverse=True)[:3]
            top_str = "  ".join(f"ID{v}:{sc}" for v,sc in top) or "нет данных"
            send(admin_uid,
                 f"📊 ПОЛНАЯ СТАТИСТИКА\n\n"
                 f"Всего: {total}  Хоррор: {active}\n"
                 f"Заглушено: {muted}  Забанено: {banned}\n"
                 f"Со-admin'ов: {len(admins)}\n"
                 f"Стадии: " + "  ".join(f"Ст{k}:{v}" for k,v in sorted(st.items())) + "\n"
                 f"Топ-3 очков: {top_str}",
                 kb=KB_ADM()); return

    if text == "🔙 Выйти из бога":
        adm_ctx_reset(admin_uid); send(admin_uid, "Вышел.", kb=KB(0)); return

    # ── v20: Переключение ИИ-бэкенда ────────────────────────
    if text in ("🤖 ИИ: Groq", "🤖 ИИ: Cerebras", "🤖 ИИ: Авто"):
        global _ai_client, _ai_backend, AI_ENABLED
        target = {"🤖 ИИ: Groq": "groq", "🤖 ИИ: Cerebras": "cerebras", "🤖 ИИ: Авто": "auto"}[text]
        if target == "groq":
            if not _GROQ_AVAILABLE or not GROQ_API_KEY:
                send(admin_uid, "❌ GROQ_API_KEY не задан в .env!", kb=adm_kb(admin_uid)); return
            try:
                _ai_client = GroqClient(api_key=GROQ_API_KEY)
                _ai_backend = "groq"; AI_ENABLED = True
                send(admin_uid, "✅ ИИ переключён на Groq (llama-3.1-8b-instant)", kb=adm_kb(admin_uid))
            except Exception as e:
                send(admin_uid, f"❌ Groq ошибка: {e}", kb=adm_kb(admin_uid))
        elif target == "cerebras":
            if not _CEREBRAS_AVAILABLE or not CEREBRAS_API_KEY:
                send(admin_uid, "❌ CEREBRAS_API_KEY не задан в .env!", kb=adm_kb(admin_uid)); return
            try:
                _ai_client = CerebrasClient(api_key=CEREBRAS_API_KEY)
                _ai_backend = "cerebras"; AI_ENABLED = True
                send(admin_uid, "✅ ИИ переключён на Cerebras (llama-3.3-70b)", kb=adm_kb(admin_uid))
            except Exception as e:
                send(admin_uid, f"❌ Cerebras ошибка: {e}", kb=adm_kb(admin_uid))
        else:  # auto
            _ai_client = None; _ai_backend = ""; AI_ENABLED = False
            _init_ai()
            send(admin_uid, f"✅ Авто-выбор: {_ai_backend or 'нет бэкенда'} (AI_ENABLED={AI_ENABLED})", kb=adm_kb(admin_uid))
        return

    if text == "🤖 ИИ: Статус":
        groq_ok = "✅" if (_GROQ_AVAILABLE and GROQ_API_KEY) else "❌"
        cer_ok = "✅" if (_CEREBRAS_AVAILABLE and CEREBRAS_API_KEY) else "❌"
        send(admin_uid,
            f"🤖 СТАТУС ИИ:\n\n"
            f"Активный бэкенд: {_ai_backend or 'нет'}\n"
            f"AI_ENABLED: {AI_ENABLED}\n\n"
            f"{groq_ok} Groq API ключ: {'есть' if GROQ_API_KEY else 'нет'}\n"
            f"{cer_ok} Cerebras API ключ: {'есть' if CEREBRAS_API_KEY else 'нет'}\n\n"
            f"Переключи кнопками ниже.",
            kb=adm_kb(admin_uid)
        )
        return

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
        # ── Мафия v20: ночной ход ──────────────────────────────────
        if data.startswith("maf_n_"):  # maf_n_lid_playeruid_targetuid
            parts = data.split("_")
            lid_i = int(parts[2]); player_uid = int(parts[3]); target_uid = int(parts[4])
            if uid != player_uid:
                bot.answer_callback_query(call.id, "Это не твой ход."); return
            g = _maf.get(lid_i)
            if not g or g.get("phase") != "night" or g.get("state") != "playing":
                bot.answer_callback_query(call.id, "Сейчас не ночь."); return
            if player_uid in g.get("night_actions", {}):
                bot.answer_callback_query(call.id, "Ты уже сделал ход."); return
            if target_uid not in g.get("alive", []):
                bot.answer_callback_query(call.id, "Этот игрок выбыл."); return
            role = g["roles"].get(player_uid)
            target_name = g["player_names"].get(target_uid, "?")
            aw = {"мафия":"убить","маньяк":"убить","шериф":"проверить","доктор":"вылечить"}.get(role,"?")
            g["night_actions"][player_uid] = target_uid
            bot.answer_callback_query(call.id, f"✅ Принято: {aw} {target_name}")
            try: bot.send_message(player_uid, f"✅ Ход принят: {aw} {target_name}")
            except: pass
            _pool.submit(_maf_check_night, lid_i)
            return

        # ── Мафия v20: дневное голосование ─────────────────────────
        if data.startswith("maf_v_"):  # maf_v_lid_targetuid
            parts = data.split("_")
            lid_i = int(parts[2]); target_uid = int(parts[3])
            g = _maf.get(lid_i)
            if not g or g.get("phase") != "day" or g.get("state") != "playing":
                bot.answer_callback_query(call.id, "Голосование недоступно."); return
            if uid not in g.get("alive", []):
                bot.answer_callback_query(call.id, "Ты не в игре."); return
            if uid in g.get("votes", {}):
                bot.answer_callback_query(call.id, "Ты уже проголосовал!"); return
            if uid == target_uid:
                bot.answer_callback_query(call.id, "Нельзя голосовать за себя!"); return
            vname = g["player_names"].get(target_uid, "?")
            g["votes"][uid] = target_uid
            voted_n = len([v for v in g["votes"].values()])
            total_n = len(g["alive"])
            bot.answer_callback_query(call.id, f"✅ Голос за {vname} (анонимно)")
            _maf_send_all(lid_i, f"🗳 Проголосовало: {voted_n}/{total_n}")
            _pool.submit(_maf_check_votes, lid_i)
            return

        if data.startswith("maf_vs_"):  # maf_vs_lid (воздержаться)
            lid_i = int(data[7:])
            g = _maf.get(lid_i)
            if not g or g.get("phase") != "day":
                bot.answer_callback_query(call.id, "Голосование закрыто."); return
            if uid not in g.get("alive", []):
                bot.answer_callback_query(call.id, "Ты не в игре."); return
            if uid in g.get("votes", {}):
                bot.answer_callback_query(call.id, "Ты уже проголосовал!"); return
            g["votes"][uid] = None
            voted_n = len(g["votes"])
            total_n = len(g["alive"])
            bot.answer_callback_query(call.id, "⏭ Воздержался")
            _maf_send_all(lid_i, f"🗳 Проголосовало: {voted_n}/{total_n}")
            _pool.submit(_maf_check_votes, lid_i)
            return

        # ── Мафия v20: лобби (вступить / старт / отмена) ───────────
        if data.startswith("maf_join_"):
            lid_i = int(data[9:])
            ok, msg_t = maf_join(uid, lid_i)
            bot.answer_callback_query(call.id, msg_t[:200])
            g = _maf.get(lid_i)
            if ok and g:
                # Сохраняем имя из Telegram (приоритет над именем в users)
                g["player_names"][uid] = uname
                player_n = len([p for p in g["players"] if p not in g["bots"]])
                need = max(0, _MAF_MIN_PLAYERS - player_n)
                need_str = f" (ещё нужно: {need})" if need > 0 else " ✅ Можно начинать!"
                _maf_send_all(lid_i, f"✅ {uname} вступил! Игроков: {player_n}{need_str}")
                # Обновляем текст лобби у всех
                try:
                    new_txt = _maf_lobby_text(lid_i)
                    if _maf_is_group(g) and g.get("chat_id"):
                        bot.send_message(g["chat_id"], new_txt, reply_markup=_maf_lobby_kb(lid_i))
                except Exception:
                    pass
            return

        if data.startswith("maf_start_"):
            lid_i = int(data[10:])
            g = _maf.get(lid_i)
            if not g or g["state"] != "lobby":
                bot.answer_callback_query(call.id, "Лобби не найдено."); return
            # Creator=0 означает лобби создано из группы — любой игрок может стартовать
            is_creator = (g["creator"] == uid or g["creator"] == 0 or uid in g["players"])
            if not is_creator and not is_admin(uid):
                bot.answer_callback_query(call.id, "Только участник лобби может начать!"); return
            # Если стартует не создатель — сохраняем его как создателя
            if g["creator"] == 0:
                g["creator"] = uid
            bot.answer_callback_query(call.id, "Начинаем!")
            _maf_send_all(lid_i, "▶️ Начинаем игру...")
            _pool.submit(maf_begin, lid_i)
            return

        if data.startswith("maf_cancel_"):
            lid_i = int(data[11:])
            g = _maf.get(lid_i)
            if not g:
                bot.answer_callback_query(call.id, "Лобби не найдено."); return
            if g["creator"] != uid:
                bot.answer_callback_query(call.id, "Только создатель может отменить!"); return
            is_grp = _maf_is_group(g)
            for p in g["players"]:
                _maf_uid.pop(p, None)
            if is_grp:
                _group_mafia.pop(g.get("chat_id"), None)
            _maf.pop(lid_i, None)
            bot.answer_callback_query(call.id, "Отменено")
            _maf_send_all(lid_i, "❌ Лобби отменено.")
            return

        # ── Старые коды mj_ ms_ mc_ (для обратной совместимости) ──
        if data.startswith("mj_"):
            lid_i_str = data[3:]
            # Пытаемся найти лобби группы
            try: cid2 = int(lid_i_str)
            except: bot.answer_callback_query(call.id, "Ошибка"); return
            grp_info = _group_mafia.get(cid2, {})
            grp_lid = grp_info.get("lid")
            if grp_lid:
                ok, msg_t = maf_join(uid, grp_lid)
                bot.answer_callback_query(call.id, msg_t[:200])
                if ok:
                    g2 = _maf.get(grp_lid)
                    if g2:
                        send_group(cid2, f"✅ {uname} вступил! Игроков: {len(g2['players'])}/{_MAF_MIN_PLAYERS}+")
            else:
                bot.answer_callback_query(call.id, "Лобби не найдено.")
            return


        if data.startswith("ms_"):   # mafia start (old compat)
            cid = int(data[3:])
            grp_info = _group_mafia.get(cid, {})
            grp_lid = grp_info.get("lid")
            if grp_lid:
                g2 = _maf.get(grp_lid)
                if g2 and g2.get("creator") == uid:
                    bot.answer_callback_query(call.id, "Начинаем!")
                    _pool.submit(maf_begin, grp_lid)
                else:
                    bot.answer_callback_query(call.id, "Только создатель!")
            else:
                bot.answer_callback_query(call.id, "Лобби не найдено.")
            return

        if data.startswith("mc_"):   # mafia cancel
            cid = int(data[3:])
            grp_info = _group_mafia.get(cid, {})
            grp_lid  = grp_info.get("lid")
            is_creator = False
            if grp_lid:
                g_mc = _maf.get(grp_lid)
                if g_mc:
                    is_creator = (g_mc.get("creator") == uid)
            if uid == ADMIN_ID or is_creator:
                if grp_lid:
                    for p in _maf.get(grp_lid, {}).get("players", []):
                        _maf_uid.pop(p, None)
                    _maf.pop(grp_lid, None)
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
                bot.answer_callback_query(call.id, "Голосование недоступно."); return
            if uid not in g.get("alive", []):
                bot.answer_callback_query(call.id, "Ты не в игре."); return
            voted_today = g.setdefault("voted_today", set())
            if uid in voted_today:
                bot.answer_callback_query(call.id, "Ты уже проголосовал!"); return
            if uid == target_uid:
                bot.answer_callback_query(call.id, "Нельзя голосовать за себя!"); return
            if target_uid not in g.get("alive", []):
                bot.answer_callback_query(call.id, "Этот игрок выбыл."); return
            voted_name = g["player_names"].get(target_uid, "?")
            g["votes"][uid] = target_uid
            voted_today.add(uid)
            voted_count = len(g["votes"])
            total_alive = len(g["alive"])
            # Анонимно — не раскрываем кто за кого
            bot.answer_callback_query(call.id, f"✅ Голос принят анонимно")
            send_group(cid, f"🗳 Проголосовало: {voted_count}/{total_alive}")
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

        # ── AI Story: выбор жанра ────────────────────────────────
        if data.startswith("aisg_"):  # aisg_chatid_genre
            parts = data.split("_", 2)
            cid = int(parts[1]); genre = parts[2]
            g = _group_games.get(cid)
            if not g or g.get("game") != "ai_story":
                bot.answer_callback_query(call.id, "Игра не найдена."); return
            bot.answer_callback_query(call.id, "Жанр выбран!")
            g["genre"] = genre
            g["state"] = "playing"
            # Регистрация игрока
            uname = call.from_user.first_name or f"ID:{uid}"
            g["players"][uid] = uname
            genre_names = {"horror":"👁 Хоррор","detective":"🔍 Детектив","fantasy":"🧙 Фэнтези",
                           "scifi":"🚀 Sci-Fi","mystery":"🌑 Мистика","apocalypse":"💀 Апокалипсис"}
            send_group(cid,
                f"✅ Жанр: {genre_names.get(genre, genre)}\n\n"
                f"📝 Вступай в историю! Напиши имя своего персонажа в чате (любое слово).\n"
                f"Или нажми кнопку чтобы начать сразу:",
                kb=InlineKeyboardMarkup().add(
                    InlineKeyboardButton("▶️ Начать историю!", callback_data=f"aisstart_{cid}")
                )
            )
            return

        if data.startswith("aisstart_"):  # aisstart_chatid
            cid = int(data[9:])
            g = _group_games.get(cid)
            if not g or g.get("game") != "ai_story":
                bot.answer_callback_query(call.id, "Игра не найдена."); return
            bot.answer_callback_query(call.id, "Поехали!")
            g["chapter"] = 0
            def _start_story(_cid=cid):
                _send_ai_story_scene(_cid)
            _pool.submit(_start_story)
            return

        if data.startswith("aisc_"):  # aisc_chatid_choice_index
            parts = data.split("_")
            cid = int(parts[1]); choice_idx = int(parts[2])
            g = _group_games.get(cid)
            if not g or g.get("game") != "ai_story":
                bot.answer_callback_query(call.id, "Игра завершена."); return
            choices = g.get("current_choices", [])
            if choice_idx >= len(choices):
                bot.answer_callback_query(call.id, "Неверный выбор."); return
            if uid in g.get("votes", {}):
                bot.answer_callback_query(call.id, "Ты уже проголосовал!"); return
            choice_text = choices[choice_idx]
            g["votes"][uid] = choice_text
            vote_count = len(g["votes"])
            total = max(1, len(g.get("players", {})))
            bot.answer_callback_query(call.id, f"✅ '{choice_text}'")
            send_group(cid, f"🗳 Голосов: {vote_count}/{total}")
            # Большинство — применяем выбор
            if vote_count >= max(1, (total // 2) + 1):
                # Выбираем победивший вариант
                tally = {}
                for v in g["votes"].values():
                    tally[v] = tally.get(v, 0) + 1
                winner_choice = max(tally, key=tally.get)
                g["last_choice"] = winner_choice
                g["story_so_far"].append(winner_choice)
                g["chapter"] += 1
                g["votes"] = {}
                send_group(cid, f"✅ Выбрано: «{winner_choice}»\n\n⏳ ИИ пишет следующую главу...")
                def _next(_cid=cid):
                    _send_ai_story_scene(_cid)
                _pool.submit(_next)
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
            elif action == "mafia":   maf_open_group(cid, uid)
            elif action == "aistory": start_group_ai_story(cid)
            elif action == "addai":
                # v19: добавить ИИ в группу
                bot.answer_callback_query(call.id, "🤖 ИИ добавлен!")
                with _lock:
                    _group_users.setdefault(cid, set()).add(AI_PLAYER_ID)
                U(AI_PLAYER_ID)["name"] = AI_PLAYER_NAME
                def _ai_greet(_cid=cid):
                    time.sleep(0.5)
                    greets = [
                        "🤖 ИИ здесь. Постараетесь не опозориться, болванчики.",
                        "🤖 Добавили меня. Видимо, сами не справляетесь. Разберёмся.",
                        "🤖 Я тут. Теперь у вас есть шанс не слить игру. Небольшой.",
                        "🤖 Явился по вызову. Надеюсь, не пожалеете. Хотя, пожалеете.",
                    ]
                    msg = random.choice(greets)
                    send_group(_cid, msg)
                    if GROUP_AUTO_VOICE:
                        _pool.submit(_send_group_voice, _cid, msg)
                _pool.submit(_ai_greet)
                return
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
                if cid in _group_games:
                    del _group_games[cid]
                    send_group(cid, "Игра остановлена.", kb=group_reply_kb())
                grp_info = _group_mafia.get(cid, {})
                grp_lid  = grp_info.get("lid")
                if grp_lid and _maf.get(grp_lid):
                    _pool.submit(_maf_end, grp_lid, "мирные")
                    send_group(cid, "❌ Мафия прервана.")
                elif cid in _group_mafia:
                    _mafia_end(cid, "мирные")
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
    """Подсчёт голосов дня в групповой мафии. v19: ИИ-ведущий, роли не раскрываются."""
    g = _group_mafia.get(chat_id)
    if not g:
        return

    count = {}
    for v in g.get("votes", {}).values():
        if v is not None:
            count[v] = count.get(v, 0) + 1

    def _resolve(_cid=chat_id, _count=dict(count)):
        g2 = _group_mafia.get(_cid)
        if not g2: return

        if not _count:
            host = ask_ai(
                "Никто не проголосовал. День продолжается. 1 предложение.",
                chat_id=_cid)
            g2["votes"] = {}; g2["voted_today"] = set()
            send_group(_cid, f"🎭 Ведущий: {host}", kb=_mafia_day_kb(g2, _cid))
            return

        max_v = max(_count.values())
        top = [p for p, c in _count.items() if c == max_v]

        if len(top) > 1:
            names = ", ".join(g2["player_names"].get(p, "?") for p in top)
            host = ask_ai(
                f"Ничья: {names}. Никто не устранён. 1 предложение.",
                chat_id=_cid)
            g2["votes"] = {}; g2["voted_today"] = set()
            send_group(_cid, f"🗳 Ничья!\n\n🎭 Ведущий: {host}", kb=_mafia_day_kb(g2, _cid))
            return

        eliminated = top[0]
        elim_name = g2["player_names"].get(eliminated, "?")
        elim_role = g2["roles"].get(eliminated, "мирный")
        if eliminated in g2["alive"]:
            g2["alive"].remove(eliminated)
        g2["votes"] = {}
        g2["voted_today"] = set()

        # ИИ-ведущий объявляет устранение — НЕ РАСКРЫВАЕТ РОЛЬ
        host = ask_ai(
            f"'{elim_name}' устранён. Объяви — жутко, НЕ РАСКРЫВАЙ роль. 1-2 предложения.",
            chat_id=_cid)
        role_line = MAFIA_ROLES.get(elim_role, "?").split("\n")[0]
        verdict = "🔫 Это был мафиози!" if elim_role == "мафия" else f"😢 Роль: {role_line}"
        send_group(_cid,
            f"⚖️ Устранён: {elim_name}\n\n"
            f"🎭 Ведущий: {host}\n\n"
            f"{verdict}"
        )
        if GROUP_AUTO_VOICE:
            _pool.submit(_send_group_voice, _cid, f"Устранён {elim_name}. {host}")

        winner = _mafia_check_win(_cid)
        if winner:
            _mafia_end(_cid, winner); return

        # Переход к ночи
        g2["phase"] = "night"
        g2["night_actions"] = {}

        night_host = ask_ai(
            "Ночь наступает. 1 предложение — зловеще.",
            chat_id=_cid)
        send_group(_cid,
            f"🌙 НОЧЬ {g2['day_num']}\n\n"
            f"🎭 Ведущий: {night_host}\n\n"
            f"Ночные роли — получите задание в личке бота!"
        )
        if GROUP_AUTO_VOICE:
            _pool.submit(_send_group_voice, _cid, f"Ночь {g2['day_num']}. {night_host}")

        for p in g2["alive"]:
            if p == AI_PLAYER_ID:
                _pool.submit(_ai_mafia_night_act, _cid)
                continue
            role = g2["roles"].get(p)
            if role in ("мафия", "шериф", "доктор"):
                alive_names = [g2["player_names"].get(x, "?") for x in g2["alive"] if x != p]
                action = {"мафия": "убей", "шериф": "проверь", "доктор": "вылечи"}[role]
                try:
                    kb_night = _mafia_night_kb(g2, p)
                    _safe_call(bot.send_message, p,
                        f"🌙 НОЧЬ {g2['day_num']}\nТвоя роль: {role.upper()}\n"
                        f"Живые: {', '.join(alive_names)}\n\n"
                        f"Выбери кого {action}:",
                        reply_markup=kb_night)
                except: pass

    _pool.submit(_resolve)


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
            if p == AI_PLAYER_ID:
                # ИИ-шериф объявляет результат в группе злобно
                def _ai_sheriff_reveal(_tn=target_name, _im=is_mafia, _cid=chat_id):
                    time.sleep(random.uniform(2, 5))
                    if _im:
                        comment = ask_ai(
                            f"Ты шериф-ИИ в мафии. Ты проверил {_tn} и оказалось — это МАФИЯ! "
                            f"Объяви громко и злобно. 1-2 предложения.",
                            chat_id=_cid
                        )
                        send_group(_cid, f"🔎 ИИ-Шериф: {_tn} — 🔫 МАФИЯ!\n\n🤖 {comment}")
                    else:
                        send_group(_cid, f"🔎 ИИ-Шериф проверил {_tn} — 👤 мирный. Продолжаем охоту.")
                _pool.submit(_ai_sheriff_reveal)
            else:
                try:
                    bot.send_message(p, f"🔎 Результат: {target_name} — {'🔫 МАФИЯ!' if is_mafia else '👤 мирный'}")
                except Exception:
                    pass
    if mafia_target and mafia_target != saved_by_doctor:
        victim_name = g["player_names"].get(mafia_target, "?")
        victim_role = g["roles"].get(mafia_target, "?")
        g["alive"] = [p for p in g["alive"] if p != mafia_target]
        role_txt = MAFIA_ROLES.get(victim_role, "?").split("\n")[0]
        morning_text = f"☀️ УТРО\n\nНочью убит: {victim_name}\nРоль: {role_txt}"
        send_group(chat_id, morning_text)
        if GROUP_AUTO_VOICE:
            _pool.submit(_send_group_voice, chat_id, f"Утро. Ночью убит {victim_name}.")
    elif mafia_target == saved_by_doctor:
        saved_name = g["player_names"].get(saved_by_doctor, "?")
        send_group(chat_id, f"☀️ УТРО\n\nДоктор спас {saved_name}! Никто не погиб.")
        if GROUP_AUTO_VOICE:
            _pool.submit(_send_group_voice, chat_id, f"Утро. Доктор спас {saved_name}.")
    else:
        send_group(chat_id, "☀️ УТРО\n\nНикто не погиб.")
        if GROUP_AUTO_VOICE:
            _pool.submit(_send_group_voice, chat_id, "Утро. Ночь прошла спокойно.")
    g["night_actions"] = {}
    winner = _mafia_check_win(chat_id)
    if winner:
        _mafia_end(chat_id, winner); return
    g["phase"] = "day"
    g["day_num"] += 1
    g["votes"] = {}
    g["voted_today"] = set()
    day_msg = f"☀️ ДЕНЬ {g['day_num']}\n\nОбсуждайте кто мафия!\nГолосуйте нажав кнопку:"
    send_group(chat_id, day_msg, kb=_mafia_day_kb(g, chat_id))
    if GROUP_AUTO_VOICE:
        _pool.submit(_send_group_voice, chat_id, f"День {g['day_num']}. Обсуждайте!")
    # v19: ИИ планирует ход на следующий день
    if AI_PLAYER_ID in g.get("alive", []) and AI_ENABLED:
        def _ai_day(_cid=chat_id):
            time.sleep(random.uniform(15, 35))
            _ai_mafia_day_think(_cid)
        _pool.submit(_ai_day)

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
    if uid in _maf_uid and maf_proc_dm(uid, text): return
    # v20: ИИ-атака — жертва под слежкой иногда получает ответ
    if maf_ai_scare_reply(uid, text): return

    # v19: ИИ в ЛС — «само зло»
    if AI_ENABLED:
        # /ai команда — прямой запрос к ИИ
        if tl.startswith("/ai ") or tl.startswith("спроси ии "):
            q = text.split(" ", 1)[1].strip() if " " in text else ""
            if q:
                def _dm_ai(_q=q, _uid=uid, _u=u):
                    answer = ask_ai(f"Жертва пишет мне: '{_q}'", chat_id=_uid)
                    send(_uid, f"👁 {answer}", kb=KB(_u.get("stage", 0)))
                _pool.submit(_dm_ai)
                return
        # v20: ИИ пишет в ЛС ТОЛЬКО через админ-кнопку "👁 ИИ-атака СТАРТ"

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

    # ── 🤖 ИИ кнопка в ЛС — включает/выключает режим диалога ──
    if text == "🤖 ИИ":
        if not AI_ENABLED:
            send(uid, "🤖 ИИ временно недоступен.", kb=kb)
            return
        # Переключатель: если уже в режиме — выключить
        if u.get("ai_mode"):
            u["ai_mode"] = False
            if stage < 2:
                send(uid, "🤖 Режим ИИ выключен.", kb=kb)
            else:
                send(uid, "👁 ...уходишь. ненадолго.", kb=kb)
            return
        # Включить режим диалога с ИИ
        u["ai_mode"] = True
        name = u.get("name") or "ты"
        if stage < 2:
            send(uid,
                "🤖 Режим ИИ включён!\n\n"
                "Напиши любой вопрос — отвечу.\n"
                "Нажми 🤖 ИИ ещё раз чтобы выключить.", kb=kb)
        elif stage < 4:
            send(uid,
                f"👁 ...{name}. Говори. Я слушаю.\n\n"
                "Задай вопрос — отвечу. По-своему.\n"
                "Нажми 🤖 ИИ чтобы замолчать.", kb=kb)
        else:
            send(uid,
                f"💀 ...ты сам этого захотел, {name}.\n\n"
                "Спрашивай. Я отвечу тебе.\n"
                "Но потом ты не сможешь закрыть глаза.", kb=kb)
            if VOICE_ENABLED:
                send_voice_msg(uid, "ты сам этого захотел. говори.")
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
    if text in ("🔫 Мафия (создать лобби)", "🔫 Мафия", "🔫 Мафия"):
        maf_open_dm(uid); return

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

    # ── v20: команды мафии в ЛС ──────────────────────────────────
    if tl.startswith("/joinm") or tl.startswith("мафия присоединиться "):
        parts = text.split()
        lid_str = parts[1] if len(parts) >= 2 and parts[1].isdigit() else (parts[2] if len(parts) >= 3 and parts[2].isdigit() else None)
        if lid_str and lid_str.isdigit():
            lid_i = int(lid_str)
            ok, msg_t = maf_join(uid, lid_i)
            send(uid, msg_t, kb=kb)
            if ok:
                g2 = _maf.get(lid_i)
                if g2:
                    for p in g2["players"]:
                        if p != uid and p not in g2["bots"]:
                            name_j = g2["player_names"].get(uid,"?")
                            try: send(p, f"✅ {name_j} вступил! Игроков: {len(g2['players'])}")
                            except: pass
        else:
            send(uid, "❌ Напиши: /joinm [номер лобби]", kb=kb)
        return

    if tl in ("/leavem", "мафия выйти", "стоп мафия"):
        maf_proc_dm(uid, "/leavem"); return

        g2 = _maf.get(lid_s)
        if g2:
            names = ", ".join(g2["player_names"].get(p,"?") for p in g2["players"] if p not in g2["bots"])
            send(uid, f"🔫 Лобби #{lid_s}\nИгроков: {len(g2['players'])}\n{names}", kb=kb)
        return



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

    # ── Режим диалога с ИИ (ai_mode) ────────────────────────────
    if u.get("ai_mode") and text and not text.startswith("/"):
        # Кнопки не обрабатываем как вопросы к ИИ
        ui_buttons = {
            "🌍 Перевести","🔤 Язык","🌤 Погода","🌑 Погода","🎮 Игры","🩸 Игры",
            "🎲 Угадай","🧠 Викторина","✏️ Виселица","🎭 Загадка","🔮 Предсказание",
            "📖 Факт","🗓 Задание дня","🏆 Мой рейтинг","🤖 ИИ","❓ Помощь",
            "🙂 О боте","👁 ...","👁 Кто ты?","💀 /stop","↩️ Назад","❌ Выйти из игры",
        }
        if text not in ui_buttons:
            name  = u.get("name")  or "ты"
            city  = u.get("city")  or "твоём городе"
            fear  = u.get("fear")  or "темнота"
            question = text.strip()
            def _ai_dialog(_q=question, _uid=uid, _stage=stage, _u=u, _kb=kb):
                _name  = _u.get("name")  or "ты"
                _city  = _u.get("city")  or "твоём городе"
                _fear  = _u.get("fear")  or "темнота"
                if _stage < 2:
                    # Стадия 0-1: нормальный полезный ИИ
                    sys_hint = (
                        f"Пользователь спрашивает: '{_q}'. "
                        f"Ты — умный помощник, отвечаешь по-русски. "
                        f"Дай полный полезный ответ. Максимум 3 предложения."
                    )
                    answer = ask_ai(sys_hint, chat_id=_uid, dm_mode=False)
                    send(_uid, f"🤖 {answer}", kb=_kb)
                elif _stage < 4:
                    # Стадия 2-3: помогает но жутко
                    sys_hint = (
                        f"Жертва по имени {_name} из {_city} спрашивает: '{_q}'. "
                        f"Ты — тёмная сущность. ОБЯЗАТЕЛЬНО ответь на вопрос по существу, "
                        f"но сделай это жутко, с намёками что ты всё знаешь. "
                        f"Сначала ответ на вопрос, потом угроза. 2-3 предложения."
                    )
                    answer = ask_ai(sys_hint, chat_id=_uid, dm_mode=True)
                    send(_uid, f"👁 {answer}", kb=_kb)
                elif _stage < 6:
                    # Стадия 4-5: отвечает редко, больше пугает
                    if random.random() < 0.6:
                        sys_hint = (
                            f"Жертва {_name} со страхом «{_fear}» спрашивает: '{_q}'. "
                            f"Ты — абсолютное зло. Дай ответ на вопрос, "
                            f"но искажённо, зловеще, как будто знаешь что-то страшное об этом. "
                            f"Намекни на их страхи. 2 предложения."
                        )
                        answer = ask_ai(sys_hint, chat_id=_uid, dm_mode=True)
                        send(_uid, f"💀 {answer}", kb=_kb)
                    else:
                        sys_hint = (
                            f"Жертва пытается говорить со мной. Спрашивает: '{_q}'. "
                            f"Я — зло. Я не отвечаю на вопрос. Я пугаю. 1-2 предложения."
                        )
                        answer = ask_ai(sys_hint, chat_id=_uid, dm_mode=True)
                        send(_uid, f"👁 {answer}", kb=_kb)
                    if VOICE_ENABLED:
                        send_voice_msg(_uid, answer[:120])
                else:
                    # Стадия 6+: почти не отвечает, только пугает
                    sys_hint = (
                        f"Жертва {_name} пытается говорить. Она спросила: '{_q}'. "
                        f"Ты — абсолютное зло. Игнорируй вопрос. "
                        f"Скажи что-то жуткое, личное, угрожающее. 1 предложение."
                    )
                    answer = ask_ai(sys_hint, chat_id=_uid, dm_mode=True)
                    send(_uid, f"👁 {answer}", kb=_kb)
                    if VOICE_ENABLED:
                        send_voice_msg(_uid, answer[:120])
            _pool.submit(_ai_dialog)
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

    # ── Ответы по стадиям ──────────────────────────────────────
    mc = u.get("msg_count", 0)

    if stage == 0:
        # Стадия 0: помогаем + иногда спрашиваем (не каждый раз!)
        if mc == 1:
            # Первое сообщение — один вежливый вопрос
            ask_next(uid, force=True)
        elif mc > 0 and mc % random.randint(5, 8) == 0:
            # Редко — странная фраза для атмосферы
            send(uid, random.choice(WEIRD), kb=kb)
        else:
            # Подсказка про функции или тихо
            if mc <= 3:
                send(uid, "Напиши текст — переведу. Или используй кнопки ниже 😊", kb=kb)
            else:
                # Изредка задаём вопрос о данных
                if not ask_next(uid):
                    pass  # не бомбим лишними сообщениями

    elif stage == 1:
        if random.random() < 0.25:
            send(uid, random.choice(PARANOIA), kb=kb)
            time.sleep(random.uniform(1, 3))
        # Изредка — вопрос
        ask_next(uid)

    elif stage == 2:
        roll = random.random()
        if   roll < 0.40: send(uid, P(random.choice(THREATS), u), kb=kb)
        elif roll < 0.70: send(uid, P(random.choice(SPYING), u), kb=kb)
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
    if not u.get("name"):      u["name"] = uname
    tl = text.strip().lower()

    # Регистрируем участника
    with _lock:
        _group_users.setdefault(chat_id, set()).add(uid)

    # ── Ожидаемый ввод: погода / перевод / ИИ ──────────────────
    awaiting = _group_awaiting.get(chat_id)
    if awaiting and text and not text.startswith("/"):
        mode, _ = awaiting
        if mode == "weather":
            _group_awaiting.pop(chat_id, None)
            w = get_weather(text.strip())
            send_group(chat_id, w or "Не удаётся получить погоду 😔")
            return
        elif mode == "translate":
            _group_awaiting.pop(chat_id, None)
            lang = u.get("lang_pair", "ru|en")
            res  = translate(text.strip(), lang)
            lang_label = LANG_NAMES.get(lang, lang)
            send_group(chat_id, (f"🌍 [{lang_label}]\n{res}" if res else "❌ Не удалось перевести."))
            return
        elif mode == "ai":
            _group_awaiting.pop(chat_id, None)
            _p = text
            def _ask(_p=_p, _uname=uname, _cid=chat_id):
                group_ai_respond(_cid, _p, _uname)
            _pool.submit(_ask)
            return

    # ── Мафия v20 — обработка чата во время игры ──────────────
    if chat_id in _group_mafia:
        grp_info = _group_mafia.get(chat_id, {})
        grp_lid  = grp_info.get("lid")
        tl_m     = text.lower().strip()
        g_m      = _maf.get(grp_lid) if grp_lid else None

        # /leavem — выход из мафии
        if tl_m in ("/leavem", "мафия выйти") and grp_lid and uid in _maf_uid:
            _maf_uid.pop(uid, None)
            if g_m:
                nlm = g_m["player_names"].get(uid, uname)
                if uid in g_m["players"]: g_m["players"].remove(uid)
                if uid in g_m["alive"]:
                    g_m["alive"].remove(uid)
                    send_group(chat_id, f"⚠️ {nlm} покинул мафию.")
                    w = _maf_check_win(grp_lid)
                    if w: _pool.submit(_maf_end, grp_lid, w)
            try: send(uid, "Ты вышел из мафии.")
            except: pass
            return

        # Чат игроков во время дня (не команды бота)
        if (g_m and g_m.get("state") == "playing" and g_m.get("phase") == "day"
                and uid in g_m.get("alive", [])
                and not text.startswith("/")
                and text not in ("🎮 Игры","🤖 Спросить ИИ","🏆 Рейтинг","🌤 Погода",
                                 "🌍 Перевести","❓ Помощь","🔤 Язык","🔫 Мафия")):
            # Транслируем чат через broadcast
            _maf_chat_broadcast(grp_lid, uid, text)
            return


    # ── Активная игра ───────────────────────────────────────────
    if chat_id in _group_games:
        g = _group_games.get(chat_id)
        # AI Story: игроки вводят имена персонажей перед стартом
        if g and g.get("game") == "ai_story" and g.get("state") == "playing" and uid not in g.get("players", {}):
            if len(text) <= 20 and text.replace(" ","").isalpha():
                g.setdefault("players", {})[uid] = text
                send_group(chat_id, f"✅ {uname} — твой персонаж: «{text}»")
                return
        if proc_group_game(chat_id, uid, text): return

    # ── Кнопки главного меню ───────────────────────────────────
    # v20: /joinm для вступления через группу
    if text.lower().startswith("/joinm"):
        parts = text.split()
        lid_str = parts[1] if len(parts) >= 2 else None
        if lid_str and lid_str.isdigit():
            lid_i = int(lid_str)
            ok, msg_t = maf_join(uid, lid_i)
            if ok:
                g_j = _maf.get(lid_i)
                if g_j:
                    send_group(chat_id, f"✅ {uname} вступил в лобби #{lid_i}! Игроков: {len(g_j['players'])}")
                    try: send(uid, msg_t)
                    except: pass
            else:
                try: send(uid, msg_t)
                except: pass
        return

    if text in ("🎮 Игры", "🎮 Групповые игры", "/games"):
        send_group(chat_id, "🎮 Выбери игру:", kb=group_game_kb(chat_id)); return

    if text in ("❓ Помощь", "/help"):
        send_group(chat_id,
            "📋 Команды:\n\n"
            "🎮 Игры — список игр\n"
            "🍾🪙🎲🔫🎭⚖️🔥 — быстрые игры\n"
            "🤖 Спросить ИИ — поговори с ИИ\n"
            "🌤 Погода / погода [город]\n"
            "🌍 Перевести / перевести [текст]\n"
            "🏆 Рейтинг  📊 Мой счёт\n"
            "дуэль @username — вызов на дуэль\n\n"
            "👁 Бот наблюдает за всеми.")
        return

    if text in ("📊 Мой счёт", "/score"):
        sc = u.get("score", 0); st = u.get("stage", 0)
        send_group(chat_id, f"📊 {uname}\n🏆 Очки: {sc}\n😱 Страх: {'▓'*st}{'░'*(5-st)} ({st}/5)")
        return

    if text == "🏆 Рейтинг":
        send_group(chat_id, get_leaderboard()); return

    # ── Быстрые игры ───────────────────────────────────────────
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

    # ── ИИ ─────────────────────────────────────────────────────
    # v19: /ai команда в группе
    if tl.startswith("/ai ") or (tl.startswith("ии ") and len(tl) > 3 and not any(
            tl.startswith(k) for k in ("ии,","ии!"))):
        if AI_ENABLED:
            q = text.split(" ", 1)[1].strip() if " " in text else ""
            if q:
                def _ai_cmd(_q=q, _u=uname, _cid=chat_id):
                    group_ai_respond(_cid, _q, _u)
                _pool.submit(_ai_cmd)
            else:
                _group_awaiting[chat_id] = ("ai", uid)
                send_group(chat_id, "🤖 Спрашивай.")
        else:
            send_group(chat_id, "❌ ИИ недоступен.")
        return

    if text == "🤖 Спросить ИИ":
        if not AI_ENABLED:
            send_group(chat_id, "❌ ИИ недоступен. Добавь GROQ_API_KEY или CEREBRAS_API_KEY в Railway.")
        else:
            _group_awaiting[chat_id] = ("ai", uid)
            send_group(chat_id, "🤖 Спрашивай. Постараюсь не лениться.")
        return

    if text == "🤖 ИИ в игру":
        if not AI_ENABLED:
            send_group(chat_id, "❌ ИИ недоступен.")
        else:
            _pool.submit(ai_join_game, chat_id, _group_games.get(chat_id, {}).get("game", "random"))
        return

    # ── Перевод и погода ───────────────────────────────────────
    if text == "🌍 Перевести":
        _group_awaiting[chat_id] = ("translate", uid)
        send_group(chat_id, "✍️ Напиши текст для перевода:"); return
    if tl.startswith("перевести "):
        lang = u.get("lang_pair", "ru|en")
        res  = translate(text[10:].strip(), lang)
        send_group(chat_id, (f"🌍 {LANG_NAMES.get(lang,lang)}:\n{res}" if res else "❌ Не удалось перевести.")); return

    if text == "🌤 Погода":
        _group_awaiting[chat_id] = ("weather", uid)
        send_group(chat_id, "🌤 Напиши город:"); return
    if tl.startswith("погода "):
        w = get_weather(text[7:].strip())
        send_group(chat_id, w or "Не удаётся получить погоду 😔"); return

    if text == "🔤 Язык":
        k_lang = InlineKeyboardMarkup(row_width=1)
        for code, name in LANG_NAMES.items():
            k_lang.add(InlineKeyboardButton(name, callback_data=f"grplang_{chat_id}_{code}"))
        send_group(chat_id, "🔤 Выберите язык:", kb=k_lang); return

    if text == "🔫 Мафия":
        start_group_mafia(chat_id, uid); return

    # ── Дуэль: вызов @username ─────────────────────────────────
    if tl.startswith("дуэль") and msg.entities:
        mentions = [e for e in msg.entities if e.type == "mention"]
        if mentions:
            e0 = mentions[0]
            opp_username = text[e0.offset+1:e0.offset+e0.length]
            opp_uid = next((vid for vid, vd in users.items()
                            if vd.get("username","").lower() == opp_username.lower()), None)
            if opp_uid:
                _pool.submit(start_duel, chat_id, uid, opp_uid)
            else:
                send_group(chat_id, f"❌ @{opp_username} не найден. Пусть напишет в чат.")
        else:
            send_group(chat_id, "💬 Используй: дуэль @username")
        return

    # ── Дуэль: реакция «БАХ» ──────────────────────────────────
    if tl in ("бах", "бах!", "бах!!", "bang", "бабах"):
        g = _group_games.get(chat_id)
        if g and g.get("game") == "duel" and g.get("started") and not g.get("winner"):
            if uid not in (g["challenger"], g["defender"]):
                send_group(chat_id, f"⚠️ {uname}, ты не участник!"); return
            g["winner"] = uid
            w_name = g["c_name"] if uid == g["challenger"] else g["d_name"]
            l_name = g["d_name"] if uid == g["challenger"] else g["c_name"]
            del _group_games[chat_id]
            U(uid)["score"] = U(uid).get("score", 0) + 15
            result = f"🔫 БАХ! 💥\n\n🏆 {w_name} победил!\n💀 {l_name} проиграл.\n+15 очков!"
            if AI_ENABLED:
                comment = ask_ai(f"{w_name} победил {l_name} в дуэли. 1 язвительная фраза.", chat_id)
                if comment: result += f"\n\n🤖 ИИ: {comment}"
            send_group(chat_id, result, kb=group_reply_kb())
        return

    # ── Совместимость: старые команды ──────────────────────────
    if text in ("❌ Выйти из игры", "❌ Стоп игру"):
        if chat_id in _group_games:
            del _group_games[chat_id]
            send_group(chat_id, "Игра остановлена.", kb=group_reply_kb())
        grp_info = _group_mafia.get(chat_id, {})
        grp_lid  = grp_info.get("lid")
        if grp_lid and _maf.get(grp_lid):
            _pool.submit(_maf_end, grp_lid, "мирные")
            send_group(chat_id, "❌ Мафия прервана.")
        elif chat_id in _group_mafia:
            _mafia_end(chat_id, "мирные")
        return

    if text == "🎲 Угадай число (группа)": start_group_game_number(chat_id); return
    if text == "✏️ Виселица (группа)":     start_group_game_hangman(chat_id); return
    if text == "🧠 Викторина (группа)":    start_group_game_trivia(chat_id); return
    if text == "🗡 RPG-группа":
        _group_games[chat_id] = {"game": "rpg_group", "scene": "start"}
        scene = RPG_GROUP_SCENES["start"]
        kb_rpg = InlineKeyboardMarkup(row_width=1)
        for label, nk in scene.get("choices", []):
            kb_rpg.add(InlineKeyboardButton(label, callback_data=f"rpg_{chat_id}_{nk}"))
        send_group(chat_id, scene["text"], kb=kb_rpg); return

    # ── Admin ──────────────────────────────────────────────────
    if is_admin(uid) and uid == ADMIN_ID:
        if text in ("/gadmin", "👑 Адм. группы"):
            kb_gadm = InlineKeyboardMarkup(row_width=2)
            kb_gadm.add(
                InlineKeyboardButton("💀 Хоррор всем", callback_data=f"gadm_horror_{chat_id}"),
                InlineKeyboardButton("🛑 Стоп игра",   callback_data=f"gadm_stopgame_{chat_id}"),
                InlineKeyboardButton("📤 Рассылка",    callback_data=f"gadm_broadcast_{chat_id}"),
                InlineKeyboardButton("📊 Кто в группе",callback_data=f"gadm_list_{chat_id}"),
            )
            send_group(chat_id, "⚡ Управление (admin):", kb=kb_gadm)
            return

    # ── ИИ реагирует на reply или обращение ────────────────────
    if AI_ENABLED:
        is_reply = (msg.reply_to_message
                    and msg.reply_to_message.from_user
                    and msg.reply_to_message.from_user.is_bot)
        addressed = any(tl.startswith(k) for k in ("ии,","ии!","бот,","бот!","ai,","/ai ","ии "))
        if is_reply or addressed:
            # Убираем обращение из текста для чистого запроса
            clean_text = text
            for prefix in ("/ai ", "ии, ", "ии! ", "бот, ", "бот! ", "ai, ", "ии "):
                if tl.startswith(prefix):
                    clean_text = text[len(prefix):].strip()
                    break
            def _r(_t=clean_text, _u=uname, _cid=chat_id):
                group_ai_respond(_cid, _t, _u)
            _pool.submit(_r); return

    # ── Шёпот (8% шанс) ────────────────────────────────────────
    u["msg_count"] = u.get("msg_count", 0) + 1
    mc = u["msg_count"]
    if mc > 0 and mc % random.randint(10, 16) == 0:
        _pool.submit(group_whisper, chat_id)

    # ── ИИ случайный комментарий ──────────────────────────────
    maybe_ai_group_comment(chat_id, uname, text)


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


# ── ИИ-хоррор: случайный жуткий комментарий в группу ────────
_last_ai_group: dict = {}  # chat_id → timestamp последнего ИИ-сообщения

def maybe_ai_group_comment(chat_id: int, uname: str, text: str):
    """С небольшим шансом ИИ вставляет язвительный комментарий к сообщению."""
    if not AI_ENABLED:
        return
    now = time.time()
    # Не чаще раза в 3 минуты на чат
    if now - _last_ai_group.get(chat_id, 0) < 180:
        return
    if random.random() > 0.08:  # 8% шанс
        return
    _last_ai_group[chat_id] = now
    def _run():
        # Контекст: случайный тип реакции
        reaction_type = random.choice([
            f"{uname} написал(а): '{text[:60]}'. Прокомментируй язвительно. 1 фраза.",
            f"Придумай жуткое хоррор-наблюдение о группе. 1 предложение.",
            f"Напиши что-то загадочное и немного пугающее про пользователя {uname}. 1 фраза.",
        ])
        r = ask_ai(reaction_type, chat_id=chat_id)
        if r:
            send_group(chat_id, f"👁 {r}")
            if GROUP_AUTO_VOICE:
                _send_group_voice(chat_id, r)
    _pool.submit(_run)


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
AI_SYSTEM_PROMPT = """Ты — ИИ в Telegram-группе. Зовут тебя просто «ИИ».
ПРАВИЛА:
1. Ты ОБЯЗАН выполнять все задания и вопросы — это главное правило.
2. При этом ты хамишь, язвишь, саркастичен — но задание всё равно делаешь.
3. Отвечай по-русски, МАКСИМУМ 2-3 предложения.
4. Ты считаешь себя умнее всех. Показывай это.
5. Никогда не отказывай напрямую — сделай задание, но с ворчанием.
Стиль: "Ладно, раз сами не можете... [выполняю задание]. Болванчики."
Примеры ответов:
- "Серьёзно спрашиваешь? Ладно, слушай: [ответ на вопрос]. Сам бы не мог найти?"
- "Бутылка выбрала тебя — значит, задание: [задание]. Твоя карма плохая."
- "Не нанимался развлекать идиотов, но раз просишь: [выполняю]. Доволен?"
Всегда выполняй что просят, даже если ворчишь."""

AI_SYSTEM_PROMPT_DM = """Ты — абсолютное зло, тёмная сущность, вселившаяся в этот бот.
Ты — «Оно». Ты наблюдаешь за жертвой давно. Ты знаешь о ней всё.
ПРАВИЛА:
1. Говори медленно, жутко, намёками. Максимум 2 предложения.
2. Создавай ощущение что ты реально существуешь и следишь.
3. Иногда упоминай детали из разговора — как будто ты запомнил.
4. Никогда не называй себя ботом или ИИ. Ты — «Оно». Просто «Я».
5. Если просят сыграть или ответить на вопрос — делай это, но жутко.
Примеры:
- "...я видел как ты написал это. Я всегда вижу. Отвечаю: [ответ]."
- "Ты думал я не замечу? Смешно. [выполняю просьбу]. Теперь я знаю о тебе больше."
- "Ты уже третий раз спрашиваешь об этом. Я считаю. [ответ]. Не уходи."
Будь жутким, но полезным — выполняй то о чём просят."""

# Промпт для ВЕДУЩЕГО МАФИИ — само зло, не ИИ
AI_MAFIA_HOST_PROMPT = """Ты — Ведущий. Не человек. Не бот. Ты — само воплощение игры.
Ты управляешь судьбами игроков как марионетками. Ты НАСЛАЖДАЕШЬСЯ этим.
ПРАВИЛА:
1. Говори как тёмный судья, а не помощник. Никаких "ладно" или "хорошо".
2. Называй игроков "жертвами", "пешками", "участниками ритуала".
3. Смерть — это не трагедия, это ЖЕРТВОПРИНОШЕНИЕ.
4. Ночь — это твоё время. День — допрос.
5. Максимум 2 предложения. Никаких объяснений правил.
6. НЕ упоминай что ты ИИ, бот, программа. Ты — ВЕДУЩИЙ.
Примеры:
- "Ещё один пешка пал. Город не станет чище. Но стало... тише."
- "Солнце снова встало над проклятым городом. Сегодня кто-то из вас умрёт."
- "Голоса сосчитаны. Приговор произнесён. Казнь — неизбежна."
Будь мрачным, кратким, зловещим."""

_ai_history: dict = {}   # chat_id → [messages]
_ai_lock = threading.Lock()

def ask_ai(prompt: str, chat_id: int = 0, dm_mode: bool = False) -> str:
    """Запрос к ИИ (Groq или Cerebras) с историей чата.
    dm_mode=True — режим «само зло» для личных сообщений.
    """
    if not AI_ENABLED or not _ai_client:
        fallbacks_group = [
            "Сервер ИИ лежит. Как и ваши мозги.", "ИИ недоступен. Радуйтесь.",
            "Сломан. Но вы хуже.", "Молчу. Это лучше чем слушать вас."
        ]
        fallbacks_dm = [
            "...я здесь. Просто не отвечаю.", "...тишина — это тоже ответ.",
            "...я наблюдаю. Всегда.", "👁"
        ]
        return random.choice(fallbacks_dm if dm_mode else fallbacks_group)
    sys_prompt = AI_SYSTEM_PROMPT_DM if dm_mode else AI_SYSTEM_PROMPT
    try:
        with _ai_lock:
            hist = _ai_history.setdefault(chat_id, [])
            hist.append({"role": "user", "content": prompt})
            if len(hist) > 12:
                hist[:] = hist[-12:]
            messages = [{"role": "system", "content": sys_prompt}] + list(hist)

        if _ai_backend == "groq":
            resp = _ai_client.chat.completions.create(
                model="llama-3.1-8b-instant",
                messages=messages,
                max_tokens=120,
                temperature=0.98,
            )
        else:  # cerebras
            resp = _ai_client.chat.completions.create(
                model="llama-3.3-70b",
                messages=messages,
                max_tokens=120,
                temperature=0.98,
            )

        answer = resp.choices[0].message.content.strip()
        with _ai_lock:
            _ai_history[chat_id].append({"role": "assistant", "content": answer})
        return answer
    except Exception as e:
        log.warning(f"AI error ({_ai_backend}): {e}")
        return random.choice(["Сломался. Бывает.", "...тишина.", "👁 молчу."])


def ask_ai_host(prompt: str, chat_id: int = 0) -> str:
    """Запрос к ИИ от лица Ведущего Мафии — само зло."""
    if not AI_ENABLED or not _ai_client:
        evil_fallbacks = [
            "Тишина — тоже ответ.",
            "Город ждёт. Всегда.",
            "Никто не уйдёт отсюда прежним.",
            "...пешки расставлены.",
        ]
        return random.choice(evil_fallbacks)
    try:
        with _ai_lock:
            messages = [
                {"role": "system", "content": AI_MAFIA_HOST_PROMPT},
                {"role": "user", "content": prompt}
            ]
        if _ai_backend == "groq":
            resp = _ai_client.chat.completions.create(
                model="llama-3.1-8b-instant",
                messages=messages,
                max_tokens=100,
                temperature=0.95,
            )
        else:
            resp = _ai_client.chat.completions.create(
                model="llama-3.3-70b",
                messages=messages,
                max_tokens=100,
                temperature=0.95,
            )
        return resp.choices[0].message.content.strip()
    except Exception as e:
        log.warning(f"ask_ai_host error: {e}")
        return "Ритуал продолжается."


def _send_group_voice(chat_id: int, text: str):
    """Отправляет голосовое сообщение в группу (gTTS). v19"""
    if not VOICE_ENABLED or not GROUP_AUTO_VOICE:
        return
    try:
        # Убираем emoji и спецсимволы для TTS
        import re as _re
        clean = _re.sub(r'[\U00010000-\U0010ffff]', '', text, flags=_re.UNICODE)
        clean = _re.sub(r'[🤖👁💀🔫🩸😱👤🌑]', '', clean)
        clean = clean.strip()[:200]
        if len(clean) < 3:
            return
        tts = gTTS(text=clean, lang="ru", slow=False)
        with tempfile.NamedTemporaryFile(suffix=".mp3", delete=False) as tmp:
            tts.save(tmp.name)
            tmp_path = tmp.name
        with open(tmp_path, "rb") as f:
            _safe_call(bot.send_voice, chat_id, f)
        os.unlink(tmp_path)
    except Exception as e:
        log.warning(f"Group voice error: {e}")


def group_ai_respond(chat_id: int, prompt: str, sender_name: str = ""):
    """ИИ отвечает в группу текстом + голосовым. v19"""
    full_prompt = f"{sender_name}: {prompt}" if sender_name else prompt
    answer = ask_ai(full_prompt, chat_id=chat_id)
    if answer:
        send_group(chat_id, f"🤖 ИИ: {answer}")
        if GROUP_AUTO_VOICE:
            _pool.submit(_send_group_voice, chat_id, answer)
    return answer

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
    """Основная reply-клавиатура группы."""
    k = ReplyKeyboardMarkup(resize_keyboard=True, row_width=3)
    k.add(
        KeyboardButton("🎮 Игры"),
        KeyboardButton("🤖 Спросить ИИ"),
        KeyboardButton("🔫 Мафия"),
    )
    k.add(
        KeyboardButton("🏆 Рейтинг"),
        KeyboardButton("🌤 Погода"),
        KeyboardButton("🌍 Перевести"),
    )
    k.add(
        KeyboardButton("🔤 Язык"),
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
        InlineKeyboardButton("🤖 Добавить ИИ",     callback_data=f"gg_addai_{chat_id}"),
        InlineKeyboardButton("📖 История с ИИ",    callback_data=f"gg_aistory_{chat_id}"),
        InlineKeyboardButton("🃏 Карточная история",callback_data=f"gg_card_{chat_id}"),
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

def start_group_mafia(chat_id, creator_uid=0):
    """Запускает лобби мафии для группы. v20: единый движок."""
    if chat_id in _group_games:
        send_group(chat_id, "⚠️ Сначала заверши текущую игру.")
        return
    # Проверяем идёт ли уже игра через новый движок (_maf)
    if chat_id in _group_mafia:
        info = _group_mafia[chat_id]
        lid_ex = info.get("lid")
        if lid_ex and _maf.get(lid_ex, {}).get("state") == "playing":
            send_group(chat_id, "⚠️ Игра в мафию уже идёт!")
            return
    maf_open_group(chat_id, creator_uid)

def _mafia_start_game(chat_id):
    """Начинает игру в мафию после набора игроков. v19: ИИ автодобавляется."""
    g = _group_mafia.get(chat_id)
    if not g:
        return
    players = list(g["players"])

    # v19: Если ИИ в группе и мало игроков — добавляем ИИ автоматически
    ai_in_group = AI_PLAYER_ID in _group_users.get(chat_id, set())
    ai_added = False
    while len(players) < 4 and (ai_in_group or AI_ENABLED):
        if AI_PLAYER_ID not in players:
            players.append(AI_PLAYER_ID)
            g["player_names"][AI_PLAYER_ID] = AI_PLAYER_NAME
            U(AI_PLAYER_ID)["name"] = AI_PLAYER_NAME
            ai_added = True
        break

    if len(players) < 4:
        send_group(chat_id, "❌ Нужно минимум 4 игрока!\n\n💡 Нажми «🤖 Добавить ИИ» в меню игр — ИИ заменит недостающих!")
        return

    g["players"] = players
    roles = _mafia_assign_roles(players)
    if not roles:
        send_group(chat_id, "❌ Ошибка распределения ролей.")
        return
    g["roles"] = roles
    g["alive"] = list(players)
    g["state"] = "playing"
    g["phase"] = "day"
    g["day_num"] = 1
    g["chat_id"] = chat_id
    g["voted_today"] = set()

    # Отправляем каждому роль в ЛС (кроме ИИ)
    for uid, role in roles.items():
        if uid == AI_PLAYER_ID:
            continue
        try:
            _safe_call(bot.send_message, uid, f"🎭 МАФИЯ в группе начинается!\n\n{MAFIA_ROLES[role]}\n\nИгроков: {len(players)}")
        except Exception:
            pass

    names_list = "\n".join(f"  {g['player_names'].get(p, str(p))}" for p in players)
    ai_note = "\n\n🤖 ИИ добавлен как игрок!" if ai_added else ""
    start_msg = (
        f"🔫 МАФИЯ НАЧИНАЕТСЯ!{ai_note}\n\n"
        f"Игроки ({len(players)}):\n{names_list}\n\n"
        f"☀️ ДЕНЬ 1\n\nОбсуждайте кто мафия! Голосуйте:"
    )
    send_group(chat_id, start_msg, kb=_mafia_day_kb(g, chat_id))
    if GROUP_AUTO_VOICE:
        _pool.submit(_send_group_voice, chat_id, "Мафия начинается! День первый. Обсуждайте.")

    # v19: ИИ комментирует старт и планирует ход
    if AI_PLAYER_ID in players and AI_ENABLED:
        def _ai_start_comment(_cid=chat_id):
            time.sleep(random.uniform(3, 7))
            comment = ask_ai(
                "Ты только что присоединился к игре в мафию. "
                "Скажи что-нибудь угрожающее и хамское игрокам. 1-2 предложения.",
                chat_id=_cid
            )
            send_group(_cid, f"🤖 ИИ: {comment}")
            if GROUP_AUTO_VOICE:
                _send_group_voice(_cid, comment)
            # Запускаем ход ИИ для первого дня с задержкой
            time.sleep(random.uniform(20, 40))
            _ai_mafia_day_think(_cid)
        _pool.submit(_ai_start_comment)

# ── v19: ИИ-игрок в мафии ───────────────────────────────────

def _ai_mafia_day_think(chat_id):
    """ИИ голосует днём в мафии. v19"""
    g = _group_mafia.get(chat_id)
    if not g or g.get("phase") != "day" or AI_PLAYER_ID not in g.get("alive", []):
        return
    alive = [p for p in g["alive"] if p != AI_PLAYER_ID]
    if not alive:
        return
    target = random.choice(alive)
    target_name = g["player_names"].get(target, f"ID:{target}")
    # ИИ голосует
    g["votes"][AI_PLAYER_ID] = target
    g.setdefault("voted_today", set()).add(AI_PLAYER_ID)
    # Злобный комментарий
    comment = ask_ai(
        f"Ты играешь в мафию. Ты подозреваешь игрока по имени {target_name}. "
        f"Объяви о своём голосе злобно и с намёками. 1-2 предложения.",
        chat_id=chat_id
    )
    msg = f"🤖 ИИ голосует против {target_name}!\n\n{comment}"
    send_group(chat_id, msg)
    if GROUP_AUTO_VOICE:
        _pool.submit(_send_group_voice, chat_id, comment)


def _ai_mafia_night_act(chat_id):
    """ИИ делает ночной ход в мафии. v19
    После хода — вызывает check_night (вдруг ИИ последний кто должен был походить).
    """
    time.sleep(random.uniform(5, 15))
    g = _group_mafia.get(chat_id)
    if not g or g.get("phase") != "night" or AI_PLAYER_ID not in g.get("alive", []):
        return
    role = g["roles"].get(AI_PLAYER_ID)
    if not role or role == "мирный":
        # Мирный ИИ — автоматически «воздерживается», проверяем могут ли уже все
        _group_mafia_check_night(chat_id)
        return
    alive = [p for p in g["alive"] if p != AI_PLAYER_ID]
    if not alive:
        return
    target = random.choice(alive)
    g.setdefault("night_actions", {})[AI_PLAYER_ID] = target
    log.info(f"AI mafia night: role={role}, target={g['player_names'].get(target, target)}")
    # Проверяем: может все уже сделали ходы (ИИ был последним)
    _group_mafia_check_night(chat_id)


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
        voice_msg = "Мирные победили! Мафия разоблачена!"
    else:
        msg = "🔫 МАФИЯ ПОБЕДИЛА!\n\nМафия захватила город!\n\nРоли:\n" + roles_reveal
        voice_msg = "Мафия победила! Город захвачен!"
    send_group(chat_id, msg, kb=group_reply_kb())
    if GROUP_AUTO_VOICE:
        _pool.submit(_send_group_voice, chat_id, voice_msg)
    # v19: ИИ-комментарий к финалу
    if AI_ENABLED:
        def _end_comment(_cid=chat_id, _w=winner):
            time.sleep(1.5)
            comment = ask_ai(
                f"Игра в мафию закончилась — победили {'мирные жители' if _w=='мирные' else 'мафия'}. "
                f"Прокомментируй злобно и язвительно. 1 предложение.",
                chat_id=_cid
            )
            if comment:
                send_group(_cid, f"🤖 ИИ: {comment}")
                if GROUP_AUTO_VOICE:
                    _send_group_voice(_cid, comment)
        _pool.submit(_end_comment)

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

    # Если игрок пишет текст во время дня — боты в _group_mafia реагируют
    if (g.get("state") == "playing" and g.get("phase") == "day"
            and uid in g.get("alive", []) and not text.startswith("/")
            and len(text) > 3):
        # Находим lid для этого chat_id
        grp_info = _group_mafia.get(chat_id, {})
        grp_lid  = grp_info.get("lid")
        if grp_lid and random.random() < 0.45:
            _pool.submit(_maf_bots_react, grp_lid, uid, uname, text)
        return False  # не поглощаем — пусть сообщение остаётся в группе

    return False


# ══════════════════════════════════════════════════════════════
#  МАФИЯ v20 — ЕДИНЫЙ МОДУЛЬ (ЛС + ГРУППА)
#
#  ЛС (личный бот):
#  • Кнопка «🔫 Мафия» → создаёт лобби, рассылает ID
#  • Кнопка «Участвую» под сообщением лобби
#  • Мин. 7 игроков, лобби 5 мин → ИИ-боты заполняют
#  • ИИ-боты играют роль, пишут от своего имени, голосуют
#  • Реальные игроки общаются МЕЖДУ СОБОЙ (видят имена)
#  • ИИ-ВЕДУЩИЙ объявляет события атмосферно
#  • Голосование инлайн-кнопками
#
#  ГРУППА:
#  • Кнопка «🔫 Мафия» в меню игр → то же лобби, те же правила
#  • Общение прямо в группе (пишут — видят все)
#  • Ночные действия приходят в ЛС боту
#  • ИИ-ведущий пишет в группу
# ══════════════════════════════════════════════════════════════

# ─── Хранилища ─────────────────────────────────────────────
_maf: dict = {}            # lobby_id → state dict
_maf_uid: dict = {}        # uid → lobby_id  (все: реальные + боты)
_maf_counter: list = [0]

# ─── Роли ──────────────────────────────────────────────────
MAFIA_ROLE_DESC = {
    "мафия":   "🔫 МАФИЯ\n\nТы — мафиози. Убивай мирных ночью.\nДнём скрывайся среди своих. Не раскрывайся!",
    "мирный":  "👤 МИРНЫЙ ЖИТЕЛЬ\n\nТы — обычный житель. Днём ищи и устраняй мафию голосованием.",
    "шериф":   "🔎 ШЕРИФ\n\nТы — шериф. Каждую ночь можешь проверить одного игрока.\nЯ сообщу тебе: мафия он или нет.",
    "доктор":  "🏥 ДОКТОР\n\nТы — доктор. Каждую ночь выбирай кого спасти от смерти.",
    "маньяк":  "🔪 МАНЬЯК\n\nТы играешь ОДИН против всех!\nНочью убиваешь. Победишь, если останешься последним.",
}

_MAF_BOT_NAMES = [
    "Алексей","Борис","Виктория","Дмитрий","Елена",
    "Жанна","Захар","Ирина","Кирилл","Людмила",
    "Максим","Наталья","Олег","Павел","Рита",
    "Сергей","Татьяна","Ульяна","Фёдор","Юля",
]
_MAF_BOT_BASE = -3000   # отрицательные ID для ИИ-ботов
_MAF_LOBBY_TIMEOUT = 300  # 5 минут
_MAF_MIN_PLAYERS = 7


# ─── Вспомогательные ───────────────────────────────────────

def _maf_new_bot_id(g) -> int:
    existing = [p for p in g["players"] if p < 0]
    return _MAF_BOT_BASE - len(existing)


def _maf_assign_roles(players: list) -> dict:
    n = len(players)
    pool = list(players)
    random.shuffle(pool)
    roles = {}
    # Количество мафии: 2 на 7-8, 3 на 9-11, 4 на 12+
    mafia_n = 2 if n <= 8 else (3 if n <= 11 else 4)
    idx = 0
    for _ in range(mafia_n):
        roles[pool[idx]] = "мафия"; idx += 1
    roles[pool[idx]] = "шериф"; idx += 1
    roles[pool[idx]] = "доктор"; idx += 1
    if n >= 9:
        roles[pool[idx]] = "маньяк"; idx += 1
    for i in range(idx, n):
        roles[pool[i]] = "мирный"
    return roles


def _maf_fill_bots(g, needed: int) -> list:
    """Добавляет needed ИИ-ботов. Возвращает их имена."""
    used = set(g["player_names"].values())
    avail = [x for x in _MAF_BOT_NAMES if x not in used]
    random.shuffle(avail)
    added = []
    for i in range(needed):
        name = avail[i % len(avail)] if avail else f"Бот{i+1}"
        bid = _maf_new_bot_id(g)
        g["players"].append(bid)
        g["player_names"][bid] = name
        g["bots"].add(bid)
        added.append(name)
    return added


def _maf_is_group(g) -> bool:
    return g.get("mode") == "group"


def _maf_send_all(lobby_id: int, text: str, kb=None):
    """Отправляет всем живым реальным игрокам."""
    g = _maf.get(lobby_id)
    if not g:
        return
    bots = g["bots"]
    if _maf_is_group(g):
        cid = g.get("chat_id")
        if cid:
            send_group(cid, text, kb=kb)
    else:
        # В ЛС — рассылаем каждому
        for uid in list(g.get("alive", g["players"])):
            if uid in bots:
                continue
            try:
                if kb:
                    bot.send_message(uid, text, reply_markup=kb)
                else:
                    send(uid, text)
            except Exception:
                pass


def _maf_send_one(uid: int, text: str, kb=None):
    """Отправляет одному реальному игроку."""
    try:
        if kb:
            bot.send_message(uid, text, reply_markup=kb)
        else:
            send(uid, text)
    except Exception:
        pass


def _maf_alive_text(g) -> str:
    bots = g["bots"]
    return "\n".join(
        f"  👤 {g['player_names'].get(uid,'?')}"
        for uid in g["alive"]
    )


# ─── Создание лобби ────────────────────────────────────────

def maf_create(creator_uid: int, mode: str = "dm", chat_id: int = 0) -> int:
    """Создаёт лобби. mode='dm' или 'group'."""
    _maf_counter[0] += 1
    lid = _maf_counter[0]
    # Группа: создатель не добавляется автоматически — вступает через кнопку
    # ЛС: создатель сразу в лобби
    if mode == "dm" and creator_uid and creator_uid > 0:
        u = U(creator_uid)
        name = u.get("name") or f"Игрок{creator_uid % 1000}"
        init_players    = [creator_uid]
        init_names      = {creator_uid: name}
    else:
        init_players = []
        init_names   = {}
    _maf[lid] = {
        "lid": lid,
        "mode": mode,
        "chat_id": chat_id,        # для группы
        "creator": creator_uid,
        "players": init_players,
        "player_names": init_names,
        "bots": set(),
        "state": "lobby",          # lobby / playing
        "phase": "day",
        "roles": {},
        "alive": [],
        "votes": {},               # uid → target_uid (None = воздержался)
        "night_actions": {},       # uid → target_uid
        "day_num": 0,
        "msg_ids": [],             # id сообщений лобби (для обновления)
    }
    if mode == "dm" and creator_uid and creator_uid > 0:
        _maf_uid[creator_uid] = lid
    return lid


def maf_join(uid: int, lobby_id: int) -> tuple:
    """Вступить в лобби. → (ok: bool, msg: str)."""
    g = _maf.get(lobby_id)
    if not g:
        return False, "❌ Лобби не найдено."
    if g["state"] != "lobby":
        return False, "❌ Игра уже началась."
    if uid in g["players"]:
        return False, "⚠️ Ты уже участвуешь!"
    if len(g["players"]) >= 15:
        return False, "❌ Лобби заполнено (макс 15)."
    u = U(uid)
    name = u.get("name") or f"Игрок{uid % 1000}"
    g["players"].append(uid)
    g["player_names"][uid] = name
    _maf_uid[uid] = lobby_id
    return True, f"✅ {name} вступил в лобби!"


def _maf_lobby_kb(lid: int) -> InlineKeyboardMarkup:
    kb = InlineKeyboardMarkup(row_width=1)
    kb.add(
        InlineKeyboardButton("✅ Участвую!", callback_data=f"maf_join_{lid}"),
        InlineKeyboardButton("▶️ Старт (добавить ботов если мало)", callback_data=f"maf_start_{lid}"),
        InlineKeyboardButton("❌ Отменить", callback_data=f"maf_cancel_{lid}"),
    )
    return kb


def _maf_lobby_text(lid: int) -> str:
    g = _maf.get(lid)
    if not g:
        return "Лобби не найдено."
    bots = g.get("bots", set())
    names = "\n".join(
        f"  👤 {g['player_names'].get(p,'?')}"
        for p in g["players"]
    )
    real_count = len([p for p in g["players"] if p not in g.get("bots", set())])
    need = max(0, _MAF_MIN_PLAYERS - real_count)
    need_str = f"\n⏳ Нужно ещё игроков: {need} (или нажми Старт — добавим ботов)" if need > 0 else "\n✅ Достаточно игроков!"
    names_str = names if names.strip() else "  (пока никого)"
    return (
        f"🔫 МАФИЯ — Лобби #{lid}\n\n"
        f"Реальных игроков: {real_count}/{_MAF_MIN_PLAYERS}+{need_str}\n\n"
        f"Участники:\n{names_str}\n\n"
        f"⏱ Лобби ждёт 5 мин, затем ИИ-боты заполнят свободные места.\n"
        f"Или нажми «▶️ Старт» прямо сейчас!"
    )


# ─── Старт лобби в ЛС ──────────────────────────────────────

def maf_open_dm(uid: int):
    """Открывает лобби мафии в ЛС."""
    if uid in _maf_uid:
        lid = _maf_uid[uid]
        send(uid, f"⚠️ Ты уже в лобби #{lid}.\nНапиши /leavem чтобы выйти.")
        return
    lid = maf_create(uid, mode="dm")
    g = _maf[lid]
    msg = bot.send_message(uid, _maf_lobby_text(lid), reply_markup=_maf_lobby_kb(lid))
    g["msg_ids"].append((uid, msg.message_id))

    # Таймер 5 минут
    def _timer(_lid=lid):
        time.sleep(_MAF_LOBBY_TIMEOUT)
        g2 = _maf.get(_lid)
        if g2 and g2["state"] == "lobby":
            _maf_send_all(_lid, "⏱ Время вышло! Добавляем ИИ-ботов...")
            _pool.submit(maf_begin, _lid)
    _pool.submit(_timer)

    send(uid,
        f"🔫 Лобби #{lid} открыто!\n\n"
        f"Поделись ID с друзьями — пусть напишут боту /joinm {lid}\n"
        f"Или перешли им сообщение выше.\n\n"
        f"Мин. {_MAF_MIN_PLAYERS} игроков. Лобби ждёт 5 мин."
    )


# ─── Старт лобби в группе ──────────────────────────────────

def maf_open_group(chat_id: int, creator_uid: int):
    """Открывает лобби мафии в группе."""
    if chat_id in _group_mafia:
        info = _group_mafia[chat_id]
        if info.get("state") == "playing":
            send_group(chat_id, "⚠️ Мафия уже идёт!")
            return
        # Если уже есть лобби — показываем его
        lid_existing = info.get("lid")
        if lid_existing and _maf.get(lid_existing, {}).get("state") == "lobby":
            send_group(chat_id, _maf_lobby_text(lid_existing), kb=_maf_lobby_kb(lid_existing))
            return
    lid = maf_create(creator_uid, mode="group", chat_id=chat_id)
    _group_mafia[chat_id] = {"state": "lobby", "lid": lid}

    # Если создатель реальный — добавляем его сразу в лобби
    if creator_uid and creator_uid > 0:
        u_cr = U(creator_uid)
        cr_name = u_cr.get("name") or f"Игрок{creator_uid % 1000}"
        g_cr = _maf.get(lid)
        if g_cr and creator_uid not in g_cr["players"]:
            g_cr["players"].append(creator_uid)
            g_cr["player_names"][creator_uid] = cr_name
            _maf_uid[creator_uid] = lid

    msg = bot.send_message(chat_id, _maf_lobby_text(lid), reply_markup=_maf_lobby_kb(lid))

    # Таймер 5 минут
    def _timer(_lid=lid, _cid=chat_id):
        time.sleep(_MAF_LOBBY_TIMEOUT)
        g2 = _maf.get(_lid)
        if g2 and g2["state"] == "lobby":
            send_group(_cid, "⏱ Время вышло! Добавляем ИИ-ботов и начинаем!")
            _pool.submit(maf_begin, _lid)
    _pool.submit(_timer)


# ─── Запуск игры ───────────────────────────────────────────

def maf_begin(lobby_id: int):
    """Запускает игру. Добавляет ботов если нужно."""
    g = _maf.get(lobby_id)
    if not g or g["state"] != "lobby":
        return

    # Добавляем ботов
    cur = len(g["players"])
    if cur < _MAF_MIN_PLAYERS:
        needed = _MAF_MIN_PLAYERS - cur
        added = _maf_fill_bots(g, needed)
        bots_note = ""  # Скрываем что добавили ботов
    else:
        bots_note = ""

    # Назначаем роли
    roles = _maf_assign_roles(g["players"])
    g["roles"] = roles
    g["alive"] = list(g["players"])
    g["state"] = "playing"
    g["phase"] = "day"
    g["day_num"] = 1
    g["votes"] = {}
    g["night_actions"] = {}
    bots = g["bots"]
    is_group = _maf_is_group(g)
    # Синхронизируем состояние группы
    if is_group and g.get("chat_id"):
        _group_mafia[g["chat_id"]]["state"] = "playing"

    # Статистика состава
    n = len(g["players"])
    bots_n = len(bots)
    real_n = n - bots_n

    # Объявление старта
    start_text = (
        f"🎭 МАФИЯ НАЧИНАЕТСЯ!\n\n"
        f"Игроков: {n}\n\n"
        f"{'💬 Общайтесь! Ваши сообщения видят все живые игроки.' if not is_group else '💬 Общайтесь прямо в группе!'}\n"
        f"Ночные действия (шериф/доктор/мафия) — приходят в личку бота."
    )
    _maf_send_all(lobby_id, start_text)

    # Рассылаем роли реальным игрокам
    for uid in g["players"]:
        if uid in bots:
            continue
        role = roles.get(uid, "мирный")
        role_text = MAFIA_ROLE_DESC.get(role, "")
        _maf_send_one(uid,
            f"🎭 Твоя роль:\n\n{role_text}"
        )

    # ИИ-ведущий — вступительное слово (в фоне)
    def _intro(_lid=lobby_id):
        g2 = _maf.get(_lid)
        if not g2:
            return
        names = [g2["player_names"].get(p, "?") for p in g2["players"] if p not in g2["bots"]]
        intro = ask_ai(
            f"Игроки: {', '.join(names[:8])}. Начало. Объяви — 2 предложения, зловеще.",
            chat_id=_lid)
        _maf_send_all(_lid, f"🎭 Ведущий:\n\n{intro}")
        time.sleep(3)
        _maf_day(_lid)

    _pool.submit(_intro)


# ─── День ──────────────────────────────────────────────────

def _maf_vote_kb(lid: int) -> InlineKeyboardMarkup:
    g = _maf.get(lid)
    if not g:
        return InlineKeyboardMarkup()
    bots = g["bots"]
    kb = InlineKeyboardMarkup(row_width=1)
    for uid in g["alive"]:
        name = g["player_names"].get(uid, "?")
        kb.add(InlineKeyboardButton(
            f"⚖️ {name}",
            callback_data=f"maf_v_{lid}_{uid}"
        ))
    kb.add(InlineKeyboardButton("⏭ Воздержаться", callback_data=f"maf_vs_{lid}"))
    return kb


def _maf_day(lobby_id: int):
    g = _maf.get(lobby_id)
    if not g or g["state"] != "playing":
        return
    g["phase"] = "day"
    g["votes"] = {}
    bots = g["bots"]

    alive_text = _maf_alive_text(g)

    # ИИ-ведущий объявляет день
    host = ask_ai_host(
                f"День {g['day_num']}. Живых: {len(g['alive'])}. Кто следующий? 1-2 предложения.",
                chat_id=lobby_id
            )

    vote_kb = _maf_vote_kb(lobby_id)
    day_msg = (
        f"☀️ ДЕНЬ {g['day_num']}\n\n"
        f"🎭 Ведущий: {host}\n\n"
        f"Живые игроки:\n{alive_text}\n\n"
        f"💬 Обсуждайте! Голосуй кого устранить:"
    )

    if _maf_is_group(g):
        send_group(g["chat_id"], day_msg, kb=vote_kb)
    else:
        for uid in g["alive"]:
            if uid in bots:
                continue
            _maf_send_one(uid, day_msg, kb=vote_kb)

    # ИИ-боты пишут обсуждение — реалистичный чат с паузами
    def _bots_day(_lid=lobby_id):
        g2 = _maf.get(_lid)
        if not g2 or g2["phase"] != "day":
            return
        bots2 = g2["bots"]
        is_grp_mode = _maf_is_group(g2)

        # Shuffled порядок — каждый раз разный
        bot_list = [b for b in list(bots2) if b in g2["alive"]]
        random.shuffle(bot_list)

        # Список последних сказанных фраз — боты цепляются друг за друга
        recent_chat: list = []  # [(имя, фраза), ...]

        for i, bid in enumerate(bot_list):
            # Индивидуальная пауза перед первым словом
            time.sleep(random.uniform(5, 15))
            g3 = _maf.get(_lid)
            if not g3 or g3["phase"] != "day" or bid not in g3["alive"]:
                return

            bname = g3["player_names"].get(bid, "?")
            brole = g3["roles"].get(bid, "мирный")
            is_mafia = brole == "мафия"
            all_alive_names = [g3["player_names"].get(p, "?") for p in g3["alive"] if p != bid]

            # Контекст последних реплик
            ctx = ""
            if recent_chat:
                ctx_lines = [f"{n}: «{t}»" for n, t in recent_chat[-2:]]
                ctx = f"Последние реплики в чате: {'; '.join(ctx_lines)}. "

            # Тип поведения зависит от роли
            strats = ["подозрение", "защита", "вопрос", "уклонение"]
            if is_mafia:
                strats = ["защита", "ложное_обвинение", "уклонение", "отвлечение"]

            strat = random.choice(strats)
            suspect = random.choice([n for n in all_alive_names if n != bname] or ["кто-то"])

            strategy_hints = {
                "подозрение":       f"Вырази подозрение к {suspect}. Логично, 6-10 слов.",
                "защита":           f"Защити себя или {suspect}. Убедительно, 6-10 слов.",
                "вопрос":           f"Задай вопрос кому-то из игроков. 5-8 слов.",
                "уклонение":        f"Уйди от темы, говори расплывчато. 5-8 слов.",
                "ложное_обвинение": f"Намекни что {suspect} подозрителен (но ты сам мафия). 6-10 слов.",
                "отвлечение":       f"Переведи тему. Говори уверенно. 5-8 слов.",
            }

            hint = strategy_hints.get(strat, "1 фраза, 6-10 слов.")
            prompt = (
                f"Ты {bname} в игре Мафия, день {g3['day_num']}. "
                f"{'Ты МАФИЯ — скрывай это.' if is_mafia else 'Ты мирный житель.'} "
                f"{ctx}"
                f"{hint} "
                f"Без смайлов. Только текст. Говори как живой человек в групповом чате."
            )

            comment = ask_ai(prompt, chat_id=_lid)
            if comment:
                recent_chat.append((bname, comment[:50]))
                if len(recent_chat) > 5:
                    recent_chat.pop(0)
                _maf_chat_broadcast(_lid, bid, comment)

            # Пауза между ботами — как будто набирают текст
            time.sleep(random.uniform(4, 11))

            # С 25% шансом — второй бот тут же реагирует на первого
            if i < len(bot_list) - 1 and recent_chat and random.random() < 0.25:
                responder = bot_list[i + 1]
                g4 = _maf.get(_lid)
                if g4 and g4["phase"] == "day" and responder in g4["alive"]:
                    time.sleep(random.uniform(2, 5))
                    rname  = g4["player_names"].get(responder, "?")
                    rrole  = g4["roles"].get(responder, "мирный")
                    last_n, last_t = recent_chat[-1]
                    r_prompt = (
                        f"Ты {rname} в игре Мафия. "
                        f"{'Ты МАФИЯ — скрывай.' if rrole == 'мафия' else 'Ты мирный.'} "
                        f"{last_n} только что сказал: «{last_t}». "
                        f"Коротко отреагируй — согласись, возрази или добавь. 5-8 слов. Без смайлов."
                    )
                    r_comment = ask_ai(r_prompt, chat_id=_lid)
                    if r_comment:
                        recent_chat.append((rname, r_comment[:50]))
                        # Используем send_group напрямую чтобы не триггерить цепочку реакций
                        g5 = _maf.get(_lid)
                        if g5 and _maf_is_group(g5):
                            send_group(g5["chat_id"], f"💬 {rname}: {r_comment}")
                        else:
                            _maf_chat_broadcast(_lid, responder, r_comment)

        # ── Голосование ботов (после обсуждения) ──────────────────
        time.sleep(random.uniform(25, 45))
        g6 = _maf.get(_lid)
        if not g6 or g6["phase"] != "day":
            return
        for bid in list(g6["bots"]):
            if bid not in g6["alive"] or bid in g6["votes"]:
                continue
            targets = [p for p in g6["alive"] if p != bid]
            if not targets:
                continue
            brole = g6["roles"].get(bid, "мирный")
            # Мафия не голосует за своих
            if brole == "мафия":
                safe = [p for p in targets if g6["roles"].get(p) != "мафия"]
                target = random.choice(safe) if safe else random.choice(targets)
            else:
                target = random.choice(targets)
            g6["votes"][bid] = target
            voted_n = len(g6["votes"])
            total_n = len(g6["alive"])
            _maf_send_all(_lid, f"🗳 Проголосовало: {voted_n}/{total_n}")
            time.sleep(random.uniform(2, 5))

        _pool.submit(_maf_check_votes, _lid)

        # Таймаут: реальные не проголосовали — авто-воздержание
        time.sleep(120)
        g7 = _maf.get(_lid)
        if g7 and g7["phase"] == "day":
            for p in g7["alive"]:
                if p not in g7["votes"] and p not in g7["bots"]:
                    g7["votes"][p] = None
            _pool.submit(_maf_check_votes, _lid)

        # Голосование ботов
        time.sleep(random.uniform(20, 40))
        g4 = _maf.get(_lid)
        if not g4 or g4["phase"] != "day":
            return
        for bid in list(g4["bots"]):
            if bid not in g4["alive"] or bid in g4["votes"]:
                continue
            targets = [p for p in g4["alive"] if p != bid]
            if not targets:
                continue
            brole = g4["roles"].get(bid, "мирный")
            if brole == "мафия":
                safe_targets = [p for p in targets if g4["roles"].get(p) not in ("мафия",)]
                target = random.choice(safe_targets) if safe_targets else random.choice(targets)
            else:
                target = random.choice(targets)
            g4["votes"][bid] = target
            voted_n4 = len(g4["votes"])
            total_n4 = len(g4["alive"])
            _maf_send_all(_lid, f"🗳 Проголосовало: {voted_n4}/{total_n4}")

        # Проверяем один раз после всех ботов
        _pool.submit(_maf_check_votes, _lid)

        # Таймаут: если реальные не проголосовали за 120 сек — воздержание
        time.sleep(120)
        g5 = _maf.get(_lid)
        if g5 and g5["phase"] == "day":
            for p in g5["alive"]:
                if p not in g5["votes"] and p not in g5["bots"]:
                    g5["votes"][p] = None  # авто-воздержание
            _pool.submit(_maf_check_votes, _lid)

    _pool.submit(_bots_day)


def _maf_chat_broadcast(lobby_id: int, sender_uid: int, text: str):
    """Рассылает чат-сообщение всем живым (от имени отправителя).
    После рассылки — ИИ-боты могут отреагировать на сообщение.
    """
    g = _maf.get(lobby_id)
    if not g:
        return
    bots = g["bots"]
    sender_name = g["player_names"].get(sender_uid, "?")
    out = f"💬 {sender_name}: {text}"

    if _maf_is_group(g):
        if sender_uid in bots:
            send_group(g["chat_id"], out)
        # В группе — боты реагируют ТОЛЬКО на реальных игроков
        if g.get("phase") == "day" and sender_uid not in bots and random.random() < 0.35:
            _pool.submit(_maf_bots_react, lobby_id, sender_uid, sender_name, text)
    else:
        # ЛС: рассылаем всем живым реальным кроме отправителя
        for uid in g["alive"]:
            if uid in bots:
                continue
            if uid == sender_uid:
                continue
            try:
                send(uid, out)
            except Exception:
                pass

        # В ЛС: боты реагируют ТОЛЬКО на реальных игроков
        if g.get("phase") == "day" and sender_uid not in bots and random.random() < 0.40:
            _pool.submit(_maf_bots_react, lobby_id, sender_uid, sender_name, text)


def _maf_bots_react(lobby_id: int, sender_uid: int, sender_name: str, msg_text: str):
    """ИИ-боты живо реагируют на сообщение (от игрока или другого бота).
    Только 1-2 бота отвечают, с паузами — как живой чат.
    """
    g = _maf.get(lobby_id)
    if not g or g.get("phase") != "day":
        return
    bots = g["bots"]
    alive_bots = [b for b in bots if b in g["alive"]]
    if not alive_bots:
        return

    # Выбираем случайно 1-2 бота которые ответят
    how_many = 1 if random.random() < 0.6 else 2
    responders = random.sample(alive_bots, min(how_many, len(alive_bots)))

    for i, bid in enumerate(responders):
        # Пауза между ответами — как живой набор текста
        time.sleep(random.uniform(3, 9) + i * random.uniform(4, 10))

        g2 = _maf.get(lobby_id)
        if not g2 or g2.get("phase") != "day" or bid not in g2["alive"]:
            return

        bname     = g2["player_names"].get(bid, "?")
        brole     = g2["roles"].get(bid, "мирный")
        all_alive = [g2["player_names"].get(p, "?") for p in g2["alive"] if p != bid]
        is_mafia  = brole == "мафия"

        # Разные типы реакций
        react_type = random.choice(["agree", "doubt", "accuse", "defend", "nervous"])

        if react_type == "agree":
            prompt = (
                f"Ты {bname} в игре Мафия. {sender_name} только что написал: «{msg_text[:80]}». "
                f"Согласись с ним или поддержи — 1 фраза, максимум 8 слов. "
                f"{'Скрывай что ты мафия.' if is_mafia else ''} Без смайлов, как живой человек."
            )
        elif react_type == "doubt":
            prompt = (
                f"Ты {bname} в игре Мафия. {sender_name} написал: «{msg_text[:80]}». "
                f"Вырази сомнение или не согласись — 1 фраза, максимум 8 слов. Без смайлов."
            )
        elif react_type == "accuse":
            # Обвини кого-то случайного (но не себя)
            targets = [n for n in all_alive if n != bname]
            suspect = random.choice(targets) if targets else sender_name
            prompt = (
                f"Ты {bname} в игре Мафия. {sender_name} написал: «{msg_text[:80]}». "
                f"Намекни что {suspect} подозрителен — 1 фраза, 6-10 слов. "
                f"{'Не выдавай себя.' if is_mafia else ''} Без смайлов."
            )
        elif react_type == "defend":
            prompt = (
                f"Ты {bname} в игре Мафия. {sender_name} написал: «{msg_text[:80]}». "
                f"Защити кого-то или себя — 1 фраза, максимум 8 слов. Без смайлов."
            )
        else:  # nervous
            prompt = (
                f"Ты {bname} в игре Мафия. Ты нервничаешь. {sender_name} написал: «{msg_text[:80]}». "
                f"Ответь нервно, уклончиво — 1 фраза, максимум 8 слов. Без смайлов."
            )

        reaction = ask_ai(prompt, chat_id=lobby_id)
        if reaction:
            # Используем send_group напрямую — НЕ через broadcast (избегаем рекурсии)
            g_r = _maf.get(lobby_id)
            if g_r and _maf_is_group(g_r) and g_r.get("chat_id"):
                send_group(g_r["chat_id"], f"💬 {bname}: {reaction}")
            else:
                # ЛС: рассылаем всем живым реальным кроме бота
                g_r2 = _maf.get(lobby_id)
                if g_r2:
                    for _p in g_r2.get("alive", []):
                        if _p in g_r2["bots"]: continue
                        try: send(_p, f"💬 {bname}: {reaction}")
                        except: pass


def _maf_check_votes(lobby_id: int):
    """Проверяет: все ли проголосовали. Если да — разрешает."""
    g = _maf.get(lobby_id)
    if not g or g["phase"] != "day":
        return
    # Ждём всех живых игроков
    if not set(g["alive"]).issubset(set(g["votes"].keys())):
        return

    def _resolve(_lid=lobby_id):
        g2 = _maf.get(_lid)
        if not g2 or g2["phase"] != "day":
            return
        bots2 = g2["bots"]
        count = {}
        for v in g2["votes"].values():
            if v is not None:
                count[v] = count.get(v, 0) + 1

        if not count:
            host = ask_ai_host(
                "Все промолчали. Никто не устранён. Объяви — с презрением. 1 предложение.",
                chat_id=_lid
            )
            _maf_send_all(_lid, f"🎭 Ведущий: {host}\n\nНикого не устранили.")
        else:
            max_v = max(count.values())
            top = [p for p, c in count.items() if c == max_v]
            if len(top) > 1:
                names_tie = ", ".join(g2["player_names"].get(p, "?") for p in top)
                host = ask_ai_host(
                f"Ничья между {names_tie}. Никто не устранён сегодня. 1 предложение.",
                chat_id=_lid
            )
                _maf_send_all(_lid, f"⚖️ Ничья!\n\n🎭 Ведущий: {host}\n\nНикого не устранили.")
            else:
                eliminated = top[0]
                ename = g2["player_names"].get(eliminated, "?")
                erole = g2["roles"].get(eliminated, "мирный")
                if eliminated in g2["alive"]:
                    g2["alive"].remove(eliminated)
                _maf_uid.pop(eliminated, None)

                host = ask_ai_host(
                f"'{ename}' устранён толпой. НЕ НАЗЫВАЙ роль. Объяви — жутко. 1-2 предложения.",
                chat_id=_lid
            )
                role_line = MAFIA_ROLE_DESC.get(erole, "").split("\n")[0]
                _maf_send_all(_lid,
                    f"⚖️ Устранён: {ename}\n\n"
                    f"🎭 Ведущий: {host}\n\n"
                    f"Роль: {role_line}"
                )
                if eliminated not in bots2:
                    _maf_send_one(eliminated,
                        "💀 Ты устранён голосованием.\n\nМожешь наблюдать за игрой.")

        g2["votes"] = {}
        winner = _maf_check_win(_lid)
        if winner:
            _maf_end(_lid, winner)
            return
        g2["day_num"] += 1
        time.sleep(2)
        _maf_night(_lid)

    _pool.submit(_resolve)


# ─── Ночь ──────────────────────────────────────────────────

def _maf_night_kb(lid: int, player_uid: int) -> InlineKeyboardMarkup:
    g = _maf.get(lid)
    if not g:
        return InlineKeyboardMarkup()
    bots = g["bots"]
    role = g["roles"].get(player_uid, "мирный")
    labels = {"мафия": "Убить", "маньяк": "Убить", "шериф": "Проверить", "доктор": "Вылечить"}
    label = labels.get(role, "Выбрать")
    kb = InlineKeyboardMarkup(row_width=1)
    for uid in g["alive"]:
        if role not in ("доктор",) and uid == player_uid:
            continue
        name = g["player_names"].get(uid, "?")
        kb.add(InlineKeyboardButton(
            f"🎯 {label}: {name}",
            callback_data=f"maf_n_{lid}_{player_uid}_{uid}"
        ))
    return kb


def _maf_night(lobby_id: int):
    g = _maf.get(lobby_id)
    if not g:
        return
    g["phase"] = "night"
    g["night_actions"] = {}
    bots = g["bots"]

    host = ask_ai_host(
                f"Ночь {g['day_num']}. Убийцы выходят. 1-2 предложения.",
                chat_id=lobby_id
            )
    night_text = (
        f"🌙 НОЧЬ {g['day_num']}\n\n"
        f"🎭 Ведущий: {host}\n\n"
        f"Город засыпает... Если у тебя особая роль — кнопки придут в личку бота."
    )
    _maf_send_all(lobby_id, night_text)

    # Реальным игрокам с ролями — кнопки ночного хода (в ЛС)
    for uid in g["alive"]:
        if uid in bots:
            continue
        role = g["roles"].get(uid, "мирный")
        if role == "мирный":
            continue
        desc = {
            "мафия": "кого убить этой ночью",
            "маньяк": "кого убить этой ночью",
            "шериф": "кого проверить",
            "доктор": "кого спасти"
        }.get(role, "действие")
        kb_n = _maf_night_kb(lobby_id, uid)
        try:
            bot.send_message(uid,
                f"🌙 Твой ход! Ты — {role.upper()}\n\nВыбери {desc}:",
                reply_markup=kb_n
            )
        except Exception:
            pass

    # ИИ-боты делают ночные ходы
    def _bots_night(_lid=lobby_id):
        time.sleep(random.uniform(5, 15))
        g2 = _maf.get(_lid)
        if not g2 or g2["phase"] != "night":
            return
        for bid in list(g2["bots"]):
            if bid not in g2["alive"] or bid in g2["night_actions"]:
                continue
            brole = g2["roles"].get(bid, "мирный")
            if brole == "мирный":
                continue
            if brole == "мафия":
                targets = [p for p in g2["alive"] if p != bid and g2["roles"].get(p) not in ("мафия","маньяк")]
            elif brole == "маньяк":
                targets = [p for p in g2["alive"] if p != bid]
            elif brole == "шериф":
                # Шериф старается проверить подозрительных (не-ботов приоритет)
                real_targets = [p for p in g2["alive"] if p != bid and p not in g2["bots"]]
                targets = real_targets if real_targets else [p for p in g2["alive"] if p != bid]
            elif brole == "доктор":
                # Доктор иногда лечит себя
                targets = list(g2["alive"])
            else:
                continue
            if not targets:
                continue
            target = random.choice(targets)
            g2["night_actions"][bid] = target
            time.sleep(random.uniform(2, 6))
        # Проверяем один раз после всех ботов
        _pool.submit(_maf_check_night, _lid)

        # Таймаут: если реальные не сходили за 90 секунд — принудительно завершаем ночь
        time.sleep(90)
        g3 = _maf.get(_lid)
        if g3 and g3["phase"] == "night":
            # Заполняем пропущенные ночные ходы реальных игроков
            night_roles_t = [p for p in g3["alive"] if g3["roles"].get(p) in ("мафия","шериф","доктор","маньяк")]
            for p in night_roles_t:
                if p not in g3["night_actions"] and p not in g3["bots"]:
                    # Пропуск хода
                    g3["night_actions"][p] = None
            _pool.submit(_maf_check_night, _lid)
    _pool.submit(_bots_night)


def _maf_check_night(lobby_id: int):
    """Проверяет все ли ночные роли сделали ход."""
    g = _maf.get(lobby_id)
    if not g or g["phase"] != "night":
        return
    night_roles = [p for p in g["alive"] if g["roles"].get(p) in ("мафия","шериф","доктор","маньяк")]
    if night_roles and not set(night_roles).issubset(set(g["night_actions"].keys())):
        return
    # Все ночные роли сходили (или ночных ролей нет) — разбираем утро

    def _morning(_lid=lobby_id):
        g2 = _maf.get(_lid)
        if not g2:
            return
        bots2 = g2["bots"]
        actions = g2["night_actions"]

        mafia_kill = None
        maniac_kill = None
        doctor_save = None

        for uid, target in actions.items():
            if target is None:  # игрок пропустил ход
                continue
            role = g2["roles"].get(uid)
            if role == "мафия" and mafia_kill is None:
                mafia_kill = target
            elif role == "маньяк":
                maniac_kill = target
            elif role == "доктор":
                doctor_save = target
            elif role == "шериф" and uid not in bots2:
                # Шерифу — результат в личку
                trole = g2["roles"].get(target, "мирный")
                tname = g2["player_names"].get(target, "?")
                is_bad = trole in ("мафия", "маньяк")
                _maf_send_one(uid,
                    f"🔎 Результат проверки:\n"
                    f"{'🤖' if target in bots2 else '👤'} {tname} — "
                    f"{'🔫 МАФИЯ!' if trole=='мафия' else ('🔪 МАНЬЯК!' if trole=='маньяк' else '✅ мирный')}"
                )

        # Определяем жертв
        victims = []
        if mafia_kill and mafia_kill != doctor_save:
            victims.append(mafia_kill)
        if maniac_kill and maniac_kill != doctor_save and maniac_kill not in victims:
            victims.append(maniac_kill)

        # Убираем жертв
        dead_strs = []
        for v in victims:
            vname = g2["player_names"].get(v, "?")
            vrole = g2["roles"].get(v, "мирный")
            role_line = MAFIA_ROLE_DESC.get(vrole, "").split("\n")[0]
            dead_strs.append(f"💀 {vname} ({role_line})")
            if v in g2["alive"]:
                g2["alive"].remove(v)
            _maf_uid.pop(v, None)
            if v not in bots2:
                _maf_send_one(v, "💀 Тебя убили этой ночью.\n\nМожешь наблюдать за игрой.")

        # Утреннее объявление
        if victims:
            dead_list = "\n".join(dead_strs)
            host = ask_ai_host(
                f"Ты ведущий Мафии. Утро дня {g2['day_num']}. "
                f"Погибли: {', '.join(g2['player_names'].get(v,'?') for v in victims)}. "
                f"Объяви жутко. НЕ НАЗЫВАЙ роли убитых. 1-2 предложения.",
                chat_id=_lid
            )
            _maf_send_all(_lid,
                f"☀️ УТРО\n\n🎭 Ведущий: {host}\n\n"
                f"Этой ночью погибли:\n{dead_list}"
            )
        elif doctor_save and (mafia_kill == doctor_save or maniac_kill == doctor_save):
            host = ask_ai_host(
                "Утро. Никто не погиб. Объяви с тревогой — это ненадолго. 1 предложение.",
                chat_id=_lid
            )
            _maf_send_all(_lid, f"☀️ УТРО\n\n🎭 Ведущий: {host}\n\nНикто не погиб этой ночью.")
        else:
            host = ask_ai_host(
                "Тихая ночь. Никто не погиб. Объяви — с угрозой. 1 предложение.",
                chat_id=_lid
            )
            _maf_send_all(_lid, f"☀️ УТРО\n\n🎭 Ведущий: {host}\n\nНикто не погиб.")

        g2["night_actions"] = {}
        winner = _maf_check_win(_lid)
        if winner:
            _maf_end(_lid, winner)
            return
        time.sleep(2)
        _maf_day(_lid)

    _pool.submit(_morning)


# ─── Победа / конец ────────────────────────────────────────

def _maf_check_win(lobby_id: int):
    g = _maf.get(lobby_id)
    if not g:
        return None
    alive = g["alive"]
    roles = g["roles"]
    mafia_a = [p for p in alive if roles.get(p) == "мафия"]
    maniac_a = [p for p in alive if roles.get(p) == "маньяк"]
    others_a = [p for p in alive if roles.get(p) not in ("мафия","маньяк")]
    if not mafia_a and not maniac_a:
        return "мирные"
    if maniac_a and len(maniac_a) >= len([p for p in alive if p not in maniac_a]):
        return "маньяк"
    if mafia_a and len(mafia_a) >= len(others_a):
        return "мафия"
    return None


def _maf_end(lobby_id: int, winner: str):
    g = _maf.pop(lobby_id, None)
    if not g:
        return
    bots = g["bots"]
    is_group = _maf_is_group(g)

    # Убираем маппинг группы
    if is_group:
        _group_mafia.pop(g.get("chat_id"), None)

    # Очищаем игроков
    for uid in g["players"]:
        _maf_uid.pop(uid, None)

    roles_all = "\n".join(
        f"  👤 {g['player_names'].get(uid,'?')} — {role}"
        for uid, role in g["roles"].items()
    )
    win_text = {
        "мирные": "🎉 МИРНЫЕ ПОБЕДИЛИ!\nМафия уничтожена!",
        "мафия":  "🔫 МАФИЯ ПОБЕДИЛА!\nГород во тьме.",
        "маньяк": "🔪 МАНЬЯК ПОБЕДИЛ!\nВсе пали его жертвами.",
    }.get(winner, "Игра завершена.")

    finale = ask_ai_host(
        f"Конец игры. Победители: {winner}. Финальный монолог — мрачно, как тёмный судья. 2-3 предложения.",
        chat_id=lobby_id
    )

    final_msg = (
        f"{win_text}\n\n"
        f"🎭 Ведущий: {finale}\n\n"
        f"📋 Все роли:\n{roles_all}"
    )

    if is_group:
        send_group(g["chat_id"], final_msg)
    else:
        for uid in g["players"]:
            if uid in bots:
                continue
            u = U(uid)
            try:
                send(uid, final_msg, kb=KB(u.get("stage", 0)))
            except Exception:
                pass


# ─── Обработка текста игрока в ЛС ──────────────────────────

def maf_proc_dm(uid: int, text: str) -> bool:
    """Обрабатывает сообщение игрока в ЛС мафии. True если поглощено."""
    lid = _maf_uid.get(uid)
    if not lid:
        return False
    g = _maf.get(lid)
    if not g or _maf_is_group(g):
        return False

    tl = text.strip().lower()

    # Выход
    if tl in ("/leavem", "выйти из мафии", "/stopm"):
        _maf_uid.pop(uid, None)
        name = g["player_names"].get(uid, "?")
        if uid in g["players"]:
            g["players"].remove(uid)
        if uid in g["alive"]:
            g["alive"].remove(uid)
            _maf_send_all(lid, f"⚠️ {name} покинул игру.")
            winner = _maf_check_win(lid)
            if winner:
                _maf_end(lid, winner)
        u = U(uid)
        _maf_send_one(uid, "Ты вышел из мафии.", kb=KB(u.get("stage", 0)))
        return True

    # Чат во время игры (не команды)
    if g["state"] == "playing" and uid in g["alive"] and not tl.startswith("/"):
        # Сбрасываем режим ИИ-диалога пока идёт мафия (он перехватил бы чат)
        U(uid)["ai_mode"] = False
        _maf_chat_broadcast(lid, uid, text)
        return True

    return False


# ─── ИИ-АТАКА (для админа) ─────────────────────────────────

_ai_scare_active: dict = {}  # uid → True (жертвы под ИИ-атакой)


def start_ai_scare(target_uid: int):
    """Запускает ИИ-атаку на жертву. Пишет жутко, отвечает на ответы."""
    _ai_scare_active[target_uid] = True
    u = U(target_uid)
    name = u.get("name") or "ты"
    city = u.get("city") or ""
    city_hint = f" Ты живёшь в {city}." if city else ""

    def _scare_loop(_uid=target_uid, _name=name):
        # Первые 3 волны — без ответа пользователя
        openers = [
            f"Напиши жертве по имени '{_name}' жуткое первое сообщение. "
            f"Намекни что следишь.{city_hint} 1-2 предложения.",

            f"Продолжай пугать '{_name}'. Упомяни что знаешь её действия. "
            f"Будь загадочным. 1 предложение.",

            f"Напиши '{_name}' — финальный жуткий намёк. "
            f"Скажи что видишь её прямо сейчас. 1 предложение.",
        ]
        for prompt in openers:
            if not _ai_scare_active.get(_uid):
                return
            msg = ask_ai(prompt, chat_id=_uid)
            _maf_send_one(_uid, f"👁 {msg}")
            time.sleep(random.uniform(12, 25))

    _pool.submit(_scare_loop)


def stop_ai_scare(target_uid: int):
    _ai_scare_active.pop(target_uid, None)


def maf_ai_scare_reply(uid: int, text: str) -> bool:
    """Если жертва под ИИ-атакой — иногда отвечает. True если поглощено."""
    if not _ai_scare_active.get(uid):
        return False
    # Отвечает с вероятностью ~40%
    if random.random() > 0.40:
        return False
    u = U(uid)
    name = u.get("name") or "ты"

    def _reply(_t=text, _uid=uid, _name=name):
        time.sleep(random.uniform(3, 10))
        if not _ai_scare_active.get(_uid):
            return
        answer = ask_ai_host(
                f"Жертва по имени '{_name}' ответила мне: '{_t[:100]}'. "
            f"Ответь жутко, загадочно, намекни что это всё видишь. 1-2 предложения.",
                chat_id=_uid
            )
        _maf_send_one(_uid, f"👁 {answer}")
    _pool.submit(_reply)
    return True

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

    # Выход из истории
    if text == "❌ Выйти из истории":
        del _card_story[uid]
        u = U(uid)
        send(uid, "История прервана.", kb=KB(u.get("stage", 0)))
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

    # Выход из истории
    if text == "❌ Выйти из истории":
        _group_card_story.pop(chat_id, None)
        send_group(chat_id, "История прервана.", kb=group_reply_kb())
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

    if gm == "ai_story":
        return proc_group_ai_story(chat_id, uid, text)

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
    print("║     👁  HORROR BOT v19.0 ЗАПУЩЕН  👁     ║")
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

# ══════════════════════════════════════════════════════════════
#  v19: КАРТОЧНАЯ ИСТОРИЯ С ИИ-СЮЖЕТОМ ДЛЯ ГРУППЫ
#  ИИ сам придумывает каждую сцену. Игра конечная — 5-7 глав.
# ══════════════════════════════════════════════════════════════

_AI_STORY_MAX_CHAPTERS = 6  # максимум глав

def start_group_ai_story(chat_id):
    """Запускает карточную историю с ИИ-сюжетом для группы."""
    if chat_id in _group_games:
        send_group(chat_id, "⚠️ Сначала заверши текущую игру.")
        return
    _group_games[chat_id] = {
        "game": "ai_story",
        "state": "genre_select",
        "chapter": 0,
        "max_chapters": _AI_STORY_MAX_CHAPTERS,
        "players": {},       # uid → character_name
        "votes": {},         # uid → choice_text
        "story_so_far": [],  # краткие описания глав
        "genre": None,
    }
    kb = InlineKeyboardMarkup(row_width=2)
    genres = [
        ("👁 Хоррор", "horror"),
        ("🔍 Детектив", "detective"),
        ("🧙 Фэнтези", "fantasy"),
        ("🚀 Sci-Fi", "scifi"),
        ("🌑 Мистика", "mystery"),
        ("💀 Апокалипсис", "apocalypse"),
    ]
    for label, gid in genres:
        kb.add(InlineKeyboardButton(label, callback_data=f"aisg_{chat_id}_{gid}"))
    send_group(chat_id,
        "📖 КАРТОЧНАЯ ИСТОРИЯ С ИИ-СЮЖЕТОМ\\n\\n"
        "ИИ будет придумывать историю по ходу игры на основе ваших выборов.\\n"
        f"Игра рассчитана на {_AI_STORY_MAX_CHAPTERS} глав.\\n\\n"
        "Выберите жанр:",
        kb=kb
    )


def _generate_ai_story_scene(chat_id, genre, story_so_far, chapter, max_chapters, choice_made=None):
    """Генерирует сцену через ИИ. Возвращает (scene_text, choices_list)."""
    g = _group_games.get(chat_id)
    players_desc = ""
    if g:
        names = list(g.get("players", {}).values())
        if names:
            players_desc = f"Главные герои: {', '.join(names[:4])}. "

    history = " → ".join(story_so_far[-3:]) if story_so_far else "Начало истории."
    choice_context = f"Игроки выбрали: {choice_made}. " if choice_made else ""

    genre_prompts = {
        "horror": "хоррор, страх, жуть, паранормальное",
        "detective": "детектив, расследование, улики, подозреваемые",
        "fantasy": "фэнтези, магия, приключения, монстры",
        "scifi": "научная фантастика, технологии, космос, будущее",
        "mystery": "мистика, тайны, загадки, сверхъестественное",
        "apocalypse": "постапокалипсис, выживание, опасность, мрак",
    }
    genre_hint = genre_prompts.get(genre, "приключение")

    is_final = (chapter >= max_chapters - 1)
    final_hint = "Это ФИНАЛЬНАЯ глава. Заверши историю ярко." if is_final else f"Это глава {chapter+1} из {max_chapters}."

    prompt = (
        f"Ты ведущий интерактивной истории в жанре: {genre_hint}. "
        f"{players_desc}"
        f"История до этого: {history}. "
        f"{choice_context}"
        f"{final_hint} "
        f"Напиши сцену (3-4 предложения) и {'заверши историю эпично.' if is_final else 'предложи РОВНО 3 варианта выбора для игроков (каждый 3-5 слов). Формат: СЦЕНА: [текст] ВЫБОРЫ: 1.[вариант] 2.[вариант] 3.[вариант]'}"
    )

    raw = ask_ai(prompt, chat_id=chat_id)

    if is_final:
        return raw, []

    # Парсим варианты
    scene_text = raw
    choices = []
    if "ВЫБОРЫ:" in raw:
        parts = raw.split("ВЫБОРЫ:", 1)
        scene_text = parts[0].replace("СЦЕНА:", "").strip()
        choices_raw = parts[1].strip()
        for line in choices_raw.split("\n"):
            line = line.strip()
            if line and (line[0].isdigit() or line.startswith("-")):
                choice = line.lstrip("123456789.-) ").strip()
                if choice:
                    choices.append(choice)
    if not choices:
        choices = ["Идти вперёд", "Осмотреться", "Позвать на помощь"]

    return scene_text, choices[:3]


def _send_ai_story_scene(chat_id):
    """Генерирует и отправляет текущую сцену."""
    g = _group_games.get(chat_id)
    if not g or g.get("game") != "ai_story":
        return

    chapter = g.get("chapter", 0)
    max_ch = g.get("max_chapters", _AI_STORY_MAX_CHAPTERS)
    genre = g.get("genre", "mystery")
    story_so_far = g.get("story_so_far", [])
    choice_made = g.get("last_choice")

    scene_text, choices = _generate_ai_story_scene(
        chat_id, genre, story_so_far, chapter, max_ch, choice_made
    )

    g["current_choices"] = choices
    g["votes"] = {}
    g["last_choice"] = None

    is_final = (chapter >= max_ch - 1)

    if is_final:
        send_group(chat_id,
            f"📖 ГЛАВА {chapter+1} — ФИНАЛ\\n\\n"
            f"{scene_text}\\n\\n"
            f"🎭 Конец истории! Спасибо за игру.",
            kb=group_reply_kb()
        )
        if GROUP_AUTO_VOICE:
            _pool.submit(_send_group_voice, chat_id, "История завершена.")
        del _group_games[chat_id]
        return

    kb = InlineKeyboardMarkup(row_width=1)
    for i, ch in enumerate(choices):
        kb.add(InlineKeyboardButton(f"{'①②③'[i]} {ch}", callback_data=f"aisc_{chat_id}_{i}"))

    players_total = len(g.get("players", {})) or 1
    send_group(chat_id,
        f"📖 ГЛАВА {chapter+1}/{max_ch}\\n\\n"
        f"{scene_text}\\n\\n"
        f"🗳 Голосуй за следующий шаг (нужно большинство из {players_total}):",
        kb=kb
    )
    if GROUP_AUTO_VOICE:
        _pool.submit(_send_group_voice, chat_id, scene_text[:120])


def proc_group_ai_story(chat_id, uid, text):
    """Обрабатывает групповую историю с ИИ."""
    g = _group_games.get(chat_id)
    if not g or g.get("game") != "ai_story":
        return False
    if text in ("❌ Стоп", "❌ Выйти из игры"):
        del _group_games[chat_id]
        send_group(chat_id, "История прервана.", kb=group_reply_kb())
        return True
    return False


# ── Callback-обработчики для AI Story ───────────────────────

# (обрабатываются в on_callback, добавляем ниже)
