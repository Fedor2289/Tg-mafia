# 👁 Horror Bot v11.0

Telegram-бот с маскировкой под переводчик. Постепенно переходит в хоррор-режим.

## Структура проекта

```
horror_bot/
├── horror_bot_v10.py   # Основной файл бота
├── gifs/               # Гифки для скримеров (добавляйте любые .gif)
├── requirements.txt    # Зависимости Python
├── Procfile            # Команда запуска для Railway/Render
├── .env.example        # Пример переменных окружения
└── .gitignore
```

## Деплой на Railway

1. Создайте аккаунт на [railway.app](https://railway.app)
2. Нажмите **New Project → Deploy from GitHub repo**
3. Выберите этот репозиторий
4. Перейдите в **Variables** и добавьте:
   - `BOT_TOKEN` — токен от @BotFather
   - `WEATHER_API_KEY` — ключ от openweathermap.org (бесплатно)
   - `ADMIN_ID` — ваш числовой Telegram ID (узнать у @userinfobot)
5. Railway автоматически прочитает `Procfile` и запустит бота

## Деплой на Render

1. Создайте аккаунт на [render.com](https://render.com)
2. **New → Background Worker**
3. Подключите GitHub репозиторий
4. **Build Command:** `pip install -r requirements.txt`
5. **Start Command:** `python horror_bot_v10.py`
6. В разделе **Environment** добавьте те же 3 переменные

## Локальный запуск

```bash
# Установите зависимости
pip install -r requirements.txt

# Создайте .env файл
cp .env.example .env
# Заполните .env своими значениями

# Запуск
python horror_bot_v10.py
```

## Гифки

Папка `gifs/` — добавляйте любые `.gif` файлы, бот подхватит их автоматически без перезапуска.

## Команды бота

- `/start` — начать
- `/stop` — остановить хоррор
- `/score` — очки страха
- `/admingo` — режим администратора (только ADMIN_ID)
