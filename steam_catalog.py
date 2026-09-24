#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Steam UA/TR catalog builder
---------------------------
Что делает:
1) Проходит Steam Search и собирает AppID полноценных игр.
2) Получает цены для Украины (UA) и Турции (TR).
3) Отбрасывает Free-to-Play и, при желании, дешёвые игры/игры по рейтингу.
4) Для каждой выбранной игры получает список DLC.
5) Получает региональные цены DLC.
6) Каждый запуск ПОЛНОСТЬЮ пересоздаёт:
      steam_catalog.json
      steam_catalog_data.js
   HTML-файл не переписывается: он автоматически читает steam_catalog_data.js.

ВАЖНО:
- Store endpoints Steam не являются официально гарантированным публичным API.
- На первом полном запуске получение DLC для десятков тысяч игр может занять очень долго,
  поэтому статические metadata/DLC связи кешируются в .steam_meta_cache.json.
- ЦЕНЫ не берутся из metadata-кеша: при каждом НОВОМ запуске они обновляются заново.
- Этот вариант поддерживает checkpoint/resume. Во время работы прогресс сохраняется
  в папку .steam_resume.
- После сбоя/закрытия окна продолжение:
      py steam_catalog.py resume
  или:
      py steam_catalog.py --resume
- При resume уже завершённые страницы поиска, пачки цен, metadata и карточки
  повторно по сети не запрашиваются.
"""

from __future__ import annotations

import argparse
import html
import json
import math
import os
import re
import shutil
import sys
import time
import unicodedata
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path
from typing import Any, Iterable

import requests
from bs4 import BeautifulSoup

# =========================
# НАСТРОЙКИ
# =========================

BASE_DIR = Path(__file__).resolve().parent
OUTPUT_JSON = BASE_DIR / "steam_catalog.json"
OUTPUT_JS = BASE_DIR / "steam_catalog_data.js"
OUTPUT_DETAILS_JS = BASE_DIR / "steam_catalog_details.js"
META_CACHE = BASE_DIR / ".steam_meta_cache.json"
RESUME_DIR = BASE_DIR / ".steam_resume"
RESUME_STATE = RESUME_DIR / "state.json"

STEAM_SEARCH_URL = "https://store.steampowered.com/search/results/"
STEAM_APPDETAILS_URL = "https://store.steampowered.com/api/appdetails"
STEAM_APP_PAGE_URL = "https://store.steampowered.com/app/{appid}/"

REGIONS = {
    "UA": {"label": "Украина"},
    "TR": {"label": "Турция"},
}


# === PLAYBOX STEAM PRICE RULES (RUB) ===
# Украина Steam:
#   UAH / 43 * 90
#   +800 ₽ если исходная цена < 250 UAH
#   +1000 ₽ если исходная цена >= 250 UAH
#
# Турция Steam (Steam показывает цену в USD):
#   USD * 90
#   +800 ₽ если исходная цена < 9.99 USD
#   +1000 ₽ если исходная цена >= 9.99 USD
#
# После наценки: округление до ближайших 100 ₽.
# Остаток >= 50 ₽ -> вверх, остаток < 50 ₽ -> вниз.
UA_DIVISOR = Decimal("43")
STEAM_RUB_RATE = Decimal("90")
UA_MARKUP_THRESHOLD = Decimal("250")
TR_MARKUP_THRESHOLD_USD = Decimal("9.99")
MARKUP_LOW_RUB = Decimal("800")
MARKUP_HIGH_RUB = Decimal("1000")


def round_rubles_to_100(value: Decimal) -> int:
    lower = (int(value) // 100) * 100
    remainder = value - Decimal(lower)
    return lower + (100 if remainder >= Decimal("50") else 0)


def playbox_steam_rub_price(region: str, minor_units: int | None) -> int | None:
    """Convert Steam minor-unit source price to final Playbox RUB price."""
    if minor_units is None:
        return None

    amount = Decimal(int(minor_units)) / Decimal("100")
    if amount <= 0:
        return 0

    region = region.upper()
    if region == "UA":
        markup = MARKUP_LOW_RUB if amount < UA_MARKUP_THRESHOLD else MARKUP_HIGH_RUB
        rub = (amount / UA_DIVISOR) * STEAM_RUB_RATE + markup
    elif region == "TR":
        markup = MARKUP_LOW_RUB if amount < TR_MARKUP_THRESHOLD_USD else MARKUP_HIGH_RUB
        rub = amount * STEAM_RUB_RATE + markup
    else:
        raise ValueError(f"Неизвестный регион для расчёта цены: {region}")

    return round_rubles_to_100(rub)


def format_rub(value: int | None) -> str:
    if value is None:
        return "—"
    if value <= 0:
        return "Бесплатно"
    return f"{value:,}".replace(",", " ") + " ₽"


# Минимальная ОБЫЧНАЯ (до скидки) цена.
# Steam price_overview хранит цену в минимальных единицах валюты:
# 12000 UAH minor units = 120.00 UAH; 300 USD cents = $3.00.
# Изменяй значения при необходимости.
MIN_BASE_PRICE_MINOR = {
    "UAH": 12000,
    "USD": 300,
}

# None = не фильтровать по рейтингу.
# Например: 70 = оставлять игры с >= 70% положительных отзывов.
MIN_RATING_PERCENT: int | None = None
MIN_REVIEW_COUNT = 20

# Новые/неоценённые игры пропускать даже без рейтинга.
KEEP_UNRATED = True

# Бесплатные DLC обычно не нужны для магазина.
INCLUDE_FREE_DLC = False

# Добавлять бесплатные Steam-игры только если у них есть платные DLC
# или пакеты игровой валюты.
INCLUDE_F2P_WITH_PAID_CONTENT = True

# При полном запуске отдельно сканируется Steam Free to Play.
# В тесте --test-limit этот большой дополнительный проход не выполняется.
FREE_TO_PLAY_GENRE = "Free to Play"

# Размер страницы Steam Search.
SEARCH_PAGE_SIZE = 100

# Цены можно запрашивать пачками.
PRICE_BATCH_SIZE = 50

# Паузы. Не ставь 0 при полном сканировании.
SEARCH_DELAY = 0.35
PRICE_DELAY = 0.55
DETAIL_DELAY = 1.55

# Сколько раз повторять сетевой запрос при временной ошибке.
MAX_RETRIES = 5

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/153.0 Safari/537.36 PlayboxStoreCatalog/1.0"
)

# Steam Search: category1=998 = Games.
STEAM_GAMES_CATEGORY = "998"


@dataclass
class SearchGame:
    appid: int
    name: str
    image: str | None
    rating_percent: int | None
    reviews: int | None
    free_hint: bool = False


session = requests.Session()
session.headers.update({
    "User-Agent": USER_AGENT,
    "Accept-Language": "en-US,en;q=0.9",
})
# Помогает получать обычную store page даже у age-gated игр.
session.cookies.update({
    "birthtime": "568022401",
    "lastagecheckage": "1-January-1988",
    "wants_mature_content": "1",
})


def log(message: str) -> None:
    stamp = datetime.now().strftime("%H:%M:%S")
    print(f"[{stamp}] {message}", flush=True)


def request_json(url: str, params: dict[str, Any], delay: float = 0.0) -> Any:
    """GET JSON with retries and 429/5xx backoff."""
    last_error: Exception | None = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            r = session.get(url, params=params, timeout=40)
            if r.status_code == 429:
                last_error = RuntimeError("HTTP 429 Too Many Requests")
                wait = min(60, 5 * attempt)
                log(f"Steam вернул 429. Пауза {wait} сек.")
                time.sleep(wait)
                continue
            if 500 <= r.status_code < 600:
                last_error = RuntimeError(f"HTTP {r.status_code}")
                wait = min(30, 3 * attempt)
                log(f"Steam {r.status_code}. Повтор через {wait} сек.")
                time.sleep(wait)
                continue
            r.raise_for_status()
            data = r.json()
            if delay:
                time.sleep(delay)
            return data
        except Exception as e:
            last_error = e
            wait = min(30, 2 * attempt)
            log(f"Ошибка запроса ({attempt}/{MAX_RETRIES}): {e}")
            time.sleep(wait)
    raise RuntimeError(f"Steam request failed: {last_error}")


def chunks(items: list[int], size: int) -> Iterable[list[int]]:
    for i in range(0, len(items), size):
        yield items[i:i + size]



# =========================
# RESUME / CHECKPOINT
# =========================

RESUME_STAGES = [
    "paid_search",
    "f2p_search",
    "game_prices_ua",
    "game_prices_tr",
    "game_meta",
    "dlc_prices_ua",
    "dlc_prices_tr",
    "dlc_meta",
    "build_cards",
    "complete",
]


def _stage_index(stage: str) -> int:
    try:
        return RESUME_STAGES.index(stage)
    except ValueError:
        return -1


def _resume_file(name: str) -> Path:
    RESUME_DIR.mkdir(parents=True, exist_ok=True)
    return RESUME_DIR / name


def _atomic_write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    tmp.replace(path)


def _append_jsonl(path: Path, record: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(record, ensure_ascii=False, separators=(",", ":")) + "\n")
        f.flush()
        os.fsync(f.fileno())


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    out: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as f:
        for line_no, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                item = json.loads(line)
            except json.JSONDecodeError:
                # Если процесс оборвался ровно во время записи последней строки,
                # игнорируем только повреждённый хвост.
                log(f"Checkpoint: игнорирую незавершённую строку {path.name}:{line_no}")
                break
            if isinstance(item, dict):
                out.append(item)
    return out


def _save_resume_state(state: dict[str, Any]) -> None:
    _atomic_write_json(RESUME_STATE, state)


def _set_resume_stage(state: dict[str, Any], stage: str) -> None:
    state["stage"] = stage
    state["updated_at"] = datetime.now(timezone.utc).isoformat()
    _save_resume_state(state)
    log(f"Checkpoint: этап -> {stage}")


def _reset_resume_checkpoint() -> None:
    if RESUME_DIR.exists():
        shutil.rmtree(RESUME_DIR)


def _init_resume_state(
    test_limit: int | None,
    refresh_metadata: bool,
    alphabetical: bool,
) -> dict[str, Any]:
    _reset_resume_checkpoint()
    RESUME_DIR.mkdir(parents=True, exist_ok=True)
    state = {
        "version": 1,
        "stage": "paid_search",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "updated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "test_limit": test_limit,
            "refresh_metadata": bool(refresh_metadata),
            "alphabetical": bool(alphabetical),
        },
    }
    _save_resume_state(state)
    return state


def _load_resume_state() -> dict[str, Any]:
    if not RESUME_STATE.exists():
        raise RuntimeError(
            "Checkpoint для resume не найден. "
            "Сначала запусти обычный полный скан; после сбоя запускай: py steam_catalog.py resume"
        )
    try:
        state = json.loads(RESUME_STATE.read_text(encoding="utf-8"))
    except Exception as exc:
        raise RuntimeError(f"Checkpoint повреждён: {exc}") from exc
    if not isinstance(state, dict) or state.get("version") != 1:
        raise RuntimeError("Checkpoint имеет неизвестный формат.")
    return state


def _search_game_to_dict(game: SearchGame) -> dict[str, Any]:
    return {
        "appid": game.appid,
        "name": game.name,
        "image": game.image,
        "rating_percent": game.rating_percent,
        "reviews": game.reviews,
        "free_hint": game.free_hint,
    }


def _search_game_from_dict(data: dict[str, Any]) -> SearchGame:
    return SearchGame(
        appid=int(data["appid"]),
        name=str(data.get("name") or f"App {data['appid']}"),
        image=data.get("image"),
        rating_percent=data.get("rating_percent"),
        reviews=data.get("reviews"),
        free_hint=bool(data.get("free_hint")),
    )


def _load_search_pages(path: Path) -> tuple[dict[int, SearchGame], int, int | None]:
    found: dict[int, SearchGame] = {}
    next_start = 0
    total_count: int | None = None
    for rec in _read_jsonl(path):
        for raw in rec.get("games") or []:
            if isinstance(raw, dict):
                game = _search_game_from_dict(raw)
                found[game.appid] = game
        next_start = int(rec.get("next_start") or next_start)
        if rec.get("total_count") is not None:
            total_count = int(rec["total_count"])
    return found, next_start, total_count


def scan_all_games_resumable(
    state: dict[str, Any],
    test_limit: int | None = None,
    alphabetical: bool = False,
) -> list[SearchGame]:
    path = _resume_file("search_paid.jsonl")
    found, start, total_count = _load_search_pages(path)

    if _stage_index(str(state.get("stage"))) > _stage_index("paid_search"):
        return list(found.values())

    log(
        "Сканирую Steam Search: полноценные игры..."
        + (f" RESUME с позиции {start:,}" if start else "")
    )

    while True:
        params = {
            "query": "",
            "start": start,
            "count": SEARCH_PAGE_SIZE,
            "infinite": 1,
            "category1": STEAM_GAMES_CATEGORY,
            "hidef2p": 1,
            "cc": "UA",
            "l": "english",
        }
        if alphabetical:
            params["sort_by"] = "Name_ASC"

        payload = request_json(STEAM_SEARCH_URL, params, SEARCH_DELAY)
        results_html = payload.get("results_html") or ""
        if total_count is None:
            total_count = int(payload.get("total_count") or 0)
            log(f"Steam сообщает примерно {total_count:,} результатов.")

        soup = BeautifulSoup(results_html, "html.parser")
        rows = soup.select("a.search_result_row")
        if not rows:
            break

        page_games: list[dict[str, Any]] = []
        stop_now = False

        for row in rows:
            raw_appid = row.get("data-ds-appid")
            if not raw_appid:
                href = row.get("href", "")
                m = re.search(r"/app/(\d+)", href)
                raw_appid = m.group(1) if m else None
            if not raw_appid or not str(raw_appid).isdigit():
                continue

            appid = int(raw_appid)
            title_node = row.select_one(".title")
            name = title_node.get_text(" ", strip=True) if title_node else f"App {appid}"
            img_node = row.select_one(".search_capsule img")
            image = img_node.get("src") if img_node else None
            review_node = row.select_one(".search_review_summary")
            tooltip = review_node.get("data-tooltip-html") if review_node else None
            rating_percent, reviews = parse_review_tooltip(tooltip)
            price_node = row.select_one(".search_price, .discount_final_price")
            price_text = price_node.get_text(" ", strip=True) if price_node else ""
            free_hint = bool(re.search(r"\bFree\b|Бесплат", price_text, re.I))

            game = SearchGame(
                appid=appid,
                name=name,
                image=image,
                rating_percent=rating_percent,
                reviews=reviews,
                free_hint=free_hint,
            )
            found[appid] = game
            page_games.append(_search_game_to_dict(game))

            if test_limit and len(found) >= test_limit:
                stop_now = True
                break

        next_start = start + len(rows)
        _append_jsonl(path, {
            "next_start": next_start,
            "total_count": total_count,
            "games": page_games,
        })
        start = next_start

        log(f"Список игр: {len(found):,}" + (f" / {total_count:,}" if total_count else ""))

        if stop_now or (total_count and start >= total_count):
            break

    next_stage = "game_prices_ua" if (test_limit is not None or not INCLUDE_F2P_WITH_PAID_CONTENT) else "f2p_search"
    _set_resume_stage(state, next_stage)
    return list(found.values())


def scan_free_to_play_games_resumable(state: dict[str, Any]) -> list[SearchGame]:
    path = _resume_file("search_f2p.jsonl")
    found, start, total_count = _load_search_pages(path)

    if _stage_index(str(state.get("stage"))) > _stage_index("f2p_search"):
        return list(found.values())

    log(
        "Сканирую Steam Free to Play для платного DLC/валюты..."
        + (f" RESUME с позиции {start:,}" if start else "")
    )

    while True:
        params = {
            "query": "",
            "start": start,
            "count": SEARCH_PAGE_SIZE,
            "infinite": 1,
            "category1": STEAM_GAMES_CATEGORY,
            "genre": FREE_TO_PLAY_GENRE,
            "cc": "UA",
            "l": "english",
        }

        payload = request_json(STEAM_SEARCH_URL, params, SEARCH_DELAY)
        results_html = payload.get("results_html") or ""

        if total_count is None:
            total_count = int(payload.get("total_count") or 0)
            log(f"Free to Play результатов: примерно {total_count:,}")

        soup = BeautifulSoup(results_html, "html.parser")
        rows = soup.select("a.search_result_row")
        if not rows:
            break

        page_games: list[dict[str, Any]] = []
        for row in rows:
            raw_appid = row.get("data-ds-appid")
            if not raw_appid:
                href = row.get("href", "")
                m = re.search(r"/app/(\d+)", href)
                raw_appid = m.group(1) if m else None
            if not raw_appid or not str(raw_appid).isdigit():
                continue

            price_node = row.select_one(".search_price, .discount_final_price")
            price_text = price_node.get_text(" ", strip=True) if price_node else ""
            if not re.search(r"\bFree\b|Бесплат", price_text, re.I):
                continue

            appid = int(raw_appid)
            title_node = row.select_one(".title")
            name = title_node.get_text(" ", strip=True) if title_node else f"App {appid}"
            img_node = row.select_one(".search_capsule img")
            image = img_node.get("src") if img_node else None
            review_node = row.select_one(".search_review_summary")
            tooltip = review_node.get("data-tooltip-html") if review_node else None
            rating_percent, reviews = parse_review_tooltip(tooltip)

            game = SearchGame(
                appid=appid,
                name=name,
                image=image,
                rating_percent=rating_percent,
                reviews=reviews,
                free_hint=True,
            )
            found[appid] = game
            page_games.append(_search_game_to_dict(game))

        next_start = start + len(rows)
        _append_jsonl(path, {
            "next_start": next_start,
            "total_count": total_count,
            "games": page_games,
        })
        start = next_start

        log(f"Free to Play список: {len(found):,}" + (f" / {total_count:,}" if total_count else ""))

        if total_count and start >= total_count:
            break

    _set_resume_stage(state, "game_prices_ua")
    return list(found.values())


def _load_price_batches(path: Path) -> tuple[dict[int, dict[str, Any] | None], int]:
    output: dict[int, dict[str, Any] | None] = {}
    completed = 0
    for rec in _read_jsonl(path):
        batch_index = int(rec.get("batch_index") or 0)
        completed = max(completed, batch_index)
        results = rec.get("results") or {}
        if isinstance(results, dict):
            for appid, price in results.items():
                output[int(appid)] = price if isinstance(price, dict) else None
    return output, completed


def get_prices_batched_resumable(
    appids: list[int],
    region: str,
    state: dict[str, Any],
    stage_name: str,
    next_stage: str,
    file_name: str,
) -> dict[int, dict[str, Any] | None]:
    path = _resume_file(file_name)
    output, completed_batches = _load_price_batches(path)
    batches = list(chunks(appids, PRICE_BATCH_SIZE))

    if _stage_index(str(state.get("stage"))) > _stage_index(stage_name):
        return output

    if completed_batches:
        log(
            f"Цены {region}: RESUME с пачки {completed_batches + 1}/{len(batches)} "
            f"(готово {completed_batches})"
        )

    for idx, batch in enumerate(batches, 1):
        if idx <= completed_batches:
            continue

        params = {
            "appids": ",".join(map(str, batch)),
            "cc": region,
            "l": "english",
            "filters": "price_overview",
        }

        # В resume-версии не помечаем целую пачку как "нет цены", если Steam
        # временно недоступен. Ошибка прерывает запуск, а checkpoint остаётся.
        payload = request_json(STEAM_APPDETAILS_URL, params, PRICE_DELAY)
        if not isinstance(payload, dict):
            raise RuntimeError(
                f"Steam вернул некорректный ответ для пачки цен {region} {idx}/{len(batches)}"
            )

        batch_results: dict[str, Any] = {}
        for appid in batch:
            item = payload.get(str(appid)) or {}
            if not item.get("success"):
                price = None
            else:
                data = item.get("data") or {}
                price = normalize_price(data.get("price_overview"))
            output[appid] = price
            batch_results[str(appid)] = price

        _append_jsonl(path, {
            "batch_index": idx,
            "results": batch_results,
        })

        if idx % 25 == 0 or idx == len(batches):
            log(f"Цены {region}: пачка {idx}/{len(batches)}")

    _set_resume_stage(state, next_stage)
    return output


def _load_done_map(path: Path) -> dict[int, dict[str, Any]]:
    out: dict[int, dict[str, Any]] = {}
    for rec in _read_jsonl(path):
        try:
            appid = int(rec["appid"])
        except Exception:
            continue
        out[appid] = rec
    return out


def parse_int(text: str | None) -> int | None:
    if not text:
        return None
    digits = re.sub(r"[^\d]", "", text)
    return int(digits) if digits else None


def parse_review_tooltip(tooltip: str | None) -> tuple[int | None, int | None]:
    """
    Обычно tooltip выглядит примерно:
      Very Positive<br>92% of the 12,345 user reviews...
    """
    if not tooltip:
        return None, None
    plain = html.unescape(re.sub(r"<[^>]+>", " ", tooltip))
    m_pct = re.search(r"(\d{1,3})\s*%", plain)
    pct = int(m_pct.group(1)) if m_pct else None

    m_reviews = re.search(r"([\d,\s.]+)\s+user reviews", plain, re.I)
    reviews = parse_int(m_reviews.group(1)) if m_reviews else None
    return pct, reviews


def scan_all_games(test_limit: int | None = None, alphabetical: bool = False) -> list[SearchGame]:
    """
    Собирает полный список игр через Steam Search.
    hidef2p=1 дополнительно просит Steam скрыть F2P.
    """
    log("Сканирую Steam Search: полноценные игры...")
    found: dict[int, SearchGame] = {}
    start = 0
    total_count: int | None = None

    while True:
        params = {
            "query": "",
            "start": start,
            "count": SEARCH_PAGE_SIZE,
            "infinite": 1,
            "category1": STEAM_GAMES_CATEGORY,
            "hidef2p": 1,
            "cc": "UA",
            "l": "english",
        }
        if alphabetical:
            # Steam Search supports alphabetical name sorting.
            params["sort_by"] = "Name_ASC"
        payload = request_json(STEAM_SEARCH_URL, params, SEARCH_DELAY)
        results_html = payload.get("results_html") or ""
        if total_count is None:
            total_count = int(payload.get("total_count") or 0)
            log(f"Steam сообщает примерно {total_count:,} результатов.")

        soup = BeautifulSoup(results_html, "html.parser")
        rows = soup.select("a.search_result_row")
        if not rows:
            break

        for row in rows:
            raw_appid = row.get("data-ds-appid")
            if not raw_appid:
                href = row.get("href", "")
                m = re.search(r"/app/(\d+)", href)
                raw_appid = m.group(1) if m else None
            if not raw_appid or not str(raw_appid).isdigit():
                continue

            appid = int(raw_appid)
            title_node = row.select_one(".title")
            name = title_node.get_text(" ", strip=True) if title_node else f"App {appid}"

            img_node = row.select_one(".search_capsule img")
            image = img_node.get("src") if img_node else None

            review_node = row.select_one(".search_review_summary")
            tooltip = review_node.get("data-tooltip-html") if review_node else None
            rating_percent, reviews = parse_review_tooltip(tooltip)

            price_node = row.select_one(".search_price, .discount_final_price")
            price_text = price_node.get_text(" ", strip=True) if price_node else ""
            free_hint = bool(re.search(r"\bFree\b|Бесплат", price_text, re.I))

            found[appid] = SearchGame(
                appid=appid,
                name=name,
                image=image,
                rating_percent=rating_percent,
                reviews=reviews,
                free_hint=free_hint,
            )

            if test_limit and len(found) >= test_limit:
                log(f"TEST LIMIT: собрано {len(found)} игр.")
                return list(found.values())

        start += len(rows)
        log(f"Список игр: {len(found):,}" + (f" / {total_count:,}" if total_count else ""))

        if total_count and start >= total_count:
            break

    return list(found.values())



def scan_free_to_play_games(limit: int | None = None) -> list[SearchGame]:
    """
    Отдельно получает Steam Free to Play.
    Нужен, потому что основной paid-проход использует hidef2p=1.
    В итог попадут только F2P, у которых позже реально найдётся
    платный DLC или игровая валюта.
    """
    log("Сканирую Steam Free to Play для платного DLC/валюты...")
    found: dict[int, SearchGame] = {}
    start = 0
    total_count: int | None = None

    while True:
        params = {
            "query": "",
            "start": start,
            "count": SEARCH_PAGE_SIZE,
            "infinite": 1,
            "category1": STEAM_GAMES_CATEGORY,
            "genre": FREE_TO_PLAY_GENRE,
            "cc": "UA",
            "l": "english",
        }
        payload = request_json(STEAM_SEARCH_URL, params, SEARCH_DELAY)
        results_html = payload.get("results_html") or ""

        if total_count is None:
            total_count = int(payload.get("total_count") or 0)
            log(f"Free to Play результатов: примерно {total_count:,}")

        soup = BeautifulSoup(results_html, "html.parser")
        rows = soup.select("a.search_result_row")
        if not rows:
            break

        for row in rows:
            raw_appid = row.get("data-ds-appid")
            if not raw_appid:
                href = row.get("href", "")
                m = re.search(r"/app/(\\d+)", href)
                raw_appid = m.group(1) if m else None
            if not raw_appid or not str(raw_appid).isdigit():
                continue

            price_node = row.select_one(".search_price, .discount_final_price")
            price_text = price_node.get_text(" ", strip=True) if price_node else ""
            if not re.search(r"\\bFree\\b|Бесплат", price_text, re.I):
                # В жанровой выдаче иногда встречаются платные DLC/пакеты.
                continue

            appid = int(raw_appid)
            title_node = row.select_one(".title")
            name = title_node.get_text(" ", strip=True) if title_node else f"App {appid}"

            img_node = row.select_one(".search_capsule img")
            image = img_node.get("src") if img_node else None

            review_node = row.select_one(".search_review_summary")
            tooltip = review_node.get("data-tooltip-html") if review_node else None
            rating_percent, reviews = parse_review_tooltip(tooltip)

            found[appid] = SearchGame(
                appid=appid,
                name=name,
                image=image,
                rating_percent=rating_percent,
                reviews=reviews,
                free_hint=True,
            )

            if limit and len(found) >= limit:
                return list(found.values())

        start += len(rows)
        log(f"Free to Play список: {len(found):,}" + (f" / {total_count:,}" if total_count else ""))

        if total_count and start >= total_count:
            break

    return list(found.values())



def normalize_price(block: dict[str, Any] | None) -> dict[str, Any] | None:
    if not block:
        return None
    currency = block.get("currency")
    initial = block.get("initial")
    final = block.get("final")
    if currency is None or initial is None or final is None:
        return None
    return {
        "currency": currency,
        "initial": int(initial),
        "final": int(final),
        "discount_percent": int(block.get("discount_percent") or 0),
        "initial_formatted": block.get("initial_formatted"),
        "final_formatted": block.get("final_formatted"),
    }


def get_prices_batched(appids: list[int], region: str) -> dict[int, dict[str, Any] | None]:
    """
    Получает только price_overview пачками.
    Это существенно быстрее, чем appdetails по одной игре.
    """
    output: dict[int, dict[str, Any] | None] = {}
    batches = list(chunks(appids, PRICE_BATCH_SIZE))
    for idx, batch in enumerate(batches, 1):
        params = {
            "appids": ",".join(map(str, batch)),
            "cc": region,
            "l": "english",
            "filters": "price_overview",
        }
        try:
            payload = request_json(STEAM_APPDETAILS_URL, params, PRICE_DELAY)
        except Exception as e:
            log(f"Пачка цен {region} не получена: {e}")
            for appid in batch:
                output[appid] = None
            continue

        if not isinstance(payload, dict):
            for appid in batch:
                output[appid] = None
            continue

        for appid in batch:
            item = payload.get(str(appid)) or {}
            if not item.get("success"):
                output[appid] = None
                continue
            data = item.get("data") or {}
            output[appid] = normalize_price(data.get("price_overview"))

        if idx % 25 == 0 or idx == len(batches):
            log(f"Цены {region}: пачка {idx}/{len(batches)}")

    return output


def price_passes_threshold(price: dict[str, Any] | None) -> bool:
    if not price:
        return False
    currency = price.get("currency")
    initial = int(price.get("initial") or 0)
    threshold = MIN_BASE_PRICE_MINOR.get(currency)
    if threshold is None:
        # Неизвестную валюту не выбрасываем автоматически.
        return initial > 0
    return initial >= threshold


def rating_passes(game: SearchGame) -> bool:
    if MIN_RATING_PERCENT is None:
        return True
    if game.rating_percent is None or game.reviews is None:
        return KEEP_UNRATED
    if game.reviews < MIN_REVIEW_COUNT:
        return KEEP_UNRATED
    return game.rating_percent >= MIN_RATING_PERCENT



def parse_supported_languages(value: str | None) -> dict[str, Any]:
    """
    appdetails.supported_languages содержит HTML-строку.
    Steam помечает <strong>*</strong> языки с Full Audio.
    Эта строка НЕ позволяет надёжно определить Subtitles отдельно.
    """
    raw = str(value or "")
    soup = BeautifulSoup(raw, "html.parser")
    plain = soup.get_text(" ", strip=True)

    russian_supported = bool(re.search(r"\bRussian\b|Русск", plain, re.I))
    russian_full_audio = False

    # Ищем звёздочку, привязанную именно к Russian.
    # Типичный Steam формат: Russian<strong>*</strong>, ...
    if russian_supported:
        russian_full_audio = bool(
            re.search(
                r"(?:Russian|Русск[^,<]*)\s*(?:<strong>\s*\*\s*</strong>|<b>\s*\*\s*</b>)",
                raw,
                re.I,
            )
        )

    return {
        "raw": raw,
        "russian_supported": russian_supported,
        "russian_full_audio": russian_full_audio,
    }


def _cell_checked(cell: Any) -> bool:
    if cell is None:
        return False
    if cell.select_one(".checkmark") is not None:
        return True
    text = cell.get_text(" ", strip=True).lower()
    return text in {"✔", "✓", "yes", "да"}


def fetch_russian_language_details(
    appid: int,
    cache: dict[str, Any],
    fallback_supported_languages: str | None = None,
    force: bool = False,
) -> dict[str, Any]:
    """
    Пытается прочитать официальную таблицу Languages на странице Steam:
    Interface / Full Audio / Subtitles.

    Запрос страницы делается ТОЛЬКО если appdetails уже говорит,
    что Russian вообще присутствует. Результат кешируется.
    """
    fallback = parse_supported_languages(fallback_supported_languages)
    result = {
        "supported": bool(fallback["russian_supported"]),
        "interface": None,
        "full_audio": bool(fallback["russian_full_audio"]) if fallback["russian_supported"] else False,
        "subtitles": None,
        "source": "appdetails",
    }

    if not fallback["russian_supported"]:
        return result

    lang_cache = cache.setdefault("language_details", {})
    key = str(appid)
    if key in lang_cache and not force:
        cached = lang_cache[key]
        if isinstance(cached, dict):
            return cached

    url = STEAM_APP_PAGE_URL.format(appid=appid)
    try:
        r = session.get(
            url,
            params={"cc": "UA", "l": "english"},
            timeout=40,
            allow_redirects=True,
        )
        if r.status_code == 429:
            log(f"Steam 429 при проверке языка AppID {appid}; использую appdetails.")
            return result
        r.raise_for_status()

        soup = BeautifulSoup(r.text, "html.parser")
        table = soup.select_one("table.game_language_options")
        if table:
            russian_row = None
            for row in table.select("tr"):
                cells = row.find_all(["td", "th"])
                if not cells:
                    continue
                lang_name = cells[0].get_text(" ", strip=True)
                if re.search(r"\bRussian\b|Русск", lang_name, re.I):
                    russian_row = cells
                    break

            if russian_row and len(russian_row) >= 4:
                result = {
                    "supported": True,
                    "interface": _cell_checked(russian_row[1]),
                    "full_audio": _cell_checked(russian_row[2]),
                    "subtitles": _cell_checked(russian_row[3]),
                    "source": "store_page",
                }

        time.sleep(0.35)
    except Exception as e:
        log(f"Язык AppID {appid}: не удалось прочитать store page ({e}); fallback appdetails.")

    lang_cache[key] = result
    return result


def russian_label(details: dict[str, Any] | None) -> str:
    d = details or {}
    if not d.get("supported"):
        return "Русского языка нет"
    if d.get("full_audio") is True:
        return "Рус (Озвучка)"
    if d.get("subtitles") is True:
        return "Рус (Субтитры)"
    return "Русский язык"


def russian_status_class(details: dict[str, Any] | None) -> str:
    """
    Класс отображения русского языка в HTML:
    ru    -> русский есть, зелёный статус;
    no-ru -> русского нет, красный статус.
    """
    return "ru" if (details or {}).get("supported") else "no-ru"



def load_cache() -> dict[str, Any]:
    if not META_CACHE.exists():
        return {"apps": {}}
    try:
        return json.loads(META_CACHE.read_text(encoding="utf-8"))
    except Exception:
        return {"apps": {}}


def save_cache(cache: dict[str, Any]) -> None:
    tmp = META_CACHE.with_suffix(".tmp")
    tmp.write_text(
        json.dumps(cache, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    tmp.replace(META_CACHE)


def fetch_app_metadata(appid: int, cache: dict[str, Any], force: bool = False) -> dict[str, Any] | None:
    """
    Полные details нужны в основном для связи game -> DLC.
    Статика кешируется; цены сюда не сохраняются.
    """
    key = str(appid)
    cached = (cache.get("apps") or {}).get(key)
    if cached and not force:
        # Старый кеш мог быть создан до добавления genres/languages.
        if (
            "genres" in cached
            and "supported_languages" in cached
            and "package_groups" in cached
            and "categories" in cached
            and "short_description" in cached
        ):
            return cached

    params = {
        "appids": appid,
        "cc": "UA",
        "l": "english",
    }

    try:
        payload = request_json(STEAM_APPDETAILS_URL, params, DETAIL_DELAY)
        item = (payload or {}).get(key) or {}
        if not item.get("success"):
            return None
        data = item.get("data") or {}
    except Exception as e:
        log(f"Не удалось получить metadata {appid}: {e}")
        raise RuntimeError(f"Metadata AppID {appid} не получена: {e}") from e

    fullgame = data.get("fullgame") or {}
    release = data.get("release_date") or {}

    meta = {
        "appid": appid,
        "type": data.get("type"),
        "name": data.get("name"),
        "header_image": data.get("header_image"),
        "capsule_image": data.get("capsule_image"),
        "is_free": bool(data.get("is_free")),
        "dlc": [int(x) for x in (data.get("dlc") or []) if str(x).isdigit()],
        "fullgame_appid": int(fullgame["appid"]) if str(fullgame.get("appid", "")).isdigit() else None,
        "release_date": release.get("date"),
        "coming_soon": bool(release.get("coming_soon")),
        "genres": [
            str(x.get("description") or "").strip()
            for x in (data.get("genres") or [])
            if isinstance(x, dict) and str(x.get("description") or "").strip()
        ],
        "supported_languages": str(data.get("supported_languages") or ""),
        "short_description": str(data.get("short_description") or ""),
        "about_the_game": str(data.get("about_the_game") or ""),
        "categories": [
            str(x.get("description") or "").strip()
            for x in (data.get("categories") or [])
            if isinstance(x, dict) and str(x.get("description") or "").strip()
        ],
        # package_groups содержит варианты покупки одного AppID
        # (например 500 / 1050 / 1600 FC Points).
        "package_groups": data.get("package_groups") or [],
        "updated_at": datetime.now(timezone.utc).isoformat(),
    }

    cache.setdefault("apps", {})[key] = meta
    return meta




# Строгие признаки игровой валюты.
# ВАЖНО: обычные слова "point", "credit", "token" в описании DLC больше
# не считаются достаточным признаком — это и давало ложные кнопки валюты.
BRANDED_CURRENCY_RE = re.compile(
    r"""
    \b(
        fc\s*points?|fifa\s*points?|
        cod\s*points?|call\s+of\s+duty\s+points?|
        v[\s-]*bucks?|minecoins?|robux|
        apex\s+coins?|helix\s+credits?|r6\s+credits?|
        virtual\s+currency|in[\s-]*game\s+currency
    )\b
    """,
    re.I | re.X,
)

GENERIC_CURRENCY_UNIT_RE = re.compile(
    r"""
    \b(
        points?|coins?|credits?|tokens?|gems?|crystals?|
        shards?|diamonds?|platinum|vc
    )\b
    """,
    re.I | re.X,
)

CURRENCY_AMOUNT_RE = re.compile(
    r"""
    (?:
        \b\d[\d\s.,]*\s*
        (?:points?|coins?|credits?|tokens?|gems?|crystals?|shards?|diamonds?|platinum|vc)\b
        |
        \b(?:points?|coins?|credits?|tokens?|gems?|crystals?|shards?|diamonds?|platinum|vc)
        \s*[x×:]?\s*\d[\d\s.,]*\b
    )
    """,
    re.I | re.X,
)


def plain_text(value: Any) -> str:
    return BeautifulSoup(str(value or ""), "html.parser").get_text(" ", strip=True)


def looks_like_currency_purchase_text(value: str | None) -> bool:
    """
    Проверяет НАЗВАНИЕ товара/варианта покупки, а не сюжетное описание.
    Поэтому "earn points in a match" больше не превращает DLC в валюту.
    """
    text = plain_text(value)
    if not text:
        return False
    if BRANDED_CURRENCY_RE.search(text):
        return True
    if CURRENCY_AMOUNT_RE.search(text):
        return True
    return False


def currency_group_identity(group: dict[str, Any] | None) -> str:
    group = group or {}
    name = normalize_search_text(str(group.get("name") or ""))
    title = normalize_search_text(str(group.get("title") or ""))
    # "default" встречается у отдельного DLC валюты, поэтому в этом
    # случае идентификатор строим по title.
    if name and name not in {"default", "purchase", "purchases"}:
        return name
    return title or name or "currency"


def is_currency_package_group(group: dict[str, Any] | None) -> bool:
    """
    Определяет именно Steam purchase group с игровой валютой.
    Например у EA SPORTS FC 27 группа name=FCPoints.
    """
    if not isinstance(group, dict):
        return False

    header = " ".join([
        str(group.get("name") or ""),
        str(group.get("title") or ""),
        str(group.get("selection_text") or ""),
    ])
    if BRANDED_CURRENCY_RE.search(plain_text(header)):
        return True

    subs = [x for x in (group.get("subs") or []) if isinstance(x, dict)]
    if not subs:
        return False

    matched = sum(
        1 for sub in subs
        if looks_like_currency_purchase_text(str(sub.get("option_text") or ""))
    )
    # Для generic-названий вроде "500 Coins" требуем, чтобы большая часть
    # вариантов группы выглядела именно как пакеты валюты.
    required = max(1, math.ceil(len(subs) * 0.6))
    return matched >= required


def is_currency_meta(meta: dict[str, Any] | None) -> bool:
    """
    Строгая проверка отдельного DLC/AppID валюты.
    Не сканируем весь about_the_game на слова points/tokens/credits:
    именно это раньше давало ложные срабатывания на обычных DLC.
    """
    if not meta:
        return False

    name = plain_text(meta.get("name"))
    if looks_like_currency_purchase_text(name):
        return True

    groups = meta.get("package_groups") or []
    if any(is_currency_package_group(g) for g in groups if isinstance(g, dict)):
        return True

    # Резервный признак: Steam прямо называет DLC virtual currency.
    # Используем только явную фразу, а не отдельные слова point/token.
    desc = " ".join([
        plain_text(meta.get("short_description")),
        plain_text(meta.get("about_the_game")),
    ])
    categories = {str(x).casefold() for x in (meta.get("categories") or [])}
    return (
        meta.get("type") == "dlc"
        and "in-app purchases" in categories
        and bool(re.search(r"\b(?:virtual|in[\s-]*game)\s+currency\b", desc, re.I))
    )


def clean_package_option_name(text: str, fallback: str) -> str:
    text = plain_text(text)
    text = re.sub(r"\s+", " ", text).strip()
    if not text:
        return fallback

    # Убираем хвост с ценой: "... - 229₴", "... - $4.99", "... - 4,99 USD"
    text = re.sub(
        r"\s*[-–—]\s*(?:[$€£₴₺¥₽]\s*)?\d[\d\s.,]*(?:\s*(?:[$€£₴₺¥₽]|USD|UAH|TRY|TL|EUR|GBP))?\s*$",
        "",
        text,
        flags=re.I,
    ).strip()
    return text or fallback


def parse_display_price_minor(option_text: str | None, region: str) -> int | None:
    """
    Запасной разбор цены из option_text на случай, если Steam
    не прислал числовое поле package price.
    """
    text = plain_text(option_text)
    if not text:
        return None

    region = region.upper()
    if region == "UA":
        m = re.search(r"(\d[\d\s.,]*)\s*₴\s*$", text)
        if not m:
            return None
        number = m.group(1).replace(" ", "").replace(",", ".")
        try:
            return int((Decimal(number) * 100).quantize(Decimal("1"), rounding=ROUND_HALF_UP))
        except Exception:
            return None

    # Steam Turkey сейчас отдаёт MENA-USD.
    m = re.search(r"(?:\$\s*|USD\s*)(\d[\d\s.,]*)\s*$", text, re.I)
    if not m:
        m = re.search(r"(\d[\d\s.,]*)\s*(?:\$|USD)\s*$", text, re.I)
    if not m:
        return None
    number = m.group(1).replace(" ", "")
    # Для USD ожидаем decimal separator; на английской локали это точка.
    if "," in number and "." not in number:
        number = number.replace(",", ".")
    else:
        number = number.replace(",", "")
    try:
        return int((Decimal(number) * 100).quantize(Decimal("1"), rounding=ROUND_HALF_UP))
    except Exception:
        return None


def package_sub_to_price(sub: dict[str, Any], region: str) -> dict[str, Any] | None:
    """
    Steam package_groups в текущем ответе использует
    price_in_cents_with_discount. Старый код читал только price_in_cents,
    поэтому реальные FC Points превращались в "Недоступно в регионе".
    """
    raw_final = sub.get("price_in_cents_with_discount")
    if raw_final is None:
        raw_final = sub.get("price_in_cents")
    if raw_final is None:
        raw_final = parse_display_price_minor(sub.get("option_text"), region)

    try:
        final = int(raw_final)
    except (TypeError, ValueError):
        return None
    if final < 0:
        return None

    try:
        discount = int(sub.get("percent_savings") or 0)
    except (TypeError, ValueError):
        discount = 0

    initial = final
    if 0 < discount < 100:
        initial = int(round(final / (1 - discount / 100)))

    currency = "UAH" if region.upper() == "UA" else "USD"
    return {
        "currency": currency,
        "initial": initial,
        "final": final,
        "discount_percent": discount,
        "initial_formatted": None,
        "final_formatted": None,
    }


def extract_package_groups(package_groups: Any, region: str) -> list[dict[str, Any]]:
    """
    Не сплющивает все purchase groups в одну кучу.
    Это важно: у FC 27 есть отдельно editions и отдельно FCPoints.
    """
    output: list[dict[str, Any]] = []

    for group in package_groups or []:
        if not isinstance(group, dict):
            continue

        subs_out: dict[int, dict[str, Any]] = {}
        for sub in group.get("subs") or []:
            if not isinstance(sub, dict):
                continue
            try:
                packageid = int(sub.get("packageid"))
            except (TypeError, ValueError):
                continue

            fallback = f"Пакет {packageid}"
            name = clean_package_option_name(str(sub.get("option_text") or ""), fallback)
            subs_out[packageid] = {
                "packageid": packageid,
                "name": name,
                "price": package_sub_to_price(sub, region),
                "raw_option_text": str(sub.get("option_text") or ""),
            }

        output.append({
            "identity": currency_group_identity(group),
            "name": str(group.get("name") or ""),
            "title": plain_text(group.get("title")),
            "display_type": str(group.get("display_type") or ""),
            "is_currency": is_currency_package_group(group),
            "subs": subs_out,
        })

    return output


def fetch_live_package_groups(appid: int, region: str) -> list[dict[str, Any]]:
    """
    Цены package purchase options обновляются при каждом запуске.
    """
    params = {
        "appids": appid,
        "cc": region,
        "l": "english",
    }
    try:
        payload = request_json(STEAM_APPDETAILS_URL, params, PRICE_DELAY)
        item = (payload or {}).get(str(appid)) or {}
        if not item.get("success"):
            return []
        data = item.get("data") or {}
        return extract_package_groups(data.get("package_groups") or [], region)
    except Exception as exc:
        log(f"Варианты покупки AppID {appid} ({region}) не получены: {exc}")
        raise RuntimeError(
            f"Варианты покупки AppID {appid} ({region}) не получены: {exc}"
        ) from exc



def extract_currency_denomination(value: str | None) -> int | None:
    """
    Строго извлекает именно НОМИНАЛ игровой валюты, а не номер игры
    и не цену Steam.

    Приоритет:
      FC Points 5900  -> 5900
      5900 FC Points  -> 5900
      COD Points 2400 -> 2400
      2400 Coins      -> 2400

    Пробелы в тысячах поддерживаются:
      5 900 -> 5900
      12 000 -> 12000
      18 500 -> 18500
    """
    text = plain_text(value)
    if not text:
        return None

    # На всякий случай убираем ценовой хвост Steam:
    # "... - 2 199₴", "... - $19.99", "... - 19.99 USD"
    text = re.sub(
        r"\s*[-–—]\s*(?:[$€£₴₺¥₽]\s*)?"
        r"\d[\d\s\u00A0.,]*"
        r"(?:\s*(?:[$€£₴₺¥₽]|USD|UAH|TRY|TL|EUR|GBP))?\s*$",
        "",
        text,
        flags=re.I,
    ).strip()

    amount = r"(\d{1,3}(?:[\s\u00A0]\d{3})+|\d+)"
    unit = (
        r"(?:"
        r"FC\s*Points?|FIFA\s*Points?|COD\s*Points?|Call\s+of\s+Duty\s+Points?|"
        r"V[\s-]*Bucks?|Minecoins?|Robux|Apex\s+Coins?|Helix\s+Credits?|R6\s+Credits?|"
        r"Points?|Coins?|Credits?|Tokens?|Gems?|Crystals?|Shards?|Diamonds?|Platinum|VC"
        r")"
    )

    # Вариант "FC Points 5900"
    m = re.search(
        rf"{unit}\s*(?:x|×|:|-)?\s*{amount}\b",
        text,
        re.I,
    )
    if m:
        raw = m.group(1)
        digits = re.sub(r"\D", "", raw)
        if digits:
            return int(digits)

    # Вариант "5900 FC Points"
    m = re.search(
        rf"\b{amount}\s*(?:x|×|:|-)?\s*{unit}\b",
        text,
        re.I,
    )
    if m:
        raw = m.group(1)
        digits = re.sub(r"\D", "", raw)
        if digits:
            return int(digits)

    # Fallback: после удаления цены берём последнее отдельное число.
    # Это всё равно лучше старого варианта, потому что ценовой хвост уже удалён.
    numbers = re.findall(r"\d{1,3}(?:[\s\u00A0]\d{3})+|\d+", text)
    if not numbers:
        return None

    digits = re.sub(r"\D", "", numbers[-1])
    return int(digits) if digits else None


def currency_denomination_sort_key(option: dict[str, Any]) -> tuple[int, int, str]:
    """
    Номиналы игровой валюты всегда идут по возрастанию.
    Варианты без распознанного номинала помещаются в конец.
    """
    name = str(option.get("name") or "")
    denomination = option.get("denomination")
    if denomination is None:
        denomination = extract_currency_denomination(name)

    if denomination is None:
        return (1, 10**18, name.casefold())

    return (0, int(denomination), name.casefold())


CURRENCY_DISPLAY_PATTERNS: list[tuple[re.Pattern[str], str]] = [
    (re.compile(r"\bFC\s*Points?\b", re.I), "FC Points"),
    (re.compile(r"\bFIFA\s*Points?\b", re.I), "FIFA Points"),
    (re.compile(r"\bCOD\s*Points?\b", re.I), "COD Points"),
    (re.compile(r"\bCall\s+of\s+Duty\s+Points?\b", re.I), "Call of Duty Points"),
    (re.compile(r"\bV[\s-]*Bucks?\b", re.I), "V-Bucks"),
    (re.compile(r"\bMinecoins?\b", re.I), "Minecoins"),
    (re.compile(r"\bRobux\b", re.I), "Robux"),
    (re.compile(r"\bApex\s+Coins?\b", re.I), "Apex Coins"),
    (re.compile(r"\bHelix\s+Credits?\b", re.I), "Helix Credits"),
    (re.compile(r"\bR6\s+Credits?\b", re.I), "R6 Credits"),
]


def detect_currency_display_label(*values: Any) -> str:
    """
    Возвращает короткое название валюты для красивого HTML-блока.
    Если бренд не распознан, пытается взять generic unit.
    """
    text = " ".join(plain_text(v) for v in values if v)
    if not text:
        return "Игровая валюта"

    for pattern, label in CURRENCY_DISPLAY_PATTERNS:
        if pattern.search(text):
            return label

    # Generic fallback: "Apex Coins", "Gold Tokens", "Credits" и т.п.
    generic = re.search(
        r"\b([A-Za-z0-9™®&+'-]+(?:\s+[A-Za-z0-9™®&+'-]+){0,2}\s+"
        r"(?:Points?|Coins?|Credits?|Tokens?|Gems?|Crystals?|Shards?|Diamonds?))\b",
        text,
        re.I,
    )
    if generic:
        return re.sub(r"\s+", " ", generic.group(1)).strip()

    special = re.search(r"\b(Platinum|VC)\b", text, re.I)
    if special:
        return special.group(1).upper() if special.group(1).lower() == "vc" else special.group(1).title()

    return "Игровая валюта"




def build_currency_entries_from_groups(
    appid: int,
    meta: dict[str, Any],
    parent_name: str,
    ua_groups: list[dict[str, Any]],
    tr_groups: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    """
    Собирает только реальные currency purchase groups и объединяет
    одинаковые packageid для UA/TR.
    """
    ua_map = {g["identity"]: g for g in ua_groups if g.get("is_currency")}
    tr_map = {g["identity"]: g for g in tr_groups if g.get("is_currency")}
    identities = list(dict.fromkeys([*ua_map.keys(), *tr_map.keys()]))

    entries: list[dict[str, Any]] = []
    for identity in identities:
        ug = ua_map.get(identity)
        tg = tr_map.get(identity)

        package_ids = sorted(set((ug or {}).get("subs", {})) | set((tg or {}).get("subs", {})))
        if not package_ids:
            continue

        options: list[dict[str, Any]] = []
        for packageid in package_ids:
            uo = (ug or {}).get("subs", {}).get(packageid)
            to = (tg or {}).get("subs", {}).get(packageid)
            name = (
                (uo or {}).get("name")
                or (to or {}).get("name")
                or f"Пакет {packageid}"
            )

            # Не добавляем "пустой" package, если Steam не дал цену
            # ни в одном из двух регионов.
            up = (uo or {}).get("price")
            tp = (to or {}).get("price")
            if not up and not tp:
                continue

            options.append({
                "packageid": packageid,
                "name": name,
                "denomination": extract_currency_denomination(name),
                "search_terms": build_search_terms(name, packageid, parent_name=parent_name),
                "ua": region_price_entry(up, "UA"),
                "tr": region_price_entry(tp, "TR"),
            })

        if not options:
            continue

        # Жёсткая числовая сортировка номиналов:
        # 500 -> 1050 -> 1600 -> 2800 -> 5900 -> 12000 -> 18500
        options.sort(key=currency_denomination_sort_key)

        title = (
            (ug or {}).get("title")
            or (tg or {}).get("title")
            or meta.get("name")
            or "Игровая валюта"
        )
        title = re.sub(r"^\s*Buy\s+", "", str(title), flags=re.I).strip()

        currency_label = detect_currency_display_label(
            title,
            *((opt.get("name") or "") for opt in options),
        )

        entries.append({
            "appid": appid,
            "name": title,
            "game_name": parent_name,
            "currency_label": currency_label,
            "steam_url": f"https://store.steampowered.com/app/{appid}/",
            "search_terms": build_search_terms(
                " ".join([title, currency_label]),
                appid,
                parent_name=parent_name,
            ),
            "options": options,
            "option_count": len(options),
        })

    return entries



def merge_currency_groups(groups: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """
    Объединяет валютные purchase groups одной и той же валюты.

    Это важно для Steam-страниц, где часть номиналов находится
    в package_groups основной игры, а отдельный номинал может
    дополнительно находиться в currency-DLC.

    Например FC Points:
      main game -> 500, 1050, 1600, 2800, 12000, 18500
      currency DLC -> 5900
    После объединения:
      500, 1050, 1600, 2800, 5900, 12000, 18500
    """
    merged: dict[str, dict[str, Any]] = {}
    order: list[str] = []

    for group in groups or []:
        label = str(group.get("currency_label") or "").strip()
        name = str(group.get("name") or "").strip()
        key = normalize_search_text(label or name or "currency")

        if key not in merged:
            merged[key] = {
                **group,
                "options": [],
            }
            order.append(key)

        target = merged[key]

        # Более конкретное название/игру сохраняем при наличии.
        if not target.get("currency_label") and group.get("currency_label"):
            target["currency_label"] = group["currency_label"]
        if not target.get("game_name") and group.get("game_name"):
            target["game_name"] = group["game_name"]

        existing_by_pid = {
            int(opt.get("packageid") or 0): opt
            for opt in (target.get("options") or [])
            if int(opt.get("packageid") or 0) > 0
        }

        for opt in group.get("options") or []:
            pid = int(opt.get("packageid") or 0)

            # Для packageid=0 используем имя как запасной уникальный ключ.
            if pid <= 0:
                synthetic = -abs(hash(normalize_search_text(str(opt.get("name") or ""))))
                pid = synthetic

            if pid not in existing_by_pid:
                copied = dict(opt)
                copied["denomination"] = (
                    copied.get("denomination")
                    if copied.get("denomination") is not None
                    else extract_currency_denomination(str(copied.get("name") or ""))
                )
                target["options"].append(copied)
                existing_by_pid[pid] = copied
                continue

            # Если одна запись была неполной по региону, дополняем второй.
            current = existing_by_pid[pid]
            for region_key in ("ua", "tr"):
                cur_region = current.get(region_key) or {}
                new_region = opt.get(region_key) or {}
                if not cur_region.get("available") and new_region.get("available"):
                    current[region_key] = new_region

            if current.get("denomination") is None:
                current["denomination"] = extract_currency_denomination(
                    str(current.get("name") or opt.get("name") or "")
                )

    result: list[dict[str, Any]] = []
    for key in order:
        group = merged[key]
        options = group.get("options") or []
        options.sort(key=currency_denomination_sort_key)
        group["options"] = options
        group["option_count"] = len(options)
        result.append(group)

    return result



def build_currency_entries_from_app(
    appid: int,
    meta: dict[str, Any],
    parent_name: str,
) -> list[dict[str, Any]]:
    """
    Главный источник валюты:
    - сначала реальные package_groups самого AppID;
    - для UA есть безопасный fallback на metadata-кеш, т.к. metadata
      у нас загружается с cc=UA;
    - TR всегда берётся отдельным живым запросом cc=TR.
    """
    ua_groups = fetch_live_package_groups(appid, "UA")
    tr_groups = fetch_live_package_groups(appid, "TR")

    if not ua_groups and meta.get("package_groups"):
        ua_groups = extract_package_groups(meta.get("package_groups") or [], "UA")

    return build_currency_entries_from_groups(
        appid=appid,
        meta=meta,
        parent_name=parent_name,
        ua_groups=ua_groups,
        tr_groups=tr_groups,
    )


def free_region_entry() -> dict[str, Any]:
    return {
        "available": True,
        "is_free": True,
        "currency": "RUB",
        "initial": 0,
        "final": 0,
        "discount_percent": 0,
        "rub_initial": 0,
        "rub_final": 0,
        "rub_initial_formatted": "Бесплатно",
        "rub_final_formatted": "Бесплатно",
        "price_rub": 0,
    }



SEARCH_STOP_WORDS = {
    "the", "a", "an", "of", "and", "for", "to", "in", "on", "with",
    "edition", "game", "digital", "standard",
}

ROMAN_TO_ARABIC = {
    "i": "1", "ii": "2", "iii": "3", "iv": "4", "v": "5",
    "vi": "6", "vii": "7", "viii": "8", "ix": "9", "x": "10",
    "xi": "11", "xii": "12", "xiii": "13", "xiv": "14", "xv": "15",
}
ARABIC_TO_ROMAN = {v: k for k, v in ROMAN_TO_ARABIC.items()}


def normalize_search_text(value: str | None) -> str:
    import unicodedata
    value = value or ""
    value = value.replace("™", " ").replace("®", " ").replace("©", " ")
    value = value.replace("&", " and ").replace("+", " plus ")
    value = unicodedata.normalize("NFKD", value)
    value = "".join(ch for ch in value if not unicodedata.combining(ch))
    value = value.casefold()
    value = re.sub(r"[^a-z0-9а-яё]+", " ", value, flags=re.I)
    return re.sub(r"\s+", " ", value).strip()



COMMON_RUSSIAN_SEARCH_ALIASES = {
    # Серии / распространённые русские варианты
    "ea sports fc": ["фифа", "фк", "фс", "еа спортс фк", "еа спортс фс", "еа спортс фифа"],
    "fifa": ["фифа"],
    "grand theft auto": ["гта", "гранд тефт ауто", "гранд зефт ауто"],
    "call of duty": ["код", "кол оф дьюти", "калл оф дьюти"],
    "resident evil": ["резидент ивил", "резидент евил"],
    "counter strike": ["кс", "контр страйк", "каунтер страйк"],
    "world of tanks": ["вот", "ворлд оф танкс", "мир танков"],
    "world of warships": ["ворлд оф варшипс", "мир кораблей"],
    "red dead redemption": ["рдр", "ред дед редемпшн"],
    "need for speed": ["нфс", "нид фор спид"],
    "assassin s creed": ["ассасин крид", "ассасинс крид"],
    "the witcher": ["витчер", "ведьмак"],
    "cyberpunk": ["киберпанк", "сайберпанк"],
    "elden ring": ["элден ринг"],
    "dark souls": ["дарк соулс"],
    "mortal kombat": ["мк", "мортал комбат"],
    "forza horizon": ["форза", "форза хорайзон"],
    "apex legends": ["апекс", "апекс легендс"],
    "war thunder": ["вар тандер"],
    "warframe": ["варфрейм"],
    "dota": ["дота"],
    "battlefield": ["батлфилд"],
    "god of war": ["год оф вар", "бог войны"],
    "spider man": ["спайдер мен", "спайдерман", "человек паук"],
    "silent hill": ["сайлент хилл"],
    "monster hunter": ["монстер хантер"],
    "final fantasy": ["финал фэнтези", "финал фантази"],
    "street fighter": ["стрит файтер"],
    "tekken": ["теккен"],
    "fallout": ["фоллаут"],
    "skyrim": ["скайрим"],
    "helldivers": ["хеллдайверс", "хеллдайверз"],
    "atomic heart": ["атомик харт"],
    "stalker": ["сталкер", "сталкер 2"],
    "metro": ["метро"],
}

def english_to_russian_phonetic(value: str) -> str:
    """
    Не перевод, а поисковая фонетическая форма:
    Grand Theft Auto -> гранд тефт ауто
    Resident Evil -> ресидент евил
    GTA -> гта
    """
    s = normalize_search_text(value)
    if not s:
        return ""

    replacements = [
        ("shch", "щ"), ("sch", "щ"), ("tch", "ч"),
        ("zh", "ж"), ("kh", "х"), ("ts", "ц"),
        ("ch", "ч"), ("sh", "ш"), ("th", "т"),
        ("ph", "ф"), ("qu", "кв"), ("ck", "к"),
        ("ee", "и"), ("oo", "у"),
        ("yo", "ё"), ("yu", "ю"), ("ya", "я"),
    ]
    for latin, cyr in replacements:
        s = s.replace(latin, cyr)

    table = str.maketrans({
        "a":"а","b":"б","c":"к","d":"д","e":"е","f":"ф","g":"г",
        "h":"х","i":"и","j":"дж","k":"к","l":"л","m":"м","n":"н",
        "o":"о","p":"п","q":"к","r":"р","s":"с","t":"т","u":"у",
        "v":"в","w":"в","x":"кс","y":"й","z":"з",
    })
    s = s.translate(table)
    return re.sub(r"\s+", " ", s).strip()


def russian_aliases_for_name(value: str) -> list[str]:
    norm_value = normalize_search_text(value)
    out: set[str] = set()

    phonetic = english_to_russian_phonetic(value)
    if phonetic:
        out.add(phonetic)
        out.add(phonetic.replace(" ", ""))

    for key, aliases in COMMON_RUSSIAN_SEARCH_ALIASES.items():
        if key in norm_value:
            out.update(aliases)
            out.update(a.replace(" ", "") for a in aliases)

    return sorted(out)



def build_search_terms(name: str, appid: int, parent_name: str | None = None) -> list[str]:
    """
    Варианты для data-search:
    - полное название;
    - название без пробелов/знаков;
    - без служебных слов;
    - аббревиатура;
    - римские/арабские цифры;
    - базовое название до подзаголовка;
    - AppID;
    - для DLC: имя основной игры + DLC.
    """
    raw_values = [name]
    if parent_name:
        raw_values.extend([f"{parent_name} {name}", parent_name])

    terms: set[str] = {str(appid)}

    for raw in raw_values:
        norm = normalize_search_text(raw)
        if not norm:
            continue

        terms.add(norm)
        terms.add(norm.replace(" ", ""))

        words = norm.split()
        meaningful = [w for w in words if w not in SEARCH_STOP_WORDS]
        if meaningful:
            terms.add(" ".join(meaningful))
            terms.add("".join(meaningful))

        acronym_words = [w for w in words if w not in {"the", "a", "an", "of"}]
        if len(acronym_words) >= 2:
            acronym = "".join(w[0] for w in acronym_words if w)
            if len(acronym) >= 2:
                terms.add(acronym)

        for separator in (":", " - ", " – ", " — "):
            if separator in raw:
                base = normalize_search_text(raw.split(separator, 1)[0])
                if base:
                    terms.add(base)
                    terms.add(base.replace(" ", ""))

        to_num = [ROMAN_TO_ARABIC.get(w, w) for w in words]
        to_roman = [ARABIC_TO_ROMAN.get(w, w) for w in words]
        terms.add(" ".join(to_num))
        terms.add("".join(to_num))
        terms.add(" ".join(to_roman))
        terms.add("".join(to_roman))

        edition_words = {
            "deluxe", "ultimate", "complete", "premium", "gold",
            "standard", "digital", "edition", "bundle", "pack",
        }
        no_edition = [w for w in words if w not in edition_words]
        if no_edition and no_edition != words:
            terms.add(" ".join(no_edition))
            terms.add("".join(no_edition))

        # Русские фонетические варианты и популярные русские названия.
        terms.update(russian_aliases_for_name(raw))

    return sorted(t for t in terms if t)


def region_price_entry(price: dict[str, Any] | None, region: str) -> dict[str, Any]:
    if not price:
        return {"available": False}

    rub_initial = playbox_steam_rub_price(region, price.get("initial"))
    rub_final = playbox_steam_rub_price(region, price.get("final"))

    return {
        "available": True,
        **price,
        "rub_initial": rub_initial,
        "rub_final": rub_final,
        "rub_initial_formatted": format_rub(rub_initial),
        "rub_final_formatted": format_rub(rub_final),
        # Текущая цена магазина для корзины:
        "price_rub": rub_final,
    }



def build_single_game_card(
    appid: int,
    sg: SearchGame,
    meta: dict[str, Any],
    language_details: dict[str, Any],
    dlc_meta: dict[int, dict[str, Any] | None],
    dlc_ua: dict[int, dict[str, Any] | None],
    dlc_tr: dict[int, dict[str, Any] | None],
    ua_prices: dict[int, dict[str, Any] | None],
    tr_prices: dict[int, dict[str, Any] | None],
) -> dict[str, Any] | None:
    dlcs: list[dict[str, Any]] = []
    currency_groups: list[dict[str, Any]] = []
    parent_name = meta.get("name") or sg.name

    has_currency_group_hint = any(
        is_currency_package_group(group)
        for group in (meta.get("package_groups") or [])
        if isinstance(group, dict)
    )
    has_in_app_purchases = any(
        str(category).casefold() == "in-app purchases"
        for category in (meta.get("categories") or [])
    )
    if has_currency_group_hint or has_in_app_purchases:
        currency_groups.extend(
            build_currency_entries_from_app(appid, meta, parent_name)
        )

    seen_currency_package_ids = {
        int(opt["packageid"])
        for group in currency_groups
        for opt in (group.get("options") or [])
        if str(opt.get("packageid", "")).isdigit()
    }

    for dlc_id in meta.get("dlc") or []:
        dm = dlc_meta.get(dlc_id) or {}
        pua = dlc_ua.get(dlc_id)
        ptr = dlc_tr.get(dlc_id)

        if is_currency_meta(dm):
            entries = build_currency_entries_from_app(dlc_id, dm, parent_name)
            for entry in entries:
                unique_options = []
                for opt in entry.get("options") or []:
                    pid = int(opt.get("packageid") or 0)
                    if pid and pid not in seen_currency_package_ids:
                        unique_options.append(opt)
                        seen_currency_package_ids.add(pid)

                if unique_options:
                    entry["options"] = unique_options
                    entry["option_count"] = len(unique_options)
                    currency_groups.append(entry)
            continue

        if not INCLUDE_FREE_DLC and not pua and not ptr:
            continue

        dlcs.append({
            "appid": dlc_id,
            "name": dm.get("name") or f"DLC {dlc_id}",
            "image": dm.get("header_image") or dm.get("capsule_image")
                or f"https://shared.fastly.steamstatic.com/store_item_assets/steam/apps/{dlc_id}/header.jpg",
            "steam_url": f"https://store.steampowered.com/app/{dlc_id}/",
            "search_terms": build_search_terms(
                dm.get("name") or f"DLC {dlc_id}",
                dlc_id,
                parent_name=parent_name,
            ),
            "ua": region_price_entry(pua, "UA"),
            "tr": region_price_entry(ptr, "TR"),
            "has_discount": bool(
                (pua and pua.get("discount_percent", 0) > 0) or
                (ptr and ptr.get("discount_percent", 0) > 0)
            ),
        })

    currency_groups = merge_currency_groups(currency_groups)

    pua = ua_prices.get(appid)
    ptr = tr_prices.get(appid)
    base_discount = bool(
        (pua and pua.get("discount_percent", 0) > 0) or
        (ptr and ptr.get("discount_percent", 0) > 0)
    )
    any_dlc_discount = any(d["has_discount"] for d in dlcs)

    is_free_game = bool(meta.get("is_free")) or (not pua and not ptr and sg.free_hint)
    has_paid_content = bool(dlcs or currency_groups)
    if is_free_game and not has_paid_content:
        return None

    return {
        "appid": appid,
        "name": meta.get("name") or sg.name,
        "image": meta.get("header_image") or sg.image,
        "steam_url": f"https://store.steampowered.com/app/{appid}/",
        "search_terms": build_search_terms(meta.get("name") or sg.name, appid),
        "rating_percent": sg.rating_percent,
        "reviews": sg.reviews,
        "release_date": meta.get("release_date"),
        "coming_soon": bool(meta.get("coming_soon")),
        "is_preorder": bool(meta.get("coming_soon")),
        "genres": list(dict.fromkeys(meta.get("genres") or [])),
        "russian": language_details or {
            "supported": False,
            "interface": None,
            "full_audio": False,
            "subtitles": None,
            "source": "none",
        },
        "russian_label": russian_label(language_details),
        "russian_status_class": russian_status_class(language_details),
        "is_free": is_free_game,
        "ua": free_region_entry() if is_free_game and not pua else region_price_entry(pua, "UA"),
        "tr": free_region_entry() if is_free_game and not ptr else region_price_entry(ptr, "TR"),
        "has_discount": base_discount,
        "has_any_discount": base_discount or any_dlc_discount,
        "dlc_count": len(dlcs),
        "dlc": dlcs,
        "currency_count": sum(int(x.get("option_count") or 0) for x in currency_groups),
        "currency_groups": currency_groups,
    }


def build_catalog(
    test_limit: int | None = None,
    refresh_metadata: bool = False,
    alphabetical: bool = False,
    resume: bool = False,
):
    if resume:
        state = _load_resume_state()
        config = state.get("config") or {}
        test_limit = config.get("test_limit")
        refresh_metadata = bool(config.get("refresh_metadata"))
        alphabetical = bool(config.get("alphabetical"))
        log(
            f"RESUME: продолжаю с этапа {state.get('stage')} "
            f"(без повторения уже завершённых сетевых этапов)."
        )
    else:
        state = _init_resume_state(
            test_limit=test_limit,
            refresh_metadata=refresh_metadata,
            alphabetical=alphabetical,
        )

    # 1) Steam Search — каждая страница сохраняется сразу.
    search_games = scan_all_games_resumable(
        state,
        test_limit=test_limit,
        alphabetical=alphabetical,
    )

    if test_limit is None and INCLUDE_F2P_WITH_PAID_CONTENT:
        free_games = scan_free_to_play_games_resumable(state)
        known = {g.appid for g in search_games}
        search_games.extend(g for g in free_games if g.appid not in known)

    appids = [g.appid for g in search_games]
    search_by_id = {g.appid: g for g in search_games}

    # 2) Цены игр. Каждая УСПЕШНАЯ пачка записывается в JSONL.
    # При сетевой ошибке пачка не теряется: запуск остановится,
    # а --resume повторит именно незавершённую пачку.
    log(f"Получаю цены {len(appids):,} игр для UA/TR...")
    ua_prices = get_prices_batched_resumable(
        appids,
        "UA",
        state,
        "game_prices_ua",
        "game_prices_tr",
        "game_prices_ua.jsonl",
    )
    tr_prices = get_prices_batched_resumable(
        appids,
        "TR",
        state,
        "game_prices_tr",
        "game_meta",
        "game_prices_tr.jsonl",
    )

    selected_ids: list[int] = []
    deferred_free_ids: list[int] = []

    for appid in appids:
        g = search_by_id[appid]
        if not rating_passes(g):
            continue

        ua = ua_prices.get(appid)
        tr = tr_prices.get(appid)

        if ua or tr:
            if price_passes_threshold(ua) or price_passes_threshold(tr):
                selected_ids.append(appid)
            continue

        if INCLUDE_F2P_WITH_PAID_CONTENT and g.free_hint:
            deferred_free_ids.append(appid)

    selected_ids.extend(x for x in deferred_free_ids if x not in selected_ids)
    log(
        f"Кандидатов после первичного фильтра: {len(selected_ids):,} "
        f"(из них F2P для проверки: {len(deferred_free_ids):,})."
    )

    cache = load_cache()

    # 3) Metadata игр. Для каждого законченного AppID сохраняем отдельную
    # запись, включая language details и список DLC.
    game_meta_records = _load_done_map(_resume_file("game_meta.jsonl"))
    game_meta: dict[int, dict[str, Any] | None] = {}
    game_language_details: dict[int, dict[str, Any]] = {}
    all_dlc_ids: set[int] = set()

    for n, appid in enumerate(selected_ids, 1):
        if appid in game_meta_records:
            rec = game_meta_records[appid]
            meta = (cache.get("apps") or {}).get(str(appid))
            if meta is None:
                # Повреждён/удалён metadata-cache: безопасно догружаем только этот AppID.
                meta = fetch_app_metadata(appid, cache, force=False)
            game_meta[appid] = meta
            lang = rec.get("language")
            if not isinstance(lang, dict):
                lang = fetch_russian_language_details(
                    appid,
                    cache,
                    fallback_supported_languages=(meta or {}).get("supported_languages"),
                    force=False,
                )
            game_language_details[appid] = lang
            all_dlc_ids.update(int(x) for x in (rec.get("dlc") or []) if str(x).isdigit())
            continue

        meta = fetch_app_metadata(appid, cache, force=refresh_metadata)
        game_meta[appid] = meta
        if meta:
            dlc_list = [int(x) for x in (meta.get("dlc") or []) if str(x).isdigit()]
            all_dlc_ids.update(dlc_list)
            lang = fetch_russian_language_details(
                appid,
                cache,
                fallback_supported_languages=meta.get("supported_languages"),
                force=refresh_metadata,
            )
        else:
            dlc_list = []
            lang = {
                "supported": False,
                "interface": None,
                "full_audio": False,
                "subtitles": None,
                "source": "none",
            }

        game_language_details[appid] = lang
        _append_jsonl(_resume_file("game_meta.jsonl"), {
            "appid": appid,
            "language": lang,
            "dlc": dlc_list,
        })

        if n % 50 == 0:
            save_cache(cache)
            log(
                f"Metadata игр: {n}/{len(selected_ids)}; "
                f"найдено DLC IDs: {len(all_dlc_ids):,}"
            )

    save_cache(cache)

    if _stage_index(str(state.get("stage"))) <= _stage_index("game_meta"):
        _set_resume_stage(state, "dlc_prices_ua")

    dlc_ids = sorted(all_dlc_ids)
    log(f"Всего привязанных DLC: {len(dlc_ids):,}")

    # 4) Цены DLC — тоже resumable по каждой пачке.
    dlc_ua = get_prices_batched_resumable(
        dlc_ids,
        "UA",
        state,
        "dlc_prices_ua",
        "dlc_prices_tr",
        "dlc_prices_ua.jsonl",
    ) if dlc_ids else {}
    dlc_tr = get_prices_batched_resumable(
        dlc_ids,
        "TR",
        state,
        "dlc_prices_tr",
        "dlc_meta",
        "dlc_prices_tr.jsonl",
    ) if dlc_ids else {}

    if not dlc_ids and _stage_index(str(state.get("stage"))) <= _stage_index("dlc_prices_tr"):
        _set_resume_stage(state, "dlc_meta")

    # 5) Metadata DLC.
    dlc_done = _load_done_map(_resume_file("dlc_meta.jsonl"))
    dlc_meta: dict[int, dict[str, Any] | None] = {}

    for n, dlc_id in enumerate(dlc_ids, 1):
        if dlc_id in dlc_done:
            meta = (cache.get("apps") or {}).get(str(dlc_id))
            if meta is None:
                meta = fetch_app_metadata(dlc_id, cache, force=False)
            dlc_meta[dlc_id] = meta
            continue

        meta = fetch_app_metadata(dlc_id, cache, force=refresh_metadata)
        dlc_meta[dlc_id] = meta
        _append_jsonl(_resume_file("dlc_meta.jsonl"), {"appid": dlc_id})

        if n % 100 == 0:
            save_cache(cache)
            log(f"Metadata DLC: {n}/{len(dlc_ids)}")

    save_cache(cache)

    if _stage_index(str(state.get("stage"))) <= _stage_index("dlc_meta"):
        _set_resume_stage(state, "build_cards")

    # 6) Финальные карточки. Сохраняем результат КАЖДОЙ игры.
    # Это важно, потому что здесь могут быть живые package-group запросы валюты.
    card_records = _load_done_map(_resume_file("cards.jsonl"))
    games_out: list[dict[str, Any]] = []

    for n, appid in enumerate(selected_ids, 1):
        if appid in card_records:
            card = card_records[appid].get("card")
            if isinstance(card, dict):
                games_out.append(card)
            continue

        sg = search_by_id[appid]
        meta = game_meta.get(appid) or {}
        card = build_single_game_card(
            appid=appid,
            sg=sg,
            meta=meta,
            language_details=game_language_details.get(appid) or {},
            dlc_meta=dlc_meta,
            dlc_ua=dlc_ua,
            dlc_tr=dlc_tr,
            ua_prices=ua_prices,
            tr_prices=tr_prices,
        )
        _append_jsonl(_resume_file("cards.jsonl"), {
            "appid": appid,
            "card": card,
        })
        if card is not None:
            games_out.append(card)

        if n % 500 == 0:
            log(f"Собрано карточек: {n}/{len(selected_ids)}")

    # Каталог сохраняем в стабильном алфавитном порядке.
    # normalize_search_text убирает ведущие пробелы/знаки вроде #, !, кавычек,
    # поэтому такие названия сортируются по самому названию, а не по символу.
    def _catalog_alpha_key(game: dict[str, Any]) -> tuple[int, str, str]:
        raw_name = str(game.get("name") or "").strip()
        normalized = normalize_search_text(raw_name)

        # Для витрины: сначала A-Z/А-Я, затем названия с цифры,
        # затем прочие алфавиты. Ведущие пробелы и знаки (#, !, кавычки)
        # не ломают порядок: смотрим на первый содержательный символ.
        first = ""
        for ch in raw_name:
            if not ch.isspace() and not unicodedata.category(ch).startswith(("P", "S")):
                first = ch
                break
        if re.match(r"[A-Za-zА-Яа-яЁё]", first):
            group = 0
        elif first.isdigit():
            group = 1
        else:
            group = 2

        return (group, normalized or raw_name.casefold(), raw_name.casefold())

    games_out.sort(key=_catalog_alpha_key)
    _set_resume_stage(state, "complete")

    return {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "regions": REGIONS,
        "filters": {
            "min_base_price_minor": MIN_BASE_PRICE_MINOR,
            "min_rating_percent": MIN_RATING_PERCENT,
            "min_review_count": MIN_REVIEW_COUNT,
            "keep_unrated": KEEP_UNRATED,
            "include_free_dlc": INCLUDE_FREE_DLC,
        },
        "steam_playbox_pricing": {
            "UA": {
                "formula": "UAH / 43 * 90 + markup",
                "markup_low_rub": 800,
                "markup_high_rub": 1000,
                "markup_threshold_uah": 250,
            },
            "TR": {
                "formula": "USD * 90 + markup",
                "markup_low_rub": 800,
                "markup_high_rub": 1000,
                "markup_threshold_usd": 9.99,
                "threshold_inclusive_high": True,
            },
            "round_to_rub": 100,
            "round_up_from_remainder_rub": 50,
        },
        "stats": {
            "steam_games_seen": len(search_games),
            "games_in_catalog": len(games_out),
            "dlc_in_catalog": sum(g["dlc_count"] for g in games_out),
            "currency_options_in_catalog": sum(int(g.get("currency_count") or 0) for g in games_out),
            "free_games_with_paid_content": sum(1 for g in games_out if g.get("is_free")),
            "preorder_games": sum(1 for g in games_out if g.get("is_preorder") or g.get("coming_soon")),
            "discounted_games": sum(1 for g in games_out if g["has_discount"]),
            "cards_with_any_discount": sum(1 for g in games_out if g["has_any_discount"]),
        },
        "games": games_out,
    }



def _browser_price(price: dict[str, Any] | None) -> dict[str, Any] | None:
    """Минимальный набор цены, реально нужный браузеру."""
    if not price or not price.get("available"):
        return None
    if price.get("is_free"):
        return {"is_free": True, "rub_final": 0}

    out: dict[str, Any] = {"rub_final": price.get("rub_final")}
    discount = int(price.get("discount_percent") or 0)
    if discount > 0:
        out["discount_percent"] = discount
        out["rub_initial"] = price.get("rub_initial")
    return out


def _limited_search_terms(values: Any, limit: int) -> list[str]:
    items = {
        str(x).strip()
        for x in (values or [])
        if str(x).strip()
    }
    return sorted(items, key=lambda x: (len(x), x))[:limit]


def _browser_search_blob(game: dict[str, Any]) -> str:
    """
    Одна готовая строка поиска для игры. В неё входят сама игра, AppID,
    основные алиасы, названия/ID DLC и игровой валюты. Так браузеру не надо
    обходить тысячи вложенных объектов на каждое нажатие клавиши.
    """
    values: list[str] = [
        str(game.get("name") or ""),
        str(game.get("appid") or ""),
    ]
    values.extend(str(x) for x in (game.get("search_terms") or []))

    for dlc in game.get("dlc") or []:
        values.extend([
            str(dlc.get("name") or ""),
            str(dlc.get("appid") or ""),
        ])
        # У DLC старые search_terms очень сильно раздувались из-за комбинаций
        # parent+dlc. Берём короткие полезные варианты/алиасы — поиск сохраняется,
        # а файл становится в разы меньше.
        values.extend(_limited_search_terms(dlc.get("search_terms"), 6))

    for group in game.get("currency_groups") or []:
        values.extend([
            str(group.get("name") or ""),
            str(group.get("currency_label") or ""),
            str(group.get("appid") or ""),
        ])
        values.extend(_limited_search_terms(group.get("search_terms"), 6))
        for option in group.get("options") or []:
            values.extend([
                str(option.get("name") or ""),
                str(option.get("packageid") or ""),
            ])
            values.extend(_limited_search_terms(option.get("search_terms"), 4))

    unique: list[str] = []
    seen: set[str] = set()
    for value in values:
        value = value.strip()
        if value and value not in seen:
            seen.add(value)
            unique.append(value)

    return normalize_search_text(" ".join(unique))


def _browser_dlc(dlc: dict[str, Any]) -> dict[str, Any]:
    out: dict[str, Any] = {
        "appid": dlc.get("appid"),
        "name": dlc.get("name") or "",
        "ua": _browser_price(dlc.get("ua")),
        "tr": _browser_price(dlc.get("tr")),
    }
    if dlc.get("image"):
        out["image"] = dlc["image"]
    if dlc.get("has_discount"):
        out["has_discount"] = True
    return out


def _browser_currency_group(group: dict[str, Any]) -> dict[str, Any]:
    out: dict[str, Any] = {
        "appid": group.get("appid"),
        "name": group.get("name") or "",
    }
    if group.get("game_name"):
        out["game_name"] = group["game_name"]
    if group.get("currency_label"):
        out["currency_label"] = group["currency_label"]

    options: list[dict[str, Any]] = []
    for option in group.get("options") or []:
        item: dict[str, Any] = {
            "packageid": option.get("packageid"),
            "name": option.get("name") or "",
            "ua": _browser_price(option.get("ua")),
            "tr": _browser_price(option.get("tr")),
        }
        if option.get("denomination") is not None:
            item["denomination"] = option.get("denomination")
        options.append(item)

    out["options"] = options
    out["option_count"] = len(options)
    return out


def _browser_game(game: dict[str, Any]) -> dict[str, Any]:
    out: dict[str, Any] = {
        "appid": game.get("appid"),
        "name": game.get("name") or "",
        "ua": _browser_price(game.get("ua")),
        "tr": _browser_price(game.get("tr")),
        "search_name": normalize_search_text(str(game.get("name") or "")),
        "search_text": _browser_search_blob(game),
    }

    if game.get("image"):
        out["image"] = game["image"]
    for key in ("rating_percent", "reviews", "release_date"):
        if game.get(key) is not None:
            out[key] = game[key]
    if game.get("is_preorder") or game.get("coming_soon"):
        out["is_preorder"] = True
    if game.get("genres"):
        out["genres"] = game["genres"]
    if game.get("russian_label"):
        out["russian_label"] = game["russian_label"]
    if game.get("russian_status_class"):
        out["russian_status_class"] = game["russian_status_class"]
    if game.get("is_free"):
        out["is_free"] = True
    if game.get("has_discount"):
        out["has_discount"] = True
    if game.get("has_any_discount"):
        out["has_any_discount"] = True

    dlc_count = len(game.get("dlc") or [])
    if dlc_count:
        out["dlc_count"] = dlc_count

    currency_count = sum(
        len(group.get("options") or [])
        for group in (game.get("currency_groups") or [])
    )
    if currency_count:
        out["currency_count"] = currency_count

    return out


def build_browser_outputs(catalog: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    """
    Разделяет каталог на:
      steam_catalog_data.js     — лёгкие карточки + поисковый индекс;
      steam_catalog_details.js  — DLC/валюта, загружается HTML только по требованию.
    """
    games = catalog.get("games") or []
    browser_catalog = {
        "generated_at": catalog.get("generated_at"),
        "regions": catalog.get("regions"),
        "stats": catalog.get("stats"),
        "games": [_browser_game(game) for game in games],
    }

    details: dict[str, Any] = {}
    for game in games:
        if not game.get("dlc") and not game.get("currency_groups"):
            continue
        item: dict[str, Any] = {}
        if game.get("dlc"):
            item["dlc"] = [_browser_dlc(dlc) for dlc in game.get("dlc") or []]
        if game.get("currency_groups"):
            item["currency_groups"] = [
                _browser_currency_group(group)
                for group in game.get("currency_groups") or []
            ]
        details[str(game.get("appid"))] = item

    return browser_catalog, details


def write_outputs(catalog: dict[str, Any]) -> None:
    # Полный JSON остаётся полным архивом/источником данных для Python.
    json_text = json.dumps(catalog, ensure_ascii=False, indent=2)
    OUTPUT_JSON.write_text(json_text, encoding="utf-8")

    # Для браузера создаём облегчённые файлы. Основной data.js больше не тащит
    # в память все DLC/валюту и не хранит лишние форматированные дубликаты цен.
    browser_catalog, browser_details = build_browser_outputs(catalog)

    OUTPUT_JS.write_text(
        "window.STEAM_CATALOG="
        + json.dumps(browser_catalog, ensure_ascii=False, separators=(",", ":"))
        + ";\n",
        encoding="utf-8",
    )
    OUTPUT_DETAILS_JS.write_text(
        "window.STEAM_CATALOG_DETAILS="
        + json.dumps(browser_details, ensure_ascii=False, separators=(",", ":"))
        + ";\n",
        encoding="utf-8",
    )

    log(f"Готово: {OUTPUT_JSON.name}")
    log(f"Готово: {OUTPUT_JS.name}")
    log(f"Готово: {OUTPUT_DETAILS_JS.name}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Build Steam UA/TR catalog")
    parser.add_argument(
        "command",
        nargs="?",
        choices=["resume"],
        help="Можно написать просто: py steam_catalog.py resume",
    )
    parser.add_argument(
        "--test-limit",
        type=int,
        default=None,
        help="Для проверки обработать только первые N игр (например 50).",
    )
    parser.add_argument(
        "--test-alpha",
        type=int,
        default=None,
        help="Для проверки обработать первые N игр по алфавиту (например 30).",
    )
    parser.add_argument(
        "--refresh-metadata",
        action="store_true",
        help="Заново скачать metadata/DLC даже для уже закешированных AppID.",
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help=(
            "Продолжить незавершённый запуск с checkpoint. "
            "Уже завершённые Steam Search, пачки цен, metadata и карточки повторно не запрашиваются."
        ),
    )
    args = parser.parse_args()
    resume_mode = bool(args.resume or args.command == "resume")

    if resume_mode and (
        args.test_limit is not None
        or args.test_alpha is not None
        or args.refresh_metadata
    ):
        parser.error(
            "resume запускается отдельно, без --test-limit, --test-alpha и --refresh-metadata. "
            "Настройки берутся из сохранённого checkpoint."
        )

    try:
        alpha_limit = args.test_alpha if args.test_alpha is not None else None
        effective_limit = alpha_limit if alpha_limit is not None else args.test_limit

        catalog = build_catalog(
            test_limit=effective_limit,
            refresh_metadata=args.refresh_metadata,
            alphabetical=alpha_limit is not None,
            resume=resume_mode,
        )
        write_outputs(catalog)

        # Только после успешной записи ОБОИХ итоговых файлов checkpoint больше не нужен.
        # Если программа упадёт раньше — .steam_resume останется для --resume.
        _reset_resume_checkpoint()

        log(
            f"Итог: {catalog['stats']['games_in_catalog']} игр, "
            f"{catalog['stats']['dlc_in_catalog']} DLC."
        )
        return 0
    except KeyboardInterrupt:
        log(
            "Остановлено пользователем. Checkpoint сохранён. "
            "Для продолжения: py steam_catalog.py resume"
        )
        return 130
    except Exception as e:
        log(f"Критическая ошибка: {e}")
        if RESUME_STATE.exists():
            log("Checkpoint сохранён. Для продолжения: py steam_catalog.py resume")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
