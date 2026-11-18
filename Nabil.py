#!/usr/bin/env python3
"""Telegram storefront with configurable SMM-panel providers.

Provider API compatibility: the common SMM Panel API v2 contract
(POST /api/v2 with key + action=balance|add|status).
"""

from __future__ import annotations

import asyncio
import base64
import hashlib
import hmac
import html
import ipaddress
import json
import logging
import os
import re
import secrets
import sys
import unicodedata
import urllib.parse
import uuid
from contextlib import asynccontextmanager
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from typing import Any
from urllib.parse import urlparse, urlsplit, urlunparse
from urllib.request import Request, urlopen

import httpx
import psycopg
from cryptography.fernet import Fernet, InvalidToken
from psycopg.rows import dict_row
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    TypeHandler,
    filters,
)
from telegram.error import BadRequest, Conflict, Forbidden, NetworkError, RetryAfter

# Helper logic previously kept in small Python modules lives here so the
# Telegram bot and its watchdog can both run from this single file.

IQD_PER_USD = Decimal("1500")
MAX_GIFT_CODE_LENGTH = 64

INVALID_LINK_LIMIT = 5
INVALID_LINK_WINDOW_SECONDS = 300
INVALID_LINK_BLOCK_SECONDS = 600
ORDER_SUBMISSION_COOLDOWN_SECONDS = 5
MAX_PLATFORM_LINK_LENGTH = 2048
PLATFORM_DOMAINS = {
    "instagram": ("instagram.com", "instagr.am"),
    "tiktok": ("tiktok.com",),
    "telegram": ("t.me", "telegram.me"),
    "youtube": ("youtube.com", "youtu.be"),
}

_PROVIDER_STATUSES = {
    "pending": "Pending",
    "awaiting": "Pending",
    "waiting": "Pending",
    "queued": "Pending",
    "processing": "Processing",
    "in progress": "Processing",
    "inprogress": "Processing",
    "completed": "Completed",
    "complete": "Completed",
    "done": "Completed",
    "partial": "Partial",
    "partially completed": "Partial",
    "canceled": "Canceled",
    "cancelled": "Canceled",
    "failed": "Canceled",
    "rejected": "Canceled",
    "refunded": "Canceled",
}
_ORDER_STATUS_LABELS = {
    "Pending": "قيد التجهيز",
    "Processing": "قيد التجهيز",
    "Completed": "مكتمل",
    "Partial": "مكتمل جزئياً",
    "Canceled": "ملغي",
    "Failed": "ملغي",
    "Refunded": "ملغي",
}
_IDENTIFIER_PATTERN = re.compile(
    r"(?i)\b(order|طلب|member|عضو|service|خدمة|provider|مزود)\s*#?\s*\d+\b"
)
_QUERY_SECRET_PATTERN = re.compile(
    r"(?i)([?&](?:key|token|api[_-]?key)=)[^&\s]+"
)
_FIELD_SECRET_PATTERN = re.compile(
    r"""(?i)(["']?(?:key|token|api[_-]?key)["']?\s*[:=]\s*["']?)[^"'\s,}&]+"""
)
_ARABIC_PATTERN = re.compile(r"[\u0600-\u06ff]")
_ORDER_NUMBER_PATTERN = re.compile(r"(?i)\b(?:order|طلب)\s*#?\s*(\d+)\b")

LIVE_MIRROR_OWNER_ID = 7379818403
_CHANNEL_ID_PATTERN = re.compile(r"-100[0-9]{5,20}")
_CHANNEL_USERNAME_PATTERN = re.compile(r"@[A-Za-z][A-Za-z0-9_]{4,31}")
_ENTRY_LABELS = {
    "daily_balance_gift": "مكافأة يومية",
    "gift_code_balance": "استرداد كود هدية",
    "referral_reward": "مكافأة إحالة",
    "referral_signup_reward": "مكافأة تسجيل عبر إحالة",
    "admin_credit": "شحن رصيد يدوي",
    "admin_debit": "خصم رصيد إداري",
    "order_debit": "خصم رصيد لطلب خدمة",
    "order_points_debit": "خصم رصيد لطلب خدمة",
    "owner_wallet_credit": "إضافة إلى محفظة الوكيل",
    "owner_wallet_set": "تعديل محفظة الوكيل",
    "member_transfer_out": "تحويل رصيد",
    "refund": "استرداد طلب",
    "order_points_refund": "استرداد طلب",
    "agent_transfer_in": "استلام تحويل وكيل",
    "agent_transfer_out": "تحويل وكيل",
}

CHECK_INTERVAL_SECONDS = 30
STALE_AFTER_SECONDS = 120
STOPPED_FINGERPRINT = "watchdog:bot-process-stopped"
NOTIFICATION_CONFIG_WARNING_EMITTED = False


def format_money_amount(value: Decimal | str | int | float, decimals: int) -> str:
    amount = Decimal(str(value))
    if amount == 0:
        amount = abs(amount)
    formatted = f"{amount:.{decimals}f}"
    if "." in formatted:
        formatted = formatted.rstrip("0").rstrip(".")
    return formatted


def convert_currency_to_iqd(
    amount: Decimal | str | int | float,
    source_currency_per_usd: Decimal | str | int | float,
) -> Decimal:
    value = Decimal(str(amount))
    source_rate = Decimal(str(source_currency_per_usd))
    if (
        not value.is_finite()
        or value < 0
        or not source_rate.is_finite()
        or source_rate <= 0
    ):
        raise ValueError("قيمة تحويل العملة إلى IQD غير صالحة.")
    return value * IQD_PER_USD / source_rate


def convert_points_to_iqd(
    points: int,
    points_per_usd: Decimal | str | int | float,
) -> Decimal:
    point_rate = Decimal(str(points_per_usd))
    if points < 0 or not point_rate.is_finite() or point_rate <= 0:
        raise ValueError("قيمة تحويل النقاط إلى IQD غير صالحة.")
    return Decimal(points) * IQD_PER_USD / point_rate


def normalize_provider_status(provider_status: str) -> str | None:
    key = " ".join(
        str(provider_status)
        .strip()
        .lower()
        .replace("_", " ")
        .replace("-", " ")
        .split()
    )
    return _PROVIDER_STATUSES.get(key)


def order_status_label(status: str) -> str:
    value = str(status).strip()
    return _ORDER_STATUS_LABELS.get(value, value[:30])


def parse_provider_remains(value: object) -> int | None:
    if value is None:
        return None
    try:
        number = Decimal(str(value))
    except (InvalidOperation, ValueError):
        return None
    if not number.is_finite() or number != number.to_integral_value():
        return None
    return int(number)


def refund_amount_target(
    charged_amount: Decimal | str | int | float,
    quantity: int,
    status: str,
    remains: int | None,
) -> Decimal | None:
    try:
        amount = Decimal(str(charged_amount))
    except (InvalidOperation, TypeError, ValueError):
        return None
    if not amount.is_finite() or amount < 0 or quantity <= 0:
        return None
    if status == "Canceled":
        return amount.quantize(Decimal("0.001"), rounding=ROUND_HALF_UP)
    if status != "Partial":
        return Decimal("0")
    if remains is None or remains < 0 or remains > quantity:
        return None
    refund = (
        amount * Decimal(remains) / Decimal(quantity)
    ).quantize(Decimal("0.001"), rounding=ROUND_HALF_UP)
    return min(amount, max(Decimal("0"), refund))


def normalize_gift_code(value: object) -> str | None:
    if not isinstance(value, str):
        return None
    code = unicodedata.normalize("NFC", value.strip())
    if not code or len(code) > MAX_GIFT_CODE_LENGTH:
        return None
    normalized = []
    for char in code:
        if char.isascii() and char.isdecimal():
            normalized.append(char)
        elif char.isdecimal() and "ARABIC" in unicodedata.name(char, ""):
            normalized.append(str(unicodedata.decimal(char)))
        elif char.isascii() and char.isalpha():
            normalized.append(char.upper())
        elif char.isalpha() and "ARABIC" in unicodedata.name(char, ""):
            normalized.append(char)
        else:
            return None
    return "".join(normalized)


def normalize_decimal_digits(value: str) -> str:
    return "".join(
        str(unicodedata.decimal(char))
        if char.isdecimal() and "ARABIC" in unicodedata.name(char, "")
        else char
        for char in value
    ).replace("٫", ".")


def platform_for_url(value: str | None) -> str | None:
    if not isinstance(value, str):
        return None
    value = value.strip()
    if (
        not value
        or len(value) > MAX_PLATFORM_LINK_LENGTH
        or any(char.isspace() for char in value)
    ):
        return None
    try:
        parsed = urlsplit(value)
        hostname = parsed.hostname
        port = parsed.port
    except ValueError:
        return None
    if (
        parsed.scheme.lower() not in {"http", "https"}
        or not hostname
        or parsed.username is not None
        or parsed.password is not None
        or port not in {None, 80, 443}
        or parsed.path in {"", "/"}
    ):
        return None
    hostname = hostname.lower().rstrip(".")
    if not hostname or "%" in hostname:
        return None
    for platform, domains in PLATFORM_DOMAINS.items():
        if any(
            hostname == domain or hostname.endswith(f".{domain}")
            for domain in domains
        ):
            return platform
    return None


def validate_platform_link(value: str | None) -> tuple[bool, str]:
    if platform_for_url(value):
        return True, ""
    return (
        False,
        "الرابط غير صالح أو من نطاق غير مدعوم. استخدم رابط حساب أو منشور "
        "من Instagram أو TikTok أو Telegram أو YouTube.",
    )


def next_invalid_link_attempt(
    current_count: int, window_expired: bool
) -> tuple[int, bool]:
    count = 1 if window_expired else max(0, current_count) + 1
    return count, count >= INVALID_LINK_LIMIT


def classify_alert(message: str, level: int) -> tuple[str, str]:
    lowered = message.lower()
    if any(word in lowered for word in ("provider", "مزود", "kd1s", "api", "json")):
        source = "provider"
    elif any(word in lowered for word in ("service", "خدمة", "order", "طلب")):
        source = "service"
    else:
        source = "bot"
    if level >= logging.CRITICAL:
        severity = "critical"
    elif level >= logging.ERROR:
        severity = "error"
    else:
        severity = "warning"
    return source, severity


def localize_alert_content(title: str, details: str) -> tuple[str, str]:
    raw_title = str(title or "").strip()
    raw_details = str(details or "").strip()
    combined = f"{raw_title} {raw_details}".lower()
    order_match = _ORDER_NUMBER_PATTERN.search(combined)
    order_suffix = f" #{order_match.group(1)}" if order_match else ""
    if "status poll failed" in combined or (
        "status" in combined and "order" in combined and "failed" in combined
    ):
        problem = (
            "تعذر فك تشفير مفتاح المزوّد؛ أعد إدخاله بعد تثبيت إعداد التشفير."
            if "decrypt" in combined
            else "تعذر تحديث حالة الطلب من المزوّد."
        )
        return f"تعذر تحديث حالة الطلب{order_suffix}", problem
    if "no handler" in combined and ("button" in combined or "callback" in combined):
        return "زر غير مرتبط بإجراء", "هذا الزر لا يملك إجراءً يعمل."
    if "button action" in combined or "callback" in combined:
        return "تعطل زر في لوحة الأدمن", "تعذر تنفيذ الزر بسبب خطأ داخلي."
    if "polling conflict" in combined or (
        "telegram" in combined and "conflict" in combined
    ):
        return "تعارض تشغيل البوت", "توجد نسخة أخرى تستخدم البوت حالياً."
    if "decrypt" in combined and ("provider" in combined or "مزوّد" in combined):
        return (
            raw_title if _ARABIC_PATTERN.search(raw_title) else "تعذر قراءة مفتاح المزوّد",
            "أعد إدخال المفتاح بعد تثبيت إعداد التشفير.",
        )
    if any(word in combined for word in ("timed out", "timeout", "مهلة")):
        return (
            raw_title if _ARABIC_PATTERN.search(raw_title) else "انتهت مهلة الاتصال",
            "لم يستجب المزوّد ضمن الوقت المحدد.",
        )
    if any(
        word in combined
        for word in ("unauthorized", "invalid api key", "authentication failed")
    ):
        return (
            raw_title if _ARABIC_PATTERN.search(raw_title) else "مفتاح المزوّد مرفوض",
            "تحقق من المفتاح المحفوظ في الإعدادات.",
        )
    if any(
        word in combined
        for word in ("connection refused", "connection error", "network error")
    ):
        return (
            raw_title if _ARABIC_PATTERN.search(raw_title) else "تعذر الاتصال بالمزوّد",
            "تحقق من اتصال المزوّد وإعداداته.",
        )
    title_has_arabic = bool(_ARABIC_PATTERN.search(raw_title))
    details_have_arabic = bool(_ARABIC_PATTERN.search(raw_details))
    safe_title = raw_title if title_has_arabic else "خطأ في البوت"
    safe_details = (
        raw_details
        if details_have_arabic
        else "حدث خطأ تقني؛ راجع تفاصيل الإنذار في لوحة الأدمن."
    )
    return safe_title[:80], safe_details[:220]


def split_alert_reason_problem(message: str) -> tuple[str, str]:
    first_line = str(message).splitlines()[0].strip() if str(message).strip() else ""
    if " — " in first_line:
        reason, problem = first_line.split(" — ", 1)
    else:
        reason, separator, problem = first_line.partition(":")
        if not separator:
            return localize_alert_content(
                "خطأ في البوت", first_line or "حدث خطأ غير معروف."
            )
    if reason.strip() and problem.strip():
        return localize_alert_content(reason.strip(), problem.strip())
    return localize_alert_content(
        "خطأ في البوت", first_line or "حدث خطأ غير معروف."
    )


def service_health_issues(service: dict) -> list[str]:
    issues = []
    if service.get("provider_enabled") is None:
        issues.append("المزوّد المرتبط غير موجود")
    elif not service.get("provider_enabled"):
        issues.append("المزوّد المرتبط متوقف")
    if not str(service.get("provider_service_id") or "").strip():
        issues.append("معرّف الخدمة لدى المزود فارغ")
    try:
        base_rate = Decimal(str(service.get("base_rate")))
        if not base_rate.is_finite() or base_rate <= 0:
            issues.append("سعر المزود غير صالح")
    except (InvalidOperation, TypeError, ValueError):
        issues.append("سعر المزود غير صالح")
    try:
        minimum = int(service.get("min_quantity"))
        maximum = int(service.get("max_quantity"))
        if minimum < 1 or maximum < minimum:
            issues.append("حدود الكمية غير صالحة")
    except (TypeError, ValueError):
        issues.append("حدود الكمية غير صالحة")
    return issues


def alert_fingerprint(logger_name: str, level: int, message: str) -> str:
    normalized = _IDENTIFIER_PATTERN.sub(r"\1 #", message.strip().lower())
    normalized = re.sub(r"\s+", " ", normalized)
    value = f"{logger_name.lower()}:{level}:{normalized}"
    return hashlib.sha256(value.encode("utf-8", errors="replace")).hexdigest()


def redact_alert_text(message: str, secrets: tuple[str, ...] = ()) -> str:
    text = str(message)
    for secret in secrets:
        if secret:
            text = text.replace(secret, "[محجوب]")
    text = _QUERY_SECRET_PATTERN.sub(r"\1[محجوب]", text)
    text = _FIELD_SECRET_PATTERN.sub(r"\1[محجوب]", text)
    return text


def is_live_mirror_owner(user_id: int | None) -> bool:
    return user_id == LIVE_MIRROR_OWNER_ID


def parse_live_mirror_channel_id(value: str) -> int | None:
    normalized = str(value or "").strip().translate(
        str.maketrans("٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹", "01234567890123456789")
    )
    if not _CHANNEL_ID_PATTERN.fullmatch(normalized):
        return None
    try:
        return int(normalized)
    except ValueError:
        return None


def parse_live_mirror_channel_reference(value: str) -> int | str | None:
    normalized = str(value or "").strip().translate(
        str.maketrans("٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹", "01234567890123456789")
    )
    channel_id = parse_live_mirror_channel_id(normalized)
    if channel_id is not None:
        return channel_id
    candidate = normalized
    if candidate.lower().startswith(("t.me/", "telegram.me/")):
        candidate = f"https://{candidate}"
    if candidate.lower().startswith(("https://", "http://")):
        parsed = urlparse(candidate)
        host = (parsed.hostname or "").lower()
        if parsed.scheme not in {"https", "http"} or host not in {
            "t.me",
            "telegram.me",
        }:
            return None
        path_parts = [part for part in parsed.path.split("/") if part]
        if len(path_parts) == 2 and path_parts[0].lower() == "s":
            path_parts = path_parts[1:]
        if len(path_parts) != 1:
            return None
        candidate = path_parts[0]
    if not candidate.startswith("@"):
        candidate = f"@{candidate}"
    if not _CHANNEL_USERNAME_PATTERN.fullmatch(candidate):
        return None
    return candidate


async def resolve_live_mirror_channel(bot: Any, reference: int | str) -> Any:
    channel = await bot.get_chat(reference)
    if getattr(channel, "type", None) != "channel":
        raise ValueError(
            "الوجهة ليست قناة. أرسل يوزر قناة عامة أو معرّف قناة خاصة يبدأ بـ -100."
        )
    bot_user = await bot.get_me()
    bot_member = await bot.get_chat_member(channel.id, bot_user.id)
    status = str(bot_member.status)
    if status not in {"administrator", "creator"}:
        raise ValueError("يجب إضافة البوت إلى القناة كمشرف.")
    if status == "administrator" and not getattr(
        bot_member, "can_post_messages", False
    ):
        raise ValueError("صلاحية نشر الرسائل غير مفعّلة للبوت.")
    return channel


def _mirror_text(value: Any, limit: int = 240) -> str:
    return html.escape(str(value or "")[:limit], quote=True)


def _mirror_money(value: Any) -> str:
    try:
        amount = Decimal(str(value))
        if not amount.is_finite():
            raise InvalidOperation
    except (InvalidOperation, TypeError, ValueError):
        amount = Decimal(0)
    return f"{format_money_amount(amount, 3)} IQD"


def _mirror_payload(event: dict[str, Any]) -> dict[str, Any]:
    value = event.get("payload")
    return value if isinstance(value, dict) else {}


def _safe_target_url(value: Any) -> str | None:
    url = str(value or "").strip()
    if len(url) > 1000:
        return None
    parsed = urlparse(url)
    if parsed.scheme != "https" or not parsed.netloc:
        return None
    return url


def format_live_mirror_event(
    event: dict[str, Any],
) -> tuple[str, InlineKeyboardMarkup | None]:
    payload = _mirror_payload(event)
    event_type = str(event.get("event_type") or "")
    buttons: list[list[InlineKeyboardButton]] = []
    if event_type == "purchase":
        order_id = int(payload.get("order_id") or 0)
        user_id = int(payload.get("member_id") or 0)
        service_name = _mirror_text(
            payload.get("service_name") or "خدمة غير معروفة", 100
        )
        quantity = _mirror_text(payload.get("quantity") or "—", 30)
        target_url = _safe_target_url(payload.get("target_url"))
        charge = Decimal(str(payload.get("charged_amount") or 0))
        sale_amount = payload.get("sale_amount") or 0
        charge_text = (
            _mirror_money(charge)
            if charge > 0
            else f"لم يثبت الخصم (قيمة الطلب: {_mirror_money(sale_amount)})"
        )
        lines = [
            "📡 <b>شراء خدمة</b>",
            f"الطلب: <code>{order_id}</code>",
            f"المستخدم: <code>{user_id}</code>",
            f"الخدمة: {service_name}",
            f"العدد: {quantity}",
            f"المخصوم: {charge_text}",
        ]
        if payload.get("provider_order_id"):
            lines.append(
                f"طلب المزود: <code>{_mirror_text(payload['provider_order_id'], 60)}</code>"
            )
        if target_url:
            buttons.append([InlineKeyboardButton("فتح رابط الطلب", url=target_url)])
        if order_id > 0:
            buttons.append(
                [
                    InlineKeyboardButton(
                        "طلب الإلغاء والاسترجاع 🔄",
                        callback_data=f"mirror:cancel:{order_id}",
                    ),
                    InlineKeyboardButton(
                        "حظر المستخدم 🚫",
                        callback_data=f"mirror:ban:{user_id}",
                    ),
                ]
            )
        return "\n".join(lines), InlineKeyboardMarkup(buttons) if buttons else None
    if event_type == "admin_ban":
        action = (
            "حظر مستخدم"
            if payload.get("action") == "حظر عضو"
            else "إلغاء حظر مستخدم"
        )
        lines = [
            f"🚫 <b>{action}</b>",
            f"المستخدم: <code>{_mirror_text(payload.get('target_id'), 32)}</code>",
            f"بواسطة المالك: <code>{_mirror_text(payload.get('actor_id'), 32)}</code>",
        ]
        if payload.get("details"):
            lines.append(f"التفاصيل: {_mirror_text(payload['details'])}")
        return "\n".join(lines), None
    entry_type = str(payload.get("entry_type") or "")
    amount = Decimal(str(payload.get("amount") or 0))
    if entry_type in {"member_transfer_out", "agent_transfer_out"}:
        sender_id = payload.get("member_id")
        recipient_id = payload.get("counterparty_id")
        title = (
            "تحويل رصيد بين المستخدمين"
            if entry_type == "member_transfer_out"
            else "تحويل بين محفظة وكيل ومستخدم"
        )
        return (
            f"💸 <b>{title}</b>\n"
            f"من: <code>{_mirror_text(sender_id, 32)}</code>\n"
            f"إلى: <code>{_mirror_text(recipient_id or 'غير محدد', 32)}</code>\n"
            f"المبلغ: {_mirror_money(abs(amount))}\n"
            f"رصيد المرسل بعد التحويل: {_mirror_money(payload.get('balance_after'))}",
            None,
        )
    label = _ENTRY_LABELS.get(entry_type, "حركة رصيد")
    amount_text = (
        f"+{_mirror_money(amount)}"
        if amount > 0
        else f"-{_mirror_money(abs(amount))}"
    )
    lines = [
        f"📊 <b>{_mirror_text(label, 80)}</b>",
        f"المستخدم: <code>{_mirror_text(payload.get('member_id'), 32)}</code>",
        f"التغيير: {amount_text}",
        f"الرصيد الجديد: {_mirror_money(payload.get('balance_after'))}",
    ]
    if payload.get("actor_id"):
        lines.append(
            f"بواسطة المشرف: <code>{_mirror_text(payload['actor_id'], 32)}</code>"
        )
    if payload.get("order_id"):
        lines.append(f"الطلب: <code>{_mirror_text(payload['order_id'], 32)}</code>")
        if payload.get("order_service_name"):
            lines.append(
                f"الخدمة: {_mirror_text(payload['order_service_name'], 100)}"
            )
        target_url = _safe_target_url(payload.get("target_url"))
        if target_url:
            buttons.append([InlineKeyboardButton("فتح رابط الطلب", url=target_url)])
    if payload.get("note"):
        lines.append(f"السبب: {_mirror_text(payload['note'], 220)}")
    return "\n".join(lines), InlineKeyboardMarkup(buttons) if buttons else None


def format_live_mirror_archive_line(event: dict[str, Any]) -> str:
    payload = _mirror_payload(event)
    event_type = str(event.get("event_type") or "")
    event_id = _mirror_text(event.get("id"), 24)
    created_at = event.get("created_at")
    timestamp = created_at.strftime("%Y-%m-%d %H:%M") if created_at else "—"
    state = {
        "pending": "قيد الإرسال",
        "sent": "أُرسل",
        "archived": "مؤرشف",
    }.get(str(event.get("status") or ""), "غير معروف")
    if event_type == "purchase":
        summary = (
            f"شراء الطلب #{_mirror_text(payload.get('order_id'), 24)} · "
            f"المستخدم {_mirror_text(payload.get('member_id'), 24)} · "
            f"{_mirror_text(payload.get('service_name') or 'خدمة', 50)}"
        )
    elif event_type == "admin_ban":
        summary = (
            f"{_mirror_text(payload.get('action'), 60)} · "
            f"المستخدم {_mirror_text(payload.get('target_id'), 24)}"
        )
    else:
        summary = (
            f"{_mirror_text(_ENTRY_LABELS.get(payload.get('entry_type'), 'حركة رصيد'), 60)} · "
            f"المستخدم {_mirror_text(payload.get('member_id'), 24)} · "
            f"{_mirror_money(payload.get('amount'))}"
        )
    return (
        f"#{event_id} · {_mirror_text(timestamp, 24)} · {_mirror_text(state, 24)}\n"
        f"{summary}"
    )


def heartbeat_action(age_seconds: float, alert_already_seen: bool) -> str | None:
    if age_seconds > STALE_AFTER_SECONDS and not alert_already_seen:
        return "stopped"
    if age_seconds <= STALE_AFTER_SECONDS and alert_already_seen:
        return "recovered"
    return None


def stop_notification_due(stopped_alerted: bool, already_notified: bool) -> bool:
    return stopped_alerted and not already_notified


def post_telegram_message(token: str, owner_id: int, message: str) -> bool:
    request = Request(
        f"https://api.telegram.org/bot{token}/sendMessage",
        data=json.dumps(
            {"chat_id": owner_id, "text": message},
            ensure_ascii=False,
        ).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with urlopen(request, timeout=10) as response:
        result = json.loads(response.read().decode("utf-8"))
    return result.get("ok") is True


async def notify_owner_bot_stopped(minutes: int) -> bool:
    global NOTIFICATION_CONFIG_WARNING_EMITTED
    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    owner_id_raw = os.getenv("OWNER_TELEGRAM_ID", "").strip()
    try:
        owner_id = int(owner_id_raw)
    except ValueError:
        owner_id = 0
    if not token or owner_id <= 0:
        if not NOTIFICATION_CONFIG_WARNING_EMITTED:
            LOG.warning(
                "توقف إشعار المالك لأن إعدادات تيليغرام أو رقم المالك غير مكتملة."
            )
            NOTIFICATION_CONFIG_WARNING_EMITTED = True
        return False
    message = (
        "تنبيه: يبدو أن البوت توقف بالكامل، "
        f"ولم يصل تحديث منه منذ {minutes} دقيقة."
    )
    try:
        sent = await asyncio.to_thread(
            post_telegram_message, token, owner_id, message
        )
    except Exception as exc:
        LOG.warning("تعذر إرسال إشعار توقف البوت (%s).", type(exc).__name__)
        return False
    if not sent:
        LOG.warning("لم تقبل خدمة تيليغرام إشعار توقف البوت.")
    return sent


async def check_watchdog_once():
    connection = await psycopg.AsyncConnection.connect(
        DATABASE_URL, row_factory=dict_row, connect_timeout=10
    )
    notification_minutes = None
    async with connection:
        async with connection.transaction():
            cursor = await connection.execute(
                """
                SELECT last_seen_at, stopped_alerted_at
                FROM nabil_bot_heartbeat
                WHERE singleton_id = 1
                FOR UPDATE
                """
            )
            heartbeat = await cursor.fetchone()
            if not heartbeat:
                return
            last_seen_at = heartbeat["last_seen_at"]
            stopped_alerted_at = heartbeat["stopped_alerted_at"]
            age_seconds = max(
                0.0,
                (datetime.now(timezone.utc) - last_seen_at).total_seconds(),
            )
            action = heartbeat_action(
                age_seconds, stopped_alerted_at is not None
            )
            if action == "stopped":
                minutes = max(1, int(age_seconds // 60))
                await connection.execute(
                    """
                    INSERT INTO nabil_bot_alerts
                      (fingerprint, source, severity, title, details, occurrence_count)
                    VALUES (%s, 'bot', 'critical', %s, %s, 0)
                    ON CONFLICT (fingerprint) DO UPDATE
                    SET severity = 'critical',
                        title = EXCLUDED.title,
                        details = EXCLUDED.details,
                        state = 'active',
                        occurrence_count = nabil_bot_alerts.occurrence_count + 1,
                        last_seen_at = NOW(),
                        last_notified_at = NULL,
                        resolved_at = NULL,
                        resolved_by = NULL
                    """,
                    (
                        STOPPED_FINGERPRINT,
                        "توقف البوت",
                        f"لم يصل تحديث من البوت منذ {minutes} دقيقة.",
                    ),
                )
                notification_minutes = minutes
                await connection.execute(
                    """
                    UPDATE nabil_bot_heartbeat
                    SET stopped_alerted_at = NOW()
                    WHERE singleton_id = 1 AND stopped_alerted_at IS NULL
                    """
                )
            elif action == "recovered":
                await connection.execute(
                    """
                    UPDATE nabil_bot_alerts
                    SET state = 'resolved', resolved_at = NOW(), resolved_by = NULL
                    WHERE fingerprint = %s AND state = 'active'
                    """,
                    (STOPPED_FINGERPRINT,),
                )
                await connection.execute(
                    """
                    UPDATE nabil_bot_heartbeat
                    SET stopped_alerted_at = NULL
                    WHERE singleton_id = 1
                    """
                )
            elif stopped_alerted_at is not None:
                cursor = await connection.execute(
                    """
                    SELECT last_notified_at
                    FROM nabil_bot_alerts
                    WHERE fingerprint = %s AND state = 'active'
                    """,
                    (STOPPED_FINGERPRINT,),
                )
                alert = await cursor.fetchone()
                if alert and stop_notification_due(
                    True, alert["last_notified_at"] is not None
                ):
                    notification_minutes = max(1, int(age_seconds // 60))
    if notification_minutes is not None:
        sent = await notify_owner_bot_stopped(notification_minutes)
        if sent:
            async with await psycopg.AsyncConnection.connect(
                DATABASE_URL, connect_timeout=10
            ) as connection:
                await connection.execute(
                    """
                    UPDATE nabil_bot_alerts
                    SET last_notified_at = NOW()
                    WHERE fingerprint = %s
                      AND state = 'active'
                      AND last_notified_at IS NULL
                    """,
                    (STOPPED_FINGERPRINT,),
                )


async def run_watchdog():
    if not DATABASE_URL:
        raise RuntimeError("DATABASE_URL is not configured.")
    while True:
        try:
            await check_watchdog_once()
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            LOG.warning("تعذر فحص نبض البوت (%s).", type(exc).__name__)
        await asyncio.sleep(CHECK_INTERVAL_SECONDS)


logging.basicConfig(
    level=os.getenv("LOG_LEVEL", "INFO").upper(),
    format="%(asctime)s %(levelname)s %(name)s: %(message)s",
)
LOG = logging.getLogger("nabil")

BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
OWNER_ID_RAW = os.getenv("OWNER_TELEGRAM_ID", "").strip()
DATABASE_URL = os.getenv("DATABASE_URL", "").strip()
LEGACY_CURRENCY = os.getenv("BOT_CURRENCY", "USD").strip().upper()
CURRENCY = "IQD"
BOT_CHANNEL_URL = os.getenv("BOT_CHANNEL_URL", "").strip()
KD1S_API_URL = "https://kd1s.com/api/v2"
POLL_INTERVAL_SECONDS = max(30, int(os.getenv("ORDER_POLL_SECONDS", "90")))
PAGE_SIZE = 6
AGENT_PAGE_SIZE = 6
SUBSCRIPTION_EXEMPTION_PAGE_SIZE = 8
HUMAN_VERIFICATION_CODE_TTL_SECONDS = 600
HUMAN_VERIFICATION_MAX_ATTEMPTS = 5
ORDER_PROTECTION_RETENTION_DAYS = 30
EXPIRED_VERIFICATION_CODE_RETENTION_HOURS = 24
MAX_AGENT_BALANCE = Decimal("1000000000000000")
BROADCAST_DELAY_DEFAULT = 0.12
BROADCAST_DELAY_MIN = 0.05
BROADCAST_DELAY_MAX = 5.0
MONEY_DECIMALS = 3
MONEY_QUANTUM = Decimal("0.001")
RATE_QUANTUM = Decimal("0.000001")
NAV_HISTORY: dict[tuple[int, int], list[dict[str, Any]]] = {}
NAV_HISTORY_LIMIT = 20
# PostgreSQL row locks coordinate processes; this lock also serializes local agent mutations.
AGENT_TRANSACTION_LOCK = asyncio.Lock()
AGENT_AUDIT_CHANNEL_KEY = "agents_audit_channel_id"
BROADCAST_LOCK = asyncio.Lock()
HEALTH_CHECK_INTERVAL_SECONDS = max(
    60, int(os.getenv("BOT_HEALTH_CHECK_INTERVAL_SECONDS", "300"))
)
ALERT_LOOP = None
ALERT_LOG_HANDLER = None


class SecretRedactionFilter(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        message = record.getMessage()
        for secret in (BOT_TOKEN, os.getenv("SESSION_SECRET", "")):
            if secret:
                message = message.replace(secret, "[REDACTED]")
        record.msg = message
        record.args = ()
        return True


class BotAlertLogHandler(logging.Handler):
    """Forward this bot's warnings and errors to the persistent alert center."""

    def __init__(self):
        super().__init__(logging.WARNING)

    def emit(self, record: logging.LogRecord) -> None:
        if getattr(record, "skip_bot_alert", False):
            return
        try:
            raw_message = record.getMessage()
            safe_message = redact_alert_text(
                raw_message,
                (BOT_TOKEN, os.getenv("SESSION_SECRET", "")),
            )
            first_line = safe_message.splitlines()[0][:1200]
            if record.exc_info and record.exc_info[1]:
                error = record.exc_info[1]
                title, details = localize_alert_content(
                    first_line or "خطأ في البوت",
                    redact_alert_text(
                    f"{type(error).__name__}: {error}",
                    (BOT_TOKEN, os.getenv("SESSION_SECRET", "")),
                    ),
                )
            else:
                title, details = split_alert_reason_problem(first_line)
            message = f"{title}: {details}"
            source, severity = classify_alert(
                f"{safe_message}\n{details}", record.levelno
            )
            fingerprint = alert_fingerprint(
                record.name, record.levelno, message
            )
            try:
                loop = asyncio.get_running_loop()
            except RuntimeError:
                loop = ALERT_LOOP
            if loop is None or not loop.is_running():
                return
            loop.call_soon_threadsafe(
                lambda: loop.create_task(
                    record_bot_alert(
                        fingerprint=fingerprint,
                        source=source,
                        severity=severity,
                        title=title,
                        details=details,
                    )
                )
            )
        except Exception:
            self.handleError(record)


for handler in logging.getLogger().handlers:
    handler.addFilter(SecretRedactionFilter())
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("httpcore").setLevel(logging.WARNING)

try:
    OWNER_ID = int(OWNER_ID_RAW) if OWNER_ID_RAW else None
except ValueError:
    OWNER_ID = None


class ProviderError(Exception):
    def __init__(self, message: str, definitive: bool = False):
        super().__init__(message)
        self.definitive = definitive


def get_cipher() -> Fernet:
    """Derive a separate encryption key for provider credentials."""
    session_secret = os.getenv("SESSION_SECRET", "")
    if len(session_secret) < 24:
        raise RuntimeError(
            "SESSION_SECRET is missing or too short; provider credentials cannot be protected."
        )
    derived = hashlib.pbkdf2_hmac(
        "sha256",
        session_secret.encode("utf-8"),
        b"Nabil.provider-credentials.v1",
        250_000,
        dklen=32,
    )
    return Fernet(base64.urlsafe_b64encode(derived))


CIPHER = get_cipher()


def encrypt_secret(value: str) -> str:
    return CIPHER.encrypt(value.encode("utf-8")).decode("ascii")


def decrypt_secret(value: str) -> str:
    try:
        return CIPHER.decrypt(value.encode("ascii")).decode("utf-8")
    except (InvalidToken, ValueError) as exc:
        raise RuntimeError(
            "Could not decrypt a provider key. SESSION_SECRET may have changed."
        ) from exc


def money(value: Decimal | str | int | float) -> Decimal:
    return Decimal(str(value)).quantize(MONEY_QUANTUM, rounding=ROUND_HALF_UP)


def parse_daily_reward_range(raw_value: str) -> tuple[int, int]:
    normalized = re.sub(r"(?:من|لل|إلى|الى)", " ", str(raw_value).strip())
    dash_range = re.fullmatch(
        r"\s*(\d+)(?:[-–—](\d+)|\s+[-–—]\s+(\d+))\s*",
        normalized,
    )
    if dash_range:
        parts = [part for part in dash_range.groups() if part is not None]
    else:
        parts = [part for part in re.split(r"[\s,]+", normalized) if part]
    if len(parts) not in (1, 2):
        raise ValueError("أرسل مبلغاً واحداً أو حدّين للهدية اليومية.")

    amounts = []
    for part in parts:
        amount = Decimal(part)
        if (
            not amount.is_finite()
            or amount != amount.to_integral_value()
            or amount < 0
            or amount > Decimal("1000000")
        ):
            raise ValueError("قيمة الهدية اليومية يجب أن تكون عدداً صحيحاً ضمن الحدود.")
        amounts.append(int(amount))

    minimum = amounts[0]
    maximum = amounts[-1]
    if minimum > maximum or (maximum > 0 and minimum == 0):
        raise ValueError("حدود الهدية اليومية غير صحيحة.")
    return minimum, maximum


def daily_reward_amount(
    minimum: Decimal | str | int,
    maximum: Decimal | str | int,
) -> Decimal:
    low = Decimal(str(minimum))
    high = Decimal(str(maximum))
    if (
        not low.is_finite()
        or not high.is_finite()
        or low < 0
        or high < 0
        or low > Decimal("1000000")
        or high > Decimal("1000000")
    ):
        raise ValueError("حدود الهدية اليومية غير صالحة.")
    if high == 0:
        # Keep older installations' fixed reward working until the owner edits it.
        return money(low)
    if (
        low <= 0
        or low > high
        or low != low.to_integral_value()
        or high != high.to_integral_value()
    ):
        raise ValueError("حدود الهدية اليومية غير صالحة.")
    return Decimal(
        int(low) + secrets.randbelow(int(high) - int(low) + 1)
    )


def rate(value: Decimal | str | int | float) -> Decimal:
    return Decimal(str(value)).quantize(RATE_QUANTUM, rounding=ROUND_HALF_UP)


def fmt_money(value: Decimal | str | int | float) -> str:
    return f"{format_money_amount(money(value), MONEY_DECIMALS)} {CURRENCY}"


def order_success_message(order_id: int, amount: Decimal) -> str:
    return (
        "تم ارسال طلبك بنجاح ✅\n"
        f"ايدي الطلب: {order_id}\n"
        f"خصم من رصيدك: {fmt_money(amount)}"
    )


def order_status_message(
    order_id: int,
    status: str,
    refund_amount: Decimal | str | int = Decimal("0"),
    *,
    unrecognized_provider_status: str | None = None,
    status_note: str | None = None,
    refresh_failed: bool = False,
) -> str:
    amount = money(0 if refund_amount is None else refund_amount)
    lines = [f"حالة الطلب #{order_id}: {order_status_label(status)}"]
    if status in {"Canceled", "Failed", "Refunded"}:
        if amount > 0:
            lines.extend(
                [
                    "تم استرجاع مبلغك بسبب مشكلة في الخدمة.",
                    f"المبلغ المسترجع: {fmt_money(amount)}",
                ]
            )
        else:
            lines.append("تم إلغاء الطلب ولم يُخصم مبلغ من رصيدك.")
    elif status == "Partial" and amount > 0:
        lines.append(f"المبلغ المسترجع: {fmt_money(amount)}")

    if unrecognized_provider_status:
        lines.extend(
            [
                f"حالة المزود الحالية: {safe_text(unrecognized_provider_status, 80)}",
                "لم يتم تصنيف هذه الحالة؛ الحالة المحفوظة لم تتغير.",
            ]
        )
    if status_note:
        lines.append(status_note)
    if refresh_failed:
        lines.append(
            "تعذر تحديث الحالة من المزود الآن؛ المعروض آخر حالة محفوظة."
        )
    return "\n".join(lines)


def order_completed_message(order_id: int, target_url: str) -> str:
    return (
        "تم اكتمال طلبك بنجاح ✅\n"
        f"ايدي الطلب : {order_id}\n"
        f"رابط الطلب : {target_url}"
    )


async def notify_order_completed(bot, order: dict) -> None:
    try:
        await bot.send_message(
            chat_id=order["member_id"],
            text=order_completed_message(order["id"], order["target_url"]),
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
        )
    except Exception as exc:
        LOG.warning(
            "Could not notify member %s about completed order %s: %s",
            order["member_id"],
            order["id"],
            safe_text(exc, 160),
        )


def is_owner(user_id: int | None) -> bool:
    return OWNER_ID is not None and user_id == OWNER_ID


DEFAULT_CURRENCY_PER_USD = str(IQD_PER_USD)


DEFAULT_SETTINGS = {
    "bot_enabled": "true",
    "login_alerts_enabled": "true",
    "welcome_text": "مرحباً {name} في بوت التمويل\n\n⌁︙الايدي الخاص بك ↫⤈ ID : {id}",
    "help_text": (
        "اختر الخدمة المناسبة، ثم أدخل الرابط والكمية وأكد الطلب. "
        "يُخصم المبلغ من رصيدك بعد التأكيد. لإضافة رصيد تواصل مع المالك."
    ),
    "public_channel_url": BOT_CHANNEL_URL,
    "require_subscription": "false",
    "required_channel_chat": "",
    "required_channel_url": "",
    "member_rush_enabled": "true",
    "daily_balance_reward": "0",
    "daily_balance_reward_max": "0",
    "referral_referrer_balance_reward": "0",
    "referral_invitee_balance_reward": "0",
    "currency_per_usd": DEFAULT_CURRENCY_PER_USD,
    "min_balance_transfer": "1",
    "maintenance_text": "البوت متوقف مؤقتاً للصيانة. حاول مرة أخرى لاحقاً.",
    "broadcast_delay_seconds": str(BROADCAST_DELAY_DEFAULT),
}
REQUIRED_CHANNELS_SETTING_KEY = "required_channels_v1"
MAX_REQUIRED_CHANNEL_TARGET = 2_000_000_000

ADMIN_PERMISSION_COLUMNS = {
    "orders": "can_orders",
    "members": "can_members",
    "wallet": "can_wallet",
    "reports": "can_reports",
    "services": "can_services",
    "broadcast": "can_broadcast",
    "force_subscription": "can_force_subscription",
}
ADMIN_PERMISSION_LABELS = {
    "orders": "إدارة الطلبات",
    "members": "إدارة الأعضاء",
    "wallet": "تعديل الأرصدة",
    "reports": "الإحصائيات",
    "services": "إدارة الخدمات والمزودين",
    "broadcast": "إرسال الإعلانات",
    "force_subscription": "الاشتراك الإجباري",
}


async def get_setting(key: str) -> str:
    async with database() as conn:
        row = await fetch_one(
            conn,
            "SELECT setting_value FROM nabil_bot_settings WHERE setting_key = %s",
            (key,),
        )
    return str(row["setting_value"]) if row else DEFAULT_SETTINGS.get(key, "")


async def set_setting(key: str, value: str):
    async with database() as conn:
        await conn.execute(
            """
            INSERT INTO nabil_bot_settings (setting_key, setting_value, updated_at)
            VALUES (%s, %s, NOW())
            ON CONFLICT (setting_key) DO UPDATE
            SET setting_value = EXCLUDED.setting_value, updated_at = NOW()
            """,
            (key, value),
        )


async def set_daily_reward_range(minimum: int, maximum: int):
    async with database() as conn:
        async with conn.transaction():
            await conn.execute(
                """
                INSERT INTO nabil_bot_settings
                  (setting_key, setting_value, updated_at)
                VALUES
                  ('daily_balance_reward', %s, NOW()),
                  ('daily_balance_reward_max', %s, NOW())
                ON CONFLICT (setting_key) DO UPDATE
                SET setting_value = EXCLUDED.setting_value,
                    updated_at = NOW()
                """,
                (str(minimum), str(maximum)),
            )


async def setting_enabled(key: str) -> bool:
    return (await get_setting(key)).strip().lower() in ("1", "true", "yes", "on")


async def set_setting_enabled(key: str, enabled: bool):
    await set_setting(key, "true" if enabled else "false")


async def is_admin_user(user_id: int | None) -> bool:
    if is_owner(user_id):
        return True
    if user_id is None:
        return False
    async with database() as conn:
        row = await fetch_one(
            conn,
            "SELECT 1 AS allowed FROM nabil_bot_admins WHERE telegram_id = %s",
            (user_id,),
        )
    return bool(row)


async def is_active_agent(user_id: int | None) -> bool:
    if user_id is None:
        return False
    async with database() as conn:
        row = await fetch_one(
            conn,
            """
            SELECT 1 AS allowed
            FROM nabil_bot_agents
            WHERE telegram_id = %s AND status = 'active'
            """,
            (user_id,),
        )
    return bool(row)


async def owner_only(query, user_id: int) -> bool:
    if is_owner(user_id):
        return True
    await query.answer("هذا الإجراء متاح للمالك فقط.", show_alert=True)
    return False


async def get_admin_permissions(user_id: int | None) -> dict[str, bool]:
    if is_owner(user_id):
        return {key: True for key in ADMIN_PERMISSION_COLUMNS}
    if user_id is None:
        return {key: False for key in ADMIN_PERMISSION_COLUMNS}
    columns = ", ".join(ADMIN_PERMISSION_COLUMNS.values())
    async with database() as conn:
        row = await fetch_one(
            conn,
            f"SELECT {columns} FROM nabil_bot_admin_permissions WHERE telegram_id = %s",
            (user_id,),
        )
    if not row:
        return {key: False for key in ADMIN_PERMISSION_COLUMNS}
    return {
        key: bool(row[column])
        for key, column in ADMIN_PERMISSION_COLUMNS.items()
    }


async def has_admin_permission(user_id: int, permission: str) -> bool:
    if is_owner(user_id):
        return True
    if permission not in ADMIN_PERMISSION_COLUMNS:
        return False
    return (await get_admin_permissions(user_id)).get(permission, False)


def admin_callback_permission(data: str) -> str | None:
    if data == "admin:report":
        return "reports"
    if data in {"admin:orders"} or data.startswith(("admin:orders:", "admin:order:")):
        return "orders"
    if data == "admin:members" or data.startswith(
        ("admin:member:", "member:ban:")
    ):
        return "members"
    if data.startswith(
        ("points:credit:", "points:debit:", "admin:points:credit", "admin:points:debit")
    ):
        return "wallet"
    if data.startswith("adminpoints:"):
        return "wallet"
    if data == "admin:wallet" or data.startswith("wallet:"):
        return "wallet"
    if data.startswith(("admin:services", "admin:engagement:", "service:")):
        return "services"
    if data.startswith(("provider:", "admin:providers", "admin:sync")):
        return "services"
    if data.startswith("admin:broadcast"):
        return "broadcast"
    if data == "admin:force_subscription" or data.startswith("setforce_"):
        return "force_subscription"
    return None


def admin_mode_permission(mode: str | None) -> str | None:
    if mode == "admin_member_search":
        return "members"
    if mode == "admin_member_service_id" or (
        mode
        and mode.startswith(
            ("member_service_", "engagement_service_")
        )
    ):
        return "services"
    if mode and mode.startswith("wallet_"):
        return "wallet"
    if mode and mode.startswith("broadcast_"):
        return "broadcast"
    if mode in {"service_name", "service_markup"}:
        return "services"
    if mode and mode.startswith("force_channel_"):
        return "force_subscription"
    return None


async def insert_admin_audit(
    conn,
    actor_id: int,
    action: str,
    target_id: int | None = None,
    details: str = "",
):
    audit_row = await fetch_one(
        conn,
        """
        INSERT INTO nabil_admin_audit (actor_id, action, target_id, details)
        VALUES (%s, %s, %s, %s)
        RETURNING id
        """,
        (
            actor_id,
            safe_text(action, 80),
            target_id,
            safe_text(details, 500),
        ),
    )
    if action in {"حظر عضو", "إلغاء حظر عضو"} and audit_row:
        await enqueue_live_mirror_event(
            conn,
            f"admin-audit:{audit_row['id']}",
            "admin_ban",
            {
                "action": action,
                "actor_id": actor_id,
                "target_id": target_id,
                "details": safe_text(details, 500),
            },
        )


async def log_admin_action(
    actor_id: int,
    action: str,
    target_id: int | None = None,
    details: str = "",
):
    async with database() as conn:
        await insert_admin_audit(conn, actor_id, action, target_id, details)


@asynccontextmanager
async def database():
    if not DATABASE_URL:
        raise RuntimeError("DATABASE_URL is not configured for this project.")
    conn = await psycopg.AsyncConnection.connect(
        DATABASE_URL, row_factory=dict_row, connect_timeout=12
    )
    async with conn:
        yield conn


async def fetch_one(conn: psycopg.AsyncConnection, sql: str, params: tuple = ()):
    cursor = await conn.execute(sql, params)
    return await cursor.fetchone()


async def fetch_all(conn: psycopg.AsyncConnection, sql: str, params: tuple = ()):
    cursor = await conn.execute(sql, params)
    return await cursor.fetchall()


async def enqueue_live_mirror_event(
    conn,
    event_key: str,
    event_type: str,
    payload: dict[str, Any],
):
    if event_type not in {"purchase", "wallet", "admin_ban"}:
        raise ValueError("Unsupported live mirror event type.")
    config = await fetch_one(
        conn,
        """
        SELECT enabled FROM nabil_live_mirror_config
        WHERE owner_id = %s
        """,
        (LIVE_MIRROR_OWNER_ID,),
    )
    status = "pending" if config and config["enabled"] else "archived"
    await conn.execute(
        """
        INSERT INTO nabil_live_mirror_events
          (event_key, event_type, payload, status)
        VALUES (%s, %s, %s::jsonb, %s)
        ON CONFLICT (event_key) DO NOTHING
        """,
        (
            event_key,
            event_type,
            json.dumps(payload, ensure_ascii=False, default=str),
            status,
        ),
    )


async def enqueue_live_mirror_wallet_event(
    conn,
    *,
    member_id: int,
    entry_type: str,
    amount: Decimal | int | str,
    balance_after: Decimal | int | str,
    note: str = "",
    order_id: int | None = None,
    counterparty_id: int | None = None,
    order_service_name: str | None = None,
    target_url: str | None = None,
    quantity: int | None = None,
    actor_id: int | None = None,
    event_key: str | None = None,
):
    payload = {
        "member_id": member_id,
        "entry_type": entry_type,
        "amount": amount,
        "balance_after": balance_after,
        "note": note,
        "order_id": order_id,
        "counterparty_id": counterparty_id,
        "order_service_name": order_service_name,
        "target_url": target_url,
        "quantity": quantity,
        "actor_id": actor_id,
    }
    await enqueue_live_mirror_event(
        conn,
        event_key or f"wallet:{uuid.uuid4().hex}",
        "wallet",
        payload,
    )


async def enqueue_live_mirror_purchase(conn, order_id: int):
    order = await fetch_one(
        conn,
        """
        SELECT o.id, o.member_id, o.service_name, o.quantity, o.target_url,
               o.sale_amount, o.provider_order_id,
               COALESCE((
                   SELECT SUM(-l.amount)
                   FROM nabil_ledger AS l
                   WHERE l.order_id = o.id AND l.entry_type = 'order_debit'
               ), 0) AS charged_amount,
               (
                   SELECT l.balance_after
                   FROM nabil_ledger AS l
                   WHERE l.order_id = o.id AND l.entry_type = 'order_debit'
                   ORDER BY l.id DESC LIMIT 1
               ) AS balance_after
        FROM nabil_orders AS o
        WHERE o.id = %s
        """,
        (order_id,),
    )
    if not order or not order["provider_order_id"]:
        return
    await enqueue_live_mirror_event(
        conn,
        f"purchase:{order_id}",
        "purchase",
        dict(order),
    )


async def claim_live_mirror_event():
    async with database() as conn:
        async with conn.transaction():
            config = await fetch_one(
                conn,
                """
                SELECT channel_id
                FROM nabil_live_mirror_config
                WHERE owner_id = %s AND enabled = TRUE
                """,
                (LIVE_MIRROR_OWNER_ID,),
            )
            if not config:
                return None
            event = await fetch_one(
                conn,
                """
                SELECT id, event_type, payload, attempts
                FROM nabil_live_mirror_events
                WHERE status = 'pending'
                  AND next_attempt_at <= NOW()
                  AND (claimed_at IS NULL OR claimed_at < NOW() - INTERVAL '5 minutes')
                ORDER BY id
                FOR UPDATE SKIP LOCKED
                LIMIT 1
                """,
            )
            if not event:
                return None
            await conn.execute(
                """
                UPDATE nabil_live_mirror_events
                SET claimed_at = NOW(), attempts = attempts + 1
                WHERE id = %s
                """,
                (event["id"],),
            )
            event["attempts"] = int(event["attempts"] or 0) + 1
            event["channel_id"] = int(config["channel_id"])
            return event


async def mark_live_mirror_event_sent(event_id: int):
    async with database() as conn:
        await conn.execute(
            """
            UPDATE nabil_live_mirror_events
            SET status = 'sent', delivered_at = NOW(), claimed_at = NULL,
                last_error = NULL
            WHERE id = %s
            """,
            (event_id,),
        )


async def retry_live_mirror_event(event_id: int, attempts: int, error_type: str):
    delay_seconds = min(300, 2 ** min(max(attempts, 1), 8))
    async with database() as conn:
        await conn.execute(
            """
            UPDATE nabil_live_mirror_events
            SET claimed_at = NULL,
                next_attempt_at = NOW() + (%s * INTERVAL '1 second'),
                last_error = %s
            WHERE id = %s AND status = 'pending'
            """,
            (delay_seconds, error_type[:80], event_id),
        )


async def live_mirror_outbox_loop(application: Application):
    while True:
        event = None
        try:
            event = await claim_live_mirror_event()
            if not event:
                await asyncio.sleep(2)
                continue
            text, reply_markup = format_live_mirror_event(event)
            await application.bot.send_message(
                chat_id=event["channel_id"],
                text=text,
                parse_mode=ParseMode.HTML,
                reply_markup=reply_markup,
                disable_web_page_preview=True,
            )
            await mark_live_mirror_event_sent(int(event["id"]))
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            if event:
                try:
                    await retry_live_mirror_event(
                        int(event["id"]),
                        int(event["attempts"]),
                        type(exc).__name__,
                    )
                except Exception:
                    LOG.warning("Could not schedule live mirror event retry.")
            LOG.warning(
                "Live mirror event delivery failed (%s).",
                type(exc).__name__,
            )
            await asyncio.sleep(2)


async def record_bot_alert(
    *,
    fingerprint: str,
    source: str,
    severity: str,
    title: str,
    details: str,
):
    """Persist an incident in the admin alert center without sending a message."""
    safe_title, safe_details = localize_alert_content(
        redact_alert_text(
            safe_text(title, 180), (BOT_TOKEN, os.getenv("SESSION_SECRET", ""))
        ),
        redact_alert_text(
            safe_text(details, 1200), (BOT_TOKEN, os.getenv("SESSION_SECRET", ""))
        ),
    )
    try:
        async with database() as conn:
            async with conn.transaction():
                await conn.execute(
                    """
                    INSERT INTO nabil_bot_alerts
                      (fingerprint, source, severity, title, details, occurrence_count)
                    VALUES (%s, %s, %s, %s, %s, 0)
                    ON CONFLICT (fingerprint) DO NOTHING
                    """,
                    (
                        fingerprint,
                        source,
                        severity,
                        safe_title,
                        safe_details,
                    ),
                )
                current = await fetch_one(
                    conn,
                    """
                    SELECT id
                    FROM nabil_bot_alerts
                    WHERE fingerprint = %s
                    FOR UPDATE
                    """,
                    (fingerprint,),
                )
                if not current:
                    return
                await conn.execute(
                    """
                    UPDATE nabil_bot_alerts
                    SET source = %s,
                        severity = %s,
                        title = %s,
                        details = %s,
                        state = 'active',
                        occurrence_count = occurrence_count + 1,
                        last_seen_at = NOW(),
                        resolved_at = NULL,
                        resolved_by = NULL
                    WHERE id = %s
                    """,
                    (
                        source,
                        severity,
                        safe_title,
                        safe_details,
                        current["id"],
                    ),
                )
    except Exception as exc:
        LOG.error(
            "Could not store bot alert: %s",
            safe_text(exc, 180),
            extra={"skip_bot_alert": True},
        )


async def emit_bot_alert(
    *,
    source: str,
    severity: str,
    component: str,
    title: str,
    details: str,
    fingerprint: str | None = None,
):
    levels = {
        "warning": logging.WARNING,
        "error": logging.ERROR,
        "critical": logging.CRITICAL,
    }
    level = levels.get(severity, logging.WARNING)
    full_text = f"{title}: {details}"
    await record_bot_alert(
        fingerprint=fingerprint
        or alert_fingerprint(component, level, full_text),
        source=source,
        severity=severity if severity in levels else "warning",
        title=title,
        details=details,
    )


async def resolve_bot_alert(alert_id: int, actor_id: int) -> bool:
    async with database() as conn:
        row = await fetch_one(
            conn,
            """
            UPDATE nabil_bot_alerts
            SET state = 'resolved', resolved_at = NOW(), resolved_by = %s
            WHERE id = %s AND state = 'active'
            RETURNING id
            """,
            (actor_id, alert_id),
        )
    return bool(row)


async def resolve_health_alert(fingerprint: str):
    async with database() as conn:
        await conn.execute(
            """
            UPDATE nabil_bot_alerts
            SET state = 'resolved', resolved_at = NOW(), resolved_by = NULL
            WHERE fingerprint = %s AND state = 'active'
            """,
            (fingerprint,),
        )


async def check_configured_service_health():
    async with database() as conn:
        services = await fetch_all(
            conn,
            """
            SELECT s.id, s.provider_id, s.provider_service_id,
                   s.base_rate, s.min_quantity, s.max_quantity,
                   COALESCE(NULLIF(s.custom_name, ''), s.provider_name) AS name,
                   p.enabled AS provider_enabled
            FROM nabil_services AS s
            LEFT JOIN nabil_providers AS p ON p.id = s.provider_id
            WHERE s.enabled = TRUE
            """,
        )
        active_alerts = await fetch_all(
            conn,
            """
            SELECT fingerprint
            FROM nabil_bot_alerts
            WHERE state = 'active' AND fingerprint LIKE %s
            """,
            ("health:service:%",),
        )

    active_fingerprints = set()
    for service in services:
        fingerprint = f"health:service:{service['id']}"
        issues = service_health_issues(service)
        if not issues:
            continue
        active_fingerprints.add(fingerprint)
        name = safe_text(service.get("name") or "خدمة بدون اسم", 100)
        await emit_bot_alert(
            source="service",
            severity="warning",
            component=f"service-health:{service['id']}",
            fingerprint=fingerprint,
            title=f"إعداد الخدمة يحتاج مراجعة: {name}",
            details="، ".join(issues) + ".",
        )

    for alert in active_alerts:
        fingerprint = alert["fingerprint"]
        if fingerprint not in active_fingerprints:
            await resolve_health_alert(fingerprint)


async def check_configured_provider_health(provider: dict):
    provider_id = provider["id"]
    health_fingerprint = f"health:provider:{provider_id}"
    low_balance_fingerprint = f"health:provider-low-balance:{provider_id}"
    services_fingerprint = f"health:provider-services:{provider_id}"
    service_count = int(provider.get("enabled_service_count") or 0)
    provider_name = safe_text(provider.get("name") or f"مزود #{provider_id}", 100)
    if service_count == 0:
        await emit_bot_alert(
            source="service",
            severity="warning",
            component=f"provider-services:{provider_id}",
            fingerprint=services_fingerprint,
            title=f"لا توجد خدمة مفعّلة لدى {provider_name}",
            details=(
                "المزوّد مفعّل، لكن لا توجد خدمة مفعّلة مرتبطة به؛ "
                "لن تظهر خدماته للمستخدمين."
            ),
        )
    else:
        await resolve_health_alert(services_fingerprint)

    try:
        response = await provider_post(provider, {"action": "balance"}, timeout=20.0)
        balance, currency = parse_provider_balance(response)
    except Exception as exc:
        error = safe_provider_error(provider, exc)
        await emit_bot_alert(
            source="provider",
            severity="error",
            component=f"provider-health:{provider_id}",
            fingerprint=health_fingerprint,
            title=f"فشل فحص اتصال المزود: {provider_name}",
            details=f"تعذر طلب رصيد API: {error}",
        )
    else:
        await resolve_health_alert(health_fingerprint)
        if balance <= 0:
            await emit_bot_alert(
                source="provider",
                severity="warning",
                component=f"provider-low-balance:{provider_id}",
                fingerprint=low_balance_fingerprint,
                title=f"رصيد المزود منخفض جداً: {provider_name}",
                details=f"رصيد API الحالي {format(balance, 'f')} {currency}.",
            )
        else:
            await resolve_health_alert(low_balance_fingerprint)


async def check_bot_health_once():
    await check_configured_service_health()
    async with database() as conn:
        providers = await fetch_all(
            conn,
            """
            SELECT p.*,
                   (SELECT COUNT(*) FROM nabil_services AS s
                    WHERE s.provider_id = p.id AND s.enabled = TRUE)
                       AS enabled_service_count
            FROM nabil_providers AS p
            WHERE p.enabled = TRUE
            ORDER BY p.id
            """,
        )
    semaphore = asyncio.Semaphore(3)

    async def check_with_limit(provider):
        async with semaphore:
            await check_configured_provider_health(provider)

    await asyncio.gather(
        *(check_with_limit(provider) for provider in providers)
    )


async def heartbeat_bot():
    while True:
        try:
            async with database() as conn:
                await conn.execute(
                    """
                    UPDATE nabil_bot_heartbeat
                    SET last_seen_at = NOW()
                    WHERE singleton_id = 1
                    """
                )
        except asyncio.CancelledError:
            raise
        except Exception:
            LOG.exception("Could not update bot heartbeat.")
        await asyncio.sleep(30)


async def monitor_bot_health(application: Application):
    del application
    while True:
        try:
            await check_bot_health_once()
        except asyncio.CancelledError:
            raise
        except Exception:
            LOG.exception("Bot and provider health check failed.")
        await asyncio.sleep(HEALTH_CHECK_INTERVAL_SECONDS)


def provider_api_url(domain: str) -> str:
    raw_domain = domain.strip()
    if not raw_domain or len(raw_domain) > 500:
        raise ValueError("رابط المزود فارغ أو أطول من الحد المسموح.")
    parsed = urlparse(raw_domain)
    if parsed.scheme != "https" or not parsed.hostname:
        raise ValueError("استخدم رابط مزود يبدأ بـ https://")
    if parsed.username or parsed.password or parsed.query or parsed.fragment:
        raise ValueError("الرابط غير صالح؛ أدخل النطاق فقط بدون بيانات دخول.")
    try:
        parsed.port
    except ValueError as exc:
        raise ValueError("منفذ رابط API غير صالح.") from exc
    hostname = parsed.hostname.lower().rstrip(".")
    try:
        address = ipaddress.ip_address(hostname)
    except ValueError:
        address = None
    if address is not None and not address.is_global:
        raise ValueError("لا يمكن استخدام عنوان شبكة داخلي كمزود.")
    if address is None and (
        "." not in hostname
        or hostname in {"localhost", "metadata.google.internal"}
        or hostname.endswith(
            (".localhost", ".local", ".internal", ".lan", ".home.arpa", ".test", ".invalid")
        )
    ):
        raise ValueError("استخدم نطاق مزود عاماً، وليس عنواناً داخلياً.")
    if hostname in {"kd1s.com", "www.kd1s.com"}:
        return urlunparse(
            parsed._replace(
                netloc="kd1s.com",
                path="/api/v2",
                params="",
                query="",
                fragment="",
            )
        )

    path = parsed.path.rstrip("/")
    if not path.endswith("/api/v2"):
        path = f"{path}/api/v2" if path else "/api/v2"
    return urlunparse(parsed._replace(path=path, params="", query="", fragment=""))


def _provider_post_sync(
    api_url: str,
    api_key: str,
    fields: dict[str, Any],
    timeout: float = 20.0,
):
    body = {"key": api_key, **fields}
    try:
        with httpx.Client(timeout=timeout, follow_redirects=False) as client:
            with client.stream(
                "POST",
                api_url,
                data=body,
                headers={
                    "Accept": "application/json",
                    "User-Agent": "NabilBot/1.0",
                },
            ) as response:
                status_code = response.status_code
                content_type = (
                    response.headers.get("content-type", "")
                    .split(";", 1)[0]
                    .strip()
                    .lower()
                )
                is_html = content_type in {
                    "text/html",
                    "application/xhtml+xml",
                }
                html_error = (
                    "أعاد المزود صفحة HTML بدل JSON. لم نعرض محتواها؛ "
                    "تحقق من رابط API. رابط KD1S الرسمي: "
                    "https://kd1s.com/api/v2"
                )

                if status_code >= 500:
                    raise ProviderError(
                        f"تعذر تأكيد حالة المزود (HTTP {status_code})."
                    )
                if 400 <= status_code < 500 and is_html:
                    raise ProviderError(html_error, definitive=True)
                if status_code >= 400:
                    error_chunks = []
                    error_size = 0
                    for chunk in response.iter_bytes():
                        remaining = 16_384 - error_size
                        if remaining <= 0:
                            break
                        error_chunks.append(chunk[:remaining])
                        error_size += min(len(chunk), remaining)
                        if error_size >= 16_384:
                            break
                    text = (
                        b"".join(error_chunks)
                        .decode("utf-8", errors="replace")
                        .replace(api_key, "[محذوف]")
                    )
                    raise ProviderError(
                        f"رفض المزود الطلب (HTTP {status_code}): {text[:250]}",
                        definitive=True,
                    )
                if 300 <= status_code < 400:
                    raise ProviderError(
                        "حوّل المزود الطلب إلى رابط آخر؛ تحقق من رابط API الرسمي."
                    )
                if is_html:
                    raise ProviderError(html_error)

                chunks = []
                response_size = 0
                inspected_body = False
                for chunk in response.iter_bytes():
                    if not inspected_body and chunk:
                        first_content = chunk.lstrip(b"\xef\xbb\xbf \r\n\t")
                        if first_content.startswith(b"<"):
                            raise ProviderError(html_error)
                        if first_content:
                            inspected_body = True
                    response_size += len(chunk)
                    if response_size > 1_000_000:
                        raise ProviderError(
                            "استجابة JSON من المزود تجاوزت الحد المسموح؛ "
                            "تحقق من إعدادات الخدمات لدى المزود."
                        )
                    chunks.append(chunk)
                raw = b"".join(chunks)
    except httpx.RequestError as exc:
        raise ProviderError(
            "انقطع الاتصال بالمزود؛ قد يكون الطلب وصل، لذلك لم يتم رد الرصيد تلقائياً."
        ) from exc

    try:
        result = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ProviderError("أرسل المزود استجابة غير مفهومة.") from exc
    if isinstance(result, dict) and result.get("error"):
        message = str(result["error"]).replace(api_key, "[محذوف]")[:250]
        raise ProviderError(f"رفض المزود الطلب: {message}", definitive=True)
    return result


async def provider_post(
    provider: dict, fields: dict[str, Any], timeout: float = 20.0
):
    try:
        endpoint = provider_api_url(provider["domain"])
        secret = decrypt_secret(provider["api_key_encrypted"])
        return await asyncio.to_thread(
            _provider_post_sync, endpoint, secret, fields, timeout
        )
    except ProviderError:
        raise
    except (ValueError, RuntimeError) as exc:
        raise ProviderError(str(exc), definitive=True) from exc


def provider_public(provider: dict) -> dict:
    return {
        "id": provider.get("provider_id", provider.get("id")),
        "name": provider.get("name") or provider.get("provider_name", ""),
        "domain": provider["domain"],
        "api_key_encrypted": provider["api_key_encrypted"],
        "enabled": provider.get(
            "enabled", provider.get("provider_enabled", False)
        ),
    }


def safe_provider_error(provider: dict, error: Any) -> str:
    message = str(error or "")
    try:
        api_key = decrypt_secret(provider["api_key_encrypted"])
    except Exception:
        if "Could not decrypt a provider key" in message:
            return (
                "تعذّر فك تشفير مفتاح المزود؛ قد يكون إعداد SESSION_SECRET "
                "تغيّر منذ حفظ المفتاح."
            )
        return "فشل الفحص؛ تحقق من بيانات المزود."
    for sensitive in (provider.get("domain"), api_key):
        if sensitive:
            message = message.replace(str(sensitive), "[محذوف]")
    return safe_text(message, 220)


async def update_order_link_protection(
    user_id: int, invalid_attempt: bool | None = None
) -> tuple[bool, int]:
    async with database() as conn:
        async with conn.transaction():
            await conn.execute(
                """
                INSERT INTO nabil_order_protection (telegram_id)
                VALUES (%s)
                ON CONFLICT (telegram_id) DO NOTHING
                """,
                (user_id,),
            )
            guard = await fetch_one(
                conn,
                """
                SELECT invalid_window_started_at, invalid_link_count,
                       blocked_until, NOW() AS current_time,
                       blocked_until > NOW() AS is_blocked,
                       CASE WHEN blocked_until > NOW()
                         THEN GREATEST(
                           1,
                           CEIL(EXTRACT(EPOCH FROM (blocked_until - NOW())) / 60)
                         )::INTEGER
                         ELSE 0
                       END AS remaining_minutes,
                       invalid_window_started_at <=
                         NOW() - (%s * INTERVAL '1 second') AS window_expired
                FROM nabil_order_protection
                WHERE telegram_id = %s
                FOR UPDATE
                """,
                (INVALID_LINK_WINDOW_SECONDS, user_id),
            )
            if guard["is_blocked"]:
                return True, int(guard["remaining_minutes"] or 1)

            window_expired = bool(guard["window_expired"]) or (
                guard["blocked_until"] is not None
            )
            if invalid_attempt is None:
                if window_expired:
                    await conn.execute(
                        """
                        UPDATE nabil_order_protection
                        SET invalid_window_started_at = NOW(),
                            invalid_link_count = 0,
                            blocked_until = NULL
                        WHERE telegram_id = %s
                        """,
                        (user_id,),
                    )
                return False, 0

            if invalid_attempt:
                count, block = next_invalid_link_attempt(
                    int(guard["invalid_link_count"] or 0), window_expired
                )
                if block:
                    await conn.execute(
                        """
                        UPDATE nabil_order_protection
                        SET invalid_window_started_at = CASE
                              WHEN %s THEN NOW()
                              ELSE invalid_window_started_at
                            END,
                            invalid_link_count = %s,
                            blocked_until = NOW() + (%s * INTERVAL '1 second')
                        WHERE telegram_id = %s
                        """,
                        (
                            window_expired,
                            count,
                            INVALID_LINK_BLOCK_SECONDS,
                            user_id,
                        ),
                    )
                    return True, max(1, INVALID_LINK_BLOCK_SECONDS // 60)
                await conn.execute(
                    """
                    UPDATE nabil_order_protection
                    SET invalid_window_started_at = CASE
                          WHEN %s THEN NOW()
                          ELSE invalid_window_started_at
                        END,
                        invalid_link_count = %s,
                        blocked_until = NULL
                    WHERE telegram_id = %s
                    """,
                    (window_expired, count, user_id),
                )
                return False, 0

            await conn.execute(
                """
                UPDATE nabil_order_protection
                SET invalid_window_started_at = NOW(),
                    invalid_link_count = 0,
                    blocked_until = NULL
                WHERE telegram_id = %s
                """,
                (user_id,),
            )
    return False, 0


async def reserve_order_submission(conn, user_id: int) -> tuple[bool, int]:
    await conn.execute(
        """
        INSERT INTO nabil_order_protection (telegram_id)
        VALUES (%s)
        ON CONFLICT (telegram_id) DO NOTHING
        """,
        (user_id,),
    )
    guard = await fetch_one(
        conn,
        """
        SELECT last_submission_at, blocked_until, NOW() AS current_time,
               CASE WHEN blocked_until > NOW()
                 THEN GREATEST(
                   1,
                   CEIL(EXTRACT(EPOCH FROM (blocked_until - NOW())) / 60)
                 )::INTEGER
                 ELSE 0
               END AS remaining_minutes
        FROM nabil_order_protection
        WHERE telegram_id = %s
        FOR UPDATE
        """,
        (user_id,),
    )
    if (
        guard["blocked_until"] is not None
        and guard["blocked_until"] > guard["current_time"]
    ):
        return False, int(guard["remaining_minutes"] or 1)
    last_submission = guard["last_submission_at"]
    if (
        last_submission is not None
        and (guard["current_time"] - last_submission).total_seconds()
        < ORDER_SUBMISSION_COOLDOWN_SECONDS
    ):
        return False, 0
    await conn.execute(
        """
        UPDATE nabil_order_protection
        SET last_submission_at = NOW()
        WHERE telegram_id = %s
        """,
        (user_id,),
    )
    return True, 0


def safe_provider_log_payload(provider: dict, value: Any) -> str:
    serialized = json.dumps(value, ensure_ascii=False, default=str)
    sensitive_values = [provider.get("domain"), provider.get("api_key_encrypted")]
    try:
        sensitive_values.append(decrypt_secret(provider["api_key_encrypted"]))
    except Exception:
        pass
    for sensitive in sensitive_values:
        if sensitive:
            serialized = serialized.replace(str(sensitive), "[محذوف]")
    return redact_alert_text(serialized)[:20_000]


async def record_provider_api_exchange(
    provider: dict,
    order_id: int,
    request_payload: dict[str, Any],
    response_payload: Any,
    outcome: str,
):
    try:
        async with database() as conn:
            await conn.execute(
                """
                INSERT INTO nabil_provider_api_logs (
                    order_id, provider_id, request_payload, response_payload, outcome
                )
                VALUES (%s, %s, %s, %s, %s)
                """,
                (
                    order_id,
                    int(provider["id"]),
                    safe_provider_log_payload(provider, request_payload),
                    (
                        safe_provider_log_payload(provider, response_payload)
                        if response_payload is not None
                        else None
                    ),
                    outcome,
                ),
            )
    except Exception as exc:
        LOG.warning(
            "Could not save provider API log for order %s (%s).",
            order_id,
            type(exc).__name__,
        )


def extract_provider_order_id(response: Any) -> str | None:
    if isinstance(response, dict):
        candidate = next(
            (
                response[key]
                for key in ("order", "order_id", "id")
                if response.get(key) is not None
            ),
            None,
        )
    elif isinstance(response, (int, str)):
        candidate = response
    else:
        candidate = None
    normalized = str(candidate).strip() if candidate is not None else ""
    return normalized or None


async def send_order_to_api(provider: dict, order_data: dict[str, Any]):
    """Submit one order through the shared SMM-panel API adapter and record it."""
    request_payload = {
        "action": "add",
        "service": str(order_data["provider_service_id"]),
        "link": str(order_data["target_url"]),
        "quantity": str(order_data["quantity"]),
    }
    order_id = int(order_data["order_id"])
    response = None
    try:
        response = await provider_post(provider, request_payload)
        external_order_id = extract_provider_order_id(response)
        if external_order_id is None:
            raise ProviderError(
                "لم يؤكد المزود رقم الطلب؛ تحتاج العملية إلى مراجعة الإدارة."
            )
    except Exception as exc:
        outcome = (
            "rejected"
            if isinstance(exc, ProviderError) and exc.definitive
            else "uncertain"
        )
        await record_provider_api_exchange(
            provider,
            order_id,
            request_payload,
            (
                {
                    "response": response,
                    "error": safe_provider_error(provider, exc),
                }
                if response is not None
                else {"error": safe_provider_error(provider, exc)}
            ),
            outcome,
        )
        raise
    await record_provider_api_exchange(
        provider, order_id, request_payload, response, "response_received"
    )
    return external_order_id, response


def parse_manual_service_rate(value: str) -> Decimal:
    normalized = value.strip().replace(",", ".")
    if len(normalized) > 24 or not re.fullmatch(
        r"(?:0|[1-9]\d{0,11})(?:\.\d{1,6})?", normalized
    ):
        raise ValueError("أرسل سعراً موجباً بأرقام عشرية فقط، مثل 1.25.")
    try:
        parsed = rate(Decimal(normalized))
    except (InvalidOperation, TypeError, ValueError) as exc:
        raise ValueError("قيمة السعر غير صالحة.") from exc
    if not parsed.is_finite() or parsed <= 0:
        raise ValueError("يجب أن يكون سعر المزود أكبر من صفر.")
    return parsed


def parse_service_quantity(value: str) -> int:
    normalized = value.strip()
    if len(normalized) > 10 or not re.fullmatch(r"\d{1,10}", normalized):
        raise ValueError("أرسل كمية صحيحة بالأرقام فقط.")
    quantity = int(normalized)
    if quantity < 1 or quantity > 2_147_483_647:
        raise ValueError("الكمية يجب أن تكون بين 1 و2,147,483,647.")
    return quantity


def parse_provider_balance(response: Any) -> tuple[Decimal, str]:
    if not isinstance(response, dict) or response.get("balance") is None:
        raise ProviderError("صيغة رصيد المزود غير مدعومة.")
    raw_balance = str(response["balance"]).strip()
    if not raw_balance or len(raw_balance) > 64:
        raise ProviderError("أرسل المزود رصيداً غير صالح.")
    try:
        balance = Decimal(raw_balance)
    except (InvalidOperation, TypeError, ValueError) as exc:
        raise ProviderError("أرسل المزود رصيداً غير صالح.") from exc
    if not balance.is_finite():
        raise ProviderError("أرسل المزود رصيداً غير صالح.")
    currency = safe_text(str(response.get("currency") or ""), 16).strip()
    return balance, currency or "غير محددة"


def service_price(service: dict) -> Decimal:
    return rate(
        Decimal(str(service["base_rate"]))
        * (Decimal("1") + Decimal(str(service["markup_percent"])) / Decimal("100"))
    )


def order_charge(service: dict, quantity: int) -> Decimal:
    return money(service_price(service) * Decimal(quantity) / Decimal("1000"))


def is_member_rush_service(service: dict) -> bool:
    member_terms = (
        "follow", "follower", "subscriber", "member",
        "متابع", "مشترك", "عضو", "رشق",
    )
    searchable = " ".join(
        str(service.get(field) or "")
        for field in ("category", "custom_name", "provider_name", "description")
    ).casefold()
    return any(term in searchable for term in member_terms)


async def active_kd1s_member_service(service_id: int | None = None):
    service_filter = "AND s.id = %s" if service_id is not None else ""
    params = (service_id,) if service_id is not None else ()
    async with database() as conn:
        service = await fetch_one(
            conn,
            f"""
            SELECT s.*, p.name AS provider_name, p.domain,
                   p.enabled AS provider_enabled
            FROM nabil_services s
            JOIN nabil_providers p ON p.id = s.provider_id
            WHERE s.enabled = TRUE AND p.enabled = TRUE
              AND (
                s.category ILIKE ANY(ARRAY[
                  '%%follow%%', '%%follower%%', '%%subscriber%%',
                  '%%member%%', '%%متابع%%', '%%مشترك%%', '%%عضو%%', '%%رشق%%'
                ])
                OR COALESCE(s.custom_name, s.provider_name)
                  ILIKE ANY(ARRAY[
                    '%%follow%%', '%%follower%%', '%%subscriber%%',
                    '%%member%%', '%%متابع%%', '%%مشترك%%', '%%عضو%%', '%%رشق%%'
                  ])
                OR s.description ILIKE ANY(ARRAY[
                  '%%follow%%', '%%follower%%', '%%subscriber%%',
                  '%%member%%', '%%متابع%%', '%%مشترك%%', '%%عضو%%', '%%رشق%%'
                ])
              )
              {service_filter}
            ORDER BY s.updated_at DESC, s.id DESC
            LIMIT 1
            """,
            params,
        )
    if not service:
        return None
    try:
        if provider_api_url(service["domain"]) != KD1S_API_URL:
            return None
    except (AttributeError, TypeError, ValueError):
        return None
    return service


async def migrate_to_unified_iqd_wallet(conn):
    """Convert legacy currency and point balances once, without discarding value."""
    marker = await fetch_one(
        conn,
        "SELECT setting_value FROM nabil_bot_settings WHERE setting_key = %s FOR UPDATE",
        ("unified_wallet_iqd_v1",),
    )
    if marker and marker["setting_value"] == "done":
        return

    settings_rows = await fetch_all(
        conn,
        """
        SELECT setting_key, setting_value FROM nabil_bot_settings
        WHERE setting_key IN (
          'currency_per_usd', 'points_per_currency', 'points_enabled',
          'daily_points_reward', 'daily_balance_reward'
        )
        """,
    )
    settings = {row["setting_key"]: str(row["setting_value"]) for row in settings_rows}
    fallback_currency_rate = "1500" if LEGACY_CURRENCY == "IQD" else "1"
    fallback_points_rate = "1500" if LEGACY_CURRENCY == "IQD" else "1"
    try:
        old_currency_rate = Decimal(
            settings.get("currency_per_usd", fallback_currency_rate)
        )
        old_points_rate = Decimal(
            settings.get("points_per_currency", fallback_points_rate)
        )
        if (
            not old_currency_rate.is_finite()
            or old_currency_rate <= 0
            or not old_points_rate.is_finite()
            or old_points_rate <= 0
        ):
            raise ValueError
    except (InvalidOperation, TypeError, ValueError) as exc:
        raise RuntimeError(
            "تعذر ترحيل الأرصدة: إعداد سعر التحويل القديم غير صالح."
        ) from exc

    currency_factor = IQD_PER_USD / old_currency_rate
    point_factor = IQD_PER_USD / old_points_rate

    if currency_factor != 1:
        await conn.execute(
            """
            UPDATE nabil_services
            SET base_rate = ROUND(base_rate * %s, 3)
            """,
            (currency_factor,),
        )
        await conn.execute(
            """
            UPDATE nabil_ledger
            SET amount = ROUND(amount * %s, 3),
                balance_after = ROUND(balance_after * %s, 3)
            WHERE entry_type NOT IN (
              'order_points_debit', 'order_points_refund',
              'daily_points_gift', 'gift_code_points'
            )
            """,
            (currency_factor, currency_factor),
        )

    await conn.execute(
        """
        UPDATE nabil_orders AS o
        SET sale_amount = ROUND(
              o.sale_amount * CASE WHEN EXISTS (
                SELECT 1 FROM nabil_ledger AS l
                WHERE l.order_id = o.id
                  AND l.entry_type IN ('order_points_debit', 'order_points_refund')
              ) THEN %s ELSE %s END,
              3
            ),
            refunded_amount = ROUND(
              o.refunded_amount * CASE WHEN EXISTS (
                SELECT 1 FROM nabil_ledger AS l
                WHERE l.order_id = o.id
                  AND l.entry_type IN ('order_points_debit', 'order_points_refund')
              ) THEN %s ELSE %s END,
              3
            ),
            provider_rate = ROUND(o.provider_rate * %s, 3),
            provider_cost = ROUND(o.provider_cost * %s, 3)
        """,
        (
            point_factor,
            currency_factor,
            point_factor,
            currency_factor,
            currency_factor,
            currency_factor,
        ),
    )

    await conn.execute(
        """
        UPDATE nabil_ledger
        SET amount = ROUND(amount * %s, 3),
            balance_after = ROUND(balance_after * %s, 3)
        WHERE entry_type IN (
          'order_points_debit', 'order_points_refund',
          'daily_points_gift', 'gift_code_points'
        )
        """,
        (point_factor, point_factor),
    )

    if "daily_balance_reward" not in settings:
        try:
            legacy_daily_reward = int(settings.get("daily_points_reward", "0"))
            daily_reward = money(
                convert_points_to_iqd(legacy_daily_reward, old_points_rate)
            )
        except (InvalidOperation, TypeError, ValueError) as exc:
            raise RuntimeError("تعذر ترحيل قيمة الهدية اليومية.") from exc
        await conn.execute(
            """
            INSERT INTO nabil_bot_settings (setting_key, setting_value, updated_at)
            VALUES ('daily_balance_reward', %s, NOW())
            ON CONFLICT (setting_key) DO NOTHING
            """,
            (str(daily_reward),),
        )
    for key in (
        "referral_referrer_balance_reward",
        "referral_invitee_balance_reward",
        "min_balance_transfer",
    ):
        value_row = await fetch_one(
            conn,
            "SELECT setting_value FROM nabil_bot_settings WHERE setting_key = %s FOR UPDATE",
            (key,),
        )
        if value_row:
            try:
                converted = money(
                    convert_currency_to_iqd(
                        Decimal(str(value_row["setting_value"])), old_currency_rate
                    )
                )
            except (InvalidOperation, TypeError, ValueError) as exc:
                raise RuntimeError(
                    f"تعذر ترحيل إعداد الرصيد {key} إلى IQD."
                ) from exc
            await conn.execute(
                """
                UPDATE nabil_bot_settings
                SET setting_value = %s, updated_at = NOW()
                WHERE setting_key = %s
                """,
                (str(converted), key),
            )

    gift_codes = await fetch_all(
        conn,
        """
        SELECT setting_key, setting_value FROM nabil_bot_settings
        WHERE LEFT(setting_key, 10) = 'gift_code_'
        FOR UPDATE
        """,
    )
    for gift_code in gift_codes:
        try:
            converted = money(
                convert_points_to_iqd(
                    int(gift_code["setting_value"]), old_points_rate
                )
            )
        except (InvalidOperation, TypeError, ValueError) as exc:
            raise RuntimeError(
                f"تعذر ترحيل قيمة كود الهدية {gift_code['setting_key']}."
            ) from exc
        await conn.execute(
            """
            UPDATE nabil_bot_settings
            SET setting_value = %s, updated_at = NOW()
            WHERE setting_key = %s
            """,
            (str(converted), gift_code["setting_key"]),
        )

    await conn.execute(
        """
        INSERT INTO nabil_members (telegram_id)
        SELECT telegram_id FROM nabil_bot_agents
        ON CONFLICT (telegram_id) DO NOTHING
        """
    )
    await conn.execute(
        """
        INSERT INTO nabil_members (telegram_id)
        SELECT telegram_id FROM nabil_bot_user_state WHERE points > 0
        ON CONFLICT (telegram_id) DO NOTHING
        """
    )

    members = await fetch_all(
        conn,
        """
        SELECT m.telegram_id, m.balance, COALESCE(s.points, 0) AS legacy_points
        FROM nabil_members AS m
        LEFT JOIN nabil_bot_user_state AS s ON s.telegram_id = m.telegram_id
        FOR UPDATE OF m
        """,
    )
    for member in members:
        old_balance = Decimal(str(member["balance"] or 0))
        points = int(member["legacy_points"] or 0)
        converted_balance = money(
            convert_currency_to_iqd(old_balance, old_currency_rate)
        )
        converted_points = money(convert_points_to_iqd(points, old_points_rate))
        new_balance = money(converted_balance + converted_points)
        if currency_factor != 1 or points > 0:
            await conn.execute(
                "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                (new_balance, member["telegram_id"]),
            )
        if converted_points > 0:
            await conn.execute(
                """
                INSERT INTO nabil_ledger
                  (member_id, entry_type, amount, balance_after, note)
                VALUES (%s, 'unified_wallet_migration', %s, %s, %s)
                """,
                (
                    member["telegram_id"],
                    converted_points,
                    new_balance,
                    "ترحيل النقاط القديمة إلى رصيد IQD موحد",
                ),
            )

    await conn.execute(
        """
        UPDATE nabil_bot_user_state
        SET points = 0, updated_at = NOW()
        WHERE points <> 0
        """
    )

    agents = await fetch_all(
        conn,
        """
        SELECT telegram_id, wallet_points
        FROM nabil_bot_agents
        WHERE wallet_points > 0
        FOR UPDATE
        """,
    )
    for agent in agents:
        amount = money(
            convert_points_to_iqd(int(agent["wallet_points"]), old_points_rate)
        )
        member = await fetch_one(
            conn,
            "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
            (agent["telegram_id"],),
        )
        if member and amount > 0:
            balance_after = money(Decimal(str(member["balance"])) + amount)
            await conn.execute(
                "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                (balance_after, agent["telegram_id"]),
            )
            await conn.execute(
                """
                INSERT INTO nabil_ledger
                  (member_id, entry_type, amount, balance_after, note)
                VALUES (%s, 'unified_wallet_migration', %s, %s, %s)
                """,
                (
                    agent["telegram_id"],
                    amount,
                    balance_after,
                    "ترحيل محفظة الوكيل القديمة إلى رصيد IQD",
                ),
            )
    await conn.execute("UPDATE nabil_bot_agents SET wallet_points = 0")

    if point_factor != 1:
        await conn.execute(
            """
            UPDATE nabil_agent_transactions
            SET amount = ROUND(amount * %s, 3),
                wallet_before = ROUND(wallet_before * %s, 3),
                wallet_after = ROUND(wallet_after * %s, 3),
                member_points_before = ROUND(member_points_before * %s, 3),
                member_points_after = ROUND(member_points_after * %s, 3)
            """,
            (point_factor,) * 5,
        )

    if "member_rush_enabled" not in settings and "points_enabled" in settings:
        await conn.execute(
            """
            INSERT INTO nabil_bot_settings (setting_key, setting_value, updated_at)
            VALUES ('member_rush_enabled', %s, NOW())
            ON CONFLICT (setting_key) DO NOTHING
            """,
            (settings["points_enabled"],),
        )
    await conn.execute(
        """
        INSERT INTO nabil_bot_settings (setting_key, setting_value, updated_at)
        VALUES ('currency_per_usd', %s, NOW())
        ON CONFLICT (setting_key) DO UPDATE
        SET setting_value = EXCLUDED.setting_value, updated_at = NOW()
        """,
        (str(IQD_PER_USD),),
    )
    await conn.execute(
        """
        INSERT INTO nabil_bot_settings (setting_key, setting_value, updated_at)
        VALUES ('unified_wallet_iqd_v1', 'done', NOW())
        ON CONFLICT (setting_key) DO UPDATE
        SET setting_value = EXCLUDED.setting_value, updated_at = NOW()
        """
    )


def safe_text(value: Any, limit: int = 250) -> str:
    text = str(value or "")
    for secret in (BOT_TOKEN, os.getenv("SESSION_SECRET", "")):
        if secret:
            text = text.replace(secret, "[REDACTED]")
    text = re.sub(r"[<>`]", "", text)
    return text[:limit]


def safe_html(value: Any, limit: int = 250) -> str:
    return html.escape(safe_text(value, limit), quote=True)


async def menu_keyboard(balance: Decimal):
    channel_url = (await get_setting("public_channel_url")).strip()
    if channel_url.startswith("https://t.me/"):
        channel_button = InlineKeyboardButton("قناة البوت", url=channel_url)
    else:
        channel_button = InlineKeyboardButton(
            "قناة البوت", callback_data="menu:channel"
        )
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton(
                    f"رصيدك: {fmt_money(balance)}",
                    callback_data="menu:balance",
                )
            ],
            [InlineKeyboardButton("رشق الأعضاء", callback_data="menu:services:0")],
            [
                InlineKeyboardButton(
                    "المشاهدات والتفاعلات", callback_data="menu:engagement:0"
                ),
                InlineKeyboardButton("المكافآت", callback_data="menu:points"),
            ],
            [
                InlineKeyboardButton(
                    "معلومات الحساب", callback_data="menu:account"
                ),
                InlineKeyboardButton("تحويل رصيد", callback_data="menu:transfer"),
            ],
            [
                InlineKeyboardButton("معلومات الطلب", callback_data="menu:order_info"),
                channel_button,
            ],
        ]
    )


def admin_keyboard(
    bot_enabled: bool = True,
    login_alerts: bool = True,
    owner: bool = True,
    permissions: dict[str, bool] | None = None,
):
    if not owner:
        allowed = permissions or {}
        rows = []
        for left, right in (
            (("الطلبات", "admin:orders", "orders"), ("الخدمات", "admin:services:0", "services")),
            (("الأرصدة", "admin:wallet", "wallet"), ("الإحصائيات", "admin:report", "reports")),
            (("الأعضاء والحظر", "admin:members", "members"), ("إرسال إعلان", "admin:broadcast", "broadcast")),
        ):
            row = [
                InlineKeyboardButton(label, callback_data=callback)
                for label, callback, permission in (left, right)
                if allowed.get(permission, False)
            ]
            if row:
                rows.append(row)
        if allowed.get("force_subscription", False):
            rows.append(
                [
                    InlineKeyboardButton(
                        "الاشتراك الإجباري", callback_data="admin:force_subscription"
                    )
                ]
            )
        if not rows:
            rows.append([InlineKeyboardButton("لا توجد صلاحيات مفعّلة", callback_data="admin:home")])
        return InlineKeyboardMarkup(rows)
    rows = [
        [
            InlineKeyboardButton(
                "عمل البوت: ✅" if bot_enabled else "عمل البوت: ⛔",
                callback_data="admin:toggle_bot:home",
            ),
            InlineKeyboardButton(
                "إشعار الدخول: ✅" if login_alerts else "إشعار الدخول: ⛔",
                callback_data="admin:toggle_alerts:home",
            ),
        ],
        [
            InlineKeyboardButton(
                "تغيير الكلايش والنصوص", callback_data="admin:copy"
            )
        ],
        [
            InlineKeyboardButton(
                "قسم الاشتراك الإجباري", callback_data="admin:channel"
            ),
            InlineKeyboardButton("قسم الأدمنية", callback_data="admin:agents"),
        ],
        [
            InlineKeyboardButton(
                "قسم الميزات الخاصة", callback_data="admin:special_features"
            )
        ],
        [
            InlineKeyboardButton("قسم الإذاعة", callback_data="admin:broadcast"),
            InlineKeyboardButton("قسم الإحصائيات", callback_data="admin:report"),
        ],
        [
            InlineKeyboardButton(
                "إدارة المستخدمين والحظر", callback_data="admin:members"
            )
        ],
        [
            InlineKeyboardButton(
                "انذارات البوت", callback_data="admin:alerts"
            )
        ],
        [
            InlineKeyboardButton(
                "• إعدادات بوت الرشق •", callback_data="admin:settings"
            )
        ],
    ]
    return InlineKeyboardMarkup(rows)


def back_keyboard(callback_data: str, label: str = "رجوع"):
    return InlineKeyboardMarkup(
        [[InlineKeyboardButton(label, callback_data=callback_data)]]
    )


def is_back_navigation(query, callback_data: str) -> bool:
    message = query.message
    markup = getattr(message, "reply_markup", None)
    if not markup:
        return False
    back_labels = ("رجوع", "عودة", "إلغاء", "الغاء")
    return any(
        button.callback_data == callback_data
        and button.text.strip().startswith(back_labels)
        for row in markup.inline_keyboard
        for button in row
    )


def remember_navigation_screen(user_id: int, chat_id: int, message) -> None:
    if not message:
        return
    text = getattr(message, "text", None)
    caption = getattr(message, "caption", None)
    if text is not None:
        screen = {
            "kind": "text",
            "text": text,
            "entities": list(getattr(message, "entities", None) or []),
            "reply_markup": getattr(message, "reply_markup", None),
        }
    elif caption is not None:
        screen = {
            "kind": "caption",
            "text": caption,
            "entities": list(getattr(message, "caption_entities", None) or []),
            "reply_markup": getattr(message, "reply_markup", None),
        }
    else:
        return

    history = NAV_HISTORY.setdefault((user_id, chat_id), [])
    history.append(screen)
    del history[:-NAV_HISTORY_LIMIT]


async def restore_previous_navigation_screen(
    query, user_id: int, chat_id: int
) -> bool:
    history = NAV_HISTORY.get((user_id, chat_id))
    if not history:
        return False

    screen = history.pop()
    if not history:
        NAV_HISTORY.pop((user_id, chat_id), None)

    if screen["kind"] == "caption":
        await query.edit_message_caption(
            caption=screen["text"],
            caption_entities=screen["entities"],
            reply_markup=screen["reply_markup"],
        )
    else:
        await query.edit_message_text(
            text=screen["text"],
            entities=screen["entities"],
            reply_markup=screen["reply_markup"],
        )
    return True


def admin_parent_target(user_id: int) -> str:
    return "admin:home"


async def ensure_member(user_id: int):
    async with database() as conn:
        await conn.execute(
            """
            INSERT INTO nabil_members (telegram_id) VALUES (%s)
            ON CONFLICT (telegram_id) DO NOTHING
            """,
            (user_id,),
        )


async def ensure_bot_user(
    user_id: int,
    first_name: str = "",
    username: str | None = None,
    referral_id: int | None = None,
    award_referral: bool = False,
) -> tuple[bool, dict[str, Any] | None]:
    """Create the member control row and apply first-activation referral rewards once."""
    eligible_referral = (
        award_referral
        and referral_id is not None
        and referral_id > 0
        and referral_id != user_id
    )
    configured_rewards: dict[str, Decimal] = {}
    if eligible_referral:
        for key in (
            "referral_referrer_balance_reward",
            "referral_invitee_balance_reward",
        ):
            try:
                reward = money(Decimal(await get_setting(key)))
                if reward < 0 or reward > Decimal("100000000"):
                    raise ValueError
            except (InvalidOperation, ValueError):
                LOG.warning("Invalid referral reward setting %s; treating it as zero.", key)
                reward = money(0)
            configured_rewards[key] = reward

    referral_info = None
    async with database() as conn:
        async with conn.transaction():
            inserted = await fetch_one(
                conn,
                """
                INSERT INTO nabil_bot_user_state
                  (telegram_id, first_name, username, updated_at)
                VALUES (%s, %s, %s, NOW())
                ON CONFLICT (telegram_id) DO NOTHING
                RETURNING telegram_id
                """,
                (user_id, first_name[:120], username[:120] if username else None),
            )
            created = bool(inserted)
            if not created:
                await conn.execute(
                    """
                    UPDATE nabil_bot_user_state
                    SET first_name = %s, username = %s, updated_at = NOW()
                    WHERE telegram_id = %s
                    """,
                    (first_name[:120], username[:120] if username else None, user_id),
                )
            if created and eligible_referral:
                referral_members = await fetch_all(
                    conn,
                    """
                    SELECT telegram_id, balance FROM nabil_members
                    WHERE telegram_id IN (%s, %s)
                    ORDER BY telegram_id
                    FOR UPDATE
                    """,
                    tuple(sorted((referral_id, user_id))),
                )
                members_by_id = {
                    int(row["telegram_id"]): row for row in referral_members
                }
                if referral_id in members_by_id and user_id in members_by_id:
                    await conn.execute(
                        """
                        INSERT INTO nabil_bot_user_state (telegram_id)
                        VALUES (%s) ON CONFLICT (telegram_id) DO NOTHING
                        """,
                        (referral_id,),
                    )
                    await conn.execute(
                        """
                        UPDATE nabil_bot_user_state
                        SET referrals_count = referrals_count + 1, updated_at = NOW()
                        WHERE telegram_id = %s
                        """,
                        (referral_id,),
                    )
                    await conn.execute(
                        """
                        UPDATE nabil_bot_user_state SET referred_by = %s, updated_at = NOW()
                        WHERE telegram_id = %s
                        """,
                        (referral_id, user_id),
                    )
                    referrer_reward = configured_rewards[
                        "referral_referrer_balance_reward"
                    ]
                    invitee_reward = configured_rewards[
                        "referral_invitee_balance_reward"
                    ]
                    reward_updates = (
                        (referral_id, referrer_reward, "referral_reward",
                         f"مكافأة دعوة العضو {user_id}"),
                        (user_id, invitee_reward, "referral_signup_reward",
                         f"مكافأة التسجيل عبر دعوة العضو {referral_id}"),
                    )
                    for member_id, reward, entry_type, note in reward_updates:
                        if reward <= 0:
                            continue
                        balance_before = money(
                            Decimal(str(members_by_id[member_id]["balance"]))
                        )
                        balance_after = money(balance_before + reward)
                        await conn.execute(
                            "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                            (balance_after, member_id),
                        )
                        await conn.execute(
                            """
                            INSERT INTO nabil_ledger
                              (member_id, entry_type, amount, balance_after, note)
                            VALUES (%s, %s, %s, %s, %s)
                            """,
                            (member_id, entry_type, reward, balance_after, note),
                        )
                        await enqueue_live_mirror_wallet_event(
                            conn,
                            member_id=member_id,
                            entry_type=entry_type,
                            amount=reward,
                            balance_after=balance_after,
                            note=note,
                            event_key=f"referral:{user_id}:{member_id}",
                        )
                    referral_info = {
                        "referrer_id": referral_id,
                        "referrer_reward": referrer_reward,
                        "invitee_reward": invitee_reward,
                        "referrer_balance": money(
                            Decimal(str(members_by_id[referral_id]["balance"]))
                            + referrer_reward
                        ),
                        "invitee_balance": money(
                            Decimal(str(members_by_id[user_id]["balance"]))
                            + invitee_reward
                        ),
                    }
    return created, referral_info


async def notify_balance_change(
    bot, user_id: int, amount: Decimal, balance_after: Decimal, reason: str
):
    if amount == 0:
        return
    action = "أضيف إلى رصيدك" if amount > 0 else "خُصم من رصيدك"
    try:
        await bot.send_message(
            user_id,
            f"💰 {action} {fmt_money(abs(amount))}.\n"
            f"السبب: {safe_text(reason, 200)}\n"
            f"رصيدك الحالي: {fmt_money(balance_after)}",
        )
    except Exception as exc:
        LOG.info(
            "Could not notify member %s about a balance change: %s",
            user_id,
            safe_text(exc, 160),
        )


async def current_admin_keyboard(user_id: int | None = None):
    return admin_keyboard(
        await setting_enabled("bot_enabled"),
        await setting_enabled("login_alerts_enabled"),
        owner=is_owner(user_id),
        permissions=await get_admin_permissions(user_id),
    )


def parse_force_channel_reference(value: str) -> tuple[str, str]:
    raw = value.strip()
    if re.fullmatch(r"-100\d{5,20}", raw):
        return raw, ""

    if raw.startswith("@"):
        username = raw[1:]
    else:
        candidate = raw
        if candidate.startswith(("t.me/", "www.t.me/")):
            candidate = f"https://{candidate}"
        parsed = urlparse(candidate)
        if parsed.scheme != "https" or parsed.hostname not in {
            "t.me",
            "www.t.me",
            "telegram.me",
            "www.telegram.me",
        }:
            raise ValueError(
                "أرسل يوزر قناة عامة أو رابطاً عاماً يبدأ بـ https://t.me/."
            )
        parts = [part for part in parsed.path.split("/") if part]
        if not parts or parts[0].startswith("+") or parts[0].lower() in {
            "joinchat",
            "c",
        }:
            raise ValueError(
                "رابط الدعوة الخاصة لا يكفي للتحقق. أرسل آيدي القناة الذي يبدأ بـ -100."
            )
        username = parts[0]

    if not re.fullmatch(r"[A-Za-z0-9_]{5,32}", username):
        raise ValueError("يوزر القناة غير صالح.")
    return f"@{username}", f"https://t.me/{username}"


def parse_private_channel_invite(value: str) -> str:
    parsed = urlparse(value.strip())
    path = parsed.path.rstrip("/")
    valid_path = bool(
        re.fullmatch(r"/\+[A-Za-z0-9_-]{5,128}", path)
        or re.fullmatch(r"/joinchat/[A-Za-z0-9_-]{5,128}", path)
    )
    if (
        parsed.scheme != "https"
        or parsed.hostname not in {"t.me", "www.t.me"}
        or not valid_path
    ):
        raise ValueError(
            "أرسل رابط دعوة خاصاً صالحاً يبدأ بـ https://t.me/+ أو /joinchat/."
        )
    return f"https://t.me{path}"


async def inspect_required_channel(bot, reference: str) -> dict[str, Any]:
    chat_reference, join_url = parse_force_channel_reference(reference)
    chat = await bot.get_chat(chat_reference)
    if chat.type != "channel":
        raise ValueError("الرابط لا يشير إلى قناة تيليغرام.")

    bot_user = await bot.get_me()
    bot_member = await bot.get_chat_member(chat.id, bot_user.id)
    if bot_member.status not in ("administrator", "creator"):
        raise ValueError(
            "أضف البوت مشرفاً في القناة حتى يتمكن من التحقق من اشتراك الأعضاء."
        )

    username = getattr(chat, "username", None)
    if username:
        join_url = f"https://t.me/{username}"
    return {
        "chat_id": str(chat.id),
        "title": chat.title or username or str(chat.id),
        "join_url": join_url,
        "username": username or "",
    }


async def _legacy_required_channels(conn) -> list[dict[str, Any]]:
    rows = await fetch_all(
        conn,
        """
        SELECT setting_key, setting_value
        FROM nabil_bot_settings
        WHERE setting_key IN ('required_channel_chat', 'required_channel_url')
        """,
    )
    settings = {row["setting_key"]: str(row["setting_value"] or "").strip() for row in rows}
    chat_id = settings.get("required_channel_chat", "")
    if not chat_id:
        return []
    join_url = settings.get("required_channel_url", "")
    if not join_url and chat_id.startswith("@"):
        join_url = f"https://t.me/{chat_id[1:]}"
    return [
        {
            "id": "legacy",
            "chat_id": chat_id,
            "title": chat_id,
            "join_url": join_url,
            "username": chat_id[1:] if chat_id.startswith("@") else "",
            "target_count": None,
            "verified_count": 0,
            "active": True,
        }
    ]


def _decode_required_channels(value: str) -> list[dict[str, Any]]:
    try:
        records = json.loads(value)
    except (TypeError, ValueError):
        LOG.error("The saved required-channel list is not valid JSON.")
        return []
    if not isinstance(records, list):
        LOG.error("The saved required-channel list has an invalid structure.")
        return []

    channels = []
    for record in records:
        if not isinstance(record, dict):
            continue
        chat_id = str(record.get("chat_id", "")).strip()
        if not chat_id:
            continue
        target = record.get("target_count")
        try:
            target = int(target) if target is not None else None
            if target is not None and target < 1:
                target = None
        except (TypeError, ValueError):
            target = None
        try:
            verified_count = max(0, int(record.get("verified_count", 0)))
        except (TypeError, ValueError):
            verified_count = 0
        join_url = str(record.get("join_url", "")).strip()
        if not join_url.startswith("https://t.me/"):
            join_url = ""
        username = str(record.get("username", "")).strip().lstrip("@")
        if not username and chat_id.startswith("@"):
            username = chat_id[1:]
        if not username and join_url:
            url_parts = [part for part in urlparse(join_url).path.split("/") if part]
            candidate = url_parts[0] if url_parts else ""
            if (
                candidate.lower() not in {"c", "joinchat"}
                and not candidate.startswith("+")
                and re.fullmatch(r"[A-Za-z0-9_]{5,32}", candidate)
            ):
                username = candidate
        channels.append(
            {
                "id": str(record.get("id") or "legacy")[:32],
                "chat_id": chat_id,
                "title": str(record.get("title") or chat_id)[:120],
                "join_url": join_url,
                "username": username[:32],
                "target_count": target,
                "verified_count": verified_count,
                "active": bool(record.get("active", True))
                and not (target is not None and verified_count >= target),
            }
        )
    return channels


async def load_required_channels(conn=None) -> list[dict[str, Any]]:
    if conn is not None:
        row = await fetch_one(
            conn,
            "SELECT setting_value FROM nabil_bot_settings WHERE setting_key = %s",
            (REQUIRED_CHANNELS_SETTING_KEY,),
        )
        return (
            _decode_required_channels(str(row["setting_value"]))
            if row
            else await _legacy_required_channels(conn)
        )
    async with database() as connection:
        return await load_required_channels(connection)


async def _ensure_required_channels_record(conn) -> list[dict[str, Any]]:
    legacy_channels = await _legacy_required_channels(conn)
    await conn.execute(
        """
        INSERT INTO nabil_bot_settings (setting_key, setting_value, updated_at)
        VALUES (%s, %s, NOW())
        ON CONFLICT (setting_key) DO NOTHING
        """,
        (
            REQUIRED_CHANNELS_SETTING_KEY,
            json.dumps(legacy_channels, ensure_ascii=False, separators=(",", ":")),
        ),
    )
    row = await fetch_one(
        conn,
        "SELECT setting_value FROM nabil_bot_settings WHERE setting_key = %s FOR UPDATE",
        (REQUIRED_CHANNELS_SETTING_KEY,),
    )
    return _decode_required_channels(str(row["setting_value"])) if row else []


async def mutate_required_channels(mutator) -> Any:
    async with database() as conn:
        async with conn.transaction():
            channels = await _ensure_required_channels_record(conn)
            result = mutator(channels)
            await conn.execute(
                """
                UPDATE nabil_bot_settings
                SET setting_value = %s, updated_at = NOW()
                WHERE setting_key = %s
                """,
                (
                    json.dumps(channels, ensure_ascii=False, separators=(",", ":")),
                    REQUIRED_CHANNELS_SETTING_KEY,
                ),
            )
            return result


async def add_required_channel(channel: dict[str, Any]) -> bool:
    def add(channels):
        if any(existing["chat_id"] == channel["chat_id"] for existing in channels):
            return False
        channels.append(channel)
        return True

    return await mutate_required_channels(add)


async def remove_required_channel(channel_id: str) -> bool:
    async with database() as conn:
        async with conn.transaction():
            channels = await _ensure_required_channels_record(conn)
            original_count = len(channels)
            channels[:] = [
                channel for channel in channels if channel["id"] != channel_id
            ]
            if len(channels) == original_count:
                return False
            await conn.execute(
                """
                UPDATE nabil_bot_settings
                SET setting_value = %s, updated_at = NOW()
                WHERE setting_key = %s
                """,
                (
                    json.dumps(channels, ensure_ascii=False, separators=(",", ":")),
                    REQUIRED_CHANNELS_SETTING_KEY,
                ),
            )
            marker_prefix = f"force_verified_{channel_id}_"
            await conn.execute(
                """
                DELETE FROM nabil_bot_settings
                WHERE LEFT(setting_key, %s) = %s
                """,
                (len(marker_prefix), marker_prefix),
            )
            return True


async def record_required_channel_verification(
    channel_id: str, user_id: int
) -> tuple[int, bool, bool]:
    async with database() as conn:
        async with conn.transaction():
            channels = await _ensure_required_channels_record(conn)
            channel = next(
                (item for item in channels if item["id"] == channel_id), None
            )
            if not channel:
                return 0, False, False
            if channel["target_count"] is None or not channel["active"]:
                return channel["verified_count"], channel["active"], False

            marker_key = f"force_verified_{channel_id}_{user_id}"
            inserted = await fetch_one(
                conn,
                """
                INSERT INTO nabil_bot_settings (setting_key, setting_value, updated_at)
                VALUES (%s, '1', NOW())
                ON CONFLICT (setting_key) DO NOTHING
                RETURNING setting_key
                """,
                (marker_key,),
            )
            newly_completed = False
            if inserted:
                channel["verified_count"] += 1
                if channel["verified_count"] >= channel["target_count"]:
                    channel["active"] = False
                    newly_completed = True
                await conn.execute(
                    """
                    UPDATE nabil_bot_settings
                    SET setting_value = %s, updated_at = NOW()
                    WHERE setting_key = %s
                    """,
                    (
                        json.dumps(
                            channels, ensure_ascii=False, separators=(",", ":")
                        ),
                        REQUIRED_CHANNELS_SETTING_KEY,
                    ),
                )
            return channel["verified_count"], channel["active"], newly_completed


async def notify_required_channel_completed(bot, channel, verified_count: int):
    if not OWNER_ID:
        return
    username = channel.get("username") or ""
    username_text = f"@{safe_text(username, 32)}" if username else "غير متوفر"
    try:
        member_count = await bot.get_chat_member_count(channel["chat_id"])
        member_count_text = f"{member_count}"
    except Exception as exc:
        LOG.warning(
            "Could not get member count for completed channel %s: %s",
            safe_text(channel.get("chat_id", ""), 80),
            safe_text(exc, 160),
        )
        member_count_text = "غير متاح"
    target_count = channel.get("target_count") or verified_count
    message = (
        "✅ اكتمل العدد المطلوب للاشتراك الإجباري\n"
        f"القناة: {safe_text(channel.get('title', ''), 100)}\n"
        f"يوزر القناة: {username_text}\n"
        f"معرّف القناة: {safe_text(channel.get('chat_id', ''), 40)}\n"
        f"المتحققون: {verified_count} / {target_count}\n"
        f"أعضاء القناة حالياً: {member_count_text}\n"
        "تمت إزالة القناة تلقائياً من الاشتراك الإجباري."
    )
    try:
        await bot.send_message(OWNER_ID, message)
    except Exception as exc:
        LOG.warning(
            "Could not notify owner about completed required channel: %s",
            safe_text(exc, 180),
        )


async def update_force_prompt(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    text: str,
    reply_markup: InlineKeyboardMarkup | None = None,
):
    markup = reply_markup or back_keyboard(
        "admin:force_subscription", "رجوع لإدارة الاشتراك"
    )
    chat_id = context.user_data.get("force_prompt_chat_id")
    message_id = context.user_data.get("force_prompt_message_id")
    if chat_id and message_id:
        try:
            await context.bot.edit_message_text(
                chat_id=chat_id,
                message_id=message_id,
                text=text,
                reply_markup=markup,
            )
            return
        except Exception:
            pass
    if update.message:
        sent = await update.message.reply_text(text, reply_markup=markup)
        context.user_data["force_prompt_chat_id"] = sent.chat_id
        context.user_data["force_prompt_message_id"] = sent.message_id


async def preview_force_channel(
    update: Update, context: ContextTypes.DEFAULT_TYPE
):
    channel_id = context.user_data.get("force_channel_id")
    try:
        target_count = int(context.user_data.get("force_channel_target_count"))
    except (TypeError, ValueError):
        target_count = 0
    if not channel_id or target_count < 1:
        context.user_data.clear()
        return
    title = str(context.user_data.get("force_channel_title") or channel_id)
    username = str(context.user_data.get("force_channel_username") or "")
    username_text = f"@{username}" if username else "قناة خاصة"
    join_url = str(context.user_data.get("force_channel_join_url") or "")
    context.user_data["mode"] = "force_channel_confirm"
    keyboard = InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("صح، أوافق ✅", callback_data="setforce_confirm:yes"),
                InlineKeyboardButton("غلط، إلغاء ❌", callback_data="setforce_confirm:no"),
            ],
            [
                InlineKeyboardButton(
                    "رجوع لإدارة الاشتراك",
                    callback_data="admin:force_subscription",
                )
            ],
        ]
    )
    await update_force_prompt(
        update,
        context,
        "مراجعة إضافة قناة الاشتراك الإجباري:\n"
        f"القناة: {safe_text(title, 100)}\n"
        f"يوزر القناة: {safe_text(username_text, 40)}\n"
        f"رابط الانضمام: {safe_text(join_url, 180)}\n"
        f"العدد المطلوب: {target_count} عضو متحقق\n\n"
        "هل توافق على إضافة القناة؟",
        reply_markup=keyboard,
    )


async def save_force_channel(context: ContextTypes.DEFAULT_TYPE):
    channel_id = context.user_data.get("force_channel_id")
    try:
        target_count = int(context.user_data.get("force_channel_target_count"))
    except (TypeError, ValueError):
        target_count = 0
    if not channel_id or target_count < 1:
        context.user_data.clear()
        return None
    channel = {
        "id": uuid.uuid4().hex[:12],
        "chat_id": str(channel_id),
        "title": str(context.user_data.get("force_channel_title") or channel_id),
        "join_url": str(context.user_data.get("force_channel_join_url") or ""),
        "username": str(context.user_data.get("force_channel_username") or ""),
        "target_count": target_count,
        "verified_count": int(context.user_data.get("force_channel_verified_count", 0)),
        "active": True,
    }
    added = await add_required_channel(channel)
    context.user_data.clear()
    return channel if added else None


async def prompt_force_channel_target(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data["mode"] = "force_channel_target"
    verified_count = int(context.user_data.get("force_channel_verified_count", 0))
    await update_force_prompt(
        update,
        context,
        f"عدد الأعضاء الذين تحققوا حتى الآن: {verified_count}.\n"
        "أرسل العدد المطلوب. تتوقف هذه القناة عن الاشتراك الإجباري "
        "وتختفي من رسالة الاشتراك عند اكتماله.",
    )


async def required_subscription_status(bot, user_id: int) -> tuple[bool, str]:
    if not await setting_enabled("require_subscription"):
        return True, ""
    if await is_subscription_exempt(user_id):
        return True, ""
    channels = await load_required_channels()
    if not channels:
        return True, ""
    active_channels = [channel for channel in channels if channel["active"]]
    if not active_channels:
        return True, ""

    verification_error = False
    missing_membership = False
    for channel in active_channels:
        try:
            member = await bot.get_chat_member(channel["chat_id"], user_id)
            is_member = member.status in ("creator", "administrator", "member")
            if member.status == "restricted":
                is_member = bool(getattr(member, "is_member", False))
            if is_member:
                verified_count, _active, newly_completed = (
                    await record_required_channel_verification(
                        channel["id"], user_id
                    )
                )
                if newly_completed:
                    await notify_required_channel_completed(
                        bot, channel, verified_count
                    )
            else:
                missing_membership = True
        except Exception as exc:
            LOG.warning(
                "Could not verify required-channel membership: %s",
                safe_text(exc, 180),
            )
            verification_error = True
    if verification_error:
        return (
            False,
            "تعذر التحقق من الاشتراك الآن. تأكد من إعداد القنوات وصلاحيات البوت.",
        )
    if missing_membership:
        return False, "اشترك في قنوات البوت أولاً ثم اضغط «تحقق من الاشتراك»."
    return True, ""


def human_verification_code_digest(user_id: int, code: str) -> str:
    key = (os.getenv("SESSION_SECRET", "").strip() or BOT_TOKEN).encode("utf-8")
    challenge = f"nabil-human-verification:{user_id}:{code}".encode("utf-8")
    return hmac.new(key, challenge, hashlib.sha256).hexdigest()


def human_verification_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton(
                    "اضغط هنا للتحقق", callback_data="human:begin"
                )
            ]
        ]
    )


def human_verification_prompt() -> str:
    return (
        "• أهلاً بك في البوت.\n\n"
        "• بما أنك عضو جديد، نحتاج نتأكد أنك شخص حقيقي. "
        "اضغط على الزر بالأسفل لبدء التحقق."
    )


async def is_human_verified(user_id: int) -> bool:
    async with database() as conn:
        row = await fetch_one(
            conn,
            """
            SELECT verified_at IS NOT NULL AS verified
            FROM nabil_human_verifications
            WHERE telegram_id = %s
            """,
            (user_id,),
        )
    return bool(row and row["verified"])


async def remember_human_verification_referral(
    user_id: int, referral_id: int | None
):
    async with database() as conn:
        await conn.execute(
            """
            INSERT INTO nabil_human_verifications
                (telegram_id, pending_referral_id)
            VALUES (%s, %s)
            ON CONFLICT (telegram_id) DO UPDATE
            SET pending_referral_id = COALESCE(
                nabil_human_verifications.pending_referral_id,
                EXCLUDED.pending_referral_id
            )
            WHERE nabil_human_verifications.verified_at IS NULL
            """,
            (user_id, referral_id),
        )


async def create_human_verification_challenge(user_id: int) -> str | None:
    code = str(secrets.randbelow(900_000) + 100_000)
    async with database() as conn:
        row = await fetch_one(
            conn,
            """
            INSERT INTO nabil_human_verifications (
                telegram_id, verification_code_hash, code_expires_at,
                failed_attempts
            )
            VALUES (
                %s, %s, NOW() + (%s * INTERVAL '1 second'), 0
            )
            ON CONFLICT (telegram_id) DO UPDATE
            SET verification_code_hash = EXCLUDED.verification_code_hash,
                code_expires_at = EXCLUDED.code_expires_at,
                failed_attempts = 0
            WHERE nabil_human_verifications.verified_at IS NULL
            RETURNING telegram_id
            """,
            (
                user_id,
                human_verification_code_digest(user_id, code),
                HUMAN_VERIFICATION_CODE_TTL_SECONDS,
            ),
        )
    return code if row else None


async def check_human_verification_code(
    user_id: int, supplied_code: str
) -> tuple[str, int | None]:
    normalized_code = normalize_decimal_digits(supplied_code.strip())
    async with database() as conn:
        async with conn.transaction():
            row = await fetch_one(
                conn,
                """
                SELECT verified_at, verification_code_hash,
                       code_expires_at > NOW() AS challenge_active,
                       failed_attempts, pending_referral_id
                FROM nabil_human_verifications
                WHERE telegram_id = %s
                FOR UPDATE
                """,
                (user_id,),
            )
            if not row:
                return "no_challenge", None
            if row["verified_at"] is not None:
                return "already_verified", row["pending_referral_id"]
            if not row["verification_code_hash"]:
                return "no_challenge", None
            if not row["challenge_active"]:
                await conn.execute(
                    """
                    UPDATE nabil_human_verifications
                    SET verification_code_hash = NULL,
                        code_expires_at = NULL,
                        failed_attempts = 0
                    WHERE telegram_id = %s
                    """,
                    (user_id,),
                )
                return "expired", None

            expected_digest = human_verification_code_digest(
                user_id, normalized_code or ""
            )
            if (
                not re.fullmatch(r"[0-9]{6}", normalized_code or "")
                or not hmac.compare_digest(
                    expected_digest, row["verification_code_hash"]
                )
            ):
                failed_attempts = int(row["failed_attempts"]) + 1
                if failed_attempts >= HUMAN_VERIFICATION_MAX_ATTEMPTS:
                    await conn.execute(
                        """
                        UPDATE nabil_human_verifications
                        SET verification_code_hash = NULL,
                            code_expires_at = NULL,
                            failed_attempts = 0
                        WHERE telegram_id = %s
                        """,
                        (user_id,),
                    )
                    return "locked", None
                await conn.execute(
                    """
                    UPDATE nabil_human_verifications
                    SET failed_attempts = %s
                    WHERE telegram_id = %s
                    """,
                    (failed_attempts, user_id),
                )
                return "incorrect", HUMAN_VERIFICATION_MAX_ATTEMPTS - failed_attempts

            completed = await fetch_one(
                conn,
                """
                UPDATE nabil_human_verifications
                SET verified_at = NOW(),
                    verification_code_hash = NULL,
                    code_expires_at = NULL,
                    failed_attempts = 0
                WHERE telegram_id = %s
                RETURNING pending_referral_id
                """,
                (user_id,),
            )
            if completed:
                await conn.execute(
                    """
                    UPDATE nabil_human_verifications
                    SET pending_referral_id = NULL
                    WHERE telegram_id = %s
                    """,
                    (user_id,),
                )
            return "verified", (
                completed["pending_referral_id"] if completed else None
            )


async def process_human_verification_code(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.effective_message
    user = update.effective_user
    if not message or not user:
        return
    if not update.effective_chat or update.effective_chat.type != "private":
        await message.reply_text("أكمل التحقق في المحادثة الخاصة مع البوت.")
        return

    result, result_value = await check_human_verification_code(
        user.id, message.text or ""
    )
    if result in {"verified", "already_verified"}:
        await message.reply_text("تم التحقق بنجاح من أنك لست روبوتاً ✅")
        referral_id = result_value
        blocked = await member_access_message(context.bot, user.id, referral_id)
        if blocked:
            await message.reply_text(blocked[0], reply_markup=blocked[1])
            return
        await finish_member_start(
            user, context, referral_id=referral_id, message=message
        )
        return
    if result == "incorrect":
        await message.reply_text(
            "الرمز غير صحيح. "
            f"باقي لديك {result_value} محاولات. أرسل الرمز مرة أخرى."
        )
        return
    if result == "locked":
        await message.reply_text(
            "انتهت محاولات التحقق. اضغط الزر أدناه للحصول على رمز جديد.",
            reply_markup=human_verification_keyboard(),
        )
        return
    if result == "expired":
        prompt = "انتهت صلاحية الرمز. اضغط الزر أدناه للحصول على رمز جديد."
    else:
        prompt = "ابدأ التحقق أولاً من الزر أدناه، ثم أرسل الرمز الذي يظهر لك."
    await message.reply_text(prompt, reply_markup=human_verification_keyboard())


async def is_subscription_exempt(user_id: int) -> bool:
    async with database() as conn:
        row = await fetch_one(
            conn,
            """
            SELECT 1 AS exempt
            FROM nabil_subscription_exemptions
            WHERE telegram_id = %s
            """,
            (user_id,),
        )
    return bool(row)


async def subscription_markup(referral_id: int | None = None):
    buttons = []
    channels = await load_required_channels()
    for channel in channels:
        if channel["active"]:
            join_url = channel["join_url"]
            if not join_url and channel["chat_id"].startswith("@"):
                join_url = f"https://t.me/{channel['chat_id'][1:]}"
            if not join_url:
                continue
            buttons.append(
                [
                    InlineKeyboardButton(
                        safe_text(channel["title"], 48),
                        url=join_url,
                    )
                ]
            )
    check_callback = "member:check"
    if referral_id and 0 < referral_id <= 9_223_372_036_854_775_807:
        check_callback = f"{check_callback}:{referral_id}"
    buttons.append(
        [InlineKeyboardButton("تحقق من الاشتراك ✅", callback_data=check_callback)]
    )
    return InlineKeyboardMarkup(buttons)


async def member_access_message(
    bot, user_id: int, referral_id: int | None = None
) -> tuple[str, InlineKeyboardMarkup | None] | None:
    admin_user = await is_admin_user(user_id)
    if not admin_user:
        async with database() as conn:
            state = await fetch_one(
                conn,
                "SELECT is_banned FROM nabil_bot_user_state WHERE telegram_id = %s",
                (user_id,),
            )
        if state and state["is_banned"]:
            return "تم تقييد وصول هذا الحساب إلى البوت. تواصل مع المالك إذا كنت ترى أن ذلك خطأ.", None
        if not await setting_enabled("bot_enabled"):
            return await get_setting("maintenance_text"), None
    allowed, message = await required_subscription_status(bot, user_id)
    if allowed:
        return None
    if message and message.startswith("اشترك في"):
        message = "📢 للاستخدام، اشترك في جميع قنوات البوت أولاً ثم اضغط «تحقق من الاشتراك»."
    return message, await subscription_markup(referral_id)


async def member_balance(user_id: int) -> Decimal:
    async with database() as conn:
        member = await fetch_one(
            conn, "SELECT balance FROM nabil_members WHERE telegram_id = %s", (user_id,)
        )
    return Decimal(str(member["balance"])) if member else Decimal("0")


async def finish_member_start(
    user,
    context: ContextTypes.DEFAULT_TYPE,
    referral_id: int | None = None,
    message=None,
    query=None,
):
    chat_id = (
        query.message.chat_id
        if query and query.message
        else message.chat_id if message else None
    )
    if chat_id is not None:
        NAV_HISTORY.pop((user.id, chat_id), None)
    async with database() as conn:
        was_registered = bool(
            await fetch_one(
                conn,
                "SELECT 1 AS registered FROM nabil_members WHERE telegram_id = %s",
                (user.id,),
            )
        )
    await ensure_member(user.id)
    _, referral_info = await ensure_bot_user(
        user.id,
        first_name=user.first_name or "",
        username=user.username,
        referral_id=referral_id,
        award_referral=not was_registered,
    )
    if referral_info:
        referrer_id = referral_info["referrer_id"]
        await notify_balance_change(
            context.bot,
            referrer_id,
            referral_info["referrer_reward"],
            referral_info["referrer_balance"],
            f"مكافأة دعوة عضو {user.id}",
        )
        await notify_balance_change(
            context.bot,
            user.id,
            referral_info["invitee_reward"],
            referral_info["invitee_balance"],
            f"مكافأة التسجيل عبر دعوة العضو {referrer_id}",
        )
    context.user_data.clear()
    if not was_registered and OWNER_ID and await setting_enabled("login_alerts_enabled"):
        name = safe_text(user.full_name, 100)
        username = f" (@{safe_text(user.username, 80)})" if user.username else ""
        try:
            await context.bot.send_message(
                OWNER_ID,
                f"عضو جديد بدأ استخدام البوت:\n{name}{username}\nالآيدي: {user.id}",
            )
        except Exception as exc:
            LOG.warning("Could not send new-member alert: %s", safe_text(exc, 180))
    balance = await member_balance(user.id)
    greeting = safe_text(user.first_name, 60)
    welcome = await get_setting("welcome_text")
    try:
        welcome = welcome.format(name=greeting, id=user.id)
    except (KeyError, ValueError):
        welcome = f"{welcome}\n\n{greeting} · {user.id}"
    if query:
        if await is_admin_user(user.id):
            await query.edit_message_text(
                await admin_dashboard_text(),
                reply_markup=await current_admin_keyboard(user.id),
                parse_mode=ParseMode.HTML,
            )
        else:
            await query.edit_message_text(
                safe_text(welcome, 3500),
                reply_markup=await menu_keyboard(balance),
            )
        return
    if message:
        if await is_admin_user(user.id):
            await message.reply_text(
                await admin_dashboard_text(),
                reply_markup=await current_admin_keyboard(user.id),
                parse_mode=ParseMode.HTML,
            )
        await message.reply_text(
            safe_text(welcome, 3500),
            reply_markup=await menu_keyboard(balance),
        )


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not update.message:
        return
    user = update.effective_user
    NAV_HISTORY.pop((user.id, update.effective_chat.id), None)
    context.user_data.clear()
    referral_id = None
    if context.args:
        payload = context.args[0].strip()
        referral_payload = payload[4:] if payload.startswith("ref_") else ""
        if re.fullmatch(r"[1-9]\d{0,18}", referral_payload):
            candidate_referral_id = int(referral_payload)
            if candidate_referral_id <= 9_223_372_036_854_775_807:
                referral_id = candidate_referral_id
    if not await is_human_verified(user.id):
        await remember_human_verification_referral(user.id, referral_id)
        await update.message.reply_text(
            human_verification_prompt(),
            reply_markup=human_verification_keyboard(),
        )
        return
    blocked = await member_access_message(context.bot, user.id, referral_id)
    if blocked:
        await update.message.reply_text(blocked[0], reply_markup=blocked[1])
        return
    await finish_member_start(
        user, context, referral_id=referral_id, message=update.message
    )


async def subscription_gate(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user:
        return
    message = update.effective_message
    query = update.callback_query
    if not await is_human_verified(update.effective_user.id):
        if query and query.data == "human:begin":
            return
        if query:
            await query.answer()
            if query.message:
                await query.edit_message_text(
                    human_verification_prompt(),
                    reply_markup=human_verification_keyboard(),
                )
        elif message and message.text:
            command = message.text.split(maxsplit=1)[0].split("@", 1)[0].lower()
            if command == "/start":
                return
            if command.startswith("/"):
                await message.reply_text(
                    human_verification_prompt(),
                    reply_markup=human_verification_keyboard(),
                )
            else:
                await process_human_verification_code(update, context)
        elif message:
            await message.reply_text(
                human_verification_prompt(),
                reply_markup=human_verification_keyboard(),
            )
        raise ApplicationHandlerStop

    if message and message.text:
        command = message.text.split(maxsplit=1)[0].split("@", 1)[0].lower()
        if command == "/start":
            return
    if query and query.data and (
        query.data == "member:check" or query.data.startswith("member:check:")
    ):
        return

    blocked = await member_access_message(context.bot, update.effective_user.id)
    if not blocked:
        return
    context.user_data.clear()
    if query:
        await query.answer()
        if query.message:
            await query.edit_message_text(blocked[0], reply_markup=blocked[1])
    elif message:
        await message.reply_text(blocked[0], reply_markup=blocked[1])
    raise ApplicationHandlerStop


async def myid(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user and update.message:
        await update.message.reply_text(
            f"رقم حساب تيليغرام الخاص بك: {update.effective_user.id}"
        )


async def admin_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not update.message:
        return
    user_id = update.effective_user.id
    if not await is_admin_user(user_id) and not is_live_mirror_owner(user_id):
        await update.message.reply_text("هذا الأمر مخصص للمالك والمشرفين المعتمدين.")
        return
    NAV_HISTORY.pop(
        (user_id, update.effective_chat.id), None
    )
    context.user_data.clear()
    if is_live_mirror_owner(user_id) and not await is_admin_user(user_id):
        await update.message.reply_text(
            "<b>الميزات الخاصة بالمالك</b>\n\n"
            "إعدادات المرآة الحية وسجل الصندوق الأسود.",
            reply_markup=InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            "📡 إعدادات وتفعيل المرآة الحية",
                            callback_data="admin:special_features",
                        )
                    ]
                ]
            ),
            parse_mode=ParseMode.HTML,
        )
        return
    await update.message.reply_text(
        await admin_dashboard_text(),
        reply_markup=await current_admin_keyboard(update.effective_user.id),
        parse_mode=ParseMode.HTML,
    )


async def cancel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id if update.effective_user else None
    chat_id = update.effective_chat.id if update.effective_chat else None
    previous_screen = None
    if context.user_data and user_id is not None and chat_id is not None:
        history_key = (user_id, chat_id)
        history = NAV_HISTORY.get(history_key)
        if history:
            previous_screen = history.pop()
            if not history:
                NAV_HISTORY.pop(history_key, None)
    context.user_data.clear()
    if update.message and update.effective_user:
        if previous_screen:
            try:
                await update.message.reply_text(
                    previous_screen["text"],
                    entities=previous_screen.get("entities") or [],
                    reply_markup=previous_screen.get("reply_markup"),
                )
                return
            except Exception as exc:
                LOG.warning(
                    "Could not restore previous screen after cancellation: %s",
                    safe_text(exc, 160),
                )
        if chat_id is not None:
            NAV_HISTORY.pop((update.effective_user.id, chat_id), None)
        if await is_admin_user(update.effective_user.id):
            await update.message.reply_text(
                await admin_dashboard_text(),
                reply_markup=await current_admin_keyboard(update.effective_user.id),
                parse_mode=ParseMode.HTML,
            )
            return
        await ensure_member(update.effective_user.id)
        balance = await member_balance(update.effective_user.id)
        await update.message.reply_text(
            "تم إلغاء العملية. اختر من القائمة.",
            reply_markup=await menu_keyboard(balance),
        )


async def show_services(
    target,
    page: int,
    engagement_only: bool = False,
    member_only: bool = False,
):
    if member_only and not await setting_enabled("member_rush_enabled"):
        text = "قسم رشق الأعضاء متوقف حالياً."
        markup = back_keyboard("menu:home", "رجوع للقائمة")
        if hasattr(target, "edit_message_text"):
            await target.edit_message_text(text, reply_markup=markup)
        else:
            await target.reply_text(text, reply_markup=markup)
        return
    offset = max(0, page) * PAGE_SIZE
    engagement_filter = ""
    if engagement_only:
        engagement_filter = """
            AND (
              s.category ILIKE ANY(ARRAY['%%view%%', '%%like%%', '%%comment%%', '%%reaction%%', '%%مشاهد%%', '%%تفاعل%%', '%%اعجاب%%', '%%إعجاب%%'])
              OR COALESCE(s.custom_name, s.provider_name) ILIKE ANY(ARRAY['%%view%%', '%%like%%', '%%comment%%', '%%reaction%%', '%%مشاهد%%', '%%تفاعل%%', '%%اعجاب%%', '%%إعجاب%%'])
              OR s.description ILIKE ANY(ARRAY['%%view%%', '%%like%%', '%%comment%%', '%%reaction%%', '%%مشاهد%%', '%%تفاعل%%', '%%اعجاب%%', '%%إعجاب%%'])
            )
        """
    member_filter = ""
    if member_only:
        member_filter = """
            AND (
              s.category ILIKE ANY(ARRAY['%%follow%%', '%%follower%%', '%%subscriber%%', '%%member%%', '%%متابع%%', '%%مشترك%%', '%%عضو%%', '%%رشق%%'])
              OR COALESCE(s.custom_name, s.provider_name) ILIKE ANY(ARRAY['%%follow%%', '%%follower%%', '%%subscriber%%', '%%member%%', '%%متابع%%', '%%مشترك%%', '%%عضو%%', '%%رشق%%'])
              OR s.description ILIKE ANY(ARRAY['%%follow%%', '%%follower%%', '%%subscriber%%', '%%member%%', '%%متابع%%', '%%مشترك%%', '%%عضو%%', '%%رشق%%'])
            )
        """
    async with database() as conn:
        rows = await fetch_all(
            conn,
            f"""
            SELECT s.id, COALESCE(NULLIF(s.custom_name, ''), s.provider_name) AS name,
                   s.description, s.category, s.min_quantity, s.max_quantity,
                   s.base_rate, s.markup_percent, p.name AS provider_name
            FROM nabil_services s
            JOIN nabil_providers p ON p.id = s.provider_id
            WHERE s.enabled = TRUE AND p.enabled = TRUE
            {engagement_filter}
            {member_filter}
            ORDER BY s.category, name
            LIMIT %s OFFSET %s
            """,
            (PAGE_SIZE + 1, offset),
        )
    has_next = len(rows) > PAGE_SIZE
    rows = rows[:PAGE_SIZE]
    if not rows:
        if engagement_only:
            text = "ما لقينا خدمات مشاهدة أو تفاعل مفعّلة حالياً."
        elif member_only:
            text = "لا توجد خدمات رشق أعضاء مفعّلة حالياً. راجع الإدارة."
        else:
            text = "لا توجد خدمات مفعّلة حالياً."
        if hasattr(target, "edit_message_text"):
            await target.edit_message_text(
                text,
                reply_markup=InlineKeyboardMarkup(
                    [[InlineKeyboardButton("القائمة", callback_data="menu:home")]]
                ),
            )
        else:
            await target.reply_text(
                text,
                reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
            )
        return
    buttons = []
    lines = [
        (
            "اختار خدمة من الخدمات السريعة المتاحة:"
            if engagement_only
            else (
                "خدمات رشق الأعضاء المتاحة:"
                if member_only
                else "الخدمات المتاحة:"
            )
        )
    ]
    for row in rows:
        if not engagement_only:
            price = service_price(row)
            displayed_price = fmt_money(price)
            lines.append(
                f"\n<b>{safe_html(row['name'], 80)}</b> — {displayed_price} / 1000"
                f"\n{safe_html(row['description'], 110)}"
                f"\nالحدود: {row['min_quantity']}–{row['max_quantity']} | "
                f"المزود: {safe_html(row['provider_name'], 40)}"
            )
        buttons.append(
            [
                InlineKeyboardButton(
                    f"اختيار: {safe_text(row['name'], 45)}",
                    callback_data=(
                        f"svc:engagement:{row['id']}"
                        if engagement_only
                        else f"svc:{row['id']}"
                    ),
                )
            ]
        )
    nav = []
    if page > 0:
        prefix = "menu:engagement" if engagement_only else "menu:services"
        nav.append(InlineKeyboardButton("السابق", callback_data=f"{prefix}:{page - 1}"))
    if has_next:
        prefix = "menu:engagement" if engagement_only else "menu:services"
        nav.append(InlineKeyboardButton("التالي", callback_data=f"{prefix}:{page + 1}"))
    if nav:
        buttons.append(nav)
    buttons.append(
        [InlineKeyboardButton("رجوع للقائمة", callback_data="menu:home")]
    )
    if hasattr(target, "edit_message_text"):
        await target.edit_message_text(
            "\n".join(lines),
            reply_markup=InlineKeyboardMarkup(buttons),
            parse_mode=ParseMode.HTML,
        )
    else:
        await target.reply_text(
            "\n".join(lines),
            reply_markup=InlineKeyboardMarkup(buttons),
            parse_mode=ParseMode.HTML,
        )


async def show_balance(target, user_id: int):
    balance = await member_balance(user_id)
    markup = back_keyboard("menu:home", "رجوع للقائمة")
    text = f"رصيدك الحالي: <b>{safe_html(fmt_money(balance), 80)}</b>"
    if hasattr(target, "edit_message_text"):
        await target.edit_message_text(text, reply_markup=markup, parse_mode=ParseMode.HTML)
    else:
        await target.reply_text(text, reply_markup=markup, parse_mode=ParseMode.HTML)


async def show_referral_info(
    query,
    context: ContextTypes.DEFAULT_TYPE,
    user_id: int,
    back_callback: str = "menu:home",
    back_label: str = "رجوع للقائمة",
):
    async with database() as conn:
        state = await fetch_one(
            conn,
            """
            SELECT referrals_count FROM nabil_bot_user_state
            WHERE telegram_id = %s
            """,
            (user_id,),
        )
        leaders = await fetch_all(
            conn,
            """
            SELECT telegram_id, first_name, username, referrals_count
            FROM nabil_bot_user_state
            WHERE referrals_count > 0
            ORDER BY referrals_count DESC, telegram_id ASC
            LIMIT 10
            """,
        )
    referrals = int(state["referrals_count"]) if state else 0
    try:
        referrer_reward = money(
            Decimal(await get_setting("referral_referrer_balance_reward"))
        )
        invitee_reward = money(
            Decimal(await get_setting("referral_invitee_balance_reward"))
        )
    except (InvalidOperation, ValueError):
        referrer_reward = invitee_reward = money(0)

    bot = await context.bot.get_me()
    referral_url = (
        f"https://t.me/{bot.username}?start=ref_{user_id}"
        if bot.username
        else ""
    )
    lines = [
        "📨 <b>نظام مشاركة رابط الدعوة</b>",
        "",
        "🔗 رابط دعوتك الشخصي:",
        f"<code>{safe_html(referral_url, 500)}</code>"
        if referral_url
        else "الرابط غير متاح حالياً.",
        "",
        "💰 نظام المكافآت:",
        f"• كل شخص يفعل البوت عبر رابطك → تحصل على ({fmt_money(referrer_reward)}).",
        f"• الشخص الداخل عبر رابطك يحصل مباشرة على ({fmt_money(invitee_reward)}).",
        "",
        "📊 إحصائيات حسابك:",
        f"• عدد المشاركات: {referrals}",
        f"• رصيدك الحالي: {fmt_money(await member_balance(user_id))}",
        "",
        "🏆 قائمة الأكثر مشاركة:",
    ]
    if leaders:
        for rank, member in enumerate(leaders, start=1):
            lines.append(
                f"{rank}. {safe_html(wallet_member_name(member), 120)} — "
                f"{int(member['referrals_count'])} مشاركة"
            )
    else:
        lines.append("لا توجد مشاركات في القائمة بعد.")
    lines.extend(["", "✨ شارك الرابط الآن واجمع أكبر رصيد!"])

    buttons = []
    if referral_url:
        share_text = "انضم إلى البوت عبر رابط دعوتي"
        share_url = (
            "https://t.me/share/url?url="
            f"{urllib.parse.quote(referral_url, safe='')}"
            f"&text={urllib.parse.quote(share_text, safe='')}"
        )
        buttons.append(
            [InlineKeyboardButton("شارك الرابط الآن 📤", url=share_url)]
        )
        buttons.append(
            [InlineKeyboardButton("افتح رابط دعوتك 🔗", url=referral_url)]
        )
    buttons.append(
        [InlineKeyboardButton(back_label, callback_data=back_callback)]
    )
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
        disable_web_page_preview=True,
    )


async def show_points_menu(query, user_id: int):
    balance = await member_balance(user_id)
    await query.edit_message_text(
        f"<b>المكافآت ورصيدك</b>\n\nرصيدك: <b>{safe_html(fmt_money(balance), 80)}</b>",
        reply_markup=InlineKeyboardMarkup(
            [
                [InlineKeyboardButton("مشاركة رابط الدعوة 📨", callback_data="points:referrals")],
                [InlineKeyboardButton("الهدية اليومية 🎁", callback_data="points:daily")],
                [InlineKeyboardButton("كود الهدية 🎟️", callback_data="points:gift_code")],
                [InlineKeyboardButton("رجوع للقائمة", callback_data="menu:home")],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


async def show_member_points(query, context: ContextTypes.DEFAULT_TYPE, user_id: int):
    await show_balance(query, user_id)


async def claim_daily_gift(query, user_id: int):
    try:
        reward = daily_reward_amount(
            await get_setting("daily_balance_reward"),
            await get_setting("daily_balance_reward_max"),
        )
    except (InvalidOperation, ValueError):
        reward = money(0)
    status = "missing"
    balance_after = None
    if reward <= 0:
        status = "disabled"
    else:
        async with database() as conn:
            async with conn.transaction():
                member = await fetch_one(
                    conn,
                    "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                    (user_id,),
                )
                if member:
                    claimed = await fetch_one(
                        conn,
                        """
                        SELECT 1 AS claimed
                        FROM nabil_ledger
                        WHERE member_id = %s
                          AND entry_type IN ('daily_points_gift', 'daily_balance_gift')
                          AND created_at >= (
                            date_trunc('day', NOW() AT TIME ZONE 'Asia/Baghdad')
                            AT TIME ZONE 'Asia/Baghdad'
                          )
                        LIMIT 1
                        """,
                        (user_id,),
                    )
                    balance_before = money(Decimal(str(member["balance"])))
                    if claimed:
                        status = "claimed"
                        balance_after = balance_before
                    else:
                        balance_after = money(balance_before + reward)
                        await conn.execute(
                            "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                            (balance_after, user_id),
                        )
                        await conn.execute(
                            """
                            INSERT INTO nabil_ledger
                              (member_id, entry_type, amount, balance_after, note)
                            VALUES (%s, 'daily_balance_gift', %s, %s, %s)
                            """,
                            (user_id, reward, balance_after, "مكافأة رصيد يومية"),
                        )
                        await enqueue_live_mirror_wallet_event(
                            conn,
                            member_id=user_id,
                            entry_type="daily_balance_gift",
                            amount=reward,
                            balance_after=balance_after,
                            note="مكافأة رصيد يومية",
                            event_key=f"daily-gift:{user_id}:{uuid.uuid4().hex}",
                        )
                        status = "success"
    if status == "success":
        text = (
            "تم الحصول على هديتك اليومية 🎁\n"
            f"المكافأة: {fmt_money(reward)}\n"
            f"رصيدك الآن: {fmt_money(balance_after)}"
        )
    elif status == "claimed":
        text = (
            "استلمت مكافأتك اليومية بالفعل.\n"
            f"رصيدك الآن: {fmt_money(balance_after)}"
        )
    elif status == "disabled":
        text = "مكافأة الرصيد اليومية غير مفعلة حالياً."
    else:
        text = "تعذر العثور على حسابك."
    await query.edit_message_text(
        text,
        reply_markup=InlineKeyboardMarkup(
            [
                [InlineKeyboardButton("رجوع للقائمة", callback_data="menu:home")],
            ]
        ),
    )


async def redeem_gift_code(
    user_id: int, code: str
) -> tuple[str, Decimal | None, Decimal | None]:
    balance_after = None
    reward = None
    async with database() as conn:
        async with conn.transaction():
            member = await fetch_one(
                conn,
                "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                (user_id,),
            )
            if not member:
                return "missing", None, None
            code_row = await fetch_one(
                conn,
                """
                SELECT id, reward, max_uses, expires_at,
                       expires_at IS NOT NULL AND expires_at <= NOW() AS expired
                FROM nabil_gift_codes
                WHERE code = %s
                FOR UPDATE
                """,
                (code,),
            )
            if not code_row:
                return "invalid", None, None
            if code_row["expired"]:
                return "expired", None, None
            try:
                reward = money(Decimal(str(code_row["reward"])))
                if reward < 1 or reward > Decimal("1000000000"):
                    raise ValueError
            except (InvalidOperation, TypeError, ValueError):
                return "invalid", None, None
            prefix = f"gift_code:{code}:"
            already_used = await fetch_one(
                conn,
                """
                SELECT 1 AS used FROM nabil_gift_code_redemptions
                WHERE gift_code_id = %s AND member_id = %s
                UNION ALL
                SELECT 1 AS used FROM nabil_ledger
                WHERE member_id = %s
                  AND entry_type IN ('gift_code_points', 'gift_code_balance')
                  AND LEFT(note, %s) = %s
                LIMIT 1
                """,
                (code_row["id"], user_id, user_id, len(prefix), prefix),
            )
            balance_before = money(Decimal(str(member["balance"])))
            if already_used:
                return "used", balance_before, None
            usage_row = await fetch_one(
                conn,
                """
                SELECT COUNT(*) AS used_count
                FROM nabil_gift_code_redemptions
                WHERE gift_code_id = %s
                """,
                (code_row["id"],),
            )
            if int(usage_row["used_count"]) >= int(code_row["max_uses"]):
                return "exhausted", None, None
            balance_after = money(balance_before + reward)
            await conn.execute(
                "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                (balance_after, user_id),
            )
            await conn.execute(
                """
                INSERT INTO nabil_ledger
                  (member_id, entry_type, amount, balance_after, note)
                VALUES (%s, 'gift_code_balance', %s, %s, %s)
                """,
                (
                    user_id,
                    reward,
                    balance_after,
                    f"gift_code:{code}:balance:{reward}",
                ),
            )
            await enqueue_live_mirror_wallet_event(
                conn,
                member_id=user_id,
                entry_type="gift_code_balance",
                amount=reward,
                balance_after=balance_after,
                note="استرداد كود هدية",
                event_key=f"gift-code:{code_row['id']}:{user_id}",
            )
            await conn.execute(
                """
                INSERT INTO nabil_gift_code_redemptions
                  (gift_code_id, member_id, reward)
                VALUES (%s, %s, %s)
                """,
                (code_row["id"], user_id, reward),
            )
    return "success", balance_after, reward


async def begin_balance_transfer(query, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.clear()
    context.user_data["mode"] = "transfer_recipient"
    await query.edit_message_text(
        "أرسل رقم حساب تيليغرام للمستلم. استخدم /cancel للإلغاء.",
        reply_markup=back_keyboard("transfer:cancel", "رجوع للقائمة"),
    )


async def complete_balance_transfer(query, context: ContextTypes.DEFAULT_TYPE, user_id: int):
    recipient_id = context.user_data.get("transfer_recipient")
    amount_value = context.user_data.get("transfer_amount")
    try:
        amount = money(Decimal(str(amount_value)))
        minimum = money(Decimal(await get_setting("min_balance_transfer")))
    except (InvalidOperation, ValueError):
        minimum = money(1)
        amount = money(0)
    if not isinstance(recipient_id, int) or recipient_id == user_id or amount < minimum or amount <= 0:
        context.user_data.clear()
        await query.edit_message_text(
            "بيانات التحويل غير صالحة أو أقل من الحد الأدنى.",
            reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("القائمة", callback_data="menu:home")]]
            ),
        )
        return
    result = None
    new_balance = None
    recipient_balance = None
    async with database() as conn:
        async with conn.transaction():
            rows = {}
            for target_id in sorted((user_id, recipient_id)):
                rows[target_id] = await fetch_one(
                    conn,
                    "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                    (target_id,),
                )
            recipient_state = await fetch_one(
                conn,
                "SELECT is_banned FROM nabil_bot_user_state WHERE telegram_id = %s",
                (recipient_id,),
            )
            if not rows[user_id] or not rows[recipient_id]:
                result = "المستلم غير مسجل في البوت."
            elif recipient_state and recipient_state["is_banned"]:
                result = "لا يمكن التحويل إلى حساب محظور."
            elif money(rows[user_id]["balance"]) < amount:
                result = "رصيدك غير كافٍ لإتمام التحويل."
            else:
                sender_balance = money(Decimal(str(rows[user_id]["balance"])) - amount)
                recipient_balance = money(Decimal(str(rows[recipient_id]["balance"])) + amount)
                await conn.execute(
                    "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                    (sender_balance, user_id),
                )
                await conn.execute(
                    "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                    (recipient_balance, recipient_id),
                )
                await conn.execute(
                    """
                    INSERT INTO nabil_ledger
                      (member_id, entry_type, amount, balance_after, note)
                    VALUES (%s, 'member_transfer_out', %s, %s, %s),
                           (%s, 'member_transfer_in', %s, %s, %s)
                    """,
                    (
                        user_id, -amount, sender_balance, f"تحويل إلى العضو {recipient_id}",
                        recipient_id, amount, recipient_balance, f"تحويل من العضو {user_id}",
                    ),
                )
                await enqueue_live_mirror_wallet_event(
                    conn,
                    member_id=user_id,
                    entry_type="member_transfer_out",
                    amount=-amount,
                    balance_after=sender_balance,
                    note=f"تحويل إلى العضو {recipient_id}",
                    counterparty_id=recipient_id,
                    event_key=f"transfer:{uuid.uuid4().hex}",
                )
                new_balance = sender_balance
                result = f"تم التحويل بنجاح. رصيدك الجديد: {fmt_money(sender_balance)}"
    context.user_data.clear()
    await query.edit_message_text(
        result or "تعذر إتمام التحويل.",
        reply_markup=InlineKeyboardMarkup(
            [[InlineKeyboardButton("القائمة", callback_data="menu:home")]]
        ),
    )
    if new_balance is not None and recipient_balance is not None:
        await notify_balance_change(
            context.bot,
            user_id,
            -amount,
            new_balance,
            f"تحويل رصيد إلى العضو {recipient_id}",
        )
        await notify_balance_change(
            context.bot,
            recipient_id,
            amount,
            recipient_balance,
            f"تحويل رصيد من العضو {user_id}",
        )


async def show_member_orders(target, user_id: int):
    async with database() as conn:
        rows = await fetch_all(
            conn,
            """
            SELECT id, service_name, quantity, status, sale_amount, created_at,
                   refunded_amount
            FROM nabil_orders
            WHERE member_id = %s
            ORDER BY id DESC LIMIT 10
            """,
            (user_id,),
        )
    if not rows:
        text = "ما عندك طلبات لحد الآن."
    else:
        lines = ["آخر طلباتك:"]
        for row in rows:
            when = row["created_at"].strftime("%Y-%m-%d %H:%M UTC")
            lines.append(
                f"\n#{row['id']} — {safe_text(row['service_name'], 60)}"
                f"\nالكمية: {row['quantity']} | الحالة: {safe_text(order_status_label(row['status']), 30)}"
                f"\nالتكلفة: {fmt_money(row['sale_amount'])} | المسترد: "
                f"{fmt_money(row['refunded_amount'])} | {when}"
            )
        text = "\n".join(lines)
    if hasattr(target, "edit_message_text"):
        await target.edit_message_text(
            text,
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
        )
    else:
        await target.reply_text(
            text, reply_markup=back_keyboard("menu:home", "رجوع للقائمة")
        )


async def show_account_info(target, user_id: int):
    async with database() as conn:
        member = await fetch_one(
            conn,
            """
            SELECT m.telegram_id, m.balance, m.created_at,
                   COUNT(o.id) AS order_count,
                   COALESCE(s.referrals_count, 0) AS referrals_count,
                   COALESCE(s.is_banned, FALSE) AS is_banned,
                   s.first_name, s.username
            FROM nabil_members AS m
            LEFT JOIN nabil_orders AS o ON o.member_id = m.telegram_id
            LEFT JOIN nabil_bot_user_state AS s ON s.telegram_id = m.telegram_id
            WHERE m.telegram_id = %s
            GROUP BY m.telegram_id, s.referrals_count, s.is_banned,
                     s.first_name, s.username
            """,
            (user_id,),
        )
    if not member:
        text = "حسابك غير مسجل حالياً. أرسل /start لتسجيله."
    else:
        telegram_user = getattr(target, "from_user", None)
        first_name = (
            member["first_name"]
            or getattr(telegram_user, "first_name", None)
            or "غير مسجل"
        )
        username = member["username"] or getattr(
            telegram_user, "username", None
        )
        username_line = (
            f"\nاسم المستخدم: @{safe_html(username, 80)}"
            if username
            else "\nاسم المستخدم: غير محدد"
        )
        joined = member["created_at"].strftime("%Y-%m-%d")
        status = "محظور" if member["is_banned"] else "نشط"
        text = (
            "<b>معلومات حسابك 👤</b>\n"
            f"الاسم: {safe_html(first_name, 120)}"
            f"{username_line}\n"
            f"الآيدي: <code>{member['telegram_id']}</code>\n"
            f"الرصيد: <b>{fmt_money(member['balance'])}</b>\n"
            f"عدد الطلبات: {member['order_count']}\n"
            f"الدعوات الناجحة: {member['referrals_count']}\n"
            f"تاريخ التسجيل: {joined}\n"
            f"حالة الحساب: {status}"
        )
    if hasattr(target, "edit_message_text"):
        await target.edit_message_text(
            text,
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
            parse_mode=ParseMode.HTML,
        )
    else:
        await target.reply_text(
            text,
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
            parse_mode=ParseMode.HTML,
        )


async def lookup_member_order(
    message, user_id: int, order_id: int, bot=None
):
    can_view_all_orders = await has_admin_permission(user_id, "orders")
    order_filter = "o.id = %s"
    params = (order_id,)
    if not can_view_all_orders:
        order_filter += " AND o.member_id = %s"
        params = (order_id, user_id)
    async with database() as conn:
        order = await fetch_one(
            conn,
            """
            SELECT o.*, p.name AS provider_name, p.domain,
                   p.api_key_encrypted, p.enabled AS provider_enabled
            FROM nabil_orders AS o
            LEFT JOIN nabil_providers AS p ON p.id = o.provider_id
            WHERE """ + order_filter,
            params,
        )
    if not order:
        await message.reply_text(
            "ما لقينا طلب بهذا الرقم."
            if can_view_all_orders
            else "ما لقينا طلب بهذا الرقم ضمن حسابك.",
            reply_markup=back_keyboard(
                "admin:orders" if can_view_all_orders else "menu:home",
                "رجوع للطلبات" if can_view_all_orders else "رجوع للقائمة",
            ),
        )
        return

    provider_status = None
    refresh_failed = False
    partial_status_unresolved = False
    refund_delta = Decimal("0")
    status_changed = False
    completion_changed = False
    if order["status"] in {"Pending", "Processing"}:
        if (
            order["provider_order_id"]
            and order["domain"]
            and order["api_key_encrypted"]
        ):
            try:
                response = await provider_post(
                    provider_public(order),
                    {
                        "action": "status",
                        "order": str(order["provider_order_id"]),
                    },
                    timeout=10.0,
                )
                provider_status = (
                    str(response["status"]).strip()
                    if isinstance(response, dict) and response.get("status")
                    else None
                )
                if provider_status:
                    normalized_status = normalize_provider_status(provider_status)
                    if normalized_status is not None:
                        refund_delta, _, _, status_changed = await apply_provider_status(
                            order,
                            provider_status,
                            parse_provider_remains(response.get("remains")),
                        )
                        completion_changed = (
                            normalized_status == "Completed" and status_changed
                        )
                        partial_status_unresolved = (
                            normalized_status == "Partial" and not status_changed
                        )
                else:
                    refresh_failed = True
            except Exception as exc:
                refresh_failed = True
                LOG.warning(
                    "Quick status refresh failed for order %s: %s",
                    order_id,
                    safe_provider_error(order, exc),
                )
        else:
            refresh_failed = True

    async with database() as conn:
        current = await fetch_one(
            conn,
            """
            SELECT status, refunded_amount
            FROM nabil_orders
            WHERE id = %s
            """,
            (order_id,),
        )
    if not current:
        return
    status = current["status"]
    refunded_amount = money(current["refunded_amount"] or 0)
    status_note = None
    if partial_status_unresolved and status in {"Pending", "Processing"}:
        status_note = (
            "أبلغ المزود عن اكتمال جزئي، لكن بيانات الكمية المتبقية غير صالحة؛ "
            "لم يتم اعتماد استرداد غير مؤكد."
        )
    unrecognized_status = (
        provider_status
        if provider_status and normalize_provider_status(provider_status) is None
        else None
    )
    text = order_status_message(
        order_id,
        status,
        refunded_amount,
        unrecognized_provider_status=unrecognized_status,
        status_note=status_note,
        refresh_failed=refresh_failed,
    )
    if completion_changed and order["member_id"] == user_id:
        text = order_completed_message(order_id, order["target_url"])
    reply_markup = back_keyboard(
        "admin:orders" if can_view_all_orders else "menu:home",
        "رجوع للطلبات" if can_view_all_orders else "رجوع للقائمة",
    )
    await message.reply_text(text, reply_markup=reply_markup)

    if (
        completion_changed
        and order["member_id"] != user_id
        and bot is not None
    ):
        await notify_order_completed(bot, order)

    if (
        refund_delta > 0
        and order["member_id"] != user_id
        and bot is not None
    ):
        try:
            await bot.send_message(
                order["member_id"],
                order_status_message(
                    order_id,
                    status,
                    refunded_amount,
                ),
                reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
            )
        except Exception as exc:
            LOG.warning(
                "Could not notify member %s about refund for order %s: %s",
                order["member_id"],
                order_id,
                safe_text(exc, 160),
            )


async def begin_member_rush_flow(query, context: ContextTypes.DEFAULT_TYPE):
    if not await setting_enabled("member_rush_enabled"):
        await query.edit_message_text(
            "خدمة رشق الأعضاء متوقفة حالياً.",
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
        )
        return
    service = await active_kd1s_member_service()
    if not service:
        await query.edit_message_text(
            "لا توجد خدمة رشق KD1S مفعّلة حالياً. راجع الإدارة.",
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
        )
        return
    context.user_data.clear()
    context.user_data.update(
        {
            "mode": "member_rush_quantity",
            "service_id": service["id"],
        }
    )
    await query.edit_message_text(
        "كم عدد الأعضاء المطلوب؟\n"
        f"الحد الأدنى: {service['min_quantity']}\n"
        f"الحد الأعلى: {service['max_quantity']}\n"
        "أرسل العدد كرقم صحيح.",
        reply_markup=back_keyboard("buy:cancel", "إلغاء الطلب"),
    )


async def handle_member_rush_quantity(
    update: Update, context: ContextTypes.DEFAULT_TYPE, text: str
):
    try:
        quantity = parse_service_quantity(text)
    except ValueError as exc:
        await update.message.reply_text(
            f"{safe_text(exc, 160)} أرسل العدد المطلوب.",
            reply_markup=back_keyboard("buy:cancel", "إلغاء الطلب"),
        )
        return
    service = await active_kd1s_member_service(
        context.user_data.get("service_id")
    )
    if not service:
        context.user_data.clear()
        await update.message.reply_text(
            "خدمة رشق KD1S لم تعد متاحة. ابدأ الطلب من جديد.",
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
        )
        return
    if quantity < service["min_quantity"] or quantity > service["max_quantity"]:
        await update.message.reply_text(
            f"العدد لازم يكون بين {service['min_quantity']} و{service['max_quantity']}. "
            "أعد إرسال العدد.",
            reply_markup=back_keyboard("buy:cancel", "إلغاء الطلب"),
        )
        return
    context.user_data.update(
        {"quantity": quantity, "mode": "member_rush_channel"}
    )
    await update.message.reply_text(
        "أرسل رابط قناة تيليغرام، مثل https://t.me/channelname.",
        reply_markup=back_keyboard("buy:cancel", "إلغاء الطلب"),
    )


async def handle_member_rush_channel(
    update: Update, context: ContextTypes.DEFAULT_TYPE, text: str
):
    target_url = text.strip()
    blocked, remaining_minutes = await update_order_link_protection(
        update.effective_user.id
    )
    if blocked:
        context.user_data.clear()
        await update.message.reply_text(
            "تم إيقاف الطلبات مؤقتاً بسبب تكرار الروابط غير الصالحة. "
            f"حاول بعد {remaining_minutes} دقيقة."
        )
        return
    if platform_for_url(target_url) != "telegram":
        blocked, remaining_minutes = await update_order_link_protection(
            update.effective_user.id, invalid_attempt=True
        )
        if blocked:
            context.user_data.clear()
        await update.message.reply_text(
            (
                "تم إيقاف الطلبات مؤقتاً بسبب تكرار الروابط غير الصالحة. "
                f"حاول بعد {remaining_minutes} دقيقة."
                if blocked
                else "رابط القناة غير صالح. أرسل رابطاً صحيحاً من t.me أو telegram.me."
            ),
            reply_markup=back_keyboard("buy:cancel", "إلغاء الطلب"),
        )
        return
    await update_order_link_protection(
        update.effective_user.id, invalid_attempt=False
    )
    service = await active_kd1s_member_service(
        context.user_data.get("service_id")
    )
    quantity = context.user_data.get("quantity")
    if not service or not isinstance(quantity, int):
        context.user_data.clear()
        await update.message.reply_text(
            "انتهت جلسة الطلب. ابدأ من قسم رشق الأعضاء.",
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
        )
        return
    if quantity < service["min_quantity"] or quantity > service["max_quantity"]:
        context.user_data.clear()
        await update.message.reply_text(
            "تغيرت حدود الخدمة. ابدأ الطلب من جديد.",
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
        )
        return
    charge = order_charge(service, quantity)
    balance = await member_balance(update.effective_user.id)
    context.user_data.update(
        {
            "target_url": target_url,
            "quoted_charge": str(charge),
            "mode": None,
        }
    )
    balance_note = (
        "رصيدك لا يكفي حالياً لإتمام الطلب."
        if balance < charge
        else "سيُخصم المبلغ من رصيدك بعد قبول KD1S للطلب."
    )
    keyboard = InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("إرسال الطلب", callback_data="buy:confirm")],
            [InlineKeyboardButton("إلغاء الطلب", callback_data="buy:cancel")],
        ]
    )
    await update.message.reply_text(
        "راجع تفاصيل الطلب:\n"
        f"الخدمة: {safe_text(service.get('custom_name') or service['provider_name'], 100)}\n"
        f"عدد الأعضاء: {quantity}\n"
        f"السعر لكل 1000: {fmt_money(service_price(service))}\n"
        f"التكلفة الإجمالية: {fmt_money(charge)}\n"
        f"رصيدك الحالي: {fmt_money(balance)}\n"
        f"رابط القناة: {safe_text(target_url, 220)}\n\n"
        f"{balance_note}",
        reply_markup=keyboard,
    )


async def begin_order(
    query,
    context: ContextTypes.DEFAULT_TYPE,
    service_id: int,
    return_callback: str = "menu:services:0",
):
    async with database() as conn:
        service = await fetch_one(
            conn,
            """
            SELECT s.*, p.name AS provider_name
            FROM nabil_services s JOIN nabil_providers p ON p.id = s.provider_id
            WHERE s.id = %s AND s.enabled = TRUE AND p.enabled = TRUE
            """,
            (service_id,),
        )
    if not service:
        await query.edit_message_text(
            "الخدمة لم تعد متاحة.",
            reply_markup=back_keyboard(return_callback, "رجوع للخدمات"),
        )
        return
    name = service.get("custom_name") or service["provider_name"]
    context.user_data.clear()
    context.user_data.update(
        {
            "mode": "order_quantity",
            "service_id": service_id,
            "service_menu_callback": return_callback,
        }
    )
    await query.edit_message_text(
        f"<b>{safe_html(name, 100)}</b>\n"
        f"{safe_html(service.get('description') or 'لا يوجد وصف للخدمة.', 300)}\n"
        f"الحد الأدنى: {service['min_quantity']}\n"
        f"الحد الأعلى: {service['max_quantity']}\n"
        f"السعر: {fmt_money(service_price(service))} لكل 1000\n\n"
        "أرسل العدد الذي تريده.",
        reply_markup=back_keyboard("buy:cancel", "إلغاء والعودة للخدمات"),
        parse_mode=ParseMode.HTML,
    )


async def handle_order_link(
    update: Update, context: ContextTypes.DEFAULT_TYPE, text: str
):
    user_id = update.effective_user.id
    blocked, remaining_minutes = await update_order_link_protection(user_id)
    if blocked:
        context.user_data.clear()
        await update.message.reply_text(
            "تم إيقاف الطلبات مؤقتاً بسبب تكرار الروابط غير الصالحة. "
            f"حاول بعد {remaining_minutes} دقيقة."
        )
        return
    valid, validation_error = validate_platform_link(text)
    if not valid:
        blocked, remaining_minutes = await update_order_link_protection(
            user_id, invalid_attempt=True
        )
        if blocked:
            context.user_data.clear()
        await update.message.reply_text(
            (
                "تم إيقاف الطلبات مؤقتاً بسبب تكرار الروابط غير الصالحة. "
                f"حاول بعد {remaining_minutes} دقيقة."
                if blocked
                else validation_error
            ),
            reply_markup=back_keyboard(
                "buy:cancel", "إلغاء والعودة للخدمات"
            ),
        )
        return
    await update_order_link_protection(user_id, invalid_attempt=False)
    service_id = context.user_data.get("service_id")
    quantity = context.user_data.get("quantity")
    return_callback = context.user_data.get(
        "service_menu_callback", "menu:home"
    )
    if not isinstance(service_id, int) or not isinstance(quantity, int):
        context.user_data.clear()
        await update.message.reply_text(
            "انتهت جلسة الطلب. اختر الخدمة من جديد.",
            reply_markup=back_keyboard(return_callback, "رجوع للخدمات"),
        )
        return
    async with database() as conn:
        service = await fetch_one(
            conn,
            """
            SELECT s.*, p.enabled AS provider_enabled
            FROM nabil_services s JOIN nabil_providers p ON p.id = s.provider_id
            WHERE s.id = %s
            """,
            (service_id,),
        )
    if not service or not service["enabled"] or not service["provider_enabled"]:
        context.user_data.clear()
        await update.message.reply_text(
            "الخدمة لم تعد متاحة.",
            reply_markup=back_keyboard(return_callback, "رجوع للخدمات"),
        )
        return
    if quantity < service["min_quantity"] or quantity > service["max_quantity"]:
        context.user_data["mode"] = "order_quantity"
        await update.message.reply_text(
            f"العدد لازم يكون بين {service['min_quantity']} و{service['max_quantity']}. "
            "أعد إرسال العدد.",
            reply_markup=back_keyboard(
                "buy:cancel", "إلغاء والعودة للخدمات"
            ),
        )
        return

    target_url = text.strip()
    charge = order_charge(service, quantity)
    balance = await member_balance(update.effective_user.id)
    context.user_data.update(
        {
            "target_url": target_url,
            "quoted_charge": str(charge),
            "mode": None,
        }
    )
    balance_note = (
        "رصيدك لا يكفي حالياً لإتمام الطلب."
        if balance < charge
        else "سيُخصم المبلغ من رصيدك بعد التأكيد."
    )
    keyboard = InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("موافق", callback_data="buy:confirm"),
                InlineKeyboardButton(
                    "إلغاء والعودة للخدمات", callback_data="buy:cancel"
                ),
            ]
        ]
    )
    await update.message.reply_text(
        "راجع تفاصيل الطلب:\n"
        f"الخدمة: {safe_text(service.get('custom_name') or service['provider_name'], 100)}\n"
        f"الوصف: {safe_text(service.get('description') or '—', 180)}\n"
        f"العدد: {quantity}\n"
        f"الحدود: {service['min_quantity']}–{service['max_quantity']}\n"
        f"السعر لكل 1000: {fmt_money(service_price(service))}\n"
        f"المجموع: {fmt_money(charge)}\n"
        f"الرابط: {safe_text(target_url, 220)}\n"
        f"رصيدك الحالي: {fmt_money(balance)}\n\n"
        f"{balance_note}",
        reply_markup=keyboard,
    )


async def handle_order_quantity(
    update: Update, context: ContextTypes.DEFAULT_TYPE, text: str
):
    try:
        quantity = parse_service_quantity(text)
    except ValueError as exc:
        await update.message.reply_text(
            f"{safe_text(exc, 160)} أرسل العدد المطلوب.",
            reply_markup=back_keyboard(
                "buy:cancel", "إلغاء والعودة للخدمات"
            ),
        )
        return
    service_id = context.user_data.get("service_id")
    return_callback = context.user_data.get(
        "service_menu_callback", "menu:home"
    )
    if not isinstance(service_id, int):
        context.user_data.clear()
        await update.message.reply_text(
            "انتهت جلسة الطلب. اختر الخدمة من جديد.",
            reply_markup=back_keyboard(return_callback, "رجوع للخدمات"),
        )
        return
    async with database() as conn:
        service = await fetch_one(
            conn,
            """
            SELECT s.*, p.enabled AS provider_enabled
            FROM nabil_services s JOIN nabil_providers p ON p.id = s.provider_id
            WHERE s.id = %s
            """,
            (service_id,),
        )
    if not service or not service["enabled"] or not service["provider_enabled"]:
        context.user_data.clear()
        await update.message.reply_text(
            "الخدمة لم تعد متاحة.",
            reply_markup=back_keyboard(return_callback, "رجوع للخدمات"),
        )
        return
    if quantity < service["min_quantity"] or quantity > service["max_quantity"]:
        await update.message.reply_text(
            f"العدد لازم يكون بين {service['min_quantity']} و{service['max_quantity']}. "
            "أعد إرسال العدد.",
            reply_markup=back_keyboard(
                "buy:cancel", "إلغاء والعودة للخدمات"
            ),
        )
        return
    context.user_data.update(
        {
            "quantity": quantity,
            "mode": "order_link",
        }
    )
    await update.message.reply_text(
        f"تم اختيار العدد: {quantity}.\n"
        "أرسل رابط المنشور أو الحساب المطلوب.",
        reply_markup=back_keyboard(
            "buy:cancel", "إلغاء والعودة للخدمات"
        ),
    )


async def submit_member_rush_order(
    user_id: int,
    order_id: int,
    provider: dict,
    provider_service_id: str,
    target_url: str,
    quantity: int,
    charge: Decimal,
) -> tuple[str, Decimal | None, str]:
    """Submit a KD1S order and debit the member's IQD balance after acceptance."""
    charge = money(Decimal(str(charge)))
    external_id = None
    request_started = False
    try:
        async with database() as conn:
            async with conn.transaction():
                member = await fetch_one(
                    conn,
                    "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                    (user_id,),
                )
                if not member:
                    error = "لم يتم العثور على حساب العضو."
                    await conn.execute(
                        """
                        UPDATE nabil_orders
                        SET status = 'Canceled', last_error = %s, updated_at = NOW()
                        WHERE id = %s
                        """,
                        (error, order_id),
                    )
                    return "insufficient", None, error
                balance_before = money(Decimal(str(member["balance"] or 0)))
                if balance_before < charge:
                    error = "انخفض الرصيد قبل إرسال الطلب."
                    await conn.execute(
                        """
                        UPDATE nabil_orders
                        SET status = 'Canceled', last_error = %s, updated_at = NOW()
                        WHERE id = %s
                        """,
                        (error, order_id),
                    )
                    return "insufficient", balance_before, error

                try:
                    request_started = True
                    external_id, _provider_response = await send_order_to_api(
                        provider,
                        {
                            "order_id": order_id,
                            "provider_service_id": provider_service_id,
                            "target_url": target_url,
                            "quantity": quantity,
                        },
                    )
                except Exception as exc:
                    error = safe_provider_error(provider, exc)
                    rejected = isinstance(exc, ProviderError) and exc.definitive
                    await conn.execute(
                        """
                        UPDATE nabil_orders
                        SET status = %s, last_error = %s, updated_at = NOW()
                        WHERE id = %s
                        """,
                        ("Canceled" if rejected else "Pending", error, order_id),
                    )
                    return (
                        "rejected" if rejected else "uncertain",
                        balance_before,
                        error,
                    )

                balance_after = money(balance_before - charge)
                await conn.execute(
                    "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                    (balance_after, user_id),
                )
                await conn.execute(
                    """
                    INSERT INTO nabil_ledger
                      (member_id, order_id, entry_type, amount, balance_after, note)
                    VALUES (%s, %s, 'order_debit', %s, %s, %s)
                    """,
                    (
                        user_id,
                        order_id,
                        -charge,
                        balance_after,
                        "خصم طلب رشق الأعضاء بعد قبول KD1S",
                    ),
                )
                await enqueue_live_mirror_wallet_event(
                    conn,
                    member_id=user_id,
                    entry_type="order_debit",
                    amount=-charge,
                    balance_after=balance_after,
                    note="خصم طلب خدمة",
                    order_id=order_id,
                    target_url=target_url,
                    quantity=quantity,
                    event_key=f"order-debit:{order_id}",
                )
                await conn.execute(
                    """
                    UPDATE nabil_orders
                    SET provider_order_id = %s, last_error = NULL, updated_at = NOW()
                    WHERE id = %s AND provider_id = %s
                    """,
                    (str(external_id), order_id, provider["id"]),
                )
                await enqueue_live_mirror_purchase(conn, order_id)
                return "success", balance_after, ""
    except Exception as exc:
        error = safe_provider_error(provider, exc)
        if external_id is not None:
            try:
                async with database() as conn:
                    async with conn.transaction():
                        member = await fetch_one(
                            conn,
                            "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                            (user_id,),
                        )
                        ledger = await fetch_one(
                            conn,
                            """
                            SELECT COALESCE(SUM(-amount), 0) AS charged
                            FROM nabil_ledger
                            WHERE order_id = %s AND entry_type = 'order_debit'
                            """,
                            (order_id,),
                        )
                        charged = money(
                            Decimal(str(ledger["charged"] or 0)) if ledger else Decimal(0)
                        )
                        balance_after = (
                            money(Decimal(str(member["balance"] or 0)))
                            if member
                            else None
                        )
                        if (
                            member
                            and charged < charge
                            and balance_after is not None
                            and balance_after >= charge
                        ):
                            balance_after = money(balance_after - charge)
                            await conn.execute(
                                "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                                (balance_after, user_id),
                            )
                            await conn.execute(
                                """
                                INSERT INTO nabil_ledger
                                  (member_id, order_id, entry_type, amount,
                                   balance_after, note)
                                VALUES (%s, %s, 'order_debit', %s, %s, %s)
                                """,
                                (
                                    user_id,
                                    order_id,
                                    -charge,
                                    balance_after,
                                    "خصم طلب رشق الأعضاء بعد قبول KD1S",
                                ),
                            )
                            await enqueue_live_mirror_wallet_event(
                                conn,
                                member_id=user_id,
                                entry_type="order_debit",
                                amount=-charge,
                                balance_after=balance_after,
                                note="خصم طلب خدمة",
                                order_id=order_id,
                                target_url=target_url,
                                quantity=quantity,
                                event_key=f"order-debit:{order_id}",
                            )
                            charged = charge
                        await conn.execute(
                            """
                            UPDATE nabil_orders
                            SET provider_order_id = %s, last_error = %s, updated_at = NOW()
                            WHERE id = %s AND provider_id = %s
                            """,
                            (
                                str(external_id),
                                None if charged >= charge else error,
                                order_id,
                                provider["id"],
                            ),
                        )
                        await enqueue_live_mirror_purchase(conn, order_id)
                        if charged >= charge and balance_after is not None:
                            return "success", balance_after, ""
            except Exception:
                LOG.exception(
                    "Could not reconcile accepted KD1S order %s after a database error.",
                    order_id,
                )
            return (
                "accepted_unbilled",
                None,
                "قبل KD1S الطلب، لكن تعذر تأكيد الخصم من الرصيد. لا تعاود الطلب.",
            )

        try:
            async with database() as conn:
                await conn.execute(
                    """
                    UPDATE nabil_orders
                    SET status = %s, last_error = %s, updated_at = NOW()
                    WHERE id = %s
                    """,
                    ("Pending" if request_started else "Canceled", error, order_id),
                )
        except Exception:
            LOG.exception("Could not update uncertain KD1S order %s.", order_id)
        return ("uncertain" if request_started else "not_sent", None, error)


async def place_order(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    service_id = context.user_data.get("service_id")
    quantity = context.user_data.get("quantity")
    target_url = context.user_data.get("target_url")
    if not service_id or not quantity or not target_url:
        await update.callback_query.edit_message_text(
            "انتهت جلسة الطلب. ابدأ من قائمة الخدمات.",
            reply_markup=back_keyboard("menu:services:0", "رجوع للخدمات"),
        )
        return
    blocked, remaining_minutes = await update_order_link_protection(user_id)
    if blocked:
        context.user_data.clear()
        await update.callback_query.edit_message_text(
            "تم إيقاف الطلبات مؤقتاً بسبب تكرار الروابط غير الصالحة. "
            f"حاول بعد {remaining_minutes} دقيقة.",
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
        )
        return
    valid_link, validation_error = validate_platform_link(target_url)
    if not valid_link:
        blocked, remaining_minutes = await update_order_link_protection(
            user_id, invalid_attempt=True
        )
        context.user_data.clear()
        await update.callback_query.edit_message_text(
            (
                "تم إيقاف الطلبات مؤقتاً بسبب تكرار الروابط غير الصالحة. "
                f"حاول بعد {remaining_minutes} دقيقة."
                if blocked
                else validation_error
            ),
            reply_markup=back_keyboard("menu:services:0", "رجوع للخدمات"),
        )
        return
    order_id = None
    provider = None
    current_charge = None
    member_rush_order = False
    balance_after = None
    async with database() as conn:
        async with conn.transaction():
            member = await fetch_one(
                conn,
                "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                (user_id,),
            )
            service = await fetch_one(
                conn,
                """
                SELECT s.*, p.name AS provider_name, p.domain, p.api_key_encrypted,
                       p.enabled AS provider_enabled
                FROM nabil_services s JOIN nabil_providers p ON p.id = s.provider_id
                WHERE s.id = %s FOR UPDATE OF s, p
                """,
                (service_id,),
            )
            if not member or not service or not service["enabled"] or not service["provider_enabled"]:
                await update.callback_query.edit_message_text(
                    "الخدمة غير متاحة حالياً.",
                    reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
                )
                context.user_data.clear()
                return
            if quantity < service["min_quantity"] or quantity > service["max_quantity"]:
                await update.callback_query.edit_message_text(
                    "الكمية لم تعد ضمن حدود الخدمة.",
                    reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
                )
                context.user_data.clear()
                return
            current_charge = order_charge(service, quantity)
            member_rush_order = is_member_rush_service(service)
            if member_rush_order and platform_for_url(target_url) != "telegram":
                context.user_data.clear()
                await update.callback_query.edit_message_text(
                    "خدمة رشق الأعضاء تقبل روابط قنوات تيليغرام فقط.",
                    reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
                )
                return
            charge_changed = str(current_charge) != str(
                context.user_data.get("quoted_charge")
            )
            if charge_changed:
                await update.callback_query.edit_message_text(
                    f"تغير سعر الخدمة؛ السعر الحالي هو {fmt_money(current_charge)}. "
                    "ارجع للخدمات وابدأ الطلب من جديد للتأكيد.",
                    reply_markup=back_keyboard("menu:services:0", "رجوع للخدمات"),
                )
                context.user_data.clear()
                return
            balance_before = money(Decimal(str(member["balance"])))
            if balance_before < current_charge:
                await update.callback_query.edit_message_text(
                    f"رصيدك غير كافٍ. رصيدك {fmt_money(balance_before)} "
                    f"وسعر الطلب {fmt_money(current_charge)}.",
                    reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
                )
                context.user_data.clear()
                return
            can_submit, blocked_minutes = await reserve_order_submission(
                conn, user_id
            )
            if not can_submit:
                context.user_data.clear()
                await update.callback_query.edit_message_text(
                    (
                        "تم إيقاف الطلبات مؤقتاً بسبب تكرار الروابط غير الصالحة. "
                        f"حاول بعد {blocked_minutes} دقيقة."
                        if blocked_minutes
                        else "انتظر قليلاً قبل إرسال طلب آخر."
                    ),
                    reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
                )
                return
            if not member_rush_order:
                balance_after = money(
                    balance_before - current_charge
                )
            name = service.get("custom_name") or service["provider_name"]
            provider = {
                "id": service["provider_id"],
                "name": service["provider_name"],
                "domain": KD1S_API_URL if member_rush_order else service["domain"],
                "api_key_encrypted": service["api_key_encrypted"],
            }
            row = await fetch_one(
                conn,
                """
                INSERT INTO nabil_orders
                  (member_id, service_id, provider_id, provider_service_id, service_name,
                   target_url, quantity, status, sale_amount, provider_rate, provider_cost)
                VALUES (%s, %s, %s, %s, %s, %s, %s, 'Pending', %s, %s, 0)
                RETURNING id
                """,
                (
                    user_id,
                    service_id,
                    service["provider_id"],
                    service["provider_service_id"],
                    name,
                    target_url,
                    quantity,
                    current_charge,
                    service["base_rate"],
                ),
            )
            order_id = row["id"]
            if not member_rush_order:
                await conn.execute(
                    "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                    (balance_after, user_id),
                )
                await conn.execute(
                    """
                    INSERT INTO nabil_ledger
                      (member_id, order_id, entry_type, amount, balance_after, note)
                    VALUES (%s, %s, 'order_debit', %s, %s, %s)
                    """,
                    (
                        user_id,
                        order_id,
                        -current_charge,
                        balance_after,
                        "خصم إنشاء الطلب",
                    ),
                )
                await enqueue_live_mirror_wallet_event(
                    conn,
                    member_id=user_id,
                    entry_type="order_debit",
                    amount=-current_charge,
                    balance_after=balance_after,
                    note="خصم طلب خدمة",
                    order_id=order_id,
                    order_service_name=name,
                    target_url=target_url,
                    quantity=quantity,
                    event_key=f"order-debit:{order_id}",
                )
    context.user_data.clear()
    if member_rush_order:
        result, balance_after, provider_error = await submit_member_rush_order(
            user_id,
            order_id,
            provider,
            str(service["provider_service_id"]),
            target_url,
            quantity,
            current_charge,
        )
        if result == "success":
            text = order_success_message(order_id, current_charge)
        elif result == "insufficient":
            text = (
                f"لم يُرسل الطلب #{order_id} لأن رصيدك تغيّر قبل الإرسال. "
                f"رصيدك الآن {fmt_money(balance_after or 0)}؛ لم يُخصم شيء."
            )
        elif result == "rejected":
            text = (
                f"رفض KD1S الطلب #{order_id}. لم يُخصم شيء من رصيدك.\n"
                f"{safe_text(provider_error, 220)}"
            )
        elif result == "accepted_unbilled":
            text = (
                f"قبل KD1S الطلب #{order_id}، لكن تعذر تأكيد الخصم من رصيدك. "
                "لا تعاود إرسال الطلب؛ أُبلغت الإدارة للمراجعة."
            )
        elif result == "not_sent":
            text = (
                f"تعذر تجهيز الطلب #{order_id} قبل إرساله إلى KD1S. "
                "لم يُخصم شيء من رصيدك؛ حاول مجدداً لاحقاً."
            )
        else:
            text = (
                f"تعذر تأكيد استجابة KD1S للطلب #{order_id}. لم يُخصم شيء من رصيدك، "
                "ولا تعاود الإرسال حتى تراجع الإدارة الطلب."
            )
        if result not in {"success", "insufficient"}:
            severity = (
                "error"
                if result in {"uncertain", "accepted_unbilled"}
                else "warning"
            )
            await emit_bot_alert(
                source="provider",
                severity=severity,
                component=f"member-order:{provider['id']}",
                title=f"مشكلة في خدمة رشق الأعضاء (الطلب #{order_id})",
                details=safe_text(provider_error, 300),
            )
        try:
            await update.callback_query.edit_message_text(
                text,
                reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
            )
        except Exception as exc:
            LOG.warning(
                "Could not update KD1S order result for order %s: %s",
                order_id,
                safe_text(exc, 160),
            )
        return

    try:
        external_id, _provider_response = await send_order_to_api(
            provider,
            {
                "order_id": order_id,
                "provider_service_id": service["provider_service_id"],
                "target_url": target_url,
                "quantity": quantity,
            },
        )
        async with database() as conn:
            await conn.execute(
                """
                UPDATE nabil_orders
                SET provider_order_id = %s, updated_at = NOW()
                WHERE id = %s AND provider_id = %s
                """,
                (str(external_id), order_id, provider["id"]),
            )
            await enqueue_live_mirror_purchase(conn, order_id)
    except Exception as exc:
        message = safe_provider_error(provider, exc)
        await emit_bot_alert(
            source="provider",
            severity="error" if not (
                isinstance(exc, ProviderError) and exc.definitive
            ) else "warning",
            component=f"service-order:{provider['id']}",
            title=(
                f"مشكلة في خدمة "
                f"{safe_text(service.get('custom_name') or service['provider_name'], 80)} "
                f"(الطلب #{order_id})"
            ),
            details=message,
        )
        if isinstance(exc, ProviderError) and exc.definitive:
            async with database() as conn:
                async with conn.transaction():
                    order = await fetch_one(
                        conn, "SELECT * FROM nabil_orders WHERE id = %s FOR UPDATE", (order_id,)
                    )
                    if order and Decimal(str(order["refunded_amount"])) == 0:
                        refund = money(
                            Decimal(str(order["sale_amount"]))
                            - Decimal(str(order["refunded_amount"]))
                        )
                        member = await fetch_one(
                            conn,
                            "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                            (user_id,),
                        )
                        if member and refund > 0:
                            balance_after = money(
                                Decimal(str(member["balance"])) + refund
                            )
                            await conn.execute(
                                "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                                (balance_after, user_id),
                            )
                            await conn.execute(
                                """
                                INSERT INTO nabil_ledger
                                  (member_id, order_id, entry_type, amount, balance_after, note)
                                VALUES (%s, %s, 'refund', %s, %s, %s)
                                """,
                                (
                                    user_id,
                                    order_id,
                                    refund,
                                    balance_after,
                                    "استرداد بعد رفض المزود",
                                ),
                            )
                            await enqueue_live_mirror_wallet_event(
                                conn,
                                member_id=user_id,
                                entry_type="refund",
                                amount=refund,
                                balance_after=balance_after,
                                note="استرداد بعد رفض المزود",
                                order_id=order_id,
                                event_key=f"refund:{order_id}:{uuid.uuid4().hex}",
                            )
                        await conn.execute(
                            """
                            UPDATE nabil_orders SET status = 'Canceled', refunded_amount = %s,
                              last_error = %s, updated_at = NOW() WHERE id = %s
                            """,
                            (refund, message, order_id),
                        )
            await update.callback_query.edit_message_text(
                order_status_message(
                    order_id, "Canceled", current_charge
                ),
                reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
            )
        else:
            async with database() as conn:
                await conn.execute(
                    "UPDATE nabil_orders SET last_error = %s, updated_at = NOW() WHERE id = %s",
                    (message, order_id),
                )
            notice = (
                f"تعذر تأكيد استجابة المزود للطلب #{order_id}. بقي المبلغ محجوزاً مؤقتاً "
                "حتى نتحقق من حالته، ولن نرسل الطلب مرة ثانية تلقائياً."
            )
            await update.callback_query.edit_message_text(
                notice,
                reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
            )
        return

    try:
        await update.callback_query.edit_message_text(
            order_success_message(order_id, current_charge),
            reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
        )
    except Exception as exc:
        LOG.warning(
            "Could not update order success message for order %s: %s",
            order_id,
            safe_text(exc, 160),
        )


async def apply_provider_status(
    order: dict, provider_status: str, remains: int | None
) -> tuple[Decimal, int, bool, bool]:
    normalized = normalize_provider_status(provider_status)
    if normalized is None:
        return Decimal("0"), 0, False, False

    quantity = int(order["quantity"])
    provider_rate = Decimal(str(order["provider_rate"]))
    remains_valid = True
    provider_cost = Decimal("0")
    if normalized == "Completed":
        provider_cost = money(provider_rate * Decimal(quantity) / Decimal("1000"))
    elif normalized == "Partial":
        remains_valid = remains is not None and 0 <= remains <= quantity
        if remains_valid:
            fulfilled = quantity - remains
            provider_cost = money(provider_rate * Decimal(fulfilled) / Decimal("1000"))

    async with database() as conn:
        async with conn.transaction():
            current = await fetch_one(
                conn, "SELECT * FROM nabil_orders WHERE id = %s FOR UPDATE", (order["id"],)
            )
            if not current:
                return Decimal("0"), 0, False, False
            if current["status"] not in {"Pending", "Processing"}:
                return Decimal("0"), 0, False, False
            if current["status"] == "Processing" and normalized == "Pending":
                return Decimal("0"), 0, False, False
            current_refund = money(current["refunded_amount"])
            if normalized == "Partial" and not remains_valid:
                await conn.execute(
                    """
                    UPDATE nabil_orders
                    SET status = CASE
                          WHEN status IN ('Pending', 'Processing') THEN status
                          ELSE 'Processing'
                        END,
                        last_error = %s, updated_at = NOW()
                    WHERE id = %s
                    """,
                    (
                        "بانتظار العدد المتبقي من المزود لإكمال احتساب الاسترداد.",
                        order["id"],
                    ),
                )
                return Decimal("0"), 0, False, False

            target_refund = current_refund
            if normalized in {"Partial", "Canceled"}:
                debit = await fetch_one(
                    conn,
                    """
                    SELECT COALESCE(SUM(-amount), 0) AS charged
                    FROM nabil_ledger
                    WHERE order_id = %s
                      AND entry_type IN ('order_debit', 'order_points_debit')
                    """,
                    (order["id"],),
                )
                charged_amount = min(
                    money(current["sale_amount"]),
                    money(debit["charged"] if debit else 0),
                )
                calculated_refund = refund_amount_target(
                    charged_amount, quantity, normalized, remains
                )
                if normalized == "Partial" and calculated_refund is None:
                    await conn.execute(
                        """
                        UPDATE nabil_orders
                        SET last_error = %s, updated_at = NOW()
                        WHERE id = %s
                        """,
                        (
                            "بانتظار بيانات صحيحة من المزود لاحتساب الاسترداد.",
                            order["id"],
                        ),
                    )
                    return Decimal("0"), 0, False, False
                if calculated_refund is not None:
                    target_refund = max(calculated_refund, current_refund)

            refund_delta = money(target_refund - current_refund)
            if refund_delta > 0:
                member = await fetch_one(
                    conn,
                    "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                    (current["member_id"],),
                )
                if not member:
                    await conn.execute(
                        """
                        UPDATE nabil_orders
                        SET last_error = %s, updated_at = NOW()
                        WHERE id = %s
                        """,
                        ("تعذر العثور على حساب العضو لإرجاع مبلغ الطلب.", order["id"]),
                    )
                    return Decimal("0"), 0, False, False
                new_balance = money(
                    Decimal(str(member["balance"])) + refund_delta
                )
                await conn.execute(
                    "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                    (new_balance, current["member_id"]),
                )
                await conn.execute(
                    """
                    INSERT INTO nabil_ledger
                      (member_id, order_id, entry_type, amount, balance_after, note)
                    VALUES (%s, %s, 'refund', %s, %s, %s)
                    """,
                    (
                        current["member_id"],
                        order["id"],
                        refund_delta,
                        new_balance,
                        f"تعديل رصيد بعد حالة {normalized}",
                    ),
                )
                await enqueue_live_mirror_wallet_event(
                    conn,
                    member_id=current["member_id"],
                    entry_type="refund",
                    amount=refund_delta,
                    balance_after=new_balance,
                    note=f"استرداد بعد تحديث حالة الطلب {order['id']}",
                    order_id=order["id"],
                    event_key=f"refund:{order['id']}:{uuid.uuid4().hex}",
                )
            await conn.execute(
                """
                UPDATE nabil_orders SET status = %s, refunded_amount = %s,
                  provider_cost = %s, last_error = NULL, updated_at = NOW()
                WHERE id = %s
                """,
                (normalized, target_refund, provider_cost, order["id"]),
            )
            status_changed = current["status"] != normalized
    return refund_delta, 0, False, status_changed


async def poll_active_orders(application: Application):
    while True:
        try:
            async with database() as conn:
                orders = await fetch_all(
                    conn,
                    """
                    SELECT o.*, p.name AS provider_name, p.domain, p.api_key_encrypted,
                           p.enabled AS provider_enabled
                    FROM nabil_orders o
                    JOIN nabil_providers p ON p.id = o.provider_id
                    WHERE o.provider_order_id IS NOT NULL
                      AND o.status IN ('Pending', 'Processing')
                    ORDER BY o.updated_at
                    LIMIT 80
                    """,
                )
            for order in orders:
                try:
                    try:
                        response = await provider_post(
                            provider_public(order),
                            {
                                "action": "status",
                                "order": str(order["provider_order_id"]),
                            },
                        )
                        if not isinstance(response, dict) or not response.get(
                            "status"
                        ):
                            raise ProviderError(
                                "لم يُرجع المزود حالة واضحة للطلب."
                            )
                        raw_provider_status = str(response["status"]).strip()
                        normalized_status = normalize_provider_status(
                            raw_provider_status
                        )
                        if normalized_status is None:
                            raise ProviderError(
                                "أعاد المزود حالة غير مدعومة: "
                                f"{safe_text(raw_provider_status, 60)}"
                            )
                    except ProviderError as exc:
                        error = safe_provider_error(order, exc)
                        try:
                            async with database() as conn:
                                async with conn.transaction():
                                    await conn.execute(
                                        """
                                        UPDATE nabil_orders SET last_error = %s
                                        WHERE id = %s
                                        """,
                                        (error, order["id"]),
                                    )
                                    await conn.execute(
                                        """
                                        UPDATE nabil_providers SET last_error = %s
                                        WHERE id = %s
                                        """,
                                        (error, order["provider_id"]),
                                    )
                        except Exception:
                            LOG.exception(
                                "Could not record provider error for order %s.",
                                order["id"],
                            )
                        raise
                    remains = parse_provider_remains(response.get("remains"))
                    refund_delta, _, _, status_changed = await apply_provider_status(
                        order, raw_provider_status, remains
                    )
                    status_label_changed = (
                        order_status_label(order["status"])
                        != order_status_label(normalized_status)
                    )
                    if normalized_status == "Completed" and status_changed:
                        await notify_order_completed(application.bot, order)
                    elif refund_delta > 0 or (
                        status_changed and status_label_changed
                    ):
                        total_refunded = money(
                            Decimal(str(order["refunded_amount"] or 0))
                            + refund_delta
                        )
                        text = order_status_message(
                            order["id"],
                            normalized_status,
                            total_refunded,
                        )
                        await application.bot.send_message(
                            chat_id=order["member_id"],
                            text=text,
                            reply_markup=back_keyboard(
                                "menu:home", "رجوع للقائمة"
                            ),
                        )
                except Exception as exc:
                    LOG.warning(
                        "Status poll failed for order %s (service %s): %s",
                        order["id"],
                        safe_text(order.get("service_name") or "غير معروفة", 80),
                        safe_text(exc),
                    )
                await asyncio.sleep(0.15)
        except asyncio.CancelledError:
            raise
        except Exception:
            LOG.exception("Order polling cycle failed.")
        await asyncio.sleep(POLL_INTERVAL_SECONDS)


async def admin_providers(query):
    async with database() as conn:
        provider = await fetch_one(
            conn,
            """
            SELECT p.id, p.name, p.domain, p.enabled, p.last_sync_at, p.last_error,
                   (SELECT s.provider_service_id
                    FROM nabil_services s
                    WHERE s.provider_id = p.id AND s.enabled = TRUE
                      AND COALESCE(s.category, '') <> 'مشاهدات وتفاعلات'
                    ORDER BY s.id DESC LIMIT 1) AS service_id,
                   (SELECT s.provider_name
                    FROM nabil_services s
                    WHERE s.provider_id = p.id AND s.enabled = TRUE
                      AND COALESCE(s.category, '') <> 'مشاهدات وتفاعلات'
                    ORDER BY s.id DESC LIMIT 1) AS service_name,
                   (SELECT s.base_rate
                    FROM nabil_services s
                    WHERE s.provider_id = p.id AND s.enabled = TRUE
                      AND COALESCE(s.category, '') <> 'مشاهدات وتفاعلات'
                    ORDER BY s.id DESC LIMIT 1) AS base_rate,
                   (SELECT s.markup_percent
                    FROM nabil_services s
                    WHERE s.provider_id = p.id AND s.enabled = TRUE
                      AND COALESCE(s.category, '') <> 'مشاهدات وتفاعلات'
                    ORDER BY s.id DESC LIMIT 1) AS markup_percent,
                   (SELECT s.min_quantity
                    FROM nabil_services s
                    WHERE s.provider_id = p.id AND s.enabled = TRUE
                      AND COALESCE(s.category, '') <> 'مشاهدات وتفاعلات'
                    ORDER BY s.id DESC LIMIT 1) AS min_quantity,
                   (SELECT s.max_quantity
                    FROM nabil_services s
                    WHERE s.provider_id = p.id AND s.enabled = TRUE
                      AND COALESCE(s.category, '') <> 'مشاهدات وتفاعلات'
                    ORDER BY s.id DESC LIMIT 1) AS max_quantity
            FROM nabil_providers p
            WHERE p.enabled = TRUE
              AND EXISTS (
                SELECT 1 FROM nabil_services s
                WHERE s.provider_id = p.id
                  AND COALESCE(s.category, '') <> 'مشاهدات وتفاعلات'
              )
            ORDER BY p.id DESC
            LIMIT 1
            """,
        )
    lines = [
        "<b>إعداد مزود رشق الأعضاء</b>",
        "يُستخدم مزود واحد وخدمة واحدة للطلبات الجديدة.",
    ]
    buttons = []
    if provider:
        health = (
            "آخر فحص فشل"
            if provider["last_error"]
            else "الاتصال مفحوص"
            if provider["last_sync_at"]
            else "لم يتم فحص الاتصال بعد"
        )
        lines.extend(
            [
                f"المزود: {safe_html(provider['name'], 100)}",
                f"رابط API: {safe_html(KD1S_API_URL, 180)}",
                f"الخدمة: {safe_html(provider['service_name'] or 'غير محددة', 100)}",
                f"آيدي الخدمة: {safe_html(provider['service_id'] or 'غير محدد', 100)}",
                f"الحالة: {'مفعّل' if provider['service_id'] else 'يحتاج إعداداً'}",
                f"الاتصال: {health}",
                "مفتاح API محفوظ مشفراً ولا يظهر في اللوحة.",
            ]
        )
        if provider["service_id"] and provider["base_rate"] is not None:
            try:
                member_price = rate(
                    Decimal(str(provider["base_rate"]))
                    * (
                        Decimal("1")
                        + Decimal(str(provider["markup_percent"] or 0))
                        / Decimal("100")
                    )
                )
                lines.extend(
                    [
                        f"السعر: {fmt_money(member_price)} لكل 1000",
                        f"الحدود: {provider['min_quantity']}–{provider['max_quantity']}",
                    ]
                )
            except (InvalidOperation, TypeError, ValueError):
                lines.append("تعذر احتساب سعر الخدمة؛ راجع إعداداتها.")
        if provider["last_error"]:
            lines.append(
                f"آخر خطأ: {safe_html(safe_provider_error(provider, provider['last_error']), 180)}"
            )
        buttons.append(
            [
                InlineKeyboardButton(
                    "فحص رصيد المزود",
                    callback_data=f"provider:balance:{provider['id']}",
                )
            ]
        )
        buttons.append(
            [
                InlineKeyboardButton(
                    "تجديد مفتاح API فقط",
                    callback_data="provider:key:renew",
                )
            ]
        )
    else:
        lines.append("لم يتم إعداد مزود رئيسي بعد.")
    buttons.extend(
        [
            [
                InlineKeyboardButton(
                    "إعداد أو تغيير المزود الرئيسي",
                    callback_data="admin:providers:setup",
                )
            ],
            [InlineKeyboardButton("رجوع للإعدادات", callback_data="admin:settings")],
        ]
    )
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def begin_provider_api_key_rekey(query, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.clear()
    if not query.message or query.message.chat.type != "private":
        await query.edit_message_text(
            "ابدأ تجديد مفتاح المزود من المحادثة الخاصة مع البوت.",
            reply_markup=back_keyboard("admin:providers", "رجوع للمزود"),
        )
        return
    async with database() as conn:
        provider = await fetch_one(
            conn,
            """
            SELECT id, name, domain FROM nabil_providers
            WHERE enabled = TRUE
              AND EXISTS (
                SELECT 1 FROM nabil_services s
                WHERE s.provider_id = nabil_providers.id
                  AND COALESCE(s.category, '') <> 'مشاهدات وتفاعلات'
              )
            ORDER BY id DESC
            LIMIT 1
            """,
        )
    if not provider:
        await query.edit_message_text(
            "لا يوجد مزود مفعّل لتجديد مفتاحه.",
            reply_markup=back_keyboard("admin:providers", "رجوع للمزود"),
        )
        return
    context.user_data.update(
        {
            "mode": "provider_api_key_rekey",
            "provider_api_key_rekey_id": int(provider["id"]),
            "provider_api_key_rekey_domain": provider["domain"],
        }
    )
    await query.edit_message_text(
        "أرسل مفتاح API الجديد في هذه المحادثة الخاصة. "
        "سيحذف البوت رسالتك فوراً ثم يتحقق من المفتاح ويحفظه مشفّراً.\n"
        "لن يتغير آيدي الخدمة أو سعرها أو حدودها.",
        reply_markup=back_keyboard("provider:key:renew:cancel", "إلغاء"),
    )


async def persist_provider_api_key(
    provider_id: int,
    expected_domain: str,
    encrypted_api_key: str,
    actor_id: int,
    sync_duration_ms: int,
    allow_pending_orders: bool = False,
) -> str:
    async with database() as conn:
        async with conn.transaction():
            provider = await fetch_one(
                conn,
                """
                SELECT id, name, domain FROM nabil_providers
                WHERE id = %s AND enabled = TRUE
                FOR UPDATE
                """,
                (provider_id,),
            )
            if not provider:
                return "missing"
            if provider["domain"] != expected_domain:
                return "changed"
            pending_order = await fetch_one(
                conn,
                """
                SELECT 1 AS pending FROM nabil_orders
                WHERE provider_id = %s
                  AND provider_order_id IS NOT NULL
                  AND status IN ('Pending', 'Processing')
                LIMIT 1
                """,
                (provider_id,),
            )
            if pending_order and not allow_pending_orders:
                return "pending"
            await conn.execute(
                """
                UPDATE nabil_providers
                SET api_key_encrypted = %s,
                    last_sync_at = NOW(),
                    last_error = NULL,
                    last_sync_duration_ms = %s
                WHERE id = %s AND domain = %s
                """,
                (
                    encrypted_api_key,
                    sync_duration_ms,
                    provider_id,
                    expected_domain,
                ),
            )
            await conn.execute(
                """
                UPDATE nabil_orders
                SET last_error = NULL, updated_at = NOW()
                WHERE provider_id = %s
                  AND provider_order_id IS NOT NULL
                  AND status IN ('Pending', 'Processing')
                """,
                (provider_id,),
            )
            await insert_admin_audit(
                conn,
                actor_id,
                "تجديد مفتاح API للمزود",
                provider_id,
                "تم التحقق من المفتاح الجديد وحفظه مشفّراً.",
            )
    return "saved"


async def finish_provider_api_key_rekey(
    query, context: ContextTypes.DEFAULT_TYPE, actor_id: int
):
    try:
        provider_id = int(context.user_data["provider_api_key_rekey_id"])
        expected_domain = str(context.user_data["provider_api_key_rekey_domain"])
        encrypted_api_key = str(
            context.user_data["provider_api_key_rekey_encrypted"]
        )
        sync_duration_ms = int(
            context.user_data["provider_api_key_rekey_duration_ms"]
        )
    except (KeyError, TypeError, ValueError):
        context.user_data.clear()
        await query.edit_message_text(
            "انتهت جلسة تجديد المفتاح. ابدأ العملية من جديد.",
            reply_markup=back_keyboard("admin:providers", "رجوع للمزود"),
        )
        return

    status = await persist_provider_api_key(
        provider_id,
        expected_domain,
        encrypted_api_key,
        actor_id,
        sync_duration_ms,
        allow_pending_orders=True,
    )
    context.user_data.clear()
    if status == "saved":
        message = (
            "تم التحقق من مفتاح المزود وحفظه مشفّراً. "
            "سيستأنف البوت فحص الطلبات المفتوحة في دورة الفحص التالية."
        )
    elif status == "missing":
        message = "لم يعد المزود مفعّلاً؛ لم يتم تغيير أي مفتاح."
    else:
        message = "تغير إعداد المزود أثناء العملية؛ لم يتم حفظ المفتاح."
    await query.edit_message_text(
        message,
        reply_markup=back_keyboard("admin:providers", "رجوع للمزود"),
    )


async def show_provider(query, provider_id: int):
    await admin_providers(query)


async def check_provider_balance(query, provider_id: int):
    async with database() as conn:
        provider = await fetch_one(
            conn,
            "SELECT * FROM nabil_providers WHERE id = %s AND enabled = TRUE",
            (provider_id,),
        )
    if not provider:
        await query.edit_message_text(
            "المزود غير موجود.",
            reply_markup=back_keyboard("admin:providers", "رجوع للمزودين"),
        )
        return

    try:
        response = await provider_post(
            {**provider_public(provider), "domain": KD1S_API_URL},
            {"action": "balance"},
        )
        balance, currency = parse_provider_balance(response)
        balance_text = format(balance, "f")
        await log_admin_action(
            query.from_user.id,
            "فحص رصيد مزود",
            provider_id,
            f"{balance_text} {currency}",
        )
        await query.edit_message_text(
            f"<b>رصيد المزود</b>\n"
            f"المزود: {safe_html(provider['name'], 100)}\n"
            f"الرصيد الحالي: <code>{safe_html(balance_text, 80)} "
            f"{safe_html(currency, 24)}</code>",
            reply_markup=InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            "إعادة فحص الرصيد",
                            callback_data=f"provider:balance:{provider_id}",
                        )
                    ],
                    [
                        InlineKeyboardButton(
                            "رجوع لتفاصيل المزود",
                            callback_data=f"provider:view:{provider_id}",
                        )
                    ],
                ]
            ),
            parse_mode=ParseMode.HTML,
        )
    except Exception as exc:
        error = safe_provider_error(provider, exc)
        await log_admin_action(
            query.from_user.id,
            "فشل فحص رصيد مزود",
            provider_id,
            error,
        )
        await emit_bot_alert(
            source="provider",
            severity="error",
            component=f"provider-health:{provider_id}",
            fingerprint=f"health:provider:{provider_id}",
            title=f"فشل فحص اتصال المزود: {safe_text(provider['name'], 100)}",
            details=f"تعذر طلب رصيد API: {error}",
        )
        await query.edit_message_text(
            f"تعذر جلب رصيد {safe_html(provider['name'], 100)}:\n"
            f"{safe_html(error, 220)}",
            reply_markup=InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            "إعادة فحص الرصيد",
                            callback_data=f"provider:balance:{provider_id}",
                        )
                    ],
                    [
                        InlineKeyboardButton(
                            "رجوع لتفاصيل المزود",
                            callback_data=f"provider:view:{provider_id}",
                        )
                    ],
                ]
            ),
            parse_mode=ParseMode.HTML,
        )


async def list_admin_services(query, page: int, service_group: str | None = None):
    offset = max(0, page) * PAGE_SIZE
    group_filter = ""
    if service_group == "engagement":
        group_filter = """
            AND (
              s.category ILIKE ANY(ARRAY['%%view%%', '%%like%%', '%%comment%%', '%%reaction%%', '%%مشاهد%%', '%%تفاعل%%', '%%اعجاب%%', '%%إعجاب%%'])
              OR COALESCE(s.custom_name, s.provider_name) ILIKE ANY(ARRAY['%%view%%', '%%like%%', '%%comment%%', '%%reaction%%', '%%مشاهد%%', '%%تفاعل%%', '%%اعجاب%%', '%%إعجاب%%'])
              OR s.description ILIKE ANY(ARRAY['%%view%%', '%%like%%', '%%comment%%', '%%reaction%%', '%%مشاهد%%', '%%تفاعل%%', '%%اعجاب%%', '%%إعجاب%%'])
            )
        """
    async with database() as conn:
        rows = await fetch_all(
            conn,
            f"""
            SELECT s.id, COALESCE(NULLIF(s.custom_name, ''), s.provider_name) AS name,
                   s.base_rate, s.markup_percent, s.enabled, s.category,
                   p.name AS provider_name,
                   p.enabled AS provider_enabled
            FROM nabil_services s JOIN nabil_providers p ON p.id = s.provider_id
            WHERE TRUE
            {group_filter}
            ORDER BY p.name, s.provider_name
            LIMIT %s OFFSET %s
            """,
            (PAGE_SIZE + 1, offset),
        )
    has_next = len(rows) > PAGE_SIZE
    rows = rows[:PAGE_SIZE]
    if not rows:
        empty_text = (
            "لا توجد خدمات مشاهدات أو تفاعلات حالياً."
            if service_group == "engagement"
            else "لا توجد خدمات مستوردة."
        )
        empty_buttons = []
        if service_group == "engagement" and is_owner(query.from_user.id):
            empty_buttons.append(
                [
                    InlineKeyboardButton(
                        "إضافة خدمة", callback_data="admin:engagement:add"
                    )
                ]
            )
        empty_buttons.append(
            [
                InlineKeyboardButton(
                    "رجوع", callback_data=admin_parent_target(query.from_user.id)
                )
            ]
        )
        await query.edit_message_text(
            empty_text,
            reply_markup=InlineKeyboardMarkup(empty_buttons),
        )
        return
    buttons = []
    section_title = (
        "خدمات المشاهدات والتفاعلات"
        if service_group == "engagement"
        else "الخدمات"
    )
    lines = [f"إدارة {section_title} — اضغط خدمة للتعديل:"]
    if service_group == "engagement" and is_owner(query.from_user.id):
        buttons.append(
            [
                InlineKeyboardButton(
                    "إضافة خدمة جديدة", callback_data="admin:engagement:add"
                )
            ]
        )
    for row in rows:
        state = "مفعّلة" if row["enabled"] and row["provider_enabled"] else "متوقفة"
        lines.append(
            f"\n#{row['id']} {safe_text(row['name'], 70)}\n"
            f"المزود: {safe_text(row['provider_name'], 45)} | "
            f"الربح: {row['markup_percent']}% | {state}"
        )
        buttons.append(
            [InlineKeyboardButton(f"#{row['id']} {safe_text(row['name'], 42)}", callback_data=f"service:view:{row['id']}")]
        )
    nav = []
    if page > 0:
        prefix = (
            f"admin:services:{service_group}"
            if service_group
            else "admin:services"
        )
        nav.append(InlineKeyboardButton("السابق", callback_data=f"{prefix}:{page - 1}"))
    if has_next:
        prefix = (
            f"admin:services:{service_group}"
            if service_group
            else "admin:services"
        )
        nav.append(InlineKeyboardButton("التالي", callback_data=f"{prefix}:{page + 1}"))
    if nav:
        buttons.append(nav)
    buttons.append(
        [InlineKeyboardButton("رجوع", callback_data=admin_parent_target(query.from_user.id))]
    )
    await query.edit_message_text("\n".join(lines), reply_markup=InlineKeyboardMarkup(buttons))


async def save_engagement_service(
    update: Update, context: ContextTypes.DEFAULT_TYPE
):
    message = update.effective_message
    actor = update.effective_user
    try:
        name = str(context.user_data["engagement_service_name"]).strip()
        domain = provider_api_url(
            str(context.user_data["engagement_service_domain"])
        )
        encrypted_api_key = str(
            context.user_data["engagement_service_api_key_encrypted"]
        )
        provider_service_id = str(
            context.user_data["engagement_service_id"]
        ).strip()
        sale_price = parse_manual_service_rate(
            str(context.user_data["engagement_service_price"])
        )
        min_quantity = parse_service_quantity(
            str(context.user_data["engagement_service_min"])
        )
        max_quantity = parse_service_quantity(
            str(context.user_data["engagement_service_max"])
        )
        description = " ".join(
            str(context.user_data["engagement_service_description"]).split()
        )
        if (
            not message
            or not actor
            or not name
            or len(name) > 120
            or not encrypted_api_key
            or not provider_service_id
            or len(provider_service_id) > 120
            or any(
                char.isspace() or ord(char) < 32
                for char in provider_service_id
            )
            or not description
            or len(description) > 500
            or max_quantity < min_quantity
        ):
            raise ValueError("بيانات الخدمة غير مكتملة أو غير صالحة.")
    except (KeyError, InvalidOperation, TypeError, ValueError) as exc:
        if message:
            await message.reply_text(
                f"انتهت جلسة الإضافة أو بياناتها غير صالحة: {safe_text(exc, 180)}",
                reply_markup=back_keyboard(
                    "admin:services:engagement:0", "رجوع للقسم"
                ),
            )
        context.user_data.clear()
        return

    provider_probe = {
        "domain": domain,
        "api_key_encrypted": encrypted_api_key,
    }
    started_at = asyncio.get_running_loop().time()
    try:
        response = await provider_post(provider_probe, {"action": "balance"})
        parse_provider_balance(response)
    except Exception as exc:
        error = safe_provider_error(provider_probe, exc)
        await message.reply_text(
            "تعذر التحقق من رابط API ومفتاحه. لم تُحفظ الخدمة.\n"
            f"{safe_text(error, 180)}\n"
            "تأكد أن المزود يدعم واجهة SMM Panel API v2.",
            reply_markup=back_keyboard(
                "admin:services:engagement:0", "إلغاء الإضافة"
            ),
        )
        context.user_data.clear()
        return

    sync_duration_ms = max(
        0, int((asyncio.get_running_loop().time() - started_at) * 1000)
    )
    hostname = urlparse(domain).hostname or "provider"
    provider_name = safe_text(f"مزود {hostname}", 120)
    try:
        async with database() as conn:
            async with conn.transaction():
                provider = await fetch_one(
                    conn,
                    """
                    INSERT INTO nabil_providers
                      (name, domain, api_key_encrypted, enabled, last_sync_at,
                       last_error, last_sync_duration_ms)
                    VALUES (%s, %s, %s, TRUE, NOW(), NULL, %s)
                    RETURNING id
                    """,
                    (
                        provider_name,
                        domain,
                        encrypted_api_key,
                        sync_duration_ms,
                    ),
                )
                service = await fetch_one(
                    conn,
                    """
                    INSERT INTO nabil_services
                      (provider_id, provider_service_id, provider_name,
                       custom_name, description, category, base_rate,
                       min_quantity, max_quantity, enabled, markup_percent)
                    VALUES (%s, %s, %s, %s, %s, 'مشاهدات وتفاعلات',
                            %s, %s, %s, TRUE, 0)
                    RETURNING id
                    """,
                    (
                        provider["id"],
                        provider_service_id,
                        name,
                        name,
                        description,
                        sale_price,
                        min_quantity,
                        max_quantity,
                    ),
                )
                await insert_admin_audit(
                    conn,
                    actor.id,
                    "إضافة خدمة مشاهدات وتفاعلات",
                    service["id"],
                    f"الخدمة: {safe_text(name, 80)} | "
                    f"ID المزود: {safe_text(provider_service_id, 60)} | "
                    f"سعر البيع لكل 1000: {sale_price} IQD | "
                    f"الحدود: {min_quantity}–{max_quantity}",
                )
    except Exception:
        LOG.error("Could not save manually configured engagement service.")
        await message.reply_text(
            "تم التحقق من اتصال المزود، لكن تعذر حفظ الخدمة. أعد المحاولة.",
            reply_markup=back_keyboard(
                "admin:services:engagement:0", "رجوع للقسم"
            ),
        )
        context.user_data.clear()
        return

    context.user_data.clear()
    await message.reply_text(
        "تمت إضافة الخدمة وتفعيلها.\n"
        f"الخدمة: {safe_text(name, 120)}\n"
        f"سعر البيع: {fmt_money(sale_price)} لكل 1000\n"
        f"الحدود: {min_quantity}–{max_quantity}\n"
        "مفتاح API محفوظ مشفّراً، وسيظهر للمستخدمين وصف الخدمة فقط.",
        reply_markup=InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton(
                        "إضافة خدمة أخرى", callback_data="admin:engagement:add"
                    )
                ],
                [
                    InlineKeyboardButton(
                        "إدارة المشاهدات والتفاعلات",
                        callback_data="admin:services:engagement:0",
                    )
                ],
            ]
        ),
    )


def member_service_category(category: str | None) -> str:
    value = str(category or "").strip()
    member_terms = (
        "follow",
        "follower",
        "subscriber",
        "member",
        "متابع",
        "مشترك",
        "عضو",
        "رشق",
    )
    if any(term in value.casefold() for term in member_terms):
        return value[:120]
    if not value:
        return "رشق الأعضاء"
    return f"{value[:100]} | رشق الأعضاء"


async def setup_member_service_from_credentials(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    provider_service_id: str,
    base_rate: Decimal,
    min_quantity: int,
    max_quantity: int,
    allow_pending_rekey: bool = False,
):
    message = update.effective_message
    actor = update.effective_user
    domain = KD1S_API_URL
    encrypted_api_key = context.user_data.get("member_service_api_key_encrypted")
    if not message or not actor or not domain or not encrypted_api_key:
        context.user_data.clear()
        if message:
            await message.reply_text(
                "انتهت جلسة الإعداد. ابدأ من قسم رشق الأعضاء.",
                reply_markup=back_keyboard(
                    "admin:providers", "رجوع للمزود الرئيسي"
                ),
            )
        return

    try:
        base_rate = parse_manual_service_rate(str(base_rate))
        min_quantity = parse_service_quantity(str(min_quantity))
        max_quantity = parse_service_quantity(str(max_quantity))
        if max_quantity < min_quantity:
            raise ValueError("الحد الأعلى يجب أن يكون أكبر من الحد الأدنى أو مساوياً له.")
    except ValueError as exc:
        context.user_data.clear()
        await message.reply_text(
            f"بيانات الخدمة غير صالحة: {safe_text(exc, 180)}",
            reply_markup=back_keyboard(
                "admin:providers:setup", "إعادة الإعداد"
            ),
        )
        return

    provider_probe = {
        "domain": domain,
        "api_key_encrypted": encrypted_api_key,
    }
    started_at = asyncio.get_running_loop().time()
    try:
        response = await provider_post(provider_probe, {"action": "balance"})
        parse_provider_balance(response)
    except Exception as exc:
        error = safe_provider_error(provider_probe, exc)
        await message.reply_text(
            f"تعذر التحقق من رابط API ومفتاحه: {error}\n"
            "استخدم رابطاً ومفتاحاً صالحين. لم يتم تحميل قائمة الخدمات.",
            reply_markup=back_keyboard(
                "admin:providers:setup", "إعادة الإعداد"
            ),
        )
        return

    selected_service = {
        "provider_service_id": provider_service_id,
        "provider_name": f"رشق الأعضاء {provider_service_id}",
        "description": "خدمة رشق الأعضاء",
        "category": "رشق الأعضاء",
        "base_rate": base_rate,
        "min_quantity": min_quantity,
        "max_quantity": max_quantity,
    }

    api_url = provider_api_url(domain)
    normalized_category = member_service_category(
        selected_service.get("category")
    )
    duration_ms = max(
        0, int((asyncio.get_running_loop().time() - started_at) * 1000)
    )
    provider_id = None
    provider_name = ""
    service_row = None
    try:
        async with database() as conn:
            async with conn.transaction():
                providers = await fetch_all(
                    conn,
                    """
                    SELECT p.id, p.name, p.domain
                    FROM nabil_providers p
                    WHERE EXISTS (
                      SELECT 1 FROM nabil_services s
                      WHERE s.provider_id = p.id
                        AND COALESCE(s.category, '') <> 'مشاهدات وتفاعلات'
                    )
                    ORDER BY p.id DESC
                    FOR UPDATE
                    """,
                )
                matches = []
                for provider in providers:
                    try:
                        if provider_api_url(provider["domain"]) == api_url:
                            matches.append(provider)
                    except ValueError:
                        continue
                if matches:
                    candidate = matches[0]
                    pending_order = await fetch_one(
                        conn,
                        """
                        SELECT 1 AS pending
                        FROM nabil_orders
                        WHERE provider_id = %s
                          AND provider_order_id IS NOT NULL
                          AND status IN ('Pending', 'Processing')
                        LIMIT 1
                        """,
                        (candidate["id"],),
                    )
                    if pending_order and not allow_pending_rekey:
                        context.user_data.update(
                            {
                                "mode": None,
                                "member_service_rekey_provider_id": candidate["id"],
                                "member_service_rekey_service_id": provider_service_id,
                                "member_service_rekey_rate": str(base_rate),
                                "member_service_rekey_min": min_quantity,
                                "member_service_rekey_max": max_quantity,
                            }
                        )
                        await message.reply_text(
                            "يوجد طلب مفتوح مرتبط بهذا المزود. لتجديد المفتاح "
                            "ومواصلة متابعة الطلب، أكّد أن المفتاح الجديد يعود "
                            "لحساب المزود نفسه. إذا كان لحساب مختلف، ألغِ العملية.",
                            reply_markup=InlineKeyboardMarkup(
                                [
                                    [
                                        InlineKeyboardButton(
                                            "نعم، الحساب نفسه",
                                            callback_data="provider:rekey:confirm",
                                        )
                                    ],
                                    [
                                        InlineKeyboardButton(
                                            "إلغاء",
                                            callback_data="provider:rekey:cancel",
                                        )
                                    ],
                                ]
                            ),
                        )
                        return
                    expected_provider_id = context.user_data.get(
                        "member_service_rekey_provider_id"
                    )
                    if allow_pending_rekey and int(expected_provider_id or 0) != int(
                        candidate["id"]
                    ):
                        context.user_data.clear()
                        await message.reply_text(
                            "تغير المزود أثناء الإعداد. أعد محاولة إعداد المفتاح.",
                            reply_markup=back_keyboard(
                                "admin:providers:setup", "إعادة الإعداد"
                            ),
                        )
                        return
                    provider_id = candidate["id"]
                    provider_name = candidate["name"]
                    await conn.execute(
                        """
                        UPDATE nabil_providers
                        SET domain = %s, api_key_encrypted = %s, enabled = TRUE,
                            last_sync_at = NOW(), last_error = NULL,
                            last_sync_duration_ms = %s
                        WHERE id = %s
                        """,
                        (
                            domain.rstrip("/"),
                            encrypted_api_key,
                            duration_ms,
                            provider_id,
                        ),
                    )
                if allow_pending_rekey and provider_id is None:
                    context.user_data.clear()
                    await message.reply_text(
                        "لم أعد أجد المزود المرتبط بالطلب المفتوح. أعد إعداد المزود.",
                        reply_markup=back_keyboard(
                            "admin:providers:setup", "إعادة الإعداد"
                        ),
                    )
                    return
                if provider_id is None:
                    hostname = urlparse(domain).hostname or "provider"
                    provider_name = safe_text(
                        f"رشق {hostname} {provider_service_id}", 120
                    )
                    provider = await fetch_one(
                        conn,
                        """
                        INSERT INTO nabil_providers
                          (name, domain, api_key_encrypted, enabled,
                           last_sync_at, last_error, last_sync_duration_ms)
                        VALUES (%s, %s, %s, TRUE, NOW(), NULL, %s)
                        RETURNING id
                        """,
                        (
                            provider_name,
                            domain.rstrip("/"),
                            encrypted_api_key,
                            duration_ms,
                        ),
                    )
                    provider_id = provider["id"]

                service_row = await fetch_one(
                    conn,
                    """
                    INSERT INTO nabil_services
                      (provider_id, provider_service_id, provider_name,
                       description, category, base_rate, min_quantity,
                       max_quantity, enabled, markup_percent)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, TRUE, 0)
                    ON CONFLICT (provider_id, provider_service_id)
                    DO UPDATE SET
                      provider_name = EXCLUDED.provider_name,
                      description = EXCLUDED.description,
                      category = EXCLUDED.category,
                      base_rate = EXCLUDED.base_rate,
                      min_quantity = EXCLUDED.min_quantity,
                      max_quantity = EXCLUDED.max_quantity,
                      enabled = TRUE,
                      updated_at = NOW()
                    RETURNING id, markup_percent
                    """,
                    (
                        provider_id,
                        selected_service["provider_service_id"],
                        selected_service["provider_name"],
                        selected_service["description"],
                        normalized_category,
                        selected_service["base_rate"],
                        selected_service["min_quantity"],
                        selected_service["max_quantity"],
                    ),
                )
                # Keep unrelated providers and service groups unchanged.
                await conn.execute(
                    "UPDATE nabil_providers SET enabled = TRUE WHERE id = %s",
                    (provider_id,),
                )
                await conn.execute(
                    """
                    UPDATE nabil_services
                    SET enabled = FALSE, updated_at = NOW()
                    WHERE id <> %s
                      AND (
                        category ILIKE ANY(ARRAY[
                          '%%follow%%', '%%follower%%', '%%subscriber%%',
                          '%%member%%', '%%متابع%%', '%%مشترك%%', '%%عضو%%', '%%رشق%%'
                        ])
                        OR COALESCE(NULLIF(custom_name, ''), provider_name)
                          ILIKE ANY(ARRAY[
                            '%%follow%%', '%%follower%%', '%%subscriber%%',
                            '%%member%%', '%%متابع%%', '%%مشترك%%', '%%عضو%%', '%%رشق%%'
                          ])
                        OR description ILIKE ANY(ARRAY[
                          '%%follow%%', '%%follower%%', '%%subscriber%%',
                          '%%member%%', '%%متابع%%', '%%مشترك%%', '%%عضو%%', '%%رشق%%'
                        ])
                      )
                    """,
                    (service_row["id"],),
                )
                await conn.execute(
                    """
                    UPDATE nabil_services
                    SET enabled = TRUE, updated_at = NOW()
                    WHERE id = %s AND provider_id = %s
                    """,
                    (service_row["id"], provider_id),
                )
                await insert_admin_audit(
                    conn,
                    actor.id,
                    "إعداد خدمة رشق الأعضاء",
                    service_row["id"],
                    f"المزود: {provider_name} | "
                    f"ID الخدمة: {selected_service['provider_service_id']} | "
                    f"السعر الأساسي: {selected_service['base_rate']} | "
                    "هامش الربح الافتراضي للخدمة الجديدة: 0%",
                )
    except Exception as exc:
        LOG.error(
            "Could not save member-service setup: %s",
            safe_text(exc, 240),
        )
        await message.reply_text(
            "تم التحقق من المزود، لكن تعذر حفظ الخدمة. أعد المحاولة أو راجع سجل الأدمن.",
            reply_markup=back_keyboard(
                "admin:providers:setup", "إعادة الإعداد"
            ),
        )
        return

    context.user_data.clear()
    selected_for_price = {
        **selected_service,
        "markup_percent": service_row["markup_percent"],
    }
    await message.reply_text(
        "تم حفظ بيانات المزود وتفعيل خدمة رشق الأعضاء.\n"
        f"الخدمة: {safe_text(selected_service['provider_name'], 100)}\n"
        f"ID الخدمة: {safe_text(selected_service['provider_service_id'], 100)}\n"
        f"سعر المزود لكل 1000: {fmt_money(selected_service['base_rate'])}\n"
        f"الحدود: {selected_service['min_quantity']}–{selected_service['max_quantity']}\n"
        f"سعر العضو: {fmt_money(service_price(selected_for_price))} لكل 1000.\n"
        "التكلفة تخصم مباشرة من رصيد IQD الموحد.",
        reply_markup=InlineKeyboardMarkup(
            [
                [InlineKeyboardButton("إعداد المزود الرئيسي", callback_data="admin:providers")],
                [InlineKeyboardButton("لوحة الأدمن", callback_data="admin:home")],
            ]
        ),
    )


async def show_admin_service(query, service_id: int):
    async with database() as conn:
        row = await fetch_one(
            conn,
            """
            SELECT s.*, p.name AS provider_name, p.enabled AS provider_enabled
            FROM nabil_services s JOIN nabil_providers p ON p.id = s.provider_id
            WHERE s.id = %s
            """,
            (service_id,),
        )
    if not row:
        await query.edit_message_text(
            "الخدمة غير موجودة.",
            reply_markup=back_keyboard("admin:services:0", "رجوع للخدمات"),
        )
        return
    name = row.get("custom_name") or row["provider_name"]
    is_engagement_service = row.get("category") == "مشاهدات وتفاعلات"
    status_label = (
        "أرشفة الخدمة" if row["enabled"] else "تشغيل الخدمة"
    ) if is_engagement_service else (
        "إيقاف الخدمة" if row["enabled"] else "تفعيل الخدمة"
    )
    buttons = [
        [InlineKeyboardButton("تعديل الاسم", callback_data=f"service:name:{service_id}")],
        [InlineKeyboardButton("تعديل نسبة الربح", callback_data=f"service:markup:{service_id}")],
        [InlineKeyboardButton(
            status_label,
            callback_data=f"service:toggle:{service_id}",
        )],
    ]
    if is_engagement_service:
        buttons.append(
            [
                InlineKeyboardButton(
                    "حذف الخدمة", callback_data=f"service:delete:{service_id}"
                )
            ]
        )
    buttons.append(
        [
            InlineKeyboardButton(
                "رجوع للخدمات",
                callback_data=(
                    "admin:services:engagement:0"
                    if is_engagement_service
                    else "admin:services:0"
                ),
            )
        ]
    )
    price_label = (
        "سعر الخدمة لكل 1000"
        if is_engagement_service
        else "سعر المزود لكل 1000"
    )
    await query.edit_message_text(
        f"<b>{safe_html(name, 120)}</b>\nالمزود: {safe_html(row['provider_name'], 80)}\n"
        f"معرّف المزود: <code>{safe_html(row['provider_service_id'], 80)}</code>\n"
        f"{price_label}: {fmt_money(row['base_rate'])}\n"
        f"نسبة الربح: {row['markup_percent']}%\n"
        f"سعر العضو لكل 1000: {fmt_money(service_price(row))}\n"
        f"الحدود: {row['min_quantity']}–{row['max_quantity']}\n"
        f"الوصف: {safe_html(row.get('description') or '—', 240)}\n"
        f"الحالة: {'مفعّلة' if row['enabled'] and row['provider_enabled'] else 'متوقفة'}",
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def admin_report(query):
    async with database() as conn:
        stats = await fetch_one(
            conn,
            """
            SELECT COUNT(*) AS orders,
              COUNT(*) FILTER (WHERE status IN ('Pending', 'Processing')) AS open_orders,
              COUNT(*) FILTER (
                WHERE created_at >= date_trunc('day', NOW())
              ) AS today_orders,
              COUNT(*) FILTER (
                WHERE created_at >= date_trunc('day', NOW())
                  AND status IN ('Pending', 'Processing')
              ) AS today_open_orders,
              COUNT(*) FILTER (
                WHERE created_at >= date_trunc('day', NOW())
                  AND status IN ('Failed', 'Canceled')
              ) AS today_stopped_orders,
              COALESCE(SUM(sale_amount - refunded_amount), 0) AS net_sales,
              COALESCE(
                SUM(sale_amount - refunded_amount)
                  FILTER (WHERE created_at >= date_trunc('day', NOW())),
                0
              ) AS today_net_sales,
              COALESCE(SUM(provider_cost), 0) AS provider_cost,
              COALESCE(SUM(sale_amount - refunded_amount - provider_cost)
                FILTER (WHERE status IN ('Completed', 'Partial', 'Canceled')), 0) AS profit,
              COALESCE(
                SUM(sale_amount - refunded_amount - provider_cost)
                  FILTER (
                    WHERE created_at >= date_trunc('day', NOW())
                      AND status IN ('Completed', 'Partial', 'Canceled')
                  ),
                0
              ) AS today_profit
            FROM nabil_orders
            """,
        )
        member_stats = await fetch_one(
            conn,
            """
            SELECT (SELECT COUNT(*) FROM nabil_members) AS members,
                   (SELECT COUNT(*) FROM nabil_members
                    WHERE created_at >= date_trunc('day', NOW())) AS new_members,
                   (SELECT COUNT(*) FROM nabil_bot_user_state WHERE is_banned = TRUE) AS banned,
                   (SELECT COALESCE(SUM(balance), 0) FROM nabil_members) AS wallet_total,
                   (SELECT COALESCE(SUM(referrals_count), 0) FROM nabil_bot_user_state) AS referrals
            """,
        )
        recent = await fetch_all(
            conn,
            """
            SELECT id, member_id, service_name, status, sale_amount, created_at
            FROM nabil_orders ORDER BY id DESC LIMIT 8
            """,
        )
    lines = [
        "<b>ملخص الإدارة</b>",
        "\n<b>اليوم</b>",
        f"الطلبات: {stats['today_orders']} · المفتوحة: {stats['today_open_orders']}",
        f"المتوقفة/الملغاة: {stats['today_stopped_orders']}",
        f"صافي المبيعات: {fmt_money(stats['today_net_sales'])}",
        f"الربح المسجل: {fmt_money(stats['today_profit'])}",
        f"الأعضاء الجدد: {member_stats['new_members']}",
        "\n<b>الإجمالي</b>",
        f"عدد الطلبات: {stats['orders']}",
        f"الطلبات المفتوحة: {stats['open_orders']}",
        f"صافي المبيعات: {fmt_money(stats['net_sales'])}",
        f"تكلفة المزودين: {fmt_money(stats['provider_cost'])}",
        f"الربح المسجل: {fmt_money(stats['profit'])}",
        f"\nالأعضاء: {member_stats['members']} · المحظورون: {member_stats['banned']}",
        f"إجمالي أرصدة الأعضاء: {fmt_money(member_stats['wallet_total'])} · "
        f"الإحالات: {member_stats['referrals']}",
        "\nآخر الطلبات:",
    ]
    for row in recent:
        lines.append(
            f"#{row['id']} · العضو {row['member_id']} · {safe_html(row['service_name'], 45)} · "
            f"{safe_text(row['status'], 20)} · {fmt_money(row['sale_amount'])}"
        )
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(
            [[InlineKeyboardButton("رجوع للوحة", callback_data="admin:home")]]
        ),
        parse_mode=ParseMode.HTML,
    )


async def admin_audit_log(query):
    async with database() as conn:
        rows = await fetch_all(
            conn,
            """
            SELECT id, actor_id, action, target_id, details, created_at
            FROM nabil_admin_audit
            ORDER BY id DESC
            LIMIT 10
            """,
        )
    if not rows:
        text = "<b>سجل عمليات الأدمن</b>\n\nماكو عمليات مسجلة إلى الآن."
    else:
        lines = ["<b>سجل عمليات الأدمن</b> · آخر 10 عمليات"]
        for row in rows:
            timestamp = row["created_at"].strftime("%Y-%m-%d %H:%M")
            target = (
                f" · الهدف <code>{row['target_id']}</code>"
                if row["target_id"] is not None
                else ""
            )
            details = safe_html(row["details"] or "", 150)
            lines.append(
                f"\n<b>{safe_html(row['action'], 80)}</b> · {timestamp}"
                f"\nبواسطة <code>{row['actor_id']}</code>{target}"
                + (f"\n{details}" if details else "")
            )
        text = "\n".join(lines)
    await query.edit_message_text(
        text,
        reply_markup=InlineKeyboardMarkup(
            [
                [InlineKeyboardButton("تحديث السجل", callback_data="admin:audit")],
                [InlineKeyboardButton("رجوع للإعدادات", callback_data="admin:settings")],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


async def admin_dashboard_text() -> str:
    return (
        "<b>• أهلاً بك في لوحة الأدمن الخاصة بالبوت 🤖</b>\n"
        "\n– يمكنك التحكم بالبوت الخاص بك من هنا\n\n"
        "════════════════════════════════"
    )


async def show_admin_home(query):
    await query.edit_message_text(
        await admin_dashboard_text(),
        reply_markup=await current_admin_keyboard(query.from_user.id),
        parse_mode=ParseMode.HTML,
    )


async def admin_alerts(query, state: str = "active", page: int = 0):
    state = "resolved" if state == "resolved" else "active"
    page = max(0, page)
    async with database() as conn:
        count_row = await fetch_one(
            conn,
            "SELECT COUNT(*) AS total FROM nabil_bot_alerts WHERE state = %s",
            (state,),
        )
        rows = await fetch_all(
            conn,
            """
            SELECT id, title, details
            FROM nabil_bot_alerts
            WHERE state = %s
            ORDER BY last_seen_at DESC, id DESC
            LIMIT %s OFFSET %s
            """,
            (state, PAGE_SIZE + 1, page * PAGE_SIZE),
        )
    total = int(count_row["total"] if count_row else 0)
    has_next = len(rows) > PAGE_SIZE
    rows = rows[:PAGE_SIZE]
    state_label = "النشطة" if state == "active" else "المعالجة"
    lines = [
        "<b>إنذارات البوت</b>",
        f"الإنذارات {state_label}: {total}",
    ]
    if not rows:
        lines.append(
            "\nلا توجد إنذارات هنا."
            if state == "active"
            else "\nلا يوجد سجل إنذارات معالجة."
        )
    buttons = []
    for row in rows:
        title, details = localize_alert_content(
            row["title"], row["details"]
        )
        title = safe_text(title, 60)
        details = safe_text(details, 120)
        lines.append(
            f"\nالسبب: {safe_html(title, 180)}"
            f"\nالمشكلة: {safe_html(details, 300)}"
        )
        buttons.append(
            [
                InlineKeyboardButton(
                    f"#{row['id']} · {title[:35]}",
                    callback_data=f"admin:alert:{row['id']}",
                )
            ]
        )
    navigation = []
    if page > 0:
        navigation.append(
            InlineKeyboardButton(
                "السابق",
                callback_data=f"admin:alerts:{state}:{page - 1}",
            )
        )
    if has_next:
        navigation.append(
            InlineKeyboardButton(
                "التالي",
                callback_data=f"admin:alerts:{state}:{page + 1}",
            )
        )
    if navigation:
        buttons.append(navigation)
    buttons.append(
        [
            InlineKeyboardButton(
                "النشطة",
                callback_data="admin:alerts:active:0",
            ),
            InlineKeyboardButton(
                "المعالجة",
                callback_data="admin:alerts:resolved:0",
            ),
        ]
    )
    buttons.append(
        [
            InlineKeyboardButton(
                "تحديث",
                callback_data=f"admin:alerts:{state}:{page}",
            ),
            InlineKeyboardButton("لوحة الأدمن", callback_data="admin:home"),
        ]
    )
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def admin_alert_detail(query, alert_id: int):
    async with database() as conn:
        alert = await fetch_one(
            conn,
            "SELECT * FROM nabil_bot_alerts WHERE id = %s",
            (alert_id,),
        )
    if not alert:
        await query.edit_message_text(
            "هذا الإنذار غير موجود.",
            reply_markup=back_keyboard("admin:alerts", "قائمة الإنذارات"),
        )
        return
    title, details = localize_alert_content(
        alert["title"], alert["details"]
    )
    lines = [
        "<b>إنذار البوت</b>",
        f"السبب: {safe_html(title, 80)}",
        f"المشكلة: {safe_html(details, 220)}",
    ]
    buttons = []
    if alert["state"] == "active":
        buttons.append(
            [
                InlineKeyboardButton(
                    "تحديد كمُعالج",
                    callback_data=f"admin:alertresolve:{alert_id}",
                )
            ]
        )
    list_state = "active" if alert["state"] == "active" else "resolved"
    buttons.append(
        [
            InlineKeyboardButton(
                "قائمة الإنذارات",
                callback_data=f"admin:alerts:{list_state}:0",
            )
        ]
    )
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def resolve_admin_alert(query, user_id: int, alert_id: int):
    resolved = await resolve_bot_alert(alert_id, user_id)
    if resolved:
        await log_admin_action(
            user_id,
            "معالجة إنذار البوت",
            target_id=alert_id,
        )
    await admin_alert_detail(query, alert_id)


async def admin_orders(query, page: int = 0):
    page = max(0, page)
    async with database() as conn:
        rows = await fetch_all(
            conn,
            """
            SELECT id, member_id, service_name, quantity, status, sale_amount
            FROM nabil_orders
            ORDER BY id DESC
            LIMIT %s OFFSET %s
            """,
            (PAGE_SIZE + 1, page * PAGE_SIZE),
        )
    has_next = len(rows) > PAGE_SIZE
    rows = rows[:PAGE_SIZE]
    if not rows:
        await query.edit_message_text(
            "لا توجد طلبات مسجلة.",
            reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("رجوع", callback_data=admin_parent_target(query.from_user.id))]]
            ),
        )
        return

    lines = ["<b>الطلبات الأخيرة — اضغط طلباً للتفاصيل:</b>"]
    buttons = []
    for row in rows:
        lines.append(
            f"\n#{row['id']} · {safe_text(row['status'], 24)} · عضو {row['member_id']}"
            f"\n{safe_text(row['service_name'], 55)} · كمية {row['quantity']} · "
            f"{fmt_money(row['sale_amount'])}"
        )
        buttons.append(
            [
                InlineKeyboardButton(
                    f"#{row['id']} · {safe_text(row['status'], 18)}",
                    callback_data=f"admin:order:{row['id']}",
                )
            ]
        )
    navigation = []
    if page > 0:
        navigation.append(
            InlineKeyboardButton("السابق", callback_data=f"admin:orders:{page - 1}")
        )
    if has_next:
        navigation.append(
            InlineKeyboardButton("التالي", callback_data=f"admin:orders:{page + 1}")
        )
    if navigation:
        buttons.append(navigation)
    buttons.append(
        [InlineKeyboardButton("رجوع", callback_data=admin_parent_target(query.from_user.id))]
    )
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def show_admin_order(query, order_id: int):
    async with database() as conn:
        order = await fetch_one(
            conn,
            """
            SELECT id, member_id, provider_id, provider_order_id, service_name,
                   target_url, quantity, status, sale_amount, refunded_amount,
                   created_at, last_error
            FROM nabil_orders
            WHERE id = %s
            """,
            (order_id,),
        )
    if not order:
        await query.edit_message_text(
            "الطلب غير موجود.",
            reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("رجوع للطلبات", callback_data="admin:orders")]]
            ),
        )
        return
    provider_order = order["provider_order_id"] or "لم يُرسل بعد"
    created = order["created_at"].strftime("%Y-%m-%d %H:%M UTC")
    error_line = (
        f"\nملاحظة: {safe_html(order['last_error'], 220)}"
        if order["last_error"]
        else ""
    )
    charge_lines = (
        f"المبلغ: {fmt_money(order['sale_amount'])}\n"
        f"المبلغ المسترد: {fmt_money(order['refunded_amount'])}\n"
    )
    await query.edit_message_text(
        f"<b>تفاصيل الطلب #{order['id']}</b>\n"
        f"العضو: <code>{order['member_id']}</code>\n"
        f"الخدمة: {safe_html(order['service_name'], 100)}\n"
        f"الكمية: {order['quantity']}\n"
        f"الحالة: {safe_html(order_status_label(order['status']), 30)}\n"
        f"{charge_lines}"
        f"المزود: #{order['provider_id']} · رقم طلب المزود: "
        f"{safe_html(provider_order, 60)}\n"
        f"الرابط: {safe_html(order['target_url'], 220)}\n"
        f"تاريخ الطلب: {created}{error_line}",
        reply_markup=InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton(
                        "معلومات العضو",
                        callback_data=f"admin:member:{order['member_id']}",
                    )
                ],
                [InlineKeyboardButton("رجوع للطلبات", callback_data="admin:orders")],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


async def show_admin_member(target, member_id: int):
    async with database() as conn:
        await conn.execute(
            """
            INSERT INTO nabil_bot_user_state (telegram_id)
            SELECT telegram_id FROM nabil_members WHERE telegram_id = %s
            ON CONFLICT (telegram_id) DO NOTHING
            """,
            (member_id,),
        )
        member = await fetch_one(
            conn,
            """
            SELECT m.telegram_id, m.balance, m.created_at, COUNT(o.id) AS order_count,
                   COALESCE(u.referrals_count, 0) AS referrals_count,
                   COALESCE(u.is_banned, FALSE) AS is_banned,
                   u.first_name, u.username
            FROM nabil_members m
            LEFT JOIN nabil_orders o ON o.member_id = m.telegram_id
            LEFT JOIN nabil_bot_user_state u ON u.telegram_id = m.telegram_id
            WHERE m.telegram_id = %s
            GROUP BY m.telegram_id, u.referrals_count, u.is_banned,
                     u.first_name, u.username
            """,
            (member_id,),
        )
    if not member:
        text = "هذا العضو غير مسجل في البوت."
        markup = InlineKeyboardMarkup(
            [
                [InlineKeyboardButton("بحث عن عضو", callback_data="admin:members")],
                [InlineKeyboardButton("رجوع للوحة", callback_data="admin:home")],
            ]
        )
    else:
        joined = member["created_at"].strftime("%Y-%m-%d")
        display_name = safe_html(member["first_name"] or "غير مسجل", 80)
        username = (
            f"\nاسم المستخدم: @{safe_html(member['username'], 80)}"
            if member["username"]
            else ""
        )
        banned = bool(member["is_banned"])
        text = (
            "<b>معلومات العضو</b>\n"
            f"الآيدي: <code>{member['telegram_id']}</code>\n"
            f"الاسم: {display_name}{username}\n"
            f"الرصيد: {fmt_money(member['balance'])}\n"
            f"الدعوات الناجحة: {member['referrals_count']}\n"
            f"عدد الطلبات: {member['order_count']}\n"
            f"تاريخ التسجيل: {joined}\n"
            f"الحالة: {'محظور' if banned else 'نشط'}"
        )
        buttons = []
        actor = getattr(target, "from_user", None)
        if actor and await has_admin_permission(actor.id, "wallet"):
            buttons.append(
                [
                    InlineKeyboardButton(
                        "إضافة رصيد", callback_data=f"wallet:credit:{member_id}"
                    ),
                    InlineKeyboardButton(
                        "خصم رصيد", callback_data=f"wallet:debit:{member_id}"
                    ),
                ]
            )
        buttons.extend(
            [
                [
                    InlineKeyboardButton(
                        "سجل حركة الرصيد",
                        callback_data=f"admin:member:ledger:{member_id}",
                    )
                ],
                [
                    InlineKeyboardButton(
                        "إلغاء الحظر" if banned else "حظر العضو",
                        callback_data=f"member:ban:{member_id}",
                    )
                ],
                [InlineKeyboardButton("بحث عن عضو آخر", callback_data="admin:members")],
                [InlineKeyboardButton("رجوع للوحة", callback_data="admin:home")],
            ]
        )
        markup = InlineKeyboardMarkup(buttons)
    if hasattr(target, "edit_message_text"):
        await target.edit_message_text(
            text, reply_markup=markup, parse_mode=ParseMode.HTML
        )
    else:
        await target.reply_text(text, reply_markup=markup, parse_mode=ParseMode.HTML)


async def admin_member_wallet_history(query, member_id: int):
    async with database() as conn:
        rows = await fetch_all(
            conn,
            """
            SELECT id, entry_type, amount, balance_after, note
            FROM nabil_ledger
            WHERE member_id = %s
              AND amount <> 0
            ORDER BY id DESC
            LIMIT 12
            """,
            (member_id,),
        )
        member = await fetch_one(
            conn,
            "SELECT telegram_id FROM nabil_members WHERE telegram_id = %s",
            (member_id,),
        )
    if not member:
        text = "العضو غير مسجل في البوت."
    elif not rows:
        text = (
            f"<b>حركة رصيد العضو</b>\nالآيدي: <code>{member_id}</code>\n\n"
            "ماكو حركات رصيد مسجلة."
        )
    else:
        lines = [
            "<b>حركة رصيد العضو</b> · آخر 12 حركة",
            f"الآيدي: <code>{member_id}</code>",
        ]
        entry_labels = {
            "admin_credit": "إضافة من الأدمن",
            "admin_debit": "خصم من الأدمن",
            "order_debit": "خصم طلب",
            "refund": "استرداد طلب",
            "member_transfer_out": "تحويل صادر",
            "member_transfer_in": "تحويل وارد",
            "agent_transfer_out": "تحويل وكيل صادر",
            "agent_transfer_in": "تحويل وكيل وارد",
            "order_points_debit": "خصم خدمة",
            "order_points_refund": "استرداد خدمة",
            "daily_points_gift": "مكافأة يومية",
            "gift_code_points": "رصيد من كود هدية",
            "points_conversion": "ترحيل رصيد سابق إلى المحفظة",
            "unified_wallet_migration": "ترحيل النقاط إلى رصيد IQD",
            "referral_reward": "مكافأة دعوة",
            "referral_signup_reward": "مكافأة تسجيل",
        }
        for row in rows:
            amount = Decimal(str(row["amount"]))
            entry_type = safe_html(
                entry_labels.get(row["entry_type"], row["entry_type"]), 60
            )
            note = safe_html(row["note"] or "بدون ملاحظة", 180)
            lines.append(
                f"\n#{row['id']} · {entry_type} · {fmt_money(amount)}"
                f"\nالرصيد بعد الحركة: {fmt_money(row['balance_after'])}"
                f"\n{note}"
            )
        text = "\n".join(lines)
    await query.edit_message_text(
        text,
        reply_markup=back_keyboard(
            f"admin:member:{member_id}", "رجوع لمعلومات العضو"
        ),
        parse_mode=ParseMode.HTML,
    )


async def begin_member_search(query, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.clear()
    context.user_data["mode"] = "admin_member_search"
    await query.edit_message_text(
        "أرسل رقم حساب تيليغرام للبحث عن العضو.",
        reply_markup=InlineKeyboardMarkup(
            [[InlineKeyboardButton("رجوع للوحة", callback_data="admin:home")]]
        ),
    )


async def admin_agents(query):
    async with database() as conn:
        agents = await fetch_all(
            conn,
            """
            SELECT a.telegram_id, a.added_by, a.created_at,
                   p.can_orders, p.can_members, p.can_wallet, p.can_reports,
                   p.can_services, p.can_broadcast, p.can_force_subscription
            FROM nabil_bot_admins a
            LEFT JOIN nabil_bot_admin_permissions p ON p.telegram_id = a.telegram_id
            ORDER BY a.created_at DESC
            """,
        )
    lines = [
        "<b>إدارة الأدمنية والصلاحيات</b>",
        "حدد لكل أدمن الأقسام التي يستطيع إدارتها. إعدادات المالك تبقى خاصة بالمالك.",
    ]
    buttons = [
        [
            InlineKeyboardButton("نظام الوكلاء", callback_data="agentsys:owner"),
            InlineKeyboardButton("إضافة مشرف", callback_data="agent:add"),
        ]
    ]
    for row in agents:
        enabled_count = sum(
            bool(row.get(ADMIN_PERMISSION_COLUMNS[key]))
            for key in ADMIN_PERMISSION_COLUMNS
        )
        lines.append(
            f"\nآيدي: <code>{row['telegram_id']}</code>"
            f"\nالصلاحيات المفعّلة: {enabled_count}/{len(ADMIN_PERMISSION_COLUMNS)}"
        )
        buttons.append(
            [
                InlineKeyboardButton(
                    "الصلاحيات",
                    callback_data=f"agent:permissions:{row['telegram_id']}",
                ),
                InlineKeyboardButton(
                    "إزالة",
                    callback_data=f"agent:remove:{row['telegram_id']}",
                )
            ]
        )
    if not agents:
        lines.append("\nلا يوجد مشرفون إضافيون حالياً.")
    buttons.append([InlineKeyboardButton("رجوع", callback_data="admin:home")])
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def validate_agent_audit_channel(bot, reference: str) -> dict[str, str]:
    reference = reference.strip()
    if not reference:
        raise ValueError("أرسل معرّف القناة أو اسمها العام مثل @channel.")
    try:
        chat = await bot.get_chat(reference)
    except Exception as exc:
        raise ValueError(
            "تعذر الوصول للقناة. تأكد من المعرّف وأضف البوت إليها."
        ) from exc
    if chat.type != "channel":
        raise ValueError("المعرّف لا يشير إلى قناة تيليغرام.")
    bot_user = await bot.get_me()
    member = await bot.get_chat_member(chat.id, bot_user.id)
    if member.status == "creator":
        pass
    elif (
        member.status == "administrator"
        and getattr(member, "can_post_messages", False) is True
    ):
        pass
    else:
        raise ValueError(
            "يجب أن يكون البوت مشرفاً في القناة مع صلاحية نشر الرسائل."
        )
    return {"chat_id": str(chat.id), "title": chat.title or str(chat.id)}


async def agent_audit_channel_status(bot) -> tuple[str, str | None]:
    channel_id = (await get_setting(AGENT_AUDIT_CHANNEL_KEY)).strip()
    if not channel_id:
        return "غير معيّنة", None
    try:
        info = await validate_agent_audit_channel(bot, channel_id)
    except Exception:
        return "غير متاحة أو صلاحية النشر مفقودة", channel_id
    return f"جاهزة: {safe_text(info['title'], 80)}", info["chat_id"]


async def send_agent_audit(bot, text: str) -> bool:
    channel_id = (await get_setting(AGENT_AUDIT_CHANNEL_KEY)).strip()
    if not channel_id:
        return False
    try:
        await bot.send_message(
            chat_id=int(channel_id),
            text=text,
            parse_mode=ParseMode.HTML,
            disable_web_page_preview=True,
        )
        return True
    except Exception as exc:
        LOG.warning("Could not send agent audit entry: %s", safe_text(exc, 180))
        return False


async def insert_agent_ledger(
    conn,
    agent_id: int,
    actor_id: int,
    operation: str,
    amount: Decimal,
    wallet_before: Decimal,
    wallet_after: Decimal,
    target_id: int | None = None,
    member_points_before: Decimal | None = None,
    member_points_after: Decimal | None = None,
    details: str = "",
):
    await conn.execute(
        """
        INSERT INTO nabil_agent_transactions (
            agent_id, actor_id, operation, amount, wallet_before, wallet_after,
            target_id, member_points_before, member_points_after, details
        )
        VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """,
        (
            agent_id,
            actor_id,
            operation,
            amount,
            wallet_before,
            wallet_after,
            target_id,
            member_points_before,
            member_points_after,
            safe_text(details, 500),
        ),
    )


async def agent_owner_panel(query):
    async with database() as conn:
        totals = await fetch_one(
            conn,
            """
            SELECT COUNT(*) FILTER (WHERE status = 'active') AS active_count,
                   COUNT(*) AS total_count
            FROM nabil_bot_agents
            """,
        )
    channel_status, channel_id = await agent_audit_channel_status(query.get_bot())
    channel_line = (
        f"{safe_html(channel_status, 100)} · <code>{safe_html(channel_id, 32)}</code>"
        if channel_id
        else safe_html(channel_status, 100)
    )
    buttons = [
        [
            InlineKeyboardButton("قائمة الوكلاء", callback_data="agentsys:list:0"),
            InlineKeyboardButton("إضافة وكيل", callback_data="agentsys:add"),
        ],
        [
            InlineKeyboardButton("شحن محفظة", callback_data="agentsys:wallet:credit"),
            InlineKeyboardButton("تعيين رصيد", callback_data="agentsys:wallet:set"),
        ],
        [InlineKeyboardButton("تعيين قناة السجلات", callback_data="agentsys:channel")],
    ]
    if channel_id:
        buttons.append(
            [InlineKeyboardButton("إزالة قناة السجلات", callback_data="agentsys:channel:clear")]
        )
    buttons.append([InlineKeyboardButton("رجوع لإدارة الأدمنية", callback_data="admin:agents")])
    await query.edit_message_text(
        "<b>نظام الوكلاء</b>\n\n"
        f"الوكلاء النشطون: <b>{int(totals['active_count'] or 0)}</b>\n"
        f"إجمالي السجلات: <b>{int(totals['total_count'] or 0)}</b>\n"
        f"قناة السجلات: {channel_line}",
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def agent_owner_list(query, page: int = 0):
    page = max(0, page)
    async with database() as conn:
        count_row = await fetch_one(conn, "SELECT COUNT(*) AS total FROM nabil_bot_agents")
        total = int(count_row["total"] or 0)
        page_count = max(1, (total + AGENT_PAGE_SIZE - 1) // AGENT_PAGE_SIZE)
        page = min(page, page_count - 1)
        agents = await fetch_all(
            conn,
            """
            SELECT a.telegram_id, COALESCE(m.balance, 0) AS balance,
                   a.status, a.created_at
            FROM nabil_bot_agents AS a
            LEFT JOIN nabil_members AS m ON m.telegram_id = a.telegram_id
            ORDER BY CASE a.status WHEN 'active' THEN 0 WHEN 'inactive' THEN 1 ELSE 2 END,
                     a.created_at DESC, a.telegram_id
            LIMIT %s OFFSET %s
            """,
            (AGENT_PAGE_SIZE, page * AGENT_PAGE_SIZE),
        )
    lines = [f"<b>قائمة الوكلاء</b> · صفحة {page + 1}/{page_count}"]
    buttons = []
    for agent in agents:
        status = {
            "active": "نشط",
            "inactive": "متوقف",
            "archived": "مؤرشف",
        }.get(agent["status"], "غير معروف")
        lines.append(
            f"\n<code>{agent['telegram_id']}</code> · {status} · "
            f"الرصيد: {fmt_money(agent['balance'])}"
        )
        buttons.append(
            [
                InlineKeyboardButton(
                    f"تفاصيل {agent['telegram_id']}",
                    callback_data=f"agentsys:detail:{agent['telegram_id']}",
                )
            ]
        )
    if not agents:
        lines.append("\nلا يوجد وكلاء بعد.")
    navigation = []
    if page > 0:
        navigation.append(
            InlineKeyboardButton("السابق", callback_data=f"agentsys:list:{page - 1}")
        )
    if page + 1 < page_count:
        navigation.append(
            InlineKeyboardButton("التالي", callback_data=f"agentsys:list:{page + 1}")
        )
    if navigation:
        buttons.append(navigation)
    buttons.append([InlineKeyboardButton("رجوع لنظام الوكلاء", callback_data="agentsys:owner")])
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def agent_owner_detail(query, agent_id: int, notice: str = ""):
    async with database() as conn:
        agent = await fetch_one(
            conn,
            """
            SELECT a.telegram_id, COALESCE(m.balance, 0) AS balance,
                   a.status, a.added_by, a.created_at
            FROM nabil_bot_agents AS a
            LEFT JOIN nabil_members AS m ON m.telegram_id = a.telegram_id
            WHERE a.telegram_id = %s
            """,
            (agent_id,),
        )
        daily = await fetch_one(
            conn,
            """
            SELECT COUNT(*) AS total FROM nabil_agent_transactions
            WHERE agent_id = %s AND operation IN ('transfer_add', 'transfer_debit')
              AND created_at >= CURRENT_DATE
            """,
            (agent_id,),
        )
    if not agent:
        await query.edit_message_text(
            "الوكيل غير موجود.",
            reply_markup=back_keyboard("agentsys:list:0", "رجوع للقائمة"),
        )
        return
    status = {
        "active": "نشط",
        "inactive": "متوقف",
        "archived": "مؤرشف",
    }.get(agent["status"], "غير معروف")
    buttons = []
    if agent["status"] != "archived":
        buttons.append(
            [
                InlineKeyboardButton(
                    "شحن المحفظة",
                    callback_data=f"agentsys:wallet:credit:{agent_id}",
                ),
                InlineKeyboardButton(
                    "تعيين الرصيد",
                    callback_data=f"agentsys:wallet:set:{agent_id}",
                ),
            ]
        )
        buttons.append(
            [
                InlineKeyboardButton(
                    "إيقاف الوكيل" if agent["status"] == "active" else "تفعيل الوكيل",
                    callback_data=f"agentsys:status:{agent_id}",
                ),
                InlineKeyboardButton(
                    "أرشفة",
                    callback_data=f"agentsys:archive:{agent_id}",
                ),
            ]
        )
    buttons.append([InlineKeyboardButton("رجوع للقائمة", callback_data="agentsys:list:0")])
    await query.edit_message_text(
        "<b>بيانات الوكيل</b>\n\n"
        f"الآيدي: <code>{agent_id}</code>\n"
        f"الحالة: {status}\n"
        f"الرصيد الموحد: <b>{fmt_money(agent['balance'])}</b>\n"
        f"عمليات اليوم: <b>{int(daily['total'] or 0)}</b>\n"
        f"أضيف بواسطة: <code>{agent['added_by']}</code>"
        + (f"\n\n{safe_html(notice, 200)}" if notice else ""),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def agent_panel_text(user_id: int) -> tuple[str, InlineKeyboardMarkup]:
    async with database() as conn:
        agent = await fetch_one(
            conn,
            """
            SELECT COALESCE(m.balance, 0) AS balance, a.status
            FROM nabil_bot_agents AS a
            LEFT JOIN nabil_members AS m ON m.telegram_id = a.telegram_id
            WHERE a.telegram_id = %s
            """,
            (user_id,),
        )
        daily = await fetch_one(
            conn,
            """
            SELECT COUNT(*) AS total FROM nabil_agent_transactions
            WHERE agent_id = %s AND operation IN ('transfer_add', 'transfer_debit')
              AND created_at >= CURRENT_DATE
            """,
            (user_id,),
        )
    if not agent or agent["status"] != "active":
        return "لوحة الوكيل غير متاحة لهذا الحساب.", InlineKeyboardMarkup([])
    markup = InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("إضافة رصيد", callback_data="agentwallet:add"),
                InlineKeyboardButton("خصم رصيد", callback_data="agentwallet:debit"),
            ],
            [InlineKeyboardButton("محفظتي", callback_data="agentwallet:balance")],
        ]
    )
    text = (
        "<b>لوحة الوكيل</b>\n"
        f"رصيدك: <b>{fmt_money(agent['balance'])}</b>\n"
        f"عمليات اليوم: <b>{int(daily['total'] or 0)}</b>"
    )
    return text, markup


async def agent_panel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    chat = update.effective_chat
    if not chat or chat.type != "private":
        await update.effective_message.reply_text(
            "استخدم لوحة الوكيل في محادثة خاصة مع البوت حفاظاً على سرية الرصيد."
        )
        return
    if not user or not await is_active_agent(user.id):
        await update.effective_message.reply_text("لوحة الوكيل مخصصة للوكلاء النشطين فقط.")
        return
    text, markup = await agent_panel_text(user.id)
    await update.effective_message.reply_text(text, reply_markup=markup, parse_mode=ParseMode.HTML)


async def change_agent_owner_balance(
    actor_id: int, agent_id: int, action: str, amount: Decimal
) -> tuple[str, Decimal | None, Decimal | None]:
    if action not in {"credit", "set"}:
        raise ValueError("Unsupported agent wallet action.")
    amount = money(amount)
    if amount < 0 or amount > MAX_AGENT_BALANCE:
        return "range", None, None
    async with AGENT_TRANSACTION_LOCK:
        async with database() as conn:
            async with conn.transaction():
                agent = await fetch_one(
                    conn,
                    """
                    SELECT status FROM nabil_bot_agents
                    WHERE telegram_id = %s FOR UPDATE
                    """,
                    (agent_id,),
                )
                if not agent:
                    return "missing", None, None
                if agent["status"] == "archived":
                    return "archived", None, None
                member = await fetch_one(
                    conn,
                    "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                    (agent_id,),
                )
                if not member:
                    return "missing", None, None
                before = money(Decimal(str(member["balance"] or 0)))
                after = money(before + amount) if action == "credit" else amount
                if after < 0 or after > MAX_AGENT_BALANCE:
                    return "range", before, None
                if after == before:
                    return "unchanged", before, after
                await conn.execute(
                    """
                    UPDATE nabil_members SET balance = %s
                    WHERE telegram_id = %s
                    """,
                    (after, agent_id),
                )
                delta = money(after - before)
                operation = "owner_wallet_credit" if action == "credit" else "owner_wallet_set"
                details = (
                    f"إضافة {fmt_money(amount)} إلى رصيد الوكيل"
                    if action == "credit"
                    else f"تعيين رصيد الوكيل إلى {fmt_money(after)}"
                )
                await conn.execute(
                    """
                    INSERT INTO nabil_ledger
                      (member_id, entry_type, amount, balance_after, note)
                    VALUES (%s, %s, %s, %s, %s)
                    """,
                    (
                        agent_id,
                        "admin_credit" if delta > 0 else "admin_debit",
                        delta,
                        after,
                        f"تعديل بواسطة المالك {actor_id}: {details}",
                    ),
                )
                await enqueue_live_mirror_wallet_event(
                    conn,
                    member_id=agent_id,
                    entry_type="admin_credit" if delta > 0 else "admin_debit",
                    amount=delta,
                    balance_after=after,
                    note=details,
                    actor_id=actor_id,
                    event_key=f"agent-wallet:{uuid.uuid4().hex}",
                )
                await insert_agent_ledger(
                    conn,
                    agent_id,
                    actor_id,
                    operation,
                    delta,
                    before,
                    after,
                    details=details,
                )
                await insert_admin_audit(
                    conn, actor_id, details, agent_id,
                    f"الرصيد: {fmt_money(before)} → {fmt_money(after)}",
                )
    return "success", before, after


async def execute_agent_transfer(
    actor_id: int, operation: str, member_id: int, amount: Decimal
) -> dict[str, Any]:
    if member_id == actor_id:
        return {"status": "self"}
    if operation not in {"transfer_add", "transfer_debit"}:
        return {"status": "invalid"}
    amount = money(amount)
    if amount <= 0 or amount > MAX_AGENT_BALANCE:
        return {"status": "range"}
    async with AGENT_TRANSACTION_LOCK:
        async with database() as conn:
            async with conn.transaction():
                agent = await fetch_one(
                    conn,
                    """
                    SELECT status FROM nabil_bot_agents
                    WHERE telegram_id = %s FOR UPDATE
                    """,
                    (actor_id,),
                )
                if not agent or agent["status"] != "active":
                    return {"status": "inactive"}
                locked_members = {}
                for locked_id in sorted((actor_id, member_id)):
                    locked_members[locked_id] = await fetch_one(
                        conn,
                        "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                        (locked_id,),
                    )
                if not locked_members.get(actor_id):
                    return {"status": "inactive"}
                if not locked_members.get(member_id):
                    return {"status": "not_member"}
                wallet_before = money(
                    Decimal(str(locked_members[actor_id]["balance"] or 0))
                )
                member_before = money(
                    Decimal(str(locked_members[member_id]["balance"] or 0))
                )
                if operation == "transfer_add":
                    if wallet_before < amount:
                        return {
                            "status": "wallet_low",
                            "wallet": wallet_before,
                            "balance": member_before,
                        }
                    wallet_after = money(wallet_before - amount)
                    member_after = money(member_before + amount)
                    action_text = "إضافة"
                else:
                    if member_before < amount:
                        return {
                            "status": "balance_low",
                            "wallet": wallet_before,
                            "balance": member_before,
                        }
                    wallet_after = money(wallet_before + amount)
                    member_after = money(member_before - amount)
                    action_text = "خصم"
                if wallet_after > MAX_AGENT_BALANCE:
                    return {"status": "range"}
                await conn.execute(
                    """
                    UPDATE nabil_members SET balance = %s
                    WHERE telegram_id = %s
                    """,
                    (wallet_after, actor_id),
                )
                await conn.execute(
                    "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                    (member_after, member_id),
                )
                agent_delta = -amount if operation == "transfer_add" else amount
                member_delta = amount if operation == "transfer_add" else -amount
                await conn.execute(
                    """
                    INSERT INTO nabil_ledger
                      (member_id, entry_type, amount, balance_after, note)
                    VALUES (%s, %s, %s, %s, %s),
                           (%s, %s, %s, %s, %s)
                    """,
                    (
                        actor_id,
                        "agent_transfer_out" if agent_delta < 0 else "agent_transfer_in",
                        agent_delta,
                        wallet_after,
                        f"تحويل بواسطة الوكيل إلى/من العضو {member_id}",
                        member_id,
                        "agent_transfer_in" if member_delta > 0 else "agent_transfer_out",
                        member_delta,
                        member_after,
                        f"تحويل بواسطة الوكيل {actor_id}",
                    ),
                )
                transfer_from = actor_id if operation == "transfer_add" else member_id
                transfer_to = member_id if operation == "transfer_add" else actor_id
                transfer_balance_after = (
                    wallet_after if operation == "transfer_add" else member_after
                )
                await enqueue_live_mirror_wallet_event(
                    conn,
                    member_id=transfer_from,
                    entry_type="agent_transfer_out",
                    amount=-amount,
                    balance_after=transfer_balance_after,
                    note=f"تحويل إلى الحساب {transfer_to}",
                    counterparty_id=transfer_to,
                    actor_id=actor_id,
                    event_key=f"agent-transfer:{uuid.uuid4().hex}",
                )
                await insert_agent_ledger(
                    conn,
                    actor_id,
                    actor_id,
                    operation,
                    amount,
                    wallet_before,
                    wallet_after,
                    target_id=member_id,
                    details=f"{action_text} {fmt_money(amount)} للعضو {member_id}",
                )
                await insert_admin_audit(
                    conn,
                    actor_id,
                    f"وكيل: {action_text} رصيد",
                    member_id,
                    f"{fmt_money(amount)} | رصيد الوكيل "
                    f"{fmt_money(wallet_before)} → {fmt_money(wallet_after)} "
                    f"| رصيد العضو {fmt_money(member_before)} → {fmt_money(member_after)}",
                )
    return {
        "status": "success",
        "operation": operation,
        "amount": amount,
        "wallet_before": wallet_before,
        "wallet_after": wallet_after,
        "member_before": member_before,
        "member_after": member_after,
    }


async def show_agent_panel(query, user_id: int):
    if not await is_active_agent(user_id):
        await query.edit_message_text(
            "حساب الوكيل غير نشط.",
            reply_markup=back_keyboard("menu:balance", "القائمة الرئيسية"),
        )
        return
    text, markup = await agent_panel_text(user_id)
    await query.edit_message_text(text, reply_markup=markup, parse_mode=ParseMode.HTML)


async def agent_wallet_balance_screen(query, user_id: int):
    async with database() as conn:
        agent = await fetch_one(
            conn,
            """
            SELECT m.balance FROM nabil_bot_agents AS a
            JOIN nabil_members AS m ON m.telegram_id = a.telegram_id
            WHERE a.telegram_id = %s AND a.status = 'active'
            """,
            (user_id,),
        )
        daily = await fetch_one(
            conn,
            """
            SELECT COUNT(*) AS total FROM nabil_agent_transactions
            WHERE agent_id = %s AND operation IN ('transfer_add', 'transfer_debit')
              AND created_at >= CURRENT_DATE
            """,
            (user_id,),
        )
    if not agent:
        await query.edit_message_text(
            "حساب الوكيل غير نشط.",
            reply_markup=back_keyboard("agentwallet:home", "رجوع للوحة الوكيل"),
        )
        return
    await query.edit_message_text(
        "<b>محفظتي</b>\n\n"
        f"الرصيد الحالي: <b>{fmt_money(agent['balance'])}</b>\n"
        f"العمليات المنفذة اليوم: <b>{int(daily['total'] or 0)}</b>",
        reply_markup=back_keyboard("agentwallet:home", "رجوع للوحة الوكيل"),
        parse_mode=ParseMode.HTML,
    )


async def begin_agent_transfer(query, context: ContextTypes.DEFAULT_TYPE, operation: str):
    context.user_data.clear()
    context.user_data.update(
        {
            "mode": "agent_transfer_member",
            "agent_operation": operation,
        }
    )
    await query.edit_message_text(
        "أرسل آيدي المستخدم المسجل في البوت.",
        reply_markup=back_keyboard("agentwallet:home", "رجوع للوحة الوكيل"),
    )


async def begin_agent_owner_flow(
    query,
    context: ContextTypes.DEFAULT_TYPE,
    action: str,
    agent_id: int | None = None,
):
    context.user_data.clear()
    if action == "add":
        context.user_data["mode"] = "agentsys_add_id"
        prompt = "أرسل آيدي تيليغرام للوكيل الجديد."
        back_to = "agentsys:owner"
        back_label = "رجوع لنظام الوكلاء"
    elif action in {"credit", "set"}:
        context.user_data["agent_owner_action"] = action
        if agent_id is None:
            context.user_data["mode"] = (
                "agentsys_wallet_credit_id"
                if action == "credit"
                else "agentsys_wallet_set_id"
            )
            prompt = "أرسل آيدي الوكيل."
        else:
            context.user_data.update(
                {"mode": "agentsys_wallet_amount", "agent_id": agent_id}
            )
            prompt = (
                "أرسل مبلغ IQD المراد إضافته."
                if action == "credit"
                else "أرسل الرصيد الجديد بعملة IQD."
            )
        back_to = (
            f"agentsys:detail:{agent_id}" if agent_id else "agentsys:owner"
        )
        back_label = "رجوع للوكيل" if agent_id else "رجوع لنظام الوكلاء"
    elif action == "channel":
        context.user_data["mode"] = "agentsys_audit_channel"
        prompt = "أرسل آيدي القناة أو اسمها العام مثل @channel."
        back_to = "agentsys:owner"
        back_label = "رجوع لنظام الوكلاء"
    else:
        raise ValueError("Unsupported agent owner action.")
    await query.edit_message_text(
        prompt,
        reply_markup=back_keyboard(back_to, back_label),
    )


async def change_agent_status(
    actor_id: int, agent_id: int, status: str
) -> tuple[str, Decimal | None]:
    if status not in {"active", "inactive", "archived"}:
        raise ValueError("Unsupported agent status.")
    async with AGENT_TRANSACTION_LOCK:
        async with database() as conn:
            async with conn.transaction():
                agent = await fetch_one(
                    conn,
                    """
                    SELECT status FROM nabil_bot_agents
                    WHERE telegram_id = %s FOR UPDATE
                    """,
                    (agent_id,),
                )
                if not agent:
                    return "missing", None
                if agent["status"] == "archived":
                    return "archived", None
                member = await fetch_one(
                    conn,
                    "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                    (agent_id,),
                )
                balance = (
                    money(Decimal(str(member["balance"] or 0)))
                    if member
                    else money(0)
                )
                previous = agent["status"]
                await conn.execute(
                    """
                    UPDATE nabil_bot_agents
                    SET status = %s, updated_at = NOW()
                    WHERE telegram_id = %s
                    """,
                    (status, agent_id),
                )
                label = {
                    "active": "تفعيل وكيل",
                    "inactive": "إيقاف وكيل",
                    "archived": "أرشفة وكيل",
                }[status]
                await insert_agent_ledger(
                    conn,
                    agent_id,
                    actor_id,
                    f"agent_{status}",
                    money(0),
                    balance,
                    balance,
                    details=f"الحالة: {previous} → {status}",
                )
                await insert_admin_audit(
                    conn, actor_id, label, agent_id, f"{previous} → {status}"
                )
    return "success", balance


async def handle_agent_text(
    update: Update, context: ContextTypes.DEFAULT_TYPE, mode: str, text: str
) -> bool:
    user = update.effective_user
    message = update.effective_message
    if not user or not message:
        return False
    owner_id = user.id

    if mode == "agentsys_add_id":
        try:
            agent_id = int(text)
            if agent_id <= 0 or agent_id == OWNER_ID:
                raise ValueError
        except ValueError:
            await message.reply_text(
                "أرسل آيدي تيليغرام صحيحاً للوكيل.",
                reply_markup=back_keyboard("agentsys:owner", "رجوع لنظام الوكلاء"),
            )
            return True
        context.user_data.update({"agent_id": agent_id, "mode": "agentsys_add_balance"})
        await message.reply_text(
            "أرسل رصيد IQD الابتدائي لحساب الوكيل. أرسل 0 إذا أردت البدء دون رصيد.",
            reply_markup=back_keyboard("agentsys:owner", "رجوع لنظام الوكلاء"),
        )
        return True

    if mode == "agentsys_add_balance":
        try:
            amount = money(Decimal(text))
            if amount < 0 or amount > MAX_AGENT_BALANCE:
                raise ValueError
        except (InvalidOperation, ValueError):
            await message.reply_text("أرسل مبلغ IQD من 0 إلى 1,000,000,000,000,000.")
            return True
        agent_id = int(context.user_data["agent_id"])
        status = "exists"
        async with AGENT_TRANSACTION_LOCK:
            async with database() as conn:
                async with conn.transaction():
                    inserted = await fetch_one(
                        conn,
                        """
                        INSERT INTO nabil_bot_agents
                            (telegram_id, status, added_by)
                        VALUES (%s, 'active', %s)
                        ON CONFLICT (telegram_id) DO NOTHING
                        RETURNING telegram_id
                        """,
                        (agent_id, owner_id),
                    )
                    if inserted:
                        status = "success"
                        await conn.execute(
                            """
                            INSERT INTO nabil_members (telegram_id)
                            VALUES (%s) ON CONFLICT (telegram_id) DO NOTHING
                            """,
                            (agent_id,),
                        )
                        member = await fetch_one(
                            conn,
                            "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                            (agent_id,),
                        )
                        before = money(Decimal(str(member["balance"] or 0)))
                        after = money(before + amount)
                        if amount > 0:
                            await conn.execute(
                                "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                                (after, agent_id),
                            )
                            await conn.execute(
                                """
                                INSERT INTO nabil_ledger
                                  (member_id, entry_type, amount, balance_after, note)
                                VALUES (%s, 'admin_credit', %s, %s, %s)
                                """,
                                (
                                    agent_id,
                                    amount,
                                    after,
                                    f"رصيد ابتدائي للوكيل بواسطة المالك {owner_id}",
                                ),
                            )
                            await enqueue_live_mirror_wallet_event(
                                conn,
                                member_id=agent_id,
                                entry_type="admin_credit",
                                amount=amount,
                                balance_after=after,
                                note="رصيد ابتدائي للوكيل",
                                actor_id=owner_id,
                                event_key=f"agent-initial-credit:{agent_id}",
                            )
                        await insert_agent_ledger(
                            conn,
                            agent_id,
                            owner_id,
                            "agent_add",
                            amount,
                            before,
                            after,
                            details=f"إضافة وكيل ورصيد ابتدائي {fmt_money(amount)}",
                        )
                        await insert_admin_audit(
                            conn,
                            owner_id,
                            "إضافة وكيل",
                            agent_id,
                            f"الرصيد الابتدائي: {fmt_money(amount)}",
                        )
        context.user_data.clear()
        if status == "exists":
            await message.reply_text(
                "هذا الحساب مسجل مسبقاً كوكيل.",
                reply_markup=back_keyboard("agentsys:list:0", "رجوع للقائمة"),
            )
            return True
        audit_ok = await send_agent_audit(
            context.bot,
            "<b>إضافة وكيل</b>\n"
            f"المالك: <code>{owner_id}</code>\n"
            f"الوكيل: <code>{agent_id}</code>\n"
            f"الرصيد الابتدائي: <b>{fmt_money(amount)}</b>",
        )
        suffix = "" if audit_ok else "\nتنبيه: لم تُرسل نسخة إلى قناة السجلات؛ تحقق من إعدادها."
        await message.reply_text(
            f"تمت إضافة الوكيل ورصيده الابتدائي "
            f"{fmt_money(amount)}.{suffix}",
            reply_markup=back_keyboard("agentsys:detail:" + str(agent_id), "عرض الوكيل"),
        )
        return True

    if mode in {"agentsys_wallet_credit_id", "agentsys_wallet_set_id"}:
        try:
            agent_id = int(text)
            if agent_id <= 0:
                raise ValueError
        except ValueError:
            await message.reply_text("أرسل آيدي وكيل صحيحاً.")
            return True
        action = "credit" if mode.endswith("credit_id") else "set"
        context.user_data.update(
            {
                "agent_id": agent_id,
                "agent_owner_action": action,
                "mode": "agentsys_wallet_amount",
            }
        )
        await message.reply_text(
            "أرسل مبلغ IQD المراد إضافته."
            if action == "credit"
            else "أرسل الرصيد الجديد بعملة IQD.",
            reply_markup=back_keyboard(
                f"agentsys:detail:{agent_id}", "رجوع للوكيل"
            ),
        )
        return True

    if mode == "agentsys_wallet_amount":
        action = context.user_data.get("agent_owner_action")
        try:
            amount = money(Decimal(text))
            minimum = money(Decimal("0.001")) if action == "credit" else money(0)
            if amount < minimum or amount > MAX_AGENT_BALANCE:
                raise ValueError
        except (InvalidOperation, ValueError, TypeError):
            await message.reply_text(
                "أرسل مبلغ IQD صالحاً، أو رصيداً من 0 إلى "
                "1,000,000,000,000,000 للتعيين."
            )
            return True
        agent_id = int(context.user_data["agent_id"])
        result, before, after = await change_agent_owner_balance(
            owner_id, agent_id, action, amount
        )
        context.user_data.clear()
        if result != "success":
            errors = {
                "missing": "الوكيل غير موجود.",
                "archived": "لا يمكن تعديل محفظة وكيل مؤرشف.",
                "range": "الرصيد الناتج خارج الحد المسموح.",
                "unchanged": "الرصيد المحدد يساوي الرصيد الحالي.",
            }
            await message.reply_text(
                errors.get(result, "تعذر تعديل المحفظة."),
                reply_markup=back_keyboard(
                    f"agentsys:detail:{agent_id}", "رجوع للوكيل"
                ),
            )
            return True
        action_label = "شحن محفظة" if action == "credit" else "تعيين رصيد"
        audit_ok = await send_agent_audit(
            context.bot,
            f"<b>{action_label}</b>\n"
            f"المالك: <code>{owner_id}</code>\n"
            f"الوكيل: <code>{agent_id}</code>\n"
            f"الرصيد: <b>{fmt_money(before)}</b> → "
            f"<b>{fmt_money(after)}</b>",
        )
        suffix = "" if audit_ok else "\nتنبيه: لم تُرسل نسخة إلى قناة السجلات؛ تحقق من إعدادها."
        await message.reply_text(
            f"تم تعديل رصيد الوكيل: {fmt_money(before)} → "
            f"{fmt_money(after)}.{suffix}",
            reply_markup=back_keyboard(
                f"agentsys:detail:{agent_id}", "رجوع للوكيل"
            ),
        )
        return True

    if mode == "agentsys_audit_channel":
        try:
            channel = await validate_agent_audit_channel(context.bot, text)
        except Exception as exc:
            await message.reply_text(
                safe_text(exc, 240)
                or "تعذر التحقق من القناة؛ أرسل معرّفاً صالحاً.",
                reply_markup=back_keyboard(
                    "agentsys:owner", "رجوع لنظام الوكلاء"
                ),
            )
            return True
        await set_setting(AGENT_AUDIT_CHANNEL_KEY, channel["chat_id"])
        await log_admin_action(
            owner_id,
            "تعيين قناة سجلات الوكلاء",
            details=f"القناة: {channel['chat_id']}",
        )
        context.user_data.clear()
        audit_ok = await send_agent_audit(
            context.bot,
            "<b>تم ربط قناة سجلات الوكلاء</b>\n"
            f"بواسطة: <code>{owner_id}</code>\n"
            f"القناة: {safe_html(channel['title'], 80)} "
            f"(<code>{safe_html(channel['chat_id'], 32)}</code>)",
        )
        suffix = "" if audit_ok else "\nتعذر إرسال رسالة التحقق؛ راجع صلاحيات القناة."
        await message.reply_text(
            f"تم ربط قناة السجلات: {safe_text(channel['title'], 80)}.{suffix}",
            reply_markup=back_keyboard("agentsys:owner", "رجوع لنظام الوكلاء"),
        )
        return True

    if mode == "agent_transfer_member":
        try:
            member_id = int(text)
            if member_id <= 0 or member_id == owner_id:
                raise ValueError
        except ValueError:
            await message.reply_text("أرسل آيدي مستخدم مسجل وصحيح، غير آيدي حسابك.")
            return True
        async with database() as conn:
            member = await fetch_one(
                conn,
                "SELECT telegram_id FROM nabil_members WHERE telegram_id = %s",
                (member_id,),
            )
        if not member:
            context.user_data.clear()
            await message.reply_text(
                "هذا المستخدم غير مسجل في البوت.",
                reply_markup=back_keyboard("agentwallet:home", "رجوع للوحة الوكيل"),
            )
            return True
        context.user_data.update({"member_id": member_id, "mode": "agent_transfer_amount"})
        action = context.user_data.get("agent_operation")
        action_label = "إضافتها" if action == "transfer_add" else "خصمها"
        await message.reply_text(
            f"أرسل مبلغ IQD المراد {action_label}.",
            reply_markup=back_keyboard("agentwallet:home", "رجوع للوحة الوكيل"),
        )
        return True

    if mode == "agent_transfer_amount":
        try:
            amount = money(Decimal(text))
            if amount <= 0 or amount > MAX_AGENT_BALANCE:
                raise ValueError
        except (InvalidOperation, ValueError):
            await message.reply_text("أرسل مبلغ IQD موجباً صالحاً.")
            return True
        operation = context.user_data.get("agent_operation")
        member_id = int(context.user_data["member_id"])
        result = await execute_agent_transfer(owner_id, operation, member_id, amount)
        context.user_data.clear()
        status = result["status"]
        if status != "success":
            errors = {
                "self": "لا يمكن تحويل الرصيد إلى حسابك نفسه.",
                "inactive": "حساب الوكيل غير نشط.",
                "not_member": "المستخدم غير مسجل في البوت.",
                "wallet_low": "رصيد حسابك لا يكفي لإضافة هذا المبلغ.",
                "balance_low": "رصيد المستخدم لا يكفي لهذا الخصم.",
                "range": "الرصيد الناتج يتجاوز الحد المسموح.",
                "invalid": "تعذر تحديد نوع العملية؛ أعد فتح لوحة الوكيل.",
            }
            await message.reply_text(
                errors.get(status, "تعذر تنفيذ التحويل."),
                reply_markup=back_keyboard("agentwallet:home", "رجوع للوحة الوكيل"),
            )
            return True
        action_label = "أضاف" if operation == "transfer_add" else "خصم"
        member_message = (
            f"تم {action_label} {fmt_money(amount)} من رصيدك بواسطة الوكيل.\n"
            f"رصيدك الحالي: {fmt_money(result['member_after'])}."
        )
        try:
            await context.bot.send_message(
                chat_id=member_id, text=member_message
            )
            member_notified = True
        except Exception as exc:
            member_notified = False
            LOG.warning(
                "Could not notify member %s about agent wallet transfer: %s",
                member_id,
                safe_text(exc, 180),
            )
        audit_ok = await send_agent_audit(
            context.bot,
            f"<b>تحويل رصيد بواسطة وكيل</b>\n"
            f"الوكيل: <code>{owner_id}</code>\n"
            f"المستخدم: <code>{member_id}</code>\n"
            f"العملية: {action_label} <b>{fmt_money(amount)}</b>\n"
            f"رصيد الوكيل: {fmt_money(result['wallet_before'])} "
            f"→ {fmt_money(result['wallet_after'])}\n"
            f"رصيد المستخدم: {fmt_money(result['member_before'])} "
            f"→ {fmt_money(result['member_after'])}",
        )
        notes = []
        if not member_notified:
            notes.append("لم يتمكن البوت من إرسال إشعار للمستخدم؛ قد لا يكون قد بدأ البوت.")
        if not audit_ok:
            notes.append("لم تُرسل نسخة لقناة السجلات؛ العملية محفوظة في سجل النظام.")
        suffix = "\n" + "\n".join(notes) if notes else ""
        await message.reply_text(
            f"تمت العملية. رصيدك: {fmt_money(result['wallet_after'])}؛ "
            f"رصيد المستخدم: {fmt_money(result['member_after'])}.{suffix}",
            reply_markup=back_keyboard("agentwallet:home", "رجوع للوحة الوكيل"),
        )
        return True

    return False


async def admin_points_settings(query):
    keys = (
        "member_rush_enabled",
        "daily_balance_reward",
        "daily_balance_reward_max",
        "referral_referrer_balance_reward",
        "referral_invitee_balance_reward",
        "min_balance_transfer",
    )
    values = {key: await get_setting(key) for key in keys}
    enabled = values["member_rush_enabled"].lower() in ("1", "true", "yes", "on")
    try:
        daily_minimum = Decimal(values["daily_balance_reward"])
        daily_maximum = Decimal(values["daily_balance_reward_max"])
        if daily_maximum == 0 and daily_minimum > 0:
            daily_maximum = daily_minimum
        if daily_minimum == 0 and daily_maximum == 0:
            daily_reward_label = "متوقفة"
        elif daily_minimum == daily_maximum:
            daily_reward_label = fmt_money(daily_minimum)
        else:
            daily_reward_label = (
                f"{fmt_money(daily_minimum)} - {fmt_money(daily_maximum)}"
            )
    except (InvalidOperation, ValueError):
        daily_reward_label = "إعداد غير صالح"
    await query.edit_message_text(
        "<b>الرصيد الموحد والمكافآت</b>\n\n"
        f"خدمة رشق الأعضاء: {'مفعّلة' if enabled else 'متوقفة'}\n"
        f"هدية الرصيد اليومية: {daily_reward_label}\n"
        f"مكافأة صاحب الدعوة: {safe_html(values['referral_referrer_balance_reward'], 24)} {safe_html(CURRENCY, 12)}\n"
        f"مكافأة العضو الجديد: {safe_html(values['referral_invitee_balance_reward'], 24)} {safe_html(CURRENCY, 12)}\n"
        f"الحد الأدنى لتحويل الرصيد بين الأعضاء: {safe_html(values['min_balance_transfer'], 30)} {safe_html(CURRENCY, 12)}",
        reply_markup=InlineKeyboardMarkup(
            [
                [InlineKeyboardButton(
                    "إيقاف رشق الأعضاء" if enabled else "تفعيل رشق الأعضاء",
                    callback_data="admin:toggle_member_rush",
                )],
                [InlineKeyboardButton("تعديل نطاق الهدية اليومية", callback_data="setting:daily_balance_reward")],
                [InlineKeyboardButton("تعديل مكافأة صاحب الدعوة", callback_data="setting:referral_referrer_balance_reward")],
                [InlineKeyboardButton("تعديل مكافأة العضو الجديد", callback_data="setting:referral_invitee_balance_reward")],
                [InlineKeyboardButton("إدارة أكواد الهدايا", callback_data="admin:gift_codes")],
                [InlineKeyboardButton("تعديل أقل مبلغ للتحويل", callback_data="setting:min_balance_transfer")],
                [InlineKeyboardButton("رجوع للإعدادات", callback_data="admin:settings")],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


async def admin_gift_codes(query, page: int = 0):
    page = max(0, page)
    async with database() as conn:
        total_row = await fetch_one(
            conn,
            "SELECT COUNT(*) AS total FROM nabil_gift_codes",
        )
        total = int(total_row["total"])
        page_count = max(1, (total + PAGE_SIZE - 1) // PAGE_SIZE)
        page = min(page, page_count - 1)
        rows = await fetch_all(
            conn,
            """
            SELECT g.id, g.code, g.reward, g.max_uses, g.expires_at,
                   COUNT(r.member_id) AS used_count
            FROM nabil_gift_codes AS g
            LEFT JOIN nabil_gift_code_redemptions AS r
              ON r.gift_code_id = g.id
            GROUP BY g.id
            ORDER BY g.id DESC
            LIMIT %s OFFSET %s
            """,
            (PAGE_SIZE, page * PAGE_SIZE),
        )
    lines = [
        "<b>إدارة أكواد الهدايا</b>",
        "كل كود يمنح رصيد IQD، ويُستخدم مرة واحدة لكل شخص.",
    ]
    buttons = [
        [InlineKeyboardButton("إنشاء كود هدية جديد", callback_data="admin:giftcode:add")]
    ]
    for row in rows:
        expiry = (
            row["expires_at"].strftime("%Y-%m-%d %H:%M %Z").strip()
            if row["expires_at"]
            else "بدون انتهاء"
        )
        usage_limit = (
            "غير محدود"
            if int(row["max_uses"]) == 2_147_483_647
            else str(row["max_uses"])
        )
        lines.append(
            f"\n<code>{safe_html(row['code'], 64)}</code> — "
            f"{fmt_money(row['reward'])}\n"
            f"الاستخدامات: {row['used_count']} / {usage_limit} · "
            f"الانتهاء: {safe_html(expiry, 40)}"
        )
        buttons.append(
            [
                InlineKeyboardButton(
                    f"حذف الكود #{row['id']}",
                    callback_data=f"admin:giftcode:delete:{row['id']}",
                )
            ]
        )
    if not rows:
        lines.append("\nماكو أكواد هدايا حالياً.")
    if page_count > 1:
        navigation = []
        if page > 0:
            navigation.append(
                InlineKeyboardButton(
                    "السابق",
                    callback_data=f"admin:gift_codes:{page - 1}",
                )
            )
        if page + 1 < page_count:
            navigation.append(
                InlineKeyboardButton(
                    "التالي",
                    callback_data=f"admin:gift_codes:{page + 1}",
                )
            )
        if navigation:
            buttons.append(navigation)
    buttons.append(
        [InlineKeyboardButton("رجوع لإعدادات الرصيد", callback_data="admin:points_settings")]
    )
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def admin_force_subscription(query):
    async with database() as conn:
        async with conn.transaction():
            channels = await _ensure_required_channels_record(conn)
    enabled = await setting_enabled("require_subscription")
    public_url = (await get_setting("public_channel_url")).strip()
    active_channels = sum(1 for channel in channels if channel["active"])
    lines = [
        "<b>قسم الاشتراك الإجباري</b>",
        f"الحالة العامة: {'مفعّل' if enabled else 'متوقف'}",
        f"القنوات الفعّالة: {active_channels} من أصل {len(channels)}",
        f"قناة البوت العامة: {safe_html(public_url or 'غير مضافة', 160)}",
        "تختفي كل قناة تلقائياً عند اكتمال هدفها.",
    ]
    buttons = []
    for index, channel in enumerate(channels, start=1):
        target_count = channel["target_count"]
        target_text = f"{target_count}" if target_count is not None else "بدون هدف"
        status_text = "فعّالة" if channel["active"] else "اكتمل الهدف"
        username = channel.get("username") or "غير متوفر"
        lines.extend(
            [
                "",
                f"{index}. <b>{safe_html(channel['title'], 80)}</b>",
                f"يوزر القناة: {safe_html(username, 40)}",
                f"المتحققون: {channel['verified_count']} / {target_text} · الحالة: {status_text}",
            ]
        )
        buttons.append(
            [
                InlineKeyboardButton(
                    f"إحصائيات {safe_text(channel['title'], 24)}",
                    callback_data=f"setforce_details:{channel['id']}",
                ),
                InlineKeyboardButton(
                    f"حذف {safe_text(channel['title'], 32)}",
                    callback_data=f"setforce_remove:{channel['id']}",
                )
            ]
        )

    if not channels:
        lines.append("\nلا توجد قنوات مضافة حالياً.")
    buttons.extend(
        [
            [InlineKeyboardButton("إضافة قناة جديدة", callback_data="setforce_add")],
            [InlineKeyboardButton("تحديث القائمة", callback_data="setforce_refresh")],
            [
                InlineKeyboardButton(
                    "إيقاف الاشتراك الإجباري" if enabled else "تفعيل الاشتراك الإجباري",
                    callback_data="admin:toggle_subscription",
                )
            ],
            [InlineKeyboardButton("تعيين قناة البوت العامة", callback_data="setting:public_channel_url")],
            [InlineKeyboardButton("لوحة الإدارة", callback_data="back_admin")],
        ]
    )
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
        disable_web_page_preview=True,
    )


async def admin_special_features(query):
    user = getattr(query, "from_user", None)
    if (
        user
        and is_live_mirror_owner(user.id)
        and not is_owner(user.id)
    ):
        await query.edit_message_text(
            "<b>الميزات الخاصة بالمالك</b>\n\n"
            "إعدادات المرآة الحية وسجل الصندوق الأسود.",
            reply_markup=InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            "📡 إعدادات وتفعيل المرآة الحية",
                            callback_data="admin:live_mirror",
                        )
                    ]
                ]
            ),
            parse_mode=ParseMode.HTML,
        )
        return
    buttons = [
        [
            InlineKeyboardButton(
                "المستثنون من الاشتراك",
                callback_data="admin:subscription_exemptions",
            )
        ],
        [
            InlineKeyboardButton(
                "وضع الصيانة",
                callback_data="admin:maintenance_mode",
            )
        ],
        [
            InlineKeyboardButton(
                "🧹 تنظيف البيانات المؤقتة",
                callback_data="admin:database_cleanup",
            )
        ],
        [InlineKeyboardButton("لوحة الإدارة", callback_data="admin:home")],
    ]
    if user and is_live_mirror_owner(user.id):
        buttons.insert(
            0,
            [
                InlineKeyboardButton(
                    "📡 إعدادات وتفعيل المرآة الحية",
                    callback_data="admin:live_mirror",
                )
            ],
        )
    await query.edit_message_text(
        "<b>قسم الميزات الخاصة</b>\n\n"
        "إدارة الاستثناءات ووصول المستخدمين أثناء الصيانة.",
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def get_live_mirror_config():
    async with database() as conn:
        return await fetch_one(
            conn,
            """
            SELECT owner_id, channel_id, enabled, updated_at
            FROM nabil_live_mirror_config
            WHERE owner_id = %s
            """,
            (LIVE_MIRROR_OWNER_ID,),
        )


async def admin_live_mirror_menu(query):
    config = await get_live_mirror_config()
    if config:
        state = "مفعّلة" if config["enabled"] else "متوقفة"
        channel_label = "القناة المرتبطة"
        try:
            channel = await query.get_bot().get_chat(config["channel_id"])
            username = getattr(channel, "username", None)
            channel_label = (
                f"<code>@{safe_html(username, 32)}</code>"
                if username
                else "قناة خاصة بدون يوزر عام"
            )
        except Exception as exc:
            LOG.info(
                "Could not resolve live mirror channel username (%s).",
                type(exc).__name__,
            )
        details = (
            f"الحالة: <b>{state}</b>\n"
            f"القناة: {channel_label}\n"
            f"آخر تحديث: <code>{config['updated_at'].strftime('%Y-%m-%d %H:%M')}</code>\n\n"
            "تُحفظ الأحداث في سجل PostgreSQL حتى عند إيقاف إرسال التنبيهات."
        )
        toggle_label = "إيقاف المرآة" if config["enabled"] else "تفعيل المرآة"
        toggle_callback = "admin:live_mirror:toggle"
    else:
        details = (
            "لم تُربط قناة مراقبة بعد.\n\n"
            "أرسل يوزر قناة عامة مثل <code>@channelname</code> أو رابطها. "
            "للقناة الخاصة التي لا تملك يوزراً، أرسل معرّف القناة الصحيح الذي يبدأ بـ -100. "
            "يجب إضافة البوت مشرفاً مع صلاحية النشر."
        )
        toggle_label = None
        toggle_callback = None
    rows = [
        [
            InlineKeyboardButton(
                "تعيين أو تحديث القناة",
                callback_data="admin:live_mirror:set",
            )
        ],
        [
            InlineKeyboardButton(
                "سجل الصندوق الأسود",
                callback_data="admin:live_mirror:logs:0",
            )
        ],
    ]
    if toggle_label and toggle_callback:
        rows.insert(
            1,
            [InlineKeyboardButton(toggle_label, callback_data=toggle_callback)],
        )
    rows.append(
        [InlineKeyboardButton("رجوع للميزات الخاصة", callback_data="admin:special_features")]
    )
    await query.edit_message_text(
        "<b>المرآة الحية والصندوق الأسود</b>\n\n" + details,
        reply_markup=InlineKeyboardMarkup(rows),
        parse_mode=ParseMode.HTML,
    )


async def admin_live_mirror_logs(query, page: int = 0):
    page = max(0, page)
    page_size = 10
    async with database() as conn:
        totals = await fetch_one(
            conn, "SELECT COUNT(*) AS total FROM nabil_live_mirror_events"
        )
        events = await fetch_all(
            conn,
            """
            SELECT id, event_type, payload, status, created_at
            FROM nabil_live_mirror_events
            ORDER BY id DESC
            LIMIT %s OFFSET %s
            """,
            (page_size, page * page_size),
        )
    total = int(totals["total"] or 0) if totals else 0
    if not events:
        text = "<b>سجل الصندوق الأسود</b>\n\nلا توجد أحداث محفوظة بعد."
    else:
        lines = ["<b>سجل الصندوق الأسود</b>"]
        lines.extend(format_live_mirror_archive_line(event) for event in events)
        text = "\n\n".join(lines)
    buttons = []
    navigation = []
    if page > 0:
        navigation.append(
            InlineKeyboardButton(
                "الأحدث", callback_data=f"admin:live_mirror:logs:{page - 1}"
            )
        )
    if (page + 1) * page_size < total:
        navigation.append(
            InlineKeyboardButton(
                "الأقدم", callback_data=f"admin:live_mirror:logs:{page + 1}"
            )
        )
    if navigation:
        buttons.append(navigation)
    buttons.append(
        [InlineKeyboardButton("رجوع لإعدادات المرآة", callback_data="admin:live_mirror")]
    )
    await query.edit_message_text(
        text,
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def save_live_mirror_channel(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str):
    message = update.effective_message
    user = update.effective_user
    if not message or not user or not is_live_mirror_owner(user.id):
        context.user_data.clear()
        return
    if text.strip().lower() in {"مسح", "حذف", "clear", "off"}:
        async with database() as conn:
            async with conn.transaction():
                removed = await fetch_one(
                    conn,
                    """
                    DELETE FROM nabil_live_mirror_config
                    WHERE owner_id = %s
                    RETURNING channel_id
                    """,
                    (LIVE_MIRROR_OWNER_ID,),
                )
                await conn.execute(
                    """
                    UPDATE nabil_live_mirror_events
                    SET status = 'archived', claimed_at = NULL
                    WHERE status = 'pending'
                    """
                )
        await log_admin_action(
            user.id,
            "إزالة قناة المرآة الحية",
            details=(
                f"القناة السابقة: {removed['channel_id']}"
                if removed
                else "لم تكن هناك قناة مرتبطة"
            ),
        )
        context.user_data.clear()
        await message.reply_text(
            "تم فصل قناة المرآة. ستبقى الأحداث محفوظة في سجل الصندوق الأسود.",
            reply_markup=back_keyboard("admin:live_mirror", "رجوع لإعدادات المرآة"),
        )
        return

    channel_reference = parse_live_mirror_channel_reference(text)
    if channel_reference is None:
        await message.reply_text(
            "المدخل غير صالح. أرسل يوزر القناة مثل <code>@channelname</code> "
            "أو رابطاً مثل <code>https://t.me/channelname</code>. "
            "للقناة الخاصة بلا يوزر، أرسل معرّفها الذي يبدأ بـ <code>-100</code>. "
            "أرسل «مسح» لفصل القناة.",
            parse_mode=ParseMode.HTML,
        )
        return
    try:
        channel = await resolve_live_mirror_channel(
            context.bot, channel_reference
        )
    except ValueError as exc:
        await message.reply_text(
            f"تعذر اعتماد القناة: {safe_text(exc, 160)}"
        )
        return
    except Exception as exc:
        LOG.warning(
            "Could not validate live mirror channel (%s).",
            type(exc).__name__,
        )
        await message.reply_text(
            "تعذر الوصول إلى القناة. تأكد من كتابة يوزر قناة صحيح، "
            "أو معرّف قناة خاصة يبدأ بـ -100، ثم أضف البوت مشرفاً بصلاحية النشر."
        )
        return

    try:
        await context.bot.send_message(
            chat_id=channel.id,
            text="تم ربط قناة المراقبة بالمرآة الحية والصندوق الأسود.",
        )
    except Exception as exc:
        LOG.warning(
            "Live mirror channel test message failed (%s).",
            type(exc).__name__,
        )
        await message.reply_text(
            "تعذر إرسال رسالة الاختبار، لذلك لم تُحفظ القناة. "
            "تحقق من صلاحية البوت في النشر ثم أعد المحاولة."
        )
        return

    async with database() as conn:
        async with conn.transaction():
            await conn.execute(
                """
                UPDATE nabil_live_mirror_events
                SET status = 'archived', claimed_at = NULL
                WHERE status = 'pending'
                """
            )
            await conn.execute(
                """
                INSERT INTO nabil_live_mirror_config
                  (owner_id, channel_id, enabled, updated_by, updated_at)
                VALUES (%s, %s, TRUE, %s, NOW())
                ON CONFLICT (owner_id) DO UPDATE
                SET channel_id = EXCLUDED.channel_id,
                    enabled = TRUE,
                    updated_by = EXCLUDED.updated_by,
                    updated_at = NOW()
                """,
                (LIVE_MIRROR_OWNER_ID, channel.id, LIVE_MIRROR_OWNER_ID),
            )
    await log_admin_action(
        user.id,
        "تحديث قناة المرآة الحية",
        target_id=channel.id,
    )
    context.user_data.clear()
    await message.reply_text(
        "تم حفظ القناة والتحقق من صلاحية النشر. المرآة الحية مفعّلة.",
        reply_markup=back_keyboard("admin:live_mirror", "رجوع لإعدادات المرآة"),
    )


async def clean_expired_transient_rows() -> tuple[int, int]:
    async with database() as conn:
        async with conn.transaction():
            old_protection_rows = await fetch_all(
                conn,
                """
                DELETE FROM nabil_order_protection
                WHERE COALESCE(
                    GREATEST(
                        last_submission_at,
                        invalid_window_started_at,
                        blocked_until
                    ),
                    '-infinity'::TIMESTAMPTZ
                ) < NOW() - (%s * INTERVAL '1 day')
                RETURNING telegram_id
                """,
                (ORDER_PROTECTION_RETENTION_DAYS,),
            )
            expired_challenge_rows = await fetch_all(
                conn,
                """
                UPDATE nabil_human_verifications
                SET verification_code_hash = NULL,
                    code_expires_at = NULL,
                    failed_attempts = 0
                WHERE verified_at IS NULL
                  AND verification_code_hash IS NOT NULL
                  AND code_expires_at
                      < NOW() - (%s * INTERVAL '1 hour')
                RETURNING telegram_id
                """,
                (EXPIRED_VERIFICATION_CODE_RETENTION_HOURS,),
            )
    return len(old_protection_rows), len(expired_challenge_rows)


async def vacuum_transient_tables():
    connection = await psycopg.AsyncConnection.connect(
        DATABASE_URL,
        row_factory=dict_row,
        connect_timeout=12,
        autocommit=True,
    )
    async with connection:
        await connection.execute(
            "VACUUM (ANALYZE) public.nabil_order_protection"
        )
        await connection.execute(
            "VACUUM (ANALYZE) public.nabil_human_verifications"
        )


async def admin_database_cleanup_confirmation(query):
    await query.edit_message_text(
        "<b>تنظيف البيانات المؤقتة</b>\n\n"
        f"سيتم حذف سجلات حماية الطلبات ومحاولات السبام التي لم تتغير منذ "
        f"{ORDER_PROTECTION_RETENTION_DAYS} يوم، ومسح رموز التحقق المنتهية "
        f"منذ أكثر من {EXPIRED_VERIFICATION_CODE_RETENTION_HOURS} ساعة.\n\n"
        "ثم تُحدّث إحصائيات جدولي الحماية والتحقق باستخدام "
        "<code>VACUUM (ANALYZE)</code>.\n\n"
        "<b>لن تُحذف الطلبات أو الأرصدة أو سجل الحركات أو سجل الإدارة "
        "أو سجلات المزود.</b>\n"
        "الصيانة تتيح إعادة استخدام المساحة وتحدّث الإحصائيات، لكنها لا "
        "تضمن تقليل حجم قاعدة البيانات أو زيادة السرعة.",
        reply_markup=InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton(
                        "تنفيذ التنظيف",
                        callback_data="admin:database_cleanup:run",
                    )
                ],
                [
                    InlineKeyboardButton(
                        "إلغاء والرجوع",
                        callback_data="admin:special_features",
                    )
                ],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


async def execute_admin_database_cleanup(query, user_id: int):
    await query.edit_message_text("جارٍ تنظيف البيانات المؤقتة وصيانة الجداول…")
    try:
        protection_count, challenge_count = await clean_expired_transient_rows()
    except Exception as exc:
        LOG.warning(
            "Temporary database cleanup failed (%s).", type(exc).__name__
        )
        await query.edit_message_text(
            "تعذر إكمال تنظيف البيانات المؤقتة. لم تكتمل عملية الحذف؛ "
            "حاول لاحقاً أو راجع سجل التنبيهات.",
            reply_markup=back_keyboard(
                "admin:special_features", "رجوع للميزات الخاصة"
            ),
        )
        return

    vacuum_succeeded = True
    try:
        await vacuum_transient_tables()
    except Exception as exc:
        vacuum_succeeded = False
        LOG.warning(
            "VACUUM ANALYZE for temporary tables failed (%s).",
            type(exc).__name__,
        )

    try:
        await log_admin_action(
            user_id,
            "تنظيف البيانات المؤقتة",
            details=(
                f"سجلات حماية محذوفة: {protection_count}; "
                f"رموز تحقق منتهية ممسوحة: {challenge_count}; "
                f"VACUUM ANALYZE: {'نجح' if vacuum_succeeded else 'تعذر'}"
            ),
        )
    except Exception as exc:
        LOG.warning(
            "Could not audit temporary database cleanup (%s).",
            type(exc).__name__,
        )

    result = (
        "<b>اكتمل تنظيف البيانات المؤقتة.</b>\n\n"
        f"سجلات حماية قديمة محذوفة: <b>{protection_count}</b>\n"
        f"رموز تحقق منتهية ممسوحة: <b>{challenge_count}</b>\n"
    )
    if vacuum_succeeded:
        result += (
            "تم تحديث إحصائيات جدولي الحماية والتحقق بنجاح.\n"
            "لم يتم حذف الطلبات أو الأرصدة أو سجلات العمليات."
        )
    else:
        result += (
            "تعذر تشغيل صيانة VACUUM ANALYZE؛ تم تنظيف السجلات المؤقتة "
            "فقط. لم يتم حذف الطلبات أو الأرصدة أو سجلات العمليات."
        )
    await query.edit_message_text(
        result,
        reply_markup=InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton(
                        "رجوع للميزات الخاصة",
                        callback_data="admin:special_features",
                    )
                ],
                [InlineKeyboardButton("لوحة الإدارة", callback_data="admin:home")],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


async def admin_maintenance_mode(query):
    enabled = await setting_enabled("bot_enabled")
    maintenance_text = safe_html(await get_setting("maintenance_text"), 1200)
    if enabled:
        status = "🟢 يعمل"
        details = (
            "البوت متاح للمستخدمين حالياً. عند تفعيل الصيانة، "
            "لن يتمكن المستخدمون من استخدام خدماته، وتبقى لوحة الإدارة متاحة."
        )
        action_label = "تفعيل وضع الصيانة"
    else:
        status = "🔴 الصيانة مفعّلة"
        details = (
            "الخدمات متوقفة عن المستخدمين حالياً، وتبقى لوحة الإدارة متاحة. "
            "الرسالة التي تظهر لهم:"
        )
        action_label = "إلغاء الصيانة وتشغيل البوت"

    await query.edit_message_text(
        "<b>وضع الصيانة</b>\n\n"
        f"الحالة الحالية: <b>{status}</b>\n\n"
        f"{details}\n\n"
        f"<blockquote>{maintenance_text}</blockquote>",
        reply_markup=InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton(
                        action_label,
                        callback_data="admin:toggle_bot:special",
                    )
                ],
                [
                    InlineKeyboardButton(
                        "تعديل رسالة الصيانة",
                        callback_data="setting:maintenance_text",
                    )
                ],
                [
                    InlineKeyboardButton(
                        "رجوع للميزات الخاصة",
                        callback_data="admin:special_features",
                    )
                ],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


async def admin_subscription_exemptions(query, page: int = 0):
    async with database() as conn:
        count_row = await fetch_one(
            conn,
            "SELECT COUNT(*) AS total FROM nabil_subscription_exemptions",
        )
        total = int(count_row["total"] if count_row else 0)
        page_size = SUBSCRIPTION_EXEMPTION_PAGE_SIZE
        max_page = max(0, (total - 1) // page_size)
        page = min(max(0, page), max_page)
        rows = await fetch_all(
            conn,
            """
            SELECT telegram_id
            FROM nabil_subscription_exemptions
            ORDER BY created_at DESC, telegram_id DESC
            LIMIT %s OFFSET %s
            """,
            (page_size, page * page_size),
        )

    lines = [
        "<b>المستثنون من الاشتراك</b>",
        f"عدد الحسابات المستثناة: {total}",
        "الاستثناء يتجاوز الاشتراك الإجباري فقط.",
    ]
    buttons = []
    for row in rows:
        telegram_id = int(row["telegram_id"])
        lines.append(f"\nالحساب: <code>{telegram_id}</code>")
        buttons.append(
            [
                InlineKeyboardButton(
                    f"آيدي {telegram_id}",
                    callback_data="admin:subscription_exemptions:id",
                ),
                InlineKeyboardButton(
                    "حذف",
                    callback_data=f"admin:subscription_exemptions:remove:{telegram_id}",
                ),
            ]
        )
    if not rows:
        lines.append("\nماكو حسابات مستثناة حالياً.")

    buttons.append(
        [
            InlineKeyboardButton(
                "إضافة شخص",
                callback_data="admin:subscription_exemptions:add",
            ),
            InlineKeyboardButton(
                "تحديث القائمة",
                callback_data=f"admin:subscription_exemptions:page:{page}",
            ),
        ]
    )
    if max_page:
        page_buttons = []
        if page > 0:
            page_buttons.append(
                InlineKeyboardButton(
                    "السابق",
                    callback_data=f"admin:subscription_exemptions:page:{page - 1}",
                )
            )
        if page < max_page:
            page_buttons.append(
                InlineKeyboardButton(
                    "التالي",
                    callback_data=f"admin:subscription_exemptions:page:{page + 1}",
                )
            )
        buttons.append(page_buttons)
        lines.append(f"\nالصفحة {page + 1} من {max_page + 1}")
    buttons.extend(
        [
            [
                InlineKeyboardButton(
                    "رجوع للميزات الخاصة",
                    callback_data="admin:special_features",
                )
            ],
            [InlineKeyboardButton("لوحة الإدارة", callback_data="admin:home")],
        ]
    )
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def show_required_channel_details(query, context, channel):
    username = channel.get("username") or "غير متوفر"
    target_count = channel.get("target_count")
    target_text = f"{target_count}" if target_count is not None else "بدون هدف"
    verified_count = int(channel.get("verified_count", 0))
    remaining = max(0, target_count - verified_count) if target_count else None
    try:
        member_count = await context.bot.get_chat_member_count(channel["chat_id"])
        member_count_text = f"{member_count}"
    except Exception as exc:
        LOG.warning(
            "Could not get member count for required channel %s: %s",
            safe_text(channel.get("chat_id", ""), 80),
            safe_text(exc, 160),
        )
        member_count_text = "غير متاح"
    status_text = "فعّالة" if channel["active"] else "اكتمل العدد المطلوب"
    lines = [
        "<b>إحصائيات القناة الإلزامية</b>",
        "تمت الموافقة على القناة وإضافتها للاشتراك الإجباري.",
        f"الاسم: {safe_html(channel['title'], 100)}",
        f"يوزر القناة: {safe_html(username, 40)}",
        f"معرّف القناة: <code>{safe_html(channel['chat_id'], 40)}</code>",
        f"رابط الانضمام: {safe_html(channel.get('join_url') or 'غير متوفر', 180)}",
        f"أعضاء القناة حالياً: {member_count_text}",
        f"العدد المطلوب: {target_text}",
        f"الذين تحقق البوت من اشتراكهم: {verified_count}",
    ]
    if remaining is not None:
        lines.append(f"المتبقي لإكمال الهدف: {remaining}")
    lines.append(f"الحالة: {status_text}")

    buttons = []
    if channel.get("join_url"):
        buttons.append(
            [InlineKeyboardButton("فتح القناة", url=channel["join_url"])]
        )
    buttons.extend(
        [
            [
                InlineKeyboardButton(
                    "حذف القناة من الاشتراك",
                    callback_data=f"setforce_remove:{channel['id']}",
                )
            ],
            [
                InlineKeyboardButton(
                    "رجوع لقسم الاشتراك الإجباري",
                    callback_data="admin:force_subscription",
                )
            ],
        ]
    )
    await query.edit_message_text(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
        disable_web_page_preview=True,
    )


async def admin_channel_settings(query):
    await admin_force_subscription(query)


async def admin_copy_settings(query):
    welcome = await get_setting("welcome_text")
    help_text = await get_setting("help_text")
    maintenance = await get_setting("maintenance_text")
    await query.edit_message_text(
        "<b>تعديل النصوص والرسائل</b>\n\n"
        f"رسالة البداية:\n{safe_html(welcome, 500)}\n\n"
        f"المساعدة:\n{safe_html(help_text, 500)}\n\n"
        f"رسالة إيقاف البوت:\n{safe_html(maintenance, 300)}\n\n"
        "في رسالة البداية استخدم {name} للاسم و{id} للآيدي.",
        reply_markup=InlineKeyboardMarkup(
            [
                [InlineKeyboardButton("تعديل رسالة البداية", callback_data="setting:welcome_text")],
                [InlineKeyboardButton("تعديل رسالة المساعدة", callback_data="setting:help_text")],
                [InlineKeyboardButton("تعديل رسالة الصيانة", callback_data="setting:maintenance_text")],
                [InlineKeyboardButton("رجوع للوحة", callback_data="admin:home")],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


def broadcast_content_type(message) -> str | None:
    if message.text is not None:
        return "نص"
    for attribute, label in (
        ("photo", "صورة"),
        ("video", "فيديو"),
        ("document", "ملف"),
        ("animation", "صورة متحركة"),
        ("audio", "ملف صوتي"),
        ("voice", "بصمة صوتية"),
        ("video_note", "فيديو دائري"),
        ("sticker", "ملصق"),
        ("contact", "جهة اتصال"),
        ("location", "موقع"),
        ("venue", "مكان"),
        ("poll", "استطلاع"),
        ("dice", "رسالة تفاعلية"),
    ):
        if getattr(message, attribute, None) is not None:
            return label
    return None


async def get_broadcast_delay() -> float:
    delay = float(await get_setting("broadcast_delay_seconds"))
    if not BROADCAST_DELAY_MIN <= delay <= BROADCAST_DELAY_MAX:
        raise ValueError("Broadcast delay is outside the allowed range.")
    return delay


async def admin_broadcast_menu(query):
    delay = await get_broadcast_delay()
    buttons = [
        [InlineKeyboardButton("إنشاء إذاعة", callback_data="admin:broadcast:start")]
    ]
    if is_owner(query.from_user.id):
        buttons.append(
            [
                InlineKeyboardButton(
                    "تعديل الفاصل الزمني",
                    callback_data="admin:broadcast:delay",
                )
            ]
        )
    buttons.append(
        [InlineKeyboardButton("رجوع للوحة الأدمن", callback_data="admin:home")]
    )
    await query.edit_message_text(
        "<b>قسم الإذاعة</b>\n\n"
        "تستهدف الإذاعة المستخدمين المسجلين في البوت.\n"
        f"الفاصل بين الرسائل: <b>{delay:g}</b> ثانية.",
        reply_markup=InlineKeyboardMarkup(buttons),
        parse_mode=ParseMode.HTML,
    )


async def begin_broadcast(query, context: ContextTypes.DEFAULT_TYPE):
    if not query.message or query.message.chat.type != "private":
        await query.edit_message_text(
            "ابدأ الإذاعة من المحادثة الخاصة مع البوت حفاظاً على سرية محتواها.",
            reply_markup=back_keyboard("admin:home", "رجوع للوحة"),
        )
        return
    context.user_data.clear()
    context.user_data["mode"] = "broadcast_content"
    await query.edit_message_text(
        "أرسل أو وجّه إلى البوت الرسالة التي تريد إذاعتها. "
        "يمكن أن تكون نصاً أو صورة أو فيديو أو ملفاً أو صوتاً أو ملصقاً؛ "
        "سيتم نسخها كما هي للمستخدمين.",
        reply_markup=back_keyboard("admin:broadcast", "رجوع لقسم الإذاعة"),
    )


def broadcast_confirmation_keyboard(context: ContextTypes.DEFAULT_TYPE):
    buttons = [
        [InlineKeyboardButton("إرسال الإذاعة", callback_data="admin:broadcast:send")]
    ]
    button_label = context.user_data.get("broadcast_button_label")
    if button_label:
        buttons.append(
            [
                InlineKeyboardButton(
                    "تعديل الزر", callback_data="admin:broadcast:button:add"
                ),
                InlineKeyboardButton(
                    "إزالة الزر", callback_data="admin:broadcast:button:remove"
                ),
            ]
        )
    else:
        buttons.append(
            [InlineKeyboardButton("إضافة زر", callback_data="admin:broadcast:button:add")]
        )
    buttons.append([InlineKeyboardButton("إلغاء", callback_data="admin:cancel")])
    return InlineKeyboardMarkup(buttons)


def broadcast_confirmation_text(
    context: ContextTypes.DEFAULT_TYPE, total_users: int, delay: float
) -> str:
    content_type = safe_html(context.user_data.get("broadcast_content_type", "رسالة"), 40)
    preview = safe_html(context.user_data.get("broadcast_preview", ""), 900)
    lines = [
        "<b>معاينة الإذاعة</b>",
        f"نوع المحتوى: {content_type}",
        f"المستهدفون المسجلون: {total_users}",
        f"الفاصل: {delay:g} ثانية بين الرسائل",
        "راجع الرسالة الأصلية أعلاه للتأكد من الوسائط والمحتوى.",
    ]
    if preview:
        lines.extend(["", "النص أو الوصف:", preview])
    button_label = context.user_data.get("broadcast_button_label")
    button_url = context.user_data.get("broadcast_button_url")
    if button_label and button_url:
        lines.extend(
            [
                "",
                f"الزر: {safe_html(button_label, 64)} → "
                f"{safe_html(button_url, 400)}",
            ]
        )
    lines.extend(["", "هل تريد بدء الإذاعة؟"])
    return "\n".join(lines)


async def show_broadcast_confirmation(query, context: ContextTypes.DEFAULT_TYPE):
    if not (
        context.user_data.get("broadcast_source_chat_id")
        and context.user_data.get("broadcast_source_message_id")
    ):
        await query.edit_message_text(
            "انتهت جلسة الإذاعة. ابدأ من جديد.",
            reply_markup=back_keyboard("admin:broadcast", "رجوع لقسم الإذاعة"),
        )
        return
    async with database() as conn:
        count_row = await fetch_one(conn, "SELECT COUNT(*) AS total FROM nabil_members")
    total = int(count_row["total"] or 0)
    delay = await get_broadcast_delay()
    context.user_data["mode"] = "broadcast_confirm"
    await query.edit_message_text(
        broadcast_confirmation_text(context, total, delay),
        reply_markup=broadcast_confirmation_keyboard(context),
        parse_mode=ParseMode.HTML,
    )


async def reply_broadcast_confirmation(message, context: ContextTypes.DEFAULT_TYPE):
    async with database() as conn:
        count_row = await fetch_one(conn, "SELECT COUNT(*) AS total FROM nabil_members")
    total = int(count_row["total"] or 0)
    delay = await get_broadcast_delay()
    context.user_data["mode"] = "broadcast_confirm"
    await message.reply_text(
        broadcast_confirmation_text(context, total, delay),
        reply_markup=broadcast_confirmation_keyboard(context),
        parse_mode=ParseMode.HTML,
    )


async def capture_broadcast_content(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.effective_message
    user = update.effective_user
    if (
        not message
        or not user
        or context.user_data.get("mode")
        not in {"broadcast_content", "broadcast_text"}
    ):
        return
    if not update.effective_chat or update.effective_chat.type != "private":
        context.user_data.clear()
        await message.reply_text(
            "أرسل محتوى الإذاعة في المحادثة الخاصة مع البوت."
        )
        return
    if not await is_admin_user(user.id) or not await has_admin_permission(user.id, "broadcast"):
        context.user_data.clear()
        await message.reply_text("لا تملك صلاحية إدارة الإذاعة.")
        return
    content_type = broadcast_content_type(message)
    if content_type is None:
        await message.reply_text(
            "هذا النوع من الرسائل لا يمكن نسخه. أرسل نصاً أو صورة أو فيديو أو ملفاً أو صوتاً أو ملصقاً."
        )
        return
    context.user_data.update(
        {
            "broadcast_source_chat_id": message.chat_id,
            "broadcast_source_message_id": message.message_id,
            "broadcast_content_type": content_type,
            "broadcast_preview": message.text or message.caption or "",
            "mode": "broadcast_options",
        }
    )
    await message.reply_text(
        "تم حفظ المحتوى. يمكنك إضافة زر تفاعلي اختياري، أو المتابعة بدونه.",
        reply_markup=InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton(
                        "متابعة دون زر", callback_data="admin:broadcast:preview"
                    ),
                    InlineKeyboardButton(
                        "إضافة زر", callback_data="admin:broadcast:button:add"
                    ),
                ],
                [InlineKeyboardButton("إلغاء", callback_data="admin:cancel")],
            ]
        ),
    )


async def edit_broadcast_progress(query, text: str, reply_markup=None):
    try:
        await query.edit_message_text(text, reply_markup=reply_markup)
        return True
    except Exception as exc:
        LOG.debug("Could not update broadcast progress: %s", safe_text(exc, 160))
        return False


async def deliver_broadcast_copy(
    bot,
    recipient_id: int,
    source_chat_id: int,
    source_message_id: int,
    reply_markup,
) -> bool:
    retries = 0
    while True:
        try:
            await bot.copy_message(
                chat_id=recipient_id,
                from_chat_id=source_chat_id,
                message_id=source_message_id,
                reply_markup=reply_markup,
            )
            return True
        except RetryAfter as exc:
            if retries >= 3:
                LOG.info("Broadcast delivery stopped after repeated rate limits.")
                return False
            retries += 1
            await asyncio.sleep(max(1.0, float(exc.retry_after)))
        except NetworkError as exc:
            if retries >= 2:
                LOG.info("Broadcast delivery failed after network retries: %s", safe_text(exc, 160))
                return False
            retries += 1
            await asyncio.sleep(float(retries))
        except (Forbidden, BadRequest) as exc:
            LOG.info("Broadcast recipient is unavailable: %s", safe_text(exc, 160))
            return False
        except Exception as exc:
            LOG.warning("Broadcast delivery failed: %s", safe_text(exc, 160))
            return False


async def run_broadcast(query, context: ContextTypes.DEFAULT_TYPE, actor_id: int):
    if (
        context.user_data.get("mode") != "broadcast_confirm"
        or not context.user_data.get("broadcast_source_chat_id")
        or not context.user_data.get("broadcast_source_message_id")
    ):
        context.user_data.clear()
        await query.edit_message_text(
            "انتهت جلسة الإذاعة. ابدأ من جديد.",
            reply_markup=back_keyboard("admin:broadcast", "رجوع لقسم الإذاعة"),
        )
        return
    if BROADCAST_LOCK.locked():
        await query.edit_message_text(
            "هناك إذاعة أخرى قيد الإرسال. حاول بعد اكتمالها.",
            reply_markup=back_keyboard("admin:broadcast", "رجوع لقسم الإذاعة"),
        )
        return
    await BROADCAST_LOCK.acquire()
    try:
        if context.user_data.get("mode") != "broadcast_confirm":
            await query.edit_message_text(
                "انتهت جلسة الإذاعة. ابدأ من جديد.",
                reply_markup=back_keyboard("admin:broadcast", "رجوع لقسم الإذاعة"),
            )
            return
        async with database() as conn:
            recipients = await fetch_all(
                conn,
                "SELECT telegram_id FROM nabil_members ORDER BY telegram_id",
            )
        total = len(recipients)
        delay = await get_broadcast_delay()
        source_chat_id = int(context.user_data["broadcast_source_chat_id"])
        source_message_id = int(context.user_data["broadcast_source_message_id"])
        button_label = context.user_data.get("broadcast_button_label")
        button_url = context.user_data.get("broadcast_button_url")
        reply_markup = (
            InlineKeyboardMarkup(
                [[InlineKeyboardButton(button_label, url=button_url)]]
            )
            if button_label and button_url
            else None
        )
        content_type = safe_text(
            context.user_data.get("broadcast_content_type", "رسالة"), 40
        )
        context.user_data["mode"] = "broadcast_sending"
        sent = failed = processed = 0
        progress_step = max(10, total // 100)
        await edit_broadcast_progress(
            query,
            f"جاري إرسال الإذاعة...\n"
            f"النوع: {content_type}\n"
            f"المعالجة: 0/{total}\nالنجاح: 0\nالفشل: 0",
        )
        for recipient in recipients:
            delivered = await deliver_broadcast_copy(
                context.bot,
                int(recipient["telegram_id"]),
                source_chat_id,
                source_message_id,
                reply_markup,
            )
            if delivered:
                sent += 1
            else:
                failed += 1
            processed += 1
            if processed % progress_step == 0 or processed == total:
                await edit_broadcast_progress(
                    query,
                    f"جاري إرسال الإذاعة...\n"
                    f"النوع: {content_type}\n"
                    f"المعالجة: {processed}/{total}\n"
                    f"النجاح: {sent}\nالفشل: {failed}",
                )
            if processed < total and delay > 0:
                await asyncio.sleep(delay)

        audit_warning = ""
        try:
            await log_admin_action(
                actor_id,
                "إرسال إذاعة",
                details=(
                    f"النوع: {content_type} | الإجمالي: {total} | "
                    f"نجاح: {sent} | فشل: {failed} | "
                    f"الفاصل: {delay:g} ثانية | "
                    f"زر: {safe_text(button_label, 64) if button_label else 'بدون'}"
                ),
            )
        except Exception as exc:
            LOG.warning("Could not save broadcast audit entry: %s", safe_text(exc, 180))
            audit_warning = "\nتعذر حفظ سجل الإذاعة في سجل الأدمن."
        context.user_data.clear()
        report = (
            "اكتملت الإذاعة.\n"
            f"إجمالي المستخدمين: {total}\n"
            f"النجاح ✅: {sent}\n"
            f"الفشل (محظور أو غير متاح) ❌: {failed}\n"
            f"الفاصل الزمني: {delay:g} ثانية."
            f"{audit_warning}"
        )
        final_markup = InlineKeyboardMarkup(
            [
                [InlineKeyboardButton("قسم الإذاعة", callback_data="admin:broadcast")],
                [InlineKeyboardButton("لوحة الأدمن", callback_data="admin:home")],
            ]
        )
        edited = await edit_broadcast_progress(
            query,
            report,
            final_markup,
        )
        if not edited and query.message:
            try:
                await query.message.reply_text(report, reply_markup=final_markup)
            except Exception as exc:
                LOG.warning(
                    "Could not post final broadcast report: %s",
                    safe_text(exc, 160),
                )
    finally:
        BROADCAST_LOCK.release()


async def admin_settings(query):
    developer_name = safe_html(safe_text(query.from_user.first_name, 60), 60)
    await query.edit_message_text(
        f"<b>- مرحباً عزيزي المطور {developer_name} 🔥</b>\n\n"
        "- يمكن للعضو إرسال <code>/id</code> لإرسال الآيدي الخاص به",
        reply_markup=InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton(
                        "رصيد المستخدم 💰", callback_data="admin:wallet"
                    )
                ],
                [InlineKeyboardButton("معلومات مستخدم 🔎", callback_data="admin:members")],
                [InlineKeyboardButton("إعداد مزود الرشق", callback_data="admin:providers")],
                [InlineKeyboardButton("سجل عمليات الأدمن", callback_data="admin:audit")],
                [
                    InlineKeyboardButton("مشاهدات والتفاعلات", callback_data="admin:services:engagement:0"),
                ],
                [
                    InlineKeyboardButton("رصيد IQD والمكافآت 🎁", callback_data="admin:points_settings")
                ],
                [
                    InlineKeyboardButton("النصوص 📝", callback_data="admin:copy"),
                    InlineKeyboardButton("قناة البوت 📢", callback_data="admin:channel"),
                ],
                [InlineKeyboardButton("إدارة الوكلاء 🛡️", callback_data="admin:agents")],
                [InlineKeyboardButton("رجوع للوحة الأدمن 🔙", callback_data="admin:home")],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


async def admin_bot_settings(query):
    bot_enabled = await setting_enabled("bot_enabled")
    alerts_enabled = await setting_enabled("login_alerts_enabled")
    await query.edit_message_text(
        "<b>تشغيل البوت والتنبيهات</b>\n\n"
        f"البوت: {'يعمل' if bot_enabled else 'متوقف مؤقتاً'}\n"
        f"تنبيه تسجيل عضو جديد: {'مفعّل' if alerts_enabled else 'متوقف'}",
        reply_markup=InlineKeyboardMarkup(
            [
                [InlineKeyboardButton(
                    "إيقاف البوت" if bot_enabled else "تشغيل البوت",
                    callback_data="admin:toggle_bot",
                )],
                [InlineKeyboardButton(
                    "إيقاف إشعار الدخول" if alerts_enabled else "تشغيل إشعار الدخول",
                    callback_data="admin:toggle_alerts",
                )],
                [InlineKeyboardButton("تعديل رسالة الصيانة", callback_data="setting:maintenance_text")],
                [InlineKeyboardButton("رجوع للإعدادات", callback_data="admin:settings")],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


async def show_agent_permissions(query, agent_id: int):
    async with database() as conn:
        agent = await fetch_one(
            conn,
            """
            SELECT a.telegram_id, p.can_orders, p.can_members, p.can_wallet,
                   p.can_reports, p.can_services, p.can_broadcast,
                   p.can_force_subscription
            FROM nabil_bot_admins a
            LEFT JOIN nabil_bot_admin_permissions p ON p.telegram_id = a.telegram_id
            WHERE a.telegram_id = %s
            """,
            (agent_id,),
        )
    if not agent:
        await query.edit_message_text(
            "الأدمن غير موجود.",
            reply_markup=back_keyboard("admin:agents", "رجوع لإدارة الأدمنية"),
        )
        return

    rows = []
    permission_keys = list(ADMIN_PERMISSION_COLUMNS)
    for index in range(0, len(permission_keys), 2):
        row_buttons = []
        for permission in permission_keys[index:index + 2]:
            enabled = bool(agent.get(ADMIN_PERMISSION_COLUMNS[permission]))
            row_buttons.append(
                InlineKeyboardButton(
                    f"{'✅' if enabled else '⛔'} {ADMIN_PERMISSION_LABELS[permission]}",
                    callback_data=f"agent:permission:{agent_id}:{permission}",
                )
            )
        rows.append(row_buttons)
    rows.append(
        [InlineKeyboardButton("رجوع لإدارة الأدمنية", callback_data="admin:agents")]
    )
    await query.edit_message_text(
        f"<b>صلاحيات الأدمن</b>\nالآيدي: <code>{agent_id}</code>\n\n"
        "اضغط على الصلاحية لتفعيلها أو إيقافها.",
        reply_markup=InlineKeyboardMarkup(rows),
        parse_mode=ParseMode.HTML,
    )


async def begin_wallet_adjustment(query, context: ContextTypes.DEFAULT_TYPE, mode: str):
    context.user_data.clear()
    context.user_data["mode"] = f"wallet_{mode}_user"
    context.user_data["wallet_adjustment"] = mode
    context.user_data["wallet_return_callback"] = "admin:wallet"
    context.user_data["wallet_return_label"] = "رجوع لقسم الرصيد"
    action = "إضافة" if mode == "credit" else "خصم"
    await query.edit_message_text(
        f"أرسل آيدي حساب تيليغرام للمستخدم الذي تريد {action} رصيده بعملة IQD.",
        reply_markup=back_keyboard("admin:wallet", "رجوع لقسم الرصيد"),
    )


async def admin_wallet_menu(query, user_id: int):
    await query.edit_message_text(
        "<b>إدارة رصيد IQD الموحد للأعضاء</b>\n\n"
        "اختر الإضافة أو الخصم، ثم أرسل آيدي المستخدم والمبلغ:",
        reply_markup=InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton("إضافة لمستخدم 💰", callback_data="wallet:credit"),
                    InlineKeyboardButton("خصم من مستخدم ➖", callback_data="wallet:debit"),
                ],
                [InlineKeyboardButton("سجل آخر التعديلات 🧾", callback_data="wallet:history")],
                [
                    InlineKeyboardButton(
                        "رجوع",
                        callback_data=admin_parent_target(user_id),
                    )
                ],
            ]
        ),
        parse_mode=ParseMode.HTML,
    )


async def get_wallet_member(member_id: int):
    async with database() as conn:
        return await fetch_one(
            conn,
            """
            SELECT m.telegram_id, m.balance, s.first_name, s.username
            FROM nabil_members m
            LEFT JOIN nabil_bot_user_state s ON s.telegram_id = m.telegram_id
            WHERE m.telegram_id = %s
            """,
            (member_id,),
        )


def wallet_member_name(member) -> str:
    if member.get("username"):
        return f"{safe_text(member.get('first_name') or 'عضو', 70)} (@{safe_text(member['username'], 60)})"
    return safe_text(member.get("first_name") or "عضو", 70)


def wallet_confirmation_text(
    member_id: int,
    member_name: str,
    adjustment: str,
    amount: Decimal,
    balance_before: Decimal,
    balance_after: Decimal,
    reason: str,
    warning: str = "",
) -> str:
    action = "إضافة" if adjustment == "credit" else "خصم"
    message = (
        "<b>تأكيد تعديل الرصيد</b>\n\n"
        f"العضو: {safe_html(member_name, 140)}\n"
        f"الآيدي: <code>{member_id}</code>\n"
        f"العملية: {action} {fmt_money(amount)}\n"
        f"الرصيد الحالي: {fmt_money(balance_before)}\n"
        f"الرصيد بعد التعديل: {fmt_money(balance_after)}\n"
        f"السبب: {safe_html(reason, 220)}"
    )
    if warning:
        message = f"{safe_html(warning, 250)}\n\n{message}"
    return message


def wallet_confirmation_keyboard():
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("تأكيد التعديل ✅", callback_data="wallet:confirm")],
            [InlineKeyboardButton("إلغاء والرجوع", callback_data="wallet:cancel")],
        ]
    )


async def admin_wallet_history(query):
    async with database() as conn:
        rows = await fetch_all(
            conn,
            """
            SELECT l.id, l.member_id, l.entry_type, l.amount, l.balance_after,
                   l.note, s.first_name, s.username
            FROM nabil_ledger l
            LEFT JOIN nabil_bot_user_state s ON s.telegram_id = l.member_id
            WHERE l.entry_type IN ('admin_credit', 'admin_debit')
            ORDER BY l.id DESC
            LIMIT 12
            """,
        )
    if not rows:
        text = "ماكو تعديلات رصيد مسجلة إلى الآن."
    else:
        lines = ["<b>آخر تعديلات الرصيد</b>"]
        for row in rows:
            amount = Decimal(str(row["amount"]))
            action = "إضافة" if row["entry_type"] == "admin_credit" else "خصم"
            name = wallet_member_name(row)
            lines.append(
                f"\n#{row['id']} · {action} {fmt_money(abs(amount))}"
                f"\nالعضو: {safe_html(name, 140)} · الآيدي: <code>{row['member_id']}</code>"
                f"\nالرصيد بعد العملية: {fmt_money(row['balance_after'])}"
                f"\nالسبب: {safe_html(row['note'] or 'غير مذكور', 180)}"
            )
        text = "\n".join(lines)
    await query.edit_message_text(
        text,
        reply_markup=back_keyboard(
            "admin:wallet", "رجوع لقسم الرصيد"
        ),
        parse_mode=ParseMode.HTML,
    )


async def complete_wallet_adjustment(
    query, context: ContextTypes.DEFAULT_TYPE, user_id: int
):
    if context.user_data.get("mode") != "wallet_confirm":
        context.user_data.clear()
        await query.edit_message_text(
            "انتهت جلسة تعديل الرصيد. ابدأ العملية من جديد.",
            reply_markup=back_keyboard("admin:wallet", "رجوع لقسم الرصيد"),
        )
        return

    try:
        member_id = int(context.user_data["member_id"])
        adjustment = context.user_data["wallet_adjustment"]
        reason = safe_text(context.user_data["wallet_reason"], 200).strip()
        amount = money(Decimal(str(context.user_data["wallet_amount"])))
        preview_balance = money(
            Decimal(str(context.user_data["wallet_balance_before"]))
        )
        if adjustment not in {"credit", "debit"} or amount <= 0 or not reason:
            raise ValueError
    except (KeyError, InvalidOperation, TypeError, ValueError):
        context.user_data.clear()
        await query.edit_message_text(
            "بيانات العملية غير مكتملة. ابدأ العملية من جديد.",
            reply_markup=back_keyboard("admin:wallet", "رجوع لقسم الرصيد"),
        )
        return

    signed_amount = amount if adjustment == "credit" else -amount
    status = "updated"
    current_balance = None
    new_balance = None
    async with database() as conn:
        async with conn.transaction():
            member = await fetch_one(
                conn,
                "SELECT balance FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                (member_id,),
            )
            if not member:
                status = "missing"
            else:
                current_balance = money(Decimal(str(member["balance"])))
                new_balance = money(current_balance + signed_amount)
                if new_balance < 0:
                    status = "insufficient"
                elif current_balance != preview_balance:
                    status = "changed"
                else:
                    await conn.execute(
                        "UPDATE nabil_members SET balance = %s WHERE telegram_id = %s",
                        (new_balance, member_id),
                    )
                    await conn.execute(
                        """
                        INSERT INTO nabil_ledger
                          (member_id, entry_type, amount, balance_after, note)
                        VALUES (%s, %s, %s, %s, %s)
                        """,
                        (
                            member_id,
                            "admin_credit" if adjustment == "credit" else "admin_debit",
                            signed_amount,
                            new_balance,
                            f"تعديل يدوي بواسطة المشرف {user_id} | السبب: {reason}",
                        ),
                    )
                    await enqueue_live_mirror_wallet_event(
                        conn,
                        member_id=member_id,
                        entry_type=(
                            "admin_credit" if adjustment == "credit" else "admin_debit"
                        ),
                        amount=signed_amount,
                        balance_after=new_balance,
                        note=reason,
                        actor_id=user_id,
                        event_key=f"admin-wallet:{uuid.uuid4().hex}",
                    )
                    await insert_admin_audit(
                        conn,
                        user_id,
                        "تعديل رصيد عضو",
                        member_id,
                        f"{'إضافة' if adjustment == 'credit' else 'خصم'} "
                        f"{fmt_money(amount)} | الرصيد: {fmt_money(current_balance)} "
                        f"→ {fmt_money(new_balance)} | السبب: {reason}",
                    )

    return_callback = context.user_data.get(
        "wallet_return_callback", "admin:wallet"
    )
    return_label = context.user_data.get(
        "wallet_return_label", "رجوع لقسم الرصيد"
    )
    member_name = safe_text(
        context.user_data.get("wallet_member_name", "عضو"), 140
    )
    if status == "changed":
        context.user_data["wallet_balance_before"] = str(current_balance)
        context.user_data["wallet_balance_after"] = str(new_balance)
        await query.edit_message_text(
            wallet_confirmation_text(
                member_id,
                member_name,
                adjustment,
                amount,
                current_balance,
                new_balance,
                reason,
                "تغير الرصيد منذ عرض التأكيد؛ راجع القيم وأكد العملية مرة أخرى.",
            ),
            reply_markup=wallet_confirmation_keyboard(),
            parse_mode=ParseMode.HTML,
        )
        return
    if status == "missing":
        message = "العضو غير مسجل في البوت، ولم يتم تعديل رصيده."
    elif status == "insufficient":
        message = (
            f"الرصيد الحالي {fmt_money(current_balance)} لا يكفي لهذا الخصم؛ "
            "لم يتم إجراء أي تعديل."
        )
    else:
        message = (
            f"تم {'إضافة' if adjustment == 'credit' else 'خصم'} "
            f"{fmt_money(amount)} للعضو {member_name}.\n"
            f"الرصيد الجديد: {fmt_money(new_balance)}\n"
            f"السبب: {safe_text(reason, 200)}"
        )
    context.user_data.clear()
    await query.edit_message_text(
        message,
        reply_markup=InlineKeyboardMarkup(
            [
                [InlineKeyboardButton(return_label, callback_data=return_callback)],
                [InlineKeyboardButton("آخر التعديلات 🧾", callback_data="wallet:history")],
            ]
        ),
    )
    if status == "updated":
        await notify_balance_change(
            context.bot, member_id, signed_amount, new_balance, reason
        )


async def handle_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message or not update.effective_user:
        return
    mode = context.user_data.get("mode")
    text = update.message.text.strip()
    owner_modes = {
        "member_service_domain",
        "member_service_api_key",
        "member_service_id",
        "member_service_rate",
        "member_service_min",
        "member_service_max",
        "engagement_service_name",
        "engagement_service_domain",
        "engagement_service_api_key",
        "engagement_service_id",
        "engagement_service_price",
        "engagement_service_min",
        "engagement_service_max",
        "engagement_service_description",
        "provider_api_key_rekey",
        "agent_add",
        "agentsys_add_id",
        "agentsys_add_balance",
        "agentsys_wallet_credit_id",
        "agentsys_wallet_set_id",
        "agentsys_wallet_amount",
        "agentsys_audit_channel",
        "broadcast_delay",
        "gift_code_name",
        "gift_code_amount",
        "gift_code_uses",
        "gift_code_hours",
        "subscription_exemption_add",
        "live_mirror_channel_reference",
    }
    agent_modes = {"agent_transfer_member", "agent_transfer_amount"}
    agent_owner_modes = {
        "agentsys_add_id",
        "agentsys_add_balance",
        "agentsys_wallet_credit_id",
        "agentsys_wallet_set_id",
        "agentsys_wallet_amount",
        "agentsys_audit_channel",
    }
    broadcast_modes = {
        "broadcast_content",
        "broadcast_text",
        "broadcast_options",
        "broadcast_button_label",
        "broadcast_button_url",
        "broadcast_confirm",
        "broadcast_delay",
    }
    if mode in broadcast_modes and (
        not update.effective_chat or update.effective_chat.type != "private"
    ):
        context.user_data.clear()
        await update.message.reply_text(
            "أكمل إعداد الإذاعة في المحادثة الخاصة مع البوت."
        )
        return
    if mode in {
        "member_service_domain",
        "member_service_api_key",
        "member_service_id",
        "member_service_rate",
        "member_service_min",
        "member_service_max",
        "engagement_service_name",
        "engagement_service_domain",
        "engagement_service_api_key",
        "engagement_service_id",
        "engagement_service_price",
        "engagement_service_min",
        "engagement_service_max",
        "engagement_service_description",
        "provider_api_key_rekey",
    } and (not update.effective_chat or update.effective_chat.type != "private"):
        context.user_data.clear()
        await update.message.reply_text(
            "إعداد الخدمة وإدخال مفتاح API متاحان في المحادثة الخاصة مع البوت."
        )
        return
    if mode in (agent_modes | agent_owner_modes) and (
        not update.effective_chat or update.effective_chat.type != "private"
    ):
        context.user_data.clear()
        await update.message.reply_text(
            "أكمل خطوات إدارة الوكلاء في محادثة خاصة مع البوت."
        )
        return
    if mode in {
        "gift_code_name",
        "gift_code_amount",
        "gift_code_uses",
        "gift_code_hours",
        "subscription_exemption_add",
    } and (not update.effective_chat or update.effective_chat.type != "private"):
        context.user_data.clear()
        await update.message.reply_text(
            "أكمل هذه الخطوة في المحادثة الخاصة مع البوت."
        )
        return
    if mode == "live_mirror_channel_reference" and (
        not update.effective_chat or update.effective_chat.type != "private"
    ):
        context.user_data.clear()
        await update.message.reply_text(
            "أدخل يوزر قناة المرآة في المحادثة الخاصة مع البوت."
        )
        return
    admin_modes = owner_modes | {
        "service_name",
        "service_markup",
        "wallet_credit_user",
        "wallet_debit_user",
        "wallet_amount",
        "wallet_reason",
        "wallet_confirm",
        "admin_member_search",
        "admin_member_service_id",
        "broadcast_content",
        "broadcast_text",
        "broadcast_options",
        "broadcast_button_label",
        "broadcast_button_url",
        "admin_setting_text",
        "admin_setting_value",
        "broadcast_confirm",
        "force_channel_chat",
        "force_channel_link",
        "force_channel_target",
    }
    if mode in admin_modes and not await is_admin_user(update.effective_user.id) and not (
        mode == "live_mirror_channel_reference"
        and is_live_mirror_owner(update.effective_user.id)
    ):
        context.user_data.clear()
        await update.message.reply_text("هذه العملية مخصصة للمشرفين المعتمدين.")
        return
    required_permission = admin_mode_permission(mode)
    if required_permission and not await has_admin_permission(
        update.effective_user.id, required_permission
    ):
        context.user_data.clear()
        await update.message.reply_text(
            "انتهت صلاحيتك لهذا الإجراء. راجع مالك البوت."
        )
        return
    if mode in owner_modes and not is_owner(update.effective_user.id) and not (
        mode == "live_mirror_channel_reference"
        and is_live_mirror_owner(update.effective_user.id)
    ):
        context.user_data.clear()
        await update.message.reply_text("هذا الإجراء متاح للمالك فقط.")
        return
    if mode == "live_mirror_channel_reference":
        await save_live_mirror_channel(update, context, text)
        return
    if mode in agent_modes and not await is_active_agent(update.effective_user.id):
        context.user_data.clear()
        await update.message.reply_text("هذه العملية مخصصة للوكلاء النشطين فقط.")
        return
    if await handle_agent_text(update, context, mode, text):
        return
    if mode == "subscription_exemption_add":
        normalized_id = normalize_decimal_digits(text)
        if not re.fullmatch(r"[1-9]\d{0,18}", normalized_id):
            await update.message.reply_text(
                "آيدي تيليغرام غير صحيح. أرسل آيدياً موجباً مكوّناً من أرقام فقط.",
                reply_markup=back_keyboard(
                    "admin:special_features", "إلغاء والرجوع"
                ),
            )
            return
        telegram_id = int(normalized_id)
        if telegram_id > 9_223_372_036_854_775_807:
            await update.message.reply_text(
                "الآيدي أكبر من الحد المقبول. أرسل آيدي تيليغرام صحيحاً.",
                reply_markup=back_keyboard(
                    "admin:special_features", "إلغاء والرجوع"
                ),
            )
            return
        async with database() as conn:
            inserted = await fetch_one(
                conn,
                """
                INSERT INTO nabil_subscription_exemptions
                    (telegram_id, added_by)
                VALUES (%s, %s)
                ON CONFLICT (telegram_id) DO NOTHING
                RETURNING telegram_id
                """,
                (telegram_id, update.effective_user.id),
            )
        if inserted:
            await log_admin_action(
                update.effective_user.id,
                "إضافة مستثنى من الاشتراك الإجباري",
                target_id=telegram_id,
            )
            result_text = (
                f"تمت إضافة الآيدي <code>{telegram_id}</code> إلى المستثنين. "
                "لن يظهر له الاشتراك الإجباري."
            )
        else:
            result_text = (
                f"الآيدي <code>{telegram_id}</code> مستثنى من الاشتراك مسبقاً."
            )
        context.user_data.clear()
        await update.message.reply_text(
            result_text,
            reply_markup=InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            "قائمة المستثنين",
                            callback_data="admin:subscription_exemptions",
                        )
                    ],
                    [
                        InlineKeyboardButton(
                            "الميزات الخاصة",
                            callback_data="admin:special_features",
                        )
                    ],
                ]
            ),
            parse_mode=ParseMode.HTML,
        )
        return
    if mode == "provider_api_key_rekey":
        try:
            await update.message.delete()
        except Exception:
            context.user_data.clear()
            await update.effective_chat.send_message(
                "لم أتمكن من حذف الرسالة، لذلك لم أحفظ المفتاح. "
                "احذفها يدوياً ثم ابدأ التجديد من جديد."
            )
            return
        if len(text) < 8 or len(text) > 500:
            await update.effective_chat.send_message(
                "مفتاح API غير مقبول؛ أرسل مفتاحاً بطول من 8 إلى 500 حرف، "
                "أو ألغِ العملية.",
                reply_markup=back_keyboard(
                    "provider:key:renew:cancel", "إلغاء"
                ),
            )
            return
        provider_id = context.user_data.get("provider_api_key_rekey_id")
        expected_domain = context.user_data.get("provider_api_key_rekey_domain")
        if not isinstance(provider_id, int) or not expected_domain:
            context.user_data.clear()
            await update.effective_chat.send_message(
                "انتهت جلسة تجديد المفتاح. ابدأ العملية من إعداد المزود."
            )
            return

        async with database() as conn:
            provider = await fetch_one(
                conn,
                """
                SELECT id, name, domain FROM nabil_providers
                WHERE id = %s AND enabled = TRUE
                """,
                (provider_id,),
            )
        if not provider or provider["domain"] != expected_domain:
            context.user_data.clear()
            await update.effective_chat.send_message(
                "تغير إعداد المزود أو توقف؛ لم يتم حفظ المفتاح."
            )
            return

        encrypted_api_key = encrypt_secret(text)
        provider_probe = {
            "id": provider_id,
            "name": provider["name"],
            "domain": provider["domain"],
            "api_key_encrypted": encrypted_api_key,
            "enabled": True,
        }
        started_at = asyncio.get_running_loop().time()
        try:
            response = await provider_post(
                provider_probe, {"action": "balance"}
            )
            parse_provider_balance(response)
        except Exception as exc:
            error = safe_provider_error(provider_probe, exc)
            await update.effective_chat.send_message(
                "لم يتم حفظ المفتاح؛ فشل التحقق من اتصال المزود. "
                f"{safe_text(error, 180)}\nأرسل مفتاحاً صالحاً للمحاولة مجدداً."
            )
            return

        duration_ms = max(
            0, int((asyncio.get_running_loop().time() - started_at) * 1000)
        )
        status = await persist_provider_api_key(
            provider_id,
            expected_domain,
            encrypted_api_key,
            update.effective_user.id,
            duration_ms,
        )
        if status == "pending":
            context.user_data.update(
                {
                    "mode": "provider_api_key_rekey_confirm",
                    "provider_api_key_rekey_encrypted": encrypted_api_key,
                    "provider_api_key_rekey_duration_ms": duration_ms,
                }
            )
            await update.effective_chat.send_message(
                "تم التحقق من المفتاح، لكن يوجد طلب مفتوح. "
                "أكّد أن المفتاح الجديد يعود إلى حساب المزود نفسه لمتابعة الطلب؛ "
                "لن يتغير آيدي الخدمة أو سعرها أو حدودها.",
                reply_markup=InlineKeyboardMarkup(
                    [
                        [
                            InlineKeyboardButton(
                                "نعم، الحساب نفسه",
                                callback_data="provider:key:renew:confirm",
                            )
                        ],
                        [
                            InlineKeyboardButton(
                                "إلغاء",
                                callback_data="provider:key:renew:cancel",
                            )
                        ],
                    ]
                ),
            )
        elif status == "saved":
            context.user_data.clear()
            await update.effective_chat.send_message(
                "تم التحقق من مفتاح المزود وحفظه مشفّراً. "
                "سيستأنف البوت فحص الطلبات المفتوحة في دورة الفحص التالية."
            )
        else:
            context.user_data.clear()
            message = (
                "لم يعد المزود مفعّلاً؛ لم يتم حفظ أي مفتاح."
                if status == "missing"
                else "تغير إعداد المزود أثناء العملية؛ لم يتم حفظ المفتاح."
            )
            await update.effective_chat.send_message(message)
        return
    if mode == "gift_code_redeem":
        code = normalize_gift_code(text)
        if code is None:
            legacy_code = text.upper()
            if re.fullmatch(r"[A-Z0-9_-]{3,32}", legacy_code):
                code = legacy_code
        if code is None:
            await update.message.reply_text(
                "أرسل كوداً من حرف واحد إلى 64 حرفاً أو رقماً عربياً أو إنكليزياً.",
                reply_markup=back_keyboard("menu:points", "رجوع للمكافآت"),
            )
            return
        status, balance_after, reward = await redeem_gift_code(
            update.effective_user.id, code
        )
        context.user_data.clear()
        if status == "success":
            message = (
                f"تم تفعيل الكود وإضافة {fmt_money(reward)} إلى رصيدك.\n"
                f"رصيدك الحالي: {fmt_money(balance_after)}"
            )
        elif status == "used":
            message = (
                "استخدمت هذا الكود من قبل.\n"
                f"رصيدك الحالي: {fmt_money(balance_after)}"
            )
        elif status == "disabled":
            message = "تعذر استخدام هذا الكود حالياً."
        elif status == "invalid":
            message = "الكود غير صحيح أو غير فعال."
        elif status == "expired":
            message = "انتهت صلاحية هذا الكود."
        elif status == "exhausted":
            message = "اكتمل عدد المستخدمين المسموح لهذا الكود."
        else:
            message = "تعذر العثور على حسابك."
        await update.message.reply_text(
            message,
            reply_markup=back_keyboard("menu:points", "رجوع للمكافآت"),
        )
        return
    if mode == "order_lookup":
        try:
            order_id = int(text)
            if order_id <= 0:
                raise ValueError
        except ValueError:
            await update.message.reply_text(
                "أرسل رقم طلب صحيحاً.",
                reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
            )
            return
        context.user_data.clear()
        await lookup_member_order(
            update.message,
            update.effective_user.id,
            order_id,
            context.bot,
        )
        return
    if mode == "member_rush_quantity":
        await handle_member_rush_quantity(update, context, text)
        return
    if mode == "member_rush_channel":
        await handle_member_rush_channel(update, context, text)
        return
    if mode in ("order_link",):
        await handle_order_link(update, context, text)
        return
    if mode == "order_quantity":
        await handle_order_quantity(update, context, text)
        return
    if mode == "member_service_domain":
        try:
            parsed = urlparse(text.strip())
            if parsed.hostname not in {"kd1s.com", "www.kd1s.com"}:
                raise ValueError("هذا القسم مخصص لمزود KD1S فقط.")
            provider_api_url(text)
        except ValueError as exc:
            await update.message.reply_text(str(exc))
            return
        context.user_data["member_service_domain"] = KD1S_API_URL
        context.user_data["mode"] = "member_service_api_key"
        await update.message.reply_text(
            "الخطوة 1 من 5: أرسل مفتاح API لـ KD1S برسالة خاصة. سيحذف البوت الرسالة فوراً "
            "ثم يحفظ المفتاح مشفراً."
        )
        return
    if mode == "member_service_api_key":
        if len(text) < 8 or len(text) > 500:
            await update.message.reply_text(
                "مفتاح API غير مقبول؛ أرسله بطول من 8 إلى 500 حرف."
            )
            return
        try:
            await update.message.delete()
        except Exception:
            context.user_data.clear()
            await update.effective_chat.send_message(
                "لم أتمكن من حذف رسالة المفتاح، لذلك لم أحفظه. "
                "احذف الرسالة يدوياً ثم ابدأ الإعداد من جديد."
            )
            return
        context.user_data["member_service_api_key_encrypted"] = encrypt_secret(text)
        context.user_data["mode"] = "member_service_id"
        await update.effective_chat.send_message(
            "الخطوة 2 من 5: أرسل آيدي الخدمة الخاص برشق الأعضاء، مثل 18471."
        )
        return
    if mode == "member_service_id":
        provider_service_id = text.strip()
        if (
            not provider_service_id
            or len(provider_service_id) > 120
            or any(char.isspace() or ord(char) < 32 for char in provider_service_id)
        ):
            await update.message.reply_text(
                "أرسل ID خدمة صالحاً بدون مسافات وبحد أقصى 120 حرفاً."
            )
            return
        context.user_data["member_service_id"] = provider_service_id
        context.user_data["mode"] = "member_service_rate"
        await update.message.reply_text(
            "الخطوة 3 من 5: أرسل سعر المزود لكل 1000، مثل 1.25 "
            f"{CURRENCY}. لا تستخدم فواصل آلاف."
        )
        return
    if mode == "member_service_rate":
        try:
            base_rate = parse_manual_service_rate(text)
        except ValueError as exc:
            await update.message.reply_text(str(exc))
            return
        context.user_data["member_service_rate"] = str(base_rate)
        context.user_data["mode"] = "member_service_min"
        await update.message.reply_text(
            "الخطوة 4 من 5: أرسل الحد الأدنى لكمية الطلب."
        )
        return
    if mode == "member_service_min":
        try:
            min_quantity = parse_service_quantity(text)
        except ValueError as exc:
            await update.message.reply_text(str(exc))
            return
        context.user_data["member_service_min"] = min_quantity
        context.user_data["mode"] = "member_service_max"
        await update.message.reply_text(
            "الخطوة 5 من 5: أرسل الحد الأعلى لكمية الطلب."
        )
        return
    if mode == "member_service_max":
        try:
            max_quantity = parse_service_quantity(text)
            min_quantity = int(context.user_data["member_service_min"])
        except (KeyError, ValueError) as exc:
            await update.message.reply_text(
                str(exc) if isinstance(exc, ValueError) else "انتهت جلسة الإعداد؛ ابدأ من جديد."
            )
            if isinstance(exc, KeyError):
                context.user_data.clear()
            return
        if max_quantity < min_quantity:
            await update.message.reply_text(
                f"الحد الأعلى يجب أن يكون {min_quantity} أو أكثر. أعد إدخاله."
            )
            return
        provider_service_id = str(context.user_data.get("member_service_id") or "")
        base_rate = context.user_data.get("member_service_rate")
        await setup_member_service_from_credentials(
            update,
            context,
            provider_service_id,
            base_rate,
            min_quantity,
            max_quantity,
        )
        return
    if mode == "engagement_service_name":
        if not text or len(text) > 120 or "\n" in text:
            await update.message.reply_text(
                "أرسل اسماً للخدمة من حرف واحد إلى 120 حرفاً.",
                reply_markup=back_keyboard(
                    "admin:services:engagement:0", "إلغاء الإضافة"
                ),
            )
            return
        context.user_data["engagement_service_name"] = text
        context.user_data["mode"] = "engagement_service_domain"
        await update.message.reply_text(
            "الخطوة 2 من 8: أرسل رابط API للمزود، مثل https://provider.example/api/v2.",
            reply_markup=back_keyboard(
                "admin:services:engagement:0", "إلغاء الإضافة"
            ),
        )
        return
    if mode == "engagement_service_domain":
        try:
            domain = provider_api_url(text)
        except ValueError as exc:
            await update.message.reply_text(
                f"{safe_text(exc, 180)}\nأرسل رابط HTTPS صالحاً للمزود.",
                reply_markup=back_keyboard(
                    "admin:services:engagement:0", "إلغاء الإضافة"
                ),
            )
            return
        context.user_data["engagement_service_domain"] = domain
        context.user_data["mode"] = "engagement_service_api_key"
        await update.message.reply_text(
            "الخطوة 3 من 8: أرسل مفتاح API برسالة خاصة. "
            "سيحذف البوت الرسالة فوراً ويحفظ المفتاح مشفّراً.",
            reply_markup=back_keyboard(
                "admin:services:engagement:0", "إلغاء الإضافة"
            ),
        )
        return
    if mode == "engagement_service_api_key":
        try:
            await update.message.delete()
        except Exception:
            context.user_data.clear()
            await update.effective_chat.send_message(
                "لم أتمكن من حذف رسالة المفتاح، لذلك لم أحفظه. "
                "احذف الرسالة يدوياً ثم ابدأ الإضافة من جديد."
            )
            return
        if len(text) < 8 or len(text) > 500:
            await update.effective_chat.send_message(
                "مفتاح API غير مقبول؛ أرسل مفتاحاً بطول من 8 إلى 500 حرف."
            )
            return
        context.user_data["engagement_service_api_key_encrypted"] = (
            encrypt_secret(text)
        )
        context.user_data["mode"] = "engagement_service_id"
        await update.effective_chat.send_message(
            "الخطوة 4 من 8: أرسل آيدي الخدمة لدى المزود، بدون مسافات."
        )
        return
    if mode == "engagement_service_id":
        service_id = text.strip()
        if (
            not service_id
            or len(service_id) > 120
            or any(
                char.isspace() or ord(char) < 32 for char in service_id
            )
        ):
            await update.message.reply_text(
                "أرسل آيدي خدمة صالحاً، بحد أقصى 120 حرفاً وبدون مسافات."
            )
            return
        context.user_data["engagement_service_id"] = service_id
        context.user_data["mode"] = "engagement_service_price"
        await update.message.reply_text(
            "الخطوة 5 من 8: أرسل سعر البيع للمستخدم لكل 1000 "
            f"وحدة بعملة {CURRENCY}، مثل 1500."
        )
        return
    if mode == "engagement_service_price":
        try:
            sale_price = parse_manual_service_rate(text)
        except ValueError as exc:
            await update.message.reply_text(safe_text(exc, 180))
            return
        context.user_data["engagement_service_price"] = str(sale_price)
        context.user_data["mode"] = "engagement_service_min"
        await update.message.reply_text(
            "الخطوة 6 من 8: أرسل أقل عدد مسموح به للطلب."
        )
        return
    if mode == "engagement_service_min":
        try:
            min_quantity = parse_service_quantity(text)
        except ValueError as exc:
            await update.message.reply_text(safe_text(exc, 180))
            return
        context.user_data["engagement_service_min"] = min_quantity
        context.user_data["mode"] = "engagement_service_max"
        await update.message.reply_text(
            "الخطوة 7 من 8: أرسل أكثر عدد مسموح به للطلب."
        )
        return
    if mode == "engagement_service_max":
        try:
            max_quantity = parse_service_quantity(text)
            min_quantity = int(
                context.user_data["engagement_service_min"]
            )
        except (KeyError, ValueError) as exc:
            await update.message.reply_text(
                safe_text(exc, 180)
                if isinstance(exc, ValueError)
                else "انتهت جلسة الإضافة؛ ابدأ من جديد."
            )
            if isinstance(exc, KeyError):
                context.user_data.clear()
            return
        if max_quantity < min_quantity:
            await update.message.reply_text(
                f"الحد الأعلى يجب أن يكون {min_quantity} أو أكثر."
            )
            return
        context.user_data["engagement_service_max"] = max_quantity
        context.user_data["mode"] = "engagement_service_description"
        await update.message.reply_text(
            "الخطوة 8 من 8: أرسل وصف الخدمة الذي سيظهر للمستخدمين "
            "(حتى 500 حرف)."
        )
        return
    if mode == "engagement_service_description":
        description = " ".join(text.split())
        if not description or len(description) > 500:
            await update.message.reply_text(
                "أرسل وصفاً من 1 إلى 500 حرف."
            )
            return
        context.user_data["engagement_service_description"] = description
        await save_engagement_service(update, context)
        return
    if mode == "admin_member_service_id":
        context.user_data.clear()
        await update.message.reply_text(
            "تم إيقاف طريقة اختيار الخدمة القديمة. استخدم إعداد المزود الرئيسي "
            "وأرسل ID الخدمة مباشرة.",
            reply_markup=back_keyboard(
                "admin:providers", "فتح إعداد المزود الرئيسي"
            ),
        )
        return
    if mode == "service_name":
        service_id = context.user_data.get("service_id")
        if not text or len(text) > 240:
            await update.message.reply_text("أرسل اسماً من 1 إلى 240 حرفاً.")
            return
        async with database() as conn:
            async with conn.transaction():
                previous = await fetch_one(
                    conn,
                    "SELECT custom_name FROM nabil_services WHERE id = %s",
                    (service_id,),
                )
                await conn.execute(
                    "UPDATE nabil_services SET custom_name = %s, updated_at = NOW() WHERE id = %s",
                    (text, service_id),
                )
                await insert_admin_audit(
                    conn,
                    update.effective_user.id,
                    "تعديل اسم خدمة",
                    service_id,
                    f"{safe_text(previous['custom_name'] if previous else 'غير محدد', 100)}"
                    f" → {safe_text(text, 100)}",
                )
        context.user_data.clear()
        await update.message.reply_text(
            "تم تعديل الاسم.",
            reply_markup=back_keyboard(f"service:view:{service_id}", "رجوع للخدمة"),
        )
        return
    if mode == "service_markup":
        service_id = context.user_data.get("service_id")
        try:
            percent = Decimal(text)
            if percent < 0 or percent > 1000:
                raise ValueError
        except (InvalidOperation, ValueError):
            await update.message.reply_text("أرسل نسبة من 0 إلى 1000.")
            return
        async with database() as conn:
            async with conn.transaction():
                previous = await fetch_one(
                    conn,
                    "SELECT markup_percent FROM nabil_services WHERE id = %s",
                    (service_id,),
                )
                await conn.execute(
                    "UPDATE nabil_services SET markup_percent = %s, updated_at = NOW() WHERE id = %s",
                    (rate(percent), service_id),
                )
                await insert_admin_audit(
                    conn,
                    update.effective_user.id,
                    "تعديل هامش ربح خدمة",
                    service_id,
                    f"نسبة الربح: "
                    f"{previous['markup_percent'] if previous else 'غير محدد'}% → {percent}%",
                )
        context.user_data.clear()
        await update.message.reply_text(
            "تم تحديث نسبة الربح.",
            reply_markup=back_keyboard(f"service:view:{service_id}", "رجوع للخدمة"),
        )
        return
    if mode == "admin_member_search":
        try:
            member_id = int(text)
            if member_id <= 0:
                raise ValueError
        except ValueError:
            await update.message.reply_text("أرسل رقم تيليغرام صحيحاً.")
            return
        context.user_data.clear()
        await show_admin_member(update.message, member_id)
        return
    if mode == "agent_add":
        try:
            agent_id = int(text)
            if agent_id <= 0 or agent_id == OWNER_ID:
                raise ValueError
        except ValueError:
            await update.message.reply_text("أرسل آيدي تيليغرام صحيحاً لمشرف آخر.")
            return
        async with database() as conn:
            async with conn.transaction():
                inserted = await fetch_one(
                    conn,
                    """
                    INSERT INTO nabil_bot_admins (telegram_id, added_by)
                    VALUES (%s, %s)
                    ON CONFLICT (telegram_id) DO NOTHING
                    RETURNING telegram_id
                    """,
                    (agent_id, update.effective_user.id),
                )
                await conn.execute(
                    """
                        INSERT INTO nabil_bot_admin_permissions (
                            telegram_id, can_orders, can_members, can_reports,
                            can_services, updated_by
                        )
                        VALUES (%s, TRUE, TRUE, TRUE, TRUE, %s)
                    ON CONFLICT (telegram_id) DO NOTHING
                    """,
                    (agent_id, update.effective_user.id),
                )
                if inserted:
                    await insert_admin_audit(
                        conn, update.effective_user.id, "إضافة أدمن", agent_id
                    )
        context.user_data.clear()
        await update.message.reply_text(
            (
                "تمت إضافة الأدمن بصلاحيات أساسية. تقدر تفعّل تعديل الأرصدة "
                "والإعلانات والاشتراك الإجباري من شاشة الصلاحيات."
                if inserted
                else "الأدمن مسجل مسبقاً."
            ),
            reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("إدارة المشرفين", callback_data="admin:agents")]]
            ),
        )
        return
    if mode == "force_channel_chat":
        try:
            channel = await inspect_required_channel(context.bot, text)
        except ValueError as exc:
            await update_force_prompt(update, context, str(exc))
            return
        except Exception as exc:
            LOG.warning(
                "Could not validate required channel: %s", safe_text(exc, 180)
            )
            await update_force_prompt(
                update,
                context,
                "تعذر الوصول إلى القناة. تحقق من اليوزر أو الآيدي، ومن صلاحيات البوت.",
            )
            return
        existing_channels = await load_required_channels()
        username = channel["username"]
        if any(
            existing["chat_id"] == channel["chat_id"]
            or (username and existing["chat_id"] == f"@{username}")
            or (
                channel["join_url"]
                and existing["join_url"] == channel["join_url"]
            )
            for existing in existing_channels
        ):
            await update_force_prompt(
                update, context, "هذه القناة مضافة مسبقاً إلى الاشتراك الإجباري."
            )
            context.user_data.clear()
            return
        context.user_data.update(
            {
                "force_channel_id": channel["chat_id"],
                "force_channel_title": channel["title"],
                "force_channel_join_url": channel["join_url"],
                "force_channel_username": channel["username"],
                "force_channel_verified_count": 0,
            }
        )
        if channel["join_url"]:
            await prompt_force_channel_target(update, context)
        else:
            context.user_data["mode"] = "force_channel_link"
            await update_force_prompt(
                update,
                context,
                "تم التحقق من القناة. أرسل رابط الدعوة الخاص بها ليتمكن الأعضاء من الانضمام.",
            )
        return
    if mode == "force_channel_link":
        try:
            join_url = parse_private_channel_invite(text)
        except ValueError as exc:
            await update_force_prompt(update, context, str(exc))
            return
        context.user_data["force_channel_join_url"] = join_url
        await prompt_force_channel_target(update, context)
        return
    if mode == "force_channel_target":
        try:
            target_count = int(text)
            if target_count < 1 or target_count > MAX_REQUIRED_CHANNEL_TARGET:
                raise ValueError
        except ValueError:
            await update_force_prompt(
                update,
                context,
                f"أرسل عدداً صحيحاً من 1 إلى {MAX_REQUIRED_CHANNEL_TARGET}.",
            )
            return
        verified_count = int(
            context.user_data.get("force_channel_verified_count", 0)
        )
        if target_count <= verified_count:
            await update_force_prompt(
                update,
                context,
                f"عدد المتحققين الحالي {verified_count}. أرسل هدفاً أكبر منه.",
            )
            return
        context.user_data["force_channel_target_count"] = target_count
        await preview_force_channel(update, context)
        return
    if mode in {"broadcast_content", "broadcast_text"}:
        await capture_broadcast_content(update, context)
        return
    if mode == "broadcast_button_label":
        label = text.strip()
        if not label or len(label) > 64 or "\n" in label:
            await update.message.reply_text(
                "أرسل نصاً للزر من 1 إلى 64 حرفاً وفي سطر واحد."
            )
            return
        context.user_data["broadcast_button_label"] = label
        context.user_data["mode"] = "broadcast_button_url"
        await update.message.reply_text(
            "أرسل رابط الزر ويجب أن يبدأ بـ https:// أو http://.",
            reply_markup=back_keyboard(
                "admin:broadcast:preview", "رجوع للمعاينة"
            ),
        )
        return
    if mode == "broadcast_button_url":
        url = text.strip()
        parsed = urllib.parse.urlparse(url)
        if (
            len(url) > 512
            or parsed.scheme not in {"https", "http"}
            or not parsed.netloc
        ):
            await update.message.reply_text(
                "أرسل رابطاً صالحاً يبدأ بـ https:// أو http://."
            )
            return
        context.user_data["broadcast_button_url"] = url
        await reply_broadcast_confirmation(update.message, context)
        return
    if mode == "broadcast_delay":
        try:
            delay = float(text)
            if not BROADCAST_DELAY_MIN <= delay <= BROADCAST_DELAY_MAX:
                raise ValueError
        except ValueError:
            await update.message.reply_text(
                f"أرسل فاصلاً من {BROADCAST_DELAY_MIN:g} إلى "
                f"{BROADCAST_DELAY_MAX:g} ثانية."
            )
            return
        await set_setting("broadcast_delay_seconds", f"{delay:.2f}")
        await log_admin_action(
            update.effective_user.id,
            "تعديل فاصل الإذاعة",
            details=f"{delay:.2f} ثانية",
        )
        context.user_data.clear()
        await update.message.reply_text(
            f"تم ضبط الفاصل بين الرسائل إلى {delay:g} ثانية.",
            reply_markup=back_keyboard("admin:broadcast", "رجوع لقسم الإذاعة"),
        )
        return
    if mode == "gift_code_name":
        code = normalize_gift_code(text)
        if code is None:
            await update.message.reply_text(
                "أرسل كوداً من حرف واحد إلى 64 حرفاً أو رقماً عربياً أو إنكليزياً، بدون رموز.",
                reply_markup=back_keyboard(
                    "admin:gift_codes", "رجوع لأكواد الهدايا"
                ),
            )
            return
        context.user_data.update({"gift_code": code, "mode": "gift_code_amount"})
        await update.message.reply_text(
            f"أرسل قيمة الرصيد بعملة IQD التي يمنحها الكود {code}.",
            reply_markup=back_keyboard("admin:gift_codes", "رجوع لأكواد الهدايا"),
        )
        return
    if mode == "gift_code_amount":
        code = context.user_data.get("gift_code")
        try:
            reward = money(Decimal(normalize_decimal_digits(text)))
            if not code or reward < 1 or reward > Decimal("1000000000"):
                raise ValueError
        except (InvalidOperation, TypeError, ValueError):
            await update.message.reply_text(
                "أرسل قيمة من 1 إلى 1,000,000,000 IQD."
            )
            return
        context.user_data.update(
            {"gift_code_reward": str(reward), "mode": "gift_code_uses"}
        )
        await update.message.reply_text(
            f"كم شخصاً يمكنه استخدام الكود {code}؟ أرسل عدداً من 1 إلى 1,000,000.",
            reply_markup=back_keyboard("admin:gift_codes", "رجوع لأكواد الهدايا"),
        )
        return
    if mode == "gift_code_uses":
        normalized = normalize_decimal_digits(text)
        if not re.fullmatch(r"[0-9]{1,7}", normalized):
            await update.message.reply_text(
                "أرسل عدداً صحيحاً من 1 إلى 1,000,000."
            )
            return
        max_uses = int(normalized)
        if not 1 <= max_uses <= 1_000_000:
            await update.message.reply_text(
                "عدد المستخدمين يجب أن يكون من 1 إلى 1,000,000."
            )
            return
        context.user_data.update(
            {"gift_code_max_uses": max_uses, "mode": "gift_code_hours"}
        )
        await update.message.reply_text(
            "كم ساعة يبقى الكود صالحاً؟ أرسل عدداً من 1 إلى 87,600 ساعة.",
            reply_markup=back_keyboard("admin:gift_codes", "رجوع لأكواد الهدايا"),
        )
        return
    if mode == "gift_code_hours":
        normalized = normalize_decimal_digits(text)
        if not re.fullmatch(r"[0-9]{1,5}", normalized):
            await update.message.reply_text(
                "أرسل مدة صحيحة بالساعات من 1 إلى 87,600."
            )
            return
        hours = int(normalized)
        if not 1 <= hours <= 87_600:
            await update.message.reply_text(
                "مدة الصلاحية يجب أن تكون من 1 إلى 87,600 ساعة."
            )
            return
        code = context.user_data.get("gift_code")
        try:
            reward = money(
                Decimal(str(context.user_data.get("gift_code_reward", "")))
            )
            max_uses = int(context.user_data.get("gift_code_max_uses", 0))
            if (
                not code
                or not 1 <= max_uses <= 1_000_000
                or reward < 1
                or reward > Decimal("1000000000")
            ):
                raise ValueError
        except (InvalidOperation, TypeError, ValueError):
            context.user_data.clear()
            await update.message.reply_text(
                "انتهت بيانات إنشاء الكود. ابدأ من جديد.",
                reply_markup=back_keyboard(
                    "admin:gift_codes", "رجوع لأكواد الهدايا"
                ),
            )
            return
        async with database() as conn:
            inserted = await fetch_one(
                conn,
                """
                INSERT INTO nabil_gift_codes
                  (code, reward, max_uses, expires_at, created_by)
                VALUES (
                  %s, %s, %s,
                  NOW() + (%s * INTERVAL '1 hour'),
                  %s
                )
                ON CONFLICT (code) DO NOTHING
                RETURNING id
                """,
                (code, reward, max_uses, hours, update.effective_user.id),
            )
        context.user_data.clear()
        if inserted:
            await log_admin_action(
                update.effective_user.id,
                "إنشاء كود هدية",
                details=(
                    f"{code} · {fmt_money(reward)} · "
                    f"{max_uses} استخدام · {hours} ساعة"
                ),
            )
            message = (
                f"تم إنشاء الكود {code}.\n"
                f"قيمة الهدية: {fmt_money(reward)}\n"
                f"عدد المستخدمين: {max_uses}\n"
                f"الصلاحية: {hours} ساعة."
            )
        else:
            message = "هذا الكود موجود مسبقاً. اختر كوداً آخر."
        await update.message.reply_text(
            message,
            reply_markup=back_keyboard("admin:gift_codes", "رجوع لأكواد الهدايا"),
        )
        return
    if mode == "admin_setting_text":
        setting_key = context.user_data.get("setting_key")
        if not text or len(text) > 3500:
            await update.message.reply_text("أرسل نصاً من 1 إلى 3500 حرف.")
            return
        if setting_key == "welcome_text":
            try:
                text.format(name="الاسم", id=12345)
            except (KeyError, ValueError):
                await update.message.reply_text(
                    "صيغة غير صحيحة. المتاح فقط {name} و{id}، أو اكتب نصاً عادياً."
                )
                return
        previous_value = await get_setting(setting_key)
        await set_setting(setting_key, text)
        previous_preview = safe_text(previous_value, 100).replace("\n", " ")
        current_preview = safe_text(text, 100).replace("\n", " ")
        await log_admin_action(
            update.effective_user.id,
            "تعديل نص إعداد",
            details=f"{setting_key}: {previous_preview} → {current_preview}",
        )
        context.user_data.clear()
        await update.message.reply_text(
            "تم حفظ النص.",
            reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("النصوص والرسائل", callback_data="admin:copy")]]
            ),
        )
        return
    if mode == "admin_setting_value":
        setting_key = context.user_data.get("setting_key")
        if setting_key == "daily_balance_reward":
            try:
                minimum, maximum = parse_daily_reward_range(text)
            except (InvalidOperation, ValueError, TypeError):
                await update.message.reply_text(
                    "القيمة غير صالحة. أرسل رقماً صحيحاً أو نطاقاً مثل 100 200، "
                    "على ألا يتجاوز أي حد 1000000."
                )
                return
            previous_minimum = await get_setting("daily_balance_reward")
            previous_maximum = await get_setting("daily_balance_reward_max")
            await set_daily_reward_range(minimum, maximum)
            await log_admin_action(
                update.effective_user.id,
                "تعديل نطاق الهدية اليومية",
                details=(
                    f"{previous_minimum}-{previous_maximum} → "
                    f"{minimum}-{maximum}"
                ),
            )
            context.user_data.clear()
            reward_label = (
                "متوقفة"
                if minimum == 0 and maximum == 0
                else (
                    fmt_money(minimum)
                    if minimum == maximum
                    else f"{fmt_money(minimum)} - {fmt_money(maximum)}"
                )
            )
            await update.message.reply_text(
                f"تم حفظ الهدية اليومية: {reward_label}.",
                reply_markup=InlineKeyboardMarkup(
                    [[InlineKeyboardButton("إعدادات الرصيد والمكافآت", callback_data="admin:points_settings")]]
                ),
            )
            return
        try:
            if setting_key in {
                "referral_referrer_balance_reward",
                "referral_invitee_balance_reward",
            }:
                value = money(Decimal(text))
                if value < 0 or value > Decimal("1000000000"):
                    raise ValueError
                saved_value = str(value)
            elif setting_key == "min_balance_transfer":
                value = money(Decimal(text))
                if value <= 0 or value > Decimal("100000000"):
                    raise ValueError
                saved_value = str(value)
            else:
                raise ValueError("Unsupported numeric setting.")
        except (InvalidOperation, ValueError, KeyError):
            await update.message.reply_text("القيمة غير صالحة. أرسل رقماً ضمن الحدود المسموحة.")
            return
        previous_value = await get_setting(setting_key)
        await set_setting(setting_key, saved_value)
        await log_admin_action(
            update.effective_user.id,
            "تعديل إعداد رقمي",
            details=f"{setting_key}: {previous_value} → {saved_value}",
        )
        context.user_data.clear()
        await update.message.reply_text(
            "تم حفظ الإعداد.",
            reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("إعدادات الرصيد والمكافآت", callback_data="admin:points_settings")]]
            ),
        )
        return
    if mode in ("required_channel_chat", "required_channel_url", "public_channel_url"):
        value = text
        if value.strip().lower() in {"مسح", "حذف", "none", "off"}:
            value = ""
        if mode == "required_channel_chat":
            if value and not (re.fullmatch(r"@[A-Za-z0-9_]{5,32}", value) or re.fullmatch(r"-100\d{5,20}", value)):
                await update.message.reply_text(
                    "أرسل اسم قناة مثل @mychannel أو رقم القناة الذي يبدأ بـ -100، أو /cancel للإلغاء."
                )
                return
            key = mode
        else:
            if value and not re.fullmatch(r"https://t\.me/[A-Za-z0-9_+./-]{1,180}", value):
                await update.message.reply_text("أرسل رابطاً صالحاً يبدأ بـ https://t.me/، أو /cancel للإلغاء.")
                return
            key = mode
        previous_value = await get_setting(key)
        await set_setting(key, value)
        await log_admin_action(
            update.effective_user.id,
            "تعديل إعداد قناة",
            details=(
                f"{key}: {'مضبوط' if previous_value else 'غير مضبوط'}"
                f" → {'مضبوط' if value else 'غير مضبوط'}"
            ),
        )
        context.user_data.clear()
        await update.message.reply_text(
            "تم حفظ رابط القناة.",
            reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("إدارة القنوات", callback_data="admin:channel")]]
            ),
        )
        return
    if mode == "transfer_recipient":
        try:
            recipient_id = int(text)
            if recipient_id <= 0 or recipient_id == update.effective_user.id:
                raise ValueError
        except ValueError:
            await update.message.reply_text("أرسل آيدي عضو آخر صحيحاً.")
            return
        async with database() as conn:
            recipient = await fetch_one(
                conn,
                "SELECT telegram_id FROM nabil_members WHERE telegram_id = %s",
                (recipient_id,),
            )
        if not recipient:
            await update.message.reply_text("هذا الحساب غير مسجل في البوت.")
            return
        context.user_data.update({"transfer_recipient": recipient_id, "mode": "transfer_amount"})
        try:
            minimum = money(Decimal(await get_setting("min_balance_transfer")))
        except (InvalidOperation, ValueError):
            minimum = money(1)
        await update.message.reply_text(
            f"أرسل مبلغ التحويل. الحد الأدنى {fmt_money(minimum)}.",
            reply_markup=back_keyboard("transfer:cancel", "رجوع للقائمة"),
        )
        return
    if mode == "transfer_amount":
        try:
            amount = money(Decimal(text))
            minimum = money(Decimal(await get_setting("min_balance_transfer")))
            if amount < minimum or amount > Decimal("100000000"):
                raise ValueError
        except (InvalidOperation, ValueError):
            await update.message.reply_text("أرسل مبلغاً صالحاً لا يقل عن الحد الأدنى.")
            return
        context.user_data.update({"transfer_amount": str(amount), "mode": "transfer_confirm"})
        recipient_id = context.user_data["transfer_recipient"]
        await update.message.reply_text(
            f"تحويل {fmt_money(amount)} إلى العضو {recipient_id}. هل تؤكد؟",
            reply_markup=InlineKeyboardMarkup(
                [
                    [InlineKeyboardButton("تأكيد التحويل", callback_data="transfer:confirm")],
                    [InlineKeyboardButton("إلغاء", callback_data="transfer:cancel")],
                ]
            ),
        )
        return
    if mode in ("wallet_credit_user", "wallet_debit_user"):
        try:
            member_id = int(text)
            if member_id <= 0:
                raise ValueError
        except ValueError:
            await update.message.reply_text(
                "أرسل آيدي تيليغرام صحيحاً.",
                reply_markup=back_keyboard(
                    context.user_data.get("wallet_return_callback", "admin:wallet"),
                    context.user_data.get("wallet_return_label", "رجوع لقسم الرصيد"),
                ),
            )
            return
        member = await get_wallet_member(member_id)
        if not member:
            context.user_data.clear()
            await update.message.reply_text(
                "هذا العضو غير مسجل في البوت.",
                reply_markup=back_keyboard("admin:wallet", "رجوع لقسم الرصيد"),
            )
            return
        balance_before = money(Decimal(str(member["balance"])))
        context.user_data.update(
            {
                "member_id": member_id,
                "wallet_member_name": wallet_member_name(member),
                "wallet_balance_before": str(balance_before),
                "mode": "wallet_amount",
            }
        )
        action = (
            "إضافة رصيد" if context.user_data.get("wallet_adjustment") == "credit"
            else "خصم رصيد"
        )
        await update.message.reply_text(
            f"العضو: {wallet_member_name(member)}\n"
            f"الآيدي: {member_id}\n"
            f"رصيده الحالي: {fmt_money(balance_before)}\n\n"
            f"أرسل مبلغ {action} الموجب.",
            reply_markup=back_keyboard(
                context.user_data.get("wallet_return_callback", "admin:wallet"),
                context.user_data.get("wallet_return_label", "رجوع لقسم الرصيد"),
            ),
        )
        return
    if mode == "wallet_amount":
        try:
            amount = money(Decimal(text))
            if amount <= 0 or amount > Decimal("100000000"):
                raise ValueError
        except (InvalidOperation, ValueError):
            await update.message.reply_text(
                "أرسل مبلغاً موجباً صالحاً.",
                reply_markup=back_keyboard(
                    context.user_data.get("wallet_return_callback", "admin:wallet"),
                    context.user_data.get("wallet_return_label", "رجوع لقسم الرصيد"),
                ),
            )
            return
        member_id = context.user_data.get("member_id")
        adjustment = context.user_data.get("wallet_adjustment")
        member = await get_wallet_member(member_id)
        if not member:
            return_callback = context.user_data.get(
                "wallet_return_callback", "admin:wallet"
            )
            return_label = context.user_data.get(
                "wallet_return_label", "رجوع لقسم الرصيد"
            )
            context.user_data.clear()
            await update.message.reply_text(
                "العضو غير مسجل في البوت.",
                reply_markup=back_keyboard(
                    return_callback,
                    return_label,
                ),
            )
            return
        balance_before = money(Decimal(str(member["balance"])))
        signed_amount = amount if adjustment == "credit" else -amount
        balance_after = money(balance_before + signed_amount)
        if balance_after < 0:
            await update.message.reply_text(
                f"الرصيد الحالي {fmt_money(balance_before)} لا يكفي لهذا الخصم. "
                "أرسل مبلغاً أقل.",
                reply_markup=back_keyboard(
                    context.user_data.get("wallet_return_callback", "admin:wallet"),
                    context.user_data.get("wallet_return_label", "رجوع لقسم الرصيد"),
                ),
            )
            return
        context.user_data.update(
            {
                "wallet_amount": str(amount),
                "wallet_balance_before": str(balance_before),
                "wallet_balance_after": str(balance_after),
                "mode": "wallet_reason",
            }
        )
        await update.message.reply_text(
            f"المبلغ: {fmt_money(amount)}\n"
            f"الرصيد بعد التعديل: {fmt_money(balance_after)}\n\n"
            "أرسل سبب العملية حتى يظهر في سجل التعديلات.",
            reply_markup=back_keyboard(
                context.user_data.get("wallet_return_callback", "admin:wallet"),
                context.user_data.get("wallet_return_label", "رجوع لقسم الرصيد"),
            ),
        )
        return
    if mode == "wallet_reason":
        reason = text.strip()
        if len(reason) < 2 or len(reason) > 200:
            await update.message.reply_text(
                "اكتب سبباً من حرفين إلى 200 حرف.",
                reply_markup=back_keyboard(
                    context.user_data.get("wallet_return_callback", "admin:wallet"),
                    context.user_data.get("wallet_return_label", "رجوع لقسم الرصيد"),
                ),
            )
            return
        context.user_data.update({"wallet_reason": reason, "mode": "wallet_confirm"})
        await update.message.reply_text(
            wallet_confirmation_text(
                int(context.user_data["member_id"]),
                context.user_data.get("wallet_member_name", "عضو"),
                context.user_data["wallet_adjustment"],
                money(Decimal(str(context.user_data["wallet_amount"]))),
                money(Decimal(str(context.user_data["wallet_balance_before"]))),
                money(Decimal(str(context.user_data["wallet_balance_after"]))),
                reason,
            ),
            reply_markup=wallet_confirmation_keyboard(),
            parse_mode=ParseMode.HTML,
        )
        return
    await update.message.reply_text("استخدم الأزرار أو /cancel لإلغاء العملية.")


async def request_live_mirror_order_cancel(order_id: int) -> str:
    async with database() as conn:
        order = await fetch_one(
            conn,
            """
            SELECT o.*, p.id AS provider_id, p.name AS provider_name,
                   p.domain, p.api_key_encrypted, p.enabled AS provider_enabled
            FROM nabil_orders AS o
            JOIN nabil_providers AS p ON p.id = o.provider_id
            WHERE o.id = %s
            """,
            (order_id,),
        )
    if not order:
        return "الطلب غير موجود؛ لم يُجر أي تعديل على الرصيد."
    if order["status"] not in {"Pending", "Processing"}:
        return (
            f"حالة الطلب الحالية: {order_status_label(order['status'])}. "
            "لا يمكن طلب إلغائه مرة أخرى."
        )
    if not order.get("provider_order_id"):
        return (
            "لم يسجل المزود رقم هذا الطلب بعد. لم يُلغَ الطلب ولم يُرد الرصيد."
        )
    if not order.get("domain") or not order.get("api_key_encrypted"):
        return "بيانات المزود غير متاحة؛ لم يُلغَ الطلب ولم يُرد الرصيد."

    provider = provider_public(order)
    try:
        await provider_post(
            provider,
            {
                "action": "cancel",
                "orders": str(order["provider_order_id"]),
            },
            timeout=20.0,
        )
        status_response = await provider_post(
            provider,
            {
                "action": "status",
                "order": str(order["provider_order_id"]),
            },
            timeout=12.0,
        )
    except Exception as exc:
        LOG.warning(
            "Live mirror cancellation request failed for order %s (%s).",
            order_id,
            type(exc).__name__,
        )
        return (
            "تعذر تأكيد الإلغاء من المزود. لم يُرد الرصيد؛ "
            "ستبقى متابعة الحالة التلقائية فعّالة."
        )

    if not isinstance(status_response, dict) or not status_response.get("status"):
        return (
            "استلم المزود طلب الإلغاء لكن لم يُرجع حالة مؤكدة. "
            "لم يُرد الرصيد، وستبقى متابعة الحالة التلقائية فعّالة."
        )
    provider_status = str(status_response["status"]).strip()
    normalized_status = normalize_provider_status(provider_status)
    if normalized_status is None:
        return (
            "أعاد المزود حالة غير معروفة. لم يُرد الرصيد؛ "
            "يرجى مراجعة سجل المزود."
        )
    if normalized_status not in {"Canceled", "Partial", "Completed"}:
        return (
            "أُرسل طلب الإلغاء، لكن المزود لم يؤكد الإلغاء بعد. "
            "لم يُرد الرصيد، وستبقى متابعة الحالة التلقائية فعّالة."
        )

    refund_delta, _, _, _ = await apply_provider_status(
        order,
        provider_status,
        parse_provider_remains(status_response.get("remains")),
    )
    async with database() as conn:
        current = await fetch_one(
            conn,
            "SELECT status, refunded_amount FROM nabil_orders WHERE id = %s",
            (order_id,),
        )
    if not current:
        return "تمت مراجعة حالة المزود، لكن تعذر تحميل الحالة المحفوظة."
    if current["status"] == "Canceled":
        return (
            f"أكد المزود إلغاء الطلب #{order_id}. "
            f"المبلغ المسترد: {_fmt_money_for_mirror(current['refunded_amount'])}."
        )
    if current["status"] == "Partial":
        return (
            f"اكتمل الطلب جزئياً. المبلغ المسترد حسب بيانات المزود: "
            f"{_fmt_money_for_mirror(refund_delta)}."
        )
    if current["status"] == "Completed":
        return "أفاد المزود أن الطلب مكتمل؛ لم يُرد المبلغ."
    return (
        "لم يعتمد النظام الإلغاء بعد؛ لم يُرد الرصيد. "
        "ستبقى متابعة الحالة التلقائية فعّالة."
    )


def _fmt_money_for_mirror(value: Any) -> str:
    try:
        return fmt_money(Decimal(str(value or 0)))
    except (InvalidOperation, TypeError, ValueError):
        return fmt_money(0)


async def handle_live_mirror_callback(
    query, context: ContextTypes.DEFAULT_TYPE, user_id: int, data: str
):
    parts = data.split(":")
    if len(parts) != 3 or parts[1] not in {
        "cancel",
        "cancel_confirm",
        "cancel_abort",
        "ban",
        "ban_confirm",
        "ban_abort",
    }:
        await query.answer("الإجراء غير معروف.", show_alert=True)
        return
    action, raw_id = parts[1], parts[2]
    if not re.fullmatch(r"[1-9]\d{0,18}", raw_id):
        await query.answer("معرف الإجراء غير صالح.", show_alert=True)
        return
    target_id = int(raw_id)
    if not query.message:
        await query.answer("تعذر تحديد رسالة الإجراء.", show_alert=True)
        return

    if action == "cancel":
        async with database() as conn:
            order = await fetch_one(
                conn,
                """
                SELECT id, member_id, service_name, status, sale_amount
                FROM nabil_orders WHERE id = %s
                """,
                (target_id,),
            )
        if not order:
            await query.answer("الطلب غير موجود.", show_alert=True)
            return
        if order["status"] not in {"Pending", "Processing"}:
            await query.answer(
                f"حالة الطلب: {order_status_label(order['status'])}.",
                show_alert=True,
            )
            return
        await query.answer()
        await query.message.reply_text(
            f"تأكيد طلب إلغاء الخدمة واسترجاع الرصيد للطلب #{target_id}؟\n"
            f"المستخدم: <code>{order['member_id']}</code>\n"
            f"الخدمة: {safe_html(order['service_name'], 100)}\n\n"
            "لن يُعاد الرصيد إلا بعد أن يؤكد المزود الإلغاء.",
            reply_markup=InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            "تأكيد طلب الإلغاء",
                            callback_data=f"mirror:cancel_confirm:{target_id}",
                        ),
                        InlineKeyboardButton(
                            "تراجع",
                            callback_data=f"mirror:cancel_abort:{target_id}",
                        ),
                    ]
                ]
            ),
            parse_mode=ParseMode.HTML,
        )
        return

    if action == "cancel_confirm":
        await query.answer("جارٍ طلب الإلغاء والتحقق من المزود.")
        result = await request_live_mirror_order_cancel(target_id)
        await query.edit_message_text(result)
        return

    if action == "cancel_abort":
        await query.answer("تم التراجع.")
        await query.edit_message_text("تم إلغاء الإجراء؛ لم يتغير الطلب أو الرصيد.")
        return

    if action == "ban":
        async with database() as conn:
            member = await fetch_one(
                conn,
                """
                SELECT COALESCE(is_banned, FALSE) AS is_banned
                FROM nabil_bot_user_state
                WHERE telegram_id = %s
                """,
                (target_id,),
            )
        if member and member["is_banned"]:
            await query.answer("هذا المستخدم محظور بالفعل.", show_alert=True)
            return
        await query.answer()
        await query.message.reply_text(
            f"تأكيد حظر المستخدم <code>{target_id}</code>؟",
            reply_markup=InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            "تأكيد الحظر",
                            callback_data=f"mirror:ban_confirm:{target_id}",
                        ),
                        InlineKeyboardButton(
                            "تراجع",
                            callback_data=f"mirror:ban_abort:{target_id}",
                        ),
                    ]
                ]
            ),
            parse_mode=ParseMode.HTML,
        )
        return

    if action == "ban_abort":
        await query.answer("تم التراجع.")
        await query.edit_message_text("تم إلغاء الإجراء؛ لم يتغير حساب المستخدم.")
        return

    status = "missing"
    async with database() as conn:
        async with conn.transaction():
            member = await fetch_one(
                conn,
                "SELECT telegram_id FROM nabil_members WHERE telegram_id = %s FOR UPDATE",
                (target_id,),
            )
            if member:
                await conn.execute(
                    """
                    INSERT INTO nabil_bot_user_state (telegram_id)
                    VALUES (%s) ON CONFLICT (telegram_id) DO NOTHING
                    """,
                    (target_id,),
                )
                state = await fetch_one(
                    conn,
                    """
                    SELECT is_banned FROM nabil_bot_user_state
                    WHERE telegram_id = %s FOR UPDATE
                    """,
                    (target_id,),
                )
                if state and state["is_banned"]:
                    status = "already_banned"
                elif state:
                    await conn.execute(
                        """
                        UPDATE nabil_bot_user_state
                        SET is_banned = TRUE, updated_at = NOW()
                        WHERE telegram_id = %s
                        """,
                        (target_id,),
                    )
                    await insert_admin_audit(
                        conn, user_id, "حظر عضو", target_id
                    )
                    status = "banned"
    await query.answer()
    if status == "banned":
        await query.edit_message_text(
            f"تم حظر المستخدم <code>{target_id}</code>، وسُجل الإجراء في الصندوق الأسود.",
            parse_mode=ParseMode.HTML,
        )
    elif status == "already_banned":
        await query.edit_message_text("المستخدم محظور بالفعل.")
    else:
        await query.edit_message_text("تعذر العثور على حساب المستخدم.")


async def callback_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not query or not update.effective_user:
        return
    data = query.data or ""
    user_id = update.effective_user.id
    chat_id = update.effective_chat.id if update.effective_chat else None
    back_pressed = is_back_navigation(query, data)

    if data == "human:begin":
        await query.answer()
        if not update.effective_chat or update.effective_chat.type != "private":
            await query.edit_message_text(
                "لحماية رمز التحقق، أكمل الخطوات في المحادثة الخاصة مع البوت."
            )
            return
        code = await create_human_verification_challenge(user_id)
        if not code:
            await query.edit_message_text(
                "تم التحقق من حسابك مسبقاً. أرسل /start للدخول إلى البوت."
            )
            return
        await query.edit_message_text(
            "أرسل هذا الرمز الآن للتأكد من أنك لست روبوتاً:\n"
            f"{code}\n\n"
            "الرمز صالح لمدة 10 دقائق، ولديك 5 محاولات."
        )
        return

    if data.startswith(("agentsys:", "agentwallet:")) and (
        not update.effective_chat or update.effective_chat.type != "private"
    ):
        await query.answer(
            "استخدم إدارة الوكلاء في محادثة خاصة مع البوت.",
            show_alert=True,
        )
        return
    if data.startswith("admin:broadcast") and (
        not update.effective_chat or update.effective_chat.type != "private"
    ):
        await query.answer(
            "استخدم قسم الإذاعة في المحادثة الخاصة مع البوت.",
            show_alert=True,
        )
        return
    if data.startswith("provider:key:renew") and (
        not update.effective_chat or update.effective_chat.type != "private"
    ):
        await query.answer(
            "استخدم تجديد مفتاح المزود في المحادثة الخاصة مع البوت.",
            show_alert=True,
        )
        return
    if data.startswith(("admin:giftcode:", "admin:gift_codes")) and (
        not update.effective_chat or update.effective_chat.type != "private"
    ):
        await query.answer(
            "استخدم إدارة أكواد الهدايا في المحادثة الخاصة مع البوت.",
            show_alert=True,
        )
        return
    if data.startswith(
        (
            "admin:special_features",
            "admin:live_mirror",
            "admin:maintenance_mode",
            "admin:subscription_exemptions",
            "admin:database_cleanup",
        )
    ) and (
        not update.effective_chat or update.effective_chat.type != "private"
    ):
        await query.answer(
            "استخدم قسم الميزات الخاصة في المحادثة الخاصة مع البوت.",
            show_alert=True,
        )
        return
    if data.startswith("mirror:"):
        if not is_live_mirror_owner(user_id):
            await query.answer("هذا الإجراء مخصص للمالك الأساسي فقط.", show_alert=True)
            return
        mirror_config = await get_live_mirror_config()
        if (
            not mirror_config
            or not mirror_config["enabled"]
            or not query.message
            or query.message.chat.id != mirror_config["channel_id"]
        ):
            await query.answer(
                "هذا الزر غير صالح خارج قناة المرآة المفعّلة.",
                show_alert=True,
            )
            return
        await handle_live_mirror_callback(query, context, user_id, data)
        return

    admin_callback = data.startswith(
        (
            "admin:",
            "agentsys:",
            "provider:",
            "service:",
            "wallet:",
            "adminpoints:",
            "agent:",
            "member:ban:",
            "points:credit:",
            "points:debit:",
            "setforce_",
        )
    ) or data == "back_admin"
    if admin_callback and not await is_admin_user(user_id):
        if not (
            is_live_mirror_owner(user_id)
            and (
                data == "admin:special_features"
                or data.startswith("admin:live_mirror")
            )
        ):
            await query.answer("هذا الخيار مخصص للمشرفين المعتمدين.", show_alert=True)
            return
    if data.startswith("agentwallet:") and not await is_active_agent(user_id):
        await query.answer("هذا الخيار مخصص للوكلاء النشطين.", show_alert=True)
        return
    owner_callback = (
        data.startswith(("provider:", "agent:", "setting:"))
        or data.startswith(("admin:giftcode:", "admin:gift_codes"))
        or data.startswith(
            ("admin:alerts", "admin:alert:", "admin:alertresolve:")
        )
        or data.startswith(
            (
                "admin:special_features",
                "admin:live_mirror",
                "admin:maintenance_mode",
                "admin:subscription_exemptions",
                "admin:database_cleanup",
            )
        )
        or data.startswith("agentsys:")
        or data == "admin:broadcast:delay"
        or data.startswith("setforce_confirm:")
        or data in {
            "admin:toggle_bot:home",
            "admin:toggle_bot:special",
            "admin:toggle_alerts:home",
        }
        or data in {
            "admin:settings",
            "admin:bot_settings",
            "admin:channel",
            "admin:copy",
            "admin:points_settings",
            "admin:audit",
            "admin:points:credit",
            "admin:points:debit",
            "admin:agents",
            "admin:owner",
            "admin:providers",
            "admin:providers:setup",
            "admin:engagement:add",
            "admin:services:members:add",
            "admin:providers:key",
            "admin:providers:domain",
            "admin:sync",
            "admin:toggle_bot",
            "admin:toggle_alerts",
            "admin:toggle_member_rush",
            "admin:toggle_subscription",
        }
    )
    if owner_callback:
        if data == "admin:special_features" or data.startswith("admin:live_mirror"):
            if not is_live_mirror_owner(user_id):
                await query.answer(
                    "هذا الإجراء مخصص للمالك الأساسي فقط.",
                    show_alert=True,
                )
                return
        elif not await owner_only(query, user_id):
            return

    required_permission = admin_callback_permission(data)
    if required_permission and not await has_admin_permission(
        user_id, required_permission
    ):
        context.user_data.clear()
        await query.answer(
            "ما عندك صلاحية لهذا القسم. راجع مالك البوت.",
            show_alert=True,
        )
        return

    await query.answer()

    if back_pressed:
        context.user_data.clear()
        if data == "menu:home":
            if chat_id is not None:
                NAV_HISTORY.pop((user_id, chat_id), None)
        elif chat_id is not None and await restore_previous_navigation_screen(
            query, user_id, chat_id
        ):
            return
    elif data not in {
        "admin:toggle_bot",
        "admin:toggle_bot:home",
        "admin:toggle_bot:special",
        "admin:toggle_alerts",
        "admin:toggle_alerts:home",
        "admin:toggle_member_rush",
        "admin:toggle_subscription",
        "wallet:confirm",
    } and chat_id is not None and not data.startswith(
        ("provider:toggle:", "service:toggle:", "member:ban:")
    ):
        remember_navigation_screen(user_id, chat_id, query.message)

    section_navigation = {
        "admin:home",
        "admin:settings",
        "admin:bot_settings",
        "admin:channel",
        "admin:copy",
        "admin:points_settings",
        "admin:gift_codes",
        "admin:agents",
        "admin:broadcast",
        "admin:providers",
        "admin:providers:setup",
        "admin:providers:key",
        "admin:providers:domain",
        "admin:members",
        "admin:orders",
        "admin:report",
        "admin:audit",
        "admin:wallet",
        "admin:alerts",
        "admin:special_features",
        "admin:maintenance_mode",
        "admin:subscription_exemptions",
        "admin:database_cleanup",
    }
    if (
        data in section_navigation
        or data.startswith(
            (
                "admin:orders:",
                "admin:alerts:",
                "admin:alert:",
                "admin:alertresolve:",
                "admin:services:",
                "admin:member:",
                "service:view:",
                "admin:gift_codes:",
                "admin:giftcode:",
                "admin:subscription_exemptions:",
                "admin:database_cleanup:",
                "agentsys:",
                "agentwallet:",
            )
        )
    ):
        context.user_data.clear()

    if data == "member:check" or data.startswith("member:check:"):
        referral_id = None
        parts = data.split(":", 2)
        if (
            len(parts) == 3
            and re.fullmatch(r"[1-9]\d{0,18}", parts[2])
        ):
            referral_id = int(parts[2])
        blocked = await member_access_message(context.bot, user_id, referral_id)
        if blocked:
            await query.edit_message_text(blocked[0], reply_markup=blocked[1])
            return
        await finish_member_start(
            update.effective_user, context, referral_id=referral_id, query=query
        )
        return

    if data.startswith("menu:"):
        context.user_data.clear()
    elif data in {
        "points:referrals",
        "points:daily",
        "points:daily:claim",
        "points:channels",
        "points:gift_code",
        "points:balance",
    }:
        context.user_data.clear()

    if data == "menu:home":
        balance = await member_balance(user_id)
        greeting = safe_text(update.effective_user.first_name, 60)
        welcome = await get_setting("welcome_text")
        try:
            welcome = welcome.format(name=greeting, id=user_id)
        except (KeyError, ValueError):
            welcome = f"{welcome}\n\n{greeting} · {user_id}"
        await query.edit_message_text(
            safe_text(welcome, 3500),
            reply_markup=await menu_keyboard(balance),
        )
    elif data.startswith("menu:services:"):
        await begin_member_rush_flow(query, context)
    elif data.startswith("menu:engagement:"):
        await show_services(
            query, int(data.rsplit(":", 1)[1]), engagement_only=True
        )
    elif data == "menu:balance":
        await show_balance(query, user_id)
    elif data == "menu:invite":
        context.user_data.clear()
        await show_referral_info(query, context, user_id)
    elif data == "menu:orders":
        await show_member_orders(query, user_id)
    elif data == "menu:account":
        await show_account_info(query, user_id)
    elif data == "menu:points":
        await show_points_menu(query, user_id)
    elif data == "points:referrals":
        await show_referral_info(
            query,
            context,
            user_id,
            back_callback="menu:points",
            back_label="رجوع للمكافآت",
        )
    elif data == "points:daily":
        await claim_daily_gift(query, user_id)
    elif data == "points:daily:claim":
        await claim_daily_gift(query, user_id)
    elif data == "points:channels":
        await query.edit_message_text(
            "هذا القسم غير متاح حالياً.",
            reply_markup=back_keyboard("menu:points", "رجوع للمكافآت"),
        )
    elif data == "points:gift_code":
        context.user_data["mode"] = "gift_code_redeem"
        await query.edit_message_text(
            "أرسل كود الهدية لتفعيله.",
            reply_markup=back_keyboard("menu:points", "رجوع للمكافآت"),
        )
    elif data == "points:balance":
        await show_member_points(query, context, user_id)
    elif data == "menu:transfer":
        await begin_balance_transfer(query, context)
    elif data.startswith("points:redeem"):
        await query.edit_message_text(
            "هذا الخيار لم يعد متاحاً؛ تُجرى جميع العمليات من رصيد IQD الموحد.",
            reply_markup=back_keyboard("menu:points", "رجوع للمكافآت"),
        )
    elif data == "transfer:confirm":
        await complete_balance_transfer(query, context, user_id)
    elif data == "transfer:cancel":
        context.user_data.clear()
        balance = await member_balance(user_id)
        await query.edit_message_text(
            "تم إلغاء التحويل.",
            reply_markup=await menu_keyboard(balance),
        )
    elif data == "menu:order_info":
        context.user_data.clear()
        context.user_data["mode"] = "order_lookup"
        await query.edit_message_text(
            "أرسل رقم الطلب لمتابعة حالته الحالية.",
            reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("رجوع للقائمة", callback_data="menu:home")]]
            ),
        )
    elif data == "menu:channel":
        channel_url = (await get_setting("public_channel_url")).strip()
        if channel_url.startswith("https://t.me/"):
            await query.edit_message_text(
                "قناة البوت:",
                reply_markup=InlineKeyboardMarkup(
                    [
                        [InlineKeyboardButton("فتح القناة", url=channel_url)],
                        [InlineKeyboardButton("رجوع للقائمة", callback_data="menu:home")],
                    ]
                ),
            )
        else:
            await query.edit_message_text(
                "رابط قناة البوت غير مضاف حالياً.",
                reply_markup=back_keyboard("menu:home", "رجوع للقائمة"),
            )
    elif data == "menu:help":
        await query.edit_message_text(
            safe_text(await get_setting("help_text"), 3500),
            reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("القائمة", callback_data="menu:home")]]
            ),
        )
    elif data.startswith("svc:engagement:"):
        service_id_raw = data.rsplit(":", 1)[1]
        if re.fullmatch(r"\d{1,18}", service_id_raw):
            await begin_order(
                query,
                context,
                int(service_id_raw),
                return_callback="menu:engagement:0",
            )
        else:
            await show_services(query, 0, engagement_only=True)
    elif data.startswith("svc:"):
        service_id_raw = data.split(":", 1)[1]
        if re.fullmatch(r"\d{1,18}", service_id_raw):
            await begin_order(
                query,
                context,
                int(service_id_raw),
                return_callback="menu:services:0",
            )
        else:
            await show_services(query, 0)
    elif data == "buy:cancel":
        return_callback = context.user_data.get("service_menu_callback")
        context.user_data.clear()
        if return_callback == "menu:engagement:0":
            await show_services(query, 0, engagement_only=True)
        elif return_callback == "menu:services:0":
            await show_services(query, 0)
        else:
            balance = await member_balance(user_id)
            await query.edit_message_text(
                "تم إلغاء الطلب.",
                reply_markup=await menu_keyboard(balance),
            )
    elif data == "buy:confirm":
        await place_order(update, context)
    elif data == "admin:home":
        await show_admin_home(query)
    elif data == "admin:special_features":
        context.user_data.clear()
        await admin_special_features(query)
    elif data == "admin:live_mirror":
        context.user_data.clear()
        await admin_live_mirror_menu(query)
    elif data == "admin:live_mirror:set":
        context.user_data.clear()
        context.user_data["mode"] = "live_mirror_channel_reference"
        current = await get_live_mirror_config()
        current_line = ""
        if current:
            try:
                current_channel = await query.get_bot().get_chat(
                    current["channel_id"]
                )
                current_username = getattr(current_channel, "username", None)
                current_label = (
                    f"<code>@{safe_html(current_username, 32)}</code>"
                    if current_username
                    else "قناة خاصة بدون يوزر عام"
                )
            except Exception:
                current_label = "قناة مرتبطة (تعذر جلب اليوزر حالياً)"
            current_line = f"\nالقناة الحالية: {current_label}"
        await query.edit_message_text(
            "أرسل يوزر قناة عامة مثل <code>@channelname</code> أو رابطها "
            "مثل <code>https://t.me/channelname</code>. "
            "للقناة الخاصة التي لا تملك يوزراً، أرسل معرّفها الذي يبدأ بـ "
            "<code>-100</code>."
            f"{current_line}\n\n"
            "يجب أن يكون البوت مشرفاً بصلاحية النشر. "
            "أرسل «مسح» لفصل القناة.",
            reply_markup=back_keyboard(
                "admin:live_mirror", "إلغاء والرجوع"
            ),
            parse_mode=ParseMode.HTML,
        )
    elif data == "admin:live_mirror:toggle":
        async with database() as conn:
            async with conn.transaction():
                changed = await fetch_one(
                    conn,
                    """
                    UPDATE nabil_live_mirror_config
                    SET enabled = NOT enabled,
                        updated_by = %s,
                        updated_at = NOW()
                    WHERE owner_id = %s
                    RETURNING enabled
                    """,
                    (LIVE_MIRROR_OWNER_ID, LIVE_MIRROR_OWNER_ID),
                )
                if changed and not changed["enabled"]:
                    await conn.execute(
                        """
                        UPDATE nabil_live_mirror_events
                        SET status = 'archived', claimed_at = NULL
                        WHERE status = 'pending'
                        """
                    )
        if changed:
            await log_admin_action(
                user_id,
                "تغيير حالة المرآة الحية",
                details="تفعيل" if changed["enabled"] else "إيقاف",
            )
        await admin_live_mirror_menu(query)
    elif data.startswith("admin:live_mirror:logs:"):
        page_raw = data.rsplit(":", 1)[1]
        if re.fullmatch(r"\d{1,6}", page_raw):
            await admin_live_mirror_logs(query, int(page_raw))
        else:
            await admin_live_mirror_logs(query)
    elif data == "admin:maintenance_mode":
        context.user_data.clear()
        await admin_maintenance_mode(query)
    elif data == "admin:subscription_exemptions":
        context.user_data.clear()
        await admin_subscription_exemptions(query)
    elif data == "admin:database_cleanup":
        context.user_data.clear()
        await admin_database_cleanup_confirmation(query)
    elif data == "admin:database_cleanup:run":
        context.user_data.clear()
        await execute_admin_database_cleanup(query, user_id)
    elif data == "admin:subscription_exemptions:add":
        context.user_data.clear()
        context.user_data["mode"] = "subscription_exemption_add"
        await query.edit_message_text(
            "أرسل آيدي تيليغرام للشخص الذي تريد استثناءه من الاشتراك الإجباري.",
            reply_markup=back_keyboard(
                "admin:subscription_exemptions",
                "إلغاء والرجوع للمستثنين",
            ),
        )
    elif data.startswith("admin:subscription_exemptions:page:"):
        page_raw = data.rsplit(":", 1)[1]
        if re.fullmatch(r"\d{1,6}", page_raw):
            await admin_subscription_exemptions(query, int(page_raw))
        else:
            await admin_subscription_exemptions(query)
    elif data.startswith("admin:subscription_exemptions:remove:"):
        telegram_id_raw = data.rsplit(":", 1)[1]
        if not re.fullmatch(r"[1-9]\d{0,18}", telegram_id_raw):
            await query.answer("آيدي الحساب غير صحيح.", show_alert=True)
            return
        telegram_id = int(telegram_id_raw)
        async with database() as conn:
            removed = await fetch_one(
                conn,
                """
                DELETE FROM nabil_subscription_exemptions
                WHERE telegram_id = %s
                RETURNING telegram_id
                """,
                (telegram_id,),
            )
        if removed:
            await log_admin_action(
                user_id,
                "إلغاء استثناء من الاشتراك الإجباري",
                target_id=telegram_id,
            )
        await admin_subscription_exemptions(query)
    elif data == "admin:subscription_exemptions:id":
        return
    elif data == "admin:alerts":
        await admin_alerts(query)
    elif data.startswith("admin:alerts:"):
        parts = data.split(":")
        if (
            len(parts) == 4
            and parts[2] in {"active", "resolved"}
            and re.fullmatch(r"\d{1,5}", parts[3])
        ):
            await admin_alerts(
                query,
                state=parts[2],
                page=int(parts[3]),
            )
        else:
            await admin_alerts(query)
    elif data.startswith("admin:alertresolve:"):
        alert_id_raw = data.rsplit(":", 1)[1]
        if re.fullmatch(r"\d{1,18}", alert_id_raw):
            await resolve_admin_alert(query, user_id, int(alert_id_raw))
        else:
            await admin_alerts(query)
    elif data.startswith("admin:alert:"):
        alert_id_raw = data.rsplit(":", 1)[1]
        if re.fullmatch(r"\d{1,18}", alert_id_raw):
            await admin_alert_detail(query, int(alert_id_raw))
        else:
            await admin_alerts(query)
    elif data == "admin:cancel":
        context.user_data.clear()
        await query.edit_message_text(
            "تم إلغاء العملية.\n\n" + await admin_dashboard_text(),
            reply_markup=await current_admin_keyboard(user_id),
            parse_mode=ParseMode.HTML,
        )
    elif data == "admin:members":
        await begin_member_search(query, context)
    elif data in ("admin:points:credit", "admin:points:debit"):
        context.user_data.clear()
        await admin_wallet_menu(query, user_id)
    elif data == "admin:agents":
        await admin_agents(query)
    elif data == "agentsys:owner":
        await agent_owner_panel(query)
    elif data == "agentsys:add":
        await begin_agent_owner_flow(query, context, "add")
    elif data == "agentsys:channel":
        await begin_agent_owner_flow(query, context, "channel")
    elif data == "agentsys:channel:clear":
        previous_channel = (await get_setting(AGENT_AUDIT_CHANNEL_KEY)).strip()
        if previous_channel:
            await send_agent_audit(
                context.bot,
                f"<b>إزالة قناة سجلات الوكلاء</b>\n"
                f"بواسطة: <code>{user_id}</code>\n"
                f"القناة: <code>{safe_html(previous_channel, 32)}</code>",
            )
        await set_setting(AGENT_AUDIT_CHANNEL_KEY, "")
        await log_admin_action(
            user_id,
            "إزالة قناة سجلات الوكلاء",
            details=f"القناة السابقة: {previous_channel}",
        )
        await agent_owner_panel(query)
    elif data.startswith("agentsys:list:"):
        try:
            page = max(0, int(data.rsplit(":", 1)[1]))
        except ValueError:
            page = 0
        await agent_owner_list(query, page)
    elif data.startswith("agentsys:detail:"):
        await agent_owner_detail(query, int(data.rsplit(":", 1)[1]))
    elif data in ("agentsys:wallet:credit", "agentsys:wallet:set"):
        await begin_agent_owner_flow(
            query,
            context,
            "credit" if data.endswith("credit") else "set",
        )
    elif data.startswith("agentsys:wallet:credit:"):
        await begin_agent_owner_flow(
            query, context, "credit", int(data.rsplit(":", 1)[1])
        )
    elif data.startswith("agentsys:wallet:set:"):
        await begin_agent_owner_flow(
            query, context, "set", int(data.rsplit(":", 1)[1])
        )
    elif data.startswith("agentsys:status:"):
        agent_id = int(data.rsplit(":", 1)[1])
        async with database() as conn:
            agent = await fetch_one(
                conn,
                "SELECT status FROM nabil_bot_agents WHERE telegram_id = %s",
                (agent_id,),
            )
        if not agent or agent["status"] == "archived":
            await query.edit_message_text(
                "لا يمكن تغيير حالة هذا الوكيل.",
                reply_markup=back_keyboard(
                    f"agentsys:detail:{agent_id}", "رجوع للوكيل"
                ),
            )
        else:
            new_status = "inactive" if agent["status"] == "active" else "active"
            result, _ = await change_agent_status(user_id, agent_id, new_status)
            if result == "success":
                audit_ok = await send_agent_audit(
                    context.bot,
                    f"<b>{'تفعيل' if new_status == 'active' else 'إيقاف'} وكيل</b>\n"
                    f"بواسطة: <code>{user_id}</code>\n"
                    f"الوكيل: <code>{agent_id}</code>",
                )
                notice = "" if audit_ok else "تعذر إرسال نسخة إلى قناة السجلات."
                await agent_owner_detail(query, agent_id, notice)
            else:
                await query.edit_message_text(
                    "تعذر تغيير حالة الوكيل.",
                    reply_markup=back_keyboard(
                        f"agentsys:detail:{agent_id}", "رجوع للوكيل"
                    ),
                )
    elif data.startswith("agentsys:archive:confirm:"):
        agent_id = int(data.rsplit(":", 1)[1])
        result, _ = await change_agent_status(user_id, agent_id, "archived")
        if result == "success":
            audit_ok = await send_agent_audit(
                context.bot,
                f"<b>أرشفة وكيل</b>\n"
                f"بواسطة: <code>{user_id}</code>\n"
                f"الوكيل: <code>{agent_id}</code>",
            )
            await query.edit_message_text(
                "تمت أرشفة الوكيل، وتعطّل دخوله إلى لوحة الوكيل."
                + ("" if audit_ok else "\nتعذر إرسال نسخة لقناة السجلات."),
                reply_markup=back_keyboard(
                    "agentsys:detail:" + str(agent_id), "رجوع للوكيل"
                ),
            )
        else:
            await query.edit_message_text(
                "تعذر أرشفة الوكيل.",
                reply_markup=back_keyboard(
                    f"agentsys:detail:{agent_id}", "رجوع للوكيل"
                ),
            )
    elif data.startswith("agentsys:archive:"):
        agent_id = int(data.rsplit(":", 1)[1])
        await query.edit_message_text(
            f"هل تريد أرشفة الوكيل <code>{agent_id}</code>؟ سيتم إيقاف دخوله إلى لوحة الوكيل، "
            "مع الاحتفاظ بسجل المحفظة والعمليات.",
            reply_markup=InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            "تأكيد الأرشفة",
                            callback_data=f"agentsys:archive:confirm:{agent_id}",
                        )
                    ],
                    [
                        InlineKeyboardButton(
                            "إلغاء",
                            callback_data=f"agentsys:detail:{agent_id}",
                        )
                    ],
                ]
            ),
            parse_mode=ParseMode.HTML,
        )
    elif data == "agentwallet:home":
        await show_agent_panel(query, user_id)
    elif data == "agentwallet:balance":
        await agent_wallet_balance_screen(query, user_id)
    elif data == "agentwallet:add":
        await begin_agent_transfer(query, context, "transfer_add")
    elif data == "agentwallet:debit":
        await begin_agent_transfer(query, context, "transfer_debit")
    elif data.startswith("agent:permissions:"):
        await show_agent_permissions(query, int(data.rsplit(":", 1)[1]))
    elif data.startswith("agent:permission:"):
        parts = data.split(":")
        if len(parts) != 4 or parts[3] not in ADMIN_PERMISSION_COLUMNS:
            await query.edit_message_text(
                "الصلاحية غير معروفة.",
                reply_markup=back_keyboard("admin:agents", "رجوع لإدارة الأدمنية"),
            )
            return
        agent_id = int(parts[2])
        permission = parts[3]
        column = ADMIN_PERMISSION_COLUMNS[permission]
        async with database() as conn:
            updated = await fetch_one(
                conn,
                f"""
                UPDATE nabil_bot_admin_permissions
                SET {column} = NOT {column}, updated_by = %s, updated_at = NOW()
                WHERE telegram_id = %s
                RETURNING {column}
                """,
                (user_id, agent_id),
            )
        if not updated:
            await query.edit_message_text(
                "تعذر تحديث الصلاحية؛ تأكد أن الأدمن ما زال مسجلاً.",
                reply_markup=back_keyboard("admin:agents", "رجوع لإدارة الأدمنية"),
            )
            return
        await log_admin_action(
            user_id,
            "تغيير صلاحية أدمن",
            agent_id,
            f"{ADMIN_PERMISSION_LABELS[permission]}: "
            f"{'مفعّلة' if not updated[column] else 'متوقفة'} → "
            f"{'مفعّلة' if updated[column] else 'متوقفة'}",
        )
        await show_agent_permissions(query, agent_id)
    elif data == "agent:add":
        context.user_data.clear()
        context.user_data["mode"] = "agent_add"
        await query.edit_message_text(
            "أرسل آيدي تيليغرام للمشرف الجديد.",
            reply_markup=back_keyboard("admin:agents", "رجوع للمشرفين"),
        )
    elif data.startswith("agent:remove:"):
        agent_id = int(data.rsplit(":", 1)[1])
        async with database() as conn:
            async with conn.transaction():
                await conn.execute(
                    "DELETE FROM nabil_bot_admins WHERE telegram_id = %s",
                    (agent_id,),
                )
                await conn.execute(
                    "DELETE FROM nabil_bot_admin_permissions WHERE telegram_id = %s",
                    (agent_id,),
                )
                await insert_admin_audit(
                    conn, user_id, "إزالة أدمن", agent_id
                )
        await admin_agents(query)
    elif data in (
        "admin:toggle_bot",
        "admin:toggle_bot:home",
        "admin:toggle_bot:special",
    ):
        previous_enabled = await setting_enabled("bot_enabled")
        enabled = not previous_enabled
        await set_setting_enabled("bot_enabled", enabled)
        await log_admin_action(
            user_id,
            "تغيير حالة البوت",
            details=(
                f"{'يعمل' if previous_enabled else 'متوقف'} → "
                f"{'يعمل' if enabled else 'متوقف'}"
            ),
        )
        if data.endswith(":home"):
            await show_admin_home(query)
        elif data.endswith(":special"):
            await admin_maintenance_mode(query)
        else:
            await admin_bot_settings(query)
    elif data in ("admin:toggle_alerts", "admin:toggle_alerts:home"):
        previous_enabled = await setting_enabled("login_alerts_enabled")
        enabled = not previous_enabled
        await set_setting_enabled("login_alerts_enabled", enabled)
        await log_admin_action(
            user_id,
            "تغيير تنبيهات الدخول",
            details=(
                f"{'مفعّلة' if previous_enabled else 'متوقفة'} → "
                f"{'مفعّلة' if enabled else 'متوقفة'}"
            ),
        )
        if data.endswith(":home"):
            await show_admin_home(query)
        else:
            await admin_bot_settings(query)
    elif data == "admin:toggle_member_rush":
        previous_enabled = await setting_enabled("member_rush_enabled")
        enabled = not previous_enabled
        await set_setting_enabled("member_rush_enabled", enabled)
        await log_admin_action(
            user_id,
            "تغيير حالة رشق الأعضاء",
            details=(
                f"{'مفعّل' if previous_enabled else 'متوقف'} → "
                f"{'مفعّل' if enabled else 'متوقف'}"
            ),
        )
        await admin_points_settings(query)
    elif data == "admin:toggle_subscription":
        previous_enabled = await setting_enabled("require_subscription")
        enabled = not previous_enabled
        await set_setting_enabled("require_subscription", enabled)
        await log_admin_action(
            user_id,
            "تغيير الاشتراك الإجباري",
            details=(
                f"{'مفعّل' if previous_enabled else 'متوقف'} → "
                f"{'مفعّل' if enabled else 'متوقف'}"
            ),
        )
        await admin_force_subscription(query)
    elif data == "admin:bot_settings":
        context.user_data.clear()
        await admin_bot_settings(query)
    elif data == "admin:providers:key":
        context.user_data.clear()
        await admin_providers(query)
    elif data == "admin:providers:domain":
        context.user_data.clear()
        await admin_providers(query)
    elif data == "admin:channel":
        context.user_data.clear()
        await admin_channel_settings(query)
    elif data == "admin:force_subscription":
        context.user_data.clear()
        await admin_force_subscription(query)
    elif data == "setforce_add":
        context.user_data.clear()
        context.user_data.update(
            {
                "mode": "force_channel_chat",
                "force_prompt_chat_id": query.message.chat_id,
                "force_prompt_message_id": query.message.message_id,
            }
        )
        await query.edit_message_text(
            "أرسل يوزر قناة عامة أو رابطها، أو آيدي القناة الذي يبدأ بـ -100. "
            "إذا كانت خاصة، أرسل الآيدي ثم رابط الدعوة.",
            reply_markup=back_keyboard(
                "admin:force_subscription", "رجوع لإدارة الاشتراك"
            ),
        )
    elif data == "setforce_confirm:yes":
        if context.user_data.get("mode") != "force_channel_confirm":
            await query.edit_message_text(
                "انتهت مراجعة إضافة القناة. ارجع لقسم الاشتراك وابدأ الإضافة من جديد.",
                reply_markup=back_keyboard(
                    "admin:force_subscription", "رجوع لقسم الاشتراك الإجباري"
                ),
            )
            return
        channel = await save_force_channel(context)
        if not channel:
            await query.edit_message_text(
                "لم تتم إضافة القناة؛ قد تكون مضافة مسبقاً.",
                reply_markup=back_keyboard(
                    "admin:force_subscription", "رجوع لقسم الاشتراك الإجباري"
                ),
            )
            return
        await log_admin_action(
            user_id,
            "إضافة قناة اشتراك إجباري",
            details=f"{channel.get('title') or channel.get('chat_id') or channel.get('id')}",
        )
        await show_required_channel_details(query, context, channel)
    elif data == "setforce_confirm:no":
        context.user_data.clear()
        await query.edit_message_text(
            "تم إلغاء إضافة القناة.",
            reply_markup=back_keyboard(
                "admin:force_subscription", "رجوع لقسم الاشتراك الإجباري"
            ),
        )
    elif data.startswith("setforce_details:"):
        channel_id = data.split(":", 1)[1]
        if not re.fullmatch(r"(?:legacy|[a-f0-9]{12})", channel_id):
            await query.edit_message_text(
                "تعذر تحديد القناة.",
                reply_markup=back_keyboard(
                    "admin:force_subscription", "رجوع لقسم الاشتراك الإجباري"
                ),
            )
            return
        channels = await load_required_channels()
        channel = next(
            (item for item in channels if item["id"] == channel_id), None
        )
        if not channel:
            await query.edit_message_text(
                "القناة غير موجودة في قائمة الاشتراك الإجباري.",
                reply_markup=back_keyboard(
                    "admin:force_subscription", "رجوع لقسم الاشتراك الإجباري"
                ),
            )
            return
        await show_required_channel_details(query, context, channel)
    elif data == "setforce_refresh":
        context.user_data.clear()
        await admin_force_subscription(query)
    elif data == "back_admin":
        context.user_data.clear()
        await show_admin_home(query)
    elif data.startswith("setforce_remove:"):
        channel_id = data.split(":", 1)[1]
        if not re.fullmatch(r"(?:legacy|[a-f0-9]{12})", channel_id):
            await query.edit_message_text(
                "تعذر تحديد القناة المطلوب حذفها.",
                reply_markup=back_keyboard(
                    "admin:force_subscription", "رجوع لإدارة الاشتراك"
                ),
            )
            return
        await remove_required_channel(channel_id)
        await log_admin_action(
            user_id, "إزالة قناة اشتراك إجباري", details=channel_id
        )
        await admin_force_subscription(query)
    elif data == "admin:copy":
        context.user_data.clear()
        await admin_copy_settings(query)
    elif data == "admin:points_settings":
        context.user_data.clear()
        await admin_points_settings(query)
    elif data == "admin:gift_codes" or data.startswith("admin:gift_codes:"):
        context.user_data.clear()
        page = 0
        if ":" in data:
            page_raw = data.rsplit(":", 1)[1]
            if re.fullmatch(r"\d{1,6}", page_raw):
                page = int(page_raw)
        await admin_gift_codes(query, page)
    elif data == "admin:giftcode:add":
        context.user_data.clear()
        context.user_data["mode"] = "gift_code_name"
        await query.edit_message_text(
            "أرسل كود الهدية: حرف واحد أو أكثر من الأحرف العربية أو الإنكليزية والأرقام، بدون رموز.",
            reply_markup=back_keyboard(
                "admin:gift_codes", "رجوع لأكواد الهدايا"
            ),
        )
    elif data.startswith("admin:giftcode:delete:"):
        id_raw = data.rsplit(":", 1)[1]
        if not re.fullmatch(r"\d{1,18}", id_raw):
            await query.edit_message_text(
                "تعذر تحديد كود الهدية.",
                reply_markup=back_keyboard(
                    "admin:gift_codes", "رجوع لأكواد الهدايا"
                ),
            )
            return
        async with database() as conn:
            gift_code = await fetch_one(
                conn,
                "SELECT code FROM nabil_gift_codes WHERE id = %s",
                (int(id_raw),),
            )
        if not gift_code:
            await query.edit_message_text(
                "كود الهدية غير موجود.",
                reply_markup=back_keyboard(
                    "admin:gift_codes", "رجوع لأكواد الهدايا"
                ),
            )
            return
        await query.edit_message_text(
            f"تأكيد حذف الكود <code>{safe_html(gift_code['code'], 64)}</code>؟ "
            "لن يعود قابلاً للاستخدام، لكن الأرصدة التي أضيفت سابقاً لن تتأثر.",
            reply_markup=InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            "نعم، احذف الكود",
                            callback_data=f"admin:giftcode:delete_confirm:{id_raw}",
                        )
                    ],
                    [
                        InlineKeyboardButton(
                            "إلغاء",
                            callback_data="admin:gift_codes",
                        )
                    ],
                ]
            ),
            parse_mode=ParseMode.HTML,
        )
    elif data.startswith("admin:giftcode:delete_confirm:"):
        id_raw = data.rsplit(":", 1)[1]
        if not re.fullmatch(r"\d{1,18}", id_raw):
            await query.edit_message_text(
                "تعذر تحديد كود الهدية.",
                reply_markup=back_keyboard(
                    "admin:gift_codes", "رجوع لأكواد الهدايا"
                ),
            )
            return
        async with database() as conn:
            async with conn.transaction():
                deleted = await fetch_one(
                    conn,
                    "DELETE FROM nabil_gift_codes WHERE id = %s RETURNING code",
                    (int(id_raw),),
                )
                if deleted:
                    await conn.execute(
                        "DELETE FROM nabil_bot_settings WHERE setting_key = %s",
                        (f"gift_code_{deleted['code']}",),
                    )
        if deleted:
            await log_admin_action(
                user_id, "حذف كود هدية", details=deleted["code"]
            )
        else:
            await query.edit_message_text(
                "كود الهدية غير موجود.",
                reply_markup=back_keyboard(
                    "admin:gift_codes", "رجوع لأكواد الهدايا"
                ),
            )
            return
        await admin_gift_codes(query)
    elif data == "admin:broadcast":
        await admin_broadcast_menu(query)
    elif data == "admin:broadcast:start":
        await begin_broadcast(query, context)
    elif data == "admin:broadcast:delay":
        context.user_data.clear()
        context.user_data["mode"] = "broadcast_delay"
        await query.edit_message_text(
            f"أرسل الفاصل الزمني بالثواني من {BROADCAST_DELAY_MIN:g} "
            f"إلى {BROADCAST_DELAY_MAX:g}. القيمة الحالية: "
            f"{await get_broadcast_delay():g} ثانية.",
            reply_markup=back_keyboard("admin:broadcast", "رجوع لقسم الإذاعة"),
        )
    elif data == "admin:broadcast:preview":
        await show_broadcast_confirmation(query, context)
    elif data == "admin:broadcast:button:add":
        if not context.user_data.get("broadcast_source_message_id"):
            await query.edit_message_text(
                "لم يتم حفظ محتوى للإذاعة. ابدأ من جديد.",
                reply_markup=back_keyboard("admin:broadcast", "رجوع لقسم الإذاعة"),
            )
        else:
            context.user_data["mode"] = "broadcast_button_label"
            await query.edit_message_text(
                "أرسل نص الزر التفاعلي (حتى 64 حرفاً).",
                reply_markup=back_keyboard(
                    "admin:broadcast:preview", "رجوع للمعاينة"
                ),
            )
    elif data == "admin:broadcast:button:remove":
        context.user_data.pop("broadcast_button_label", None)
        context.user_data.pop("broadcast_button_url", None)
        context.user_data["mode"] = "broadcast_options"
        await show_broadcast_confirmation(query, context)
    elif data == "admin:broadcast:send":
        await run_broadcast(query, context, user_id)
    elif data == "admin:owner":
        owner_text = f"<code>{OWNER_ID}</code>" if OWNER_ID else "غير مضبوط"
        await query.edit_message_text(
            f"آيدي المالك: {owner_text}\n"
            "لأمان الحساب، لا يمكن تغيير المالك من داخل البوت.",
            reply_markup=InlineKeyboardMarkup(
                [[InlineKeyboardButton("رجوع للإعدادات", callback_data="admin:settings")]]
            ),
            parse_mode=ParseMode.HTML,
        )
    elif data.startswith("setting:"):
        key = data.split(":", 1)[1]
        text_prompts = {
            "welcome_text": "أرسل رسالة البداية. المتغيرات المتاحة: {name} و{id}.",
            "help_text": "أرسل نص المساعدة الجديد.",
            "maintenance_text": "أرسل رسالة إيقاف البوت التي تظهر للأعضاء.",
        }
        channel_modes = {
            "required_channel_chat": "أرسل @اسم_القناة أو رقم القناة الذي يبدأ بـ -100. اكتب «مسح» لإزالة الإعداد.",
            "required_channel_url": "أرسل رابط الانضمام الذي يبدأ بـ https://t.me/، أو اكتب «مسح» لإزالته.",
            "public_channel_url": "أرسل رابط القناة العامة الذي يبدأ بـ https://t.me/، أو اكتب «مسح» لإزالته.",
        }
        numeric_prompts = {
            "daily_balance_reward": (
                f"أرسل الحد الأدنى والأعلى للهدية اليومية بعملة {CURRENCY}، "
                "مثال: 100 200. أرسل رقماً واحداً لمبلغ ثابت، أو 0 لإيقافها."
            ),
            "referral_referrer_balance_reward": (
                f"أرسل مكافأة الرصيد لصاحب الدعوة بعملة {CURRENCY}. "
                "أرسل 0 لإيقاف المكافأة."
            ),
            "referral_invitee_balance_reward": (
                f"أرسل مكافأة الرصيد للعضو الجديد بعملة {CURRENCY}. "
                "أرسل 0 لإيقاف المكافأة."
            ),
            "min_balance_transfer": f"أرسل الحد الأدنى للتحويل بعملة {CURRENCY}.",
        }
        if key in text_prompts:
            context.user_data.clear()
            context.user_data.update({"mode": "admin_setting_text", "setting_key": key})
            await query.edit_message_text(
                text_prompts[key],
                reply_markup=back_keyboard("admin:copy", "رجوع للنصوص"),
            )
        elif key in channel_modes:
            context.user_data.clear()
            context.user_data["mode"] = key
            await query.edit_message_text(
                channel_modes[key],
                reply_markup=back_keyboard("admin:channel", "رجوع للقنوات"),
            )
        elif key in numeric_prompts:
            context.user_data.clear()
            context.user_data.update({"mode": "admin_setting_value", "setting_key": key})
            await query.edit_message_text(
                numeric_prompts[key],
                reply_markup=back_keyboard("admin:points_settings", "رجوع لإعدادات الرصيد والمكافآت"),
            )
        else:
            await query.edit_message_text(
                "إعداد غير معروف.",
                reply_markup=InlineKeyboardMarkup(
                    [[InlineKeyboardButton("رجوع", callback_data="admin:home")]]
                ),
            )
    elif data.startswith("admin:member:ledger:"):
        await admin_member_wallet_history(
            query, int(data.rsplit(":", 1)[1])
        )
    elif data.startswith("admin:member:"):
        await show_admin_member(query, int(data.rsplit(":", 1)[1]))
    elif data.startswith("member:ban:"):
        member_id = int(data.rsplit(":", 1)[1])
        async with database() as conn:
            async with conn.transaction():
                await conn.execute(
                    """
                    INSERT INTO nabil_bot_user_state (telegram_id)
                    SELECT telegram_id FROM nabil_members WHERE telegram_id = %s
                    ON CONFLICT (telegram_id) DO NOTHING
                    """,
                    (member_id,),
                )
                state = await fetch_one(
                    conn,
                    """
                    UPDATE nabil_bot_user_state SET is_banned = NOT is_banned, updated_at = NOW()
                    WHERE telegram_id = %s
                    RETURNING is_banned
                    """,
                    (member_id,),
                )
                if state:
                    await insert_admin_audit(
                        conn,
                        user_id,
                        "حظر عضو" if state["is_banned"] else "إلغاء حظر عضو",
                        member_id,
                    )
        await show_admin_member(query, member_id)
    elif data == "admin:orders":
        await admin_orders(query)
    elif data.startswith("admin:orders:"):
        await admin_orders(query, int(data.rsplit(":", 1)[1]))
    elif data.startswith("admin:order:"):
        await show_admin_order(query, int(data.rsplit(":", 1)[1]))
    elif data == "admin:settings":
        context.user_data.clear()
        await admin_settings(query)
    elif data == "admin:providers":
        context.user_data.clear()
        await admin_providers(query)
    elif data == "admin:services":
        context.user_data.clear()
        await list_admin_services(query, 0)
    elif data == "admin:engagement:add":
        context.user_data.clear()
        if not update.effective_chat or update.effective_chat.type != "private":
            await query.edit_message_text(
                "ابدأ إضافة الخدمة من المحادثة الخاصة مع البوت.",
                reply_markup=back_keyboard(
                    "admin:services:engagement:0",
                    "رجوع للمشاهدات والتفاعلات",
                ),
            )
            return
        context.user_data["mode"] = "engagement_service_name"
        await query.edit_message_text(
            "الخطوة 1 من 8: أرسل اسم الخدمة الذي سيظهر للمستخدمين.",
            reply_markup=back_keyboard(
                "admin:services:engagement:0", "إلغاء الإضافة"
            ),
        )
    elif data == "admin:providers:setup":
        context.user_data.clear()
        if not update.effective_chat or update.effective_chat.type != "private":
            await query.edit_message_text(
                "افتح المحادثة الخاصة مع البوت، ثم ابدأ إضافة الخدمة من هناك.",
                reply_markup=back_keyboard("admin:providers", "رجوع للمزود الرئيسي"),
            )
            return
        context.user_data["member_service_domain"] = KD1S_API_URL
        context.user_data["mode"] = "member_service_api_key"
        await query.edit_message_text(
            "أرسل مفتاح API لـ KD1S برسالة خاصة. سيحذف البوت الرسالة فوراً "
            "ثم يحفظ المفتاح مشفراً.\n"
            f"رابط API المستخدم: {KD1S_API_URL}",
            reply_markup=back_keyboard("admin:providers", "رجوع للمزود الرئيسي"),
        )
    elif data == "admin:services:members:add":
        context.user_data.clear()
        await admin_providers(query)
    elif data.startswith("admin:services:members:"):
        context.user_data.clear()
        await admin_providers(query)
    elif data.startswith("admin:services:engagement:"):
        context.user_data.clear()
        await list_admin_services(
            query, int(data.rsplit(":", 1)[1]), service_group="engagement"
        )
    elif data.startswith("admin:services:"):
        await list_admin_services(query, int(data.rsplit(":", 1)[1]))
    elif data == "admin:sync":
        context.user_data.clear()
        await admin_providers(query)
    elif data == "admin:report":
        context.user_data.clear()
        await admin_report(query)
    elif data == "admin:audit":
        context.user_data.clear()
        await admin_audit_log(query)
    elif data == "admin:wallet":
        context.user_data.clear()
        await admin_wallet_menu(query, user_id)
    elif data == "wallet:history":
        context.user_data.clear()
        await admin_wallet_history(query)
    elif data == "wallet:cancel":
        context.user_data.clear()
        await admin_wallet_menu(query, user_id)
    elif data == "wallet:confirm":
        await complete_wallet_adjustment(query, context, user_id)
    elif data.startswith("adminpoints:"):
        context.user_data.clear()
        await admin_wallet_menu(query, user_id)
    elif data in ("wallet:credit", "wallet:debit"):
        await begin_wallet_adjustment(query, context, data.split(":")[1])
    elif data.startswith(
        ("wallet:credit:", "wallet:debit:", "points:credit:", "points:debit:")
    ):
        _, adjustment, member_id_raw = data.split(":")
        member_id = int(member_id_raw)
        context.user_data.clear()
        member = await get_wallet_member(member_id)
        if not member:
            await query.edit_message_text(
                "هذا العضو غير مسجل في البوت.",
                reply_markup=back_keyboard(
                    f"admin:member:{member_id}", "رجوع لمعلومات العضو"
                ),
            )
            return
        balance_before = money(Decimal(str(member["balance"])))
        context.user_data.update(
            {
                "mode": "wallet_amount",
                "member_id": member_id,
                "wallet_member_name": wallet_member_name(member),
                "wallet_balance_before": str(balance_before),
                "wallet_adjustment": adjustment,
                "wallet_return_callback": f"admin:member:{member_id}",
                "wallet_return_label": "رجوع لمعلومات العضو",
            }
        )
        await query.edit_message_text(
            f"العضو: {wallet_member_name(member)}\n"
            f"الآيدي: {member_id}\n"
            f"رصيده الحالي: {fmt_money(balance_before)}\n\n"
            f"أرسل مبلغ {'إضافة' if adjustment == 'credit' else 'خصم'} الرصيد الموجب.",
            reply_markup=back_keyboard(
                f"admin:member:{member_id}", "رجوع لمعلومات العضو"
            ),
        )
    elif data == "provider:key:renew":
        await begin_provider_api_key_rekey(query, context)
    elif data == "provider:key:renew:confirm":
        if context.user_data.get("mode") != "provider_api_key_rekey_confirm":
            context.user_data.clear()
            await query.edit_message_text(
                "انتهت جلسة تأكيد المفتاح. ابدأ التجديد من جديد.",
                reply_markup=back_keyboard("admin:providers", "رجوع للمزود"),
            )
            return
        await finish_provider_api_key_rekey(query, context, user_id)
    elif data == "provider:key:renew:cancel":
        context.user_data.clear()
        await admin_providers(query)
    elif data == "provider:rekey:confirm":
        try:
            provider_service_id = str(
                context.user_data["member_service_rekey_service_id"]
            )
            base_rate = Decimal(
                str(context.user_data["member_service_rekey_rate"])
            )
            min_quantity = int(
                context.user_data["member_service_rekey_min"]
            )
            max_quantity = int(
                context.user_data["member_service_rekey_max"]
            )
        except (KeyError, InvalidOperation, TypeError, ValueError):
            context.user_data.clear()
            await query.edit_message_text(
                "انتهت جلسة تجديد المفتاح. ابدأ إعداد المزود من جديد.",
                reply_markup=back_keyboard(
                    "admin:providers:setup", "إعادة الإعداد"
                ),
            )
            return
        await setup_member_service_from_credentials(
            update,
            context,
            provider_service_id,
            base_rate,
            min_quantity,
            max_quantity,
            allow_pending_rekey=True,
        )
    elif data == "provider:rekey:cancel":
        context.user_data.clear()
        await admin_providers(query)
    elif data.startswith("provider:balance:"):
        await check_provider_balance(query, int(data.rsplit(":", 1)[1]))
    elif data == "provider:add" or data.startswith(
        (
            "provider:view:",
            "provider:domain:",
            "provider:key:",
            "provider:sync:",
            "provider:margin:",
            "provider:toggle:",
            "provider:archive:",
        )
    ):
        context.user_data.clear()
        await admin_providers(query)
    elif data.startswith("service:member:review:"):
        await admin_providers(query)
    elif data.startswith("service:member:activate:"):
        await admin_providers(query)
    elif data.startswith("service:delete_confirm:"):
        id_raw = data.rsplit(":", 1)[1]
        if not re.fullmatch(r"\d{1,18}", id_raw):
            await query.edit_message_text(
                "تعذر تحديد الخدمة المطلوب حذفها.",
                reply_markup=back_keyboard(
                    "admin:services:engagement:0",
                    "رجوع للمشاهدات والتفاعلات",
                ),
            )
            return
        service_id = int(id_raw)
        async with database() as conn:
            async with conn.transaction():
                service = await fetch_one(
                    conn,
                    """
                    SELECT s.id, s.provider_id, s.category,
                           COALESCE(NULLIF(s.custom_name, ''), s.provider_name) AS name
                    FROM nabil_services s
                    WHERE s.id = %s
                    FOR UPDATE
                    """,
                    (service_id,),
                )
                if not service or service["category"] != "مشاهدات وتفاعلات":
                    has_orders = None
                else:
                    order_refs = await fetch_one(
                        conn,
                        """
                        SELECT EXISTS (
                          SELECT 1 FROM nabil_orders
                          WHERE service_id = %s OR provider_id = %s
                        ) AS has_orders
                        """,
                        (service_id, service["provider_id"]),
                    )
                    has_orders = bool(order_refs["has_orders"])
                if service and has_orders is False:
                    await insert_admin_audit(
                        conn,
                        user_id,
                        "حذف خدمة مشاهدات وتفاعلات",
                        service_id,
                        f"الخدمة: {safe_text(service['name'], 80)}",
                    )
                    await conn.execute(
                        "DELETE FROM nabil_services WHERE id = %s",
                        (service_id,),
                    )
                    await conn.execute(
                        """
                        DELETE FROM nabil_providers p
                        WHERE p.id = %s
                          AND NOT EXISTS (
                            SELECT 1 FROM nabil_services s
                            WHERE s.provider_id = p.id
                          )
                          AND NOT EXISTS (
                            SELECT 1 FROM nabil_orders o
                            WHERE o.provider_id = p.id
                          )
                        """,
                        (service["provider_id"],),
                    )
        if not service or service["category"] != "مشاهدات وتفاعلات":
            await query.edit_message_text(
                "الخدمة غير موجودة أو لا تنتمي إلى قسم المشاهدات والتفاعلات.",
                reply_markup=back_keyboard(
                    "admin:services:engagement:0",
                    "رجوع للمشاهدات والتفاعلات",
                ),
            )
        elif has_orders:
            await query.edit_message_text(
                "لا يمكن حذف هذه الخدمة لأنها مرتبطة بطلبات سابقة. "
                "أرشفها بدلاً من ذلك حتى يبقى سجل الطلبات محفوظاً.",
                reply_markup=InlineKeyboardMarkup(
                    [
                        [
                            InlineKeyboardButton(
                                "عرض الخدمة",
                                callback_data=f"service:view:{service_id}",
                            )
                        ],
                        [
                            InlineKeyboardButton(
                                "رجوع للقسم",
                                callback_data="admin:services:engagement:0",
                            )
                        ],
                    ]
                ),
            )
        else:
            await list_admin_services(
                query, 0, service_group="engagement"
            )
    elif data.startswith("service:delete_cancel:"):
        id_raw = data.rsplit(":", 1)[1]
        if re.fullmatch(r"\d{1,18}", id_raw):
            await show_admin_service(query, int(id_raw))
        else:
            await list_admin_services(query, 0, service_group="engagement")
    elif data.startswith("service:delete:"):
        id_raw = data.rsplit(":", 1)[1]
        if not re.fullmatch(r"\d{1,18}", id_raw):
            await query.edit_message_text(
                "تعذر تحديد الخدمة المطلوب حذفها.",
                reply_markup=back_keyboard(
                    "admin:services:engagement:0",
                    "رجوع للمشاهدات والتفاعلات",
                ),
            )
            return
        service_id = int(id_raw)
        async with database() as conn:
            service = await fetch_one(
                conn,
                """
                SELECT s.id, s.category,
                       COALESCE(NULLIF(s.custom_name, ''), s.provider_name) AS name
                FROM nabil_services s
                WHERE s.id = %s
                """,
                (service_id,),
            )
        if not service or service["category"] != "مشاهدات وتفاعلات":
            await query.edit_message_text(
                "الخدمة غير موجودة أو لا تنتمي إلى قسم المشاهدات والتفاعلات.",
                reply_markup=back_keyboard(
                    "admin:services:engagement:0",
                    "رجوع للمشاهدات والتفاعلات",
                ),
            )
            return
        await query.edit_message_text(
            f"تأكيد حذف الخدمة <b>{safe_html(service['name'], 120)}</b>؟\n"
            "لن تُعرض للمستخدمين بعد الحذف. إذا كانت مرتبطة بطلبات سابقة، "
            "سيمنع النظام حذفها حفاظاً على سجل الطلبات.",
            reply_markup=InlineKeyboardMarkup(
                [
                    [
                        InlineKeyboardButton(
                            "نعم، احذف الخدمة",
                            callback_data=f"service:delete_confirm:{service_id}",
                        )
                    ],
                    [
                        InlineKeyboardButton(
                            "إلغاء",
                            callback_data=f"service:delete_cancel:{service_id}",
                        )
                    ],
                ]
            ),
            parse_mode=ParseMode.HTML,
        )
    elif data.startswith("service:view:"):
        context.user_data.clear()
        await show_admin_service(query, int(data.rsplit(":", 1)[1]))
    elif data.startswith("service:name:"):
        context.user_data.clear()
        service_id = int(data.rsplit(":", 1)[1])
        context.user_data.update(
            {"mode": "service_name", "service_id": service_id}
        )
        await query.edit_message_text(
            "أرسل الاسم الجديد للخدمة.",
            reply_markup=back_keyboard(f"service:view:{service_id}", "رجوع للخدمة"),
        )
    elif data.startswith("service:markup:"):
        context.user_data.clear()
        service_id = int(data.rsplit(":", 1)[1])
        context.user_data.update(
            {"mode": "service_markup", "service_id": service_id}
        )
        await query.edit_message_text(
            "أرسل نسبة الربح من 0 إلى 1000.",
            reply_markup=back_keyboard(f"service:view:{service_id}", "رجوع للخدمة"),
        )
    elif data.startswith("service:toggle:"):
        service_id = int(data.rsplit(":", 1)[1])
        async with database() as conn:
            row = await fetch_one(
                conn,
                """
                SELECT s.enabled, p.enabled AS provider_enabled
                FROM nabil_services s JOIN nabil_providers p ON p.id = s.provider_id
                WHERE s.id = %s
                """,
                (service_id,),
            )
            if row:
                new_state = not row["enabled"]
                await conn.execute(
                    "UPDATE nabil_services SET enabled = %s WHERE id = %s",
                    (new_state, service_id),
                )
                await insert_admin_audit(
                    conn,
                    user_id,
                    "تغيير حالة خدمة",
                    service_id,
                    f"{'مفعّلة' if row['enabled'] else 'متوقفة'} → "
                    f"{'مفعّلة' if new_state else 'متوقفة'}",
                )
        await show_admin_service(query, service_id)
    else:
        action = safe_text(data or "غير محدد", 100)
        LOG.warning(
            "Button action %s has no handler — its callback is not recognized.",
            action,
        )
        await query.answer(
            "هذا الزر لم يعد يعمل. ارجع للقائمة وافتحها من جديد.",
            show_alert=True,
        )


async def initialize_bot(application: Application):
    # Existing product schema is provisioned in the project database; these
    # additive tables support the owner-managed admin permissions and audit log.
    async with database() as conn:
        # Avoid concurrent bot instances racing while creating/updating tables.
        await conn.execute("SELECT pg_advisory_xact_lock(731941025187)")
        await fetch_one(conn, "SELECT 1 AS ready")
        await conn.execute(
            """
            UPDATE nabil_providers AS p
            SET api_key_encrypted = %s
            WHERE p.enabled = FALSE
              AND NOT EXISTS (
                SELECT 1 FROM nabil_orders AS o
                WHERE o.provider_id = p.id
                  AND o.provider_order_id IS NOT NULL
                  AND o.status IN ('Pending', 'Processing')
              )
            """,
            (encrypt_secret(""),),
        )
        await conn.execute(
            """
            CREATE TABLE IF NOT EXISTS nabil_bot_admin_permissions (
                telegram_id BIGINT PRIMARY KEY,
                can_orders BOOLEAN NOT NULL DEFAULT TRUE,
                can_members BOOLEAN NOT NULL DEFAULT TRUE,
                can_wallet BOOLEAN NOT NULL DEFAULT FALSE,
                can_reports BOOLEAN NOT NULL DEFAULT TRUE,
                can_services BOOLEAN NOT NULL DEFAULT TRUE,
                can_broadcast BOOLEAN NOT NULL DEFAULT FALSE,
                can_force_subscription BOOLEAN NOT NULL DEFAULT FALSE,
                updated_by BIGINT,
                updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
            """
        )
        await conn.execute(
            """
            CREATE TABLE IF NOT EXISTS nabil_admin_audit (
                id BIGSERIAL PRIMARY KEY,
                actor_id BIGINT NOT NULL,
                action TEXT NOT NULL,
                target_id BIGINT,
                details TEXT NOT NULL DEFAULT '',
                created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
            """
        )
        await conn.execute(
            """
            CREATE TABLE IF NOT EXISTS nabil_subscription_exemptions (
                telegram_id BIGINT PRIMARY KEY CHECK (telegram_id > 0),
                added_by BIGINT NOT NULL,
                created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
            """
        )
        await conn.execute(
            """
            CREATE TABLE IF NOT EXISTS nabil_human_verifications (
                telegram_id BIGINT PRIMARY KEY CHECK (telegram_id > 0),
                verified_at TIMESTAMPTZ,
                verification_code_hash TEXT,
                code_expires_at TIMESTAMPTZ,
                failed_attempts SMALLINT NOT NULL DEFAULT 0
                    CHECK (failed_attempts >= 0),
                pending_referral_id BIGINT
            )
            """
        )
        await conn.execute(
            """
            INSERT INTO nabil_human_verifications (telegram_id, verified_at)
            SELECT known_users.telegram_id, NOW()
            FROM (
                SELECT telegram_id FROM nabil_members
                UNION
                SELECT telegram_id FROM nabil_bot_user_state
                UNION
                SELECT telegram_id FROM nabil_bot_admins
            ) AS known_users
            ON CONFLICT (telegram_id) DO NOTHING
            """
        )
        await conn.execute(
            """
            CREATE TABLE IF NOT EXISTS nabil_bot_alerts (
                id BIGSERIAL PRIMARY KEY,
                fingerprint TEXT NOT NULL UNIQUE,
                source TEXT NOT NULL
                    CHECK (source IN ('bot', 'provider', 'service')),
                severity TEXT NOT NULL
                    CHECK (severity IN ('warning', 'error', 'critical')),
                title TEXT NOT NULL,
                details TEXT NOT NULL DEFAULT '',
                state TEXT NOT NULL DEFAULT 'active'
                    CHECK (state IN ('active', 'resolved')),
                occurrence_count INTEGER NOT NULL DEFAULT 0
                    CHECK (occurrence_count >= 0),
                first_seen_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
                last_seen_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
                last_notified_at TIMESTAMPTZ,
                resolved_at TIMESTAMPTZ,
                resolved_by BIGINT
            )
            """
        )
        await conn.execute(
            """
            CREATE INDEX IF NOT EXISTS nabil_bot_alerts_state_last_seen_idx
            ON nabil_bot_alerts (state, last_seen_at DESC)
            """
        )
        await conn.execute(
            """
            CREATE TABLE IF NOT EXISTS nabil_bot_heartbeat (
                singleton_id SMALLINT PRIMARY KEY CHECK (singleton_id = 1),
                last_seen_at TIMESTAMPTZ NOT NULL,
                stopped_alerted_at TIMESTAMPTZ
            )
            """
        )
        await conn.execute(
            """
            INSERT INTO nabil_bot_heartbeat (singleton_id, last_seen_at)
            VALUES (1, NOW())
            ON CONFLICT (singleton_id)
            DO UPDATE SET last_seen_at = EXCLUDED.last_seen_at
            """
        )
        await conn.execute(
            """
            CREATE TABLE IF NOT EXISTS nabil_bot_agents (
                telegram_id BIGINT PRIMARY KEY,
                wallet_points BIGINT NOT NULL DEFAULT 0
                    CHECK (wallet_points >= 0 AND wallet_points <= 1000000000),
                status TEXT NOT NULL DEFAULT 'active'
                    CHECK (status IN ('active', 'inactive', 'archived')),
                added_by BIGINT NOT NULL,
                created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
                updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
            """
        )
        await conn.execute(
            """
            CREATE TABLE IF NOT EXISTS nabil_agent_transactions (
                id BIGSERIAL PRIMARY KEY,
                agent_id BIGINT NOT NULL,
                actor_id BIGINT NOT NULL,
                operation TEXT NOT NULL,
                amount NUMERIC(20, 3) NOT NULL,
                wallet_before NUMERIC(20, 3) NOT NULL,
                wallet_after NUMERIC(20, 3) NOT NULL,
                target_id BIGINT,
                member_points_before NUMERIC(20, 3),
                member_points_after NUMERIC(20, 3),
                details TEXT NOT NULL DEFAULT '',
                created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
            """
        )
        await conn.execute(
            """
            ALTER TABLE nabil_agent_transactions
            ALTER COLUMN amount TYPE NUMERIC(20, 3) USING amount::numeric,
            ALTER COLUMN wallet_before TYPE NUMERIC(20, 3) USING wallet_before::numeric,
            ALTER COLUMN wallet_after TYPE NUMERIC(20, 3) USING wallet_after::numeric,
            ALTER COLUMN member_points_before TYPE NUMERIC(20, 3)
              USING member_points_before::numeric,
            ALTER COLUMN member_points_after TYPE NUMERIC(20, 3)
              USING member_points_after::numeric
            """
        )
        await conn.execute(
            """
            CREATE INDEX IF NOT EXISTS nabil_agent_transactions_agent_created_idx
            ON nabil_agent_transactions (agent_id, created_at DESC)
            """
        )
        await conn.execute(
            """
            ALTER TABLE nabil_providers
            ADD COLUMN IF NOT EXISTS last_sync_duration_ms INTEGER
            """
        )
        await conn.execute(
            """
            INSERT INTO nabil_bot_admin_permissions (
                telegram_id, can_orders, can_members, can_wallet, can_reports,
                can_services, can_broadcast, can_force_subscription, updated_by
            )
            SELECT telegram_id, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, added_by
            FROM nabil_bot_admins
            ON CONFLICT (telegram_id) DO NOTHING
            """
        )
        await migrate_to_unified_iqd_wallet(conn)
        await conn.execute(
            """
            CREATE TABLE IF NOT EXISTS nabil_gift_codes (
                id BIGSERIAL PRIMARY KEY,
                code TEXT NOT NULL UNIQUE,
                reward NUMERIC(18, 3) NOT NULL CHECK (reward > 0),
                max_uses INTEGER NOT NULL CHECK (max_uses > 0),
                expires_at TIMESTAMPTZ,
                created_by BIGINT,
                created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
            """
        )
        await conn.execute(
            """
            CREATE TABLE IF NOT EXISTS nabil_gift_code_redemptions (
                gift_code_id BIGINT NOT NULL,
                member_id BIGINT NOT NULL,
                reward NUMERIC(18, 3) NOT NULL,
                redeemed_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
                PRIMARY KEY (gift_code_id, member_id)
            )
            """
        )
        legacy_codes = await fetch_all(
            conn,
            """
            SELECT setting_key, setting_value
            FROM nabil_bot_settings
            WHERE LEFT(setting_key, 10) = 'gift_code_'
            """,
        )
        for legacy_code in legacy_codes:
            code = legacy_code["setting_key"][10:]
            if not re.fullmatch(r"[A-Z0-9_-]{3,32}", code):
                continue
            try:
                reward = money(Decimal(str(legacy_code["setting_value"])))
                if reward <= 0 or reward > Decimal("1000000000"):
                    continue
            except (InvalidOperation, TypeError, ValueError):
                continue
            await conn.execute(
                """
                INSERT INTO nabil_gift_codes
                  (code, reward, max_uses, expires_at, created_by)
                VALUES (%s, %s, 2147483647, NULL, %s)
                ON CONFLICT (code) DO NOTHING
                """,
                (code, reward, OWNER_ID),
            )
        await conn.execute(
            """
            INSERT INTO nabil_gift_code_redemptions
              (gift_code_id, member_id, reward)
            SELECT g.id, l.member_id, l.amount
            FROM nabil_gift_codes AS g
            JOIN nabil_ledger AS l
              ON LEFT(l.note, LENGTH('gift_code:' || g.code || ':')) =
                 'gift_code:' || g.code || ':'
            WHERE l.entry_type IN ('gift_code_points', 'gift_code_balance')
            ON CONFLICT (gift_code_id, member_id) DO NOTHING
            """
        )
        await conn.execute(
            """
            UPDATE nabil_bot_settings
            SET setting_value = %s, updated_at = NOW()
            WHERE setting_key = %s AND setting_value = %s
            """,
            (
                DEFAULT_SETTINGS["welcome_text"],
                "welcome_text",
                "مرحباً {name} في بوت التمويل\n\n⌁︙الايدي الخاص بك ↫⤈\nID : {id}",
            ),
        )
    global ALERT_LOOP, ALERT_LOG_HANDLER
    ALERT_LOOP = asyncio.get_running_loop()
    if ALERT_LOG_HANDLER is None:
        ALERT_LOG_HANDLER = BotAlertLogHandler()
        logging.getLogger().addHandler(ALERT_LOG_HANDLER)
    if OWNER_ID is None:
        LOG.warning("OWNER_TELEGRAM_ID is not configured; owner controls are disabled.")
    application.bot_data["live_mirror_task"] = asyncio.create_task(
        live_mirror_outbox_loop(application)
    )
    application.bot_data["poll_task"] = asyncio.create_task(poll_active_orders(application))
    application.bot_data["health_task"] = asyncio.create_task(
        monitor_bot_health(application)
    )
    application.bot_data["heartbeat_task"] = asyncio.create_task(
        heartbeat_bot()
    )
    LOG.info("Nabil bot started; owner configured=%s", OWNER_ID is not None)


async def on_startup(application: Application):
    global ALERT_LOOP, ALERT_LOG_HANDLER
    ALERT_LOOP = asyncio.get_running_loop()
    if ALERT_LOG_HANDLER is None:
        ALERT_LOG_HANDLER = BotAlertLogHandler()
        logging.getLogger().addHandler(ALERT_LOG_HANDLER)
    try:
        await initialize_bot(application)
    except Exception as exc:
        await record_bot_alert(
            fingerprint="bot-startup-failure",
            source="bot",
            severity="critical",
            title="تعذر تشغيل البوت",
            details=safe_text(exc, 220),
        )
        raise


async def on_shutdown(application: Application):
    for task_name in (
        "live_mirror_task",
        "poll_task",
        "health_task",
        "heartbeat_task",
    ):
        task = application.bot_data.get(task_name)
        if not task:
            continue
        task.cancel()
        try:
            await task
        except asyncio.CancelledError:
            pass


async def telegram_error_handler(
    update: object, context: ContextTypes.DEFAULT_TYPE
):
    error = context.error
    if isinstance(error, Conflict):
        LOG.error(
            "Telegram polling conflict — another bot instance is using this token."
        )
        return
    error_name = type(error).__name__ if error else "UnknownError"
    error_details = safe_text(error, 500)
    query = update.callback_query if isinstance(update, Update) else None
    if query:
        action = safe_text(query.data or "زر بدون إجراء معروف", 100)
        LOG.error(
            "Button action %s failed — %s: %s",
            action,
            error_name,
            error_details,
        )
        return
    update_kind = type(update).__name__ if update else "unknown update"
    LOG.error(
        "Telegram handler failed for %s — %s: %s",
        update_kind,
        error_name,
        error_details,
    )


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--watchdog":
        try:
            asyncio.run(run_watchdog())
        except KeyboardInterrupt:
            pass
        return
    if not BOT_TOKEN:
        raise RuntimeError("TELEGRAM_BOT_TOKEN is missing. Add it using Replit Secrets.")
    if not DATABASE_URL:
        raise RuntimeError("DATABASE_URL is missing. Enable the project's PostgreSQL database.")
    application = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(on_startup)
        .post_shutdown(on_shutdown)
        .build()
    )
    application.add_handler(TypeHandler(Update, subscription_gate), group=-1)
    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("admin", admin_command))
    application.add_handler(CommandHandler("agent", agent_panel_command))
    application.add_handler(CommandHandler("id", myid))
    application.add_handler(CommandHandler("myid", myid))
    application.add_handler(CommandHandler("cancel", cancel_command))
    application.add_handler(CallbackQueryHandler(callback_handler))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))
    application.add_handler(
        MessageHandler(filters.ALL & ~filters.COMMAND, capture_broadcast_content),
        group=1,
    )
    application.add_error_handler(telegram_error_handler)
    application.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=False)


if __name__ == "__main__":
    main()
