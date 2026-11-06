"""Single-file version of RashqZe.

Adapted from Source-Ze/RashqZe, distributed under GNU GPL version 3.
The original project includes the GPL-3.0 license; retain that license when
redistributing this derivative. License text: https://www.gnu.org/licenses/gpl-3.0.txt

Install dependencies with:
    pip install pyrogram pyromod kvsqlite requests

Configure these environment variables before running:
    TG_BOT_TOKEN, API_HASH, DB_PASSWORD
Optional:
    APP_ID (defaults to 21627756), ADMIN_IDS (comma-separated Telegram user IDs),
    DATABASE_PATH (defaults to data.sqlite)

Use the original database password in DB_PASSWORD when opening an existing database.
"""

import asyncio
import datetime
import os
import random
import time
from urllib.parse import urlsplit

from dotenv import load_dotenv
import pyromod  # noqa: F401 - installs Client.ask used by the conversation prompts
import requests
from kvsqlite.sync import Client as KVClient
from pyrogram import Client, filters
from pyrogram.enums import ChatMemberStatus, ParseMode
from pyrogram.types import InlineKeyboardButton as Button
from pyrogram.types import InlineKeyboardMarkup as Keyboard


# ---------------------------------------------------------------------------
# Configuration and database
# ---------------------------------------------------------------------------

load_dotenv()

TG_BOT_TOKEN = os.getenv("TG_BOT_TOKEN", "").strip()
API_ID = int(os.getenv("API_ID", "21627756"))
API_HASH = os.getenv("API_HASH", "").strip()
DATABASE_PATH = os.getenv("DATABASE_PATH", "data.sqlite")

if not TG_BOT_TOKEN:
    raise RuntimeError("Set TG_BOT_TOKEN in the environment before starting the bot.")
def configured_admin_ids():
    """Read the initial administrators from ADMIN_IDS."""
    result = []
    for raw_id in os.environ.get("ADMIN_IDS", "").split(","):
        raw_id = raw_id.strip()
        if raw_id:
            try:
                result.append(int(raw_id))
            except ValueError as exc:
                raise RuntimeError("ADMIN_IDS must contain comma-separated integers.") from exc
    return list(dict.fromkeys(result))


BOOTSTRAP_ADMIN_IDS = configured_admin_ids()
db = KVClient(DATABASE_PATH)

DEFAULTS = {
    "ban_list": [],
    "force": ["ui_xb"],
    "force_msg": "يرجى الاشتراك في القناة التالية لاستخدام البوت:",
    "coin_msg": "$",
    "start_msg": "مرحباً بك في البوت",
    "invite_price": 0.1,
    "transfer": 100,
    "member_price": 0.2,
    "bot_enabled": True,
    "join_notifications": True,
}

if not db.exists("admin_list"):
    db.set("admin_list", BOOTSTRAP_ADMIN_IDS)
for setting, default_value in DEFAULTS.items():
    if not db.exists(setting):
        db.set(setting, default_value)

if not db.get("admin_list") and not BOOTSTRAP_ADMIN_IDS:
    print("Warning: no administrators configured; set ADMIN_IDS to enable admin tools.")

bot = Client(
    name="RashqZe",
    api_id=APP_ID,
    api_hash=API_HASH,
    bot_token=TG_BOT_TOKEN,
    workers=20,
    parse_mode=ParseMode.DEFAULT,
)

balance_lock = asyncio.Lock()


def get_admin_ids():
    stored = db.get("admin_list") or []
    return set(BOOTSTRAP_ADMIN_IDS) | {
        int(user_id) for user_id in stored if str(user_id).lstrip("-").isdigit()
    }


def is_admin(user_id):
    return int(user_id) in get_admin_ids()


async def require_admin(query):
    if is_admin(query.from_user.id):
        return True
    await query.answer("غير مصرح لك باستخدام هذا الأمر", show_alert=True)
    return False


def user_ids():
    """Yield numeric user IDs from profile keys, not related settings keys."""
    for item in db.keys():
        key = item[0] if isinstance(item, (tuple, list)) else item
        key = str(key)
        suffix = key[5:] if key.startswith("user_") else ""
        if suffix.isdigit():
            yield int(suffix)


def get_user(user_id):
    return db.get(f"user_{int(user_id)}")


def ensure_user(user_id):
    profile = get_user(user_id)
    if profile is None:
        profile = {
            "coins": 0.2,
            "id": int(user_id),
            "premium": False,
            "admin": False,
            "phone": [],
            "users": [],
            "date": str(time.time()),
        }
        db.set(f"user_{int(user_id)}", profile)
    return profile


def make_user_keyboard(profile):
    balance = float(profile.get("coins", 0))
    return Keyboard(
        [
            [Button(f"رصيدك : {balance:g} $", callback_data="lol")],
            [Button("طلب رشق أعضاء", callback_data="member")],
            [
                Button("تجميع النقاط", callback_data="sharelink"),
                Button("شراء رصيد", url="https://t.me/EK_N1"),
            ],
            [
                Button("معلومات حسابك", callback_data="account"),
                Button("تحويل رصيد", callback_data="tran"),
            ],
            [Button("معلومات الطلب", callback_data="id_requests")],
        ]
    )


def make_admin_keyboard():
    bot_state = "✅" if db.get("bot_enabled") else "❌"
    notification_state = "✅" if db.get("join_notifications") else "❌"
    return Keyboard(
        [
            [Button("آخر تحديثات البوت", url="https://t.me/UI_XB")],
            [
                Button(f"تشغيل البوت: {bot_state}", callback_data="toggle_bot"),
                Button(
                    f"إشعار دخول الأعضاء: {notification_state}",
                    callback_data="toggle_join_notifications",
                ),
            ],
            [Button("قسم تغيير الكليشة", callback_data="set_start")],
            [
                Button("الاشتراك الإجباري", callback_data="setforce"),
                Button("قسم الأدمنية", callback_data="admins_bot"),
            ],
            [
                Button("الإذاعة", callback_data="brods"),
                Button("الإحصائيات", callback_data="stats"),
            ],
            [Button("إعدادات البوت", callback_data="setting_bot")],
        ]
    )


def admin_panel_text():
    return (
        "**أهلاً بك في لوحة إدارة البوت**\n\n"
        "يمكنك إدارة الإعدادات والمستخدمين من الأزرار أدناه."
    )


async def show_user_home(client, user_id, destination):
    profile = get_user(user_id)
    if not profile:
        text = "لم يتم العثور على حسابك. أرسل /start للبدء."
        if hasattr(destination, "edit_message_text"):
            await destination.edit_message_text(text)
        else:
            await client.send_message(user_id, text)
        return

    start_text = db.get("start_msg") or "مرحباً بك في البوت"
    text = f"{start_text}\n\nمعرّفك: `{user_id}`"
    keyboard = make_user_keyboard(profile)
    if hasattr(destination, "edit_message_text"):
        await destination.edit_message_text(text, reply_markup=keyboard)
    else:
        await client.send_message(user_id, text, reply_markup=keyboard)


def is_banned(user_id):
    return int(user_id) in (db.get("ban_list") or [])


async def require_user_access(query):
    user_id = query.from_user.id
    if is_admin(user_id):
        return True
    if is_banned(user_id):
        await query.answer("حسابك محظور.", show_alert=True)
        return False
    if db.get("bot_enabled") is False:
        await query.answer("البوت متوقف مؤقتاً.", show_alert=True)
        return False
    return True


async def check_channel_member(client, channel, user_id):
    channel = str(channel).strip().lstrip("@")
    if not channel:
        return True
    try:
        member = await client.get_chat_member(
            chat_id=f"@{channel}", user_id=int(user_id)
        )
        return member.status in (
            ChatMemberStatus.OWNER,
            ChatMemberStatus.ADMINISTRATOR,
            ChatMemberStatus.MEMBER,
        )
    except Exception:
        # If membership cannot be checked, do not silently bypass the requirement.
        return False


async def require_membership(client, query):
    channels = db.get("force") or []
    message = db.get("force_msg") or "يرجى الاشتراك في القناة التالية:"
    for channel in channels:
        if not await check_channel_member(client, channel, query.from_user.id):
            channel_name = str(channel).strip().lstrip("@")
            await query.edit_message_text(
                f"{message}\n\n@{channel_name}",
                reply_markup=Keyboard(
                    [[Button("اضغط هنا للاشتراك", url=f"https://t.me/{channel_name}")]]
                ),
            )
            return False
    return True


async def verify_new_user(client, user_id, referrer_id=None, user=None):
    code = random.randint(100000, 999999)
    prompt = await client.ask(
        user_id,
        f"أرسل رمز التحقق التالي لإكمال التسجيل: `{code}`",
        filters=filters.user(user_id),
    )

    for attempt in range(5):
        try:
            if int(prompt.text or "") == code:
                ensure_user(user_id)
                await prompt.reply("تم التحقق بنجاح. أرسل /start لفتح القائمة.")

                if db.get("join_notifications") is not False:
                    display_name = user.mention if user else f"`{user_id}`"
                    username = f"@{user.username}" if user and user.username else "غير متاح"
                    for admin_id in get_admin_ids():
                        try:
                            await client.send_message(
                                admin_id,
                                "انضم عضو جديد إلى البوت.\n"
                                f"الاسم: {display_name}\n"
                                f"المعرّف: {username}\n"
                                f"ID: `{user_id}`\n"
                                f"إجمالي الأعضاء: {get_user_count()}",
                            )
                        except Exception:
                            pass

                if (
                    referrer_id
                    and int(referrer_id) != int(user_id)
                    and get_user(referrer_id)
                ):
                    inviter = get_user(referrer_id)
                    invited_users = inviter.setdefault("users", [])
                    if user_id not in invited_users:
                        reward = float(db.get("invite_price") or 0.1)
                        invited_users.append(user_id)
                        inviter["coins"] = float(inviter.get("coins", 0)) + reward
                        db.set(f"user_{int(referrer_id)}", inviter)
                        await client.send_message(
                            int(referrer_id),
                            f"دخل عضو جديد عبر رابطك؛ أضيف إلى رصيدك {reward:g} نقطة.",
                        )
                return profile
        except (TypeError, ValueError):
            pass

        if attempt < 4:
            prompt = await client.ask(
                user_id,
                "الرمز غير صحيح. أرسل رمز التحقق مرة أخرى.",
                filters=filters.user(user_id),
            )

    await client.send_message(user_id, "تعذر إكمال التحقق. أرسل /start للمحاولة مجدداً.")
    return None


def get_user_count():
    return sum(1 for _ in user_ids())


def leaderboard():
    profiles = []
    for user_id in user_ids():
        profile = get_user(user_id)
        if profile:
            profiles.append(profile)
    profiles.sort(key=lambda profile: len(profile.get("users", [])), reverse=True)
    lines = ["أكثر المشاركين في روابط الدعوة:"]
    for profile in profiles[:5]:
        lines.append(
            f"🏅 {len(profile.get('users', []))} مشاركة — "
            f"[{profile.get('id')}](tg://user?id={profile.get('id')})"
        )
    return "\n".join(lines)


def normalized_domain():
    raw_domain = str(db.get("set_domain") or "").strip()
    if not raw_domain:
        raise ValueError("لم يتم إعداد نطاق مزود الخدمة.")
    parsed = urlsplit(raw_domain if "://" in raw_domain else f"https://{raw_domain}")
    if parsed.scheme != "https" or not parsed.netloc:
        raise ValueError("يجب إعداد نطاق HTTPS صالح لمزود الخدمة.")
    base_path = parsed.path.rstrip("/")
    return f"https://{parsed.netloc}{base_path}/api/v2"


async def call_service_api(params):
    endpoint = normalized_domain()
    response = await asyncio.to_thread(
        requests.get, endpoint, params=params, timeout=25
    )
    response.raise_for_status()
    result = response.json()
    if not isinstance(result, dict):
        raise ValueError("استجابة مزود الخدمة غير صالحة.")
    return result


async def ask_admin_text(client, query, prompt):
    await query.answer()
    return await client.ask(
        query.from_user.id,
        prompt,
        filters=filters.user(query.from_user.id),
    )


# ---------------------------------------------------------------------------
# Commands and user-facing navigation
# ---------------------------------------------------------------------------

@bot.on_message(filters.private & filters.command("start"))
async def start_command(client, message):
    user_id = message.from_user.id
    if is_banned(user_id):
        return

    if is_admin(user_id):
        await message.reply(admin_panel_text(), reply_markup=make_admin_keyboard())
        return

    if db.get("bot_enabled") is False:
        await message.reply("البوت متوقف مؤقتاً. حاول مرة أخرى لاحقاً.")
        return

    if get_user(user_id):
        await show_user_home(client, user_id, message)
        return

    parts = (message.text or "").split(maxsplit=1)
    referrer_id = None
    if len(parts) == 2:
        try:
            referrer_id = int(parts[1].strip())
        except ValueError:
            referrer_id = None

    if referrer_id:
        await verify_new_user(client, user_id, referrer_id, message.from_user)
    else:
        await message.reply(
            f"مرحباً {message.from_user.mention}!\n"
            "اضغط الزر للتحقق وإنشاء حسابك.",
            reply_markup=Keyboard([[Button("التحقق", callback_data="send_code")]]),
        )


@bot.on_callback_query(filters.regex(r"^send_code$"))
async def verify_button(client, query):
    if not await require_user_access(query):
        return
    if get_user(query.from_user.id):
        await query.answer("تم التحقق من حسابك بالفعل.", show_alert=True)
        return
    await query.answer()
    await verify_new_user(client, query.from_user.id, None, query.from_user)


@bot.on_callback_query(filters.regex(r"^(back|back_home|back_invite)$"))
async def user_home_callback(client, query):
    if not await require_user_access(query):
        return
    await query.answer()
    await show_user_home(client, query.from_user.id, query)


@bot.on_callback_query(filters.regex(r"^lol$"))
async def balance_callback(client, query):
    if not await require_user_access(query):
        return
    profile = get_user(query.from_user.id)
    if not profile:
        await query.answer("أرسل /start أولاً.", show_alert=True)
        return
    await query.answer(
        f"رصيدك الحالي: {float(profile.get('coins', 0)):g} $",
        show_alert=True,
    )


# ---------------------------------------------------------------------------
# Admin menus and settings
# ---------------------------------------------------------------------------

@bot.on_callback_query(filters.regex(r"^back_admin$"))
async def admin_back_callback(client, query):
    if not await require_admin(query):
        return
    await query.edit_message_text(admin_panel_text(), reply_markup=make_admin_keyboard())


@bot.on_callback_query(filters.regex(r"^toggle_bot$"))
async def toggle_bot_callback(client, query):
    if not await require_admin(query):
        return
    enabled = not bool(db.get("bot_enabled"))
    db.set("bot_enabled", enabled)
    await query.answer("تم تشغيل البوت." if enabled else "تم إيقاف البوت.")
    await query.edit_message_text(admin_panel_text(), reply_markup=make_admin_keyboard())


@bot.on_callback_query(filters.regex(r"^toggle_join_notifications$"))
async def toggle_join_notifications_callback(client, query):
    if not await require_admin(query):
        return
    enabled = not bool(db.get("join_notifications"))
    db.set("join_notifications", enabled)
    await query.answer(
        "تم تفعيل إشعارات الدخول." if enabled else "تم إيقاف إشعارات الدخول."
    )
    await query.edit_message_text(admin_panel_text(), reply_markup=make_admin_keyboard())


@bot.on_callback_query(filters.regex(r"^startt$"))
async def legacy_admin_toggle_callback(client, query):
    # Older copies of the original menu used one callback for two unrelated buttons.
    if not await require_admin(query):
        return
    await query.answer("حدّثت القائمة؛ استخدم زري التشغيل والإشعارات المنفصلين.")
    await query.edit_message_text(admin_panel_text(), reply_markup=make_admin_keyboard())


@bot.on_callback_query(filters.regex(r"^admins_bot$"))
async def admins_menu_callback(client, query):
    if not await require_admin(query):
        return
    await query.edit_message_text(
        "إدارة المشرفين:",
        reply_markup=Keyboard(
            [
                [Button("إضافة مشرف", callback_data="add_admin")],
                [Button("حذف مشرف", callback_data="delete_admin")],
                [Button("رجوع", callback_data="back_admin")],
            ]
        ),
    )


@bot.on_callback_query(filters.regex(r"^add_admin$"))
async def add_admin_callback(client, query):
    if not await require_admin(query):
        return
    ask = await ask_admin_text(client, query, "أرسل معرّف المستخدم لإضافته كمشرف.")
    try:
        target_id = int(ask.text)
    except (TypeError, ValueError):
        await ask.reply("أرسل معرّفاً رقمياً صالحاً.")
        return
    admins = list(get_admin_ids())
    if target_id in admins:
        await ask.reply("هذا المستخدم مشرف بالفعل.")
        return
    admins.append(target_id)
    db.set("admin_list", admins)
    await ask.reply(f"تمت إضافة المستخدم {target_id} كمشرف.")


@bot.on_callback_query(filters.regex(r"^delete_admin$"))
async def delete_admin_callback(client, query):
    if not await require_admin(query):
        return
    ask = await ask_admin_text(client, query, "أرسل معرّف المشرف المراد حذفه.")
    try:
        target_id = int(ask.text)
    except (TypeError, ValueError):
        await ask.reply("أرسل معرّفاً رقمياً صالحاً.")
        return
    if target_id in BOOTSTRAP_ADMIN_IDS:
        await ask.reply("لا يمكن حذف مشرف أساسي مضبوط عبر ADMIN_IDS.")
        return
    admins = [admin_id for admin_id in get_admin_ids() if admin_id != target_id]
    if len(admins) == len(get_admin_ids()):
        await ask.reply("هذا المستخدم غير موجود في قائمة المشرفين.")
        return
    if not admins:
        await ask.reply("يجب أن يبقى مشرف واحد على الأقل.")
        return
    db.set("admin_list", admins)
    await ask.reply(f"تم حذف المستخدم {target_id} من المشرفين.")


@bot.on_callback_query(filters.regex(r"^stats$"))
async def stats_callback(client, query):
    if not await require_admin(query):
        return
    total_users = get_user_count()
    total_coins = 0.0
    for user_id in user_ids():
        profile = get_user(user_id) or {}
        try:
            total_coins += float(profile.get("coins", 0))
        except (TypeError, ValueError):
            continue
    await query.answer()
    await client.send_message(
        query.from_user.id,
        f"إحصائيات البوت:\nعدد المستخدمين: {total_users}\n"
        f"إجمالي الأرصدة: {total_coins:g}",
    )


@bot.on_callback_query(filters.regex(r"^setting_bot$"))
async def settings_menu_callback(client, query):
    if not await require_admin(query):
        return
    await query.edit_message_text(
        "إعدادات البوت:",
        reply_markup=Keyboard(
            [
                [Button("إضافة نقاط", callback_data="add_coins"), Button("خصم نقاط", callback_data="less_coin")],
                [Button("معلومات مستخدم", callback_data="get_infos")],
                [Button("تعيين API key", callback_data="set_api"), Button("تعيين النطاق", callback_data="set_domain")],
                [Button("تعيين معرّف الخدمة", callback_data="id_service")],
                [Button("سعر العضو", callback_data="member_price")],
                [Button("الحد الأدنى للتحويل", callback_data="transfer")],
                [Button("مكافأة الدعوة", callback_data="invite_coin")],
                [Button("رسالة الاشتراك الإجباري", callback_data="force_msg")],
                [Button("رجوع", callback_data="back_admin")],
            ]
        ),
    )


async def set_text_setting(client, query, key, prompt, success):
    if not await require_admin(query):
        return
    ask = await ask_admin_text(client, query, prompt)
    if not ask or not ask.text:
        await ask.reply("لم يتم استلام قيمة.")
        return
    db.set(key, ask.text.strip())
    await ask.reply(success)


async def set_number_setting(client, query, key, prompt, converter, success):
    if not await require_admin(query):
        return
    ask = await ask_admin_text(client, query, prompt)
    try:
        value = converter(ask.text)
        if value <= 0:
            raise ValueError
    except (TypeError, ValueError):
        await ask.reply("أرسل رقماً موجباً صالحاً.")
        return
    db.set(key, value)
    await ask.reply(success)


@bot.on_callback_query(filters.regex(r"^set_start$"))
async def set_start_message_callback(client, query):
    await set_text_setting(client, query, "start_msg", "أرسل رسالة الترحيب الجديدة.", "تم تحديث رسالة الترحيب.")


@bot.on_callback_query(filters.regex(r"^set_api$"))
async def set_api_key_callback(client, query):
    await set_text_setting(client, query, "api_key", "أرسل API key الجديد.", "تم تحديث API key.")


@bot.on_callback_query(filters.regex(r"^set_domain$"))
async def set_domain_callback(client, query):
    await set_text_setting(client, query, "set_domain", "أرسل نطاق HTTPS الخاص بمزود الخدمة.", "تم تحديث النطاق.")


@bot.on_callback_query(filters.regex(r"^id_service$"))
async def set_service_id_callback(client, query):
    await set_number_setting(client, query, "id_service", "أرسل معرّف الخدمة.", int, "تم تحديث معرّف الخدمة.")


@bot.on_callback_query(filters.regex(r"^invite_coin$"))
async def set_invite_reward_callback(client, query):
    await set_number_setting(client, query, "invite_price", "أرسل مكافأة الدعوة الجديدة.", float, "تم تحديث مكافأة الدعوة.")


@bot.on_callback_query(filters.regex(r"^transfer$"))
async def set_transfer_minimum_callback(client, query):
    await set_number_setting(client, query, "transfer", "أرسل الحد الأدنى للتحويل.", float, "تم تحديث الحد الأدنى للتحويل.")


@bot.on_callback_query(filters.regex(r"^member_price$"))
async def set_member_price_callback(client, query):
    await set_number_setting(client, query, "member_price", "أرسل سعر العضو الواحد.", float, "تم تحديث السعر.")


@bot.on_callback_query(filters.regex(r"^force_msg$"))
async def set_force_message_callback(client, query):
    await set_text_setting(client, query, "force_msg", "أرسل رسالة الاشتراك الإجباري.", "تم تحديث الرسالة.")


@bot.on_callback_query(filters.regex(r"^setforce$"))
async def set_force_channels_callback(client, query):
    if not await require_admin(query):
        return
    ask = await ask_admin_text(
        client,
        query,
        "أرسل معرفات القنوات مفصولة بمسافة، أو أرسل - لإيقاف الاشتراك الإجباري.",
    )
    channels = [] if ask.text.strip() == "-" else [
        channel.strip().lstrip("@") for channel in ask.text.split() if channel.strip()
    ]
    db.set("force", channels)
    await ask.reply("تم تحديث قنوات الاشتراك الإجباري.")


# ---------------------------------------------------------------------------
# Admin account operations and broadcast
# ---------------------------------------------------------------------------

@bot.on_callback_query(filters.regex(r"^add_coins$"))
async def add_coins_callback(client, query):
    if not await require_admin(query):
        return
    ask_user = await ask_admin_text(client, query, "أرسل معرّف المستخدم.")
    try:
        target_id = int(ask_user.text)
    except (TypeError, ValueError):
        await ask_user.reply("أرسل معرّفاً رقمياً صالحاً.")
        return
    ask_amount = await client.ask(query.from_user.id, "أرسل عدد النقاط المراد إضافته.")
    try:
        amount = float(ask_amount.text)
        if amount <= 0:
            raise ValueError
    except (TypeError, ValueError):
        await ask_amount.reply("أرسل مبلغاً موجباً صالحاً.")
        return
    async with balance_lock:
        profile = get_user(target_id)
        if not profile:
            await ask_amount.reply("هذا المستخدم لا يملك حساباً في البوت.")
            return
        profile["coins"] = float(profile.get("coins", 0)) + amount
        db.set(f"user_{target_id}", profile)
    await ask_amount.reply(f"تمت إضافة {amount:g} نقطة إلى {target_id}.")
    try:
        await client.send_message(target_id, f"أضيف إلى رصيدك {amount:g} نقطة من الإدارة.")
    except Exception:
        pass


@bot.on_callback_query(filters.regex(r"^less_coin$"))
async def subtract_coins_callback(client, query):
    if not await require_admin(query):
        return
    ask_user = await ask_admin_text(client, query, "أرسل معرّف المستخدم.")
    try:
        target_id = int(ask_user.text)
    except (TypeError, ValueError):
        await ask_user.reply("أرسل معرّفاً رقمياً صالحاً.")
        return
    ask_amount = await client.ask(query.from_user.id, "أرسل عدد النقاط المراد خصمه.")
    try:
        amount = float(ask_amount.text)
        if amount <= 0:
            raise ValueError
    except (TypeError, ValueError):
        await ask_amount.reply("أرسل مبلغاً موجباً صالحاً.")
        return
    async with balance_lock:
        profile = get_user(target_id)
        if not profile:
            await ask_amount.reply("هذا المستخدم لا يملك حساباً في البوت.")
            return
        if amount > float(profile.get("coins", 0)):
            await ask_amount.reply("الرصيد الحالي أقل من المبلغ المطلوب خصمه.")
            return
        profile["coins"] = float(profile.get("coins", 0)) - amount
        db.set(f"user_{target_id}", profile)
    await ask_amount.reply(f"تم خصم {amount:g} نقطة من {target_id}.")
    try:
        await client.send_message(target_id, f"تم خصم {amount:g} نقطة من رصيدك بواسطة الإدارة.")
    except Exception:
        pass


@bot.on_callback_query(filters.regex(r"^get_infos$"))
async def user_info_callback(client, query):
    if not await require_admin(query):
        return
    ask = await ask_admin_text(client, query, "أرسل معرّف المستخدم.")
    try:
        target_id = int(ask.text)
    except (TypeError, ValueError):
        await ask.reply("أرسل معرّفاً رقمياً صالحاً.")
        return
    profile = get_user(target_id)
    if not profile:
        await ask.reply("هذا الحساب غير موجود في البوت.")
        return
    try:
        joined = datetime.datetime.fromtimestamp(float(profile.get("date", 0)))
        joined_text = joined.strftime("%Y-%m-%d %H:%M:%S")
    except (TypeError, ValueError, OSError):
        joined_text = "غير متاح"
    await ask.reply(
        f"معلومات الحساب:\nالرصيد: {float(profile.get('coins', 0)):g}\n"
        f"تاريخ الانضمام: {joined_text}"
    )


@bot.on_callback_query(filters.regex(r"^brods$"))
async def broadcast_callback(client, query):
    if not await require_admin(query):
        return
    prompt = await ask_admin_text(client, query, "أرسل الرسالة أو الوسائط المراد إذاعتها.")
    status = await client.send_message(
        query.from_user.id, f"بدأ الإرسال إلى {get_user_count()} مستخدم..."
    )
    sent = 0
    for target_id in user_ids():
        try:
            await client.copy_message(
                chat_id=target_id,
                from_chat_id=query.from_user.id,
                message_id=prompt.id,
            )
            sent += 1
            if sent % 25 == 0:
                await status.edit_text(
                    f"جاري الإرسال: وصل إلى {sent} من {get_user_count()} مستخدم."
                )
        except Exception:
            continue
    await status.edit_text(
        f"انتهت الإذاعة. تم الإرسال إلى {sent} من {get_user_count()} مستخدم."
    )


@bot.on_callback_query(filters.regex(r"^hkajs$"))
async def broadcast_done_callback(client, query):
    if not await require_admin(query):
        return
    await query.answer("انتهت العملية.")


@bot.on_callback_query(filters.regex(r"^ban_mes$"))
async def ban_user_callback(client, query):
    if not await require_admin(query):
        return
    ask = await ask_admin_text(client, query, "أرسل معرّف المستخدم لحظره.")
    try:
        target_id = int(ask.text)
    except (TypeError, ValueError):
        await ask.reply("أرسل معرّفاً رقمياً صالحاً.")
        return
    if not get_user(target_id):
        await ask.reply("هذا المستخدم غير موجود في البوت.")
        return
    bans = set(db.get("ban_list") or [])
    bans.add(target_id)
    db.set("ban_list", sorted(bans))
    await ask.reply("تم حظر المستخدم.")


@bot.on_callback_query(filters.regex(r"^unban_mes$"))
async def unban_user_callback(client, query):
    if not await require_admin(query):
        return
    ask = await ask_admin_text(client, query, "أرسل معرّف المستخدم لإلغاء حظره.")
    try:
        target_id = int(ask.text)
    except (TypeError, ValueError):
        await ask.reply("أرسل معرّفاً رقمياً صالحاً.")
        return
    bans = set(db.get("ban_list") or [])
    if target_id not in bans:
        await ask.reply("هذا المستخدم غير موجود في قائمة الحظر.")
        return
    bans.remove(target_id)
    db.set("ban_list", sorted(bans))
    await ask.reply("تم إلغاء حظر المستخدم.")


# ---------------------------------------------------------------------------
# User profile, referrals, transfers, and service requests
# ---------------------------------------------------------------------------

@bot.on_callback_query(filters.regex(r"^account$"))
async def account_callback(client, query):
    if not await require_user_access(query):
        return
    if not await require_membership(client, query):
        return
    profile = get_user(query.from_user.id)
    if not profile:
        await query.answer("أرسل /start أولاً.", show_alert=True)
        return
    user_id = query.from_user.id
    buys = int(db.get(f"user_{user_id}_buys") or 0)
    transfers = int(db.get(f"user_{user_id}_trans") or 0)
    text = (
        f"معلومات حسابك:\nالرصيد: {float(profile.get('coins', 0)):g} $\n"
        f"دعواتك: {len(profile.get('users', []))}\n"
        f"طلباتك: {buys}\nتحويلاتك: {transfers}\n\n{leaderboard()}"
    )
    await query.edit_message_text(
        text,
        reply_markup=Keyboard([[Button("رجوع", callback_data="back")]]),
    )


@bot.on_callback_query(filters.regex(r"^sharelink$"))
async def share_link_callback(client, query):
    if not await require_user_access(query):
        return
    if not await require_membership(client, query):
        return
    profile = get_user(query.from_user.id)
    if not profile:
        await query.answer("أرسل /start أولاً.", show_alert=True)
        return
    me = await client.get_me()
    reward = float(db.get("invite_price") or 0.1)
    link = f"https://t.me/{me.username}?start={query.from_user.id}"
    text = (
        f"شارك رابط الدعوة لتحصل على {reward:g} $ لكل مستخدم جديد.\n\n"
        f"رابطك:\n{link}\n"
        f"عدد الدعوات: {len(profile.get('users', []))}\n\n{leaderboard()}"
    )
    await query.edit_message_text(
        text, reply_markup=Keyboard([[Button("رجوع", callback_data="back")]])
    )


@bot.on_callback_query(filters.regex(r"^tran$"))
async def transfer_callback(client, query):
    if not await require_user_access(query):
        return
    sender_id = query.from_user.id
    sender = get_user(sender_id)
    if not sender:
        await query.answer("أرسل /start أولاً.", show_alert=True)
        return
    minimum = float(db.get("transfer") or 100)
    ask_target = await client.ask(
        sender_id, "أرسل معرّف المستخدم المستلم.", filters=filters.user(sender_id)
    )
    try:
        target_id = int(ask_target.text)
    except (TypeError, ValueError):
        await ask_target.reply("أرسل معرّفاً رقمياً صالحاً.")
        return
    if target_id == sender_id or not get_user(target_id):
        await ask_target.reply("المستلم غير موجود أو لا يمكن التحويل إلى حسابك.")
        return
    ask_amount = await client.ask(
        sender_id, "أرسل مبلغ التحويل.", filters=filters.user(sender_id)
    )
    try:
        amount = float(ask_amount.text)
        if amount <= 0:
            raise ValueError
    except (TypeError, ValueError):
        await ask_amount.reply("أرسل مبلغاً موجباً صالحاً.")
        return
    if amount < minimum:
        await ask_amount.reply(f"الحد الأدنى للتحويل هو {minimum:g}.")
        return

    async with balance_lock:
        sender = get_user(sender_id)
        recipient = get_user(target_id)
        if not sender or not recipient:
            await ask_amount.reply("تعذر العثور على أحد الحسابين.")
            return
        if amount > float(sender.get("coins", 0)):
            await ask_amount.reply("رصيدك غير كافٍ.")
            return
        sender["coins"] = float(sender.get("coins", 0)) - amount
        recipient["coins"] = float(recipient.get("coins", 0)) + amount
        db.set(f"user_{sender_id}", sender)
        db.set(f"user_{target_id}", recipient)
        trans_key = f"user_{sender_id}_trans"
        db.set(trans_key, int(db.get(trans_key) or 0) + 1)

    await ask_amount.reply(f"تم تحويل {amount:g} نقطة إلى {target_id}.")
    try:
        await client.send_message(
            target_id,
            f"وصل إلى حسابك {amount:g} نقطة من {query.from_user.mention}.",
        )
    except Exception:
        pass
    for admin_id in get_admin_ids():
        try:
            await client.send_message(
                admin_id,
                f"تم تحويل {amount:g} نقطة من {sender_id} إلى {target_id}.",
            )
        except Exception:
            pass


def check_request_cooldown(user_id):
    key = f"user_{int(user_id)}_request"
    current_time = time.time()
    state = db.get(key)
    wait_seconds = 40
    if state:
        elapsed = current_time - float(state.get("time", 0))
        if elapsed < wait_seconds:
            return int(wait_seconds - elapsed)
    db.set(key, {"time": current_time})
    return None


@bot.on_callback_query(filters.regex(r"^member$"))
async def member_request_callback(client, query):
    user_id = query.from_user.id
    if not await require_user_access(query):
        return
    if not await require_membership(client, query):
        return
    cooldown = check_request_cooldown(user_id)
    if cooldown is not None:
        await query.answer(f"انتظر {cooldown} ثانية قبل طلب آخر.", show_alert=True)
        return

    profile = get_user(user_id)
    if not profile:
        await query.answer("أرسل /start أولاً.", show_alert=True)
        return
    try:
        await client.delete_messages(query.message.chat.id, query.message.id)
    except Exception:
        pass

    count_answer = await client.ask(
        user_id,
        "أرسل العدد المطلوب (من 500 إلى 30000).",
        filters=filters.user(user_id),
    )
    try:
        count = int(count_answer.text)
    except (TypeError, ValueError):
        await count_answer.reply("أرسل عدداً صحيحاً.")
        return
    if not 500 <= count <= 30000:
        await count_answer.reply("يجب أن يكون العدد بين 500 و30000.")
        return

    link_answer = await client.ask(
        user_id,
        "أرسل رابط قناة أو مجموعة عامة يبدأ بـ t.me/.",
        filters=filters.user(user_id),
    )
    link = (link_answer.text or "").strip()
    if "t.me/" not in link:
        await link_answer.reply("أرسل رابطاً عاماً صالحاً يبدأ بـ t.me/.")
        return
    try:
        parts = link.split("t.me/", 1)[1].split("/")
        target_chat = parts[0].split("?", 1)[0].lstrip("@")
        if not target_chat or target_chat.startswith("+"):
            raise ValueError
        chat_info = await client.get_chat(f"@{target_chat}")
        starting_members = int(chat_info.members_count or 0)
    except Exception:
        await link_answer.reply("تعذر الوصول إلى القناة. تحقق من الرابط وإمكانية الوصول.")
        return

    price_per_member = float(db.get("member_price") or 0.2)
    total_price = price_per_member * count
    profile = get_user(user_id) or {}
    if total_price > float(profile.get("coins", 0)):
        await link_answer.reply(f"رصيدك غير كافٍ. التكلفة هي {total_price:g} $.")
        return

    confirm = await client.ask(
        user_id,
        f"مراجعة الطلب:\nالرابط: {link}\nالعدد: {count}\n"
        f"التكلفة: {total_price:g} $\n"
        "أرسل /ok للتأكيد أو /cancel للإلغاء.",
        filters=filters.user(user_id),
    )
    if (confirm.text or "").strip().lower() == "/cancel":
        await confirm.reply("تم إلغاء الطلب.")
        return
    if (confirm.text or "").strip().lower() != "/ok":
        await confirm.reply("لم يتم تأكيد الطلب.")
        return

    api_key = str(db.get("api_key") or "").strip()
    service_id = db.get("id_service")
    if not api_key or service_id is None:
        await confirm.reply("لم يتم إعداد بيانات مزود الخدمة.")
        return

    async with balance_lock:
        profile = get_user(user_id) or {}
        if total_price > float(profile.get("coins", 0)):
            await confirm.reply("لم يعد رصيدك كافياً لإتمام الطلب.")
            return
        profile["coins"] = float(profile.get("coins", 0)) - total_price
        db.set(f"user_{user_id}", profile)

    try:
        result = await call_service_api(
            {
                "key": api_key,
                "action": "add",
                "service": service_id,
                "quantity": count,
                "link": link,
            }
        )
        order_id = result.get("order")
        if not order_id:
            raise ValueError(str(result.get("error") or "رفض مزود الخدمة الطلب."))
    except Exception as exc:
        async with balance_lock:
            profile = get_user(user_id) or {}
            profile["coins"] = float(profile.get("coins", 0)) + total_price
            db.set(f"user_{user_id}", profile)
        # Do not expose exception text: HTTP errors can contain the API key in a URL.
        await confirm.reply(
            "تعذر تسجيل الطلب؛ تمت إعادة الرصيد. "
            "تحقق من إعدادات مزود الخدمة وحاول لاحقاً."
        )
        return

    buys_key = f"user_{user_id}_buys"
    db.set(buys_key, int(db.get(buys_key) or 0) + 1)
    await confirm.reply(
        f"تم تسجيل الطلب.\nالرابط: {link}\nالعدد: {count}\n"
        f"الأعضاء قبل الطلب: {starting_members}\nمعرّف الطلب: {order_id}"
    )


@bot.on_callback_query(filters.regex(r"^id_requests$"))
async def order_status_callback(client, query):
    if not await require_user_access(query):
        return
    if not await require_membership(client, query):
        return
    if not get_user(query.from_user.id):
        await query.answer("أرسل /start أولاً.", show_alert=True)
        return
    ask = await client.ask(
        query.from_user.id,
        "أرسل معرّف الطلب.",
        filters=filters.user(query.from_user.id),
    )
    try:
        order_id = int(ask.text)
    except (TypeError, ValueError):
        await ask.reply("أرسل معرّف طلب رقمي صالحاً.")
        return
    api_key = str(db.get("api_key") or "").strip()
    if not api_key:
        await ask.reply("لم يتم إعداد API key.")
        return
    try:
        result = await call_service_api(
            {"key": api_key, "action": "status", "order": order_id}
        )
        await ask.reply(
            "حالة الطلب:\n"
            f"الحالة: {result.get('status', 'غير متاحة')}\n"
            f"العدد عند البداية: {result.get('start_count', 'غير متاح')}\n"
            f"المتبقي: {result.get('remains', 'غير متاح')}"
        )
    except Exception:
        await ask.reply("تعذر جلب حالة الطلب. تحقق من المعرّف وإعدادات مزود الخدمة.")


if __name__ == "__main__":
    bot.run()
