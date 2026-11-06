import telebot
from telebot import types

# توكن البوت الخاص بك
TOKEN = "8782796572:AAGd1ceUuoA60lfArszLy1__CI_93urBaP8"
ADMIN_ID = 7379818403  # أيدي المالك الخاص بك

bot = telebot.TeleBot(TOKEN)

# قائمة مؤقتة لتخزين النقاط (يمكن ربطها بقاعدة بيانات لاحقاً)
user_points = {}

# أمر البداية (Start) مع رابط الدعوة والاشتراك
@bot.message_handler(commands=['start'])
def start_command(message):
    user_id = message.from_user.id
    user_name = message.from_user.first_name
    
    # تسجيل المستخدم إذا كان جديداً
    if user_id not in user_points:
        user_points[user_id] = 0

    # لوحة المفاتيح الرئيسية للبوت
    markup = types.ReplyKeyboardMarkup(resize_keyboard=True)
    markup.row("💰 تجميع النقاط", "👤 حسابي")
    markup.row("🔗 رابط الدعوة", "🎁 سحب النقاط")
    
    if user_id == ADMIN_ID:
        markup.row("🛠 لوحة الأدمن")

    welcome_text = (
        f"أهلاً بك يا {user_name} في بوت التمويل الرسمي! 🚀\n\n"
        "من خلال هذا البوت يمكنك جمع النقاط عبر دعوة أصدقائك وتمويل قناتك.\n"
        "اختر أحد الأوامر من القائمة أدناه للبدء:"
    )
    
    bot.send_message(message.chat.id, welcome_text, reply_markup=markup)

# زر حسابي
@bot.message_handler(func=lambda msg: msg.text == "👤 حسابي")
def my_account(message):
    user_id = message.from_user.id
    points = user_points.get(user_id, 0)
    
    text = (
        f"📊 **معلومات حسابك:**\n\n"
        f"🆔 الاي دي: `{user_id}`\n"
        f"💎 رصيدك من النقاط: **{points} نقطة**"
    )
    bot.send_message(message.chat.id, text, parse_mode="Markdown")

# زر رابط الدعوة (التمويل)
@bot.message_handler(func=lambda msg: msg.text == "🔗 رابط الدعوة")
def referral_link(message):
    user_id = message.from_user.id
    bot_info = bot.get_me()
    link = f"https://t.me/{bot_info.username}?start={user_id}"
    
    text = (
        f"🔗 **رابط الدعوة الخاص بك:**\n\n"
        f"`{link}`\n\n"
        "شارك الرابط مع أصدقائك، وكل شخص يدخل عبر رابطك ستحصل على نقاط إضافية في رصيدك!"
    )
    bot.send_message(message.chat.id, text, parse_mode="Markdown")

# لوحة الأدمن الخاصة بك
import logging
import re
import datetime
from decimal import Decimal, InvalidOperation
from html import escape

from pyrogram import Client as app, enums, filters
from pyrogram.enums import ChatMemberStatus, ChatType
from pyrogram.types import InlineKeyboardButton as btn, InlineKeyboardMarkup as mk
from kvsqlite.sync import Client as mody
from config import Config
from .navigation import ask_with_back, clear_section_message
from .bot_controls import admin_dashboard_keyboard
from .moderation import _user_admin_keyboard
from .order_lock import ORDER_LOCK
from .points_core import open_transaction, read_value, write_value

db = mody("data.sqlite", 'fuck')
ADMIN_BACK = mk([[btn("رجوع", callback_data="back_admin")]])
logger = logging.getLogger(__name__)
MAX_POINTS = Decimal("1000000000")


def _admin_ids():
    stored = db.get("admin_list")
    if not isinstance(stored, (list, tuple, set)):
        return []
    return [
        admin_id
        for admin_id in stored
        if isinstance(admin_id, int) and not isinstance(admin_id, bool)
    ]


def _is_admin(user_id):
    return user_id in _admin_ids()


def _parse_user_id(text):
    value = (text or "").strip()
    if not re.fullmatch(r"\d{1,20}", value) or int(value) < 1:
        raise ValueError("أرسل آيدي مستخدم رقمي صحيح.")
    return int(value)


def _parse_points(text):
    value = (text or "").strip()
    if not re.fullmatch(r"\d{1,10}(?:\.\d{1,4})?", value):
        raise ValueError("أرسل كمية موجبة حتى 4 منازل عشرية.")
    try:
        amount = Decimal(value)
    except InvalidOperation as error:
        raise ValueError("الكمية غير صحيحة.") from error
    if not amount.is_finite() or amount <= 0 or amount > MAX_POINTS:
        raise ValueError("الكمية خارج الحدود المسموحة.")
    return amount


async def _adjust_user_points(user_id, amount, increase):
    async with ORDER_LOCK:
        connection = open_transaction()
        try:
            profile = read_value(connection, f"user_{user_id}")
            if not isinstance(profile, dict):
                connection.rollback()
                return False, "هذا الحساب غير موجود في البوت."
            try:
                current = Decimal(str(profile.get("coins")))
            except (InvalidOperation, TypeError, ValueError):
                connection.rollback()
                return False, "تعذر قراءة رصيد هذا الحساب."
            if not current.is_finite() or current < 0 or current > MAX_POINTS:
                connection.rollback()
                return False, "رصيد الحساب خارج الحدود المسموحة."

            updated = current + amount if increase else current - amount
            if updated < 0:
                connection.rollback()
                return False, "الرصيد الحالي أقل من المبلغ المطلوب خصمه."
            if updated > MAX_POINTS:
                connection.rollback()
                return False, "الرصيد الناتج يتجاوز الحد المسموح."

            profile["coins"] = float(updated)
            write_value(connection, f"user_{user_id}", profile)
            connection.commit()
            return True, updated
        except Exception:
            if connection.in_transaction:
                connection.rollback()
            raise
        finally:
            connection.close()


# بدء لوحة الأدمن عند إرسال /start
@app.on_message(filters.private & filters.regex("^/start$"), group=1)
async def admin_start_handler(app, msg):
    user_id = msg.from_user.id
    if _is_admin(user_id):
        keys = admin_dashboard_keyboard()
        await msg.reply(
            "**• اهلا بك في لوحه الأدمن الخاصه بالبوت 🤖**\n\n- يمكنك التحكم في البوت الخاص بك من هنا \n\n===================",
            reply_markup=keys
        )


# العودة للوحة الأدمن الرئيسية
@app.on_callback_query(filters.regex("^back_admin$"))
async def back_to_admin_panel(app, query):
    user_id = query.from_user.id
    if not _is_admin(user_id):
        await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
        return
    keys = admin_dashboard_keyboard()
    rk = "**• اهلا بك في لوحه الأدمن الخاصه بالبوت 🤖**\n\n- يمكنك التحكم في البوت الخاص بك من هنا \n\n==================="
    await query.edit_message_text(rk, reply_markup=keys)


# إدارة الأدمنية
@app.on_callback_query(filters.regex("^admins_bot$"))
async def admins_panel(app, query):
    if not _is_admin(query.from_user.id):
        await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
        return

    admin_ids = _admin_ids()
    text = "إدارة الأدمنية\n\n"
    text += "\n".join(f"• <code>{admin_id}</code>" for admin_id in admin_ids)
    rows = []
    if query.from_user.id == Config.OWNER_ID:
        rows.append(
            [
                btn("➕ إضافة أدمن", "add_admin"),
                btn("➖ حذف أدمن", "delete_admin"),
            ]
        )
    rows.append([btn("↩️ رجوع للوحة الأدمن", "back_admin")])
    await query.edit_message_text(
        text,
        reply_markup=mk(rows),
        parse_mode=enums.ParseMode.HTML,
    )


@app.on_callback_query(filters.regex("^add_admin$"), group=6)
async def add_admin(app, query):
    user_id = query.from_user.id
    if user_id != Config.OWNER_ID:
        await query.answer("إدارة صلاحيات الأدمن مخصصة لمالك البوت فقط.", show_alert=True)
        return
    await clear_section_message(query)
    askk = await ask_with_back(app, user_id, 'يرجى إرسال معرف المستخدم لترقيته كمسؤول في البوت', "back_admin")
    if not askk or not askk.text:
        return
    try:
        t_id = _parse_user_id(askk.text)
    except ValueError:
        await askk.reply("يرجى إرسال معرف المستخدم بتنسيق صحيح", reply_markup=ADMIN_BACK)
        return
    s = _admin_ids()
    if t_id in s:
        await askk.reply(f"المستخدم {t_id} مسؤول بالفعل", reply_markup=ADMIN_BACK)
        return
    s.append(t_id)
    db.set("admin_list", s)
    await askk.reply(f"تمت إضافة المستخدم {t_id} كمسؤول في البوت", reply_markup=ADMIN_BACK)


@app.on_callback_query(filters.regex("^delete_admin$"), group=7)
async def ada_admin(app, query):
    user_id = query.from_user.id
    if user_id != Config.OWNER_ID:
        await query.answer("إدارة صلاحيات الأدمن مخصصة لمالك البوت فقط.", show_alert=True)
        return
    await clear_section_message(query)
    askk = await ask_with_back(app, user_id, 'ارسل الان ايدي الشخص لازالته من الادمنية', "back_admin")
    if not askk or not askk.text:
        return
    try:
        t_id = _parse_user_id(askk.text)
    except ValueError:
        await askk.reply("برجاء ارسل الايدي بشكل صحيح", reply_markup=ADMIN_BACK)
        return
    if t_id == Config.OWNER_ID:
        await askk.reply("لا يمكن إزالة مالك البوت من قائمة الأدمنية.", reply_markup=ADMIN_BACK)
        return
    s = _admin_ids()
    if t_id not in s:
        await askk.reply("هذا المستخدم ليس ضمن الأدمنية.", reply_markup=ADMIN_BACK)
        return
    s.remove(t_id)
    db.set("admin_list", s)
    await askk.reply(f"تم مسح : {t_id} من ادمنية البوت", reply_markup=ADMIN_BACK)


# إضافة نقاط
@app.on_callback_query(filters.regex("^add_coins$"), group=8)
async def add_coinssw(app, query):
    user_id = query.from_user.id
    if not _is_admin(user_id):
        await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
        return
    await clear_section_message(query)
    askk = await ask_with_back(app, user_id, 'ارسل اي دي العضو اللي تريد ترسله النقاط.', "back_admin")
    if not askk or not askk.text:
        return
    try:
        t_id = _parse_user_id(askk.text)
    except ValueError:
        await askk.reply("ارسل الايدي بشكل صحيح", reply_markup=ADMIN_BACK)
        return
    
    ask2 = await ask_with_back(app, user_id, 'ارسل عدد النقاط اللي تريد ارسالها للشخص', "back_admin")
    if not ask2 or not ask2.text:
        return
    try:
        amount = _parse_points(ask2.text)
    except ValueError as error:
        await ask2.reply(str(error), reply_markup=ADMIN_BACK)
        return
    
    try:
        success, result = await _adjust_user_points(t_id, amount, True)
    except Exception as error:
        logger.error("Admin balance update failed (%s)", type(error).__name__)
        await ask2.reply("تعذر تحديث الرصيد حالياً. لم يتم تأكيد العملية.", reply_markup=ADMIN_BACK)
        return
    if not success:
        await ask2.reply(result, reply_markup=ADMIN_BACK)
        return
    
    amount_text = format(amount.normalize(), "f")
    await ask2.reply(
        f"• تم اضافة نقاط الي : `{t_id}`\n\n• العدد : `{amount_text}` ",
        reply_markup=ADMIN_BACK,
    )
    try:
        await app.send_message(int(t_id), f"• تم اضافة `{amount_text}` نقاط الى حسابك من قبل المطور")
    except Exception:
        pass


# خصم نقاط
@app.on_callback_query(filters.regex("^less_coin$"), group=9)
async def les_co(app, query):
    user_id = query.from_user.id
    if not _is_admin(user_id):
        await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
        return
    await clear_section_message(query)
    askk = await ask_with_back(app, user_id, 'ارسل اي دي العضو اللي تريد تخصم منه النقاط', "back_admin")
    if not askk or not askk.text:
        return
    try:
        t_id = _parse_user_id(askk.text)
    except ValueError:
        await askk.reply("رجاء ارسل الاي دي بشكل صحيح", reply_markup=ADMIN_BACK)
        return
    
    ask2 = await ask_with_back(app, user_id, 'ارسل عدد النقاط اللي تريد خصمة من هذا الشخص', "back_admin")
    if not ask2 or not ask2.text:
        return
    try:
        amount = _parse_points(ask2.text)
    except ValueError as error:
        await ask2.reply(str(error), reply_markup=ADMIN_BACK)
        return
    
    try:
        success, result = await _adjust_user_points(t_id, amount, False)
    except Exception as error:
        logger.error("Admin balance update failed (%s)", type(error).__name__)
        await ask2.reply("تعذر تحديث الرصيد حالياً. لم يتم تأكيد العملية.", reply_markup=ADMIN_BACK)
        return
    if not success:
        await ask2.reply(result, reply_markup=ADMIN_BACK)
        return
    
    amount_text = format(amount.normalize(), "f")
    await ask2.reply(
        f"• تم خصم نقاط من : `{t_id}`\n\n• العدد : `{amount_text}` ",
        reply_markup=ADMIN_BACK,
    )
    try:
        await app.send_message(int(t_id), f"• تم خصم `{amount_text}` نقاط من حسابك من قبل المطور")
    except Exception:
        pass


# الإذاعة
@app.on_callback_query(filters.regex("^brods$"), group=10)
async def brod_ss(app, query):
    user_id = query.from_user.id
    if not _is_admin(user_id):
        await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
        return
    user_ids = sorted(
        {
            int(match.group(1))
            for key in db.keys()
            if (match := re.fullmatch(r"user_(\d+)", str(key[0])))
        }
    )
    count = len(user_ids)
    await clear_section_message(query)
    ask1 = await ask_with_back(app, user_id, '• ارسل محتوى الاذاعة : \n\n•يمكنك ارسال : نص او ميديا او الخ', "back_admin")
    if not ask1:
        return
    
    c = 0
    msg_id = ask1.id
    for target_id in user_ids:
        try:
            await app.copy_message(target_id, user_id, msg_id)
            c += 1
            await app.edit_message_text(user_id, ask1.request.id, f'• جاري الاذاعة الى `{count}` مستخدم 🌐\n\n• تم الارسال الى `{c}` مستخدم')
        except Exception:
            continue
            
    all_failed = int(count) - int(c)
    await ask1.reply(f"• تم انتهاء الاذاعة بنجاح ✅:\n\n• عدد الاشخاص الذين شاهدو الاذاعة : {c}\n\n• المستخدمين الذين لم يستطع البوت ارسال اذاعه لهم {all_failed} مستخدم", reply_markup=mk([[btn(text='رجوع', callback_data='back_admin')]]))
    await app.edit_message_text(user_id, ask1.request.id, f'• تم الارسال الى `{c}` مستخدم', reply_markup=mk([[btn(text='رجوع', callback_data='back_admin')]]))


def ttd(timestamp) -> str:
    date = datetime.datetime.fromtimestamp(timestamp)
    return date.strftime('%Y-%m-%d %H:%M:%S')


# معلومات العضو
@app.on_callback_query(filters.regex("^get_infos$"), group=11)
async def get_infso(app, query):
    user_id = query.from_user.id
    if not _is_admin(user_id):
        await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
        return
    await clear_section_message(query)
    ask = await ask_with_back(app, user_id, 'ارسل الان ايدي الشخص اللي تريد تعرف معلوماته', "back_admin")
    if not ask or not ask.text:
        return
    try:
        target_id = int(ask.text)
    except ValueError:
        return
    d = db.get(f"user_{target_id}")
    if d is None:
        await ask.reply("هذا الحساب غير موجود في البوت", reply_markup=ADMIN_BACK)
        return
    try:
        coins = d.get('coins', 0)
        ddd = str(d.get('date', time.time())).split(".")[0]
        date = ttd(int(ddd))
    except Exception:
        return
    await ask.reply(
        f'• معلومات حسابه :\n\n• عدد نقاطه : {coins}\n\n• تاريخ دخولة للبوت : {date} ',
        reply_markup=_user_admin_keyboard(target_id),
    )


# الاشتراك الإجباري (Force Subscription)
@app.on_callback_query(filters.regex('^setforce$'))
async def setforcee(app, query):
    if not _is_admin(query.from_user.id):
        await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
        return
    await _show_force_panel(query)


def _force_channels():
    channels = db.get("force") or []
    if not isinstance(channels, list):
        return []
    result = []
    for value in channels:
        name = str(value).strip().removeprefix("@").lower()
        if name and name not in result:
            result.append(name)
    return result


def _force_targets():
    targets = db.get("force_targets")
    return targets if isinstance(targets, dict) else {}


def _force_panel_content():
    channels = _force_channels()
    targets = _force_targets()
    lines = ["<b>قسم الاشتراك الإجباري</b>"]
    if not channels:
        lines.append("لا توجد قنوات اشتراك إجباري حالياً.")
    for channel in channels:
        entry = targets.get(channel, {})
        count = entry.get("count", 0) if isinstance(entry, dict) else 0
        target = entry.get("target") if isinstance(entry, dict) else None
        count = escape(str(count))
        required = escape(str(target)) if target is not None else "غير محدد"
        lines.extend(
            [
                "",
                f"يوزر القناة: @{escape(channel)}",
                f"عدد المشتركين: {count} : {required}",
            ]
        )
    return "\n".join(lines)


def _force_panel_keyboard():
    rows = [
        [
            btn(
                f"حذف @{channel}",
                callback_data=f"setforce_remove:{channel}",
            )
        ]
        for channel in _force_channels()
    ]
    rows.extend(
        [
            [btn("إضافة قناة جديدة", callback_data="setforce_add")],
            [btn("تحديث القائمة", callback_data="setforce")],
            [btn("رجوع", callback_data="back_admin")],
        ]
    )
    return mk(rows)


async def _show_force_panel(query):
    await query.edit_message_text(
        _force_panel_content(),
        reply_markup=_force_panel_keyboard(),
        parse_mode=enums.ParseMode.HTML,
    )


@app.on_callback_query(filters.regex(r"^setforce_remove:([A-Za-z0-9_]{5,32})$"))
async def remove_force_channel(client, query):
    if not _is_admin(query.from_user.id):
        await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
        return

    channel_name = query.data.rsplit(":", 1)[1].lower()
    channels = _force_channels()
    if channel_name not in channels:
        await query.answer("القناة غير موجودة في الاشتراك الإجباري.", show_alert=True)
        return

    db.set("force", [channel for channel in channels if channel != channel_name])
    targets = _force_targets()
    targets.pop(channel_name, None)
    db.set("force_targets", targets)
    await query.answer(f"تم حذف @{channel_name} من الاشتراك الإجباري.")
    await _show_force_panel(query)


@app.on_callback_query(filters.regex("^setforce_add$"))
async def add_force_channel(client, query):
    user_id = query.from_user.id
    if not _is_admin(user_id):
        await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
        return

    await clear_section_message(query)
    username_message = await ask_with_back(
        client,
        user_id,
        "أرسل يوزر القناة مثل @mychannel أو رابطها على t.me:",
        "back_admin",
        filters=filters.user(user_id),
    )
    if not username_message or not username_message.text:
        return

    raw_username = username_message.text.strip()
    raw_username = re.sub(
        r"^(?:https?://)?(?:www\.)?t\.me/",
        "",
        raw_username,
        flags=re.IGNORECASE,
    ).rstrip("/")
    match = re.fullmatch(r"@?([A-Za-z][A-Za-z0-9_]{4,31})", raw_username)
    if not match:
        await username_message.reply(
            "يوزر القناة غير صالح. أرسل يوزراً عاماً من 5 إلى 32 حرفاً."
        )
        return
    channel_name = match.group(1).lower()

    target_message = await ask_with_back(
        client,
        user_id,
        "أرسل الحد الأقصى لعدد المشتركين المطلوب (رقم أكبر من صفر):",
        "back_admin",
        filters=filters.user(user_id),
    )
    if not target_message or not target_message.text:
        return
    try:
        target = int(target_message.text.strip())
    except ValueError:
        await target_message.reply("أرسل الحد المطلوب كرقم صحيح.")
        return
    if target <= 0:
        await target_message.reply("الحد المطلوب يجب أن يكون أكبر من صفر.")
        return

    try:
        chat = await client.get_chat(f"@{channel_name}")
        if chat.type not in (ChatType.CHANNEL, ChatType.SUPERGROUP):
            await target_message.reply("اليوزر الذي أرسلته ليس قناة أو مجموعة عامة.")
            return
        bot_user = await client.get_me()
        bot_member = await client.get_chat_member(chat.id, bot_user.id)
        if bot_member.status not in (
            ChatMemberStatus.OWNER,
            ChatMemberStatus.ADMINISTRATOR,
        ):
            await target_message.reply(
                "أضف البوت مشرفاً في القناة أولاً حتى يتمكن من التحقق من الاشتراك."
            )
            return
    except Exception:
        await target_message.reply(
            "تعذّر الوصول إلى القناة. تحقق من اليوزر، ثم أضف البوت مشرفاً وحاول مجدداً."
        )
        return

    channels = _force_channels()
    targets = _force_targets()
    existing_target = targets.get(channel_name)
    if isinstance(existing_target, dict) and existing_target.get("target"):
        await target_message.reply("هذه القناة مضافة بالفعل ولها حد اشتراك.")
        return
    if channel_name not in channels:
        channels.append(channel_name)
    targets[channel_name] = {"target": target, "count": 0, "users": []}
    db.set("force", channels)
    db.set("force_targets", targets)

    await target_message.reply(
        f"تمت إضافة القناة @{channel_name}، والحد المطلوب {target} مشترك."
    )
    await client.send_message(
        user_id,
        _force_panel_content(),
        reply_markup=_force_panel_keyboard(),
        parse_mode=enums.ParseMode.HTML,
    )

# تشغيل البوت
print("بوت التمويل يعمل الآن...")
bot.infinity_polling()
