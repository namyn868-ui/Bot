import datetime
from decimal import Decimal, InvalidOperation
from html import escape
import logging
from pathlib import Path
import re
import sqlite3
import time
from zoneinfo import ZoneInfo

from config import Config
from kvsqlite import PickleEncoder
from kvsqlite.sync import Client as Database
from kvsqlite.sync import Client as mody
from pyrogram import Client as app, enums, filters
from pyrogram import Client as temp
from pyrogram.enums import ChatMemberStatus, ChatType
from pyrogram.types import InlineKeyboardButton as btn, InlineKeyboardMarkup as mk

from .bot_controls import admin_dashboard_keyboard
from .moderation import _user_admin_keyboard
from .navigation import ask_with_back, clear_section_message
from .order_lock import ORDER_LOCK
from .points_core import open_transaction, read_value, write_value

# تهيئة قاعدة البيانات والإعدادات
db = mody("data.sqlite", "fuck")
DATABASE_PATH = Path(__file__).resolve().parents[1] / "data.sqlite"
ENCODER = PickleEncoder()
ADMIN_BACK = mk([[btn("رجوع", callback_data="back_admin")]])
logger = logging.getLogger(__name__)
MAX_POINTS = Decimal("1000000000")
LOCAL_TIMEZONE = ZoneInfo("Asia/Baghdad")

# مفاتيح نظام الوكلاء
AGENT_KEY = "agent_registry"
DAILY_KEY = "agent_daily_stats"
LOG_CHAT_KEY = "agent_audit_chat_id"
LOG_CHANNEL_USERNAME_KEY = "agent_audit_channel_username"


# دوال مساعدة عامة والوكلاء والأدمن
def _get_agents():
  value = db.get(AGENT_KEY)
  return value if isinstance(value, dict) else {}


def is_active_agent(user_id):
  record = _get_agents().get(str(user_id))
  return isinstance(record, dict) and record.get("status") == "active"


def _format_amount(value):
  return format(Decimal(str(value)).normalize(), "f")


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


def _parse_channel_username(text):
  value = (text or "").strip()
  value = re.sub(
      r"^(?:https?://)?(?:www\.)?t\.me/", "", value, flags=re.IGNORECASE
  ).strip("/")
  value = value.removeprefix("@")
  if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{4,31}", value):
    raise ValueError("أرسل يوزر قناة صحيحاً مثل @mychannel.")
  return value


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


def _parse_amount(text, allow_zero=False):
  value = (text or "").strip()
  if not re.fullmatch(r"\d{1,10}(?:\.\d{1,4})?", value):
    raise ValueError("أرسل كمية موجبة، ويمكن استخدام حتى 4 منازل عشرية.")
  try:
    amount = Decimal(value)
  except InvalidOperation as exc:
    raise ValueError("الكمية غير صحيحة.") from exc
  if amount < 0 or (amount == 0 and not allow_zero) or amount > MAX_POINTS:
    raise ValueError("الكمية خارج الحدود المسموحة.")
  return amount


def _open_transaction():
  connection = sqlite3.connect(
      str(DATABASE_PATH), timeout=15, isolation_level=None
  )
  connection.execute("PRAGMA busy_timeout = 15000")
  connection.execute(
      'CREATE TABLE IF NOT EXISTS "fuck" '
      "(k VARCHAR(4096) PRIMARY KEY, v BLOB, expire_time INTEGER DEFAULT NULL) "
      "WITHOUT ROWID"
  )
  connection.execute("BEGIN IMMEDIATE")
  return connection


def _read_value(connection, key):
  row = connection.execute(
      'SELECT v FROM "fuck" WHERE k = ? '
      "AND (expire_time IS NULL OR expire_time > ?) LIMIT 1",
      (key, time.time()),
  ).fetchone()
  return ENCODER.decode(row[0]) if row else None


def _write_value(connection, key, value):
  connection.execute(
      'REPLACE INTO "fuck" (k, v, expire_time) VALUES (?, ?, NULL)',
      (key, ENCODER.encode(value)),
  )


def _active_agent(agents, user_id):
  record = agents.get(str(user_id))
  if not isinstance(record, dict) or record.get("status") != "active":
    return None
  return record


def _agent_keyboard():
  return mk([
      [
          btn("➕ إضافة نقاط", callback_data="agent_add_points"),
          btn("➖ خصم نقاط", callback_data="agent_take_points"),
      ],
      [btn("💼 محفظتي", callback_data="agent_wallet")],
      [btn("↩️ القائمة الرئيسية", callback_data="back")],
  ])


def _owner_keyboard():
  agents = _get_agents()
  visible = [
      record
      for record in agents.values()
      if isinstance(record, dict) and record.get("status") != "archived"
  ]
  log_chat_id = db.get(LOG_CHAT_KEY)
  log_username = db.get(LOG_CHANNEL_USERNAME_KEY)
  if log_chat_id:
    log_status = (
        f"مضبوطة (@{log_username})" if log_username else f"مضبوطة ({log_chat_id})"
    )
  else:
    log_status = "غير مضبوطة"
  return (
      "إدارة الوكلاء\n\n"
      f"الوكلاء المسجلون: {len(visible)}\n"
      f"قناة السجلات: {log_status}\n"
      "يجب ضبط قناة السجلات ومنح البوت صلاحية النشر قبل إجراء تحويلات."
  ), mk([
      [btn("➕ إضافة وكيل", callback_data="agent_add")],
      [
          btn("💰 شحن محفظة", callback_data="agent_wallet_topup"),
          btn("✏️ تعيين الرصيد", callback_data="agent_wallet_set"),
      ],
      [
          btn("📋 قائمة الوكلاء", callback_data="agent_list:0"),
          btn("🧾 قناة السجلات", callback_data="agent_log_config"),
      ],
      [btn("↩️ رجوع للإعدادات", callback_data="setting_bot")],
  ])


async def _show_owner_panel(query):
  text, keyboard = _owner_keyboard()
  await query.edit_message_text(text, reply_markup=keyboard)


async def _require_agent(query):
  if is_active_agent(query.from_user.id):
    return True
  await query.answer("هذا القسم مخصص للوكلاء الفعّالين فقط.", show_alert=True)
  return False


async def _require_owner(query):
  if query.from_user.id == Config.OWNER_ID:
    return True
  await query.answer("إدارة الوكلاء مخصصة للمالك الأساسي فقط.", show_alert=True)
  return False


async def _ask_value(client, user_id, prompt, parser, error_message):
  current_prompt = prompt
  while True:
    answer = await ask_with_back(
        client,
        user_id,
        current_prompt,
        "agent_owner" if user_id == Config.OWNER_ID else "agent_panel",
        filters=filters.user(user_id),
    )
    if not answer:
      return None
    try:
      value = parser(answer.text or "")
    except ValueError:
      for message in (getattr(answer, "sent_message", None), answer):
        if message is not None:
          try:
            await message.delete()
          except Exception:
            pass
      current_prompt = f"{prompt}\n\n{error_message}"
      continue

    for message in (getattr(answer, "sent_message", None), answer):
      if message is not None:
        try:
          await message.delete()
        except Exception:
          pass
    return value


def _today_key():
  return datetime.now(LOCAL_TIMEZONE).date().isoformat()


async def _transfer_points(client, agent_id, target_id, amount, add_points):
  log_chat_id = db.get(LOG_CHAT_KEY)
  if not log_chat_id:
    return "log_missing", None

  async with ORDER_LOCK:
    connection = None
    audit_sent = False
    try:
      connection = _open_transaction()
      agents = _read_value(connection, AGENT_KEY) or {}
      agent = _active_agent(agents, agent_id)
      if not agent:
        connection.rollback()
        return "not_agent", None

      user_key = f"user_{target_id}"
      user_info = _read_value(connection, user_key)
      if not isinstance(user_info, dict):
        connection.rollback()
        return "no_user", None

      wallet = Decimal(str(agent.get("wallet", "0")))
      target_balance = Decimal(str(user_info.get("coins", 0)))
      if add_points and wallet < amount:
        connection.rollback()
        return "insufficient", None
      if not add_points and target_balance < amount:
        connection.rollback()
        return "target_insufficient", None

      wallet_after = wallet - amount if add_points else wallet
      target_after = (
          target_balance + amount if add_points else target_balance - amount
      )
      if target_after > MAX_POINTS:
        connection.rollback()
        return "target_limit", None
      today = _today_key()
      daily = _read_value(connection, DAILY_KEY) or {}
      stats = daily.get(str(agent_id), {})
      count = int(stats.get("count", 0)) + 1 if stats.get("date") == today else 1
      operation = "إضافة نقاط" if add_points else "خصم نقاط"
      audit_text = (
          "سجل عملية وكيل\n"
          f"العملية: {operation}\n"
          f"الوكيل: {agent_id}\n"
          f"المستخدم: {target_id}\n"
          f"الكمية: {_format_amount(amount)} نقطة\n"
          f"رصيد محفظة الوكيل بعد العملية: {_format_amount(wallet_after)}"
      )

      try:
        await client.send_message(log_chat_id, audit_text)
        audit_sent = True
      except Exception:
        logger.exception("Could not send agent transaction audit")
        connection.rollback()
        return "audit_failed", None

      agent["wallet"] = _format_amount(wallet_after)
      user_info["coins"] = float(target_after)
      daily[str(agent_id)] = {"date": today, "count": count}
      _write_value(connection, AGENT_KEY, agents)
      _write_value(connection, user_key, user_info)
      _write_value(connection, DAILY_KEY, daily)
      connection.commit()
      return "ok", {
          "wallet": wallet_after,
          "target_balance": target_after,
          "operation": operation,
      }
    except Exception:
      if connection is not None:
        connection.rollback()
      logger.exception("Agent points transaction failed")
      if audit_sent:
        try:
          await client.send_message(
              log_chat_id,
              f"تنبيه تصحيح: تعذر حفظ عملية الوكيل {agent_id} للمستخدم"
              f" {target_id}. راجع قاعدة البيانات قبل أي تسوية.",
          )
        except Exception:
          logger.exception("Could not send agent transaction correction")
      return "error", None
    finally:
      if connection is not None:
        connection.close()


async def _change_agent_wallet(client, actor_id, agent_id, amount, mode):
  log_chat_id = db.get(LOG_CHAT_KEY)
  if not log_chat_id:
    return "log_missing", None

  async with ORDER_LOCK:
    connection = None
    try:
      connection = _open_transaction()
      agents = _read_value(connection, AGENT_KEY) or {}
      record = agents.get(str(agent_id))
      if not isinstance(record, dict) or record.get("status") == "archived":
        connection.rollback()
        return "no_agent", None

      before = Decimal(str(record.get("wallet", "0")))
      after = before + amount if mode == "topup" else amount
      if after > MAX_POINTS:
        connection.rollback()
        return "wallet_limit", None
      action = "شحن محفظة" if mode == "topup" else "تعديل رصيد المحفظة"
      audit_text = (
          "سجل تعديل محفظة وكيل\n"
          f"المنفذ: {actor_id}\n"
          f"الوكيل: {agent_id}\n"
          f"العملية: {action}\n"
          f"الرصيد السابق: {_format_amount(before)}\n"
          f"الرصيد الجديد: {_format_amount(after)}"
      )
      try:
        await client.send_message(log_chat_id, audit_text)
      except Exception:
        logger.exception("Could not send agent wallet adjustment audit")
        connection.rollback()
        return "audit_failed", None

      record["wallet"] = _format_amount(after)
      _write_value(connection, AGENT_KEY, agents)
      connection.commit()
      return "ok", after
    except Exception:
      if connection is not None:
        connection.rollback()
      logger.exception("Agent wallet adjustment failed")
      return "error", None
    finally:
      if connection is not None:
        connection.close()


async def _finish(client, chat_id, text, owner=False):
  callback = "agent_owner" if owner else "agent_panel"
  await client.send_message(
      chat_id,
      text,
      reply_markup=mk([[btn("رجوع", callback_data=callback)]]),
  )


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


def ttd(timestamp) -> str:
  date = datetime.datetime.fromtimestamp(timestamp)
  formatted_date = date.strftime("%Y-%m-%d %H:%M:%S")
  return formatted_date


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
    lines.extend([
        "",
        f"يوزر القناة: @{escape(channel)}",
        f"عدد المشتركين: {count} : {required}",
    ])
  return "\n".join(lines)


def _force_panel_keyboard():
  rows = [
      [btn(f"حذف @{channel}", callback_data=f"setforce_remove:{channel}")]
      for channel in _force_channels()
  ]
  rows.extend([
      [btn("إضافة قناة جديدة", callback_data="setforce_add")],
      [btn("تحديث القائمة", callback_data="setforce")],
      [btn("رجوع", callback_data="back_admin")],
  ])
  return mk(rows)


async def _show_force_panel(query):
  await query.edit_message_text(
      _force_panel_content(),
      reply_markup=_force_panel_keyboard(),
      parse_mode=enums.ParseMode.HTML,
  )


# الهاندلرات (Handlers) والأوامر والأزرار
@app.on_message(filters.private & filters.regex("^/start$"), group=1)
async def ade(app, msg):
  user_id = msg.from_user.id
  if _is_admin(user_id):
    keys = admin_dashboard_keyboard()
    await msg.reply(
        """**• اهلا بك في لوحه الأدمن الخاصه بالبوت 🤖**

- يمكنك التحكم في البوت الخاص بك من هنا \n\n===================""",
        reply_markup=keys,
    )


@app.on_callback_query(filters.regex("^back_admin$"))
async def dailygiftt(app, query):
  user_id = query.from_user.id
  if not _is_admin(user_id):
    await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
    return
  keys = admin_dashboard_keyboard()
  rk = f"""**• اهلا بك في لوحه الأدمن الخاصه بالبوت 🤖**

- يمكنك التحكم في البوت الخاص بك من هنا \n\n==================="""
  await query.edit_message_text(rk, reply_markup=keys)


@app.on_callback_query(filters.regex("^admins_bot$"))
async def admins_panel(app, query):
  if not _is_admin(query.from_user.id):
    await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
    return

  admin_ids = db.get("admin_list") or []
  text = "إدارة الأدمنية\n\n"
  text += "\n".join(f"• <code>{admin_id}</code>" for admin_id in admin_ids)
  rows = []
  if query.from_user.id == Config.OWNER_ID:
    rows.append([
        btn("➕ إضافة أدمن", "add_admin"),
        btn("➖ حذف أدمن", "delete_admin"),
    ])
  rows.append([btn("↩️ رجوع للوحة الأدمن", "back_admin")])
  await query.edit_message_text(
      text, reply_markup=mk(rows), parse_mode=enums.ParseMode.HTML
  )


@app.on_callback_query(filters.regex("^add_admin$"), group=6)
async def add_admin(app, query):
  user_id = query.from_user.id
  if user_id != Config.OWNER_ID:
    await query.answer("إدارة صلاحيات الأدمن مخصصة لمالك البوت فقط.", show_alert=True)
    return
  await clear_section_message(query)
  askk = await ask_with_back(
      app,
      user_id,
      "يرجى إرسال معرف المستخدم لترقيته كمسؤول في البوت",
      "back_admin",
  )
  if not askk:
    return
  if askk.text:
    try:
      t_id = _parse_user_id(askk.text)
    except ValueError:
      await askk.reply(
          "يرجى إرسال معرف المستخدم بتنسيق صحيح", reply_markup=ADMIN_BACK
      )
      return
    s = _admin_ids()
    if t_id in s:
      await askk.reply(f"المستخدم {t_id} مسؤول بالفعل", reply_markup=ADMIN_BACK)
      return
    s.append(t_id)
    db.set("admin_list", s)
    await askk.reply(
        f"تمت إضافة المستخدم {t_id} كمسؤول في البوت", reply_markup=ADMIN_BACK
    )


@app.on_callback_query(filters.regex("^delete_admin$"), group=7)
async def ada_admin(app, query):
  user_id = query.from_user.id
  if user_id != Config.OWNER_ID:
    await query.answer("إدارة صلاحيات الأدمن مخصصة لمالك البوت فقط.", show_alert=True)
    return
  await clear_section_message(query)
  askk = await ask_with_back(
      app, user_id, "ارسل الان ايدي الشخص لازالته من الادمنية", "back_admin"
  )
  if not askk:
    return
  if askk.text:
    try:
      t_id = _parse_user_id(askk.text)
    except ValueError:
      await askk.reply("برجاء ارسل الايدي بشكل صحيح", reply_markup=ADMIN_BACK)
      return
    if t_id == Config.OWNER_ID:
      await askk.reply(
          "لا يمكن إزالة مالك البوت من قائمة الأدمنية.", reply_markup=ADMIN_BACK
      )
      return
    s = _admin_ids()
    if t_id not in s:
      await askk.reply("هذا المستخدم ليس ضمن الأدمنية.", reply_markup=ADMIN_BACK)
      return
    s.remove(t_id)
    db.set("admin_list", s)
    await askk.reply(f"تم مسح : {t_id} من ادمنية البوت", reply_markup=ADMIN_BACK)


@app.on_callback_query(filters.regex("^add_coins$"), group=8)
async def add_coinssw(app, query):
  user_id = query.from_user.id
  if not _is_admin(user_id):
    await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
    return
  await clear_section_message(query)
  askk = await ask_with_back(
      app, user_id, "ارسل الي دي العضو اللي تريد ترسله النقاط.", "back_admin"
  )
  if not askk:
    return
  if askk.text:
    try:
      t_id = _parse_user_id(askk.text)
    except ValueError:
      await askk.reply("ارسل الايدي بشكل صحيح", reply_markup=ADMIN_BACK)
      return
    ask2 = await ask_with_back(
        app, user_id, "ارسل عدد النقاط اللي تريد ارسالها للشخص", "back_admin"
    )
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
      await ask2.reply(
          "تعذر تحديث الرصيد حالياً. لم يتم تأكيد العملية.",
          reply_markup=ADMIN_BACK,
      )
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
      await app.send_message(
          int(t_id),
          f"• تم اضافة `{amount_text}` نقاط الى حسابك من قبل المطور",
      )
    except Exception as error:
      logger.warning("Balance notification failed (%s)", type(error).__name__)


@app.on_callback_query(filters.regex("^less_coin$"), group=9)
async def les_co(app, query):
  user_id = query.from_user.id
  if not _is_admin(user_id):
    await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
    return
  await clear_section_message(query)
  askk = await ask_with_back(
      app, user_id, "ارسل اي دي العضو اللي تريد تخصم منه النقاط", "back_admin"
  )
  if not askk:
    return
  if askk.text:
    try:
      t_id = _parse_user_id(askk.text)
    except ValueError:
      await askk.reply("رجاء ارسل الاي دي بشكل صحيح", reply_markup=ADMIN_BACK)
      return
    ask2 = await ask_with_back(
        app, user_id, "ارسل عدد النقاط اللي تريد خصمة من هذا الشخص", "back_admin"
    )
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
      await ask2.reply(
          "تعذر تحديث الرصيد حالياً. لم يتم تأكيد العملية.",
          reply_markup=ADMIN_BACK,
      )
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
      await app.send_message(
          int(t_id), f"• تم خصم `{amount_text}` نقاط من حسابك من قبل المطور"
      )
    except Exception as error:
      logger.warning("Balance notification failed (%s)", type(error).__name__)


@app.on_callback_query(filters.regex("^brods$"), group=10)
async def brod_ss(app, query):
  user_id = query.from_user.id
  if not _is_admin(user_id):
    await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
    return
  user_ids = sorted({
      int(match.group(1))
      for key in db.keys()
      if (match := re.fullmatch(r"user_(\d+)", str(key[0])))
  })
  count = len(user_ids)
  await clear_section_message(query)
  ask1 = await ask_with_back(
      app,
      user_id,
      "• ارسل محتوى الاذاعة : \n\n•يمكنك ارسال : نص او ميديا او الخ",
      "back_admin",
  )
  if not ask1:
    return
  if ask1:
    c = 0
    msg_id = ask1.id
    for target_id in user_ids:
      try:
        await app.copy_message(target_id, user_id, msg_id)
        c += 1
        await app.edit_message_text(
            user_id,
            ask1.request.id,
            f"• جاري الاذاعة الى `{count}` مستخدم 🌐\n\n• تم الارسال الى `{c}` مستخدم",
        )
      except Exception:
        continue
    all_failed = int(count) - int(c)
    await ask1.reply(
        f"• تم انتهاء الاذاعة بنجاح ✅:\n\n• عدد الاشخاص الذين شاهدو الاذاعة :"
        f" {c}\n\n• المستخدمين الذين لم يستطع البوت ارسال اذاعه لهم"
        f" {all_failed} مستخدم",
        reply_markup=mk([[btn(text="رجوع", callback_data="back_admin")]]),
    )
    await app.edit_message_text(
        user_id,
        ask1.request.id,
        f"• تم الارسال الى `{c}` مستخدم",
        reply_markup=mk([[btn(text="رجوع", callback_data="back_admin")]]),
    )


@app.on_callback_query(filters.regex("^get_infos$"), group=11)
async def get_infso(app, query):
  user_id = query.from_user.id
  if not _is_admin(user_id):
    await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
    return
  await clear_section_message(query)
  ask = await ask_with_back(
      app, user_id, "ارسل الان ايدي الشخص اللي تريد تعرف معلوماته", "back_admin"
  )
  if not ask:
    return
  if ask.text:
    try:
      target_id = int(ask.text)
    except:
      return
    d = db.get(f"user_{target_id}")
    if d is None:
      await ask.reply("هذا الحساب غير موجود في البوت", reply_markup=ADMIN_BACK)
      return
    try:
      coins = d["coins"]
      ddd = str(d["date"]).split(".")[0]
      date = ttd(int(ddd))
    except Exception as x:
      logger.warning("Unable to render user details (%s)", type(x).__name__)
      return
    await ask.reply(
        f"• معلومات حسابه :\n\n• عدد نقاطه : {coins}\n\n• تاريخ دخولة للبوت :"
        f" {date} ",
        reply_markup=_user_admin_keyboard(target_id),
    )


@app.on_callback_query(filters.regex("^setforce$"))
async def setforcee(app, query):
  if not _is_admin(query.from_user.id):
    await query.answer("هذا القسم مخصص للأدمن فقط.", show_alert=True)
    return
  await _show_force_panel(query)


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
      r"^(?:https?://)?(?:www\.)?t\.me/", "", raw_username, flags=re.IGNORECASE
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


# مسارات نظام الوكلاء المدمجة
@app.on_callback_query(filters.regex(r"^agent_panel$"))
async def agent_panel(client, query):
  if not await _require_agent(query):
    return
  await query.answer()
  await query.edit_message_text(
      "لوحة تحكم الوكيل 🛡️\n\nاختر العملية التي تريد تنفيذها.",
      reply_markup=_agent_keyboard(),
  )


@app.on_callback_query(filters.regex(r"^agent_wallet$"))
async def agent_wallet(client, query):
  if not await _require_agent(query):
    return
  agents = _get_agents()
  record = _active_agent(agents, query.from_user.id)
  daily = db.get(DAILY_KEY) or {}
  stats = daily.get(str(query.from_user.id), {})
  count = int(stats.get("count", 0)) if stats.get("date") == _today_key() else 0
  await query.answer()
  await query.edit_message_text(
      "معلومات محفظتي\n\n"
      f"رصيد النقاط: {_format_amount(record.get('wallet', '0'))}\n"
      f"العمليات اليوم: {count}",
      reply_markup=mk([[btn("رجوع للوحة الوكيل", callback_data="agent_panel")]]),
  )


async def _agent_transfer_flow(client, query, add_points):
  if not await _require_agent(query):
    return
  user_id = query.from_user.id
  await clear_section_message(query)
  target_id = await _ask_value(
      client,
      user_id,
      "أرسل آيدي المستخدم الذي تريد التعامل معه.",
      _parse_user_id,
      "الآيدي غير صحيح. أرسل أرقام الآيدي فقط.",
  )
  if target_id is None:
    return
  amount = await _ask_value(
      client,
      user_id,
      "أرسل كمية النقاط.",
      _parse_amount,
      "الكمية غير صحيحة. أرسل رقماً موجباً حتى 4 منازل عشرية.",
  )
  if amount is None:
    return

  status, result = await _transfer_points(
      client, user_id, target_id, amount, add_points
  )
  messages = {
      "log_missing": "لم تُضبط قناة السجلات بعد. يرجى مراجعة المالك.",
      "audit_failed": "تعذر تسجيل العملية في قناة الرقابة؛ لم تُنفذ أي حركة.",
      "not_agent": "حساب الوكيل غير فعّال.",
      "no_user": (
          "لا يوجد حساب لهذا المستخدم. يجب أن يبدأ البوت أولاً عبر /start."
      ),
      "insufficient": "رصيدك غير كافي، يرجى مراجعة المطور لشحن المحفظة.",
      "target_insufficient": "رصيد المستخدم غير كافٍ للخصم المطلوب.",
      "target_limit": "الرصيد الناتج يتجاوز الحد الأعلى المسموح.",
      "error": "تعذر إتمام العملية بأمان. لم يتم تأكيدها؛ راجع المالك.",
  }
  if status != "ok":
    await _finish(client, user_id, messages.get(status, messages["error"]))
    return

  verb = "أُضيفت" if add_points else "خُصمت"
  receipt = (
      f"تمت العملية: {verb} {_format_amount(amount)} نقطة "
      f"{'للمستخدم' if add_points else 'من المستخدم'} {target_id}.\n"
      f"رصيد المستخدم: {_format_amount(result['target_balance'])}\n"
      f"رصيد محفظتك: {_format_amount(result['wallet'])}"
  )
  await _finish(client, user_id, receipt)
  try:
    action = "إضافة" if add_points else "خصم"
    await client.send_message(
        target_id,
        f"تمت {action} {_format_amount(amount)} نقطة إلى حسابك بواسطة وكيل.\n"
        f"رصيدك الحالي: {_format_amount(result['target_balance'])}",
    )
  except Exception:
    logger.info("Could not notify the user about an agent points transaction")


@app.on_callback_query(filters.regex(r"^agent_add_points$"))
async def agent_add_points(client, query):
  await _agent_transfer_flow(client, query, True)


@app.on_callback_query(filters.regex(r"^agent_take_points$"))
async def agent_take_points(client, query):
  await _agent_transfer_flow(client, query, False)


@app.on_callback_query(filters.regex(r"^agent_owner$"))
async def agent_owner(client, query):
  if not await _require_owner(query):
    return
  await query.answer()
  await _show_owner_panel(query)


@app.on_callback_query(filters.regex(r"^agent_add$"))
async def agent_add(client, query):
  if not await _require_owner(query):
    return
  await clear_section_message(query)
  agent_id = await _ask_value(
      client,
      query.from_user.id,
      "أرسل آيدي المستخدم الذي تريد إضافته وكيلاً.",
      _parse_user_id,
      "أرسل آيدي رقمي صحيح.",
  )
  if agent_id is None:
    return
  amount = await _ask_value(
      client,
      query.from_user.id,
      "أرسل رصيد المحفظة الابتدائي.",
      lambda value: _parse_amount(value, allow_zero=True),
      "أرسل رصيداً من صفر إلى 1,000,000,000.",
  )
  if amount is None:
    return

  log_chat_id = db.get(LOG_CHAT_KEY)
  if not log_chat_id:
    await _finish(
        client,
        query.from_user.id,
        "اضبط قناة السجلات أولاً ثم أعد إضافة الوكيل.",
        owner=True,
    )
    return

  async with ORDER_LOCK:
    connection = None
    try:
      connection = _open_transaction()
      agents = _read_value(connection, AGENT_KEY) or {}
      existing = agents.get(str(agent_id))
      if isinstance(existing, dict) and existing.get("status") != "archived":
        connection.rollback()
        await _finish(
            client, query.from_user.id, "هذا المستخدم مسجل كوكيل بالفعل.", True
        )
        return
      audit = (
          "إضافة وكيل\n"
          f"المالك: {query.from_user.id}\n"
          f"الوكيل: {agent_id}\n"
          f"رصيد المحفظة الابتدائي: {_format_amount(amount)}"
      )
      try:
        await client.send_message(log_chat_id, audit)
      except Exception:
        logger.exception("Could not send agent creation audit")
        connection.rollback()
        await _finish(
            client,
            query.from_user.id,
            "تعذر التسجيل في قناة السجلات؛ لم تتم إضافة الوكيل.",
            owner=True,
        )
        return
      agents[str(agent_id)] = {
          "status": "active",
          "wallet": _format_amount(amount),
          "created_at": int(time.time()),
          "created_by": query.from_user.id,
      }
      _write_value(connection, AGENT_KEY, agents)
      connection.commit()
    except Exception:
      if connection is not None:
        connection.rollback()
      logger.exception("Could not add agent")
      await _finish(
          client, query.from_user.id, "تعذر إضافة الوكيل بأمان.", owner=True
      )
      return
    finally:
      if connection is not None:
        connection.close()

  await _finish(
      client,
      query.from_user.id,
      f"تمت إضافة الوكيل {agent_id} برصيد {_format_amount(amount)} نقطة.",
      owner=True,
  )


@app.on_callback_query(filters.regex(r"^agent_wallet_(topup|set)$"))
async def agent_owner_wallet_change(client, query):
  if not await _require_owner(query):
    return
  mode = query.data.rsplit("_", 1)[-1]
  await clear_section_message(query)
  agent_id = await _ask_value(
      client,
      query.from_user.id,
      "أرسل آيدي الوكيل.",
      _parse_user_id,
      "أرسل آيدي رقمي صحيح.",
  )
  if agent_id is None:
    return
  amount = await _ask_value(
      client,
      query.from_user.id,
      "أرسل كمية الشحن." if mode == "topup" else "أرسل الرصيد الجديد للمحفظة.",
      lambda value: _parse_amount(value, allow_zero=mode == "set"),
      "الكمية غير صحيحة. أرسل رقماً من صفر إلى 1,000,000,000.",
  )
  if amount is None:
    return
  status, after = await _change_agent_wallet(
      client, query.from_user.id, agent_id, amount, mode
  )
  if status == "ok":
    text = f"تم تحديث محفظة الوكيل {agent_id}. الرصيد الجديد: {_format_amount(after)} نقطة."
  elif status == "log_missing":
    text = "اضبط قناة السجلات أولاً."
  elif status == "audit_failed":
    text = "تعذر تسجيل التعديل؛ لم يتغير رصيد المحفظة."
  elif status == "no_agent":
    text = "الوكيل غير موجود أو مؤرشف."
  elif status == "wallet_limit":
    text = "الرصيد الناتج يتجاوز الحد الأعلى المسموح."
  else:
    text = "تعذر تحديث المحفظة بأمان."
  await _finish(client, query.from_user.id, text, owner=True)


def _agent_list_keyboard(agents, page):
  page_size = 8
  active_records = [
      (agent_id, record)
      for agent_id, record in sorted(
          agents.items(), key=lambda item: int(item[0])
      )
      if isinstance(record, dict) and record.get("status") != "archived"
  ]
  pages = max(1, (len(active_records) + page_size - 1) // page_size)
  page = min(max(page, 0), pages - 1)
  rows = []
  for agent_id, record in active_records[
      page * page_size : (page + 1) * page_size
  ]:
    active = record.get("status") == "active"
    status = "فعّال" if active else "متوقف"
    wallet = escape(_format_amount(record.get("wallet", "0")))
    rows.append([
        btn(
            f"{agent_id} · {status} · {wallet} نقطة",
            callback_data=f"agent_show:{agent_id}",
        )
    ])
    rows.append([
        btn(
            "تعطيل" if active else "تفعيل",
            callback_data=f"agent_status:{agent_id}",
        ),
        btn("أرشفة", callback_data=f"agent_archive:{agent_id}"),
    ])
  navigation = []
  if page > 0:
    navigation.append(btn("السابق", callback_data=f"agent_list:{page - 1}"))
  if page + 1 < pages:
    navigation.append(btn("التالي", callback_data=f"agent_list:{page + 1}"))
  if navigation:
    rows.append(navigation)
  rows.append([btn("رجوع لإدارة الوكلاء", callback_data="agent_owner")])
  return active_records, pages, page, mk(rows)


async def _show_agent_list(query, page):
  agents = _get_agents()
  records, pages, page, keyboard = _agent_list_keyboard(agents, page)
  if records:
    text = (
        f"الوكلاء المسجلون ({len(records)})\n"
        f"الصفحة {page + 1} من {pages}\n"
        "اضغط على اسم الوكيل لعرض التفاصيل."
    )
  else:
    text = "لا يوجد وكلاء مسجلون حالياً."
  await query.edit_message_text(text, reply_markup=keyboard)


@app.on_callback_query(filters.regex(r"^agent_list(?::\d+)?$"))
async def agent_list(client, query):
  if not await _require_owner(query):
    return
  page_match = re.search(r":(\d+)$", query.data)
  await query.answer()
  await _show_agent_list(query, int(page_match.group(1)) if page_match else 0)


@app.on_callback_query(filters.regex(r"^agent_show:(\d+)$"))
async def agent_show(client, query):
  if not await _require_owner(query):
    return
  agent_id = query.data.split(":", 1)[1]
  record = _get_agents().get(agent_id)
  if not isinstance(record, dict) or record.get("status") == "archived":
    await query.answer("الوكيل غير موجود.", show_alert=True)
    return
  await query.answer()
  await query.edit_message_text(
      f"معلومات الوكيل {agent_id}\n"
      f"الحالة: {'فعّال' if record.get('status') == 'active' else 'متوقف'}\n"
      f"رصيد المحفظة: {_format_amount(record.get('wallet', '0'))} نقطة",
      reply_markup=mk([
          [btn("شحن المحفظة", callback_data="agent_wallet_topup")],
          [btn("رجوع للقائمة", callback_data="agent_list:0")],
      ]),
  )


@app.on_callback_query(filters.regex(r"^agent_status:(\d+)$"))
async def agent_toggle_status(client, query):
  if not await _require_owner(query):
    return
  agent_id = query.data.split(":", 1)[1]
  agents = _get_agents()
  record = agents.get(agent_id)
  if not isinstance(record, dict) or record.get("status") == "archived":
    await query.answer("الوكيل غير موجود.", show_alert=True)
    return
  async with ORDER_LOCK:
    agents = _get_agents()
    re