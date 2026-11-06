import os
from dotenv import load_dotenv

# تحميل المتغيرات من ملف .env إذا كان موجوداً محلياً
load_dotenv()

class Config:
    # توكن البوت الأساسي (يتم جلبه من BotFather)
    BOT_TOKEN = os.getenv("8918257481:AAHd3VjfpGeb-M7oFRCRYWQHM8-d6Bh2uik", "")
    
    # آيدي مالك البوت (المالك الأساسي الذي يمتلك الصلاحيات المطلقة)
    OWNER_ID = int(os.getenv("OWNER_ID", "7379818403"))
    
    # بيانات الاتصال بـ Telegram API (اختياري، إذا كان البوت يستخدم UserBot أو مكتبات متقدمة)
    API_ID = os.getenv("33102618")
    API_HASH = os.getenv("3e35792a1cb6a7d6f49f54c4839f9102")

# التحقق السريع من توفر التوكن عند التشغيل
if not Config.BOT_TOKEN:
    raise RuntimeError("Set TG_BOT_TOKEN in the environment before starting the bot.")
  
