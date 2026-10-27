from .main_bot import bot
import os
bot.run(os.environ["DISCORD_BOT_TOKEN"])
