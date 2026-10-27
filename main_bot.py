from __future__ import annotations
import os, discord
from discord.ext import commands
PROFILE=os.environ.get("COGS_PROFILE","tsum").strip().lower()
intents=discord.Intents.default(); intents.message_content=True
bot=commands.Bot(command_prefix="!",intents=intents,help_command=None)
async def setup_hook():
    if PROFILE in ("tsum","both"): await bot.load_extension("cogs.tsum")
    if PROFILE in ("ywp","both"): await bot.load_extension("cogs.ywp")
bot.setup_hook=setup_hook
@bot.event
async def on_ready(): print(f"[cogs] ログイン: {bot.user} ({bot.user.id}) / profile={PROFILE}")
def main():
    token=os.environ.get("DISCORD_TOKEN","").strip()
    if not token: raise SystemExit("DISCORD_TOKEN が設定されていません。")
    bot.run(token)
if __name__=="__main__": main()
