from __future__ import annotations
import asyncio, sys
from pathlib import Path
import discord
from discord import app_commands
from discord.ext import commands
ROOT=Path(__file__).resolve().parent.parent
TSUM_DIR=ROOT/"modules"/"tsum"
if str(TSUM_DIR) not in sys.path: sys.path.insert(0,str(TSUM_DIR))
import tsum_bot_core as core

class TsumCog(commands.Cog):
    def __init__(self, bot):
        self.bot=bot; self._commands=[]
    async def cog_load(self):
        core.bot=self.bot
        for name in ("MenuView","TicketView","FreeDaikouView","RentalPanelView"):
            cls=getattr(core,name,None)
            if cls:
                try: self.bot.add_view(cls())
                except Exception as e: print(f"[tsum] add_view({name}) failed: {e}")
        for name in ("RetryLoginButton","GuestRetryButton"):
            cls=getattr(core,name,None)
            if cls:
                try: self.bot.add_dynamic_items(cls)
                except Exception as e: print(f"[tsum] add_dynamic_items({name}) failed: {e}")
        for name in ("_rental_expiry_watcher","_achievement_channel_updater","_discord_proxy_watchdog","_proxy_pool_worker"):
            fn=getattr(core,name,None)
            if fn:
                try: asyncio.create_task(fn())
                except Exception as e: print(f"[tsum] worker {name} failed: {e}")
        for callback,kwargs in core._COMMANDS:
            try:
                cmd=app_commands.Command(callback=callback,**kwargs)
                self.bot.tree.add_command(cmd); self._commands.append(cmd)
            except Exception as e: print(f"[tsum] command register failed: {getattr(callback,'__name__',callback)}: {e}")
        for fn in core._EVENTS:
            try: self.bot.add_listener(fn,name=fn.__name__)
            except Exception as e: print(f"[tsum] event register failed: {fn.__name__}: {e}")
        if core._TREE_ERRORS:
            try: self.bot.tree.on_error=core._TREE_ERRORS[-1]
            except Exception as e: print(f"[tsum] tree error register failed: {e}")
        try:
            gid=getattr(core,"GUILD_ID",None)
            if gid:
                g=discord.Object(id=int(gid)); self.bot.tree.copy_global_to(guild=g)
                await self.bot.tree.sync(guild=g); self.bot.tree.clear_commands(guild=None); await self.bot.tree.sync()
            else: await self.bot.tree.sync()
        except Exception as e: print(f"[tsum] tree sync failed: {e}")

async def setup(bot): await bot.add_cog(TsumCog(bot))
