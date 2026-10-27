from __future__ import annotations
import sys
from pathlib import Path
import discord
from discord import app_commands
from discord.ext import commands
ROOT=Path(__file__).resolve().parent.parent
YWP_DIR=ROOT/"modules"/"ywp"
if str(YWP_DIR) not in sys.path: sys.path.insert(0,str(YWP_DIR))
import ywp_core as core

class YWPCog(commands.Cog):
    def __init__(self, bot):
        self.bot=bot; self._commands=[]
    async def cog_load(self):
        core.bot=self.bot
        for name in ("PanelView","CancelView","HitodamaTestView","AgedAccountView","VipAccountView","PaidVipView","AdminPanelView"):
            cls=getattr(core,name,None)
            if cls:
                try: self.bot.add_view(cls())
                except Exception as e: print(f"[ywp] add_view({name}) failed: {e}")
        for callback,kwargs in core._COMMANDS:
            try:
                cmd=app_commands.Command(callback=callback,**kwargs)
                self.bot.tree.add_command(cmd); self._commands.append(cmd)
            except Exception as e: print(f"[ywp] command register failed: {getattr(callback,'__name__',callback)}: {e}")
        for fn in core._EVENTS:
            try: self.bot.add_listener(fn,name=fn.__name__)
            except Exception as e: print(f"[ywp] event register failed: {fn.__name__}: {e}")
        if core._TREE_ERRORS:
            try: self.bot.tree.on_error=core._TREE_ERRORS[-1]
            except Exception as e: print(f"[ywp] tree error register failed: {e}")
        try: await self.bot.tree.sync()
        except Exception as e: print(f"[ywp] tree sync failed: {e}")

async def setup(bot): await bot.add_cog(YWPCog(bot))
