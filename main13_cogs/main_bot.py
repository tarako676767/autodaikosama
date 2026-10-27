import asyncio
import os
import logging
import discord
from discord.ext import commands

from . import core

logger = logging.getLogger(__name__)

EXTENSIONS = (
    "main13_cogs.cogs.records",
    "main13_cogs.cogs.points",
    "main13_cogs.cogs.panel",
    "main13_cogs.cogs.paypay",
    "main13_cogs.cogs.pricing",
)

class MainBot(commands.Bot):
    async def setup_hook(self):
        # core.py 内のバックグラウンド処理から参照されるBot本体を設定。
        core.bot = self

        for extension in EXTENSIONS:
            try:
                await self.load_extension(extension)
                print(f"[Cogs] loaded: {extension}")
            except Exception:
                logger.exception(f"[Cogs] failed to load: {extension}")
                raise

        try:
            asyncio.create_task(core._point_referral_worker())
        except Exception:
            logger.exception("point referral worker start failed")

        try:
            synced_global = await self.tree.sync()
            print(f"[Discord] グローバルコマンド同期完了: {len(synced_global)}個")

            # 既存のギルドコマンドを整理し、現在のグローバルコマンドをコピー。
            for guild in self.guilds:
                try:
                    self.tree.clear_commands(guild=guild)
                    self.tree.copy_global_to(guild=guild)
                    synced = await self.tree.sync(guild=guild)
                    print(f"[Discord] {guild.name} にコマンド同期完了: {len(synced)}個")
                except Exception:
                    logger.exception(f"Discord guild command sync failed: {guild.id}")
        except Exception:
            logger.exception("Discord slash command sync failed")

    async def on_ready(self):
        for guild in self.guilds:
            try:
                await core._point_cache_invites(guild)
            except Exception:
                pass

    async def on_member_join(self, member):
        if member.bot:
            return
        guild = member.guild
        try:
            invites = await guild.invites()
        except Exception:
            return

        used_invite = None
        for inv in invites:
            old = core._POINT_INVITE_CACHE.get((guild.id, inv.code), (None, 0))[1]
            if int(inv.uses or 0) > int(old or 0):
                used_invite = inv
                break

        for inv in invites:
            inviter = getattr(inv, "inviter", None)
            core._POINT_INVITE_CACHE[(guild.id, inv.code)] = (
                int(inviter.id) if inviter else 0,
                int(inv.uses or 0),
            )

        if not used_invite:
            return

        with core._POINT_DB_LOCK:
            conn = core._point_db()
            row = conn.execute(
                "SELECT inviter_id FROM point_invites WHERE guild_id=? AND invite_code=?",
                (guild.id, used_invite.code),
            ).fetchone()
            conn.close()

        if not row or int(row[0]) == member.id:
            return

        import datetime
        joined = core._point_now().isoformat()
        with core._POINT_DB_LOCK:
            conn = core._point_db()
            conn.execute(
                "INSERT OR IGNORE INTO point_referrals"
                "(guild_id,inviter_id,member_id,invite_code,joined_at,eligible_at)"
                " VALUES(?,?,?,?,?,?)",
                (
                    guild.id,
                    int(row[0]),
                    member.id,
                    used_invite.code,
                    joined,
                    (core._point_now() + datetime.timedelta(
                        hours=core.POINT_INVITE_HOLD_HOURS
                    )).isoformat(),
                ),
            )
            conn.commit()
            conn.close()

def create_bot():
    intents = discord.Intents.default()
    intents.guilds = True
    intents.members = True
    # Message Content Intent は元コード側で必要な場合に環境/Developer Portal側で有効化。
    bot = MainBot(command_prefix="!", intents=intents)
    core.bot = bot
    return bot

bot = create_bot()

if __name__ == "__main__":
    token = os.getenv("DISCORD_BOT_TOKEN", "").strip()
    if not token:
        raise RuntimeError(
            "DISCORD_BOT_TOKEN が未設定です。環境変数 DISCORD_BOT_TOKEN を設定してください。"
        )
    bot.run(token)
