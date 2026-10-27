from discord.ext import commands
from discord import app_commands, Interaction
from .. import core

class RecordsCog(commands.Cog):
    @app_commands.command(name="代行実績", description="このチャンネルを代行実績の投稿先に設定します")
    async def set_jisseki_channel_cmd(self, interaction: Interaction):
        await core.set_jisseki_channel_cmd(interaction)

async def setup(bot):
    await bot.add_cog(RecordsCog(bot))
