from discord.ext import commands
from discord import app_commands, Interaction
from .. import core

class PanelCog(commands.Cog):
    @app_commands.command(name="にゃんこパネル設置", description="VIP代行自販機パネルを設置します")
    async def vip_panel_cmd(self, interaction: Interaction):
        await core.vip_panel_cmd(interaction)

async def setup(bot):
    await bot.add_cog(PanelCog(bot))
