from discord.ext import commands
from discord import app_commands, Interaction
from .. import core

class PricingCog(commands.Cog):
    @app_commands.command(name="値段変更", description="サービス価格を変更し、既設パネルも更新します")
    async def change_price_cmd(self, interaction: Interaction):
        await core.change_price_cmd(interaction)

async def setup(bot):
    await bot.add_cog(PricingCog(bot))
