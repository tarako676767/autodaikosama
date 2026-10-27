from discord.ext import commands
from discord import app_commands, Interaction
from .. import core

class PointsCog(commands.Cog):
    @app_commands.command(name="ポイント認証", description="ポイント不正対策用の端末認証URLを発行します")
    async def point_auth_cmd(self, interaction: Interaction):
        await core.point_auth_cmd(interaction)

    @app_commands.command(name="ポイント", description="ポイント残高と履歴を確認します")
    async def point_balance_cmd(self, interaction: Interaction):
        await core.point_balance_cmd(interaction)

    @app_commands.command(name="ポイント代行", description="ポイントで利用できるにゃんこ大戦争代行パネルを設置します")
    async def point_panel_cmd(self, interaction: Interaction):
        await core.point_panel_cmd(interaction)

    @app_commands.command(name="ポイント変更", description="ポイント代行の必要ポイント数を変更します")
    async def change_point_price_cmd(self, interaction: Interaction):
        await core.change_point_price_cmd(interaction)

async def setup(bot):
    await bot.add_cog(PointsCog(bot))
