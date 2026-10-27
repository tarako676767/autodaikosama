from discord.ext import commands
from discord import app_commands, Interaction
from .. import core

class PayPayCog(commands.Cog):
    @app_commands.command(name="paypayログイン", description="PayPayアカウントを登録します")
    @app_commands.describe(phone="電話番号（例: 09012345678）", password="PayPayパスワード")
    async def paypay_login(self, interaction: Interaction, phone: str, password: str):
        await core.paypay_login(interaction, phone, password)

    @app_commands.command(name="paypayログアウト", description="登録済みのPayPay情報を削除します")
    async def paypay_delete(self, interaction: Interaction):
        await core.paypay_delete(interaction)

async def setup(bot):
    await bot.add_cog(PayPayCog(bot))
