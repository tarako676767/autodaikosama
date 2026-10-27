# にゃんこ代行 Discord Bot - Cogs版

元の `main13 7(2).py` をベースに、Discordのスラッシュコマンド登録部分をCogsへ分離した構成です。

## 構成
- `main_bot.py` - Bot起動・Cogs読み込み・イベント
- `core.py` - 元コードの処理本体、View/Modal、代行処理、DB/API処理
- `cogs/records.py` - `/代行実績`
- `cogs/points.py` - `/ポイント認証` `/ポイント` `/ポイント代行` `/ポイント変更`
- `cogs/panel.py` - `/にゃんこパネル設置`
- `cogs/paypay.py` - `/paypayログイン` `/paypayログアウト`
- `cogs/pricing.py` - `/値段変更`

## 重要
既存の `Nyanko_*`、BCSFE、`DISCORD/discord_log.py`、PayPay関連ファイル等はこの分割対象に含めていません。
元の実行環境にあるものを同じプロジェクトへ残してください。

`core.py` は元ファイルの `__file__` 基準パスを維持するため、`main_bot.py` と同じ階層に置いてあります。

## 起動
```bash
python -m main13_cogs.main_bot
```

またはプロジェクトルートにこのパッケージを展開して、環境変数 `DISCORD_BOT_TOKEN` を設定してください。
