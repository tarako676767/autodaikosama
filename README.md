# Cogs化パッケージ

アップロードされた **30MBのツムツムZIP** と **約1.2MBのぷにぷにZIP** の両方を含めて、Discordコマンド登録部分をCog化したパッケージです。

- `cogs/tsum.py` — ツムツム
- `cogs/ywp.py` — ぷにぷに
- `modules/tsum/tsum_bot_core.py` — ツムツムのコア
- `modules/ywp/ywp_core.py` — ぷにぷにのコア
- 元ZIPのデータ、PayPay、Tor等も保持

単体起動:
```bash
export DISCORD_TOKEN="BOT_TOKEN"
export COGS_PROFILE="tsum"
python main_bot.py
```
ぷにぷに:
```bash
export COGS_PROFILE="ywp"
python main_bot.py
```

`both` は元ソースに `/パネル設置` 等の同名コマンドがあるため競合します。通常はどちらか一方をロードしてください。

元の処理ロジックとViewをなるべく変更せず、Botへのコマンド登録をCogアダプタへ移しています。
