# Nirvana

<img src="assets/nirvana-logo.png" alt="Nirvana" width="320">

x86-64の機械語からCを生成するデコンパイラです。命令デコーダ、IR、CFG解析、C出力をRustの標準ライブラリで実装しています。

## 使い方

Linux x86-64、Rust stable、C11コンパイラ（`cc`）を使います。ビルド管理コマンドにはPython 3を使います。

```sh
cc -O2 -c tests/fixtures/cases/diamond.c -o /tmp/nirvana-diamond.o
python3 tools/dev.py cargo run --release -- /tmp/nirvana-diamond.o --emit readable-c
```

既定では`fixture`関数を読みます。別の関数は`--symbol NAME`で指定します。
この例の関数本体は、次のように出力されます。

```c
value = read64(input.field_0);
value = value <= 9 ? value * 3 : value + 20;
write64(input.field_8, value);
return value;
```

`read64`・`write64`は、生成Cに含まれる境界検査付きのゲストメモリアクセスです。
実行結果の対応は[実行モデル](docs/equivalence.md)で定義しています。

リンク済みELFでは、入口から複数関数を読み込めます。

```sh
python3 tools/dev.py cargo run --release -- ./program --symbol main --emit module-readable-c
```

| 出力 | 用途 |
| --- | --- |
| `readable-c` | 単一関数の制御構造・局所変数・メモリ参照を読む |
| `module-readable-c` / `module-locals-c` | 呼出しとゲスト状態を保って複数関数を読む |
| `types` / `record-types` | 整数幅・フィールド配置・構造体の候補を調べる |
| `references` / `module-values` / `module-jumps` | 文字列・値の寿命・書込み元・分岐先を調べる |

対応する命令・入力形式と全オプションは[CLIリファレンス](docs/machine-frontend.md)にあります。
複数関数とsocket I/Oの実行例には[HTTPサーバfixture](tests/fixtures/http-server/README.md)を使えます。

## 開発

```sh
python3 tools/dev.py cargo test --locked --all-targets
python3 tools/dev.py cargo clippy --locked --all-targets -- -D warnings
cargo fmt --all -- --check
python3 -m unittest discover -s tools/tests
```

開発用ビルドはデバッグ情報とincremental cacheを省きます。`dev.py cargo`はworktree間でビルド領域を共有し、Cargo中間ファイルが2GiBを超えると実行前後に整理します。実行ファイルは通常の`target/debug/`・`target/release/`に残ります。

実験の出力には`{out}`を渡すと、終了時に一時ファイルを片付けます。

```sh
python3 tools/dev.py run -- python3 tools/build_fixtures.py --out '{out}'
python3 tools/dev.py status
python3 tools/dev.py clean --runs
```

`run --keep`は最新2件・合計512MiBの範囲で出力とコマンドを保持します。保存予算を超えたrunは削除して失敗を返します。長期保存する比較証跡は、必要な入力・ログ・hashをcheckpointとして別途管理します。

`dev.py cargo`と`dev.py run`は、起動時に登録されているworktreeの`target`合計を開始前・実行中・終了時に検査します。既定4GiBを超えたら、その管理コマンドで起動したプロセス群を停止し、終了コード75と大きい保存先を報告します。一時出力と整理対象のキャッシュを片付け、既存の実行ファイル・証跡は保持します。コマンド終了時には、そのプロセス群に残るバックグラウンド処理も片付けます。実行中は約1秒間隔で検査するため、検査の間に一時的な超過が生じます。

上限は`--cache-mib`・`--runs-mib`・`--max-target-mib`をサブコマンドの前に指定できます。通常の`cargo`で直接起動した処理や`target`外の出力は、手動で保存期間を管理します。

[ドキュメント](docs/README.md)に設計・実行モデル・検証方法を、[テストガイド](tests/README.md)にsuite構成とケースの追加方法をまとめています。
