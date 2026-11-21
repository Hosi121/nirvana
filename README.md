# Nirvana

<img src="assets/nirvana-logo.png" alt="Nirvana" width="320">

x86-64の機械語からCを生成するデコンパイラです。命令デコーダ、IR、CFG解析、C出力をRustの標準ライブラリで実装しています。

## 使い方

Linux x86-64、Rust stable、C11コンパイラ（`cc`）を使います。

```sh
cc -O2 -c tests/fixtures/cases/diamond.c -o /tmp/nirvana-diamond.o
cargo run --release -- /tmp/nirvana-diamond.o --emit readable-c
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
cargo run --release -- ./program --symbol main --emit module-readable-c
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
cargo test --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo fmt --all -- --check
python3 -m unittest discover -s tools/tests
```

[ドキュメント](docs/README.md)に設計・実行モデル・検証方法を、[テストガイド](tests/README.md)にsuite構成とケースの追加方法をまとめています。
