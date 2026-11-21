# Nirvana

<img src="assets/nirvana-logo.png" alt="Nirvana" width="320">

x86-64の機械語からCを生成するデコンパイラ。命令デコーダ、IR、CFG解析、C出力をRustの標準ライブラリだけで実装しています。

## 使い方

実行例はLinux x86-64向けです。RustのstableツールチェーンとCコンパイラ（`cc`）を使います。

```sh
cc -O2 -c tests/fixtures/cases/diamond.c -o /tmp/nirvana-diamond.o
cargo run --release -- /tmp/nirvana-diamond.o --emit readable-c
```

既定では`fixture`関数を読みます。別の関数は`--symbol NAME`で指定します。
IRやCFGの出力、生バイト列の入力は[CLIと対応範囲](docs/machine-frontend.md)を参照してください。

## 出力例

上の例の関数本体から抜粋:

```c
value = read64(input.field_0);
value = value <= 9 ? value * 3 : value + 20;
write64(input.field_8, value);
return value;
```

`read64`・`write64`は生成Cに含まれる境界検査付きのメモリアクセスです。
生成関数はゲストメモリの配列とアドレス範囲を受け取ります。

## 対応範囲

入力は、関数シンボルとサイズを持つELF64の`.o`、実行ファイル、PIEです。
`module-*`では入口を`--entry ADDRESS`で指定し、strip後のELFも`.eh_frame`の範囲情報から読み取れます。
整数演算・比較・分岐・スタック操作の一部を扱います。
制御フローに応じて`if/else`、`for`、`while`、`do/while`、`goto`を出力します。
変数名は値の使われ方から生成し、整数型は保存する値の幅から選びます。
`--emit types`では、SSA値の使用制約とフィールド・配列の候補をJSONで確認できます。
`--emit record-types`では、ポインタの受渡しとフィールド参照から推定した構造体候補をCの宣言として確認できます。
`--emit references`では、ELFの文字列・シンボル・外部呼出しの引数の対応を確認できます。
`--emit effects-readable-c`は、`puts`の外部結果入力と境界検査を保ち、制御構造を復元したCを出力します。
`--run-effects 7`で出力と返り値を試せます。
`--emit module-c`は`main`から複数関数を扱う実行用Cを生成します。
内部・間接呼出しとゲストスタックを保持し、Linux x86-64のPOSIXアダプタを通してHTTPサーバfixtureを実行できます。
`--emit module-readable-c`は同じ実行状態を保ち、名前付き関数と`if/while`を使って出力します。
`--emit module-locals-c`は、値の生存範囲からまとめた局所変数とφの辺上コピーを加え、呼出し・途中再開時にはゲスト状態から値を復元します。
`--emit module-values`では、関数ごとの値ID・生存集合・呼出し前後の値と、メモリ世代・Loadへの書込み候補をJSONで確認できます。
`--emit ssa-c`は単一関数を名前付きの局所変数で描画し、元の全レジスタへ書込みを反映します。
参照幅が揃う局所アドレスには型名を付け、動的な配列参照を`element(base, index, stride)`で表示します。
入力条件・対応命令・今後の対象は[機械語とCLI](docs/machine-frontend.md)にまとめています。

## 開発

```sh
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
```

`main`へのpushとpull requestでは、[GitHub Actions](.github/workflows/ci.yml)がRust/Pythonの通常テスト、Clippy、fmtを検査します。

[ドキュメント](docs/README.md)に設計・実行モデル・検証方法をまとめています。
テスト入力の追加と生成方法は[C fixtures](tests/fixtures/README.md)を参照してください。
複数モジュール・間接呼出し・socket I/Oの評価には[小さなHTTPサーバ](tests/fixtures/http-server/README.md)を使います。
