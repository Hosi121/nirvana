# C fixture corpus

デコンパイラの入力として使う、手書きのC11ソース20例です。
元Cを実行結果の正本とし、現在は対応する14例について手書きIRと生成Cを照合します。
機械語を入口にする別の検査もあり、40構成中33構成で自作デコーダ→IR→再生成Cまで照合しています。
元Cを直接読むパーサはなく、元Cはコンパイラで機械語にした入力と実行結果の正本として使います。

## 中身

| ファイル | 用途 |
| --- | --- |
| `cases/*.c` | 独立に書いた元C。生成Cのコピーではない |
| `cases.tsv` | fixture ID、対応する手書きIR ID、ソース上の特徴 |
| `inputs.tsv` | 共通の63入力。以前の57境界入力と6つの小さな具体例 |
| `golden.tsv` | 手計算した27期待値。全20例を最低1件ずつ含む |
| `fixture.h` | unsigned 64-bitの入力状態4要素と返り値の共通契約 |
| `harness.c` | 標準入力から状態を読み、返り値と最終状態4要素を出す |
| `helpers.c` | 関数呼び出しfixtureで使う別翻訳単位の関数 |
| `recovery/*.c` | 別corpusの12ソース。幅・alias・添字・複数入口goto・早期脱出 |

入力値、計算結果、状態はすべてunsigned 64-bitです。演算の折り返しを許可し、シフト量はマスクします。
配列の添字とループ回数は入力から小さな範囲へ制限しています。全fixtureが自動検査の入力で停止するようにしています。
`golden.tsv`はテスト対象のCから自動生成しません。例の意味を変えたときは、期待値の理由も確認してください。

## 対象

対応する手書きIRがあるのは、分岐、合流、早期return、ループ、入れ子、複数出口、共有末尾、
非可約な循環、非局所脱出、unsigned演算の14例です。

次の6例は手書きIRを用意していないソースfixtureです。
機械語経由では現在`do-while`・`short-circuit`・`struct-fields`がO0/O2とも通り、
`switch`・`array-walk`・`call-chain`は再配置が必要なため拒否しています。

| ID | 主に確かめたいこと |
| --- | --- |
| `switch` | case、意図的なfallthrough、default、早期return |
| `do-while` | 条件が最初から偽でも本体を一度実行すること |
| `short-circuit` | `&&`・`||`で副作用のある右辺を実行する条件 |
| `array-walk` | ローカル配列と境界内の添字アクセス |
| `struct-fields` | 構造体のフィールド、条件付きの交換 |
| `call-chain` | 別翻訳単位への呼び出しとオブジェクト内の再配置 |

特徴は元ソースの分類です。最適化後も同じCFGや命令が残るとは限りません。
`goto`の数や元ソースとの文字列一致を、正しさの基準にはしていません。

## Rustテストから実行する

リポジトリのルートで実行します。Rustと、`cc`として呼べるC11コンパイラを使います。

```sh
cargo test --test native_c
cargo test --test machine_pipeline -- --nocapture
cargo test --test recovery_fixture -- --nocapture
```

全20例×63入力×`-O0/-O2`の2,520ケースで元Cを実行します。最適化設定間の一致と、
手計算した期待値を確認します。対応する14例では、同じ入力で手書きIRと生成Cも照合し、
1,764ケースを追加で比較します。返り値だけでなく最終状態4要素も対象です。
検査用ファイルは一時ディレクトリに作り、終了時に削除します。

`machine_pipeline`は、同じCソースをコンパイルしたELFから自作readerで関数のバイト列を取得し、
手書きIRを使わずにIRへ変換します。現在は33構成×63入力の2,079ケースで元C・IR・再コンパイルした生成Cが一致し、
そのうち32構成は構造化前後の命令trace・全レジスタ・全メモリも比較します。
未対応の7構成は再配置が必要なケースです。詳細は[機械語フロントエンド](../../docs/machine-frontend.md)を参照してください。

`recovery_fixture`は独立した12ソース×O0/O2×69入力、計1,656比較を行います。
`byte-fields`・`packed-update`は幅と重なる更新、`strided-input`は添字、`selected-alias`は選択されたポインタ、
`three-entry-goto`は3か所から入る有限循環、`early-exit-chain`は複数の脱出、
`volatile-bound`は上限の再読と途中break、`cyclic-guard`は入口判定と折り返すcounterを確かめます。
`branch-break`・`branch-return`は異なる状態書込みを持つ脱出経路と、共通のbreak・返り値計算を含みます。
`two-phase-loops`は二つの独立したループの更新値・上限・終了後の状態を確かめます。
`branch-lifetimes`は条件で異なる定義が合流した後のループと、段階ごとの値の使い分けを確かめます。
全構成のliftを必須とし、失敗をskipしません。元C・IRの返り値と4状態ワードに加え、
readable CとIRはstackを含む64KiB全体のdigestも照合します。

## 機械語fixtureと実行結果を保存する

Python 3の標準ライブラリだけを使う生成道具があります。デコンパイラ本体の依存ではありません。

```sh
python3 tools/build_fixtures.py --list
python3 tools/build_fixtures.py
python3 tools/build_fixtures.py --case call-chain --opt O2 --out target/calls
```

既定では`target/c-fixtures/cc-0/O0/`と`O2/`に、各例の`.o`、実行用`.bin`、入力ID付きの
実行結果`.oracle.tsv`を保存します。`fixture`が検査対象の公開シンボルです。
`harness.o`と`helpers.o`は別に作り、LTOを無効にします。`call-chain.o`には`fixture_mix`への
外部参照が残るので、将来のcall命令や再配置の処理に使えます。

`manifest.json`には、コンパイラの実体パス・バージョン・ターゲット、コンパイルフラグ、
ソース・ヘッダ・入力・期待値と生成物のSHA-256、手書きIRとの対応、各生成物への相対パスを記録します。
正常終了したmanifestだけが`complete: true`になります。生成物はGit管理しません。

これは選択したコンパイラのnativeターゲット向けです。今回確認した環境は
GCC 13.3.0の`x86_64-linux-gnu`でした。現在のデコンパイラの機械語入力もこのx86-64を対象にしています。
`--cc`は複数回指定でき、ローカルにある別のコンパイラでも同じ入力・期待値で比較できます。
Clangはこの環境にないため未検証です。

```sh
python3 tools/build_fixtures.py --cc gcc --cc clang --opt O0 --opt O2
python3 tools/build_fixtures.py --opt O2 --sanitize --out target/c-fixtures-ubsan
```

UndefinedBehaviorSanitizerを使う2番目のコマンドも、この環境で全20例×63入力の1,260ケースを通過しています。
sanitizer付きのオブジェクトには追加の計装が入るため、通常のデコード用fixtureとは別ディレクトリに保存します。

生成道具自身はデコンパイラを呼びません。manifestの`decompiler_tested: false`は、この道具単独の検査範囲を表します。
デコンパイラを通す検査には、別途`cargo test --test machine_pipeline`を使います。
