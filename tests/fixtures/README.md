# C fixtures

機械語へのコンパイルとnative実行の参照に使うC11ソースです。
元Cを実行結果の正本とし、自作デコーダから得たIRと、再コンパイルした生成Cを照合します。

## ファイル

| パス | 内容 |
| --- | --- |
| `cases/*.c` | 基本の分岐・ループ・演算・メモリアクセス |
| `cases.tsv` | fixture ID、手書きIRとの対応、特徴 |
| `recovery/*.c` | 幅、alias、添字、複数入口、途中脱出、変数の再利用 |
| `inputs.tsv` | IDと4個の入力状態ワード |
| `golden.tsv` | 手計算した返り値と最終状態の期待値 |
| `fixture.h` | 共通の関数宣言 |
| `harness.c` | 標準入力から状態を読み、返り値と最終状態を出力 |
| `helpers.c` | 外部呼出しを残すfixture用の別翻訳単位 |
| `value-lifetimes.c` | O0/O2のループ・分岐・関数呼出しを含む値追跡用の独立した実行ファイル |
| `value-swap.c` | O0/O2の変数の入替えと、機械語から局所変数Cへの復元 |

共通インターフェースは`uint64_t fixture(uint64_t state[4])`です。
演算はunsigned 64-bitの折返しを許し、添字とループ回数は小さな範囲に制限しています。
fixtureの特徴は元Cの分類です。最適化後の命令列とCFGは、各コンパイル結果から検査します。

## 実行検査

Rustと`cc`で呼べるC11コンパイラを使います。

```sh
cargo test --test native_c
cargo test --test machine_pipeline -- --nocapture
cargo test --test recovery_fixture -- --nocapture
```

`native_c`は元CのO0/O2と手計算の期待値、対応する手書きIRを比較します。
`machine_pipeline`はELFから得た機械語を入口にし、`recovery_fixture`は追加の回復例を検査します。
返り値と状態に加え、readable CとIRではゲストメモリ全体のdigestも照合します。
固定seedによる追加ソースの生成は[generated_recovery.rs](../generated_recovery.rs)にあります。

## オブジェクトと参照結果を保存する

```sh
python3 tools/build_fixtures.py --case diamond --opt O2
```

`target/c-fixtures/cc-0/O2/`に`.o`、実行ファイル、参照結果を保存します。
manifestにはコンパイラ、フラグ、入力と生成物のハッシュを記録します。
`--case`を省くと基本corpus全体、`--opt`を省くとO0/O2を生成します。
このツールはCのコンパイルと参照結果の保存を担当します。生成物は`target/`に保存します。

検証の範囲とSMT検査は[検証ガイド](../../docs/verification.md)を参照してください。
