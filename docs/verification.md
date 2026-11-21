# 検証ガイド

Nirvanaは、機械語・IR・生成Cを工程ごとに検査します。具体入力での実行比較と、定義したモデル全体の対応検査を組み合わせます。
観測する値・RAM・fault・外部効果・停止位置は[実行モデル](equivalence.md)を正本にします。

## 通常の検査

Rust stable、`cc`として呼べるC11コンパイラ、Python 3を使います。
一部の入力はGNU `gcc`・`readelf`・`strip`を使い、追加の差分検査は`sha256sum`を使います。

```sh
cargo test --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo fmt --all -- --check
python3 -m unittest discover -s tools/tests
```

10個の分野別suite、共有helper、ケースの追加方法は[テストガイド](../tests/README.md)にあります。
例えば`cargo test --locked --test codegen c_evaluation::`でCの評価順の比較だけを実行できます。
ソルバ・Clang・大きい生成比較は`#[ignore]`の任意テストです。

## 比較の境界

| 境界 | 主な検査 |
| --- | --- |
| 機械語→IR | 元Cまたは独立した実機assembly、命令境界、部分レジスタ、例外とメモリアクセス順 |
| IR→構造AST | 元IRとASTを個別にグラフ化し、命令・逐次代入・条件・移転先を照合 |
| SSA・保存先・φコピー | readごとの値対応、全先行辺、生存範囲と干渉、記号による並列代入の照合 |
| 算術・表示IR | 定義位置・値ID・算術の十分条件、削除候補の死活性、Load/Storeの位置と順序 |
| MemorySSA | byteに書込み元tagを置く独立した実行で候補maskを照合。部分Store、alias、φ、ループ、未知への拡大を含む |
| IR→再コンパイルC | 返り値・RAM・fault、モデルに応じた全レジスタ・PC・予算・外部結果の消費・途中再開 |

候補の構築器と検査器は個別に実行します。モデルと共有する実装、ソルバ、エンコーダは検査の信頼基盤です。
具体入力の一致はその入力の実行結果として記録し、SMTの結果はモデルと前提を添えて扱います。
[ソースの責務](architecture.md#ソースの配置)から各解析と検査器を参照できます。

純粋式の`pure-u64-v1`はSelectの両枝を含む文法を持ち、メモリ操作は`checked-memory-block-v1`で検査します。
ブロック検査は全到達境界の必要値・返り値・全メモリ・最初のfaultを比較し、入口関係の外にあるレジスタは左右独立に扱います。
fault時は正確なfaultと全メモリを比較します。SATモデルは小さい具体メモリで再実行し、UNSAT判定にはモデルの全メモリ領域を使います。

| 判定 | 意味 |
| --- | --- |
| `EquivalentUnderModel` | モデルの制約下で、差を示す問い合わせがUNSAT |
| `Counterexample` | SATモデルから得た差をIRで再現 |
| 未判定 | 時間・資源上限、対応構文、再現条件などを理由として記録 |

`--verify-reduction`は全到達ブロックで`EquivalentUnderModel`を得た還元を採用します。
各表示変換も自身の採用条件を検査し、退避経路を実行比較に含めます。
`ReadableC`は元IRと表示IRの構造証拠、web回復・定数伝播・式選択・領域復元の採否を保持します。
Cの型幅と描画は再コンパイル後の実行で確認します。

## Native Cと生成C

[fixtureガイド](../tests/fixtures/README.md)に入力・ABIとコンパイル条件をまとめています。
元Cは有効な引数で実行し、fixture ABIの返り値と4状態ワードを比較します。
IR間は全RAMのbyte列を、再コンパイルCとの比較は全RAMのdigestまたはbyte列を使います。
モデル付きCでは全レジスタ・fault・予算停止・途中PCへの再開も比較します。

共通のnative helperは、stdinの送信とstdout/stderrの回収を並行して行い、生成プログラムを期限付きで実行します。
コンパイラの同時起動はsuite内で4個までに制限しています。ケース固有のフラグ・状態形式は各比較器が指定します。

保存したCをUBSanで再検査する例:

```sh
NIRVANA_RECOVERY_ARTIFACTS=target/memory-recovery/generated cargo test --locked --test end_to_end generated_recovery::
python3 tools/validate_recovery_artifacts.py
```

`--inputs FILE`で空白区切りの4ワード行を指定できます。保存先のO0/O1/O2/Os/O3構成を検査します。
固定seedの追加比較はソース数1〜64（通常の生成比較は既定64、CFG比較は既定16）で、入力・ELF・C・フラグ・ハッシュを`target/generated-recovery/`へ保存します。

```sh
NIRVANA_RECOVERY_CASES=16 cargo test --locked --test end_to_end generated_recovery::seeded_pipeline_differential_campaign -- --ignored --exact
NIRVANA_RECOVERY_CASES=16 cargo test --locked --test end_to_end generated_recovery::seeded_control_flow_differential_campaign -- --ignored --exact
```

`NIRVANA_RECOVERY_PROFILES=O0,O1,O2,Os,O3`でprofileを選べます。既定はO0/O2です。
O0の基準実行を補完し、要求列と実効列をmanifestに記録します。各構成のlift成功が比較の前提です。

## 任意のZ3検査

開発用ソルバは[requirements](../tools/verification-requirements.txt)の`z3-solver==4.15.4.0`へ固定しています。

```sh
uv venv target/verification-venv
uv pip install --python target/verification-venv/bin/python -r tools/verification-requirements.txt
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --locked --all-targets -- --ignored --skip clang_ --test-threads=1
```

既存のZ3は`NIRVANA_Z3=/path/to/z3`で指定できます。上例は任意テストを直列実行します。
Clang比較は各fixtureのREADMEにあるコマンドで実行します。
[除算モデル](../tests/models/division_step.smt2.in)は8/16/32/64-bitの算術lemmaと反例を、[guarded dispatch](../tests/models/guarded_dispatch.smt2)は実target照合の有無による分岐選択の差を検査します。
適用範囲は各モデルの算術・分岐選択と停止済みprefixです。C全体とISAの対応は実行比較でも確認します。

問い合わせと採否を保存する例:

```sh
python3 tools/build_fixtures.py
cargo run --example verify_expressions -- --z3 target/verification-venv/bin/z3
cargo run --example verify_reductions -- --z3 target/verification-venv/bin/z3
cargo run --example verify_definition_webs -- target/c-fixtures/cc-0/O2/diamond.o
```

`verify_expressions`は式対のSMTとレポート、`verify_reductions`はブロック問い合わせと採否を保存します。
後者の終了コード0はレポート生成の成功を表し、候補の採否はレポートに含まれます。
`verify_definition_webs`はオブジェクトごとの改名候補と対応検査を表示します。

## 元変数との対応評価

[measure_source_recovery.py](../tools/measure_source_recovery.py)はGNU readelfを使い、非debug版と機械語が一致するGNU C O0/DWARF5コピーを参照します。
既知対応の分割・混在と新しい対応範囲を個別に集計し、曖昧な位置は未判定として記録します。

```sh
cargo build --example inspect_stack_frame --example measure_variables
python3 tools/measure_source_recovery.py --help
```
