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
[符号付き整数モデル](../tests/models/signed_integer.smt2)は、算術シフトの符号埋めと上位積の2の補数補正を、誤った変換の反例とともに検査します。
[符号拡張の検査](../tests/verification/unary_ops.rs)は、各幅の補正式と入れ子の拡張を実際のSMTエンコーダで照合し、誤ったゼロ拡張の反例をIRで再実行します。
同じsuiteで静的bit抽出の全開始位置と各幅を照合し、シフト数のmask・上位byteの位置・符号拡張を取り違えた反例も再実行します。
[word除算の検査](../tests/verification/word_signed.rs)は、整数モデルで商・剰余を、bit-vectorモデルで幅への射影・右シフトの分割を検査します。[GCC入力](../tests/fixtures/recovery/word-signed-reciprocal.c)は、32-bitの結果と64-bitへ拡張した戻り値をnative・IR・生成Cで比較します。
[全域商・剰余の検査](../tests/verification/division_ops.rs)は、符号の4通りを合わせて64-bit全入力の定義を照合し、除数ゼロ・±1と誤った変換の反例も検査します。8-bitの復元kernelは実際のIR演算との等式として照合します。
[word値グラフの検査](../tests/model/semantic_ir/word.rs)は、上位bitを失った分子、レジスタの上書き、符号境界を跨ぐループについて、元レジスタ・RAM・履歴・fault・予算を比較します。[GCC入力](../tests/fixtures/recovery/word-signed-memory.c)もnative・IR・生成Cで比較します。
[既知bitの検査](../tests/verification/known_bits.rs)は転送規則をSMTで、[dataflow検査](../tests/dataflow/known_bits.rs)は小領域の全列挙・64-bit境界・φとループの不変条件で確認します。設計の参考は[LLVM KnownBits](https://llvm.org/doxygen/structllvm_1_1KnownBits.html)で、Nirvanaの規則は全域の64-bit演算とmaskしたシフト数に対して検査します。
[メモリbitの補題](../tests/verification/memory_bits.rs)は成功した同幅Store/Load、別byteへの書込み、byteからwordの組立て、共通bitを持つ分岐を配列SMTで検査します。書込み候補の完全性と元のfault順はMemorySSAの検査・IR比較・C再実行で確認し、変更されたalias・幅・初期メモリの反例も含めます。
[保存値の検査](../tests/dataflow/memory_values.rs)はレジスタの上書き、分岐での保存、ループ内の再読込み、停止位置ごとの元レジスタ全体を比較します。[word射影の補題](../tests/verification/memory_values.rs)は保存時のmask・拡張幅をSMTで照合します。入口からの実行を対象に、追加したレジスタを射影した状態を比較し、実際の候補SSAで保存値の初期化も確認します。
[byte対応表の検査](../tests/verification/byte_memory.rs)は、実際のMemorySSAが出した候補を独立したSMT配列モデルと比較します。全幅の位置関係、曖昧なアドレス、φの変換を含みます。実行追跡では書込み元IDに加え、そのStoreのどのbyteが読まれたかも照合します。
[射影の合成則](../tests/verification/unary_ops.rs)は、静的抽出・mask・符号拡張から作った実際の還元候補を全域u64で照合します。[実行比較](../tests/transform/simplify.rs)ではLoadとlazy Selectを同じ式へ入れ、faultと状態を含めて確認します。
[bit挿入の検査](../tests/verification/bit_insert.rs)は全位置・幅の純粋式と、両operandのLoad・lazy Select・Storeの順序を持つブロックを照合します。未使用operandのfaultを落とした対照例もIRで再実行します。
[保存値のbyte復元](../tests/verification/memory_values.rs)は、実際の変換候補をchecked-memory-blockモデルで照合します。幅・位置の全contained組合せについて、正常終了時の元レジスタ境界と返り値、RAM、最初のfaultを検査します。一回だけ通るブロックの判定は、4頂点の全有向グラフで独立した到達可能性計算と照合します。ループ終了後の保存や、別レジスタでシフト・mask・Extractした値を分割保存する候補も、実際の変換をSMTで照合します。独立したbit出所検査器には、SSA値と位置を変えた候補も渡します。
[符号付き逆数除算モデル](../tests/models/signed_reciprocal.smt2.in)は、20種類の正負の除数について、整数上の上位積の正規化・範囲・商・剰余と、誤った係数の反例・最小負数の到達を検査します。
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

[保存式の検査](../tests/verification/memory_values.rs)は、加算・積・XOR・部分挿入・除算・条件式の実際の変換を、RAMと最初のfaultを含むSMTモデルで照合します。捕捉する式を変えた候補では反例を再実行します。別々のStoreの未知bitも区別し、捕捉後に利用する値を取り違えた内部planを検査します。

[lifterの切詰め検査](../src/binary/x86/lift/clipping_proofs.rs)は、実際の構築関数が作る式を従来のmaskとSMTで照合します。幅付きLoadとネストしたアドレス読込みも含め、幅の保持とfaultを確認します。機械語のbyte再読込みはnativeとも照合し、直接liftしたIRから保存値の対応を導けることを検査します。
