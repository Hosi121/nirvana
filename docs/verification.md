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

## 制御構造の部分評価

M0の[構造評価器](../tools/evaluate_structure.py)は、元Cと生成CをClang 18の[debug.DumpCFG](https://clang.llvm.org/docs/analyzer/developer-docs/DebugChecks.html)で読み、制御の形を比較します。[初回corpus](../tools/corpora/structure-smoke.json)は既存4ソース族の開発集合です。GCC/Clang × O2/O3で16構成となります。

```sh
cargo build --locked --bin nirvana
python3 tools/evaluate_structure.py --clang clang-18 \
  --compiler gcc=cc --compiler clang=clang-18 --out target/structure-baseline
NIRVANA_CLANG=clang-18 python3 -m unittest discover -s tools/tests
```

入力のコンパイラと、生成Cを再コンパイルする`--c-compiler`（既定`cc`）を個別に固定します。元Cを各入力compilerで前処理し、そのCから作った機械語だけをNirvanaへ渡します。
出力先は空のディレクトリを使い、`report.json`と各入力の前処理C・object・生成C・生のCFG・正規化グラフ・コマンド記録を保存します。
compiler・実行ファイル・評価器・入力・グラフのhash、時間、探索予算を報告し、未対応・エラー・timeoutも要求した全構成に含めます。終了コード0は報告の生成を示します。

指標`nirvana-control-topology-v1`は、入口・出口・return・分岐・残るflowをラベルにした有向多重グラフを使います。式・名前・分岐の極性を捨て、明示的に剪定された辺と入口から届かないblockを除きます。出口は保持し、単一後続のflowを縮約します。自己循環は残します。関数内のdispatcherも同じ規則で比較します。
距離は入口・出口を対応させ、nodeの追加・削除・ラベル変更とedgeの追加・削除をそれぞれ1と数えます。`exact`と、探索予算で止まった`upper_bound`を区別し、下限・上限・対応表・停止理由を保存します。対応表は`control_graph.graph_from_json`と`mapping_cost`で再計算できます。

この指標は制御の形を観測します。基本block内の演算・効果・処理の複製と、意味の同値性は別の評価対象です。初回報告の意味比較は`semantics: not_run`、最大RSSは`null`で、hold-outと既存の意味比較を統合する部分もM0の残作業です。
[対照テスト](../tools/tests/test_control_graph.py)は名前変更の距離0、goto削減に伴う条件複製の距離悪化、小グラフの全ての部分対応との比較、打切り結果の対応表を検査します。

## 比較の境界

| 境界 | 主な検査 |
| --- | --- |
| 機械語→IR | 元Cまたは独立した実機assembly、命令境界、部分レジスタ、例外とメモリアクセス順 |
| Low IR→Middle IR | 元の式・命令・CFGの再構成、SSA版と値のscope、lazyな子領域とLoadの順序。直接MIR実行とLow IR実行の全状態・fault・停止予算を比較 |
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

[Middle IRの比較](../tests/model/middle_ir.rs)は、Store先の先行検査、選ばれた枝の読込み、部分的な書込み、φとループを含みます。検査器にはLoadの脱落・複製・並べ替え、scope外の値、誤ったSSA版を渡します。直接MIR実行器とLow IR実行器は、scalar演算とchecked memoryの基本処理を共有し、式と制御の評価を別々に実装しています。
[メモリ値の回復](../tests/model/middle_ir/memory.rs)は部分Store・may-alias・照会上限を含み、偽の既知値と循環した根拠を拒否します。回復前後のMIRと戻し変換の全状態を照合し、[生成C](../tests/model/middle_ir/memory_c.rs)はO0/O2・UBSanでRAMと最初のfaultを比較します。byteの一致判定はMemorySSAの書込み候補を前提とし、その候補解析は上表の独立実行比較で検査します。
[保存値の同一性](../tests/model/middle_ir/saved.rs)は、共通の保存値fixtureを使い、コピー・部分抽出・φ・ループ・上書きとsnapshotの初期化を検査します。通常のMIRは全状態を直接比較し、保存値を展開したLow IRは追加レジスタを除いて比較します。異なるφ入力、偽のslice、古いsnapshot、根拠を欠くreadを拒否し、[同じC比較](../tests/codegen/byte_values_backend.rs)で元の出力・保存値展開・候補選択を照合します。
[CLI比較](../tests/cli/middle_ir_cli.rs)はMiddle IR経由の生成Cと既存出力を照合します。保持したM0 smoke集合には次の任意比較を使えます。16構成すべてを要求し、全RAMをbyte単位で照合します。

```sh
NIRVANA_MIDDLE_OBJECTS=target/structure-baseline cargo test --locked --test model \
  middle_ir::fixtures::retained_m0_objects_keep_direct_middle_execution_and_exact_low_reconstruction \
  -- --ignored --exact --nocapture
```

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
[word除算の検査](../tests/verification/word_signed.rs)は、整数モデルで商・剰余を、bit-vectorモデルで幅への射影・右シフトの分割を検査します。[GCC入力](../tests/fixtures/recovery/word-signed-reciprocal.c)は、32-bitの結果と64-bitへ拡張した戻り値をnative・IR・生成Cで比較します。
[全域商・剰余の検査](../tests/verification/division_ops.rs)は、符号の4通りを合わせて64-bit全入力の定義を照合し、除数ゼロ・±1と誤った変換の反例も検査します。8-bitの復元kernelは実際のIR演算との等式として照合します。
[word値グラフの検査](../tests/model/semantic_ir/word.rs)は、上位bitを失った分子、レジスタの上書き、符号境界を跨ぐループについて、元レジスタ・RAM・履歴・fault・予算を比較します。[GCC入力](../tests/fixtures/recovery/word-signed-memory.c)もnative・IR・生成Cで比較します。
[既知bitの検査](../tests/verification/known_bits.rs)は転送規則をSMTで、[dataflow検査](../tests/dataflow/known_bits.rs)は小領域の全列挙・64-bit境界・φとループの不変条件で確認します。設計の参考は[LLVM KnownBits](https://llvm.org/doxygen/structllvm_1_1KnownBits.html)で、Nirvanaの規則は全域の64-bit演算とmaskしたシフト数に対して検査します。

| bit・保存値の検査 | 対象と照合方法 |
| --- | --- |
| [メモリbit](../tests/verification/memory_bits.rs)・[byte対応表](../tests/verification/byte_memory.rs) | 部分Store、alias、φの書込み候補を配列SMTと実行時の書込み元tagで照合 |
| [保存値と保存式](../tests/verification/memory_values.rs) | 幅・位置、分割Store、SSA定義、純粋な右辺から作った実際の候補について、返り値・元レジスタ・RAM・最初のfaultを検査 |
| [保存値の寿命](../tests/dataflow/memory_values.rs)・[不変条件](../src/dataflow/memory_values/stability.rs) | 停止予算ごとの実行比較、捕捉の初期化、循環と不変値の閉じた主張を検査。SMTは1〜4回に展開した反復経路を照合 |
| [保存値のφ合流](../tests/dataflow/memory_values/phis.rs)・[経路SMT](../tests/verification/memory_values/phis.rs) | copy・bit抽出・入れ子の合流・ループ戻り辺と、検査済み段階の合成を検査。還元前の復元は返り値・RAM・最初のfaultを照合。異なる射影・初期値・ゼロ拡張を失う主張を拒否し、SMTは分岐経路と0〜3回のループ経路を照合 |
| [射影](../tests/verification/unary_ops.rs)・[実行比較](../tests/transform/simplify.rs) | 全開始位置・幅と、mask・符号拡張を合成した候補を検査。Load・lazy Selectの状態とfaultも比較 |
| [bit挿入](../tests/verification/bit_insert.rs) | 全位置・幅の純粋式と、両operandのLoad・Store順序を検査 |
| [lifterの切詰め](../src/binary/x86/lift/clipping_proofs.rs)・[native比較](../tests/binary/x86.rs) | 実際の構築関数を従来のmaskと照合。幅付きLoad、ネストしたアドレス読込み、nativeとの比較を含む |

保存値の実行比較は入口から始め、追加レジスタを射影した元の状態を照合します。出所検査にはSSA値・位置・反復を取り違えた候補を渡し、SMTの反例もIRで再実行します。一回だけ通るブロックの判定は、4頂点の全有向グラフで独立した到達可能性計算と照合します。

[実GCCのstack alias比較](../tests/end_to_end/recovery_fixture/aliases.rs)は、入力領域をcalleeのstackへ重ね、還元前の保存値復元を元レジスタ・RAM・PC・停止予算で照合します。生成Cは同じ入力について全RAM・返り値・最初のfaultをUBSan付きで比較します。

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
