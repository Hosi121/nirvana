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

[M0評価ガイド](evaluation.md)に、固定corpus、native・IR・生成Cの観測、段階別検査、比較と再解析の手順をまとめています。

## 比較の境界

| 境界 | 主な検査 |
| --- | --- |
| 機械語→IR | 元Cまたは独立した実機assembly、命令境界、部分レジスタ、例外とメモリアクセス順 |
| Low IR→Middle IR | 元の式・命令・CFGの再構成、SSA版と値のscope、lazyな子領域とLoadの順序。直接MIR実行とLow IR実行の全状態・fault・停止予算を比較 |
| IR→構造AST | 元IRとASTを個別にグラフ化し、命令・逐次代入・条件・移転先を照合 |
| SSA・保存先・φコピー | readごとの値対応、全先行辺、生存範囲と干渉、記号による並列代入の照合 |
| 算術・表示IR | 定義位置・値ID・算術の十分条件、削除候補の死活性、Load/Storeの位置と順序 |
| MemorySSA | byteに書込み元tagを置く独立した実行で候補maskを照合。部分Store、alias、φ、ループ、未知への拡大を含む |
| C継続グラフ | 保存先とメモリviewの確定後、前後のASTから順序付きC断片と継続先を照合。メモリ条件の削除・アクセス幅の変更・効果の脱落や並替えを対照で拒否する。観測境界とprinterへの依存は[設計](architecture.md#c保存先確定後の継続処理)を参照 |
| IR→再コンパイルC | 返り値・RAM・fault、モデルに応じた全レジスタ・PC・予算・外部結果の消費・途中再開 |

候補の構築器と検査器は個別に実行します。モデルと共有する実装、ソルバ、エンコーダは検査の信頼基盤です。
具体入力の一致はその入力の実行結果として記録し、SMTの結果はモデルと前提を添えて扱います。
[ソースの責務](architecture.md#ソースの配置)から各解析と検査器を参照できます。

純粋式の`pure-u64-v1`はSelectの両枝を含む文法を持ち、メモリ操作は`checked-memory-block-v1`で検査します。
ブロック検査は全到達境界の必要値・返り値・全メモリ・最初のfaultを比較し、入口関係の外にあるレジスタは左右独立に扱います。
fault時は正確なfaultと全メモリを比較します。SATモデルは小さい具体メモリで再実行し、UNSAT判定にはモデルの全メモリ領域を使います。

[隣接Storeの順序検査](../tests/verification/store_order.rs)は、両範囲への先行Loadと非重複を前提に、純粋な二つのStoreを入れ替えて比較します。1/2/4/8-byte幅、任意の相対offsetと64-bit折返しを含む36問い合わせでUNSATを得ました。先行読込みの欠如、条件付き読込み、重複、右辺のLoad、アドレス変更、異なる入力のaliasでは、6件のSATを具体IR実行で再現します。生成Cでは[採用条件とfaultの比較](../tests/codegen/c_evaluation.rs)をO0/O2・メモリviewの有無で確認します。適用範囲はflat RWの単一関数Cで、moduleの権限・外部効果・途中再開は元の順序を保ちます。
同じモデルで、Storeが読むC保存先と独立な純粋更新の移動も照合します。加算・AND・OR・XORと1/2/4/8-byte幅の16問い合わせがUNSAT、格納値・アドレス・右辺Loadの依存を壊した3問い合わせが具体実行で再現するSATです。正常終了の全レジスタも比較します。生成器の依存は割当て後のC変数名で照合し、仮想レジスタが異なる同一保存先も[回帰検査](../tests/codegen/c_evaluation.rs)に含めます。

```sh
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --locked --test verification \
  store_order::successful_read_ranges_allow_disjoint_pure_store_permutations -- --ignored --exact
```

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
[snapshot統合の対照](../src/dataflow/memory_values/roots/tests.rs)は、bit境界、循環、偽のSSA事実、入れ子の根拠、入力変更を検査します。誤ったoffsetは拒否した上で、生成された候補が異なる返り値を出す反例も実行します。
[経路条件の対照](../src/dataflow/predicates/tests.rs)は、全流入辺の主張、異なるLoad・φ入力・再定義、booleanと一般のwordに対するXORを検査します。誤った分岐先は拒否した上で具体実行の差も確認します。元IR・変換後IR・再構築したMiddle IRの入口実行を、全レジスタ・RAM・fault・PC・予算について比較します。純粋式の値番号付けとscalar演算は検査器の共有する信頼基盤です。
[既知Loadから条件への接続](../tests/model/middle_ir/memory.rs)は、MIRの定数回復からCFG回復までを合成して比較します。[メモリを含む経路検査](../tests/verification/predicates.rs)は4幅のmasked Loadをchecked-memoryモデルで照合し、Loadを消した4候補のfault差を再現します。
[純粋DAGの経路検査](../tests/verification/predicates.rs)は、実際に採用された7計画をSSAや経路事実を使わずに記号実行します。`pure-dag-entry-prefix-v1`は、各予算の返り値・全レジスタ・PC・trace・停止状態を`pure-u64-v1`へ符号化します。51問い合わせのUNSATと、誤った移転先のSAT・実行による再現を検査します。対象は小さいload/store-freeなDAGです。M0の具体実行比較が、メモリを含む実バイナリ側の境界を補います。

```sh
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --locked --test verification \
  predicates::actual_predicate_plans -- --ignored --nocapture
```
[CLI比較](../tests/cli/middle_ir_cli.rs)はMiddle IR経由の生成Cと既存出力を照合します。保持したM0 smoke集合には次の任意比較を使えます。16構成すべてを要求し、全RAMをbyte単位で照合します。

[経路入力の検査](../tests/verification/path_inputs.rs)は、64-bitの折返し、部分書込みのalias、lazyなfault、ループの指定回数を含めてSAT入力を再実行します。UNSATは固定profileと指定した命令prefixに結びます。DAGの全prefix列挙は、全192個の小さい前向きProgramを、命令単位の経路oracleと照合します。[ツールの正負対照](../tools/tests/test_evaluation_witnesses.py)は、稀な分岐への入力追加、solver欠如・予算不足の未判定、正常returnに至らない候補の除外、debug objectの拒否を確認します。

```sh
NIRVANA_MIDDLE_OBJECTS=target/structure-baseline cargo test --locked --test model \
  middle_ir::fixtures::retained_m0_objects_keep_direct_middle_execution_and_exact_low_reconstruction \
  -- --ignored --exact --nocapture
```

## Native Cと生成C

[状態値のCモデル](../tools/evaluation/state_values/)は、Clang ASTをC局所変数のsnapshotと32個の状態byteへ対応付けます。[native対照](../tools/tests/test_state_value_ast.py)はcast・alias・条件・旧値の保存を実際のCと照合し、[SMT対照](../tools/tests/test_state_value_solver.py)は稀な分岐の反例を元C・生成Cで再現します。[保存結果の検査](../tools/tests/test_state_value_protocol.py)は、graph・query・solver出力をhashごと書き換えた場合や、ABI・数値型の変更も検出します。モデルはx86-64 LP64のC整数と既知helper契約を信頼基盤に含みます。[整数helperの対照](../tools/tests/test_state_value_helpers.py)は実際のC定義をO0/O2・UBSanで実行し、評価器・SMTと照合します。除数ゼロ、最小負数、語幅を超える64-bit除数、シフト数の折返しを含みます。変換・演算の境界は[C11草案 §6.3.1.3・§6.5](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)を参照します。

[SSE2レーンの検査](../tests/verification/vector_lanes.rs)は実際のdecode結果を、独立したbyte並替え・整数除算・減算と照合します。全256種のPSHUFD、シフトの境界、PADDQ、XMM→GPRの349問い合わせがUNSAT、シフト数64を誤ってmaskする対照がIRで再現するSATです。初期の全64 architecturalレジスタを任意値とし、privateな一時値を射影します。[native対照](../tests/binary/x86_vector.rs)は実機assemblyを使います。

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
[途中値の符号補正](../tests/verification/word_correction.rs)は、8/16/32-bit・正負66組について、全積の範囲・補正値の範囲・商・剰余の264問い合わせをUNSATで確認します。最小負数に必要な厳しい誤差条件を外す対照はSATとなり、IRで商43と正しい42の差を再現します。[実行対照](../tests/transform/word_signed_division.rs)は264種の補正・分配形を独立した整数演算と比較し、[意味IR](../tests/model/semantic_ir/word.rs)は入力の上書き・fault・途中予算を含めて元の全状態を検査します。定数除算の背景は[LLVMの実装](https://llvm.org/doxygen/DivisionByConstantInfo_8cpp_source.html)を参照してください。

C値モデルの除算抽象化は、[SMT-LIBのsigned演算の定義](https://smt-lib.org/logics-all.shtml#QF_BV)に沿い、任意のunsigned商関数と`n-q*d`から四つの符号ケースを照合します。[対照](../tools/tests/test_state_value_helpers.py)は8/16/32/64-bitの280問い合わせがUNSAT、byteの全65,536組は実際のC商・剰余と一致します。`NIRVANA_VALUE_PROOFS=DIR`で問い合わせを保存できます。抽象化だけのSATを[通常の式へ戻す検査](../tools/tests/test_state_value_solver.py)と、問い合わせ区分を含む[保存結果の検査](../tools/tests/test_state_value_protocol.py)も行います。
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
