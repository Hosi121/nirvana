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
| 選択したSemantic IR→実行IR | 実入力・計画・出力を保持した`Lowering`を再検査。入力の全レジスタ・RAM・fault・PC・traceを予算ごとに比較し、追加した捕捉レジスタだけを除く。入力・出力dumpと観測件数をM0へ記録 |
| IR→構造AST | 元IRとASTを個別にグラフ化し、命令・逐次代入・条件・移転先を照合 |
| SSA・保存先・φコピー | readごとの値対応、全先行辺、生存範囲と干渉、記号による並列代入の照合 |
| ループ入口の関係 | 元の初回到達と一巡後のDAGで純粋なレジスタ条件をSMT検査。初期値の誤りと、帰納条件の不成立を区別 |
| 選択したCのunsigned保存幅 | 実際の表示IRと幅証跡を保持して再検査し、局所変数の所属レジスタ・幅と生成Cのhashを対応付ける。[固定比較](../tools/corpora/ir-selected-storage-v1.m1.json)は開発用6構成、[条件付き上限](../tools/corpora/ir-guarded-storage-v1.m1.json)は比較時の値・全先行辺・入口条件を記録 |
| 選択したCのsigned保存表現 | 最終display IRとSSAを独立なi128演算で再検査し、全read/writeの符号拡張条件とlocalの全メンバを照合。[固定比較](../tools/corpora/ir-signed-storage-v1.m1.json)は既存推論・C本文・値モデルの証明を維持 |
| 算術・表示IR | 定義位置・値ID・算術の十分条件、削除候補の死活性、Load/Storeの位置と順序 |
| MemorySSA | 世代グラフと、各Loadの先行状態・全候補byteを覆う閉じた証跡を独立に検査。部分Store・alias・φ・ループ・未知への拡大をbyte tagと配列SMTでも照合 |
| C継続グラフ | 保存先とメモリviewの確定後、前後のASTから順序付きC断片と継続先を照合。メモリ条件の削除・アクセス幅の変更・効果の脱落や並替えを対照で拒否する。観測境界とprinterへの依存は[設計](architecture.md#c保存先確定後の継続処理)を参照 |
| IR→再コンパイルC | 返り値・RAM・fault、モデルに応じた全レジスタ・PC・予算・外部結果の消費・途中再開 |

候補の構築器と検査器は個別に実行します。モデルと共有する実装、ソルバ、エンコーダは検査の信頼基盤です。
具体入力の一致はその入力の実行結果として記録し、SMTの結果はモデルと前提を添えて扱います。
[ソースの責務](architecture.md#ソースの配置)から各解析と検査器を参照できます。

純粋式の`pure-u64-v1`はSelectの両枝を含む文法を持ち、メモリ操作は`checked-memory-block-v1`で検査します。
ブロック検査は全到達境界の必要値・返り値・全メモリ・最初のfaultを比較し、入口関係の外にあるレジスタは左右独立に扱います。
fault時は正確なfaultと全メモリを比較します。SATモデルは小さい具体メモリで再実行し、UNSAT判定にはモデルの全メモリ領域を使います。

`checked-memory-dag-region-v1`は、[閉じたDAG領域](../src/verification/block_verify/region.rs)の入口からReturnまでを比較します。正常時の必要レジスタは呼出し側が指定し、共有しない初期値は左右独立です。全RAM・最初のfaultと、各経路の完了も問い合わせへ含めます。上限は128レジスタ・128命令・式深さ128で、source全体を検査してからcloneします。SATは最大64KiBの具体RAMで再生し、その範囲に反例がない場合は`ReplayLimit`へ戻します。

`query_at_returns`は、正常な終了タグごとに比較するレジスタを指定します。未指定のタグでは共通する全レジスタを比較し、返り値・全RAM・最初のfaultは全経路で観測します。反例のRust再生も実際の終了タグから同じ観測を選びます。既存の一律比較と分け、`checked-memory-dag-return-outputs-v1`として記録します。

問い合わせは出口別、または任意の入力ワードの下位1〜4bitで分割できます。各式は元の反例条件へguardだけを追加し、全分割のUNSATから同じ契約の等価性を判定します。正常・fault・未指定タグの被覆と全64-bit入力の被覆を、Rustが生成したguardのSMT照合で確認します。ケースを一つ欠いた対照はSATになります。合計30秒までの共通予算をsolverと反例抽出へ配分し、途中の未判定は全体の未判定として保持します。入力の分割を`with_input`で直積にし、`with_return_partitions`で終了状態と組み合わせられます。上限は256ケースです。

[継続先の生存値](../src/verification/block_verify/region/extraction/live_out.rs)は、各継続先を任意入力の入口としてSSAと生存解析を作り直します。元の入口から未到達のblockも対象に含め、元Programと終了タグの対応を保持します。独立した命令・式の走査が、除外した値の書換え前のreadを全経路で検査します。実際の関数返り値を捕捉するスロットも各行に残します。上限は16継続先と検査work 800万で、超過時は候補全体を保留します。

[入口条件の帰納検査](../src/verification/block_verify/region/invariants.rs)は、レジスタ代入の固定点を条件とし、元の初回到達と次の入口までの経路を検査します。
代入は条件を満たす状態では恒等写像になるため、一巡の検査はその全状態を覆います。独立したIR検査が、元の射影・純粋な仮定・観測markerの追加と共有入力を照合します。
二つの問い合わせがUNSATなら、同じソース・入口に結び付いた証跡からbit上限を取り出せます。戻り辺の反例は仮定が許す局所状態の反例で、関数入口からの到達可能性とは分けます。反復全体の停止は別の検査対象です。

[入口条件の候補生成](../src/transform/loop_entry_facts.rs)は、元SSAから単位増分の戻り辺、上限値の区間、laneの剰余maskを拾います。値の区間は候補生成だけに使い、帰納検査を通した証跡を領域の入口へ渡します。入口上限のヒントだけで再編した候補は、元の広い入力契約を保持します。
[復元の接続](../src/transform/loop_recovery.rs)は最初の検証済み候補を確保し、その後にlaneの拡張を試します。追加検査は描画開始から10秒の残り時間内で、入口条件に最大3秒、拡張候補の完了・同値検査に共通で最大5秒を使います。先行する基準候補の検査は従来の予算を使います。追加検査の不成立・予算切れでは検証済み候補を返し、`EntryAttempt`へ段階と時間を記録します。

[反復の式パターン](../src/dataflow/lane_patterns.rs)は、元SSAのcopyと自明なφをたどり、load・accumulator更新・storeの組を自動で照合します。3組以上で同じ間隔に変わるリテラル位置をパラメータとし、他の位置で同じ値を取るリテラルを保持します。loadは元の捕捉位置を持つ値として扱います。この段階の成果物は式の復元候補であり、制御フロー・効果順序・aliasを含む採用判断には領域の検証を使います。探索には1,024命令・64組・65,536式node・work 200万の上限を設けています。

[自動反復候補](../src/transform/rolled_loop.rs)は、単一ラッチ、3〜8個の等間隔lane、反復に対して不変の更新式・Store先を持つ領域から構築します。分岐と更新の実行順序を元の1反復から引き継ぎ、添字・脱出時の更新・反復上限を候補へ写します。関数のReturnは切出しの継続先として扱います。sourceは125レジスタ・128命令まで、比較DAGは従来の128レジスタ・128命令までを対象にします。

`Proposal::verification_problem()`は、solver実行前に完了式・比較式・分割条件を取り出せます。`composition_problem()`は、元SSAの式、反復上限、私有カウンタの値から区間ごとの対応・事後条件を構築します。入口の式は純粋なレジスタ等式で、最初の入口は元の共有入力をそのまま使います。事後条件が次の入口の式を保証し、対応検査が出口と共有値を保証します。各問い合わせは全RAM・最初のfaultと元の正常出口の観測を保持します。上限は16区間、各式4MiB、全式16MiBです。

`VerificationProblem::check()`は完了検査に5秒まで、区間合成・従来の分割比較・反例抽出に共通15秒を使います。受理結果は`EquivalenceProof`で証明経路を保持します。局所の不成立後は残り予算で元の全体比較を行い、変換の反例を両方の循環CFGで再生します。未判定と反復数不足は個別に記録します。

[区間合成のcheckpoint](../tools/corpora/compositional-roll-v1.m2.json)では、保存済みClang objectの12証明義務と完了検査が通り、元の領域契約で候補を受理しました。同じ候補Cについて325入力・O0/O2計650実行の全RAM・返り値・fault比較も一致します。3,072構成の生成Program監査は、受理512件、誤った入口条件による保留512件、意味改変の反例再生2,048件を、旧エンコーダの全体比較と照合しています。通常CLIは現行の描画方針を使います。

保存したSMTは[再現ツール](../tools/replay_loop_checkpoint.py)で検査できます。objectをcheckpointから復元するため、Clangは不要です。`--rust`はソースhashを確認し、証明の再構築・生成C比較・全artifactの一致まで検査します。`--flat`は従来の全体比較を別の結果として記録します。
関数への適用と元の引数番号を含む[checkpoint](../tools/corpora/contextual-loop-v1.m2.json)から、[入口条件を証明するcheckpoint](../tools/corpora/inductive-loop-v1.m2.json)へ進みました。実Clang入力で先頭を含む4laneを復元し、入口2問・完了検査・15個の局所証明を通しています。同じM0入力で構造距離は前回の16から4へ下がり、局所変数9個を維持しました。Rustの再構築にはcheckpointの`source_sha256`に一致するソースを使います。

```sh
NIRVANA_Z3=/path/to/z3 python3 tools/dev.py run -- \
  python3 tools/replay_loop_checkpoint.py --out '{out}' \
  --checkpoint tools/corpora/inductive-loop-v1.m2.json --rust --flat
```

[固定checkpoint](../tools/corpora/ir-dag-regions-v1.m1.json)は、任意のRAMと整数入力を持つ8組の同値判定、7組の反例再生、再生上限の対照1組を記録しています。検証プロファイルはsolver呼出しごとに5秒です。APIは渡されたsolver予算を使い、2秒で未判定となった結果もcheckpointへ残しています。 複数のSMT検査をまとめる固定profileは`--test-threads=1`で実行し、並列実行で5秒の未判定となった記録も保持します。自動候補の受理では、この領域検査と反復の完了検査を使います。

[領域の切り出し](../src/verification/block_verify/region/extraction.rs)は、指定した入口から継続先へ達するまでをDAGに写します。元のレジスタ空間と逐次効果を保持し、実際の関数返り値と継続先を別に記録します。検査器は元CFGをblock単位で歩き直し、命令の被覆、分岐の両腕、Return式、追加prefixと終了タグを照合します。任意の入口値を使う形式と、同じ元Programで検査した`ValueWidths`のbit上限をprefixへ反映する形式を選べます。後者の契約は、その入口上限を満たす元の状態です。

[実コンパイラ入力の任意実行テスト](../tests/verification/region_extraction.rs)は、開発用の入れ子ループobjectを読み、元IRの到達状態と不正アドレスについて、全元レジスタ・全RAM・最初のfault・継続先または実際の返り値を比較します。`NIRVANA_REGION_OBJECT`にobject、`NIRVANA_REGION_OUTPUT`に短期出力先、`NIRVANA_Z3`にsolverを指定し、`python3 tools/dev.py cargo test --test verification actual_compiler_region_extraction_probe -- --ignored --nocapture`で実行します。SMT自己比較はエンコーダの確認として記録します。切り出しの意味保存は投影検査と具体比較で確認し、循環候補の[完了検査](../src/verification/block_verify/region/extraction/repeat.rs)は、この投影の入口へ戻る継続先だけを有限回接続します。最後の戻り辺に専用の打切り印を置き、そこへ到達できないとSMTで判定された場合に`Complete`を作ります。回数不足の反例は元の循環IRでも再生し、solverや再生の上限は未判定へ戻します。契約の終点は、戻り辺以外の継続先・実際のReturn・最初のfaultです。

[完了検査の対照](../src/verification/block_verify/region/extraction/repeat/tests.rs)は、任意の64bit counterと検査済み2bit上限で、0・1・3回の不足、4・5回の完了を確認します。入口上限を外すと4回でも不足します。別に作った4段の展開IRと証明済み循環候補を全RAM・正常時の必要値まで比較し、増分を壊した候補の差を両方の循環IRで再生します。自動的な復元候補は、この完了検査を受理条件に持ちます。

`Prefixed`は実際の入口prefixと反復領域を接続し、初期化・分岐・メモリ効果も完了検査へ含めます。両者を同じ元Programと終了タグへ結び、反復側は任意の入口値を受け入れます。これにより、反復途中の値域へ初期状態を丸めずに`j = 1`・`limit > 0`などの入口の関係を利用できます。等値比較で抜ける対照では、検査済み2bit上限だけの場合の回数不足と、prefixから3反復で完了する場合を区別し、不足時は元のprefixから再生します。


[レジスタ番号の投影](../src/verification/block_verify/region/registers.rs)は、疎な表示IRから命令に現れるレジスタだけを詰め、番号の対応を式・逐次代入・制御から独立に検査します。使われない元のレジスタは正確な入口状態から復元でき、全レジスタ・PC・trace・RAM・fault・命令予算の観測を保ちます。sourceの番号空間は最大65,536、問い合わせ側は既存の128レジスタ上限です。異なるIRの比較には`compact_comparison`を使い、共有入力と必要な終了値を含む共通の対応表を作ります。最初の形式は同じ元レジスタ空間の二つのProgramを扱います。

実Clangの選択済み表示IRで740→38レジスタを確認し、5,764件の全状態比較と反復領域590件を照合しました。保存済みのM0入力とのhashも一致しています。 [チェックポイント](../tools/corpora/ir-region-feedback-v1.m1.json)に、全体検査と32+2構成の比較を固定しています。投影後のProgramで値域を解析・検査し直してから領域を切り出すため、元の番号空間の証跡を取り違えずに利用できます。SMT自己比較は問い合わせへの入力確認であり、ソースから生成Cまでの全体証明とは別の観測です。



```sh
NIRVANA_Z3=/path/to/z3 NIRVANA_REGION_SECONDS=5 python3 tools/dev.py cargo test --lib \
  memory_regions_cover_unrolling_aliases_faults_exits_and_join_constants -- --ignored --nocapture
```

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
[アドレスclassの対照](../src/dataflow/address_identity/verify/tests.rs)は、異なる初期値・Load・opaque出力の結合、欠けたφ入力、循環した根拠、利用前の代表値、反復で変わる値を拒否します。省略した同一性と恒等写像を許し、SSAの番号を変えても利用可能な代表値を受理することを確認します。
[メモリ値の回復](../tests/model/middle_ir/memory.rs)は部分Store・may-alias・照会上限を含み、偽の既知値と循環した根拠を拒否します。回復前後のMIRと戻し変換の全状態を照合し、[生成C](../tests/model/middle_ir/memory_c.rs)はO0/O2・UBSanでRAMと最初のfaultを比較します。byteの一致判定はMemorySSAの書込み候補を前提とし、その候補解析は閉じた被覆証跡と独立実行比較で検査します。アドレス恒等式は[sourceの係数とアクセス位置の検査](../src/dataflow/address_identity/modular_verify.rs)を通します。[改変対照](../src/dataflow/address_identity/modular_verify/tests.rs)は欠けた項・offset・符号・shift・φ入力と、相殺したsource atomを含みます。byteの区間判定と列挙した等式の対応は、任意の64-bit offsetを持つモデルでSMT照合し、境界とsource位置を誤るモデルをSATと実行で確認します。

[unsigned幅の検査](../src/dataflow/type_infer/bounds_verify.rs)は、型解析の幅計算を共有せず、元の式を数値上限で照合します。[対照](../src/dataflow/type_infer/bounds_verify/tests.rs)では除数ゼロ・最小負数・signed剰余・bit hullと静的な抽出位置を実際のIR実行で確認し、入口・φ・逐次readの改変を拒否します。検査済みの性質はu64整数の上限で、元Cの宣言型との対応は型回復の評価で扱います。
[moduleの投影検査](../src/dataflow/module_values/memory_verify.rs)は、元命令・解析イベント・opaque効果・出力レジスタの対応を検査します。対照ではCALL/REPの効果の削除・位相の変更・誤った読取り・閉じた呼出しの出力差を拒否します。DIVの未知出力を定数placeholderとして使う候補も拒否し、MemorySSAの記号アドレスへ数値の事実が混入する経路を検査します。

[閉じた呼出しの検査](../src/dataflow/call_footprint/verify.rs)は、要約を使う前に元moduleの正常継続経路と照合します。[改変対照](../tests/dataflow/call_footprint.rs)ではread・clobber・calleeの欠落、戻り先を壊すStore、RSPを変える入口backedge、DIV/call後の古いアドレス、再帰calleeの効果の脱落を拒否します。書込みの検査は同一命令内の代入順とvectorの全幅を保ちます。正常復帰後の保存値と未読レジスタの非干渉は、[実際のmodule実行](../tests/model/call_preservation.rs)でも比較します。スタック候補は[独立した入口・辺・アクセスの検査](../src/dataflow/stack/verify.rs)を通し、要約は有限の正常復帰を適用条件とします。[スタックの改変対照](../src/dataflow/stack/verify/tests.rs)は入口backedge、両分岐、代入順、offset、アクセスの幅・重複を壊した候補と、安全に未知へ弱めた候補を含みます。

[M1の部分checkpoint](../tools/corpora/closed-calls-v1.m1.json)には、同じ27関数のELFでの解析・C出力の比較、9個の閉じた要約の検査件数、改変対照と実行テスト、source版と成果物hashを記録しています。生データは容量管理付きの短期保存です。
[アフィン式と幅のcheckpoint](../tools/corpora/ir-affine-v1.m1.json)は、このELFの解析・C出力を保ち、スタック354点の根拠を加えています。M0の同じGCC/Clang O2の4構成では、36アクセス・136アフィン等式と681個のSSA値の上限を検査し、native・生成C・IRの観測を維持しました。Cの保存幅の解析は、型制約のunsigned上限と別に扱います。

[条件付きの保存幅](../src/dataflow/value_width/verify/edge_bounds.rs)は、元の逐次代入から比較時の値を後方参照し、分岐後も同じ値を持つレジスタだけへ上限を適用します。入口は任意u64、比較後の上書き・blockを越えた古い条件・未知の高32bitは区別します。[SMT検査](../tests/verification/edge_storage.rs)は実際の推論結果に対する80件の全u64問い合わせと、狭すぎる76件の反例再生を記録しています。保存幅の証跡と、生成C全体の同値性はそれぞれの境界で評価します。
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
[途中値の符号補正](../tests/verification/word_correction.rs)は、8/16/32-bit・正負66組について、全積・補正値の範囲、商・剰余、結果の符号拡張の330問い合わせをUNSATで確認します。別の3問い合わせは、認証対象の全除数を変数として商・剰余の範囲を検査します。最小負数に必要な厳しい誤差条件を外す対照はSATとなり、IRで商43と正しい42の差を再現します。[実行対照](../tests/transform/word_signed_division.rs)は264種の補正・分配形を独立した整数演算と比較し、[意味IR](../tests/model/semantic_ir/word.rs)は入力の上書き・fault・途中予算を含めて元の全状態を検査します。定数除算の背景は[LLVMの実装](https://llvm.org/doxygen/DivisionByConstantInfo_8cpp_source.html)を参照してください。

signed wordへのC変換は、実際のhelperの式をClangで読み、全64-bit入力について返り値とcast・減算のdefinednessを[3問い合わせで照合](../tools/tests/test_state_value_solver.py)します。通常のC演算子で出す商・剰余と、境界helperへ残すゼロ・±1・大きい除数は、同じnativeハーネスでO0/O2・UBSan比較します。

[signed保存範囲](../tests/verification/signed_width.rs)は、bit演算・算術シフト・Select・抽出の41問い合わせをUNSATで確認し、zero-extensionを同じ幅のsigned値と誤認した3対照のSATをIRで再現します。[SSAの検査](../tests/dataflow/signed_width.rs)は入口の未知値、ループphi、コピー後の上書き、資源上限を含みます。[Cの比較](../tests/codegen/typed_locals.rs)は、負数のunsigned比較・論理シフト、wrap、unsigned値への上書き、遅延LoadをO0/O2・UBSanで実行し、返り値・全RAM・最初のfaultを照合します。

C値モデルの除算抽象化は、[SMT-LIBのsigned演算の定義](https://smt-lib.org/logics-all.shtml#QF_BV)に沿い、任意のunsigned商関数と`n-q*d`から四つの符号ケースを照合します。[対照](../tools/tests/test_state_value_helpers.py)は8/16/32/64-bitの280問い合わせがUNSAT、byteの全65,536組は実際のC商・剰余と一致します。`NIRVANA_VALUE_PROOFS=DIR`で問い合わせを保存できます。抽象化だけのSATを[通常の式へ戻す検査](../tools/tests/test_state_value_solver.py)と、問い合わせ区分を含む[保存結果の検査](../tools/tests/test_state_value_protocol.py)も行います。
[全域商・剰余の検査](../tests/verification/division_ops.rs)は、符号の4通りを合わせて64-bit全入力の定義を照合し、除数ゼロ・±1と誤った変換の反例も検査します。8-bitの復元kernelは実際のIR演算との等式として照合します。
[word値グラフの検査](../tests/model/semantic_ir/word.rs)は、上位bitを失った分子、レジスタの上書き、符号境界を跨ぐループについて、元レジスタ・RAM・履歴・fault・予算を比較します。[GCC入力](../tests/fixtures/recovery/word-signed-memory.c)もnative・IR・生成Cで比較します。
[既知bitの検査](../tests/verification/known_bits.rs)は転送規則をSMTで、[dataflow検査](../tests/dataflow/known_bits.rs)は小領域の全列挙・64-bit境界・φとループの不変条件で確認します。設計の参考は[LLVM KnownBits](https://llvm.org/doxygen/structllvm_1_1KnownBits.html)で、Nirvanaの規則は全域の64-bit演算とmaskしたシフト数に対して検査します。
[数値検査のcheckpoint](../tools/corpora/ir-known-bits-v1.m1.json)には、加減算prefixの128式とbit演算・射影・合流などの101式を、全maskと64-bit値に対してSMTで確認した結果も保存します。式と実Rust演算核の対応は有限のbridgeテストで確認し、数式の保証と実装の検証範囲を分けて記録します。

| bit・保存値の検査 | 対象と照合方法 |
| --- | --- |
| [メモリbit](../tests/verification/memory_bits.rs)・[byte対応表](../tests/verification/byte_memory.rs) | 部分Store、alias、φの書込み候補を配列SMTと実行時の書込み元tagで照合 |
| [保存値と保存式](../tests/verification/memory_values.rs) | 幅・位置、分割Store、SSA定義、純粋な右辺から作った実際の候補について、返り値・元レジスタ・RAM・最初のfaultを検査 |
| [保存値の寿命](../tests/dataflow/memory_values.rs)・[不変条件](../src/dataflow/memory_values/stability.rs) | 停止予算ごとの実行比較、捕捉の初期化、循環と不変値の閉じた主張を検査。SMTは1〜4回に展開した反復経路を照合 |
| [保存値のφ合流](../tests/dataflow/memory_values/phis.rs)・[経路SMT](../tests/verification/memory_values/phis.rs) | copy・bit抽出・入れ子の合流・ループ戻り辺と、検査済み段階の合成を検査。還元前の復元は返り値・RAM・最初のfaultを照合。異なる射影・初期値・ゼロ拡張を失う主張を拒否し、SMTは分岐経路と0〜3回のループ経路を照合 |
| [射影](../tests/verification/unary_ops.rs)・[実行比較](../tests/transform/simplify.rs) | 全開始位置・幅と、mask・符号拡張を合成した候補を検査。Load・lazy Selectの状態とfaultも比較 |
| [語幅内の算術整理](../tests/verification/unary_ops.rs) | 8/16/32-bitの実際の簡約243件を全u64入力で照合。右シフト・上位積・除算・比較・狭い符号埋めを越える誤変換17件はSATをIRで再現。描画段階で認識済みの意味演算を保持する |
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

[保存先IRへの下ろし変換](../src/transform/allocated_storage.rs)は、`allocation_verify`で元Programと色分けを検査してから、パラメータと分離した新しいbankへ写します。色が異なる保存先の分離、同じ色の共有、命令・式・幅・逐次順序の対応も検査します。新しいbankの初期値は任意で、初期値を読む割当ては拒否されます。[通常テスト](../src/transform/allocated_storage/tests.rs)は、先行Storeを残したLoad fault、lazy Select、全PC・予算、色の衝突や出力IRの改変を確認します。実Clangの最終表示IRでは35レジスタを9bankへ写し、番号投影後は12レジスタとなりました。5,569件の返り値・全RAM・最初のfault・PC・trace・予算比較を行い、全元レジスタの最終値を比較する番号投影の契約と分けて記録します。 [チェックポイント](../tools/corpora/ir-entry-storage-v1.m1.json)に全体検査・同じ32+2構成の比較と、別の検査済み13レジスタ版の具体IRを保存しています。

## 元変数との対応評価

[measure_source_recovery.py](../tools/measure_source_recovery.py)はGNU readelfを使い、非debug版と機械語が一致するGNU C O0/DWARF5コピーを参照します。
既知対応の分割・混在と新しい対応範囲を個別に集計し、曖昧な位置は未判定として記録します。

```sh
cargo build --example inspect_stack_frame --example measure_variables
python3 tools/measure_source_recovery.py --help
```

## Quint・TLA+による構造対応の検査

M2の受理済み候補をQuintの独立モデルで監査する。正本は[実行契約](equivalence.md)と[層間契約](architecture.md)。[最初の実行可能モデル](../models/README.md)は、共有末尾・外側continue・同一後続への条件評価について、手書きASTと実回復ASTの計6組を扱う。命令予算0〜6でTLCの有限状態探索を行い、改変した候補と実Rustでの再生を別のゲートにする。版・入力hash・反例は[checkpoint](../tools/corpora/structured-events-v1.m2.json)へ保存する。

| 対象 | 最初に確かめること |
| --- | --- |
| CFG → Structured AST | 実Rustが受理した組のStep・評価・Return・外側transfer・予算境界が、独立した実行で対応するか |
| MemorySSAの候補被覆 | 成功したLoadの各byteについて、最後にcommitしたwriterとStore内のbyte位置が受理済み候補に含まれるか |
| 反例の再生 | 抽象traceを具体化し、実Rustの受理結果と完全なRunReportを別々に照合できるか |

最初は実Rustの[`structure_verify::validate`](../src/control_flow/structure_verify.rs)を完走させ、候補ごとの受理・通常拒否・資源上限・export対象外を保存する。検査器はStepのPC・逐次代入列・条件・Return式を構文で比較し、分岐の両腕を調べる。この性質に合わせ、sourceをPC、ASTをraw構文cursorとlexical stackで実行するeventモデルから始める。`Step(pc, ordered_body)`・`Eval(condition)`・`Return(expression)`のtokenを先に照合し、対応したイベントへ共通の非決定的な成功・枝・faultを与える。不一致は明示的なエラーへ進める。tokenの忠実性と共通の決定的な命令意味論を前提に、有限の制御構造を値域によらず監査する設計である。

sourceには`Ready → ControlPending → Ready`の位相を置く。残り予算が0でも、最後のStepの代入・条件・Returnは完了し、次Stepの試行時にSuspendedとなる。その試行PCは`instruction`へ入り、traceへの追加は止まる。モデルは約6 PC・2段loop・命令予算0〜6から始め、node数・コピー数・stackにも上限を置く。guest Step間のEvaluate/Ifも含む全遷移を進捗検査へ数え、有限configurationの再訪を調べる。任意の小さいwatchdog到達は未判定、stack等のoverflowはエラーとする。探索上限とguest予算を別に記録する。

Quintの[言語仕様](https://quint.sh/docs/language-basics)に合わせ、構文は有限ID表と明示的なstackへ写す。eventモデルは式の意味を共通の前提に置く。後続の2reg・2-byte RAMの具体モデルでは、Storeの宛先評価→全幅検査→右辺評価→commit、先行Storeの保持、Selectの選択枝だけの評価も独立に検査する。

非空の正対照には共有tail・外側continue・同一後続へのfault可能な条件を使う。独立実行器へStep欠落・枝交換・transfer深さ変更・Eval削除・control前の予算停止を入れ、負対照の検出も確認する。[既存の構造改変対照](../tests/control_flow/structure_verification.rs)と[prefix比較](../tests/control_flow/structure_splitting.rs)を出発点にする。モデル側のIR/AST実行は、検査対象のFlowGraph loweringから独立させる。

初回の[テスト用adapter](../src/control_flow/structure/model_trial_tests.rs)は、raw ASTを実際の[`execute_nodes`](../src/control_flow/structure.rs)で実行する。具体的な観測cutでは、元IRの[`run_with_memory`](../src/model/ir.rs)とstatus・全register・RAM/base/layout・trace・instructionを直接比較する。[`Contract::compare`](../src/model/observe.rs)は途中停止を未判定とする最終状態向けの契約である。全Stepコピー・途中再開の検査は`validate_reentries`を別のゲートにする。抽象的な枝列には実入力で再現できないものも含まれるため、初回は各改変ASTの具体的な差をRustで確認し、TLC traceの自動具体化を次の接続点にする。

MemorySSAでは、Initial・Storeの静的位置とsource byte・Opaqueを具体writerとし、φは先行辺を選ぶ操作として扱う。opaqueのMay writeが何も書かない場合や部分書込みでも、[現在の検査器](../src/dataflow/memory_ssa/verify/queries.rs)は以前のwriterを覆う義務を保持する。`unknown_bytes`もこの被覆を保つ。初回は1 PCに1アクセス・root Load・一意なbyte tagへ絞り、元IRのprefix実行で前向きのwriterと比較する。raw証跡の注入にはprivateなAnalysis用adapterが必要で、query生成器による補修を介さず検査する。実CALL/REPのopaqueとの対応は、効果付きの内部検査と[`module_values::memory_verify`](../src/dataflow/module_values/memory_verify.rs)を別に照合する。照会の未取得・予算到達は未判定として残す。

Quintは[ランダム探索・有界検査・帰納不変条件](https://quint.sh/docs/checking-properties)と[TLC backend](https://quint.sh/docs/model-checkers)を使い分けられる。TLCの完走は指定した有限モデルの到達状態を覆う。演算の全域検査には既存SMTを使い、構造品質はM0の同条件比較へ結ぶ。[Quint Connect](https://github.com/quint-co/quint-connect)もtrace再生の候補である。モデル検査、Rustの受理結果との適合、具体実行の再生を分けて報告し、exporter・adapter・式やメモリの意味論・有限集合の範囲を信頼境界へ残す。
