# M0 Evaluation

M0の[構造評価器](../tools/evaluate_structure.py)は、元Cと生成CをClang 18の[debug.DumpCFG](https://clang.llvm.org/docs/analyzer/developer-docs/DebugChecks.html)で読み、制御の形を比較します。[初回corpus](../tools/corpora/structure-initial-v1.json)は開発用4ソース族とhold-outの2ソース族を分け、GCC/Clang × O2/O3の24構成へ固定しています。[追加の整数corpus](../tools/corpora/structure-integer-v1.json)は、狭いsigned演算、反復中の添字とalias、ベクトル化の3族・12構成を開発用として保持します。従来の[16構成のsmoke集合](../tools/corpora/structure-smoke.json)も個別の比較に使えます。

```sh
python3 tools/dev.py cargo build --locked --bin nirvana --example evaluation_probe
python3 tools/dev.py run --keep -- python3 tools/evaluate_structure.py --cases tools/corpora/structure-initial-v1.json \
  --clang clang-18 --compiler gcc=cc --compiler clang18=clang-18 \
  --semantic-probe target/debug/examples/evaluation_probe --c-footprint --measure-rss \
  --out '{out}'
NIRVANA_CLANG=clang-18 python3 -m unittest discover -s tools/tests
```

入力のコンパイラと、生成Cを再コンパイルする`--c-compiler`（既定`cc`）を個別に固定します。元Cを各入力compilerで前処理し、そのCから作った機械語だけをNirvanaへ渡します。
出力先は空のディレクトリを使い、`report.json`と各入力の前処理C・object・生成C・生のCFG・正規化グラフ・コマンド記録を保存します。
`nirvana --version`とprobeの`--version`は、ビルド時のcommitとRust入力の変更有無を返します。Git情報のないアーカイブはunknownです。報告の`workspace_revision`は評価器のcheckout、`decompiler.build`はbinaryが返した出所で、binaryのSHA256を別に保持します。比較形式v2も`evaluation_revision`と`binary_build`を分け、凍結した旧binaryの版を評価器の版から推測せずに残します。
compiler・実行ファイル・評価器・入力・グラフのhash、時間、探索予算を報告し、未対応・エラー・timeoutも要求した全構成に含めます。終了コード0は報告の生成を示します。

## 観測と指標

指標`nirvana-control-topology-v1`は、入口・出口・return・分岐・残るflowをラベルにした有向多重グラフを使います。式・名前・分岐の極性を捨て、明示的に剪定された辺と入口から届かないblockを除きます。出口は保持し、単一後続のflowを縮約します。自己循環は残します。関数内のdispatcherも同じ規則で比較します。
距離は入口・出口を対応させ、nodeの追加・削除・ラベル変更とedgeの追加・削除をそれぞれ1と数えます。`exact`と、探索予算で止まった`upper_bound`を区別し、下限・上限・対応表・停止理由を保存します。対応表は`control_graph.graph_from_json`と`mapping_cost`で再計算できます。
探索の下限には、未対応ラベルの不足数と、固定した対応の内側・境界・残余に分けた辺数の差を使います。[全部分対応のoracle](../tools/tests/test_control_graph.py)で小グラフの下限と最短距離を照合します。

`--c-footprint`は[Clang JSON AST](https://clang.llvm.org/docs/IntroductionToTheClangAST.html)から`nirvana-c-ast-footprint-v1`を測ります。対象関数の演算・リテラル・型、条件式の規模、メモリ参照構文、checked read/write helperの呼出し箇所を記録します。局所変数を宣言順のIDへ対応付け、名前変更を吸収した条件・関数のfingerprintを保存します。`_Generic`は選択された式、`sizeof`は未評価のoperandを区別して数えます。重複条件は同じ構文の出現数で、可変な局所変数が各使用点で持つ値の同一性は別の解析対象です。helper呼出し箇所も静的な構文の観測です。元Cとの差分は指標ごとに示し、意味的な距離や総合点への換算は将来の対応解析で扱います。

ASTの生データとhashを保持し、比較器が集計値とfingerprintを再計算します。Clang 18の版を固定し、対象外のAST構文・読取り失敗も全構成の分母に保持します。これにより、制御の距離だけでは見えない処理や条件の増減を確認できます。
配列は固定長を対象とします。可変長配列の宣言や`sizeof`には実行時の評価が関わるため、未対応として保持します（[C11草案 §6.5.3.4](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)）。

`--state-memory-sites`は、固定の`state[4]` ABIについて元Cと生成Cの参照位置を対応付けます。`--c-footprint`と`--semantic-probe`を併用します。元Cの第0引数を、probeが記録したRDI（NirvanaのレジスタID 7）と生成Cの引数の対応へ結び、read/writeのバイトoffset・幅・静的な出現数を保存します。たとえば`state[2]`と、入口アドレスから16バイトの位置への8バイトアクセスを対応付けます。生成Cのconstなview初期値とアドレス式を使い、field名には依存しません。

動的添字、書換えられるアドレス引数、未解決の参照元や呼出しは`partial`として件数を残します。整数の切詰め・wrapは幅を保って扱います。これはABIの状態ワードとの位置の対応で、元の局所変数・型・格納値の同一性は次の評価対象です。生ASTとhash付きのABI情報から対応と集計を再検査し、対応範囲の喪失を比較結果へ記録します。

`--state-values`は、同じABIの元Cと生成Cを[型付きの値グラフ](../tools/evaluation/state_values/)へ変換し、返り値と32-byteの状態に差がある入力をSMTで探します。対象は整数演算、閉じた`if / return`、関数本体の後続ラベルへのgotoと、`while / for / do`です。gotoは現在の値のsnapshotを後続処理へ渡します。ループは16回まで展開し、`break / continue`と反復ごとの局所値を保持します。展開後にも実行が続く入力をSMTの差分条件へ加え、全入力で展開内に終了するときに同値性を判定します。残る反復がある場合は`unknown / loop_bound_exhausted`と入力を保存します。局所変数への代入は値のsnapshotへ、メモリはbyte列へ対応付け、部分書込みとcastの幅を保持します。x86-64 LP64、有効な状態ポインタ、状態内の参照、既知のchecked-memory helper契約を前提にします。各反復で確定する添字も扱い、sourceのポインタ演算は中間位置も状態object内かone-pastかを検査します。未知のsigned overflow・範囲外のsigned cast・ゼロ除算・未解決の参照・制御は、評価の未対応として記録します。

`equivalent_under_model`は4状態ワードの全域に対するモデル下の結果です。SATは値グラフで再実行し、`counterexample_under_model`として入力と差を保存します。sourceの変数名や寿命、機械語全体の正しさはそれぞれ別の評価項目です。無効ポインタのfault、全RAM、PC・予算は既存の具体実行検査へ結びます。値グラフの規模・fingerprintは構文的な補助観測として扱います。

値モデルv7は、生成Cのrecord・view・整数アドレスを宣言時の値として保存します。ループ内の宣言は各反復で捕捉し直します。signed演算は保守的な区間で候補を作り、幅を広げた独立のSMT式でcastの範囲・overflowなどの前提も検査します。前提の反例は`unknown / definedness_not_established`として再実行します。既知の整数helperには別の全域契約を使い、符号拡張、mask付き算術シフト、8/16/32-bitの商・剰余と、範囲内のsigned wordへの変換を扱います。helperの返り型も照合し、Cの整数昇格へ結びます。C演算の未定義動作とhelperの全域定義を区別します。

値モデルv8は、現在または祖先のblockの後続ラベルへ、値とメモリのsnapshotを渡します。各blockの自動変数は反復ごとに初期化状態を作り直し、合流ではguard付きの値・byte・viewを結びます。初期化済みメモリcontextも経路ごとに保持します。空の初期化・増分を持つforの直前ラベルへの移転は、同じ外側loopのcontinueとして表現します。その他の後方移転やloop途中への入場は未対応として保持します。状態は不変なwordのbyte射影で保存し、必要なLoadで展開するため、4,096値node・64経路・10,000work・16反復の上限を保ちます。

定数除算では、同じ幅・分子・除数の商を任意の関数へ置き換えた保守的な抽象化も使います。剰余は`n-q*d`、signed除数は絶対値と結果の符号へ分けます。この広いモデルでUNSATなら元の演算でも同値です。抽象化のSAT・unknownは通常のbit-vector式で再検査し、反例は元の演算で再実行します。抽象化には最大0.25秒（指定予算の1/4以下）、通常問い合わせと反例取得にはそれぞれ`--value-seconds`を使い、最大3回の起動と合計の完了時間を記録します。通常式と抽象式、各応答の問い合わせ区分を別々に保存・再検査します。

```sh
python3 tools/evaluate_structure.py --cases tools/corpora/structure-initial-v1.json \
  --clang clang-18 --compiler gcc=cc --compiler clang18=clang-18 \
  --semantic-probe target/debug/examples/evaluation_probe --c-footprint --state-memory-sites \
  --state-values --value-solver target/verification-venv/bin/z3 --out target/structure-values
```

AST・ABI情報から値グラフと問い合わせを再構築し、hash付きのsolver出力とSAT入力を照合します。UNSATは保存したsolverの判定を使います。報告の評価器revisionとmodule hashを揃えて再解析します。solverの完了した起動ごとの時間を保存し、そのRSSは未計測として扱います。Z3の準備と正負対照は[検証ガイド](verification.md)にまとめています。

## リンク済みleaf関数

`evaluation_probe --module`は、リンク済みELFの`fixture`に固定の`state[4]`を渡します。通常入力と、各命令PCから0/1/2/4/8/16/32命令で停止する再開ケースを保存します。module IRとcore/readable/localsの生成CをO0/O2・UBSanで比較し、全80レジスタ・RAM・PC・停止結果・fault・命令開始数・残り予算を照合します。RAMは生成observer内でbyte比較し、保存行にはdigestを残します。native oracleとの比較対象は返り値と4状態ワードです。このleaf profileの観測項目は上記の状態で、命令traceや外部I/Oの列は別profileで評価します。

```sh
target/debug/examples/evaluation_probe --module input.elf inputs.txt target/module-leaf native-oracle
python3 tools/compare_module_reports.py target/module-before target/module-after > target/module-comparison.json
NIRVANA_MODULE_PROBE="$PWD/target/debug/examples/evaluation_probe" \
  python3 -m unittest discover -s tools/tests -p test_module_evaluation_probe.py
```

比較器は同名の構成ディレクトリを要求し、ELF・入力・profile・予算・nativeの観測を照合します。全行と期待RAMの再生、生成Cの保存行の比較を行い、未対応や評価器エラーも要求分母に残します。1関数256命令、4,096ケース、期待RAM計128 MiBを上限とします。追加整数corpusのベクトル化4構成は、閉じたET_RELでは定数の再配置が未対応です。同じobjectをリンクしたELFではSSE2のmodule経路で評価し、閉じた関数の回収率と別に報告します。

`--semantic-probe`は、同じobjectのnative実行とIRの返り値・4状態ワード、IRと生成Cの全RAM・最初のfaultを各行へ結びます。入力は固定境界値とseed付きの16組で、正常・末尾境界・無効pointerを使います。生成CはO0/O2・UBSanで比較し、停止予算切れを未判定として分母に保持します。構造の読取りに失敗した行でも、意味の比較を別に進めます。

同じprobeの`stage_checks`は、Low IR→Middle IRの再構成、直接MIR実行と戻し変換、経路条件回復後のMIRを別々に記録します。0/1/2/4/8/16/32/64/128と指定上限の各予算で、全レジスタ・全RAM・最初のfault・PC・traceを元IRと照合します。総実行予算を超えた段階は未判定として残します。反例や観測器のエラーがあっても、native/Cの比較は独立に進めます。

段階形式v3は`middle_memory`と`middle_saved`を加えます。前者はメモリ定数を回復したMIRの直接実行とLow IRへの戻し変換、後者は保存値を回復したMIRの直接実行とsnapshot展開後のLow IRを、元の機械レジスタ空間で照合します。snapshot用の追加レジスタは0/`UINT64_MAX`で初期化し、その内部レジスタだけを除いて比較します。各段階の入力・MIR・出力dump、回復件数、全状態のJSON Linesを保存し、再検査時にhash・入力・比較順・件数・状態の一致を確認します。適用なし・未判定・反例を区別します。

段階形式v2以降の`selected_semantic`は、選ばれたC出力が保持する[実際の意味IRの入力と下ろし変換](../src/model/semantic_ir.rs)を比較します。入力は幅・変数の整理後の表示IRで、その全レジスタを保存し、追加した意味演算の捕捉レジスタだけを除いて照合します。入力側の仮想レジスタと捕捉レジスタを0/`UINT64_MAX`の2パターンで初期化し、同じ予算ごとのRAM・fault・PC・traceも比較します。機械レジスタと表示IRの値IDは別の範囲です。前段の還元を含む返り値・RAM・faultは、同じ行のnative/IR/C比較で扱います。

意味IRの入力・出力dumpとhash、捕捉数・置換数、観測件数を保持します。`architecture_execution`は各段階の状態を要求した全構成から集計し、未適用・未実行も残します。比較器は保存データを再検査し、通過していた段階の脱落を回帰、prefix予算の変更を比較条件の変更として扱います。従来の段階形式v1/v2も読み取れます。

`state_pairs`は、各ケース・予算・初期値で比較した全状態をJSON Linesへ保存します。再検査器はレジスタ・全RAM・返り値/fault・PC・traceを比較し、件数・順序・幅・初期状態を確認します。nativeの入力ベクトルが全件ある場合は、初期RAMも共通の512-byte profileへ結び、`input_binding: native-vectors`と記録します。それ以外は`stage-profile`です。記録量は1行4 MiB・1構成128 MiBを上限とし、上限到達は未判定となります。以前の件数だけの報告は`metadata_only`として区別し、保存済み状態の検査が脱落した比較を回帰に含めます。これらは記録した入力・予算での具体比較です。

`encoding: register-rle-u64-v1`を持つ記録は、各snapshotの`registers`をdense配列か`{"rle":[[個数,値],...]}`で保存し、短い表現を選びます。元IRのレジスタ数を使って展開前に個数と論理バイト数を検査し、上記の容量上限を物理・復元後の両方へ適用します。`sha256`は保存ファイル、`decoded_sha256`は従来のdense JSON Linesへ戻した正確なバイト列、`decoded_bytes`はその長さです。RAM・fault・PC・traceなどのバイト列はそのまま保持します。encodingの宣言がない旧記録はdense形式として再検査し、未知のencodingや宣言のないRLEを拒否します。
[固定比較](../tools/corpora/state-records-v1.m0.json)では、Semantic IRの4,080記録が46.3→21.9 MB、MIRの7,140記録が38.3→37.8 MBとなりました。全件の復元hash・生成C・IR dump・検査結果を維持しています。レジスタ数の小さいMIRでは、RAMが記録量の多くを占めます。

段階形式v4の`analysis_checks`は、元のLow IRに対するMemorySSAの世代グラフ検査と候補被覆検査を、具体入力の実行比較と別に記録します。入力IR・MemorySSAのJSON・検査器名・件数・未判定理由を保持し、`architecture_analysis`は生成できなかった行も含む全構成を集計します。保存データの再検査ではhash・形・件数とprobeの生JSONとの一致を確認し、通過した解析検査の脱落を回帰に含めます。世代・byte・SSAの意味の検査はRustの検査器が担当します。旧版v1〜v3のprobeも同じ評価器で比較できます。

v5は`memory_addresses`と`unsigned_bounds`を加え、元Low IR・MemorySSA・型制約の報告をhashで結びます。前者は64-bitアフィン等式と全アクセス位置、後者はunsigned整数の上限と全SSA入力を検査します。`phi_checked`はアドレスのφ入力まで検査できたかを表し、その範囲の縮退も回帰へ含めます。型制約のレイアウトと元C型は引き続き候補として扱います。評価器は旧版の分母を保持し、v4/v5を同じ入力で比較できます。
[v5の固定比較](../tools/corpora/ir-affine-v1.m1.json)では、同じ開発用4構成のC本文と構造・実行結果を保ち、追加した2検査が各4件の通過となりました。保存先を移動した報告も、元の出力パスを正規化して比較でき、compiler flagと入力パスの変更は引き続き検出します。

v6は`storage_widths`を加え、Cの保存幅と表示変換が使う`ValueWidths`の検査を元Low IRへ結びます。`storage-widths.json`には到達blockの入口条件、全レジスタの保存幅、検査結果を保存し、失敗時も理由を保持します。再検査器は入口条件・到達範囲・件数と生JSONの対応を確認し、意味の帰納条件はRustの`value_width::validate`が照合します。[固定比較](../tools/corpora/ir-storage-v1.m1.json)では同じ4構成のC本文と構造を保ち、旧v5の未記録4件から通過4件となりました。

v7の`selected_storage`は、採用されたCの保存幅を、その候補が実際に解析した表示IRへ結びます。`selected-storage-input.ir.txt`・`selected-storage.json`・`selected-readable.c`を保持し、同じ入力への幅検査、unsigned局所変数と所属レジスタの幅、CLI出力との本文一致を確認します。解析位置は表示変換前とDCE後を区別します。[固定比較](../tools/corpora/ir-selected-storage-v1.m1.json)では開発用6構成で検査を通し、同じデコンパイラのv6/v7比較でC本文と構造を保ちました。signed表現・Cの整数昇格・途中PCからの再開は、それぞれの契約で評価します。

v8の`selected_signed_storage`は、signed局所変数を選んだ最終display IR・SSA・符号拡張の証跡・生成Cを対応付けます。各localの全メンバが選択したsigned幅へ収まることを再検査し、`prepared-display`という解析位置を記録します。再検査helperのhashも評価器の版へ含めます。[固定比較](../tools/corpora/ir-signed-storage-v1.m1.json)では、既存のsigned例4構成で各3個のsigned localを検査し、初回24構成とともにC本文と意味比較を維持しました。旧v4〜v7の結果も同じ評価器で読み、検査の追加・脱落・未判定を分けて集計します。

[v4統合のcheckpoint](../tools/corpora/structure-analysis-v1.m0.json)は、[開発用2ソース](../tools/corpora/structure-analysis-v1.json)のGCC/Clang O2、計4構成を固定しています。同じobject・デコンパイラ・8入力・4096-step上限でv3/v4を比較し、2種類の解析検査が各4件の未記録から通過へ進みました。生成Cと正規化グラフは同じで、native 32件・O0/O2生成C 192件・IRの全状態比較2,400件を維持しています。保存した実データへの5種類の欠落・改変も拒否しました。checkpointには版・hash・再現条件を残し、生データは[容量管理](../README.md#開発)付きの短期保存へ置きます。

`low_coverage`は元IRで開始した命令と観測したCFG遷移を数え、通っていない遷移のPC対も保持します。遷移の分母は構文上の`(block末尾PC, 移転先PC)`の集合で、実行可能性の証明とは分けて使います。`selected_c`には採用した経路条件の根拠と構造対応検査の有無を記録します。

`continuations`はC保存先の確定後に検査した終了処理の共有を、モデルID・条件nodeの減少数・照合グラフ規模で示します。v2の`shared_fragments`は、非空のStep/Evaluate/Return断片の減少数です。条件の複製を一箇所へまとめる場合も、各経路での評価を保持します。v3は`store_order`に保持するprefix node数・成功読込みの範囲数・Store交換数を加えます。これらは静的な変換根拠で、C文数や動的な実行回数と分けて扱います。v4の`effect_order`はStore同士と独立な局所更新との交換数を分けます。比較器はv1〜v4を読み、[設計](architecture.md#c保存先確定後の継続処理)に記したCの観測境界とMIRの全状態検査を別々に集計します。対応検査と具体入力での一致は、それぞれの対象範囲を持つ検証結果です。

## 追加入力

[追加入力の探索](../examples/evaluation_witnesses.rs)は、元の非debug objectと入力集合から未観測のCFG遷移を求めます。`checked-memory-path-inputs-v1`は512-byteのRAM、RDI/RSP、他レジスタを固定し、4状態ワードだけを任意値とします。生成Cのprobeと[同じ初期化](../examples/evaluation/fixture.rs)を使います。SAT入力は元IRで命令prefixと次のPCを再現し、正常returnまで実行できたものを`inputs.txt`へ加えます。途中停止やfaultへ至った候補も根拠を残します。

対象命令の先祖領域がDAGなら、[上限付きの全経路列挙](../src/verification/block_verify/paths/enumerate.rs)で全prefixを求めます。その全てがUNSATの場合だけ、固定入力profileでの到達不能を`infeasible_dag`と記録します。循環を含む領域では観測済みのprefixを使い、未知・列挙上限・問い合わせ上限を残します。構文上のcoverageの分母は維持し、到達不能の判定を別軸で報告します。これは有効ポインタ時の元IRに対する結果で、全ABIやnative命令の一般的な到達不能とは分けて扱います。

`report.json`には各辺・列挙の完全性・問い合わせと入力、出力先には元object・初期入力のコピー、SMTとsolver結果、具体実行を保存します。問い合わせ数、solver起動ごとのミリ秒、実行step数を順に指定できます。固定した追加入力は`--semantic-inputs FILE --semantic-cases N`でnative・IR・生成Cへ渡し、同じ入力集合で変更前後を比較します。hold-outで得た入力は、凍結済み実装の追加検証として扱います。

[17組の固定入力](../tools/corpora/structure-branch-inputs-v1.txt)は、既定の16組に、開発用Clang 18 O2のループ脱出例から得た`0 1 0 0`を加えた集合です。利用時は`--semantic-inputs tools/corpora/structure-branch-inputs-v1.txt --semantic-cases 17`を指定します。

```sh
cargo build --locked --example evaluation_witnesses
NIRVANA_Z3=target/verification-venv/bin/z3 target/debug/examples/evaluation_witnesses \
  target/structure-baseline/CASE/input.o \
  target/structure-baseline/CASE/semantics/native-inputs.txt \
  target/structure-witnesses/CASE 8 1000
```

[メモリ変換corpus](../tools/corpora/structure-memory-v1.json)は、定数Store・部分byte更新・保存値の再利用をGCC/ClangのO0/O1/O2で比較する開発用の追加profileです。`--cases tools/corpora/structure-memory-v1.json --optimization O0 --optimization O1 --optimization O2`で選び、上記17組の固定入力を使います。初回corpusのhold-outと分母を分けて集計します。

## 測定費用と対象範囲

`--measure-rss`はGNU timeでコマンドごとの最大RSS（KiB）とCPU時間を記録します。RSSはそのコマンドと待機した子のうち最大の単一プロセスの値で、同時実行プロセスの合計とは区別します。意味比較を省略した実行は`semantics: not_run`として残ります。演算・条件・効果と元ソースの値の対応を結ぶ指標はM0の継続対象です。
[対照テスト](../tools/tests/test_control_graph.py)は名前変更の距離0、goto削減に伴う条件複製の距離悪化、小グラフの全ての部分対応との比較、打切り結果の対応表を検査します。

## 比較と再解析

[報告の比較器](../tools/compare_structure_reports.py)は、corpus・binary・compiler・フラグ・観測契約を照合し、保存したdumpからの正規化、対応表の費用、具体実行の全ワードを再検査します。probeの生JSONもhashを保持し、観測profileと段階別の検査結果を再解析して照合します。このhashを持つ報告は`probe_metadata: replayed`、従来の報告は`legacy_unbound`として区別します。探索結果の最適性は記録したソルバの判定を使い、打切り区間が重なる結果は未判定として扱います。同じグラフ同士の比較では、打切り後も距離が等しいことを確認できます。失敗行も分母に保持します。

```sh
python3 tools/compare_structure_reports.py \
  target/structure-baseline/report.json target/structure-candidate/report.json \
  > target/structure-comparison.json
```

探索器を更新した場合は、[保存グラフの再解析](../tools/reanalyze_structure_report.py)で同じ入力を使えます。元の報告を保持したまま同じディレクトリへ別名で保存し、元報告のhash・新しい探索器のhash・新しい距離を記録します。native/Cのコマンド費用は元測定の値として保持します。

```sh
python3 tools/reanalyze_structure_report.py target/structure-baseline/report.json \
  --out target/structure-baseline/report-refined.json
```

