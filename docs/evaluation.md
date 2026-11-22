# M0 Evaluation

M0の[構造評価器](../tools/evaluate_structure.py)は、元Cと生成CをClang 18の[debug.DumpCFG](https://clang.llvm.org/docs/analyzer/developer-docs/DebugChecks.html)で読み、制御の形を比較します。[初回corpus](../tools/corpora/structure-initial-v1.json)は開発用4ソース族とhold-outの2ソース族を分け、GCC/Clang × O2/O3の24構成へ固定しています。従来の[16構成のsmoke集合](../tools/corpora/structure-smoke.json)も個別の比較に使えます。

```sh
cargo build --locked --bin nirvana --example evaluation_probe
python3 tools/evaluate_structure.py --cases tools/corpora/structure-initial-v1.json \
  --clang clang-18 --compiler gcc=cc --compiler clang18=clang-18 \
  --semantic-probe target/debug/examples/evaluation_probe --c-footprint --measure-rss \
  --out target/structure-baseline
NIRVANA_CLANG=clang-18 python3 -m unittest discover -s tools/tests
```

入力のコンパイラと、生成Cを再コンパイルする`--c-compiler`（既定`cc`）を個別に固定します。元Cを各入力compilerで前処理し、そのCから作った機械語だけをNirvanaへ渡します。
出力先は空のディレクトリを使い、`report.json`と各入力の前処理C・object・生成C・生のCFG・正規化グラフ・コマンド記録を保存します。
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

`--state-values`は、同じABIの元Cと生成Cを[型付きの値グラフ](../tools/evaluation/state_values/)へ変換し、返り値と32-byteの状態に差がある入力をSMTで探します。対象は整数演算、閉じた`if / return`、関数本体の後続ラベルへのgotoです。gotoは現在の値のsnapshotを後続処理へ渡します。局所変数への代入は値のsnapshotへ、メモリはbyte列へ対応付け、部分書込みとcastの幅を保持します。x86-64 LP64、有効な状態ポインタ、状態内の参照、既知のchecked-memory helper契約を前提にします。未知のsigned overflow・範囲外のsigned cast・ゼロ除算・未解決の参照・制御は、評価の未対応として記録します。

`equivalent_under_model`は4状態ワードの全域に対するモデル下の結果です。SATは値グラフで再実行し、`counterexample_under_model`として入力と差を保存します。sourceの変数名や寿命、機械語全体の正しさはそれぞれ別の評価項目です。無効ポインタのfault、全RAM、PC・予算は既存の具体実行検査へ結びます。値グラフの規模・fingerprintは構文的な補助観測として扱います。

```sh
python3 tools/evaluate_structure.py --cases tools/corpora/structure-initial-v1.json \
  --clang clang-18 --compiler gcc=cc --compiler clang18=clang-18 \
  --semantic-probe target/debug/examples/evaluation_probe --c-footprint --state-memory-sites \
  --state-values --value-solver target/verification-venv/bin/z3 --out target/structure-values
```

AST・ABI情報から値グラフと問い合わせを再構築し、hash付きのsolver出力とSAT入力を照合します。UNSATは保存したsolverの判定を使います。報告の評価器revisionとmodule hashを揃えて再解析します。solverの完了した起動ごとの時間を保存し、そのRSSは未計測として扱います。Z3の準備と正負対照は[検証ガイド](verification.md)にまとめています。

`--semantic-probe`は、同じobjectのnative実行とIRの返り値・4状態ワード、IRと生成Cの全RAM・最初のfaultを各行へ結びます。入力は固定境界値とseed付きの16組で、正常・末尾境界・無効pointerを使います。生成CはO0/O2・UBSanで比較し、停止予算切れを未判定として分母に保持します。構造の読取りに失敗した行でも、意味の比較を別に進めます。

同じprobeの`stage_checks`は、Low IR→Middle IRの再構成、直接MIR実行と戻し変換、経路条件回復後のMIRを別々に記録します。0/1/2/4/8/16/32/64/128と指定上限の各予算で、全レジスタ・全RAM・最初のfault・PC・traceを元IRと照合します。総実行予算を超えた段階は未判定として残します。反例や観測器のエラーがあっても、native/Cの比較は独立に進めます。

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

