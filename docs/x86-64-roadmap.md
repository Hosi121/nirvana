# x86-64デコンパイラのロードマップ

対象はx86-64 long modeのバイナリを調べる開発者・解析者。
機械語の動作を保ち、人が関数・データ・制御の意味を追えるCを、より広い入力から得ることを目指す。
現状の記述は [`ef581a1`](https://github.com/Hosi121/nirvana/tree/ef581a12f3b073145af4a81bff6d9ea8a3dc71bd) を基準とする。
以下は、各段階の成果物と合格条件を定める開発案である。

## 「完璧」を評価できる目標にする

目標を、対応領域の広さ、動作の保存、理解しやすさの三つで評価する。
各出力に、入力形式・CPU機能・ABI・実行環境・許される初期状態・観測契約を対応付ける。
対応領域内では、その契約の動作を保った実行可能Cを生成し、解析根拠と元の命令位置を追えるようにする。
未知の分岐先、未対応命令、資源上限は位置と理由を示し、対応範囲の集計に含める。

現在の契約は[実行モデル](equivalence.md)にある。
単一関数では返り値・全ゲストRAM・最初のメモリfaultを、moduleでは全レジスタ・PC・命令予算・外部効果も照合する。
将来のプロファイルには、例外、浮動小数点状態、syscall、スレッド間の観測などを明示的に追加する。
CPU実時間やホストのfd番号を含め、何を同一視するかもプロファイル側で定義する。

元ソースの文字列一致は、別の問題になる。
例えば局所変数名だけが異なる二つのソースから同じ機械語を作れるため、失われた名前・コメント・元の型宣言は一意に決まらない。
型や構造の候補には根拠と曖昧さを残し、元ソースとの近さを動作の正しさとは別に測る。
一般の無限メモリ計算には万能な停止性判定がないという[Turingの結果 §8](https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf)もある。
固定された有限状態の機械をそのまま決定不能と呼ぶのは適切ではないが、全状態の列挙を実用的な検査法にはできない。
検査には適用領域・前提・上限を持たせ、未判定を保持する。

## 確認できる現在地

| 領域 | 基準コミットにある能力と根拠 | 現在の境界 |
| --- | --- | --- |
| 入力 | [ELF reader](../src/elf.rs)、[linked ELF](../src/linked_elf.rs)、[CLI](machine-frontend.md)。ELF64 LEのET_REL/ET_EXEC/ET_DYN、raw bytes、再配置・PLT/GOT・BSS | 通常は名前と正のサイズを持つ関数シンボルが入口。stripped画像全体の関数発見は今後の対象 |
| 命令意味 | [x86](../src/x86/mod.rs)の整数・部分レジスタ・5種のflag。moduleに[限定的なSSE搬送等](../src/x86/vector.rs) | DIV/IDIV、一般のSIMD演算・浮動小数点、FS/GS、一般例外などに追加実装が必要 |
| 関数間実行 | [module IR](../src/module_ir.rs)、[HTTP比較](../tests/fixtures/http-server/README.md)。内部・間接CALL、実stackのRET、POSIXアダプタ | ロード直後のモデル画像と限定したLinux環境。起動処理・TLS・実libc全体の再現は別の対象 |
| 間接分岐 | [jump tables](../src/jump_tables.rs)、[input breadth](../tests/input_breadth.rs)。絶対・符号付き相対表から追加命令を発見 | 初期画像の候補は `complete:false`。実行時は現在のRAMを読み、未発見PCでは `UnknownTarget` |
| 値・型 | [SSA検査](../src/ssa/verify.rs)、[module values](../src/module_values.rs)、[record候補](../src/record_shapes.rs)、[型テスト](../tests/record_shapes.rs) | 値ID・寿命・保存場所と、元変数・型互換性・実際のaliasは個別の情報。候補宣言は検査付きメモリ実行を変更しない |
| 出力・検査 | [構造化](architecture.md)、[独立検査器とSMT](verification.md)。if/loop/goto、φコピー、局所変数、途中PCからの再開 | 検査モデルと具体入力比較にはそれぞれ適用範囲がある。生成Cまでの包括的な証明は未達 |

ジャンプテーブルの[基準コミットの比較記録](https://github.com/Hosi121/nirvana/blob/ef581a12f3b073145af4a81bff6d9ea8a3dc71bd/tests/fixtures/input-breadth/README.md)は、3ソース×O0/O2×ET_EXEC/PIEの12構成で、
1,452件のnative/oracle/IR比較と10,128件の生成C状態比較を報告している。
これは小さい固定corpusの実績である。別コンパイラ、stripped入力、一般の間接分岐への汎化は、以降の評価で確かめる。

## 優先する四つの難所

### 1. 発見したコードと、未発見の制御を同時に表す

最初はLinux ELFを深め、入口・命令境界・コードとデータ・関数の所属を相互に更新する。
シンボル、再配置、unwind情報、直接参照、値域、間接target式を根拠として保持する。
関数は非連続な領域、共有末尾、tail call、複数入口を表せるようにする。
根拠の競合や重なる命令列は診断し、根拠の弱い推定を後段の固定事実にしない。

ジャンプテーブルは、短い命令窓から先行CFGの経路別文脈へ進める。
合流時の異なる定義、部分レジスタ、stackへの退避、経路条件、ループ、CALLによる破壊を扱い、探索上限を記録する。
候補の導出には[Ddisasmの絶対・相対表の区別](https://grammatech.github.io/ddisasm/DATALOG-API/src_docs/jump_tables.html)も参考になる。
添字範囲の証拠に加え、表の書換えと外部効果を調べ、全targetを覆う根拠が揃った範囲を閉じたCFGとして扱う。
既知の候補と未知の残余辺を併記し、開いた辺に依存する支配・SSA・関数要約の前提を明示する。

次に関数ポインタ、vtable、callback、computed gotoへ対象を広げる。
動的traceで得たtargetは観測済み集合として追加し、静的な完全性の証拠とは区別する。
実行時の元のtarget式・Load・fault順序を保持し、候補外への移転も診断できる経路を持つ。
JIT・自己書換えはコードの版と再解析が必要になるため、固定画像の後に独立した実行プロファイルで評価する。

### 2. ISA・ABI・実行環境の意味を揃える

[Intel SDM](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)と
[AMD APM](https://docs.amd.com/v/u/en-US/40332_4.09_APM_PUB)を命令意味の根拠にし、文書版とCPU機能を固定する。
対応表をopcode名だけでなく、prefix・幅・addressing・flag定義・例外・機能条件の組合せで管理する。
未定義flagは定義済み値と区別し、独立したデコーダ比較とnative命令oracleでlifterを検査する。

整数の欠けた形式、DIV/IDIVの例外、REP文字列操作、FS/GS・TLSを先に扱う。
続いてSSE/AVXの整数演算と浮動小数点へ進み、レーン、mask、上位レジスタ、丸め、NaN、MXCSR/x87状態を表す。
生成Cには、許される機械状態でCの未定義動作を起こさないloweringと必要なhelperを用意する。
ホストのfloatやlibcに委ねる部分は、保存できる意味と環境条件を検査する。

関数境界では[SysV AMD64 ABI](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/master/x86-64-ABI/low-level-sys-info.tex)を基準に、
引数・返り値・stack alignment・red zone・可変長引数・集約値・破壊集合を回復する。
最適化された内部関数の独自規約は、実際のread/writeから検査する。
外部関数は、RAM・出力・errno・復帰・非局所制御の効果を持つ要約にする。
起動状態、動的リンク、syscall、allocator、setjmp/longjmp、例外unwindを段階的に接続する。
ページ権限・CPU例外、atomic・x86メモリ順序・signal・MMIOは、それぞれ観測契約の拡張として扱う。

### 3. メモリから値・オブジェクト・型へ上げる

現在のレジスタSSAを土台に、メモリの世代とmay-alias/must-aliasを追加する。
[LLVM MemorySSA](https://llvm.org/docs/MemorySSA.html)のdef/use/phiは設計の参考になるが、aliasの正しさやfault順序は別に検査する。
stackの部分書込み、再利用、動的RSP、escape、heap、global、未知CALLの破壊を同じ値の流れへ結び付ける。
同じアドレス式の再Loadを同じ値と扱うには、間の書込み・外部効果が干渉しない根拠を要求する。

その上で関数間の引数・返り値・効果を反復して絞り、寿命、所有する領域、オブジェクト境界の候補を作る。
型は符号、幅、pointer、配列、struct、union、再帰型、関数pointerを使用制約から求める。
重なるフィールド、型の混用、tagged pointer、container内の途中pointerを表し、矛盾や複数候補を保持する。
C++のclass/vtable、RustやGoのruntime由来の形は、この共通基盤に言語別の回復規則を重ねる。

型候補を実行用のC pointer/structアクセスへ反映する際は、alignment、範囲、alias、表現、faultの対応を追加検査する。
検査が届かない領域では、型候補の表示と既存のbyteメモリ操作を組み合わせる。
「局所変数が減った」「structらしく見える」を、元変数や実際のオブジェクトの回復と同一視しない。

### 4. コンパイラ変換を踏まえて構造と意図を回復する

[CFG調査](cfg-recovery-research.md)と[SAILR](https://www.usenix.org/conference/usenixsecurity24/presentation/basque)を踏まえ、
loop rotation、jump threading、共通末尾、複製、if-conversion、switch loweringを領域単位で扱う。
純粋なCFG配置変更と、条件・演算・反復数を変える候補では、別の意味検査を使う。
Store・CALL・fault・途中再開の対応を維持し、変更後のSSA・寿命・型根拠を更新する。

未知の辺が残る領域にも局所gotoやdispatcherを置き、外側のif/loopと名前付き関数を保つ。
switchは添字とcase値・default・残余targetを対応付けて表示し、書換え可能な表の実行意味も保つ。
最終的な出力では、宣言、式、API、データ型、名前、元PCへの対応を統一し、生成Cの再コンパイル比較まで行う。
構造の評価にはgoto数に加え、条件長、深さ、複製量、元ソースとの構造距離、解析作業の正答率を使う。

AIは名前・型・領域変換の候補生成や説明に利用できる。
表示名だけの変更と実行意味を変える提案を分け、後者は対応する独立検査器を通して採用する。
検査器の範囲を超える提案は注釈として示し、実行用IRへ確定しない。
AIの効果は固定した評価集合で、既存処理に対する精度・費用・再現性を測って判断する。

## 段階と合格条件の案

依存関係は `M0 → M1`、`M0 → M2`、`M1 + M2 → M3`、`M2 + M3 → M4`、`M1〜M4 → M5`。
各段階は部分集合から進め、契約が成立した領域を公開する。

| 段階 | 完了時に残す成果物 | 次へ進む評価ゲート |
| --- | --- | --- |
| M0: 比較の土台 | 対応表、失敗分類、再現manifest、固定corpusとhold-outの分割、独立oracle | 既存12構成を再現。Clangを加えた24構成でlift可否と意味比較を全件記録。未対応・timeoutを成功率の分母に残す |
| M1: 意味の拡充 | 整数・例外・SIMD/FP・ABI・外部効果を小さい契約ごとに追加 | 各形式の境界値・flag・fault比較、生成CのO0/O2比較とUBSanを通過。対応宣言した範囲の既知の意味反例が0件 |
| M2: 発見の拡充 | 先行CFG文脈の表解析、stripped関数候補、間接target残余、閉包根拠 | 分岐合流・上書き・loop・表変異で誤った閉包を採用しない。hold-outで命令/辺の回収率が改善し、正確率と既存意味比較を維持 |
| M3: データの回復 | メモリ世代、alias、関数間要約、型・object・局所変数候補 | 部分書込み・escape・未知CALLの反例集合を通過。hold-outでfield/型/変数対応の正確率を維持し回収率を改善。実行意味の回帰0件 |
| M4: 高水準の出力 | switch、領域goto、compiler-aware変換、型付き出力、検査証拠 | 固定とhold-outの両方で構造・読解指標が改善。全状態・fault・外部効果・再開検査を通過し、出力量と解析費用を併記 |
| M5: 実用範囲の拡張 | 大きい実プログラム、追加runtime、PE/COFF・Windows x64、Mach-O等のプロファイル | 各形式・ABI・環境に独立したcorpusと意味ゲートを用意。プログラム全体の外部観測と関数単位の回復品質を両方報告 |

PEでは[Windows x64の呼出し規約](https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention)とunwind、import、TLSを一緒に実装する。
Mach-Oや追加runtimeも、ファイルを読める段階と動作を保つ段階を区別する。
kernel・難読化・JIT・並行実行への拡張は、それぞれの契約と評価入力が揃った時点で段階を追加する。

## 評価を過学習させない

- **corpus**: 手書き命令境界例、既存fixture、生成プログラム、実OSSを分ける。実OSSの初回候補はparser、圧縮、hash、コンテナ、CLI、ネットワーク処理の6系統とし、ライセンスと再配布条件を記録する。
- **分割**: プロジェクト・ソース族単位で開発用とhold-outを固定する。失敗例を実装修正へ使ったら開発用へ移し、hold-outを補充する。同じソースの別最適化版を別集合へ分散させない。
- **compiler**: GCC/Clang各2版を目標にO0/O2/O3/Os、PIE/ET_EXEC、strip有無を測る。LTO、PGO、stack protector、CET、各ISA機能は別軸として段階的に追加し、MSVCはWindows段階で加える。
- **正解情報**: シンボル・DWARF・link map・compiler dumpは評価器側に置く。decompilerへの入力条件を固定し、inline・共有末尾などの多対多対応を表す。独立ツールとの一致も、正解そのものとは扱わない。
- **意味**: native/oracle→IR→再コンパイルCを照合する。全RAM digestは比較を省力化する補助で、差が出たらbyte列を保存する。trap、外部効果、停止prefix、途中再開、予算境界を含める。
- **報告**: 成功、明示拒否、未知target、予算切れ、検査未判定、誤った出力を分け、全入力に対する件数と率を出す。命令・関数・CFG辺のprecision/recall、観測した誤閉包数、実行中の未知target率も併記する。
- **費用と再現**: compiler・CPU機能・ソルバ・入力seed・全フラグ・binary hash・モデルID・解析上限を保存する。時間・最大RSS・出力量の中央値とp95を、同一画像・同一環境で変更前後比較する。

意味を誤った受理結果は0件を採用ゲートとし、有限テストの0件を全入力の証明とは呼ばない。
SMTのUNSATは、そのモデルと前提についての結果として記録する。
CPU仕様からlifter、IR、検査器、C backendまでの信頼基盤と、独立oracleとの共有部分も明示する。

## 次の比較で確かめる一つの問い

**先行CFGの経路文脈を使うと、既存の動的target評価を保ちながら、通常のcompiler出力から発見できる表と命令が増えるか。**

経路文脈の初期実装を、既存3形状のGCC/Clang×O0/O2×ET_EXEC/PIEの24構成と、
diamond合流、定義の上書き、loop、部分レジスタ、表の書換えを含む反例集合で区切る。
共有dispatchを含む手書き命令例の改善に加え、通常のcompiler出力での広がりを評価する。
同一binaryについて、既存方式と新方式の候補・発見命令・未知の残余・意味比較・費用を並べる。
探索上限への到達も結果として保存し、追加発見が確認できない場合は文脈の拡大を続ける前に原因を分類する。
この比較で得た費用から、M0の実OSS corpusに対する時間・メモリ予算と達成値の案を決める。

その後の優先順位には、Linux ELFの実用範囲を先に広げるか、Windowsへの到達を早めるか、
機械状態を追う出力と型付きCのどちらを主な利用体験にするか、という判断が残る。
各ゲートの結果と実際の利用対象を根拠に、この順序を更新する。
