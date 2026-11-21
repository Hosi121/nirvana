# 実行モデルと同値性

Nirvanaは、対応する初期状態からの実行結果を比較します。
読みやすいCの観測対象は、返り値・ゲストメモリ全体・最初のメモリfaultです。
`puts`を含むモデル付きCでは、出力byte列と外部結果入力の消費数も比較します。

## 値と評価順

レジスタは任意の初期値を持つu64です。整数演算は次の規則に従います。

| 演算 | 意味 |
| --- | --- |
| 加減乗算 | modulo 2^64 |
| 比較 | unsigned比較の結果を0/1で表現 |
| シフト | シフト数の下位6bitを使用 |
| 上位乗算 | unsigned 128-bit積の上位64bit |
| 二項式 | 左、右の順に評価 |
| Select | 条件を評価し、選択した枝を評価 |

代入は記載順に実行します。メモリアクセスも元IRの評価回数と順序を保ちます。

## ゲストメモリ

メモリはbaseと有限のbyte配列で与える、単一のchecked memory領域です。stackも同じ領域に含みます。
Load/Storeはlittle-endianの1/2/4/8 byteで、非整列アクセスに対応します。
Loadはゼロ拡張し、Storeは値の下位byteを書き込みます。

アドレス計算はu64で折り返します。各アクセスでは全幅のアドレス範囲を検査し、
u64アドレス空間の末尾を跨ぐ場合と領域外参照をfaultとして返します。
Storeの処理順は次のとおりです。

1. アドレス式を評価する。
2. 宛先の全幅を検査する。
3. 右辺を評価する。
4. 全幅を書き込む。

最初のfaultで実行を停止し、それまでに成功した代入・Storeを状態に保持します。
このため、同じfaultでも停止前のメモリが異なる実行は区別されます。
このモデルが扱う範囲は、単一スレッドの通常メモリと境界検査です。
CPUのページ権限・その他の例外・MMIO・並行実行は今後の拡張対象です。
関数境界と命令集合は[機械語フロントエンド](machine-frontend.md)を参照してください。

## 実行API

`Program`・`StructuredFunction`・`ReducedFunction`の`run_with_memory`は、
`Result<RunReport, ExecutionError>`を返します。実装は[ir.rs](../src/ir.rs)にあります。

| 結果 | 内容 |
| --- | --- |
| `Returned(value)` | 正常終了と返り値 |
| `Fault(MemoryFault)` | 最初のfaultのread/write・address・width |
| `Suspended` | 命令開始数の予算に到達した途中状態 |

`RunReport.state`はレジスタ、全メモリとbase、命令trace、現在／次の命令位置を保持します。
入力レジスタ数などの呼出し条件は実行前に検査します。
`execute_with_memory`は正常終了向けの便宜APIです。fault前の部分状態の比較には`run_with_memory`を使います。

`emit::emit_c(&program)`は`Result<COutput, SequenceError>`を返します。
成功時の`code`に全レジスタ形式のCが入り、式の資源上限はエラーで確認できます。
生成Cの呼出し側では、レジスタ配列とゲストbyte配列にそれぞれ独立したホスト領域を用意します。

## 比較プロファイル

[observe::Contract](../src/observe.rs)は、終了結果と正確なfault、全メモリのbase・size・byte列を共通で比較します。
用途に応じて、レジスタと命令traceを追加します。

| ID | 追加の比較項目 | 用途 |
| --- | --- | --- |
| `full-ir-state-v1` | 全レジスタと命令trace | 同じレジスタ空間の構造化前後 |
| `return-memory-v1` | — | 高水準化後の具体実行と読みやすいC |
| `return-memory-trace-v1` | 命令trace | 命令位置を保つ還元・改名 |

`state.instruction`は診断用の情報です。比較項目は上表で定義します。
内部レジスタを分割・還元したプログラムには、観測したい結果に合わせたプロファイルを選びます。
呼出し側で対応する初期状態を用意し、比較結果を次のように読みます。

| 比較結果 | 意味 |
| --- | --- |
| `MatchForInput` | その対応入力で完了した実行の観測が一致 |
| `Counterexample` | 終了結果・メモリ・追加項目の具体的な差 |
| `Inconclusive` | 片方以上が予算に到達し、最終観測は未判定 |

入力集合やモデル全体を対象とする検証は、[検証ガイド](verification.md)にまとめています。

## putsの外部効果

`effects::MODEL_ID`は`puts-byte-output-tape-v1`です。
`effects::Program`は通常の整数・メモリ命令と明示的なCALLを実行します。
文字列・GOT・stackは同じゲストRAMにあり、`puts`は呼出し時のRAMを読みます。

CALLの順序は次のとおりです。

1. 命令予算を使い、直接値・レジスタ・GOTのLoadから呼出先を得る。
2. 通常CALLではRSPを8減らし、戻り先をStoreする。末尾CALLは現在のstackを使う。
3. 呼出先を照合し、RDIからNULまで1 byteずつchecked Loadする。
4. 次の`PutsOutcome`を検査し、出力prefix・破壊レジスタ・入力消費を確定する。
5. calleeのRETとしてRSPを8進め、継続または関数の終了へ移る。

直接PLT呼出しでは、手順2の戻り先Store後にGOTをLoadします。
間接CALLのメモリオペランドは手順1でLoadします。
この区別により、GOTとstackが重なる場合のtargetと最初のfaultも保持します。

faultでは、それまでのStoreと以前の呼出しの出力を保持します。
文字列読出しを完了した呼出しに、指定した入出力結果を適用するモデルです。
この規則をIR/Cの比較に使い、実マシンのABIとは結果を制御する外部関数oracleを通して照合します。
抽象化したcalleeのRAM効果は文字列の読出しで、戻り先Storeは呼出し側の効果として保持します。

`PutsOutcome`は全RAX、SysVの破壊レジスタと5つのBoolean flag、出力するprefixを指定します。
RAXの下位32bitが非負のintなら文字列と改行を全て出力し、負なら指定prefixを出力します。
RAXの上位32bitも結果入力として保持します。`Output::All`は全文、`Output::Prefix(n)`は先頭n byteです。
`PutsOutcome::success(value)`は、RAXをvalue、他の破壊値を0とする入力の便宜コンストラクタです。

`Program::run`へ初期レジスタ・RAM・結果入力列・`Limits`を渡すと、
`Report`に終了状態、部分状態、`output`、`consumed`が返ります。
命令、外部読出し、出力、呼出し数の各予算は個別に設定します。

`effects_observe::Contract::return_memory_output()`は、同じ初期状態・import・結果入力の下で、
返り値／正確なfault・全RAM・出力・消費数を比較します。
予算切れ、結果入力の不足・不正、未対応の呼出先は`Inconclusive`です。
`full_ir_state()`はIR間の比較に全レジスタと命令traceも加えます。
生成Cの診断情報には命令開始数と現在位置を保持します。

## 複数関数とPOSIX

`module_ir::MODEL_ID`は`module-normal-ram-calls-v2`です。
v2は既存の通常RAM・呼出し規則へ、DIV/IDIVのdivide error（#DE）を加えます。
通常CALLはtargetを評価してから戻り先をStoreし、直接PLTではStore後にGOTを読みます。
RETとimportからの復帰は実際のゲストstackから戻り先をLoadします。
再帰・末尾呼出し・間接呼出し・戻り先の書換えも、このPC dispatchで扱います。
16-byteのベクトルアクセスは全範囲とalignmentを検査した後、レーンの値を反映します。
未登録のtarget、予算到達、range／alignment違反は、部分状態付きの停止結果を返します。

入口は、シンボルまたはunwind情報から範囲を検査したコード領域です。初期画像にはrootの戻り先markerとerrno用領域を置きます。
生成Cの入口はRSP以外をゼロとし、プロセス起動処理・argv・constructorは追加の実行環境の対象です。
単一関数と同じ通常RAMの規則を使います。
IR/Cの比較では、全レジスタ・全RAM・fault・PC・命令開始数を照合します。

リンク済み画像の`stdin/stdout/stderr`は、8-byteポインタ変数とopaque handleを持つ明示的なbindingです。
COPY先と同名のGOT参照は同じ変数を共有し、別名経由の書換えも共通RAMへ反映します。
このprofileが定める初期値と、stream handleの解釈を担う外部adapterを組み合わせて実行します。
生成CのPOSIX adapterは、`puts`の呼出し時にゲストの`stdout`変数を読みます。
既知のstdout／stderr handleは対応するホストstreamへ出力し、未知のhandleは出力前に部分状態付きで停止します。
stderrへの転送時の返り値はLinux/glibcの[puts](https://github.com/bminor/glibc/blob/master/libio/ioputs.c)に合わせ、glibc環境で検証します。
一般の外部データの初期化とFILE内部のモデルは、追加bindingの対象です。

module画像はstackの前に64-byteのゲストTLS領域を持ちます。
`FS:0x28`の8-byte sourceはその領域のguard slotへ対応付け、命令のPC・幅・評価順・flagの効果を保ちます。
初期guardは`0x6e697276616e6100`で、`LinkedImage.thread_local`から位置を取得して、実行前のRAMで設定できます。
これは供給する初期状態の一部です。通常のポインタでguardを書き換えた場合も、後のFS Loadは更新された値を読みます。
他のFS/GSオフセット、thread pointerの変更、PT_TLSは別のprofileとして扱います。
glibcの配置は[tcbhead_t](https://github.com/bminor/glibc/blob/master/sysdeps/x86_64/nptl/tls.h)と[guard参照](https://github.com/bminor/glibc/blob/master/sysdeps/x86_64/stackguard-macros.h)を参照してください。

PLT照合はENDBR64・BND付きJMPを受理し、通常RAM profileではMPXを無効、CETを非追跡として扱います。
BND PLTの形式は[GNU ldのbndplt](https://sourceware.org/binutils/docs-2.29/ld/Options.html)、MPX状態は[Intel SDM Appendix E](https://cdrdv2-public.intel.com/835781/325462-sdm-vol-1-2abcd-3abcd-4.pdf)を参照してください。

DIV/IDIVは8/16/32/64-bitのレジスタ／メモリsourceを扱います。
命令予算を消費し、sourceを一度評価してから、二倍幅の被除数を割ります。
領域外のメモリsourceは通常のRAM faultで停止します。
sourceが0、または商が出力幅に収まらない場合は`Status::DivideError`（生成Cのstatus 10）で停止します。
この時点のPCは元のDIV/IDIVで、レジスタとRAMはその命令の開始時の値を保ちます。
成功時は商と剰余を反映し、8/16-bitの部分書込みと32-bitのゼロ拡張を適用します。
符号付きの商は0方向へ丸め、剰余の符号は被除数に従います。
未定義の5つのflagには従前値を選ぶ決定的なモデルを使います。
関数内のflag検査はDIV/IDIVで利用可能性を消し、以後の定義とCALL境界で更新します。
`CWD/CDQ/CQO`は被除数を符号拡張し、flagを保持します。
局所変数付きCも同じ除算処理を使い、成功した後に生存値を実レジスタから読み戻します。
このためRAM fault・#DEでの停止は、局所変数の更新より先に起こります。
解析用SSAでは結果を未知として区別し、除算以外のレジスタの値追跡を継続します。

CのPOSIXアダプタはLinux x86-64の、有効なbufferを持つ呼出しを対象とします。
socket類の整数返り値、ssize_t、sockaddr、socklen、pollfd、timevalを型に合わせて変換します。
成功した出力はerrnoと重なっていても保持し、失敗した呼出しではerrnoを更新します。
破壊レジスタにはSysV ABIで許される固定値を選び、callee-savedレジスタとRSPを保持します。
sockaddrは128 byte、pollは65536要素、setsockoptは送受信timeoutのtimevalを扱います。
HTTP比較の観測はstatus・headers・body・接続終了・プロセス終了です。各実行のportとfdはOSが割り当てます。

書式付きI/Oは[`formatted.h`](../src/module_emit/formatted.h)で共通化しています。
SysVの整数／pointer引数を6個のGP registerと、calleeの`RSP+8`以降のstack slotから読みます。
`printf/sprintf/snprintf`は`diuoxX`・`c`・`s`・`%%`、整数の`hh/h/l/ll`、幅・精度と`*`を扱います。
`scanf/__isoc99_scanf`は整数の`diuoxX`、同じ幅修飾、field幅、空白・literal・`%%`を扱い、代入数・EOF・部分成功を保持します。
全書式を検査してからI/Oへ進み、scanfの各destinationはその変換の直前に検査します。先のStoreが後のstack引数を書き換えた場合も再Loadします。
各変換は型を合わせたホストlibc呼出しへ渡し、ゲストpointerは検査済みRAM内のhost pointerへ変換します。
`snprintf`は切詰め・NUL・本来の出力長を区別し、capacity 0ではdestinationへアクセスしません。
`putchar`と`printf`はゲストstdout binding、`scanf`はゲストstdin bindingを参照します。
`__printf_chk/__sprintf_chk/__snprintf_chk`も対応する引数位置を使い、object size条件を検査します。
fortifyの条件違反は外部効果前のunsupportedとして扱い、SIGABRTの再現はsignal profileの対象です。
このprofileはC locale、対象整数型の範囲内の入力、重ならないformat／出力bufferを前提にします。
書式は4,096 byte、出力は65,536 byte、変換は32個までです。上限、浮動小数点、位置指定、`%n`、入力の抑制・文字列変換はunsupportedとして保持します。
仕様の根拠は[SysVの可変長引数](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/master/x86-64-ABI/low-level-sys-info.tex)、glibcの[出力書式](https://sourceware.org/glibc/manual/latest/html_node/Output-Conversion-Syntax.html)・[整数入力](https://sourceware.org/glibc/manual/latest/html_node/Numeric-Input-Conversions.html)・[fortify](https://sourceware.org/glibc/manual/latest/html_node/Source-Fortification.html)です。

`module-readable-c`も同じmoduleモデルを使います。
構造ASTの全Stepから始めた次命令・条件・代入を独立検査します。
描画後のCは、途中PCへの再入を含む具体状態で比較します。
Cの呼出しから戻った後は、実stackから読み出したPCと継続先を照合します。
一致すれば関数内を進め、別の戻り先ならCのframeを離れてゲストPCから再開します。
`NV_HOST_DEPTH_LIMIT`は1〜256、既定は64です。上限ではゲストの命令・RAM・レジスタを変更せずにframeを離れます。
この経路も、全レジスタ・RAM・PC・fault・予算・命令開始数を維持します。

`module-locals-c`は同じ観測契約を使います。
元の代入を順番に実行し、成功した各レジスタ書込みを直ちにゲスト状態へ反映します。
途中PCではその命令の生存値を復元し、通常CALLの継続時にも保存値を含めて実レジスタから読み直します。
分岐のφコピーは元の条件を保存してから適用します。構造化した制御が再評価する条件は、同じRAMとレジスタを参照します。
このモデルのRAM readの観測対象は、返る値とfaultです。
追加の局所変数領域に応じてホスト深度を最大256、目安32768個の64-bit保存先へ抑え、同じ途中再開経路を使います。
最大の単一frameはこの目安を超える場合があり、実際のホストstack量はCコンパイラにも依存します。
