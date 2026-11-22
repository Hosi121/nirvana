# CLIと対応範囲

Nirvanaは、指定した関数の機械語を[ELF reader](../src/binary/elf.rs)で切り出し、
[x86-64 decoder/lifter](../src/binary/x86/mod.rs)でIRへ変換します。
関数はシンボル名または入口アドレスで指定します。後続の処理は[設計](architecture.md)を参照してください。

## 入力

| 入力 | 入口と用途 |
| --- | --- |
| ELF64 little-endian x86-64（`ET_REL` / `ET_EXEC` / `ET_DYN`） | 単一関数は名前と正のサイズを持つ`STT_FUNC`を使用。既定は`fixture` |
| リンク済みELFの`module-*` | 既定の`main`、`--symbol NAME`、または`--entry ADDRESS`から複数関数を読み込む |
| `--raw`のbyte列 | `--base`がコード先頭、`--entry`が領域内の入口。ゲストメモリの配置は実行APIで指定 |

`module-*`の数値入口はリンク時の仮想アドレスです。PIEのbiasはローダが加算します。
通常ELFは固定アドレス、PIEは既定bias `0x10000`を使います。APIの`linked_elf::LinkedOptions`ではbiasとstack容量を指定できます。
strip入力には実行可能なファイル範囲と照合した`.eh_frame`のFDE範囲を使い、サイズ付き関数シンボルを優先します。
FDEは関数の一部の場合もあるため、合成名`sub_ADDRESS`を持つ連続コード領域として扱います。
`linked_elf::load_at`・`module_ir::lift_elf_at`は数値入口に対応し、範囲の根拠とFDE位置を`FunctionOrigin`に保持します。

リンク済み画像ではsegment・BSS・動的再配置・GOTを読み、PLTを実命令とimportから照合します。
`effects-*`は単一関数と`puts`、`module-*`は内部・間接CALL・RETとPOSIX importを扱います。
初期状態はロード直後のモデル画像です。疎なRAM、stream binding、TLS、外部効果の規則は[実行モデル](equivalence.md#複数関数とposix)にあります。

デコーダは入口から直接辺と継続先をたどり、命令先頭・範囲・必要byteを検査します。
表の初期値から追加命令を発見し、動的移転は現在のRAMから評価します。
`module-jumps`は候補・読取り位置・範囲のヒントと未知の残余を表示し、探索上限に達した分岐を`context_limited_branches`へ記録します。

## 命令

主な対応形式は次のとおりです。個々の形式は[decode.rs](../src/binary/x86/decode.rs)にあります。

| 命令群 | 対応形式 |
| --- | --- |
| 移動とアドレス | 8/16/32/64-bit MOV、MOVZX/MOVSX/MOVSXD、CBW/CWDE/CDQE、CWD/CDQ/CQO、LEA、XCHG |
| 整数演算 | 算術・bit演算・シフト・ROL/ROR、即値SHLD/SHRD、暗黙オペランドのMUL・IMUL、明示オペランドのIMUL |
| 条件と分岐 | 直接JMP/Jcc、SETcc、CMOVcc |
| スタックと境界 | 64-bit PUSH/POP/LEAVE、RET |
| byte/bit操作 | 32/64-bit BSWAP、16/32/64-bitレジスタのBT |
| メモリのbyte順変換 | 16/32/64-bit MOVBE load/store |
| その他 | NOP、ENDBR64 |

部分レジスタとCF/ZF/SF/OF/PFをIRへ展開します。
条件式で使うフラグは、全到達経路で定義されたものを受理します。
即値SHLD/SHRDは、mask後のcountがオペランド幅以下の形式を扱います。
`module-*`ではNOTRACK付きの近距離間接CALL/JMPも扱います。CETの追跡状態は実行モデルの追加対象です。
`module-*`のTLS guard profileは、`FS:0x28`を64-bit MOV・ALU sourceとして読みます。
初期guardと通常RAMを介した書換えの規則は[実行モデル](equivalence.md)にあります。
`module-*`は8/16/32/64-bitのDIV/IDIVを、sourceのLoadとdivide error（#DE）を持つ命令として実行します。
商・剰余・部分レジスタと停止位置の規則は[実行モデル](equivalence.md)にあります。
`module-*`のSTOS・MOVSは8/16/32/64-bit、REP（F3）、CLD／STDを扱い、64-bitのアドレスとcountを使います。途中faultまでの書込みとcount・pointerの進捗を保持します。
仕様は[Intel SDM Vol.1 §18.3.1](https://cdrdv2-public.intel.com/843827/253665-sdm-vol-1-dec-24.pdf)と、[命令リファレンス](https://cdrdv2-public.intel.com/782156/325383-sdm-vol-2abcd.pdf)を参照してください。
CMOVのメモリsourceは、条件の真偽にかかわらず読み込みます。
RETではRSPを進め、RAXを対象関数の返り値として実行を終えます。

拡張予定の範囲:

| 分野 | 今後の対象 |
| --- | --- |
| コード画像 | PE、関数境界の推定、汎用的なリンク・import解決 |
| 関数間制御 | 関数境界の推定、呼出し規約・プロトタイプの回復、追加の外部効果 |
| 命令と環境 | SIMD、memory BT・BTS/BTR/BTC、FS/GS base、追加のCPU例外 |

## CLI

```sh
cargo run -- FILE.o --symbol fixture --emit readable-c
cargo run -- FILE.bin --raw --base 0x1000 --entry 0x1000 --emit ir
cargo run -- STRIPPED_ELF --entry 0x401200 --emit module-readable-c
```

| オプション | 内容 |
| --- | --- |
| `--help` / `-h` | 引数一覧 |
| `--symbol NAME` | ELFの関数名。既定は`fixture` |
| `--raw` | コードのbyte列を入力 |
| `--base ADDRESS` | raw領域の先頭。既定は0 |
| `--entry ADDRESS` | raw領域の入口、または`module-*`でのリンク時の領域入口 |
| `--emit c` | 全レジスタ形式のC。既定の出力 |
| `--emit ssa-c` | 検査済みの局所値・φの辺上コピーと、全レジスタへの書込みを持つC |
| `--emit readable-c` | 値引数、局所変数、メモリviewを使うC |
| `--emit middle-ir` | 評価領域ごとの不変な値、根拠付きの既知Load、Store、保存場所のSSA版、CFGを出力 |
| `--emit middle-c` | Middle IRの検査付きメモリ値回復を既存のreadable Cと比較し、同じ引数で小さい出力を選択 |
| `--emit types` | SSA値の幅・使用制約と、フィールド・配列の候補をJSONで出力 |
| `--emit record-types` | フィールド配置・ポインタの型互換性から構造体候補をC11の宣言で出力 |
| `--emit references` | ELFの参照先・文字列候補・外部呼出しの引数レジスタをJSONで出力 |
| `--emit effects-c` / `effects-ir` | `puts`モデル付きの実行可能C／明示的なCALLを持つIR |
| `--emit effects-readable-c` | 命令ごとの予算・fault・CALLを保った構造化C |
| `--emit module-c` / `module-ir` | 複数関数の実行用C／CALL・動的RETを持つIR。既定の入口は`main` |
| `--emit module-jumps` | 初期画像のジャンプテーブル候補、範囲のヒント、残る未知の分岐先をJSONで出力 |
| `--emit module-readable-c` | 名前付きC関数・構造化した制御・検査付きの途中再開を持つ複数関数C |
| `--emit module-locals-c` | 生存範囲を共有する局所変数・φコピー・途中再開用の値復元を加えた複数関数C |
| `--emit module-values` | レジスタSSA・生存範囲・MemorySSAの世代とLoadへの書込み候補をJSONで出力 |
| `--run-effects RESULTS` | 指定したint返り値列でモデルを実行し、出力byte列を標準出力へ送る |
| `--emit ir` / `decoded` | IR／デコード済み命令のテキスト |
| `--emit cfg` / `structured-cfg` | 元CFG／対応検査済みASTのグラフをDOT出力 |
| `--run A,B,C,D` | fixture ABIで実行し、返り値と最終状態4要素を出力 |
| `--steps N` | runの元命令数の上限。既定は100000 |
| `--no-coalesce-locals` | readable-c/middle-cで局所値ごとに保存場所を確保 |
| `--verify-reduction PATH` | readable-cのIR還元を指定のZ3で検査 |

`module-c`はstandalone C11です。`cc -std=c11 -O2 server.c -o server`でコンパイルし、POSIX importをLinux x86-64 libcへ接続できます。
入口はRSP以外をゼロ初期化し、独自の入力には`Module::initial_registers`と`Program::run`を使います。
命令・import予算は`NV_INSTRUCTION_LIMIT`・`NV_IMPORT_LIMIT`で指定します。[HTTP fixture](../tests/fixtures/http-server/README.md)に全体の実行例があります。

`module-readable-c`は名前付き関数と構造AST、`module-locals-c`はさらに生存範囲で共有した`v_N`の局所変数を使います。
途中PCからの再入、成功したCALL/DIV/STOS/MOVS後の値復元、レジスタ形式への関数単位のfallbackは[設計](architecture.md#cの描画と途中再開)にあります。
変数数・復元数を標準エラーへ、fallback理由をCのコメントへ出力します。

strip入力の範囲読取りはCIE v1/v3、32-bitレコード長、絶対／PC相対の対応ポインタ表現を扱います。
範囲の重なり、実行可能なファイルbyteとの対応、逆参照と整数overflowを検査し、位置付きのエラーを返します。
CFIは領域発見のメタデータとして読み、命令の復号・フラグ・実行状態には既存の検査を適用します。
extended長、追加のCIE形式、`.eh_frame`内の動的再配置、section tableを持たないstrip入力の範囲発見は今後の対象です。
関数名や型、プロセス起動時の`main`の発見は、それぞれ独立した解析として扱います。

アドレスとrunの入力値は10進数または`0x`付き16進数です。
`--no-coalesce-locals`と`--verify-reduction`はreadable-c出力時の設定で、`--run`は実行用の別モードです。
本体は標準出力へ、還元の検査結果と入力エラーは標準エラーへ出力します。

`--run`は`0x1000`から64 KiBをゼロ初期化し、`0x2000`に入力状態を置きます。
RDI=`0x2000`、RSP=`0x10000`、その他のレジスタはゼロです。
独自の引数・メモリ配置には[実行API](equivalence.md)へ初期状態を渡します。

## 生成C

メモリを使う`--emit c`の関数:

```c
uint64_t nirvana_fn(uint64_t *r, uint8_t *memory, uint64_t base, uint64_t size);
```

x86フロントエンドの`r`は32要素で、RAX=`r[0]`、RSP=`r[4]`、RDI=`r[7]`です。
メモリ操作を持つ関数には、ゲストbyte配列とそのbase・sizeを渡します。それ以外の関数は`r`を受け取ります。

readable-cの`nirvana_readable`は、必要な入口レジスタを`uint64_t`の値引数として受け取ります。
対応は生成Cのコメントに記載します。メモリ操作を持つ関数には、同じ`memory, base, size`も渡します。
メモリhelperはアクセス範囲を検査し、無効なアクセスで`abort`します。
詳しい[実行モデル](equivalence.md)と[検証方法](verification.md)も参照してください。

## 型制約の確認

```sh
cc -O2 -c tests/fixtures/types/record-index.c -o /tmp/nirvana-record.o
cargo run -- /tmp/nirvana-record.o --emit types
```

`values`はSSA値の上位ビット境界と直接・伝播後の使用、`accesses`は幅・位置・参照形状を示します。
`layout_candidates`はこれらをまとめたフィールド・配列の候補です。重なるアクセスは`overlaps`に残します。
`maximum_bits`は値を格納できる上位ビット境界、`storage_bits_candidate`はその候補幅です。
元の型宣言やオブジェクト全体の大きさは、候補を評価する次の段階で扱います。

`record_shapes.constraints`の`kind: "memory"`は、完全な64-bit Storeからの読戻しに基づく型互換性です。`site`は書込み位置、`to`はLoad結果のSSA値IDを示します。
`record_shapes.memory_flow`は検査した直接64-bit Load数（`considered_loads`）と、全経路の書込み元を確認できた数（`complete_loads`）を表示します。後者にはRHSから型関係を取り出せないStoreも含みます。
解析上限では`status: "unavailable"`と理由を残し、copy・φ・stackから得た候補を出力します。[record-memory.c](../tests/fixtures/types/record-memory.c)が最適化後の読戻しの例です。

## 文字列と呼出し参照

```sh
cc -O2 -c tests/fixtures/references/hello.c -o /tmp/nirvana-hello.o
cargo run -- /tmp/nirvana-hello.o --emit references
```

この例では、再配置から`puts`と文字列のアドレスを解決し、
`calls[].source_hint`に`puts("Hello, world!")`を表示します。
参照先はセクション番号とオフセット、外部シンボルは名前とaddendで保持します。
文字列アドレスのPC相対・絶対32/64bit参照、GOT経由の呼出し、末尾JMPによる呼出しを扱います。

`literals`は読取り専用セクションのNUL終端ファイルbyte列です。
`references`には元の再配置・命令位置・解決先、`calls`にはSysV ABIの引数候補レジスタを記録します。
分岐・ループの全流入が同じ参照先を持つ場合に引数を特定し、CALL後はABIの破壊レジスタを更新します。
`source_hint`はこの静的な対応の表示で、外部呼出しの効果は`call_effects: "opaque"`として保持します。
`effects-ir`・`effects-c`では、この参照先の照合を実行モデルへ接続します。

## putsモデルの実行とC出力

```sh
cc -O2 -c tests/fixtures/references/hello.c -o /tmp/nirvana-hello.o
cargo run -- /tmp/nirvana-hello.o --run-effects 7
cargo run -- /tmp/nirvana-hello.o --emit effects-c > /tmp/nirvana-hello.c
cc -std=c11 -Wall -Wextra -Werror -pedantic -O2 -c /tmp/nirvana-hello.c
```

`--run-effects 7`は`Hello, world!`と改行を出力し、返り値7を標準エラーへ報告します。
`effects-readable-c`は制御構造とともに、RIP相対アドレスなどから得た初期文字列をコメントへ表示します。
CALLは呼出し時のゲストRAMを読み、文字列の書換えを反映します。
複数の呼出しには`--run-effects 3,7`のように結果入力を列挙します。
このCLIは全文出力、指定int値を下位32bitに持つRAX、他の破壊値0を入力とします。
GPレジスタの初期値は0、RSPは配置したstackの入口です。
詳細な結果入力と予算には[実行API](equivalence.md#putsの外部効果)を使います。

生成Cは`nirvana_effect_init(r, memory)`で再配置済みの初期imageとレジスタを用意し、
`nirvana_effect_run(r, memory, base, size, &effects)`で実行します。
`struct nirvana_effects`に結果入力列、独立した出力bufferと容量、各予算を渡します。
終了status・返り値・出力長・消費数・faultは同じ構造体へ返します。
レジスタ、ゲストRAM、出力buffer、結果入力列には、それぞれ独立したホスト領域を用意します。

オブジェクトの配置先は`loader::LoadOptions`で指定できます。alignment・BSS・RELA・GOTと呼出し証拠を照合し、実行時にもGOTの値を検査します。
RAM容量と動的移転の規則は[実行モデル](equivalence.md)を参照してください。
