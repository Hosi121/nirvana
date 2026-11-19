# 機械語とCLI

Nirvanaは、指定した関数の機械語を[ELF reader](../src/elf.rs)で切り出し、
[x86-64 decoder/lifter](../src/x86/mod.rs)でIRへ変換します。
関数はシンボル名または入口アドレスで指定します。後続の処理は[設計](architecture.md)を参照してください。

## 入力

ELF入力はELF64・little-endian・`EM_X86_64`のオブジェクト（`ET_REL`）、実行ファイル（`ET_EXEC`）、PIE（`ET_DYN`）です。
名前と正のサイズを持つ`STT_FUNC`シンボルを使い、既定名は`fixture`です。
実行IR・C生成では対象関数の再配置を検査し、解決が必要な参照を位置と種類で報告します。
`--emit references`では、元の再配置を使って文字列・シンボル・呼出し引数の対応を解析します。

リンク済みELFは`PT_LOAD`をゲストRAMへ配置し、BSSをゼロ初期化します。
`PT_DYNAMIC`の再配置を使ってPIEのデータポインタとGOTを解決し、実際のPLT命令とimportを照合します。
通常の実行ファイルは固定アドレス、PIEは既定bias `0x10000`を使います。
ライブラリAPIの`linked_elf::LinkedOptions`ではPIEのbiasとstack容量を指定できます。
選択した関数の整数処理と`puts`モデルを対象とし、内部CALL・他の外部関数は呼出位置付きで報告します。
初期状態はロード直後のモデル画像です。プロセス起動処理・constructor・実libcの内部状態は別の実行環境として扱います。
ゲストRAMのアクセス規則は[実行モデル](equivalence.md)に従います。

`--raw`ではコード領域のbyte列を入力します。
`--base`はコード先頭、`--entry`は領域内の入口アドレスです。
コードの配置と、実行APIに渡すゲストメモリの配置は個別に指定します。

デコーダは入口から直接分岐と継続先をたどります。
分岐先が命令先頭にあること、命令の範囲が整合すること、必要なbyteが揃うことを検査します。
解析対象は到達する命令列です。

## 命令

主な対応形式は次のとおりです。個々の形式は[decode.rs](../src/x86/decode.rs)にあります。

| 命令群 | 対応形式 |
| --- | --- |
| 移動とアドレス | 8/16/32/64-bit MOV、MOVZX/MOVSX/MOVSXD、LEA、XCHG |
| 整数演算 | 算術・bit演算・シフト・ROL/ROR、暗黙オペランドのunsigned MUL、明示オペランドのIMUL |
| 条件と分岐 | 直接JMP/Jcc、SETcc、CMOVcc |
| スタックと境界 | 64-bit PUSH/POP/LEAVE、RET |
| byte/bit操作 | 32/64-bit BSWAP、16/32/64-bitレジスタのBT |
| メモリのbyte順変換 | 16/32/64-bit MOVBE load/store |
| その他 | NOP、ENDBR64 |

部分レジスタとCF/ZF/SF/OF/PFをIRへ展開します。
条件式で使うフラグは、全到達経路で定義されたものを受理します。
CMOVのメモリsourceは、条件の真偽にかかわらず読み込みます。
RETではRSPを進め、RAXを対象関数の返り値として実行を終えます。

拡張予定の範囲:

| 分野 | 今後の対象 |
| --- | --- |
| コード画像 | PE、関数境界の推定、汎用的なリンク・import解決 |
| 関数間制御 | 任意の外部・内部関数のCALL、間接JMP、戻り先の探索 |
| 命令と環境 | SIMD、DIV/IDIV、暗黙オペランドのIMUL、memory BT・BTS/BTR/BTC、FS/GS base |

## CLI

```sh
cargo run -- FILE.o --symbol fixture --emit readable-c
cargo run -- FILE.bin --raw --base 0x1000 --entry 0x1000 --emit ir
```

| オプション | 内容 |
| --- | --- |
| `--help` / `-h` | 引数一覧 |
| `--symbol NAME` | ELFの関数名。既定は`fixture` |
| `--raw` | コードのbyte列を入力 |
| `--base ADDRESS` / `--entry ADDRESS` | rawの先頭／入口。既定は0／base |
| `--emit c` | 全レジスタ形式のC。既定の出力 |
| `--emit readable-c` | 値引数、局所変数、メモリviewを使うC |
| `--emit types` | SSA値の幅・使用制約と、フィールド・配列の候補をJSONで出力 |
| `--emit references` | ELFの参照先・文字列候補・外部呼出しの引数レジスタをJSONで出力 |
| `--emit effects-c` / `effects-ir` | `puts`モデル付きの実行可能C／明示的なCALLを持つIR |
| `--emit effects-readable-c` | 命令ごとの予算・fault・CALLを保った構造化C |
| `--run-effects RESULTS` | 指定したint返り値列でモデルを実行し、出力byte列を標準出力へ送る |
| `--emit ir` / `decoded` | IR／デコード済み命令のテキスト |
| `--emit cfg` / `structured-cfg` | 元CFG／対応検査済みASTのグラフをDOT出力 |
| `--run A,B,C,D` | fixture ABIで実行し、返り値と最終状態4要素を出力 |
| `--steps N` | runの元命令数の上限。既定は100000 |
| `--no-coalesce-locals` | readable-cで局所値ごとに保存場所を確保 |
| `--verify-reduction PATH` | readable-cのIR還元を指定のZ3で検査 |

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
複数の呼出しには`--run-effects 3,7`のように結果入力を列挙します。
このCLIは全文出力、指定int値を下位32bitに持つRAX、他の破壊値0を入力とします。
GPレジスタの初期値は0、RSPは配置したstackの入口です。
詳細な結果入力と予算には[実行API](equivalence.md#putsの外部効果)を使います。

生成Cは`nirvana_effect_init(r, memory)`で再配置済みの初期imageとレジスタを用意し、
`nirvana_effect_run(r, memory, base, size, &effects)`で実行します。
`struct nirvana_effects`に結果入力列、独立した出力bufferと容量、各予算を渡します。
終了status・返り値・出力長・消費数・faultは同じ構造体へ返します。
レジスタ、ゲストRAM、出力buffer、結果入力列には、それぞれ独立したホスト領域を用意します。

モデル付き読込みは割当てセクションのalignment、BSS、コード・データのRELA、GOTを扱います。
対応importは`puts`で、通常CALL・GOT経由・末尾CALLを実行します。
配置先は`loader::LoadOptions`で指定でき、RAMはpadding・GOT・stackを含めて16 MiBが上限です。
元オブジェクトの呼出し証拠と配置後の命令を照合し、実行時にもGOTの値を検査します。
