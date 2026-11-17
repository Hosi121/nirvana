# 機械語とCLI

Nirvanaは、指定した関数の機械語を[ELF reader](../src/elf.rs)で切り出し、
[x86-64 decoder/lifter](../src/x86/mod.rs)でIRへ変換します。
関数はシンボル名または入口アドレスで指定します。後続の処理は[設計](architecture.md)を参照してください。

## 入力

ELF入力はELF64・little-endian・`EM_X86_64`・`ET_REL`のオブジェクトファイルです。
名前と正のサイズを持つ`STT_FUNC`シンボルを使い、既定名は`fixture`です。
対象関数の再配置は入力時に検査し、未解決のREL/RELAがあれば位置と種類をエラーに出します。

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
| 整数演算 | 算術・bit演算・シフト・ROL/ROR、明示オペランドのIMUL |
| 条件と分岐 | 直接JMP/Jcc、SETcc、CMOVcc |
| スタックと境界 | 64-bit PUSH/POP/LEAVE、RET |
| byte/bit操作 | 32/64-bit BSWAP、16/32/64-bitレジスタのBT |
| その他 | NOP、ENDBR64 |

部分レジスタとCF/ZF/SF/OF/PFをIRへ展開します。
条件式で使うフラグは、全到達経路で定義されたものを受理します。
CMOVのメモリsourceは、条件の真偽にかかわらず読み込みます。
RETではRSPを進め、RAXを対象関数の返り値として実行を終えます。

拡張予定の範囲:

| 分野 | 今後の対象 |
| --- | --- |
| コード画像 | ET_EXEC/ET_DYN、PE、関数境界の推定、リンクと再配置の解決 |
| 関数間制御 | CALL、間接JMP、戻り先の探索 |
| 命令と環境 | SIMD、除算、memory BT・BTS/BTR/BTC、FS/GS base |

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
