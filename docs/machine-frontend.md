# 機械語フロントエンドと CLI

既知の一関数を [ELF reader](../src/elf.rs) で切り出し、[x86-64 decoder/lifter](../src/x86/mod.rs) で IR へ変換する。
関数境界や呼び出し規約の推定は行わない。[アーキテクチャ](architecture.md)に後続の流れを示す。

## 入力の範囲

ELF 入力は ELF64・little-endian・`EM_X86_64`・`ET_REL` に限定する。
名前と正のサイズを持つ `STT_FUNC` シンボルが必要で、既定名は `fixture`。
対象関数にかかる REL/RELA が一件でもあれば拒否する。リンクや再配置の解決は行わない。
実行形式 `ET_EXEC`/`ET_DYN`、サイズ不明の関数、PE は対象外である。

`--raw` はシンボルの代わりにコード領域の byte 列を受け取る。
`--base` はコード先頭のアドレス、`--entry` はその領域内の入口を指定する。
この配置と、実行時の guest memory の配置は別である。

入口から直接分岐と継続先をたどり、到達する命令だけを読む。
命令途中への分岐、重複する命令列、コード領域外への転送、切断された命令はエラーになる。
return 後の padding を一律に命令として扱わない。

主な対応範囲は整数命令の次の形式である。個々の形式の実装は [decode.rs](../src/x86/decode.rs) を参照。

- 8/16/32/64-bit MOV、MOVZX/MOVSX/MOVSXD、LEA、XCHG、算術・bit 演算・シフト・ROL/ROR。
- 明示オペランドの IMUL、直接 JMP/Jcc、SETcc、CMOVcc。
- 64-bit PUSH/POP/LEAVE、RET、NOP、ENDBR64。

部分レジスタと CF/ZF/SF/OF/PF を IR に展開する。
入口のフラグは未定義として解析し、全到達経路で定義を確認できないフラグの読出しは拒否する。
CMOV のメモリ source は条件が偽でも読み込む。
CALL、間接 JMP、SIMD、除算、FS/GS base を使うアクセスなどは未対応。
RET は RSP を進めて RAX を返す対象関数の終了であり、戻り先の探索や例外処理はモデル化しない。

## CLI

```sh
cargo run -- FILE.o --symbol fixture --emit readable-c
cargo run -- FILE.bin --raw --base 0x1000 --entry 0x1000 --emit ir
```

各モードとも先に入力検査と IR への変換を行う。詳細な引数処理は [main.rs](../src/main.rs) にある。

| オプション | 内容 |
| --- | --- |
| `--help` / `-h` | 引数一覧を表示 |
| `--symbol NAME` | ELF の対象関数。既定は `fixture` |
| `--raw` | ファイル全体をコードの byte 列として読む |
| `--base ADDRESS` | raw コードの先頭。既定は `0` |
| `--entry ADDRESS` | raw の入口。既定は base。base/entry は raw 専用 |
| `--emit c` | 全レジスタ形式の C。出力形式の既定値 |
| `--emit readable-c` | 値引数、局所変数、名前付き memory view を使う C |
| `--emit ir` / `decoded` | IR 命令 / デコード済み命令のテキスト |
| `--emit cfg` / `structured-cfg` | 元 CFG / 対応検査済み AST からのフローグラフを DOT 出力 |
| `--run A,B,C,D` | fixture ABI で実行し、返り値と最終状態4要素を出力 |
| `--steps N` | run の元命令数の上限。既定は `100000` |
| `--no-coalesce-locals` | readable-c の局所保存場所の共有を無効化 |
| `--verify-reduction PATH` | readable-c の IR 還元を Z3 で検査 |

アドレスと run の入力値は10進数または `0x` 付き16進数で指定できる。
`--no-coalesce-locals` と `--verify-reduction` は `--emit readable-c` 専用で、`--run` と併用できない。
定義 web 分割は保存場所の共有とは独立した前処理である。
還元の検査結果は標準エラー、C・IR・DOT などの本体は標準出力へ出す。

`--run` は `0x1000` から64 KiBをゼロ初期化し、`0x2000` に入力の状態配列を書き込む。
レジスタは RDI=`0x2000`、RSP=`0x10000` とし、その他はゼロから始める。
一般の引数渡しやデータ領域の再現には [ir.rs](../src/ir.rs) の実行 API へ初期状態を渡す。

## 生成 C のインターフェース

メモリを使う `--emit c` は次の関数と必要な helper を出力する。

```c
uint64_t nirvana_fn(uint64_t *r, uint8_t *memory, uint64_t base, uint64_t size);
```

この x86 フロントエンドの `r` は32要素。RAX=`r[0]`、RSP=`r[4]`、RDI=`r[7]` である。
メモリを使わない関数は `r` だけを受け取る。
readable-c の `nirvana_readable` は必要な入口レジスタを `uint64_t` の値引数にし、対応を C のコメントへ出す。
メモリを使う場合は末尾に同じ `memory, base, size` を受け取る。
どちらも caller が guest byte 配列を用意し、無効なアクセスでは生成 helper が `abort` する。
メモリ・fault の契約は[同値性](equivalence.md)、生成 C の検査方法は[検証ガイド](verification.md)を参照。
