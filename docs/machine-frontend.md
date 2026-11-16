# 機械語からIRまで

## 到達点

既知の一関数について、実際の機械語を自作デコーダで読み、実行可能IRへ変換し、
既存のCFG構造化とC生成へ渡せるようにしました。
Ghidra、Capstone、LLVMや外部逆アセンブラの出力は実装の依存にも入力にも使いません。
Rust標準ライブラリのみです。Cコンパイラはfixtureの作成と実行比較に使います。

```text
元C ── cc ──> ELF .o ── 自作ELF reader ──> 関数のバイト列
                                               ↓
                                        自作x86-64 decoder
                                               ↓
                                      フラグとメモリを含むIR
                                               ↓
                                       CFGの構造化 → C
                                               ↓
                                         cc → 実行比較
```

## 使い方

```sh
python3 tools/build_fixtures.py
cargo run -- target/c-fixtures/cc-0/O2/diamond.o --run 12,2,3,4
cargo run -- target/c-fixtures/cc-0/O2/diamond.o --emit decoded
cargo run -- target/c-fixtures/cc-0/O2/diamond.o --emit ir
cargo run -- target/c-fixtures/cc-0/O2/diamond.o --emit cfg
cargo run -- target/c-fixtures/cc-0/O2/diamond.o --emit c
cargo test --test machine_pipeline -- --nocapture
```

最初の実行結果は`32 12 32 3 4`です。順に返り値と状態配列4要素を表します。
既定の関数名は`fixture`で、`--symbol NAME`で選択します。
生のバイト列を読む場合は`--raw --base ADDRESS --entry ADDRESS`も使えます。
`--steps`はIRで実行する元命令数の上限です。

`--run`はこのリポジトリのfixture ABI専用です。32個のIRレジスタと64 KiBのguestメモリを用意し、
SysV ABIのRDIに状態配列のguestアドレス、RSPにguestスタック先頭を設定します。
汎用の関数引数・呼び出し規約の推定器ではありません。

レジスタ配列の0..15はRAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8..R15です。
16..20はCF, ZF, SF, OF, PF、21以降は変換用の一時レジスタです。`--emit c`の生成Cへは32要素の配列を渡してください。
`--emit readable-c`は必要な入力レジスタを値引数にした別インターフェースです。

## ELFの範囲

ELF64・little-endian・EM_X86_64・ET_RELに限定します。
STT_FUNCの名前と宣言済みサイズを読み、section先頭からの位置とサイズに従ってバイト列を切り出します。
関数境界の発見、サイズ0の関数、stripされたファイル、実行形式ET_EXEC/ET_DYN、PEなどは未対応です。

REL/RELAは、対象関数を変更する再配置を相対offset・種別・参照シンボル名として保持します。
現在のフロントエンドは一件でもあれば拒否します。外部参照や定数のアドレスを0として処理することはありません。
ヘッダ・table・section・stringの範囲はchecked arithmeticで検査し、曖昧な関数名や境界を跨ぐ再配置もエラーにします。

ELF readerはサブエージェントが独立コピーで実装し、親が差分を確認して統合しました。
公開契約と統合結果は[作業記録](agent-work/elf-reader/verification.md)に残しています。

## x86-64の範囲

関数の入口から直接分岐と継続先をたどって、到達する命令をデコードします。
return後のpaddingなどを無理に命令化しません。命令の途中への分岐、重複する命令列、
関数外への制御移転、切断された入力、15バイトを超える命令はエラーです。

主な対応対象は次の通りです。すべてのprefixや命令形式に対応するという意味ではありません。

- REX、ModR/M、SIB、符号付き変位、RIP相対アドレス。
- 8/16/32/64-bitのMOV、MOVZX/MOVSX/MOVSXD、LEA、XCHG。
- ADD/ADC/SUB/SBB/CMP、AND/OR/XOR/TEST、INC/DEC/NEG/NOT。
- SHL/SHR/SAR、明示オペランド形式のIMUL。
- 直接JMP/Jcc、SETcc、CMOVcc。
- 64-bitのPUSH/POP/LEAVEと根のRET、NOP、ENDBR64の通常データフロー上の扱い。

部分レジスタの読み書きを明示します。32-bit書き込みは上位を0にし、8/16-bit書き込みは他のビットを残します。
REXの有無によるAH等とSPL等の違い、即値の符号拡張、命令末尾基準の相対アドレスを扱います。
メモリやオペランドを先に一時レジスタへ保存し、更新先がアドレス計算にも使われる場合の順序を保ちます。

CF/ZF/SF/OF/PFはIRの専用レジスタへ展開します。入口のフラグは不明とし、全到達経路で
定義されていると確認できたフラグだけをJcc等で使用できます。IMULの未定義フラグや、
動的シフトで確実性を示せないフラグは黙って0扱いせず拒否します。この解析は保守的です。

CMOVのメモリsourceは条件が偽でも読みます。これは[命令仕様](https://cdrdv2.intel.com/v1/dl/getContent/671199)に従い、
単純な遅延評価の条件式へ置き換える前にloadを分離しています。
命令形式・各フラグは[Intel SDM](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)のVolume 2を参照しました。

現在はCALL、間接JMP、SIMD、除算、segment baseを使うアクセスなどを拒否します。
RETは対象関数を終了してRAXを返す根のreturnとして扱い、RSPを更新します。
戻り先の探索、呼び出しスタック全体、CET・例外・割り込み等の実行環境はモデル化していません。

## IRとメモリ

`Place`はレジスタとメモリの書き込み先を区別します。`Expr::Load`は1/2/4/8バイトの
little-endian load、`Expr::Select`は選択された側だけを評価する条件式です。
メモリは一つの有限なguestアドレス範囲を表すbyte配列で、hostのポインタを直接操作しません。
範囲外アクセスと64-bitアドレスを跨ぐアクセスは`MemoryAccess`エラーです。

```rust
program.execute_with_memory(&registers, guest_base, &memory_bytes, step_limit)
```

成功時には返り値・全レジスタ・命令アドレスのtrace・最終メモリを返します。
構造化後も同じ初期状態と上限で比較します。行き先が同じ条件分岐でも、条件loadが失敗し得るため、
その評価は`Evaluate`ノードに残します。

メモリを使うIRからのC関数は次の形です。

```c
uint64_t nirvana_fn(uint64_t *r, uint8_t *memory, uint64_t base, uint64_t size);
```

register-only IRの従来の一引数形式は維持しています。Cのメモリアクセスはbyte単位で行い、
アラインメントやhostエンディアンに依存させません。無効な範囲はabortします。
IRと生成Cの実行比較は有効なguestメモリの入力で行い、CPU例外全体との同値性は主張しません。

返り値と全ゲストメモリを観測対象にする別モード `--emit readable-c` もあります。
こちらは不要なフラグと補助値を除き、値引数とローカル変数でCを生成します。
契約と検証方法は[readable-c.md](readable-c.md)を参照してください。

## 検証結果

GCC 13.3.0、`x86_64-linux-gnu`、従来のfixtureと同じC11・`-fno-lto`・`-O0/-O2`を使いました。
デコーダに都合のよい追加の最適化無効化オプションは入れていません。

| 検査対象 | 結果 |
| --- | --- |
| 元C 20例×2設定 | 40構成中33構成を機械語からIRへ変換 |
| O0 / O2の内訳 | 17/20、16/20 |
| 元C・IR・機械語から再生成したC | 33構成×63入力、計2,079ケースで返り値と状態配列が一致 |
| 構造化できた機械語CFG | 32構成。独立したASTグラフの対応検査を通過。全レジスタ・全メモリ・命令traceもIRと一致 |
| 構造化未対応だがC出力できたCFG | 1構成。goto付きCで同じ実行比較に成功 |
| 還元IR・読みやすいC | 同じ2,079入力。IRは全メモリとtrace、Cは状態配列と全メモリのダイジェストも一致 |
| 全体 | 通常273テスト＋別途SMT9テスト、Clippy警告ゼロ、rustfmt確認 |

現在の最初の拒否理由は次の通りです。再配置を解決した後にも未対応命令が残る可能性があります。

| fixture | O0 | O2 |
| --- | --- | --- |
| `switch` | table参照の再配置 | table参照の再配置 |
| `array-walk` | stack protectorの外部参照 | stack protectorの外部参照 |
| `call-chain` | `fixture_mix`への外部呼び出し | `fixture_mix`への外部呼び出し |
| `nonlocal-exit` | 成功 | `.LC0`への定数参照の再配置 |

算術フラグは8/16/32/64-bitについて広い整数型を使った別計算と照合し、IMULのsigned overflowも
`i128`の計算と照合します。さらに、overflowを返り値へ反映する機械語とnativeコンパイラの
overflow検出を49入力×O0/O2で比較し、Cのhigh-multiply実装も検査しています。
ELFの切断・1バイト変異、固定シードの命令入力2,048個の各切断長、不正prefixや不正分岐も検査します。

これは限定した命令とfixtureでの検証です。任意のバイナリを扱う完成したデコンパイラや、
既存製品より優れた復元精度を実証したものではありません。次は再配置・データ配置・呼び出し・間接分岐と、
レジスタやフラグが残る出力を変数へ整理するSSA解析が必要です。
