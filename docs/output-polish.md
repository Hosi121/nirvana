# 最終C出力の改善

今回の区切りは、独立した3個のC fixtureを追加し、同じ機械語・観測契約で関数本文を読みやすくすることです。
基準は`9c56366`、実装は`c3d1687`です。AIによる後処理は使っていません。

## 実際の出力

`diamond -O2`の計算部分は次のようになります。周囲には入力ビューの宣言とchecked-memoryヘルパーがあります。

```c
uint64_t value;
value = read64(input.field_0);
value = value <= 9 ? value * 3 : value + 20;
write64(input.field_8, value);
return value;
```

`readN`と`writeN`は同じlittle-endian guest memoryと境界検査を呼ぶC11マクロです。
整数アドレスもビューも受け取ります。型選択の`_Generic`では引数を評価せず、実際の変換関数へ一度だけ渡します。
生成関数の直後でundefし、後ろに連結するharnessへマクロを残しません。
添字は`read64(element(input.base, index, 8))`の形になります。
負のoffsetやstrideも、uint64_tの仮引数へ変換して元のmodular arithmeticを保ちます。

`input_address`・`stack_base`・`valueN`は役割に基づく生成名です。元ソースの名前を復元したという意味ではありません。
フィールドも整数アドレスのdescriptorであり、元のC構造体型や非aliasの証明ではありません。
ライブラリは`ReadableOptions { compact_memory: true, ..Default::default() }`でこの表示を選べます。
CLIの`--emit readable-c`はこの表示を使います。`--emit c`の全レジスタ入出力契約は維持します。

## 式と制御の整理

`presentation::normalize`は、既存の`ValueWidths`が保証するunsigned幅を使い、
冗長なmask、既知のゼロ上位部分、neutralな演算、純粋な同一オペランドの演算を除きます。
すべての構文上のLoadを保持し、遅延Selectを含めて削除・複製・並べ替えません。
入力引数はuint64_tのままで、全観測値に通用しない狭い型を仮定しません。
65,536式ノード・深さ128の上限では元の式を反復的にコピーして返します。

表示用Programのコピーをビュー・使用値・保存場所の解析にも使い、元IRは変更しません。
構造の対応検査は元の還元IRとNode ASTに対するものです。
その後のC表示、今回の幅依存の式変換、guard配置全体を証明するcertificateではありません。
代入・storeの保存幅で切り捨てるmaskはC表示で省き、複合代入では必要なuint64_t昇格を演算前に残します。

分岐の片側がreturn・break・continueなら、guardとして先に配置して後続のelseを減らします。
goto fallbackでは、代入も条件評価もない無条件の中継ブロックだけを畳み、隣に続く行き先はfallthroughさせます。
条件が同じ行き先へ進む場合も評価を残し、空の循環は自己ループする代表を保持します。
16,384ブロック・262,144命令を超えるlayoutや不正な辺では部分的な計画を採用しません。
元の実行IRのtraceとstep limitは維持しますが、C表示での空ブロック縮約に同じ命令数を要求しません。

独立レビューでは、幅の簡約で露出した`x ^ x`をループ表示時だけさらに簡約すると、
使用変数の解析後に最後の参照が消え、生成Cがunused-but-set警告でコンパイル失敗する例が見つかりました。
一般の代数簡約を表示段階から外し、比較の真偽反転はオペランド順序と依存を保つ変換だけに限定しました。
自己比較を含む純粋な同一オペランドの簡約は依存解析前に行い、tautological-compare警告も避けます。
通常分岐とループ、Xor/Eq/Ult/Ule、正常・fault経路、二つの表示形式のnative回帰テストを追加しています。

## 同じ入力での比較

GCC 13.3.0、x86_64-linux-gnu、C11・Wall/Wextra/Werror/pedantic・fno-lto・O0/O2を共通にしました。
既存20ソースとrecovery 6ソースの52構成中、同じ45構成を比較しています。
再配置が未対応の7構成は両版とも拒否し、対応数の向上とは扱いません。
前後それぞれ45本の生成Cを同じ条件でコンパイルしています。

| 計測 | 変更前 | 変更後 |
| --- | ---: | ---: |
| 関数本文のトークン合計（コメント・空白を除外） | 20,937 | 15,316 |
| 関数全体のbyte数（引数・宣言・コメントを含む） | 89,125 | 76,623 |
| mask演算 | 231 | 96 |
| 明示的な整数cast | 46 | 33 |
| goto | 45 | 14 |
| ラベル | 33 | 12 |
| 共通ヘルパー込みのCファイルbyte数 | 165,090 | 217,709 |

短いメモリ構文の共通ヘルパーを足すため、ファイル全体は増えます。
本文の短さだけで元ソースとの近さ、一般の復元精度、処理速度を示すものではありません。

| 個別例 | 変更前 → 変更後 |
| --- | --- |
| `byte-fields O2` | mask 28 → 4 |
| `irreducible O0` | goto 9 → 2、label 7 → 2 |
| `three-entry-goto O0` | goto 20 → 5、label 15 → 4 |
| `three-entry-goto O2` | goto 16 → 7、label 11 → 6 |
| `early-exit-chain O2` | 最大字下げ24 → 12 spaces |

## fixtureと検証

追加した`three-entry-goto`は有限な3入口循環、`packed-update`は異なる幅と重なるbyte更新、
`early-exit-chain`は添字・複数の早期脱出を含みます。新しい命令や失敗をskipする例外は足していません。

| corpus | native/IR/readable比較 |
| --- | --- |
| 既存20ソース | 33/40構成 × 63入力 = 2,079 |
| recovery 6ソース | 12/12構成 × 69入力 = 828 |
| 固定seedの生成8ソース | 16/16構成 × 67入力 = 1,072 |
| 合計 | 61/68構成、3,979入力比較 |

元CとIRでは返り値・4状態ワードを照合します。再生成CとIRではstackを含む64KiB全体のdigestも比較します。
fault専用テストは最初に失敗したアドレスと停止前の全メモリを比較します。
生成16構成はUBSan付きでも63入力ずつ、計1,008比較が一致し、診断はありませんでした。
式の専用生成テストは480形/幅profileについて216,000回のIR実行比較も行います。

全282テスト（通常273＋任意SMT9）、Clippy警告ゼロ、rustfmtを確認しました。
SMTは既存のIR還元・幅/添字などのモデルに対する検査で、今回のC出力全体の証明ではありません。
間接分岐、再配置、関数呼び出し、ソース型の復元は今回の対応範囲に加えていません。

## 再現と成果物

比較用CLIを別の一時ディレクトリで`9c56366`からビルドし、現在のCLIと比較します。

```sh
cargo build --bin nirvana
python3 tools/compare_readable_output.py --before /path/to/baseline/nirvana
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --all-targets -- --include-ignored
NIRVANA_RECOVERY_ARTIFACTS=target/output-polish/generated cargo test --test generated_recovery
python3 tools/validate_recovery_artifacts.py --artifacts target/output-polish/generated --out target/output-polish/ubsan
cargo clippy --all-targets -- -D warnings
cargo fmt --check
```

`target/output-polish/comparison.json`にコンパイラ情報、フラグ、ソース・機械語・両CLIのSHA-256と個別値を残します。
同じ場所に元オブジェクト、前後のC全体・関数部分、全テストログ、UBSan結果があります。
成果物はGit管理せず、生成道具・fixture・検証・設計をコミットしています。
