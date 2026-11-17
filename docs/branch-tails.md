# 分岐末尾の共有とcontinue側のカウンタ

基準は `8f94893`。今回の到達点は、構造が完全一致する分岐末尾を共有候補にし、
continueからループへ戻る条件にもカウンタの役割を見出せることです。
fixtureは `bfe7385`、解析は `58da6db`、C統合は `2ede974` にコミットしました。
元Cの文字列、AI整形、既存デコンパイラは使いません。

## 保持する条件

観測対象は返り値・checked guest memory全体・最初のモデル化されたfaultです。
条件の評価は分岐本体の前に一度実行し、Loadの順番、Selectの遅延評価、
fault以前の書込みを保ちます。両分岐が同じ処理だけになっても、条件をEvaluateとして残します。
純粋な条件も残すため、表示前の依存解析が見ていた読出しを消しません。

Stepの比較は、命令位置と逐次代入の全体を含めます。同じ変数名や表示文字列だけでは一致と扱いません。
命令位置を捨てると、その位置で証明したアドレスのviewを別経路へ誤って持ち出す可能性があります。
Return・Break・Continue・外側ループへの転送は、同じループ深さを維持して共有します。
元の実行IRと構造certificateは変更しません。certificateの対象は表示変換前のASTまでです。

`branch_tail::factor`はIfとLoopの内側から変換します。全Node・代入・式を先に検査し、
65,536要素、Node深さ64、式深さ128、構造比較work 262,144を上限とします。
超過時は途中結果を採用せず、元の表示用ASTへ戻します。

この共有候補と元のASTを、同じ名前・保存場所・幅・view・初期Factsで別々に描画します。
C本文が厳密に短くなり、最大の字下げが増えない場合に限って候補を採用します。
候補描画の失敗でも元の本文を使います。判定は関数全体に対して行うので、一つの候補が悪化すると
その関数内の共有全体を見送る場合があります。実行速度の最適化を主張する基準ではありません。

コンパイラが別の形へ展開したループの同一性や、元ソースとの一致はこの変換では判断しません。
カウンタの役割名も使い道の推定であり、元の変数名・単調性・停止性の証明ではありません。
保存場所の生存期間ごとの分割は行わないため、ループ外では別の用途に使われる値が同じ名前になる場合があります。

## continueと後続処理の関係

`value_role`は通常完了・現在のループへのcontinue・現在のループからの脱出・不明な転送を区別し、
後続処理を合成します。次の形の定数更新をcounter、ループ内で不変な比較相手をlimitとして認識します。

```c
counter += 1;
if (limit > counter) {
    continue;
}
write64(input.field_8, accumulator1);
value0 = accumulator1;
break;
```

途中のstoreやEvaluateは、成功すれば後続へ進む処理として扱います。評価や削除はしません。
両側がcontinueとなる条件、未到達のbreak、内側ループのbreak、外側への転送を新たな根拠にしません。
明確な脱出枝と、continueまたは別の脱出へ進む枝を持つ従来のガードも保持します。
初期実装はこの複数出口ガードを見落としたため、独立レビューの反例と回帰検査で修正しました。

## 検証の区切り

`branch-break.c` と `branch-return.c` は、異なる状態書込みを伴う脱出経路を持つ独立した元Cです。
両方ともO0/O2のliftを必須とし、未対応をskipしません。
専用のnative回帰検査では、二つの同じReturnの共有、順序付き条件読出し、
条件のfault、分岐内の書込み、共有末尾のfaultを元IRと比較します。

## 同じ機械語で分かったこと

既存20ソースとrecovery 10ソースのO0/O2、60構成中同じ53構成で比較しました。
GCC 13.3.0、C11・Wall/Wextra/Werror/pedantic・fno-ltoを共通とし、前後106本のCをコンパイルしました。
再配置で拒否する7構成は変わりません。

最初の「一致すれば必ず共有する」案では、breakが26→20、returnが72→71になりましたが、
本文は94,360→94,622 byteへ増え、`early-exit-chain -O2`の最大字下げも12→24へ悪化しました。
この案は採用せず、C本文を比較して選ぶ方式へ変更しました。

| 計測 | 基準 | 最終版 |
| --- | ---: | ---: |
| 関数本文byte数 | 94,360 | 94,244 |
| 関数内token数 | 18,586 | 18,586 |
| 役割名の付いた保存場所 | 19 | 21 |
| 数値局所変数 / 単純コピー | 183 / 23 | 183 / 23 |
| goto / label | 14 / 12 | 14 / 12 |
| if / break / return | 83 / 26 / 72 | 83 / 26 / 72 |

最終版では全53構成の最大字下げが基準以下です。`branch-break -O2`と`early-exit-chain -O2`で役割名が増えました。
このcorpusの末尾共有候補はすべて採用条件を満たさず、制御構造は変えていません。
byte減少は名前の変更によるもので、計算の削減や元ソースへの近さの改善とは主張しません。
一方、専用IR回帰例では複数Loadを含む同じ返り値計算を2か所から1か所へ共有し、native Cとの実行比較も通ります。
この差は、既存の構造化が通常の共有末尾をすでに扱っていることと、残る単独の脱出は平坦な表示が有利なことを示しています。

## 検証結果と再現

357テスト（通常348＋任意Z3 9）、Clippy全targetの警告ゼロ、rustfmt、diffの検査が通りました。
新規の末尾変換9テストは、独立したNode実行器とchecked IRで、上限0..79の各停止位置、全レジスタ・全メモリ・
fault・Step PC列を比較します。転送はlocal/outerのbreak/continueを含みます。
役割解析は18テストです。native C回帰検査はviewの有無・二つの表記・O0/O2で、最初のfaultアドレスと停止前の全バイトを照合します。
空になった分岐の純粋な条件、順序付きLoad、Selectの遅延評価も含めています。

| source corpus | 実行比較 |
| --- | --- |
| 既存20ソース | 33/40構成 × 63入力 = 2,079 |
| recovery 10ソース | 20/20構成 × 69入力 = 1,380 |
| 固定seedの生成8ソース | 16/16構成 × 67入力 = 1,072 |
| 合計 | 69/76構成、4,531入力比較 |

元Cとの比較は返り値と4状態ワード、readable CとIRの比較はstackを含む64KiB全体のdigestも対象です。
別途、生成16構成をUBSan付きの1,008入力で比較し、診断なしで一致しました。
有限入力の比較は全入力の同値性証明ではなく、既存のSMT検査も今回のC表示全体を証明しません。

```sh
NIRVANA_Z3=target/verification-venv/bin/z3 \
  NIRVANA_RECOVERY_ARTIFACTS=target/branch-tails/generated \
  cargo test --all-targets -- --include-ignored
cargo build --bin nirvana
python3 tools/compare_readable_output.py \
  --before /path/to/8f94893/nirvana --out target/branch-tails/comparison
python3 tools/validate_recovery_artifacts.py \
  --artifacts target/branch-tails/generated --out target/branch-tails/ubsan
```

`target/branch-tails/`に基準のソースarchive・CLI、前後のC・機械語・計測JSON・全テストログを残します。
不採用案の比較も`rejected-unconditional/`へ分けて残しました。
ソース、機械語、両CLI、コンパイラとフラグの出所は比較JSON、集約ハッシュはmanifestで確認できます。
作業snapshotは基準と差分を照合し、全変更がコミット内容と一致したことを記録してから削除しました。
