# 5時締切の並列改修・最終検証

2026-11-17 03:42 JST開始、05:00 JST締切。基点は`c4de482`です。
目的は、元のreturn・checked guest memoryを保ちながら、入力メモリ・添字・局所値をCへ表せる範囲を広げることです。
処理速度や既存製品への優位性を、この作業の評価には使っていません。

固定API・範囲は[contract.json](contract.json)、依存関係は[dag.json](dag.json)、
成果の取り込みハッシュ・計測結果・レビュー・片付けは[execution.json](execution.json)に分けて保存しました。

3 workerを独立コピーへ分け、親だけが共有masterを編集しました。

| 担当 | 独立した成果 |
| --- | --- |
| stack_analysis | 入力originとU64 spill、unsigned保存幅、CFG生存性による局所値の彩色 |
| expression_sequence | Load評価計画、借用するwhile-header形、生成C source holdout |
| variable_hir | mixed-width/alias/array fixture、base/index/stride回収、SMT検査、設計文書の初稿 |
| 親 | C/CLI接続、定義時アドレス形成、同じ保存幅内での共有、native fault検査、計測・UBSan・文書・コミット |

各段階は固定したAPIと別ファイルに対して実装し、同じコードを複数workerに書かせていません。
読み取り専用の統合レビューも実施しました。逐次実行との費用・速度比較は行っていません。

統合中に生成holdoutの`narrow-select seed10 O2`が、アドレス形成の表示変更後に不要になった
基底一時変数を`-Wunused-but-set-variable`で検出しました。
警告を弱めず、出力した添字・保存した入口基底と、依存レジスタの集計を一致させて修正しました。
入力オブジェクト回収を無効にしたstack-only表示では、元の右辺の依存を保持することも確認しました。

## 最終結果

- `NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --all-targets -- --include-ignored --test-threads=1`:
  **258成功、失敗0、未実行0**。通常249＋任意SMT9です。
- `cargo clippy --all-targets -- -D warnings`、`cargo fmt --all -- --check`、`git diff --check`: 成功。
- 元の20ソース: 33/40構成×63入力＝2,079比較。7構成の再配置は未対応のままです。
- 独立fixture 3ソース: O0/O2全6構成×69入力＝414比較。
- 決定的に生成する8ソース: O0/O2全16構成×67入力＝1,072比較。追加のskip・コンパイラflag変更なし。
- 合計55構成・3,565入力で、native元C・IR・再生成Cを比較。
  Cはreturn/stateに加え全64KiB guest memoryのdigestもIRと照合します。
- 手書きのalias・重なる幅・添字変更・上限近くのアドレス・部分状態では、全バイトも比較。
  複数Load、Select、nested address、Storeの先行チェック、後の反復でのfault、goto出力もnative実行しています。
- 生成例16構成×63入力＝1,008比較をUBSan付きで再実行。return/state一致、診断なし。
- stack-only/separate/full表示のC計165本が、strict C11・警告をエラー扱いでコンパイル成功。

同一オブジェクトに対し、field/index復元と幅推定を同じにして局所値の共有だけを切り替えると、
数値一時変数の宣言数は**912→229**でした。`sum O0`は13→2、`struct-fields O0`は19→3です。
記述できた定数オフセットfieldは139箇所、indexed形は16種類、定義時アドレス形成は14箇所です。
descriptor・引数・C評価計画の私有temporaryは、この数値一時変数の宣言数には含めません。

## 証明と未判定

既存`pure-u64-v1`のbit-vector検査で、宣言した幅推論の式対119件と添字変換の式対18件を
`EquivalentUnderModel`として確認しました。誤ったU8 mask・stride・offsetの3件はSATで、IRでも差を再現しました。
U64の自明なmask 31件は検査件数へ加えていません。

最初に試した一般のsymbolic×symbolic 7-bit乗算は、既定2秒でUnknownでした。
このケースは別のresource probeとして残し、Unknown時に`checked_rewrite`が元の式を保持することを検査しています。
strictな正例の乗算範囲は定数乗算に限定し、Unknownを137件の証明へ混ぜていません。
CFG上の解析、originの正しさ、C出力全体を証明した結果ではありません。

## 再現と到達段階

再現コマンドと制約は[memory-recovery.md](../../memory-recovery.md)を参照してください。
生成C・オブジェクト・入力/出力hash・コンパイラ情報・表・ログは`target/memory-recovery/`に保存しています。
UBSanは検証用再コンパイルだけに追加し、機械語入力の生成条件を変更していません。

workerの20成果物について一致または親での統合差分を確認し、その他の追跡ファイルは各コピーの基点と照合しました。
新しい想定外ファイルがないことも確認して、4つの作業用コピーを削除しました。未反映のソースはありません。
変更理由ごとにローカルコミットを作成しています。remoteがないためpush・PR・公開は実施していません。
