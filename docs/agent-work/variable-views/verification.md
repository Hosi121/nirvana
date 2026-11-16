# スタックビューの並列実装・統合記録

2026-11-17。ユーザーの明示依頼で、独立できる実装を並列化しました。
区切りは、既存メモリ契約を維持しながらO0の`sum`と`struct-fields`のスタック位置へ名前を付けることです。

固定したAPIと担当範囲は[contract.json](contract.json)、依存関係は[dag.json](dag.json)、
担当ごとの成果と取り込み時のハッシュは[execution.json](execution.json)に分けて保存しています。

- エージェントA: `hir.rs`と専用テスト。明示的なobject/field/indexを既存メモリIRへ下げる部分。
- エージェントB: `stack.rs`と専用テスト。入口スタックを基準にCFG固定点で定数オフセットを追う部分。
- 親: C出力・CLIとの接続、既存機械語fixtureでの評価、ネイティブfault検査、統合・コミット。

エージェントは別の独立コピーを編集し、共有masterへの書き込みは親だけが行いました。
コード間の依存を作らず、先に固定した既存IRとAPIに対して並列で実装しました。
同じ人数での逐次作業との時間・費用比較は実施していないため、並列化による高速化率は主張しません。

HIR担当による統合コードの読み取り専用レビューでは、純粋なアドレス置換、入口アドレスの保持、
出力時の依存関係追跡に新しいblocking issueは見つかりませんでした。
一方、従来のC store呼び出しは右辺Loadをdestination検査より先に評価する点を指摘しました。
親がreadable出力へ先行する範囲検査文を追加し、生成Cの最初のfaultアドレスと停止前のメモリを検査しました。
この修正を含めたC出力全体の形式証明ではありません。

親による最終検証:

```sh
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --all-targets -- --include-ignored --test-threads=1
cargo clippy --all-targets -- -D warnings
cargo fmt --all -- --check
git diff --check
cargo run --quiet --example measure_stack_views -- target/stack-views
```

- **166テスト成功**。通常160＋任意のSMT6、失敗・未実行0。Clippy、rustfmt、差分検査も成功。
- 既存33構成×63入力の元C・元IR・還元IR・再生成Cが一致。IRは全メモリ・trace、Cは全メモリのダイジェストも照合。
- 追加のalias・重なり・入口後のSP変更・u64上限付近のアドレス: 18入力×O0/O2、全32バイトも一致。
- faultを伴う3種類のプログラム: 4入力×ビュー有無×O0/O2、計48実行。
  最初のfaultアドレスと停止前の全16バイト、正常終了時の返り値が一致。
- 同一オブジェクトでの表現比較: 47ビュー、読み出し218箇所・書き込み58箇所。
  `sum O0`は5箇所、`struct-fields O0`は6箇所。元ソースへの復元精度とは区別。
- `sum O0`のCLI出力とAPI経由の比較用Cがバイト単位で一致。

再現用のC・表・全テストログは`target/stack-views/`に保存しています。
workerの担当4ファイルは取り込み後のファイルとバイト単位で照合しました。
コピー内のその他の追跡ファイルは、検証用module exportを除き基点`eef1379`と一致することを確認し、
不要な独立コピーを削除しました。未反映のソースは残していません。

設計と制約は[stack-views.md](../../stack-views.md)を参照してください。
ローカルコミットまで実施し、remoteがないためpush・PR・公開は実施していません。
