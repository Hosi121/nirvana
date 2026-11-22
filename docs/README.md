# ドキュメント

利用時はCLI、開発時は設計とテストガイドから読み始められます。
実行結果の対応を判断するときは、実行モデルを正本にします。

| 目的 | 文書 |
| --- | --- |
| 入力形式・対応命令・出力・実行APIを選ぶ | [CLIと対応範囲](machine-frontend.md) |
| IRの抽象化・段階間の保証・コードの担当箇所を知る | [設計](architecture.md) |
| 整数・メモリ・外部効果・途中停止の意味を確認する | [実行モデルと同値性](equivalence.md) |
| 比較の観測対象・独立検査・任意のSMT検査を確認する | [検証ガイド](verification.md) |
| テストを探す・ケースを追加する | [テストガイド](../tests/README.md)・[C fixtures](../tests/fixtures/README.md) |
| 現行のM0・到達基準・実装の着手順を確認する | [ロードマップ](x86-64-roadmap.md) |

## 調査記録

調査当時の入力・結果・提案を保存しています。現在の優先順位はロードマップにまとめています。

- [CFG復元とコンパイラ最適化](research/cfg-recovery-research.md)
- [公開CTFバイナリの入力調査（2026-11-21）](research/ctf-audit-2026-11-21.md)
- [追加CTF候補と評価案（2026-11-21）](research/ctf-next-2026-11-21.md)
