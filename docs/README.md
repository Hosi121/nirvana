# ドキュメント

| 内容 | 文書 |
| --- | --- |
| 入力形式、命令の対応範囲、CLI、生成Cのインターフェース | [機械語とCLI](machine-frontend.md) |
| パイプライン、制御構造、変数の回復、モジュール構成 | [設計](architecture.md) |
| 整数とメモリの意味、実行結果、同値性の観測対象 | [実行モデル](equivalence.md) |
| テスト、fixture比較、独立検査器、任意のSMT検査 | [検証](verification.md) |
| コンパイラ最適化を踏まえたCFG復元の調査と次の比較計画 | [CFG復元の調査](cfg-recovery-research.md) |
| x86-64に絞った到達目標、難所、実装段階と評価ゲート | [ロードマップ](x86-64-roadmap.md) |
| 公開CTFのC／x86-64配布バイナリ6問で測った対応範囲と障害 | [CTF入力の調査](ctf-audit-2026-11-21.md) |

テストデータの構成と生成は[fixturesの説明](../tests/fixtures/README.md)を参照してください。
