# 検証契約とテストの整合記録

## REDUCTION-RESOURCE-001

- 正本: block-verification.mdの「資源上限は未判定」「未採用なら元IRを保持する」。
- 仕様変更: なし。
- 実装変更: DAGで共有末尾の配置を改善。SMTエンコーダ・還元器・ソルバ上限は変更していない。
- 検証モデル変更: なし。checked-memory-block-v1。
- 確認コマンド: `NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --test machine_pipeline accepted_reductions_feed_native_c_and_the_cli_reports_only_the_ir_scope -- --include-ignored`。
- 以前の結果: nonlocal-exit O0の全ブロックがUNSATとなり採用された実行がある。
- 今回の結果: 同じ例の0x51でSolverUnknownとなり、元IRを保持した。単独再実行でも再現。
- 分類: harness-drift。テストが「一定時間内に必ず証明できる」を要求し、未判定を許容するAPI契約とずれていた。
- 利用上の意味: 未判定の還元候補は採用されず、出力は元IRを使う。これは意味の不一致を示す反例ではない。
- 修正対象: テストハーネス。小さなdiamond/sumでは採用経路を要求したまま、複雑なnonlocal-exitでは採用またはソルバ時間切れだけを許す。
- 追加確認: 非採用ならpasses=0、全入力レジスタ、元の代入数を要求し、生成Cの63入力の値・状態配列・全メモリダイジェストを照合する。
- 維持する条件: 反例、プロトコルエラー、未対応、その他のUnknownはこの既知候補ではテスト失敗。時間切れを検証成功に数えない。既存のソルバ予算を増やさない。
- 未決の利用者判断: なし。既に承認された未判定時の元IR保持契約を維持する。
- 修正後の確認: `NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --all-targets -- --include-ignored --test-threads=1` が全139テスト成功。Clippyとrustfmtも成功。
- 証拠状態: machine-confirmed（失敗の再現と修正後のテスト結果）、diff-inferred（モデル・上限に変更なし）。
