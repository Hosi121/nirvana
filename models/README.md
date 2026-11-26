# 構造対応の有限モデル

[structured_events.qnt](structured_events.qnt)は、元IRのPC実行と、raw ASTの構文cursor・lexical stackによる実行のイベント順を比較する。
入力は[exporter](../examples/structure_model.rs)が実Rustの`Program`・`Node`から生成し、`structure_verify::validate`の採否も保存する。モデルのAST実行はFlowGraph loweringから独立している。

初回の集合は共有末尾・外側continue・同一後続へのfault可能な条件評価の3形状。それぞれ手書きASTと実際の`StructuredFunction::recover`の出力を使う。命令予算は0〜6、loopの深さは最大2。

```sh
python3 tools/dev.py run -- python3 tools/quint_trial.py --out '{out}' --report target/structured-events-trial.json
```

Linux x86-64と`dpkg-deb`があれば、SHA-256を固定したQuint・Java・Apalacheを一時展開する。ツールと作業領域は終了時に片付き、指定したJSONへ結果・反例を保存する。展開中の保存量は約600MiB、JVM heapは512MiB、TLC workerは1、各問い合わせは最大180秒。既存のQuint0.34.0・Java環境には`--quint PATH`を指定できる。

検査は次を分けて記録する。

- TLCによる有限状態空間の探索と不変条件の検査。
- 固定seedのQuint simulationによる正常終了・fault・予算停止の到達確認。
- 枝交換・Step欠落・評価削除・transfer深さ変更・代入順変更・早すぎる予算停止の負対照。
- [実Rust executorでの再生](../src/control_flow/structure/model_trial_tests.rs)。正常6組の336件を完全な`RunReport`で比較し、5種類の改変ASTに具体的な差が出ることを確認する。予算停止の負対照はモデル実行器へのfault injectionで、同じASTを実Rustで動かした結果は正常である。

検証対象は、この有限集合の制御イベント対応である。順序付き代入列・式をtokenで比較し、対応した原始操作の意味を共通の前提に置く。枝の結果は値の制約を超えて探索する。Rust再生は各改変候補の具体例を確認する段階で、TLC traceの自動具体化は次の接続点になる。算術・MemorySSA・native命令の意味は、それぞれの検査契約で扱う。

保存した結果は[初回checkpoint](../tools/corpora/structured-events-v1.m2.json)を参照。

## 実Rust実装の監査

[小CFG監査](../src/control_flow/structure/audit_tests.rs)は、元IRと復元したStructured ASTを公開実行APIで動かし、完全な`RunReport`を比較する。観測には全レジスタ・RAM・返り値・fault・実行trace・命令予算切れを含む。同じ入力とコピー上限で、対応漏れの修正前後を比較した。

| 固定集合 | 修正前の復元成功 | 修正後の復元成功 | 修正後の全状態比較 |
| --- | ---: | ---: | ---: |
| 4命令CFG × 3効果 | 2,841 / 3,000 | 3,000 / 3,000 | 672,000 |
| 5命令CFG × 3効果 | 61,962 / 62,208 | 61,995 / 62,208 | 13,886,880 |

5命令集合は最初の2修正後に固定し、共有末尾の修正前後を比較した。

4命令集合では、返る枝と無限ループの混在、および異なるループ出口の復元を修正した。5命令集合では、共有するループ末尾を合流点として選び、1コピー・全5ステップで復元する例を追加した。生成Cも全命令位置からの再開と予算切れを含む5,544件で全状態が一致した。変更前の[監査checkpoint](../tools/corpora/rust-structure-audit-v1.m2.json)と、各修正・拒否件数・固定評価の結果を含む[修正checkpoint](../tools/corpora/structure-divergent-v1.m2.json)を保存している。

```sh
python3 tools/dev.py cargo test --lib control_flow::structure::audit_tests -- --include-ignored --nocapture
```

通常のテスト実行には、返る枝と無限ループ、異なるループ出口、共有末尾の回帰テストが入る。有限列挙の2件は上のコマンドで明示的に実行する。5命令集合で残る213件の拒否は、ノード分割後の構造化や探索上限の調査対象として分母に保持する。

この監査は有限の実Rust差分検査である。共通の`Machine`が実装する原始演算には生成Cとnativeを別のoracleとして使う。先のQuint/TLCの対象は同じ6組を維持し、今回の追加形状にはRustと生成Cでの検査範囲を記録している。
