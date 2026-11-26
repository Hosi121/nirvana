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
