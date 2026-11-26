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
- [実Rust executorでの再生](../src/control_flow/structure/model_trial_tests.rs)。正常12組の672件を完全な`RunReport`で比較し、5種類の改変ASTに具体的な差が出ることを確認する。予算停止の負対照はモデル実行器へのfault injectionで、同じASTを実Rustで動かした結果は正常である。

検証対象は、この有限集合の制御イベント対応である。順序付き代入列・式をtokenで比較し、対応した原始操作の意味を共通の前提に置く。枝の結果は値の制約を超えて探索する。Rust再生は各改変候補の具体例を確認する段階で、TLC traceの自動具体化は次の接続点になる。算術・MemorySSA・native命令の意味は、それぞれの検査契約で扱う。

保存した結果は[初回checkpoint](../tools/corpora/structured-events-v1.m2.json)を参照。

同じStep列へ合流する制御転送は、構文の変更と意味の破壊を分け、受理した変更も全状態で再生する。たとえば`continue`を`break`へ変えても、後続が同じ無限ループへ戻る場合がある。

[配置回復のcheckpoint](../tools/corpora/structure-placement-v1.m2.json)では、共有するループ出口と複数入口の循環に、手書きASTと実際の復元結果を加えた。TLCは正常12組・2,176状態を探索し、既存の6つの負対照でも反例を得た。命令予算0〜6・loop深さ最大2と、モデルの不変条件を維持している。

## 実Rust実装の監査

[小CFG監査](../src/control_flow/structure/audit_tests.rs)は、元IRと復元したStructured ASTを公開実行APIで動かし、完全な`RunReport`を比較する。観測には全レジスタ・RAM・返り値・fault・実行trace・命令予算切れを含む。同じ入力とコピー上限で、対応漏れの修正前後を比較した。

| 固定集合 | 修正前の復元成功 | 修正後の復元成功 | 修正後の全状態比較 |
| --- | ---: | ---: | ---: |
| 4命令CFG × 3効果 | 2,841 / 3,000 | 3,000 / 3,000 | 672,000 |
| 5命令CFG × 3効果 | 61,962 / 62,208 | 62,208 / 62,208 | 13,934,592 |

5命令集合は最初の2修正後に固定した。入口領域の修正で135件、循環を保つ領域複製でさらに78件を復元し、以前の成功入力もすべて維持した。

4命令集合では、返る枝と無限ループの混在、および異なるループ出口の復元を修正した。5命令集合では、共有末尾・ループ出口・循環を含む入口領域を検査付きで回復する。生成Cも全命令位置からの再開と予算切れを含む46,464件で全状態が一致した。変更前の[監査](../tools/corpora/rust-structure-audit-v1.m2.json)と[循環領域のcheckpoint](../tools/corpora/structure-entry-cycles-v1.m2.json)に、観測契約・入力ID・各修正・固定評価の結果を保存している。

```sh
python3 tools/dev.py cargo test --lib control_flow::structure::audit_tests -- --include-ignored --nocapture
```

通常のテスト実行には、共有末尾・ループ出口・入口領域・独立した循環の回帰テストが入る。列挙2件と固定サンプル2件は上のコマンドで明示的に実行する。

より大きい入力には、6・7命令で各4,096形状×3効果の固定サンプルを置いた。

| 固定サンプル | 変更前の復元成功 | 変更後の復元成功 | 変更後の全状態比較 |
| --- | ---: | ---: | ---: |
| 6命令CFG × 3効果 | 12,267 / 12,288 | 12,279 / 12,288 | 4,322,208 |
| 7命令CFG × 3効果 | 12,198 / 12,288 | 12,249 / 12,288 | 4,312,704 |

7命令の比較件数は、意味を保つ3つの構文変更の再生を含む。分岐ごとの合流点とループ出口の配置を最大8候補で試し、複数入口が一つのコピー領域を共有できるようにした。入口複製は探索16候補・元命令の複製8個を全段で共有する。既存の成功した配置を優先し、最後に元PC・コピー数・元IRとの対応を再検査する。実ELFの17関数では、全命令位置・8入力・予算0〜20からの再開を、3種類の生成CのO0/O2・UBSanで170,352件比較した。

旧集合の成功例を維持し、今回の63構成の改善後も48構成の拒否を分母に残す。入力ID、拒否集合、比較条件、採用理由は[配置回復のcheckpoint](../tools/corpora/structure-placement-v1.m2.json)に固定した。

この監査は有限の実Rust差分検査である。共通の`Machine`が実装する原始演算には生成Cとnativeを別のoracleとして使う。Quint/TLCは上記の正常12組を対象とし、複数段で復元した循環にはRustと生成Cでの検査範囲を記録している。
