# 実行モデルと同値性

Nirvanaは、対応する初期状態からの実行結果を比較します。
読みやすいCの観測対象は、返り値・ゲストメモリ全体・最初のメモリfaultです。

## 値と評価順

レジスタは任意の初期値を持つu64です。整数演算は次の規則に従います。

| 演算 | 意味 |
| --- | --- |
| 加減乗算 | modulo 2^64 |
| 比較 | unsigned比較の結果を0/1で表現 |
| シフト | シフト数の下位6bitを使用 |
| 上位乗算 | unsigned 128-bit積の上位64bit |
| 二項式 | 左、右の順に評価 |
| Select | 条件を評価し、選択した枝を評価 |

代入は記載順に実行します。メモリアクセスも元IRの評価回数と順序を保ちます。

## ゲストメモリ

メモリはbaseと有限のbyte配列で与える、単一のchecked memory領域です。stackも同じ領域に含みます。
Load/Storeはlittle-endianの1/2/4/8 byteで、非整列アクセスに対応します。
Loadはゼロ拡張し、Storeは値の下位byteを書き込みます。

アドレス計算はu64で折り返します。各アクセスでは全幅のアドレス範囲を検査し、
u64アドレス空間の末尾を跨ぐ場合と領域外参照をfaultとして返します。
Storeの処理順は次のとおりです。

1. アドレス式を評価する。
2. 宛先の全幅を検査する。
3. 右辺を評価する。
4. 全幅を書き込む。

最初のfaultで実行を停止し、それまでに成功した代入・Storeを状態に保持します。
このため、同じfaultでも停止前のメモリが異なる実行は区別されます。
このモデルが扱う範囲は、単一スレッドの通常メモリと境界検査です。
CPUのページ権限・その他の例外・MMIO・並行実行は今後の拡張対象です。
関数境界と命令集合は[機械語フロントエンド](machine-frontend.md)を参照してください。

## 実行API

`Program`・`StructuredFunction`・`ReducedFunction`の`run_with_memory`は、
`Result<RunReport, ExecutionError>`を返します。実装は[ir.rs](../src/ir.rs)にあります。

| 結果 | 内容 |
| --- | --- |
| `Returned(value)` | 正常終了と返り値 |
| `Fault(MemoryFault)` | 最初のfaultのread/write・address・width |
| `Suspended` | 命令開始数の予算に到達した途中状態 |

`RunReport.state`はレジスタ、全メモリとbase、命令trace、現在／次の命令位置を保持します。
入力レジスタ数などの呼出し条件は実行前に検査します。
`execute_with_memory`は正常終了向けの便宜APIです。fault前の部分状態の比較には`run_with_memory`を使います。

`emit::emit_c(&program)`は`Result<COutput, SequenceError>`を返します。
成功時の`code`に全レジスタ形式のCが入り、式の資源上限はエラーで確認できます。
生成Cの呼出し側では、レジスタ配列とゲストbyte配列にそれぞれ独立したホスト領域を用意します。

## 比較プロファイル

[observe::Contract](../src/observe.rs)は、終了結果と正確なfault、全メモリのbase・size・byte列を共通で比較します。
用途に応じて、レジスタと命令traceを追加します。

| ID | 追加の比較項目 | 用途 |
| --- | --- | --- |
| `full-ir-state-v1` | 全レジスタと命令trace | 同じレジスタ空間の構造化前後 |
| `return-memory-v1` | — | 高水準化後の具体実行と読みやすいC |
| `return-memory-trace-v1` | 命令trace | 命令位置を保つ還元・改名 |

`state.instruction`は診断用の情報です。比較項目は上表で定義します。
内部レジスタを分割・還元したプログラムには、観測したい結果に合わせたプロファイルを選びます。
呼出し側で対応する初期状態を用意し、比較結果を次のように読みます。

| 比較結果 | 意味 |
| --- | --- |
| `MatchForInput` | その対応入力で完了した実行の観測が一致 |
| `Counterexample` | 終了結果・メモリ・追加項目の具体的な差 |
| `Inconclusive` | 片方以上が予算に到達し、最終観測は未判定 |

入力集合やモデル全体を対象とする検証は、[検証ガイド](verification.md)にまとめています。
