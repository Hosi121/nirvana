# 同値性の契約

IRと生成Cを比較するための実行モデルと観測対象です。
比較は、対応する初期状態からの実行に対して行います。

## IRの値とメモリ

- レジスタは初期値を与えたu64です。任意の入力値を許し、ゼロ初期化を前提にしません。
- 加減乗算はmodulo 2^64、比較はunsignedの0/1、シフト数は63でマスクします。
- 上位乗算はunsigned 128-bit積の上位64-bitです。
- 二項式は左、右の順で評価します。Selectは条件の後、選択した枝だけを評価します。
- メモリはbaseと有限byte列で与える単一のguest領域です。stackも観測対象に含みます。
- Load/Storeはlittle-endianの1/2/4/8 byteで、非整列も許します。
  Loadはゼロ拡張し、Storeは値の下位byteを書きます。
- アドレス計算は折り返しても、アクセス全体のu64アドレス折り返しや領域外参照はFaultです。
- 代入は逐次処理します。Storeはアドレス式、宛先全幅の範囲検査、右辺の順で評価し、
  すべて成功してから全幅を書き込みます。失敗したStoreの一部だけを書くことはありません。

最初のFaultで停止し、先に成功した代入・Storeは取り消しません。
同じ命令の途中で失敗しても、それ以前の副作用を残します。
異なる値をStoreした後で同じLoadに失敗する二つの実行は、同じエラーでも非同値です。
Loadの削除・複製・移動や、選択しない枝の評価を許す契約ではありません。

これはchecked guest memoryのモデルです。実CPUのページ権限・全例外、MMIO、並行実行を扱いません。
関数境界・命令集合・外部呼び出しの制約は[機械語フロントエンド](machine-frontend.md)を参照してください。

## 状態を保持する実行API

`Program`・`StructuredFunction`・`ReducedFunction`の`run_with_memory`は`Result<RunReport, ExecutionError>`を返します。
正常な呼び出しの結果は`RunReport { status, state }`です。実装は[IR](../src/ir.rs)にあります。

| status | 意味 |
| --- | --- |
| `Returned(value)` | 正常終了と返り値 |
| `Fault(MemoryFault)` | 最初のchecked memory失敗。read/write・address・widthを区別 |
| `Suspended` | 命令開始数の予算を使い切った。停止・非停止は未判定 |

stateにはレジスタ、全メモリとbase、開始した命令のtrace、現在／次に試みる命令位置を保持します。
入力レジスタ数の不一致は、実行前の外側の`Err`です。
`execute_with_memory`は正常終了用の射影で、Fault時の部分状態を失います。
失敗前のStoreまで比較するにはrun APIを使います。
改名・還元後のレジスタは内部値を含むため、元のレジスタ配列との単純な最終一致を要求しません。

## 観測プロファイル

[observe::Contract](../src/observe.rs)は、すべてのプロファイルで終了結果・正確なモデル内Fault・
全メモリのbase/size/byte列を比較します。メモリ領域やFaultを無視する設定はありません。

| ID | 追加で比較する項目 | 主な用途 |
| --- | --- | --- |
| `full-ir-state-v1` | 全レジスタと命令trace | 同じレジスタ空間の構造化前後 |
| `return-memory-v1` | なし | 高水準化後の具体実行 |
| `return-memory-trace-v1` | 命令trace | 命令位置を残す還元・改名 |

`state.instruction`は報告には残りますが、この比較器は直接比較しません。
読みやすいCの外部観測に、命令trace・実行時間・局所名は含めません。
初期状態の対応は呼び出し側の責任で、比較器はそれ自体を証明しません。

`MatchForInput`は、この対応入力で完了した実行の一致です。全入力の証明ではありません。
`Counterexample`は観測した差を示します。同じFaultでも停止前の全メモリを比較します。
片方でも`Suspended`なら`Inconclusive`で、片方が正常終了していても成功や反例に数えません。
異なる途中状態だけでは、最終的な観測の違いは判定できないためです。

変換の採否と、具体比較・モデル内検証それぞれの保証範囲は[検証手順](verification.md)を参照してください。
