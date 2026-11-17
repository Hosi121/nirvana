# 設計

Nirvanaは機械語を実行可能IRへ変換し、制御構造と値の流れからCを生成します。
命令デコーダからC出力までをRustの標準ライブラリで実装しています。
入力形式とコマンドは[機械語とCLI](machine-frontend.md)にあります。

## パイプライン

```text
ELF / raw bytes → x86-64 decoder・lifter → Program（IR + CFG）
  ├─ 実行 / IR・グラフ出力 / 全レジスタ形式のC
  └─ 還元 → reduced IR
       ├─ IRと構造の対応検査
       └─ 定義web分割・対応検査 → 表示IR
            → 構造対応検査
            → 式の整形・メモリview・LocalPlan → readable C
```

`Program`は命令位置、順序付き代入、制御移転を持ちます。
CFGの到達可能部分について、支配関係・後支配関係・自然ループを解析し、
`If`・`Loop`・脱出などの`Node`を組み立てます。
Nodeを独立にフローグラフへ戻して元IRと照合し、構造に応じたCまたはgotoを出力します。
複数ループを跨ぐ転送は、対象ループの深さを保ちます。

## 還元と表示IR

還元はブロック内の補助値や代入を整理し、入口レジスタを値引数へ対応付けます。
`reduce_checked`は候補をSMTで検査し、採用条件が揃った候補へ置き換えます。
検査結果に応じて元IRを保持する経路もあります。

定義web分割は、レジスタの定義をCFG上のreadとの関係で分ける前処理です。
演算・幅・代入順・命令位置・分岐先・入口ABIを保持したまま、レジスタIDを割り当て直します。
`web_verify`は、追加レジスタの任意の初期値を含め、各readで元の値との対応を検査します。

元IRの構造証拠は`ReadableC.structure_evidence`、表示IRの証拠は`display_structure_evidence`に保持します。
`web_recovery`には候補の採用状態と退避理由を記録します。
IR・構造・C描画は、それぞれの段階に合った[検査](verification.md)を持ちます。

## 保存場所と変数

`prepare`は幅解析、表示用Program、構造候補を用意します。
メモリview・依存関係・変数計画・描画は、この表示用Programを共通に使います。
パラメータの型は`uint64_t`、局所値の型は全定義を収められる幅から選びます。

`LocalPlan`が名前・幅・保存場所を計画します。同幅の局所値を生存解析とcopy関係で色分けし、
系譜と役割から表示上の変数を分けます。入口パラメータには個別の保存場所を割り当てます。
`counter`・`limit`・`accumulator`・`address`は、ここで推論した役割に基づく生成名です。

保存場所の共有は、干渉グラフを守る割当て候補と、`allocation_verify`による各readの値の対応検査で決めます。
`source_locals`は位置・幅・役割の整合する候補をまとめ、元の色を跨ぐ統合も全体検査へ渡します。
結果は表示変数の候補と、採用した保存場所の対応として保持します。

スタック解析は次の情報を供給します。

| 解析 | 情報と用途 |
| --- | --- |
| `stack_values` | 正確な位置・幅ごとの到達書込み。部分書込み、不明アドレス、入口メモリ、合流も追跡 |
| `stack_cells` | 単一定義のLoadとcopyから得る読込み位置 |
| `stack_role` | spill/reloadの系譜と役割。命名と割当ての優先情報 |

メモリ操作はIRの評価順と回数を保持します。これらの位置情報は表示変数の計画に使います。
メモリviewは、入口スタックや入力レジスタからのオフセット・添字を名前で表します。
view同士のaliasを許し、アクセス先は同じゲストメモリです。

## Cの表示

複数のLoadは順序付きの評価へ分け、Selectは選択した枝を評価します。
while・for・do-whileや複合代入は、元の更新順と脱出先を保つ借用viewから描画します。
途中のcontinueは対象ループを判別し、returnに至る脱出末尾は制御条件が揃った場合にループの後へ表示します。
共通分岐末尾は命令位置まで一致する場合に共有候補とします。
候補の選択条件は、C本体が短くなり、最大の字下げが同じか小さくなることです。

純粋なrotate64・byte swap32/64の厳密な式にはC helperを使い、使用する定義を出力します。
展開された加算ループは、前段から導出した有限入力全体の対応とC保存幅を検査して通常ループへ戻します。
初期累積値が任意のu64なら、有限な制御値ごとに`a*A+b mod 2^64`の対応を検査します。
表示領域の証拠は`finite_regions`・`affine_regions`に記録し、元CFGの証拠も保持します。

goto配置では空の無条件経路を畳み、空の巡回には代表を残します。
各任意解析は資源上限を持ち、結果に応じて既存の表示経路を選びます。

## 主なモジュール

| 責務 | モジュール |
| --- | --- |
| 機械語変換 | [frontend.rs](../src/frontend.rs)、[elf.rs](../src/elf.rs)、[x86](../src/x86/mod.rs) |
| 実行と観測 | [ir.rs](../src/ir.rs)、[observe.rs](../src/observe.rs) |
| CFGと構造 | [cfg.rs](../src/cfg.rs)、[structure.rs](../src/structure.rs)、[structure_verify.rs](../src/structure_verify.rs) |
| 還元と改名 | [reduce.rs](../src/reduce.rs)、[block_verify.rs](../src/block_verify.rs)、[web.rs](../src/web.rs)、[web_verify.rs](../src/web_verify.rs) |
| 表示変数 | [locals.rs](../src/readable/locals.rs)、[allocation.rs](../src/allocation.rs)、[allocation_verify.rs](../src/allocation_verify.rs)、[source_locals.rs](../src/source_locals.rs) |
| メモリとスタック | [views.rs](../src/readable/views.rs)、[provenance.rs](../src/provenance.rs)、[stack.rs](../src/stack.rs)、[stack_values.rs](../src/stack_values.rs) |
| 描画と評価順 | [readable.rs](../src/readable.rs)、[sequence.rs](../src/sequence.rs)、[bit_expr.rs](../src/bit_expr.rs) |
| ループ表示 | [for_loop.rs](../src/for_loop.rs)、[loop_shape.rs](../src/loop_shape.rs)、[loop_exit.rs](../src/loop_exit.rs) |
| 純粋領域の復元 | [loop_recover.rs](../src/loop_recover.rs)、[finite_region.rs](../src/finite_region.rs)、[affine_region.rs](../src/affine_region.rs) |
