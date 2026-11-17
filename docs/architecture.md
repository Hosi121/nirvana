# アーキテクチャ

Nirvana は既知の関数の機械語を実行可能 IR へ変換し、制御構造と値の使われ方から C を生成する。
Rust 標準ライブラリで実装し、命令デコードや関数の切り出しに外部逆アセンブラを使わない。
受理する入力と CLI は[機械語フロントエンド](machine-frontend.md)を参照。

## 処理の流れ

```text
ELF / raw bytes → x86-64 decoder・lifter → Program（IR + CFG）
  ├─ 実行 / IR・グラフ出力 / 全レジスタ形式の C
  └─ 還元 → 元の reduced IR
       ├─ 元 IR の構造対応検査
       └─ 定義 web 分割・独立対応検査 → 表示に使う IR
            → 表示用の構造対応検査
            → 式の整形・メモリ view・LocalPlan → readable C
```

`Program` は命令位置、順序付き代入、制御移転を持つ。CFG は到達可能部分を解析し、
支配関係・後支配関係・自然ループから `If`、`Loop`、脱出などの `Node` を組み立てる。
独立した AST→フローグラフの検査で、元の命令・代入・条件・転送先との対応を確かめる。
構造化できない CFG は goto で出力する。複数ループを跨ぐ転送はループの深さを保つ。

## reduced IR と表示用 IR

還元はブロック内の補助値や不要な代入を整理し、入力レジスタを値引数へ対応付ける。
`reduce_checked` は還元候補を SMT で検査し、受理できなければ元 IR を保持する。
観測対象と検査モデルの範囲は[同値性](equivalence.md)にまとめる。

定義 web 分割は、同じレジスタの定義を CFG 上の読出しとの関係で分ける任意の前処理である。
入口で読むレジスタ ID と引数の対応を保ち、演算・幅・代入順・命令位置・分岐先は変えない。
独立した `web_verify` が、各読出しで元と改名後の値が対応することを検査する。
追加レジスタの初期値に依存する候補は採用しない。

元の reduced IR の構造対応検査が成功した場合、その証拠を `ReadableC.structure_evidence` に保持する。
表示用 IR も別に構造化・検査し、成功した AST の証拠を `display_structure_evidence` に付ける。
元 IR で構造化できる場合は、改名後も構造化できる候補だけを採用する。
`web_recovery` は未変更・資源上限・対応検査失敗・構造化や描画の fallback を区別する。
web 候補で検査や描画に失敗した場合は元の reduced IR の経路へ戻る。
これらの証拠が対象とする IR/AST と、後続の C 整形は別の検査境界にある。

## 保存場所と表示変数

`prepare` は選んだ IR の幅解析・表示用 Program・構造候補を用意する。
以降の view、依存関係、変数計画、描画は同じ表示用 Program を使う。
パラメータは `uint64_t` を保ち、局所値には全定義を収められる幅を選ぶ。

`LocalPlan` は名前・幅・保存場所を描画から分離する。
同じ幅の局所値を CFG の生存解析とコピー関係で色分けし、共有できる保存場所を選ぶ。
その色の内側で値の系譜とループ中の役割を調べ、異なる役割の群を分ける。
別の色を統合せず、同じ役割や匿名値の共有は保つ。パラメータは共有対象から除く。
`counter`、`limit`、`accumulator`、`address` はこの構造から付ける表示名である。
`stack_role` は到達書込みから spill/reload の候補を結び、解析専用の木でスタック上の役割も調べる。
役割は名前と色の分割に使い、役割名だけを根拠に保存場所を統合しない。曖昧な値や異なる役割の根拠は採用しない。
同じ系譜の値には割当ての優先情報を渡すが、干渉辺は減らさない。選んだ割当ては別の
`allocation_verify` が各読出し時点の値の対応で検査し、通らなければ通常の割当て・個別変数へ戻す。

メモリ view は、入口のスタック位置や入力レジスタ由来のオフセット・添字を名前で表す。
view 同士や別のポインタが同じバイトを指すことを許し、アクセスは同じ guest memory に残す。
変数名・構造体型・所有権の復元とは区別する。

`stack_values` は正確な位置・幅ごとに、読込みへ到達し得るスタック書込みを CFG 上で追う。
不明アドレスや重複する部分書込みは値を不明に戻し、初期メモリと合流経路も保持する。メモリ操作は変更しない。

描画時は複数の Load を順序付きの評価へ分け、Select の選ばれた側だけを評価する。
while/for、入口 guard、複合代入の整形は、元の更新順と脱出先を保てる形に限る。
共通分岐末尾は命令位置まで一致する場合に共有候補とし、条件の評価を残す。
C 本体が短くなり、最大の字下げが増えない候補を採用する。
goto 配置では空の無条件経路を畳むが、空の巡回には代表を残す。
各任意解析は上限を持ち、適用できなければ既存の表示経路を使う。

## ソースの入口

| 責務 | 主なモジュール |
| --- | --- |
| 入力と機械語変換 | [frontend.rs](../src/frontend.rs)、[elf.rs](../src/elf.rs)、[x86](../src/x86/mod.rs) |
| 実行モデルと観測 | [ir.rs](../src/ir.rs)、[observe.rs](../src/observe.rs) |
| CFG と構造化 | [cfg.rs](../src/cfg.rs)、[structure.rs](../src/structure.rs)、[structure_verify.rs](../src/structure_verify.rs) |
| 還元と検査 | [reduce.rs](../src/reduce.rs)、[block_verify.rs](../src/block_verify.rs) |
| 定義 web と対応検査 | [web.rs](../src/web.rs)、[web_verify.rs](../src/web_verify.rs) |
| 表示前処理 | [prepare.rs](../src/readable/prepare.rs)、[webs.rs](../src/readable/webs.rs) |
| 保存場所と名前 | [locals.rs](../src/readable/locals.rs)、[allocation.rs](../src/allocation.rs)、[allocation_verify.rs](../src/allocation_verify.rs)、[local_identity.rs](../src/local_identity.rs) |
| メモリ view | [views.rs](../src/readable/views.rs)、[provenance.rs](../src/provenance.rs) |
| スタック値と役割 | [stack.rs](../src/stack.rs)、[stack_values.rs](../src/stack_values.rs)、[stack_role.rs](../src/stack_role.rs) |
| C 描画と評価順 | [readable.rs](../src/readable.rs)、[sequence.rs](../src/sequence.rs) |

検査の実行方法は[検証ガイド](verification.md)、導入手順は[README](../README.md)を参照。
