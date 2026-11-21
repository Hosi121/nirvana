# 設計

Nirvanaは機械語を実行可能IRへ変換し、制御構造と値の流れからCを生成します。
命令の意味と観測項目は[実行モデル](equivalence.md)、入力形式は[CLI](machine-frontend.md)、検査の実行方法は[検証ガイド](verification.md)にまとめています。

## 処理の流れ

```text
ELF / raw bytes
  → binary: 配置・再配置・命令デコード・IRへの変換
  → model: 命令位置、順序付き代入、CALL/RET、ゲスト状態
      ├─ 実行・状態観測・解析レポート
      └─ control_flow / dataflow: 制御構造・SSA・値とメモリの対応
           → transform: 還元・式選択・表示用IR
           → 対応検査
           → codegen: 変数計画・構造化C・再入用dispatch
```

単一関数、外部効果付き単一関数、複数関数は、それぞれの状態モデルに対応する生成経路を持ちます。
各経路は実行時のアドレスとゲストRAMを使い、外部効果や途中停止を観測できる状態を保ちます。

## ソースの配置

| ディレクトリ | 責務と入口 |
| --- | --- |
| [binary](../src/binary/mod.rs) | ELF・再配置・範囲発見、x86デコーダ/lifter、ジャンプテーブル候補 |
| [model](../src/model/mod.rs) | IRの構造と実行器、checked memory、外部効果、状態観測 |
| [control_flow](../src/control_flow/mod.rs) | CFG、支配関係、自然ループ、構造ASTと対応検査 |
| [dataflow](../src/dataflow/mod.rs) | SSA、生存範囲、アドレスの恒等関係、MemorySSA、型候補、変数割当て |
| [transform](../src/transform/mod.rs) | IR還元、算術の復元、不要代入除去、評価順・ループの表示変換 |
| [codegen](../src/codegen/mod.rs) | Cの式・宣言・描画、複数関数のoutline・局所変数・dispatch |
| [verification](../src/verification/mod.rs) | 純粋式とブロック還元のSMTエンコード・反例の再実行 |

公開APIはこの配置で参照できます。従来の`nirvana::ir`や`nirvana::memory_ssa`などのパスも、[lib.rs](../src/lib.rs)の再公開で維持しています。
解析固有の検査器は、候補を作る解析と同じディレクトリに置きます。`verification`はSMTによる検査を担当します。

## 機械語から実行IRへ

[elf](../src/binary/elf.rs)は元のセクション座標と再配置を保持し、[object_refs](../src/binary/object_refs.rs)が実opcodeのフィールドと照合して文字列・呼出し参照を導きます。
[loader](../src/binary/loader.rs)はオブジェクトの割当てセクションを、[linked_elf](../src/binary/linked_elf.rs)は実行ファイルのsegment・GOT・動的再配置をゲスト画像へ配置します。
strip入力の数値入口は、[eh_frame](../src/binary/eh_frame.rs)のFDE範囲を実行可能なファイル範囲と照合して読み込みます。
疎な画像は[共通の範囲表](../src/model/memory.rs)で元アドレス・権限とpacked backingを対応付けます。

[x86](../src/binary/x86/mod.rs)は直接辺から命令を発見し、部分レジスタ・フラグ・評価順を実行IRへ展開します。
符号付き上位積と算術右シフトは`SMulHigh`・`AShr`として保持し、レジスタのbit列に対する演算として解釈します。これにより、後段はu64の補正式を再認識せず演算の関係を追えます。
符号拡張は`UnaryOp::SignExtend(Width)`で入力幅を保持します。SSA・値グラフ・メモリの参照位置もこの単項演算を通じて追跡し、Cへはunsignedだけで計算するhelperとして下ろします。
[word_signed_division](../src/transform/word_signed_division.rs)は8/16/32-bitへの射影と符号付き積を区別し、定数除算・剰余を復元します。数値証明を64-bit版と共有し、右シフトには符号拡張と観測幅の条件を確認します。生成する結果は上位bitがゼロのwordで、後続の符号拡張も保持します。
[jump_tables](../src/binary/jump_tables.rs)は先行CFGの経路文脈、copy、stack退避、比較とmaskから表候補を求め、追加デコードと交互に進めます。
候補には読取り位置・範囲の根拠・未探索の残余を保持します。実行時の間接移転は現在のRAMからtargetを評価し、発見済みPCへdispatchします。

[effects](../src/model/effects.rs)は`puts`の外部結果入力を、[module_ir](../src/model/module_ir.rs)は複数関数とimportを扱います。
CALLの戻り先Store、PLT targetのLoad、RET、DIV/IDIV、STOS・MOVSの部分進捗を明示し、faultと命令予算を同じ順序で処理します。
POSIXアダプタはゲスト構造体とホストABIを変換します。TLS guardとstream handleの規則は実行モデルにあります。

## CFGの構造化

[cfg](../src/control_flow/cfg.rs)・支配/後支配解析・自然ループ解析から、`If`・`Loop`・脱出を持つ[Node](../src/control_flow/structure.rs)を組み立てます。
[structure_verify](../src/control_flow/structure_verify.rs)はNodeを独立にグラフへ戻し、命令・逐次代入・条件・移転先を元IRと照合します。
複数ループを跨ぐ転送には、対象ループのcontinue/breakラベルを割り当てます。

複数入口の循環には、[短い入口の制限付き複製](../src/control_flow/structure/split.rs)を試します。
候補PCを元PCへ対応付けて全体を照合し、コピー数とStep数の上限を検査します。
構造化の採用条件が揃わない領域は、元の制御をgotoで描画します。

## 値・メモリ・型の解析

[ssa](../src/dataflow/ssa.rs)は逐次read/定義に値IDを付け、φの全先行辺と任意の初期値を持つ仮想入口を表します。
独立した[SSA検査器](../src/dataflow/ssa/verify.rs)が元IRとの対応を確認します。
[value_liveness](../src/dataflow/value_liveness.rs)はφ入力を辺ごとに扱い、ループの固定点まで使用を伝播します。
[ssa_locals](../src/dataflow/ssa_locals.rs)・[ssa_storage](../src/dataflow/ssa_storage.rs)は干渉を守って保存先をまとめます。
[parallel_copy](../src/dataflow/parallel_copy.rs)はφの同時代入を逐次化し、記号による検査で循環と他の保存先の保持を確認します。
[ssa_destroy](../src/dataflow/ssa_destroy.rs)が実行可能IRへの配置を、[emit/ssa](../src/codegen/emit/ssa.rs)がCの宣言と保存先名の描画を担当します。

アドレスの正確な恒等関係は[address_identity](../src/dataflow/address_identity.rs)が担当します。
`offset + Σ(coefficient × SSA値) mod 2^64`を、型やオブジェクト形状の仮説から独立して扱います。
[type_infer](../src/dataflow/type_infer.rs)はこの参照情報と値の幅・使用制約からフィールドや配列の候補を組み、[record_shapes](../src/dataflow/record_shapes.rs)が構造体候補をまとめます。
構造体の互換性は、copy・φ・stackに加え、MemorySSAで全8 byteの書込み元を確認できたStore→Loadにも伝播します。辺上のアドレス変換を使い、初期メモリ・部分上書き・may-aliasを含むLoadは元の候補を保ちます。
追加解析の上限では、追加した辺とnull候補を破棄して従来の候補を構成し、理由をレポートへ残します。

[memory_ssa](../src/dataflow/memory_ssa.rs)はStoreごとのメモリ世代とφを作り、Loadへの書込み候補をbyte mask付きで求めます。
確実なStoreで埋まったbyteだけ遡及を止め、may-alias・未知の効果では前の候補も残します。分岐ごとの未解決byteを個別に追跡します。
先行辺ではφ入力を同時置換し、ループで成長するアドレス式や予算到達では未知へ広げます。
別々の入力pointerとstackの間にもmay-aliasを保ちます。対象は関数入口から正常に継続した経路です。
解析グラフの構築と書込み元の照会は個別の予算を持ち、未判定の理由をレポートへ残します。

[module_values](../src/dataflow/module_values.rs)はCALL・DIV・STOS・MOVSを順序付きイベントに写します。
[call_footprint](../src/dataflow/call_footprint.rs)の閉じた正常復帰要約を使える場合は保存レジスタの値IDを継続し、未知の結果には新しいIDを付けます。
レジスタの保存とRAMの保存は個別に判断します。CALLと未知のメモリ効果はMemorySSAの境界になります。
DIV/IDIVを含むcalleeも、正常復帰とreturn slotの保護を確認してレジスタ要約を作ります。商・剰余の結果は未知とし、書き換えられないレジスタの値IDを継続します。

## 表示用IRと局所変数

[reduce](../src/transform/reduce.rs)は補助値を整理し、[web](../src/dataflow/web.rs)はレジスタ定義を使用とのつながりで分割します。
候補ごとの検査を経て、load-mask、SSA定数伝播、算術式選択、純粋な不要代入除去を表示IRへ適用します。
[arithmetic_graph](../src/transform/arithmetic_graph.rs)と[expression_ir](../src/model/expression_ir.rs)は、分子・上位乗算・商・剰余を値IDと定義位置で結び、算術の証拠を照合します。
[signed_division_expr](../src/transform/signed_division_expr.rs)は純粋な64-bit式の符号付き商・剰余を、正数・負数それぞれの誤差境界から復元します。C helperはunsignedの絶対値とbit列を使い、最小負数の入力も扱います。
[semantic_ir](../src/model/semantic_ir.rs)はblock内の不変な値IDを使い、別々に保存された上位積・符号補正・商・剰余を結びます。分子を一度保存し、代入・メモリアドレス・分岐・返り値の部分式を、利用可能な意味付きの値へ置き換えます。独立した対応検査が、保存時点、元レジスタへの書込み、Load/Storeの順序、制御辺を照合します。
Loadのスナップショット、保存位置、全命令の代入順も採用条件です。

[LocalPlan](../src/codegen/readable/locals.rs)は表示IRの幅・生存範囲・copy関係・値の系譜から名前と保存場所を決めます。
[allocation_verify](../src/dataflow/allocation_verify.rs)は各readの値を、[DeclarationPlan](../src/codegen/readable/declarations.rs)は宣言・初期化の位置を照合します。
[stack_values](../src/dataflow/stack_values.rs)は部分Storeとaliasを含む到達書込み、[stack_role](../src/dataflow/stack_role.rs)はspill/reloadの系譜を供給します。
メモリviewは同じゲストRAMへの表示名として使い、互いのaliasを許します。

## Cの描画と途中再開

[readable](../src/codegen/readable.rs)は公開出力型を持ち、[pipeline](../src/codegen/readable/pipeline.rs)が変換と計画を組み立て、[printer](../src/codegen/readable/printer.rs)が描画します。
共通の[sequence](../src/transform/sequence.rs)が式の規模・評価順の前提を確認し、複数Loadやlazy Selectは順序付きの処理へ展開します。
ループ更新・共有末尾・有限/affine領域の表示も、元の制御と値の対応を検査して採用します。

複数関数では[module_outline](../src/codegen/module_outline.rs)が全Stepからの再入を検査し、[module_readable](../src/codegen/module_readable.rs)が名前付き関数を描画します。
間接移転の局所化は[module_tail_dispatch](../src/codegen/module_tail_dispatch.rs)・[module_switch_keys](../src/codegen/module_switch_keys.rs)が計画し、保存したkeyと実targetを照合して局所ラベルを選びます。
残るtargetはdispatcherへ渡します。通常CALLはCの呼出しを使い、深い再帰や想定外の戻り先ではゲストPCから再開します。

[module_local_plan](../src/dataflow/module_local_plan.rs)は局所値と元の代入を照合し、各レジスタ書込みをゲスト状態へ反映します。
途中PCと成功したCALL/DIV/STOS/MOVSの後には、生存値を実レジスタから復元します。
検査や資源上限に達した関数はレジスタ形式を使い、理由を出力へ記録します。
