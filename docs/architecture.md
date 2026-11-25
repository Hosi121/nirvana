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

## 抽象化の段階と保証

実行IRが機械語の動作を表す正本です。SSAとMemorySSAはその上の解析表現、Semantic IRは検査付きの意味回復計画、Structured ASTは制御構造の表現です。解析結果を対象の入力IRと命令位置へ結び、変換後は影響する解析を再構築します。

| 表現 | 担当する抽象化 | 次へ渡す契約と現在の検査 |
| --- | --- | --- |
| Executable IR | [単一関数](../src/model/ir.rs)・[module](../src/model/module_ir.rs)のbit演算、順序付き効果、PCとゲスト状態 | 幅・flag・Load/Store・CALL/RET・最初のfaultを明示する。native/oracle比較で命令意味を検査し、moduleでは予算と途中再開も照合する |
| Register SSA | [定義・使用・φ](../src/dataflow/ssa.rs)による値の識別 | 各readを元IRの定義へ結び、仮想入口と全先行辺を保持する。[独立検査](../src/dataflow/ssa/verify.rs)を通した値IDを変換の根拠にする |
| Middle IR | [不変な値ID・保存場所・評価領域・CFG](../src/model/middle_ir.rs) | 単一関数の実行IRを持ち上げ、元の式・命令・SSA対応を再構成して照合する。Loadの順序とlazyな枝、Store先の先行検査、guest命令のPC・予算を保持する |
| MemorySSA | [メモリ世代とbyteごとの到達書込み候補](../src/dataflow/memory_ssa.rs) | may-alias・初期メモリ・未知CALLの寄与を保持する。[独立検査](../src/dataflow/memory_ssa/verify.rs)で元IRのread/commit順序・全流入辺・仮想入口・opaque効果と、候補集合の被覆を照合する。[byte tagの独立実行比較](../tests/dataflow/memory_ssa.rs)も併用する |
| Semantic IR | [保存時点と値IDに結び付けた意味付き演算](../src/model/semantic_ir.rs) | 現在はblock内の商・剰余などを回復する。入力の保存時点、置換箇所、元の効果と制御を照合して実行IRへ下ろす。検査済みの`Lowering`に実入力・計画・出力を結び、入力の全状態と追加レジスタの射影を観測できる。関数全体の型付きIRは到達目標 |
| Structured AST | [Step・If・Loop・脱出](../src/control_flow/structure.rs)による制御の構成 | [ASTをグラフへ戻す検査](../src/control_flow/structure_verify.rs)で元PC、代入、条件、移転先を照合する。条件の集約・移動には追加の意味検査を結ぶ |
| C continuation graph | [保存先確定後のC断片と継続先](../src/codegen/readable/continuations.rs) | 閉じた非循環領域で、順序付きC断片と返り値の対応を検査する。同一の継続先を持つ純粋な条件を除き、重複した終了処理を共有する |
| C | 保存先・宣言・型表記と再コンパイル可能な出力 | 単一関数は返り値・RAM・最初のfault、moduleはレジスタ・PC・予算・外部効果も比較する。現在は個別の対応検査と再コンパイル実行比較を組み合わせる |

元変数の同定、非aliasの証明、Cの型や所有権の確定は、それぞれ追加の回復主張です。値ID・メモリ世代・viewの名前から得られる事実と、[実行契約](equivalence.md)を保つ根拠を分けて記録します。

情報が失われた名前・元変数の分割・構造体境界は、根拠付きの推定として回復する領域です。将来LLMを用いる場合も候補を提案する部品へ置き、値・効果の変換は対応するIRの検査を通します。表示上の推定と、意味を保存する根拠を区別して評価します。

`ReadableC.semantic_lowering`は、採用した意味IRの段階を`Arc`で共有します。複数の配置候補で同じ入力・計画・下ろしたIRを参照し、表示用DCEの前の状態を保持します。評価器は生成C本文との一致を確認してから、この段階の入力と出力を照合します。入力は前段の表示IRのレジスタ空間で、機械レジスタとの対応・元変数の同定はそれぞれの契約へ結びます。

compiler-awareなCFG回復は、実行IRと解析表現を使って辺・領域の候補を作り、検査後にSSA・MemorySSAを更新して構造化へ渡します。[ロードマップのM2](x86-64-roadmap.md#段階と到達基準)で扱い、元ソースへの構造的な近さはM0の評価で測ります。

[経路条件の回復](../src/dataflow/predicates.rs)は、閉じたDAGのSSA値を使い、各block入口のゼロ・非ゼロの事実を求めます。別の検査器が元CFGの全流入辺から主張を確認し、純粋な条件分岐・代入・returnの変更を検査します。Loadは定義ごとに独立な値とし、メモリ効果・命令位置・予算を保ちます。契約は関数入口からの実行とそのprefixです。Middle IRの`recover_predicates()`は変更後のCFGからSSAと値IDを再構築し、readable Cは同じ引数契約で従来の出力と比較して候補を選びます。
Loadは出現ごとに独立な結果値を持ち、正常に評価を終えた結果へ純粋なbit演算の恒等式を適用します。これにより、`KnownLoad`の戻し変換である`(read & 0) | known`からも条件へ定数性を伝えます。メモリを含む代入・条件・returnの式は元の位置に保持し、読込み順序・lazyな枝・最初のfaultを実行比較とSMTで検査します。

Middle IRはM1の段階間契約を実装する最初の共通表現です。保存場所IDと値IDを分け、各read/writeにレジスタSSAの版を対応付けます。値は64-bit bit列として計算し、Loadと抽出には幅を保持します。条件付きの式は子の評価領域を持ち、Storeはアドレスと右辺の領域を分けます。同じ領域の純粋な計算と同じSSA版の読取りを共有し、Loadは個別に保持します。戻し変換は式を再構成し、Loadの脱落・複製・順序変更を検査します。

直接実行器とLow IRへの戻し変換を、全レジスタ・RAM・最初のfault・PC・命令予算で比較します。`--emit middle-ir`は値と領域・SSA版・CFGを表示し、`--emit middle-c`は検査済みの再構成を既存C backendへ渡します。型・元変数の回復とmoduleの外部効果は、この単一関数の契約から段階的に広げます。

[Middle IRのメモリ情報](../src/model/middle_ir/memory.rs)は、一つの不変な関数に結び付く解析viewです。各Loadを元の式のpath・幅・位置でMemorySSAへ対応付け、到達するStoreをMIRの右辺値IDへ結びます。到達不能・照会の未判定・書込み候補を区別し、全候補のbyte値が一致したLoadには定数値を示します。Storeの世代は右辺評価後のcommitに対応し、右辺のLoadはその前の世代を参照します。

世代グラフの検査器は元IRの式を別にたどり、Loadのpath・幅・SSA結果とStoreの確定位置を照合します。各blockのφは実CFGの全先行辺と、入口blockの仮想初期辺へ結びます。メモリ世代IDとblockの保存順は任意で、定義とaccessを一度ずつ対応付けます。記号アドレスの恒等式は既存のアドレス解析を共有します。資源上限は未判定として返し、`graph_evidence`は世代グラフを検査した範囲を示します。

候補の被覆は、Loadごとにメモリ世代・記号アドレス・未確定byteの状態集合を証跡として保持します。検査器は入口状態と各状態の先行辺を照合し、確実に重なるStoreだけが古い寄与を消すこと、残る全候補とStore内のbyte位置が含まれることを確認します。φではアドレスを各流入辺へ同時置換し、ループで広がるアドレスは未知状態へ拡大します。探索の発見順を再現する代わりに、有限な状態集合が必要な先行状態を覆うことを検査します。`validate()`と`query_evidence`はこの範囲を示し、照会・証跡・検査の上限到達は候補集合全体を未判定として残します。

[アドレスの同一視の検査](../src/dataflow/address_identity/verify.rs)は、copy・φでまとめた各classを元のSSAへ結びます。代表値からたどる根拠を起点に、他の値が実際のcopyまたは全流入辺を持つφで導けることと、根拠へ到達できることを検査します。条件ごとに値が異なるφも、後続copyの起点として使えます。代表値の利用可能性はCFGと命令順で別に確認し、ループの過去の値や未定義の値への置換を拒否します。検査は十分条件であり、affine式の計算とbit幅の根拠は既存の解析へ結びます。

[メモリ値の回復](../src/model/middle_ir/recover_memory.rs)は、その根拠から`KnownLoad`を作ります。検査器は元のMIRとの対応と全候補のbyte値を再計算します。既知値の根拠には元のLoadを使い、回復結果の循環した自己参照を防ぎます。実行と戻し変換は元のchecked readを保持します。`middle-ir`は回復後の値を表示し、`middle-c`は同じ引数契約で既存の出力と比較して、局所変数数・関数長の順で小さい出力を選びます。この定数回復は単一関数のscalar値を対象とし、MemorySSA自体の検証境界は表の通りです。

[保存値の同一性](../src/model/middle_ir/saved_values.rs)は、既存の`MemoryValuePlan`で検査したsnapshotとbit範囲を`ReadSaved`へ結びます。同じ保存値を読む値は、コピー・部分抽出・等しいφ入力を通して同じsnapshotを参照します。通常の実行と`lower()`は元のレジスタ範囲を保ち、`lower_saved_values()`は検査済みの保存用レジスタを追加します。後者の比較は`SavedLowering::project_report()`で内部レジスタを除き、元の全レジスタ・RAM・fault・PC・予算を照合します。`middle-ir`はこれらの同一性を表示し、`middle-c`は保存値を展開した候補も既存出力と比較します。

[snapshotの統合](../src/dataflow/memory_values/roots.rs)は、直接検査済みの計画を根拠に使います。提案はsliceを合成し、検査器はbitごとの対応と統合後の保存先の初期化を再検査します。根拠は一段に制限し、統合後も元のLoad/Storeとguest命令境界を保持します。

M0の段階形式v3は、元のLow IRからメモリ定数回復と保存値回復をそれぞれ構築し、直接MIR実行・戻し変換を同じ入力とprefix予算で照合します。保存値用の追加レジスタだけを射影し、元の全状態をJSON Linesへ保持します。この検査は各回復APIの契約を対象とし、readable Cが選んだ表示候補の検査はnative/IR/Cの比較へ結びます。

### C保存先確定後の継続処理

保存先の候補には、既存のspill/reload系譜を優先した割当てと、算術更新の入力・結果を寄せる割当てを用意します。後者も[干渉の独立検査](../src/dataflow/allocation_verify.rs)を通し、幅と旧値の生存範囲を保持します。閉じた非循環領域で、それぞれの保存先から終了処理の共有を試し、同じ引数契約の出力を比較します。`LocalPlanStats.update_hint_pairs`は選択した候補が考慮した更新の組数で、元変数の同定とは別の情報です。

`c-fragment-continuation-v2`は、Cの保存先・幅・メモリviewが確定した後の小さい制御表現です。[提案器](../src/codegen/readable/continuations/propose.rs)が枝ごとの処理に続く共通末尾を探し、[独立検査器](../src/codegen/readable/continuations/verify.rs)が変換前後のASTから`Step / Branch / Return / End`の継続グラフを組み立てます。C断片と順序を照合し、両枝が同じ継続へ届く純粋で全域な条件を除いた根が一致する候補を採用します。v1の条件削除に加え、枝ごとの異なる前処理と条件を保持したまま末尾を共有します。元からreturnが一箇所へ合流する形も対象です。メモリ条件は評価を保持し、循環や非局所脱出は既存の描画経路を使います。検査には命令数・深さ・作業量・断片長の上限があります。

`c-fragment-continuation-v3`は、単一関数Cのflat RWメモリで、先行読込みにより成功が保証される書込みの並べ替えを加えます。[範囲の収集と提案](../src/codegen/readable/continuations/order.rs)は、分岐前に必ず実行する直接Loadと、同じ不変な入力view・offset・実アクセス幅を対応付けます。同じ入力ベースに属する非重複範囲への隣接Storeで、右辺とアドレスが純粋なものを対象にします。検査器は元の読込みprefixが残ることを確認し、継続グラフへ別の方法で書込みを挿入して、byte集合の非重複を照合します。viewのfieldサイズは観測範囲であり、成功の根拠には実際のLoad幅を使います。従来の順序を保つ候補とも比較し、同じ引数契約で局所変数数・関数長の順に小さい出力を選びます。

`c-fragment-continuation-v4`は、[C断片の効果](../src/codegen/readable/continuations/effects.rs)として実際のC変数名のread/writeを加えます。定数・現在の局所値・加算とbit演算からなる全域な更新を、書込みの値が読む変数と独立な場合にStoreの前へ動かします。保存先の共有後に判定するため、異なる仮想レジスタが同じC変数へ割り当てられる場合も依存を保持します。入力viewは入口で捕捉した不変なアドレスに限定し、Load・文脈依存の剰余復元・アドレスの更新は境界として扱います。提案の隣接交換と検査器のグラフ挿入を別に行い、v2/v3の候補も同じ費用で比較します。

PCごとのメモリviewを使う既存printerが生成した断片を固定して比較するため、実装の信頼境界にはprinter・型/保存先の割当て・宣言計画を含みます。検査時は局所変数を関数scopeへ置き、採用後に宣言位置を計画し直します。元PCは由来として残し、観測は返り値・全RAM・最初のfaultと停止性です。MIRのPC・trace・命令予算の検査は元のIRで継続します。生成CはM0の同じ入力でO0/O2・UBSan実行を比較します。

### 次の上層IRの設計境界

次の設計候補は、block引数を持つSSA値・順序付きメモリ効果・継続先を中心にした表現です。CFGの領域変換を済ませてから、φコピーとCの保存先を割り当てます。元PCは由来として保持し、メモリ参照には不変なアドレス値と幅を結びます。これにより、制御を変更した後の描画で元PCの解析結果を再利用する依存を解消します。

この層へ移る際には、[観測契約](../src/model/observe.rs)の`return-memory-v1`を明示します。MIRは全レジスタ・PC・予算を持つ実行の正本として残し、上層の縮約は返り値・全RAM・最初のfaultと停止性を保つ根拠へ結びます。予算切れは未判定として扱います。C continuation graphで扱う重複cleanupを出発点に、printerへ依存する断片を型付きの値・効果へ置き換えていきます。M0の同じ入力で意味・構造・処理の複製を比較して採用します。

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
`UnaryOp::Extract { start, width }`はbitの抽出位置と幅を保持します。AL・AX・EAXと上位8-bitレジスタの読み取り、演算結果の切詰めに使い、幅推論・既知bit解析・SMT・C出力で同じゼロ拡張の意味を追います。抽出・mask・符号拡張を合成する局所還元は、operandを一度評価する順序とfaultを保ちます。除算・剰余・rotateの認識器も幅付き抽出を扱います。Load幅・定数mask・既存の射影から結果が既に範囲内と分かる場合は、その値を直接使います。
`BinaryOp::Insert { start, width }`は左の値の指定bit範囲を右の下位bitで更新します。8/16-bitの部分レジスタ書込みに使い、上位bitの保持を演算の意味に含めます。値グラフは演算の位置・幅もキーに含め、既知bit解析と幅推論は更新部分と保持部分を追います。
証明済みの商・剰余は`UDiv`・`URem`・`SDiv`・`SRem`へ下ろし、後続の幅推論と割当てでも演算の意味を保持します。これらの全域bit-vector演算は[SMT-LIBの定義](https://smt-lib.org/logics-all.shtml#QF_BV)に従い、Cではunsigned演算と明示した境界処理で実装します。
[word_signed_division](../src/transform/word_signed_division.rs)は8/16/32-bitへの射影と符号付き積を区別し、定数除算・剰余を復元します。数値証明を64-bit版と共有し、右シフトには符号拡張と観測幅の条件を確認します。生成する結果は上位bitがゼロのwordで、後続の符号拡張も保持します。
[jump_tables](../src/binary/jump_tables.rs)は先行CFGの経路文脈、copy、stack退避、比較とmaskから表候補を求め、追加デコードと交互に進めます。
候補には読取り位置・範囲の根拠・未探索の残余を保持します。実行時の間接移転は現在のRAMからtargetを評価し、発見済みPCへdispatchします。

[effects](../src/model/effects.rs)は`puts`の外部結果入力を、[module_ir](../src/model/module_ir.rs)は複数関数とimportを扱います。
CALLの戻り先Store、PLT targetのLoad、RET、DIV/IDIV、STOS・MOVSの部分進捗を明示し、faultと命令予算を同じ順序で処理します。
POSIXアダプタはゲスト構造体とホストABIを変換します。TLS guardとstream handleの規則は実行モデルにあります。

[module解析の対応検査](../src/dataflow/module_values/memory_verify.rs)は、元の命令と解析用イベントの代入・読取り・継続先を照合します。CALLのopaque効果、PLT読取り前のstack効果、DIVとREPの未知レジスタ出力を対応付け、入口から到達する効果がMemorySSAへ残ることを確認します。`FunctionValues.memory_projection()`とJSONの`memory_projection`は、その命令・代入・opaque出力・効果の件数を示します。閉じた呼出しのレジスタ効果は`call_footprint`の契約を使い、faultとREPの部分進捗はmodule実行の比較で扱います。

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
要約は[独立検査器](../src/dataflow/call_footprint/verify.rs)が元の命令からたどり、読取り・書換え・直接calleeの集合、通常callの復帰先、末尾callとRETのRSP、戻り先RAMを守るStoreを照合します。再帰は有限回で正常復帰した実行についてcallee間の集合方程式を検査します。`module_values::Analysis::call_summaries()`は検査済み要約を共有参照で返し、`call_verification()`とJSONの`call_verification`は検査対象の件数を示します。

スタックの関係は、元命令から作る保守的な投影に対して`StackAnalysis`が候補を求めます。[スタック検査器](../src/dataflow/stack/verify.rs)は元IRの入口・全後続辺・代入順と照合し、入口RSPに対する係数とoffsetを別の制限付きアフィン計算で検査します。未知へ弱めた不変条件も受理し、戻り辺とアクセスの幅・重複を保持します。`CheckedStack`は検査したsourceと候補を借用し、呼出し検査器の問い合わせとJSONの`stack_verification`をこの検査へ結びます。
レジスタの保存とRAMの保存は個別に判断します。CALLと未知のメモリ効果はMemorySSAの境界になります。
DIV/IDIVを含むcalleeも、正常復帰とreturn slotの保護を確認してレジスタ要約を作ります。商・剰余の結果は未知とし、書き換えられないレジスタの値IDを継続します。

## 表示用IRと局所変数

[reduce](../src/transform/reduce.rs)は補助値を整理し、[web](../src/dataflow/web.rs)はレジスタ定義を使用とのつながりで分割します。
候補ごとの検査を経て、load-mask、SSA定数伝播、算術式選択、純粋な不要代入除去を表示IRへ適用します。
[known_bits](../src/dataflow/known_bits.rs)は既知の0/1を別maskで持ち、φでは両経路に共通するbitを残します。定数伝播と[SSA fact基盤](../src/dataflow/ssa_facts.rs)を共有し、解いた固定点を閉じた不変条件として再検査します。表示IRへは、証明できたLoad-freeの定数部分式を採用します。
[メモリ入力](../src/dataflow/ssa_facts/memory.rs)はMemorySSAのbyte対応表を使い、StoreのSSA入力からLoad結果へ依存辺を加えます。幅の違う書込みもbyteごとに組み立て、φでは書込み元byteの候補を合流します。曖昧なアドレスのStoreにも、その値のbyteだけが届くという範囲を使います。初期メモリ・opaque効果が届くbyteは未知とし、Load自体を元の位置に保って固定点を検査します。
[memory_values](../src/dataflow/memory_values.rs)は、書込み候補が同じ保存値の連続bit範囲を指すLoadの利用先を、その値のスナップショットへ結びます。SSA値の全bitを一度保存し、幅・位置の違うLoadや分割Storeの射影で共有します。シフト・mask・Extract・Insertの定義を遡り、別レジスタ経由のbyteも元のwordへ結びます。純粋なStore右辺は、そのStoreが成功した直後の値も保持できます。循環成分に属さない到達可能ブロックで確保し、ループ終了後の定義も扱います。

[不変値の解析](../src/dataflow/memory_values/stability.rs)は、一度だけ定義される値を起点に、純粋な計算のSSA入力を伝播します。反復中も入力が同じ値なら、循環内での捕捉にも使います。循環内のφとLoadを境界とし、Storeでは右辺とアドレスの入力を分けて検査します。初期値の捕捉は一度通る入口に置きます。

[対応検査](../src/dataflow/memory_values/verify.rs)は実際の候補と初期化状態を照合します。候補側の窓をたどる処理とは別に、検査側はSSA定義とStoreの全bitの出所を評価し、未知のbitをSSA結果・Storeごとに区別します。同じSSA IDでも反復で変わるbitは未知として保持し、不変な結果のbitだけを共有します。C出力は元の候補、SSA値だけを使う復元、保存式も使う復元、不変値を使う循環内の復元を生成し、局所変数数、関数本体長、全体長の順で選びます。

再帰的な出所検査では、64 bitの出所表をヒープ上で共有し、サンプル固有のbitを付けるときに複製します。式の深さ上限を維持しながら、解析の呼出しスタックを小さく保ちます。

[保存値の同値伝播](../src/dataflow/memory_values/value_facts.rs)は、保存元のwordと検査済みLoadの結果を`(保存値, bit開始位置, 幅)`へ結び、copy・bit抽出・φへ伝播します。抽出の合成では入力のゼロ拡張も保ち、合流では全入力の射影を照合します。固定点の計算中に使う未評価状態は、公開時には未知へ変換します。独立した検査が元SSAの全入力・仮想入口・戻り辺を照合し、捕捉した保存先の利用可能性は候補SSAの初期化検査で確認します。

表示用の保存値復元は、検査済み変換を最大3段階まで合成します。各段階でSSA・MemorySSAを作り直し、合流した値を再保存した後の読込みにも元のwordとの対応を伝えます。各段階のCと従来の候補を同じ評価基準で比較し、局所変数数・関数本体長・全体長の順に選びます。`memory_value_rounds`は段階ごとの証拠を、`memory_values`は最初の段階の証拠を保持します。

既定の出力では、最初の局所値還元より前にも保存値復元を一度適用した候補を比較します。入力引数の対応を維持し、代入を大きな式へ畳み込む前に保存値を結ぶ順序も選べます。`pre_reduction_memory_rounds`が還元前の段階数を示し、還元統計と構造の証拠はその後の入力に対応します。検査付き還元APIは、渡された入力そのものに対するブロック検査の証拠を返します。
[arithmetic_graph](../src/transform/arithmetic_graph.rs)と[expression_ir](../src/model/expression_ir.rs)は、分子・上位乗算・商・剰余を値IDと定義位置で結び、算術の証拠を照合します。
[signed_division_expr](../src/transform/signed_division_expr.rs)は純粋な64-bit式の符号付き商・剰余を、正数・負数それぞれの誤差境界から復元します。C helperはunsignedの絶対値とbit列を使い、最小負数の入力も扱います。
[semantic_ir](../src/model/semantic_ir.rs)はblock内の不変な値IDを使い、別々に保存された上位積・符号補正・商・剰余を結びます。分子を一度保存し、代入・メモリアドレス・分岐・返り値の部分式を、利用可能な意味付きの値へ置き換えます。独立した対応検査が、保存時点、元レジスタへの書込み、Load/Storeの順序、制御辺を照合します。
[word用の認識器](../src/transform/word_signed_division/matcher.rs)は式と値グラフで共通です。[source adapter](../src/transform/word_signed_division/source.rs)が参照と値IDを型で分け、Loadの結果は不変な値として扱います。上位bitを失った分子も、必要なwordの一致と保存時点での利用可能性を確認して確保します。
意味演算は、入力の語幅と結果の拡張を区別します。`SignedDivide(width)`と`SignedRemainder(width)`は下位word、`SignedDivideExtended(width)`と`SignedRemainderExtended(width)`はその符号拡張を表します。後者も元レジスタのword値を保持したまま実行IRへ下ろします。絶対値が2以上の認証済み除数では商・剰余がsigned word内に収まるため、Cでは範囲内の変換helperと通常の`/`・`%`を使えます。整数昇格と結果のunsigned変換を明示し、元の全状態比較とCの未定義動作検査を別々に通します。
Loadのスナップショット、保存位置、全命令の代入順も採用条件です。

[LocalPlan](../src/codegen/readable/locals.rs)は表示IRの幅・生存範囲・copy関係・値の系譜から名前と保存場所を決めます。

[SignedWidths](../src/dataflow/signed_width.rs)は、全64-bit値が指定幅の符号拡張と一致するという保存範囲を、既存のSSA固定点で求めます。初期値は任意のu64とし、全phi入力・逐次代入・read/writeを検査してから公開します。unsigned幅とは別の性質です。Cの保存先は、共有する全値が範囲内に収まり、アドレス用の保存先から分離できる場合に`int8_t/16_t/32_t`を選びます。`LocalValue.signed_width`がこの表現を示し、通常のIR演算で読むたびにu64へ戻します。代入時の変換とLoadの順序も保持します。これは生成Cの保存表現の検査で、元ソースの変数型との対応はM3で評価します。
[allocation_verify](../src/dataflow/allocation_verify.rs)は各readの値を、[DeclarationPlan](../src/codegen/readable/declarations.rs)は宣言・初期化の位置を照合します。
[stack_values](../src/dataflow/stack_values.rs)は部分Storeとaliasを含む到達書込み、[stack_role](../src/dataflow/stack_role.rs)はspill/reloadの系譜を供給します。
メモリviewは同じゲストRAMへの表示名として使い、互いのaliasを許します。

## Cの描画と途中再開

[readable](../src/codegen/readable.rs)は公開出力型を持ち、[pipeline](../src/codegen/readable/pipeline.rs)が変換と計画を組み立て、[printer](../src/codegen/readable/printer.rs)が描画します。
共通の[sequence](../src/transform/sequence.rs)が式の規模・評価順の前提を確認し、複数Loadやlazy Selectは順序付きの処理へ展開します。
語幅内の式の整理は、意味演算・rotate・文脈付き剰余を認識した後に行います。[word_arithmetic](../src/transform/simplify.rs)はこれらとLoadを境界にし、外側のmask・抽出・符号拡張が観測する下位bitを保って、加減乗算・bit演算の内側の射影を整理します。C型による切詰めへ移す前に係数をまとめるため、たとえば32-bitの`(x * 8 - x)`を`x * 7`へ戻せます。早いreductionに同じ規則を適用すると除算・rotateの認識形を失ったため、元の解析入力を保つ描画段階へ配置しています。
ループ更新・共有末尾・有限/affine領域の表示も、元の制御と値の対応を検査して採用します。

複数関数では[module_outline](../src/codegen/module_outline.rs)が全Stepからの再入を検査し、[module_readable](../src/codegen/module_readable.rs)が名前付き関数を描画します。
間接移転の局所化は[module_tail_dispatch](../src/codegen/module_tail_dispatch.rs)・[module_switch_keys](../src/codegen/module_switch_keys.rs)が計画し、保存したkeyと実targetを照合して局所ラベルを選びます。
残るtargetはdispatcherへ渡します。通常CALLはCの呼出しを使い、深い再帰や想定外の戻り先ではゲストPCから再開します。

[module_local_plan](../src/dataflow/module_local_plan.rs)は局所値と元の代入を照合し、各レジスタ書込みをゲスト状態へ反映します。
途中PCと成功したCALL/DIV/STOS/MOVSの後には、生存値を実レジスタから復元します。
検査や資源上限に達した関数はレジスタ形式を使い、理由を出力へ記録します。
