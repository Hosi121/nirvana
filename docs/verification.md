# 検証ガイド

Nirvanaは、機械語・IR・生成Cを工程ごとに検査します。
具体入力での実行比較と、定義したモデル全体の対応検査を組み合わせています。
観測項目は[実行モデル](equivalence.md)を参照してください。

## 通常の検査

Rust/Cargoと、`cc`として呼べるC11コンパイラを使います。
fixtureツールにはPython 3、追加の差分検査には`sha256sum`を使います。

```sh
cargo test --all-targets
cargo clippy --all-targets -- -D warnings
cargo fmt --check
```

通常テストにはCFG解析、IR実行、構造化、表示変換、native C比較が含まれます。
`cargo test --test c_evaluation`のように対象を絞って実行できます。
ソルバ検査と大きい生成fixture検査は`#[ignore]`の任意テストです。

## Z3による検査

開発用ソルバは[requirements](../tools/verification-requirements.txt)の`z3-solver==4.15.4.0`へ固定しています。
`uv`で準備する場合:

```sh
uv venv target/verification-venv
uv pip install --python target/verification-venv/bin/python -r tools/verification-requirements.txt
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --all-targets -- --include-ignored --test-threads=1
```

既存のZ3は`NIRVANA_Z3=/path/to/z3`で指定できます。上例は任意テストを資源上限付きで直列実行します。
問い合わせと採否を保存する例:

```sh
python3 tools/build_fixtures.py
cargo run --example verify_expressions -- --z3 target/verification-venv/bin/z3
cargo run --example verify_reductions -- --z3 target/verification-venv/bin/z3
cargo run --example verify_definition_webs -- target/c-fixtures/cc-0/O2/diamond.o
```

`verify_expressions`は式対のSMTとレポート、`verify_reductions`はブロック問い合わせと採否を保存します。
`verify_reductions`の終了コード0はレポート生成の成功を表します。候補の採否はレポートで確認します。
`verify_definition_webs`はオブジェクトごとの改名候補と対応検査の結果を表示します。

## 検査モデル

| 検査器 | 入力と検査する対応 |
| --- | --- |
| [verify](../src/verify.rs) / `pure-u64-v1` | レジスタ・定数・演算・比較・Selectによるu64式のbit-vector同値性 |
| [block_verify](../src/block_verify.rs) / `checked-memory-block-v1` | 全到達ブロック境界の還元。次の境界に必要なレジスタ値、返り値、全メモリ、最初のfaultの対応 |
| [structure_verify](../src/structure_verify.rs) / `structured-flow-v1` | 元IRとNodeを独立にグラフ化し、命令・逐次代入・条件・両分岐先・ループ転送を照合 |
| [web_verify](../src/web_verify.rs) | レジスタ改名後の各readで、元の値とのMUST対応と入口ABIを検査 |
| [allocation_verify](../src/allocation_verify.rs) | 元レジスタとu64保存slotの対応。入口read、上書き、合流、同値copyを検査 |
| [load_mask](../src/load_mask.rs) | 表示用のLoadとmaskの対。変更形・全read・単一定義・同一ブロックの順序と、元のLoadの位置を検査 |
| [division_expr](../src/division_expr.rs) | 上位乗算とシフトによる定数割算。丸め誤差の上限をu128で再計算し、全u64入力に対する十分条件を照合 |
| [add_division_expr](../src/add_division_expr.rs) | `/7`などの補正付き上位乗算。65bitの逆数と丸め誤差の上限から、全u64入力に対する十分条件を再計算 |
| [remainder_expr](../src/remainder_expr.rs) | 同じ入力の証明済み商から `X - (X / d) * d` を `% d` と表示。積・差の非overflowと、各マスクが数値上限の全ビットを覆うことを再照合 |
| [context_remainder](../src/context_remainder.rs) | 商を別レジスタに保存した剰余。定義・商のStore・使用の順序と、同一ブロック内の入力・商への上書きを再照合 |
| [remainder_graph](../src/remainder_graph.rs) | 値グラフで共有された上位乗算と商を照合。商の証明、積の係数、Storeの順序、元の減算左辺との値対応を再検査 |
| [ssa/verify](../src/ssa/verify.rs) | 実際のread・逐次定義・φの全先行辺と出口値の対応。仮想入口と戻り辺を含む実行辺について帰納的に照合 |
| [ssa_constants](../src/ssa_constants.rs) | 任意の初期値に対する定数の閉じた不変条件と、純粋な式片の定数化を照合。メモリ操作と分岐先を保持 |
| [type_infer](../src/type_infer.rs) | SSA値の上位ビット境界を初期値・φ入力・定義式から検査。符号・アドレス・参照形状は根拠付きの検査用候補として出力 |
| [access_expr](../src/access_expr.rs) | 現在の純粋アドレス式に含まれるbase・indexを借用し、modulo 2^64の対応とオペランドの同一性を独立に照合 |
| [address_types](../src/address_types.rs) | 実際のreadと参照幅を照合して表示用の型名を選択。Cの保存型は`uint64_t`を維持し、統合する全メンバーの候補一致を要求 |
| [arithmetic_graph](../src/arithmetic_graph.rs) | 分子・上位乗算・商の定義と剰余の値対応を再構築し、除算証明と積の係数を照合 |
| [expression_ir](../src/expression_ir.rs) | 明示的な値の保存と除算・剰余のlowering。元の定義、追加レジスタ、全命令・代入と数式の証拠を照合 |
| [display_dce](../src/display_dce.rs) | 候補が元の代入列の部分列であることと、削除した純粋代入の死活性をCFG上で検査。全Storeと構文上の全Loadを保持 |
| [finite_region](../src/finite_region.rs) | 前段から導出した有限入力の全組合せについて、純粋領域を抜ける時点の全write先を照合 |
| [affine_region](../src/affine_region.rs) | 有限制御値の全組合せと任意のu64入力Aについて、`a*A+b mod 2^64`の対応を検査 |

純粋式の文法はSelectの両枝を含む式全体に適用します。メモリ操作はブロック検査のモデルで扱います。
ブロック検査は全到達ブロック境界の対応を対象とし、入口関係で結ばれた値以外の初期レジスタは左右独立に扱います。
fault時の比較対象は正確なfaultと全メモリです。SAT反例は小さい具体メモリで再実行し、UNSAT判定にはモデルの全メモリ領域を使います。

| 判定 | 読み方 |
| --- | --- |
| `EquivalentUnderModel` | モデルの制約の下で、差を示す問い合わせがUNSAT |
| `Counterexample` | SATモデルから得た差をIRで再現 |
| 未判定 | 時間・資源上限、未実装の構文、再現条件などにより採否を保留 |

検査の信頼基盤はIRの意味、検査器、エンコーダ、使用するソルバです。
`ReadableC.structure_evidence`は元の還元IR、`display_structure_evidence`はweb改名・load-mask・SSA定数伝播・算術式選択を経て採用した表示IRと構造ASTの対応を保持します。
表示用ループには`finite_regions`・`affine_regions`を付け、導出値域と全中間値のC保存幅も検査します。
`ssa_constants`には検査したSSAの規模と定数・書換え件数、`expression_evidence`には選択した分子の保存・除算・剰余の件数を記録します。
Cの幅選択と描画は、次節の再コンパイル・実行比較で確認します。

## 変換候補の採用

`--verify-reduction`は関数の全到達ブロックで`EquivalentUnderModel`を得た候補を採用します。
未判定や検査失敗では、元IRとその入力レジスタを保持します。
webの改名候補も対応・構造化・描画の検査を経て採用し、失敗時は元の表示経路へ戻ります。
表示処理全体が失敗した場合はエラーを返します。
採否はソルバと資源予算に依存し、退避経路も実行比較の対象にしています。

## Native Cと生成Cの比較

[fixtureガイド](../tests/fixtures/README.md)に入力とABIをまとめています。
`cases/`は固定catalog、`recovery/`は追加のソース例、`generated_recovery`は固定seedの生成例です。
機械語の検査はコンパイルしたELFを入口とし、各fixtureでliftの成功、または既知のrelocationエラーを確認します。

元Cはfixture ABIの有効な引数で実行し、返り値と4状態ワードを比較します。IR間は全メモリのbyte列を比較します。
生成Cは再コンパイルしてIRと照合し、stackを含む全ゲストメモリのdigestも比較します。
これは各入力の実行比較です。fault検査ではabortを捕捉し、最初のfaultのaddress・read/write・widthと、停止前の全メモリを照合します。
整数昇格、Loadの順序、lazy Select、Storeの宛先検査順にも回帰例があります。

保存したCをUBSanで再検査する例:

```sh
NIRVANA_RECOVERY_ARTIFACTS=target/memory-recovery/generated cargo test --test generated_recovery
python3 tools/validate_recovery_artifacts.py
```

`--inputs FILE`で空白区切りの4ワード行を指定できます。保存先にあるO0/O1/O2/Os/O3の各構成を検査します。
追加の生成比較はソース数1〜64（既定64）で実行し、ソース・機械語・入力・生成C・フラグ・ハッシュを`target/generated-recovery/`へ保存します。

```sh
NIRVANA_RECOVERY_CASES=16 cargo test --test generated_recovery seeded_pipeline_differential_campaign -- --ignored --exact
```

CFG向けの生成比較は、入れ子のループ、共有する末尾、複数の入口を持つループ、早期returnを含みます。
ソース数は1〜64、既定16です。

```sh
NIRVANA_RECOVERY_CASES=16 cargo test --test generated_recovery seeded_control_flow_differential_campaign -- --ignored --exact
```

`NIRVANA_RECOVERY_PROFILES=O0,O1,O2,Os,O3`でprofileを選べます。既定はO0/O2です。
O0の基準実行を補完し、要求列と実効列をmanifestに記録します。各構成のlift成功を比較の前提にします。

## 元変数との対応評価

[評価ツール](../tools/measure_source_recovery.py)はGNU readelfを使い、非debug版と機械語が一致するGNU C O0/DWARF5コピーを参照します。
既知対応の分割・混在と、新しく対応づけた範囲を分けて集計し、曖昧な位置は未判定として記録します。

```sh
cargo build --example inspect_stack_frame --example measure_variables
python3 tools/measure_source_recovery.py --help
python3 -m unittest discover -s tools/tests
```
