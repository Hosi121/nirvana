# 検証手順と保証の範囲

観測対象は[同値性の契約](equivalence.md)に従い、具体入力での一致、モデル内の全入力に対する検証、生成Cの検査を区別します。

## 通常の検査

リポジトリのルートで実行します。Rust/Cargoと、`cc`として呼べるC11コンパイラが必要です。
fixtureの保存・追加ツールにはPython 3を使います。通常のデコンパイラ実行にZ3は不要です。

```sh
cargo test --all-targets
cargo clippy --all-targets -- -D warnings
cargo fmt --check
```

通常テストはCFG解析、IR実行、構造化、表示変換とnative C比較を含みます。
ソルバ依存のテストは`#[ignore]`で、通常は実行しません。
部分実行は`cargo test --test c_evaluation`などで指定できます。

## 任意のZ3検査

開発用ソルバは[requirements](../tools/verification-requirements.txt)の`z3-solver==4.15.4.0`へ固定しています。`uv`を使う準備例:

```sh
uv venv target/verification-venv
uv pip install --python target/verification-venv/bin/python -r tools/verification-requirements.txt
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --all-targets -- --include-ignored --test-threads=1
```

既存のZ3も`NIRVANA_Z3=/path/to/z3`で指定できます。既定の時間・資源上限を使い、上例は負荷を避けて直列実行します。
問い合わせを保存して調べるには次を使います。

```sh
python3 tools/build_fixtures.py
cargo run --example verify_expressions -- --z3 target/verification-venv/bin/z3
cargo run --example verify_reductions -- --z3 target/verification-venv/bin/z3
cargo run --example verify_definition_webs -- target/c-fixtures/cc-0/O2/diamond.o
```

`verify_expressions`は式対のSMTとレポートを、`verify_reductions`はブロック問い合わせと採否を保存します。
後者の終了コード0はレポート生成の成功であり、全候補の採用ではありません。
`verify_definition_webs`はソルバを使わず、オブジェクトごとの改名候補と検査結果を表示します。

## 各検査器の境界

| 検査 | 保証の対象 | 対象外 |
| --- | --- | --- |
| [verify](../src/verify.rs) / `pure-u64-v1` | Loadのないu64式対のbit-vector同値性。比較・masked shift・上位積・Selectを符号化 | メモリ、CFG、機械語、C |
| [block_verify](../src/block_verify.rs) / `checked-memory-block-v1` | 同じCFG境界での還元。対応入力から次の境界・返り値・全メモリ・最初のFaultを比較 | リフト、構造化、C描画 |
| [structure_verify](../src/structure_verify.rs) / `structured-flow-v1` | Nodeを独立にグラフ化し、元の命令・逐次代入・条件と両制御先・ループ転送を対応検査 | 表示用のcompact・ループ整形・C文字列 |
| [web_verify](../src/web_verify.rs) | Reg以外の構文を変えない改名。CFG上のMUST関係で書込み前の各readを検査し、入口ABIと任意のfresh初期値を扱う | 最終レジスタ配列の一致、演算の書換え、C |
| [allocation_verify](../src/allocation_verify.rs) | 元Regとu64保存slotのMUST対応。未定義の入口read、上書き、合流と同値copyを検査 | Cの幅選択・描画、元Reg配列の最終一致 |
| [finite_region](../src/finite_region.rs) | 実際の前段から得た有限値集合の全組合せで、純粋領域の正常fallthroughと全write先を照合。中間値の最大も記録 | 領域内のメモリ・例外・非局所転送、命令trace、C全体 |
| [affine_region](../src/affine_region.rs) | 有限制御値の全組合せと、任意のu64入力Aに対する厳密な `a*A+b` の対応。演算はmod 2^64、全write先と中間値の上限を検査 | 非線形演算、A依存の分岐、領域内メモリ・例外・非局所転送、C全体 |

純粋式の検査は、非選択枝に含まれるLoadも未対応です。メモリを自由変数へ置き換えて証明しません。
SMT検査ではUNSATのみを`EquivalentUnderModel`とします。SATはモデルをIRで再実行して差を確認し、不完全・不正・再現不能なモデルは成功へ昇格させません。

ブロック検査では入口関係で対応させないレジスタの初期値を左右独立に扱い、後続境界の必要な関係も確認します。
Fault時は正確な失敗と全メモリを比較してレジスタは観測せず、有限回のループ展開ではなく全ブロック境界の対応を検査します。
SAT反例の再実行にだけ小さいメモリ制限を使い、その制限からUNSATの主張はしません。

構造化の検査はrecoverの成功条件です。webの候補も独立検査を通してから表示に使います。
元IRの構造証拠と改名後の表示IRの構造証拠を分け、C表示全体の証明に読み替えません。
検査器・エンコーダ自体は証明支援系で証明しておらず、共通IRの意味と検査実装も信頼する部分です。

表示用ループの候補は役割名から提案しますが、採用には有限領域またはaffine領域の独立検査を必要とします。
値域は変更しない前段から導出し、記録した全中間値がC保存幅に収まることも検査します。証拠は `ReadableC.finite_regions`・`affine_regions` に分け、元CFGの構造証拠を保持します。

## 未判定と退避

時間切れ、`Unknown`、未対応、資源上限は検証成功でも誤変換の反例でもありません。
`--verify-reduction`は全ブロックの採用条件が揃わなければ、関数全体の元IRを保持します。
通ったブロックだけを候補へ差し替えず、元IRに必要な全入力レジスタも保持します。
webの解析・対応検査・候補の構造化や描画に失敗した場合も、元の表示経路へ退避します。
元の描画も失敗すればエラーを返し、部分的なCの返却や無限の再試行はしません。

同じ候補でも、ソルバと予算によって採否が変わり得ます。
退避経路のテストでは、元IRが保持されることと、その生成Cの動作を検査します。

## Native fixtureとCの検査

入力とfixture ABIは[fixtureガイド](../tests/fixtures/README.md)を参照してください。
`cases/`は固定catalog、`recovery/`は独立したソース例、`generated_recovery`は固定seedの生成例です。
`machine_pipeline`はコンパイルしたELFを自作reader/decoderへ渡し、手書きIRをfrontend入力に使いません。
既知の未対応relocationを明示的に検査する例を除き、新しいlift失敗を黙ってskipしません。
元Cとは返り値と4状態ワードを比較し、IR間は全メモリをバイト列で比較します。
再生成Cはstackを含む同じguest領域全体のdigestも照合します。digest一致は形式証明ではありません。
共通のfault検査ではabortを捕捉し、最初のfaultのアドレス・read/write種別・幅と停止前の全メモリをIRと比較します。
Cの整数昇格、Loadの順序、lazy Select、Storeの宛先検査順も独立した回帰例を持ちます。

元変数との対応は任意の[評価ツール](../tools/measure_source_recovery.py)で測れます。非debug版と機械語が一致するGNU C O0/DWARF5コピーだけを使い、既知対応の分割・混在と新しい対応範囲を分けます。範囲外・曖昧な位置を成功に数えません。
`cargo build --example inspect_stack_frame --example measure_variables` の後、ツールの `--help` に従ってcase一覧・比較用metadata・frame helperを指定します。parserの検査は `python3 -m unittest discover -s tools/tests` です。

```sh
NIRVANA_RECOVERY_ARTIFACTS=target/memory-recovery/generated cargo test --test generated_recovery
python3 tools/validate_recovery_artifacts.py
```

後者は保存した元C/readable CをUBSan付きで再実行し、診断と観測差を検出します。
