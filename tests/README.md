# テストガイド

統合テストは分野別の10 suiteにまとめています。入口は`tests/<suite>.rs`、各ケースは同名ディレクトリ内のモジュールです。
外部公開APIの比較は統合テスト、非公開の実装詳細の検査は担当するソースモジュールのunit testに置きます。

| Suite | 対象 |
| --- | --- |
| `binary` | ELF・ローダ・デコーダ・命令・ジャンプテーブル |
| `control_flow` | CFG・支配関係・構造化・ループ |
| `dataflow` | SSA・生存範囲・MemorySSA・型候補・変数割当て |
| `model` | IR実行・メモリ・評価順・制御転送 |
| `transform` | 式・還元・剰余や除算の復元・表示変換 |
| `codegen` | Cの式・変数名・宣言・読みやすさ・評価順 |
| `module` | 複数関数・CALL/RET・局所値・途中再開・状態の一致 |
| `end_to_end` | 元C→ELF→IR→再コンパイルCの比較 |
| `verification` | 独立検査器・SMT・候補の採否 |
| `cli` | CLIのオプション・JSON出力 |

## 実行

```sh
cargo test --locked --all-targets
cargo test --locked --test dataflow memory_ssa::
cargo test --locked --test end_to_end machine_pipeline:: -- --nocapture
cargo test --locked --lib codegen::readable::declarations::tests
python3 -m unittest discover -s tools/tests
```

絞り込み名は`<ケースファイル名>::<テスト名>`です。`-- --list`で確認できます。
任意のソルバ・Clang・生成比較は`#[ignore]`で区別します。依存の準備と観測項目は[検証ガイド](../docs/verification.md)を参照してください。

## 共通処理

共通helperは`tests/support/`に置き、各suiteの`mod support`で使用するモジュールを選びます。
例えば[プロセス起動と一時領域](support/native.rs)は、native比較を行うsuiteから読み込みます。

- `native`: 一時ディレクトリ、コンパイラ起動、入力と出力、期限付き実行。コンパイラはsuite内で最大4個を同時実行します。
- `checked_c`・`module_fixture`: 生成Cのコンパイルとゲスト状態の比較。
- `memory_trace`・`dispatch_oracle`: 実際の書込み元や分岐の独立した参照結果。
- `ir`・`programs`・`rewrite_cases`・`loop_headers`: 小さなIR構築部品と共有ケース。

ケース固有のコンパイラフラグや観測形式は、そのケースに残します。
外部プロセスを起動するときは、`native::compile`・`compile_output`・`run_output`・`command_output`を使えます。

## ケースの追加

1. 担当suite内にモジュールを追加し、suite入口で宣言します。
2. 元Cを入口とする比較には、[fixtures](fixtures/README.md)へ入力とABI・フラグを置きます。生成物は`target/`に保存します。
3. 正例に加え、採用条件を崩した候補・alias・途中停止など、その変更が誤りやすい境界を検査します。
4. 絞った比較を通した後、通常の全targetテスト・Clippy・fmt・Pythonテストを実行します。

候補を生成する処理と検査器は個別に呼び出します。生成CはC11の厳格な警告設定で再コンパイルし、元の観測対象を維持して比較します。
