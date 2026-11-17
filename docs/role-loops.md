# 役割名とforの更新節

今回の区切りは、`valueN`で隠れていたループ内の使い道を表し、順序を保てる更新処理をfor節へ移すことです。
基準は`6990e7f`、C出力の実装は`d7cfdb2`です。AIによる後処理や元Cの読み取りは使っていません。

## 実際の出力

`sum -O2`のループの一部は、次のようになります。型と演算は従来どおりです。

```c
do {
    accumulator = accumulator + 1 + counter * 2;
    counter += 2;
} while (limit != counter);
```

`multi-exit-prefix -O2`では、次の形になります。終了時のcounter値も後で使います。

```c
for (; counter <= 2; counter += 1) {
}
```

初期化は元の位置に残します。メモリからcounterを読むO0のループでは、条件前の読出しと更新時のreload/storeも残します。
長いforヘッダは改行して表示します。構文を短くするためにstackへのアクセスを消す変更ではありません。

## 役割は最終的な保存場所から判断する

`value_role::infer`は表示用Node ASTと、仮想レジスタからCの保存場所への対応を読み取ります。
式、制御、値を変更・評価する解析ではありません。

| 役割 | 根拠 |
| --- | --- |
| `counter` | 同じ保存場所へのゼロ以外の定数加減算と、ループ脱出に関係する条件 |
| `accumulator` | 同じ保存場所を算術・bit演算で更新し、無関係な代入が混ざらないこと |
| `limit` | counterとの比較相手が単純な保存場所で、そのループ内で書き換わらないこと |
| `address` | bare registerを介するLoad/Storeのアドレス使用。数値・条件・return・store値にも使う場所は除外 |

同じ保存場所へ割り当てた別々の仮想レジスタをまとめて分析します。
役割が矛盾する場所は仮名を残し、同じ役割が複数あれば番号を付けます。
パラメータ、ビュー、ヘルパーと重複しないC識別子を生成します。
CLIは役割名を使い、ライブラリ既定の明示表示は従来の`vN`を使います。
`LocalValue.role`には表示形式と独立して推定結果を返します。

統合時には、O0の保存場所がprologueではポインタ、ループでは数値、最後は返り値にも使われる例を確認しました。
この全体を`address`と呼ぶと誤解を招くので、アドレス以外の読出しがある場所はAddress候補から外しています。
Counter等も元ソースの変数名や型、単調性、停止性の証明ではありません。
保存場所の共有により、ループ外で一時的に別用途の値が入る場合は残ります。元変数ごとの生存期間分割は今回の範囲外です。

深さ128、式とNode合計32,768、保存場所4,096、解析work 1,000,000を上限にします。
超えた場合は役割の結果全体を破棄し、仮名へ戻します。途中までの名前を採用しません。

## 更新節へ移せる形

`for_loop::recover`は`while_header`から、条件前処理・条件・本体・更新の借用スライスを返します。
更新は元の末尾にある連続したStepのままです。命令内の逐次代入やcopyback、必要な隣接reloadを並べ替えません。

- 条件に使う保存場所の定数更新、または条件の値を使う定数更新のstoreを目印にします。
- 条件前処理はforの条件内に置き、初回・次回・最後に偽となる訪問でも元の順で実行します。
- 本体途中のcontinue・非局所転送・入れ子ループがあれば変換しません。末尾のcontinueだけを除きます。
- break・returnの経路では更新を実行しません。
- 更新内の各レジスタ式はLoad高々1個、storeのアドレスと値はLoadを含まない式に限ります。
- メモリstoreを目印にしても、読出し元と書込み先のaliasや、counterの進行を証明したとは扱いません。

storeでは境界検査以外に競合するfaultがない形だけを移します。
複数Loadや複雑なstoreは既存の文による評価計画に残し、C11の引数評価順へ依存させません。
更新は16代入・16Step、対象ASTは4,096 Node・深さ64、式合計65,536 Node・深さ128で打ち切ります。
認識できない形は従来のwhile・do/while・一般のループを使います。

元の実行IRと構造化ASTは変更しません。既存の構造certificateは元のASTまでが対象で、今回のfor表示全体の証明ではありません。

## 同じ機械語での比較

既存20ソースとrecovery 7ソースのO0/O2、54構成中の同じ47構成で比較しました。
GCC 13.3.0、C11・Wall/Wextra/Werror/pedantic・fno-ltoを共通にし、前後それぞれ47本をコンパイルしています。
再配置が未対応の7構成は両版とも拒否します。

| 計測 | 前 | 後 |
| --- | ---: | ---: |
| 数値局所変数の宣言 | 158 | 158 |
| 役割名の付いた保存場所 | 0 | 15 |
| 更新節を分離したfor | 0 | 4 |
| 単純な局所値コピー | 20 | 20 |
| goto / mask / cast | 14 / 104 / 33 | 14 / 104 / 33 |
| 関数内token数 | 16,051 | 16,055 |
| 関数全体byte数 | 80,421 | 80,914 |

名前が長くなり、forに区切りが増えるため、サイズは少し増えます。
役割名の数は記述できた範囲であり、元ソースとの一致率や一般の復元精度ではありません。
測定道具は宣言から局所名を集める方式に変え、`valueN`以外の名前や更新節のコピーも数えます。
識別子が変わっただけで変数数やコピー数が減ったことにしないためです。

## fixtureと検証

`volatile-bound.c`を追加しました。上限の再読、動的添字、途中breakを含み、O0/O2の全構成を必須にしています。
native検査はfixtureの返り値と4状態ワードをIRと比較し、readable CとIRではstackを含む64KiB全体のdigestも比較します。

| corpus | 比較 |
| --- | --- |
| 既存20ソース | 33/40構成 × 63入力 = 2,079 |
| recovery 7ソース | 14/14構成 × 69入力 = 966 |
| 固定seedの生成8ソース | 16/16構成 × 67入力 = 1,072 |
| 合計 | 63/70構成、4,117入力比較 |

役割解析12検査、for認識11検査、Cで実行する新しいfor回帰検査を追加しています。
独立したfor replayでは命令数上限0..79、全レジスタ・全メモリ・faultを比較します。
native回帰検査は正常経路、break、更新を飛ばすcontinue、条件読出しのfault、bodyの書込み後に更新storeがfaultする場合を比較し、
最初のfaultアドレスと停止前の全バイトも照合します。メモリ表示の有無と二つの表記、O0/O2で実行します。

全314テスト（通常305＋任意SMT9）、Clippy警告ゼロ、rustfmtを確認しました。
生成16構成はUBSan付き1,008入力比較でも一致し、診断はありません。
SMTの保証は既存モデルの範囲です。今回の役割名・for表示全体を形式証明したものではありません。

```sh
cargo test --test value_role --test for_loop --test c_evaluation --test recovery_fixture
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --all-targets -- --include-ignored
cargo build --bin nirvana
python3 tools/compare_readable_output.py --before /path/to/6990e7f/nirvana --out target/role-loops
NIRVANA_RECOVERY_ARTIFACTS=target/role-loops/generated cargo test --test generated_recovery
python3 tools/validate_recovery_artifacts.py --artifacts target/role-loops/generated --out target/role-loops/ubsan
```

`target/role-loops/`に前後のC・機械語・比較JSON・全テストログを残します。
コンパイラ、フラグ、ソース・機械語・両CLIのSHA-256も記録しています。生成物はGit管理せず、解析・fixture・検査・道具をコミットします。
