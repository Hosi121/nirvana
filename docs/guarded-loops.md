# 入口ガードと累積式の整理

基準は`57c589a`、C出力の実装は`939ea54`です。
今回の区切りは、入口のifとループ末尾の条件が初回に同じ意味になる形をまとめ、
左に連なる累積式を複合代入で読めるようにすることです。
元Cを読む処理や、AIによる後処理は使っていません。

## 実際に変わる形

`sum O2`の奇数側では、counterが1の時点で次の入口条件を確認していました。

```c
counter = 1;
if (limit != 1) {
    do {
        accumulator = accumulator + 1 + counter * 2;
        counter += 2;
    } while (limit != counter);
}
```

同じ箇所は次のようになります。counterの初期値を条件へ埋め込まず、各回の値を読みます。

```c
counter = 1;
while (limit != counter) {
    accumulator += counter * 2 + 1;
    counter += 2;
}
```

`cyclic-guard O2`でも入口のifとdo/whileが一つのwhileになります。
このfixtureはcounterを8で折り返すため、単調性や一般的な停止性を仮定する変換ではありません。
関数全体の分岐や複製されたループをすべて元ソースどおりに統合する機能ではありません。

## 初回の条件だけを確認する

`guarded_loop::Facts`は、最終Cの保存場所ごとに初期化済みかどうかと、正確に分かる定数を追います。
代入を記載順に観測し、値が不明なLoadでも、正常に次の文へ到達した時点で初期化を記録します。
分岐・ループでは書き換わる可能性のある定数を捨てます。
ループ本体を表示する前にも本体内の書込みを調べ、初回だけの定数を次回以降へ持ち込みません。

入口がif、真側が一つの後置判定ループ、偽側が空である形を対象にします。
条件はLoadを含まない式に限定し、既知の定数を置いた比較用の式が同じ真偽になる場合だけ採用します。
検査用の簡約式をCへ出力することはありません。返す条件は元の末尾判定を保ちます。

- 入口で読む保存場所は、新しい条件でも読むことを要求します。
- 新しい条件のすべての読出しは、初回から初期化済みであることを要求します。
- 本体途中のcontinue・非局所転送・入れ子ループがあれば対象外です。
- 本体はそのまま残し、break・return・faultが起きる順序も維持します。
- 非局所転送を持つ関数では、C表示側がこの追加変換を見送ります。

末尾判定だけに使う一時変数は、入口で未初期化の場合があります。
最終のレジスタ代入Stepがcounterへコピーしている場合は、順序付きの値tokenで終了時の等値性を確認します。
他のscalar書込みには新しいtokenを割り当て、後の上書きで等値性を壊します。
初期化済みで入口でも読んでいた別名へ置き換えられる場合だけ、条件のレジスタ参照を変えます。
コピーそのものは本体に残します。最終StepがMemory destinationを含む場合は、この別名回収を行いません。

さらに、アドレスビューがコピーの右辺をdescriptorへ置き換える場合は、
元の一時変数の最後のC参照まで消える可能性があります。この保存場所の別名置換は見送り、checked Loadを保持します。
別名置換で`x != x`のような自己比較が現れる場合も、C警告を避けるため元の形を保ちます。
後段で一般の代数簡約や不要変数除去を追加する方法は使いません。

上限は保存場所・Nodeが4,096、式workが65,536、深さ64、fact workが1,000,000です。
最終コピーStepは16代入までです。資源や情報が不足した候補は元の表示へ戻します。
元IRとその構造化AST、既存の構造certificateは変更しません。

## 累積式の複合代入

`self_update::extract`はAdd/Mul/And/Or/Xorの同じ演算が左へ連なる形から、
保存先と同じ最初のレジスタ参照だけを取り出します。
実際のIRで使われていた`(1 + accumulator) + rhs`にも対応するため、
最も内側の「定数 op 自分」だけは、効果のない定数を右辺先頭へ残して取り出します。
他レジスタやLoadの右にしか自分がない形、異なる演算が混ざる左枝は変換しません。

残りのオペランド、Loadの回数と順序、lazy Selectを保持します。
式木は2ノード小さくなり、元IRは書き換えません。
抽出器は深さ128・16,384ノードを超えたら、callbackやcloneの前にNoneを返します。
C出力では複数Loadがある式をこの経路へ渡さず、従来の順序付き評価計画に残します。
狭いC保存先でも、演算前に右辺をuint64_tへ昇格させてから代入時に切り詰めます。

## 同じ入力での検証

既存20ソースとrecovery 8ソースの56構成中、同じ49構成を比較しました。
GCC 13.3.0、C11・Wall/Wextra/Werror/pedantic・fno-lto・O0/O2を共通にし、前後49本ずつのCをコンパイルしています。
未対応の再配置7構成は両方で拒否します。

| 計測 | 前 | 後 |
| --- | ---: | ---: |
| if | 73 | 71 |
| 後置判定do/while | 8 | 6 |
| 複合代入 | 40 | 46 |
| 関数内token数 | 16,752 | 16,722 |
| 関数全体byte数 | 84,551 | 84,359 |
| 局所変数 / コピー / goto | 167 / 21 / 14 | 167 / 21 / 14 |
| mask / cast / 更新節付きfor | 110 / 34 / 4 | 110 / 34 / 4 |

この構成数と名前・構文の数は、元ソースとの類似度や一般の復元精度を示す値ではありません。
空のforに複数の計算を押し込む形は採用せず、while本体へ残します。

`cyclic-guard.c`を追加しました。indexと停止値を0..7に制限し、折り返しを含むrolling hashを計算します。
O0/O2を必須にし、両構成69入力ずつ、計138比較を追加しました。

| corpus | native / IR / readable Cの比較 |
| --- | --- |
| 既存20ソース | 33/40構成 × 63入力 = 2,079 |
| recovery 8ソース | 16/16構成 × 69入力 = 1,104 |
| 生成8ソース | 16/16構成 × 67入力 = 1,072 |
| 合計 | 65/72構成、4,255入力比較 |

native CとIRは返り値・4状態ワード、readable CとIRはstackを含む64KiB全体のdigestも比較します。
専用のnative検査は最初のfaultアドレスと停止前の全バイトを比較します。
抽出器8検査、guard解析15検査に加え、Cで実行するwraparound・狭い保存先・fault・コピー参照消失・自己比較の回帰検査を追加しました。
独立guard replayは命令数上限0..69と、通常終了・fault・部分メモリを比較しています。

全340テスト（通常331＋任意SMT9）、Clippy警告ゼロ、rustfmtを確認しました。
生成16構成はUBSan付きの1,008入力比較でも一致し、診断はありません。
最初の全体実行では模擬solverの一時スクリプト起動が一度ETXTBSYとなり、単独再実行は成功しました。
テスト用パスに原子的な連番と排他的作成を加えて上書き衝突を防ぎ、全体を再実行して成功しました。
この一度の起動失敗の原因を、パス衝突と断定はしていません。元ログも成果物へ残します。
solverの応答・反例の検査や、製品側のUnknownで元式を保持する挙動は変えていません。

今回の確認はモデル内の純粋な初回条件・コピーの等値性と、具体的な実行比較です。
既存のSMTやAST certificateがC表示全体を証明するものではありません。

```sh
cargo test --test guarded_loop --test self_update --test c_evaluation --test recovery_fixture
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --all-targets -- --include-ignored
cargo build --bin nirvana
python3 tools/compare_readable_output.py --before /path/to/57c589a/nirvana --out target/guarded-loops
NIRVANA_RECOVERY_ARTIFACTS=target/guarded-loops/generated cargo test --test generated_recovery
python3 tools/validate_recovery_artifacts.py --artifacts target/guarded-loops/generated --out target/guarded-loops/ubsan
```

`target/guarded-loops/`に機械語、前後のC、比較JSON、コンパイラとSHA-256、検査ログを保存します。
生成物はGit管理せず、実装・fixture・検査・生成道具をコミットしています。
