# 純粋な式のtranslation validation

`verify` は簡約器から独立して、変換前後の二つのExprをSMT-LIBへ変換する。
モデルIDは `pure-u64-v1`。入力レジスタはすべて制約なしの64-bit値とする。
検証の主張は、このモデルのもとで全入力について二つの式の値が等しいこと。
CFG、メモリ、機械語、生成C全体の同値性までは主張しない。

## 意味と判定

演算は[同値性の契約](equivalence.md)のu64モデルに従う。
SMTの加減乗算・ビット演算は64-bitのbit-vectorとして出力する。比較はBoolを0/1のu64へ変換する。
シフト数はSMT側でも明示的に63でマスクする。SMTのシフト演算自体にx86のマスクを期待しない。
上位乗算は二つの値を128-bitへゼロ拡張して掛け、上位64-bitを取り出す。
Selectは条件が非0ならtakenを選ぶiteとして符号化する。

問い合わせは `before != after` が成立する入力の存在判定。

| ソルバの結果 | APIの結果 | 候補の採用 |
| --- | --- | --- |
| UNSAT | EquivalentUnderModel | この式対に対して採用可能 |
| SAT＋完全な値取得＋IRで差を再現 | Counterexample | 元の式を保持 |
| unknown、時間切れ、未対応、プロトコル／プロセス失敗 | Unknown | 元の式を保持 |

`Solver::checked_rewrite` がこの採否を行う。変換器は候補を出し、検査器が判定する。
Loadは選択されない枝に含まれていても未対応とする。メモリを純粋な変数に置換して証明してはならない。
4096以上のレジスタ番号、深さ256超、訪問ノード100,000超もResourceLimitとして未判定にする。
これは式の値域の制限ではなく、検査器の実装上の資源上限。

solverのstdoutは期待する応答だけを受け付ける。非0終了、stderr、追加のerror応答は成功にしない。
SAT時は全入力レジスタの値を取得し、元のIRインタプリタで変換前後を実行して差を確認する。
欠落・重複・余分なモデル値や、再実行で差が出ないモデルはUnknownにする。
ソルバにはタイムアウトを渡し、別途wall-clock上限で停止・回収する。

## 再現

ソルバは開発時の任意依存で、通常のデコンパイラ実行には不要。
既存のZ3がある場合は `NIRVANA_Z3=/path/to/z3` を使える。検証に使った固定版の準備例:

```sh
uv venv target/verification-venv
uv pip install --python target/verification-venv/bin/python -r tools/verification-requirements.txt
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --test verification -- --include-ignored --nocapture
cargo run --example verify_expressions -- --z3 target/verification-venv/bin/z3
```

最後のコマンドは `target/verification/` に式対ごとのSMTファイルと `report.tsv` を保存する。
問い合わせが未判定だった場合もレポートを残し、コマンドは非0終了する。未対応Loadの負例だけは想定されたUnknownとして検査する。

```sh
target/verification-venv/bin/z3 target/verification/machine-cmp.smt2
```

上の単独問い合わせの期待結果はunsat。`wrong-shift-width.smt2` はsatである。

## 実行した検査

Z3 4.15.4で次を実行した。

- 実際のsimplify出力42式対がUNSAT。各式対について全u64入力で等しい。
- 各42式の候補へ1を足した誤変換がSAT。反例をIRでも再現し、元の式を保持。
- 幅を32-bitと誤るシフト、overflowの無視、truthinessと値の混同、signed/unsignedの混同もSAT。
- 13演算×7境界値×7境界値の637問い合わせで、エンコーダの定数演算とIR実行結果が一致。
- ソルバ欠如・時間切れ・不正応答・偽のSATモデルなどが、採用につながらないことを通常テストで確認。

得られた反例の一部:

| 誤変換 | 入力 | 元の結果 | 誤変換の結果 |
| --- | --- | --- | --- |
| `(x + 1) == 0` を常に0とする | x=18446744073709551615 | 1 | 0 |
| unsigned比較をsigned比較へ変える | x=18446744073709551614, y=0 | 0 | 1 |
| shift countを31でマスクする | x=554050781055, count=32 | 18446743519658770432 | 554050781055 |

## 信頼する部分と残る範囲

UNSATの主張は、独立エンコーダの意味付けとZ3の正しさを信頼する。独立の証明カーネルで証明証明書を検査してはいない。
IRとの境界値比較はエンコーダの検査材料であり、エンコーダ自体の全入力の正しさの形式証明ではない。
SATの反例再実行は誤った反例を採用しないための追加検査で、UNSATの独立証明にはならない。

通常のreadable-cはソルバを起動しない。任意の `--verify-reduction` モードでは、
[メモリ付きブロックの検査器](block-verification.md)を還元器の採否へ接続している。
42式対の検証を、簡約器の全規則・全適用箇所や関数全体の検証済みという意味に広げない。
メモリ付きブロックとループ境界の状態対応は別モデルで扱う。
構造化ASTには[独立したグラフ化と対応検査](structure-verification.md)がある。

参考: [Z3のbit-vector仕様と例](https://microsoft.github.io/z3guide/docs/theories/Bitvectors/)、
[Alive2の論文](https://web.ist.utl.pt/nuno.lopes/pubs/alive2-pldi21.pdf)。NirvanaはLLVM IRやAlive2を組み込まない。
