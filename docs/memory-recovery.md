# 入力メモリ・添字・局所変数の回収

`--emit readable-c`で、返り値と境界検査付きゲストメモリを保ちながら、
入力基底からの位置、stride付き添字、局所値の保存幅を名前で表します。
対象は整数IRからCへの表現です。元ソースの変数名・型・配列長・所有権や、
異なる入力ポインタ間の非aliasは推定しません。
従来の[スタックビュー](stack-views.md)と[readable C](readable-c.md)を拡張する機能です。

## 入力基底とspill

`AddressAnalysis`は、指定された入力レジスタをそれぞれ「入口値＋定数」の基底とします。
それ以外のレジスタと初期メモリは未知です。ポインタ型か整数型かを仮定する解析ではありません。
コピー、定数の加減算、一致する合流の事実をCFG上の固定点で追い、
命令内の代入ごとに直前の状態を区別します。オフセットはmodulo 2^64です。

既知の場所へ既知の値をU64で保存した場合は、同じ8バイト全体を再読するLoadの値を追えます。
これは解析上のspill/reloadの事実であり、実際のStoreやLoadを除去する変換ではありません。
異なる幅の書き込み、重なる書き込み、aliasの可能性がある書き込みで該当事実を無効にします。
異なる入力基底は互いにaliasし得るので、同じ基底の定数オフセットなどで
バイト範囲の非重複を確認できる場合だけ事実を残します。未知の書き込み先ではメモリの事実をすべて捨てます。

`origin_before`は、Loadをどこかに含む問い合わせ式を拒否します。
両腕が同じ値でも、faultし得る条件を持つSelectのLoadは消せません。
不一致の合流や資源上限では未知へ戻し、未解決のアクセスは元のアドレス式で出力します。

## フィールドと添字のdescriptor

固定オフセットのアクセスは入力基底ごとにまとめ、Cでは次のような形で表します。
これは値の構造体ではなく、整数のguest addressを保存するdescriptorの構造体です。

```c
const struct {
    struct nirvana_view base;
    struct nirvana_view field_8;
} object_0 = {{arg0}, {arg0 + 8}};
v0 = nirvana_view_load(&m, object_0.field_8, 2);
v1 = nirvana_view_load(&m,
    nirvana_view_index(object_0.base, v2, UINT64_C(8), UINT64_C(0)), 8);
```

基底は関数入口で保存します。添字は各アクセス時点の式を評価し、入口値へ置換したりループ外へ持ち出したりしません。
`base.address + offset + index * stride`はu64のmodular arithmeticです。
定数乗算と定数左シフトを回収し、シフト数はIRと同じく63でマスクします。
負のオフセットやstrideもu64のビット列で扱います。
係数1で加算される基底候補が複数あれば回収せず、scale付きの入力値は添字としてそのまま保持します。
LoadやSelectを含む添字アドレス、ゼロscale、複数の添字項などは保守的に回収しません。

`nirvana_view_load/store`は従来のchecked little-endian guest memoryへ接続します。
ホストポインタへのキャストや、別の配列境界検査は導入しません。
field名、最大観測幅、重なりの情報は記述用であり、配置・範囲・型の保証ではありません。
未知のポインタからの書き込みも同じバイト列へ反映されます。
`ReadableC.object_views`と`stack_views`で、この記述を生成Cとともに取得できます。


LEAの結果を複数回使う場合など、添字式がレジスタの後ろに隠れるケースも扱います。
メモリアドレスとして使われるレジスタとコピー経路を辿り、純粋なアドレス形成を定義した位置で
`nirvana_view_index(...).address`と表します。その後で添字が変わっても、保存した数値アドレスを使います。
使用位置へ式を展開する変換ではありません。`IndexedView.address_sites`はこの形成箇所数で、
実際のLoad/Store箇所数とは分けています。形成だけが見つかる形の`byte_size`は0（未推定）です。

## 保存幅と局所変数の共有

`ValueWidths`は、到達可能な各読み書きの値を収められるunsignedの保存幅を求めます。
初期値を読む場合は未知のu64として扱い、すべての利用を収められる場合だけ
局所変数を`uint8_t`、`uint16_t`、`uint32_t`へ狭めます。未知や解析上限では`uint64_t`です。
これは元の型やsignednessの復元ではありません。引数は`uint64_t`のままです。

保存幅を狭めても、IRの中間演算はu64のままです。
Cの整数昇格により`uint16_t`同士の乗算がintになったり、`uint32_t`で途中のoverflowが起きたりしないよう、
必要なオペランドを演算前に`uint64_t`へ昇格させます。比較結果のintも同様です。
代入後のcastだけで演算を修正する方式ではありません。

`coalesce_locals`はCFG上の生存性と干渉を使い、同時に必要でない局所値へ同じ保存場所を割り当てます。
C出力側では同じ保存幅のクラス内だけで共有するため、狭い変数をU64変数との共有で広げません。
引数を共有対象にせず、メモリ操作や命令をこの割り当てによって削除しません。
割り当て解析の上限では個別の保存場所へ戻します。

ライブラリの`ReadableOptions::default()`は`stack_register: None`、`recover_objects: false`、
`coalesce_locals: false`です。CLIの`--emit readable-c`はRSP、入力オブジェクト、局所変数共有を有効にします。
共有前の局所値を個別に見るには`--no-coalesce-locals`を指定します。
`ReadableC.locals`には共有後の幅・名前・対応するIRレジスタ群、`local_value_count`には共有前の局所値数を記録します。

## Loadの評価順とループ

複数または入れ子のLoadは、`sequence`のLoad・代入・Ifからなる明示的な評価計画に下げます。
左右のLoadをIRと同じ順番で実行し、Selectは選んだ枝だけを実行します。
実行用の式からLoadを分離し、元アドレスは解析用metadataとしてだけ保持します。
Storeでは書き込み先を評価・検査してから右辺の計画を実行します。
gotoによる出力にも同じ順序処理を適用します。
計画の深さ・ノード数・一時レジスタなどの上限に達したら`ReadableError::Sequencing`を返し、
評価順の不明な生のC式へ戻すことはしません。

単純なループヘッダは、元のsetup代入をcomma operatorで条件の前へ並べて表せます。

```c
while ((v0 = nirvana_load(&m, address0, 1),
        v1 = nirvana_load(&m, address1, 1), v0 != v1)) {
    /* body */
}
```

setupは各ヘッダ訪問で順番に評価され、continue後と、最後に条件が偽になる訪問でも実行されます。
Loadをループ外へ持ち出しません。対象は先頭のレジスタ代入と直後の単純なbreak条件に限定し、
各右辺と条件に含むLoadは高々一つです。複数Loadや入れ子などの形は、明示的な評価計画を使う一般形のループに残します。

## 比較結果と証明の境界

native Cは返り値とfixture ABIの4状態ワードを元IRと比較します。
再生成readable Cは同じflat guest memoryで実行し、stackを含む全バイトの64-bit digestも照合します。
IR間では全メモリのバイト列を比較します。digestによる照合を全入力の同値性証明とは扱いません。
fault専用のnative検査ではabortを捕捉し、最初に失敗したアドレスと停止前の全メモリも比較します。

以下の入力比較数は構成×入力の組数であり、互いに異なる入力値の個数ではありません。
既存corpusの7構成は再配置が未対応のままです。追加した手書き8ソース・生成8ソースはO0/O2の全構成を要求し、
新しい失敗をskipして通す例外を置きません。生成8ソースは固定した4系列×2 seedであり、一般のバイナリ分布の標本ではありません。

| 検証・測定項目 | 結果 |
| --- | --- |
| 既存20ソース×O0/O2 | 33/40構成、33×63＝2,079入力比較 |
| 独立した手書き8ソース×O0/O2 | 16/16構成、16×69＝1,104入力比較 |
| 決定的に生成した8ソース×O0/O2 | 16/16構成、16×67＝1,072入力比較 |
| 3 corpusの合計 | 65/72構成、4,255入力比較、未対応7構成 |
| 前回55構成の数値一時変数（共有なし→あり） | 912→229。U8:67→42、U16:25→7、U32:21→8、U64:799→172 |
| 前回55構成の名前付きメモリ表現 | 定数オフセットfield 139箇所、index形16種類、定義時のアドレス形成14箇所 |

前回の保存場所・ビューの計測は`9c56366`時点です。今回の追加fixtureと式・goto・C表記の比較は
[出力の改善](output-polish.md)を参照してください。CLIは`input.field_8`・`read16(...)`・`element(...)`で表し、
上の長いhelper名の例はライブラリ既定の明示表記です。

`tests/recovery_verification.rs`は既存の`pure-u64-v1`モデルで、
選んだ幅推論119式対とindexed address 18式対を`EquivalentUnderModel`として確認します。
入力制約はExpr内のmaskで表し、幅0/1/7/8/15/16/31/32/63/64を含めます。
U64の自明な制約31件は証明件数から外します。乗算のstrictな検証範囲は`x*3`と`high(x*2^63)`です。
誤ったU8 mask・stride・offsetの3件はSATとなり、反例をIRでも再現します。

symbolic×symbolicの7-bit乗算は別のresource probeとして残しています。
既定2秒でUnknownとなった実行では、`checked_rewrite`が元の式を保持することを確認します。
Unknownを137件の証明に加算しません。CFG全体の解析、originの正しさ、メモリ効果、C出力全体の形式証明でもありません。
`--verify-reduction`の保証範囲も引き続き[メモリ付きIR還元](block-verification.md)までです。

数値一時変数の比較は、同じ機械語・同じfield/index復元・同じ保存幅解析に対し、
`coalesce_locals`だけを切り替えています。メモリビューのdescriptor、引数、C評価計画の私有temporaryは
この宣言数に含めません。`sum O0`は13→2、`struct-fields O0`は19→3でした。
元ソースとの一致率・実バイナリ全般の復元精度・処理速度の改善を示す値ではありません。

その後の[コピーを考慮した割り当て](copy-aware-allocation.md)では、コピーで同じ値を持つ局所値を保存場所の候補に加えます。
従来の割り当てを保持し、保存場所が減るか、同数でコピーが減る場合だけ採用します。

生成例16構成をUBSan付きでも再コンパイルし、既存63入力ずつの1,008比較で返り値・状態ワードが一致し、
UBSan診断はありませんでした。計測用のstack-only/separate/fullのC計165本もC11の警告をエラーにしてコンパイルしています。

## 再現

既存catalogのbuilderはオブジェクト・oracle・コンパイラ情報を`target/c-fixtures/`へ保存します。
追加の手書き・生成corpusはそれぞれのRustテストで別にコンパイルします。

```sh
python3 tools/build_fixtures.py
cargo test --test recovery_fixture --test generated_recovery
cargo test --test c_evaluation --test typed_locals --test indexed_views --test allocation
NIRVANA_RECOVERY_ARTIFACTS=target/memory-recovery/generated cargo test --test generated_recovery -- --nocapture
cargo run --quiet --example measure_memory_recovery -- target/memory-recovery
python3 tools/validate_recovery_artifacts.py
cargo run --quiet -- target/c-fixtures/cc-0/O0/sum.o --emit readable-c
cargo run --quiet -- target/c-fixtures/cc-0/O0/sum.o --emit readable-c --no-coalesce-locals
```

`NIRVANA_RECOVERY_ARTIFACTS`を指定すると、生成ソース、元オブジェクト、harness付きreadable Cを指定先へ残します。
通常は一時ディレクトリを終了時に削除します。
SMTを実行する場合は[既存のZ3準備手順](pure-expression-verification.md#再現)を使います。

```sh
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --test recovery_verification -- --include-ignored --nocapture --test-threads=1
NIRVANA_Z3=target/verification-venv/bin/z3 cargo test --all-targets -- --include-ignored --test-threads=1
```

比較表・前後のC・コンパイラ情報・全テストログは`target/memory-recovery/`に保存します。
既存catalogと追加corpusはいずれもGCC 13.3.0、C11・`-fno-lto`・O0/O2です。
UBSanは検証用の再コンパイルにのみ追加し、そのオブジェクトをデコンパイラへの入力には使いません。
