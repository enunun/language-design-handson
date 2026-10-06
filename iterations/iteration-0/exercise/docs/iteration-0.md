# Iteration 0 自然数の四則と評価器

このIterationでは，自然数と`+`，`-`，`*`からなる式を評価する処理系を作る．
評価器`eval`と，構文解析から評価までをつなぐ`run`を実装し，その振る舞いと性質をLeanの定理として証明する．

## 0-1 準備

コンテナの端末で，このパッケージのディレクトリに移る．

``` sh
cd iterations/iteration-0/exercise
```

パッケージをビルドし，テストを実行する．
テストファイルはまだないので，`lake test`は何も検査せずに成功する．

```text
$ lake build
✔ [14/14] Built mini:exe (372ms)
Build completed successfully (14 jobs).
$ lake test
✔ [2/4] Built MiniTest.Unit (586ms)
✔ [3/4] Built MiniTest.Integration (562ms)
✔ [4/4] Built MiniTest (345ms)
```

コマンド`mini`を実行する．

``` sh
lake exe mini eval "1 + 2"
```

`eval`と`run`は仮の実装なので，空の行だけが表示される．

最初に入っているファイルは次のとおりである．

| ファイル | 内容 |
| --- | --- |
| `Mini/Syntax.lean` | 式の抽象構文`Term`(完成している) |
| `Mini/Parser.lean` | 構文解析器`parse`(配布物．完成している) |
| `Mini/Eval.lean` | 評価器`eval`(仮の実装) |
| `Mini/Run.lean` | 構文解析と評価をつなぐ`run`(仮の実装) |
| `Main.lean` | コマンド`mini eval <式>`(完成している) |
| `MiniTest.lean`，`MiniTest/Unit.lean`，`MiniTest/Integration.lean` | テストの入口 |
| `design/spec.md`，`design/modules.md` | 設計書(見出しだけ) |
| `TESTLIST.md` | テストリスト(見出しだけ) |

## 0-2 構文と概念

次の2つのノートを読む．

- [Leanの基礎](../../../docs/lean/iteration-0.md)
- [構文と意味](../../../docs/semantics/iteration-0.md)

読み終えたら，パッケージのディレクトリに`Scratch.lean`を作り，次の課題を試す．
このファイルは試すためだけのもので，Gitには登録されない．

``` lean
import Mini

open Mini

#eval parse "1 + 2 * 3"
```

1. `#eval parse "1 + 2 * 3"`の結果を見て，`*`が`+`より強く結合していることを確かめる．`"(1 + 2) * 3"`とも比べる．
2. `#eval parse "1 +"`を実行し，構文解析に失敗したときの結果の形を確かめる．
3. `Mini/Syntax.lean`の`Term`を読み，`1 + 2 * 3`を表す式を構成子で書いて`#eval`する．
4. ノートの`Shape`と`area`を`Scratch.lean`に書き写し，`area`の具体例を`decide`で証明する．

端末で結果を見るときは，`lake env lean Scratch.lean`を実行する．

## 0-3 テストリスト

### 要件

- 自然数，`+`，`-`，`*`，かっこからなる式を評価し，結果の自然数を表示する．
- `-`は自然数の引き算で，結果が負になるときは`0`とする．
- `*`は`+`と`-`より強く結合し，同じ強さの演算子は左から結合する．

### 使用例

```text
$ lake exe mini eval "1 + 2 * 3"
7
$ lake exe mini eval "(1 + 2) * 3"
9
$ lake exe mini eval "2 - 5"
0
$ lake exe mini eval "1 +"
構文エラー：式が途中で終わっている
```

### 作るもの

| モジュール | 定義 | 内容 |
| --- | --- | --- |
| `Mini.Eval` | `def eval : Term → Nat` | 式の値 |
| `Mini.Run` | `def run : String → String` | 文字列を構文解析して評価し，表示する文字列を返す．構文解析に失敗したときは`構文エラー：`に続けて理由を返す |

### 課題

要件と使用例から，確かめるべきことを`TESTLIST.md`に書き出す．
書き方は[定理によるテスト駆動開発](../../../docs/tdd.md)を参照する．

- `eval`の単体テストと，`run`の統合テストに分ける．それぞれ，どのファイルに置くかも書く．
- 各演算子の具体例を考える．引き算の結果が負になる場合も入れる．
- Miniの式の性質を考える．どの演算子について，交換法則や結合法則が成り立つか．成り立たないものには反例を示す定理を考える．
- 性質のテストには定理の名前を付ける．
- 統合テストでは，演算子の結合の強さと結合の向き，構文エラーを，文字列の入力で確かめる．

## 0-4 設計書

まず[設計書の書き方](../../../docs/design.md)を読む．
このIterationでは，2つの設計書の最初の版を書く．

- `design/spec.md`
  - `## 構文`：`Term`の4つの構成子に対応するBNFを書く．
  - `## 意味`：構成子ごとに，`eval`の等式を書く．引き算の扱いも書く．
  - `## 性質`：テストリストに書いた性質を，定理の名前とともに並べる．
- `design/modules.md`
  - `Mini/`の4つのモジュールと`Main`の依存を描く．各ファイルの`import`の行を見て，矢印を決める．

書いたら，リポジトリのルートで`mise run lint`を実行し，数式と図の構文を確かめる．

## 0-5 テストファーストの実装

テストリストの項目を1つずつ，Red → Green → Refactorで進める．

### 単体テスト

1. `MiniTest/Unit/EvalTest.lean`を作り，`MiniTest/Unit.lean`に`import MiniTest.Unit.EvalTest`を足す．
2. テストファイルの先頭で`import Mini.Eval`と`open Mini`を書く．
3. 最初の具体例を書き，`lake test`で失敗することを確かめる．
4. `Mini/Eval.lean`の`eval`を実装し，`lake test`で成功することを確かめる．

次のヒントを参考にする．

- 具体例は`example : eval (.num 3) = 3 := by decide`の形で書く．
- `eval`は，`Term`の構成子ごとにパターンマッチで定義する．部分式の値は`eval`を再帰的に呼んで求める．
- 交換法則や結合法則は，`simp only [eval]`で`eval`を展開すると，自然数の等式になる．残りは`Nat`の定理で証明する．定理の名前は`#check`や`exact?`で探す．
- 反例の定理は，ノートの`not_all_square`と同じ形で証明する．どの数を選ぶと等式が偽になるかを先に計算しておく．

### 統合テスト

1. `MiniTest/Integration/RunTest.lean`を作り，`MiniTest/Integration.lean`に登録する．
2. 具体例を書いて失敗を確かめてから，`Mini/Run.lean`の`run`を実装する．

次のヒントを参考にする．

- 文字列を入力にした具体例は`example : run "1 + 2 * 3" = "7" := by decide +kernel`の形で書く．
- `run`では，`parse s`の結果を`match`で場合分けする．
- 構文解析に成功したときの`run`の性質を，定理として書ける．前提`parse s = .ok t`を受け取り，`simp`に`run`の定義と前提を渡して証明する．

### 動作の確認

テストがすべて通ったら，使用例のとおりに動くことを確かめる．

``` sh
lake exe mini eval "1 + 2 * 3"
```

## 0-6 振り返り

1. 自分の`TESTLIST.md`を，`solution/TESTLIST.md`と比べる．足りない項目や，自分だけが書いた項目はあったか．
2. 単体テストと統合テストは，それぞれ何を確かめたか．`run`の具体例だけで，`eval`の単体テストを置き換えられるか．
3. `eval_add_comm`のような定理は，具体例をいくつ書いても置き換えられない．それはなぜか．
4. 設計書と実装を見比べ，食い違っていれば設計書を直す．パッケージのディレクトリで`mise run check-design`を実行し，`一致`と表示されることを確かめる．

## 0-7 発展課題

最適化器が式を書き換えるとき，使ってよい書き換えは，元の式と等価なものだけである．
`0`と`1`が関わる書き換えについて，使ってよいものと使ってはいけないものを調べる．

- `t + 0`と`t`，`0 + t`と`t`，`t * 0`と`0`，`t - 0`と`t`，`0 - t`と`0`，`t - t`と`0`は等価か．
- `t₁ * (t₂ + t₃)`と`t₁ * t₂ + t₁ * t₃`(分配法則)は等価か．`+`の代わりに`-`ではどうか．

これも，テストリスト，設計書(言語仕様書の`## 性質`)，実装(定理の証明)の順に進める．
