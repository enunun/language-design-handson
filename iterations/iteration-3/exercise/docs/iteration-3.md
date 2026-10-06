# Iteration 3 真偽値と条件分岐

このIterationでは，Miniに真偽値`true`と`false`，条件式`if c then t else e`，`0`かどうかを調べる`iszero t`を足す．
評価の結果は自然数か真偽値になり，`1 + true`のように演算できない式は評価が行き詰まる．

## 3-1 準備

このパッケージは，Iteration 2の解答と同じ状態から始まる．

``` sh
cd iterations/iteration-3/exercise
lake build
lake test
```

Iteration 2までのテストがすべて通ることを確かめる．
`handout/Parser.lean`は，このIterationの構文に対応した構文解析器である．
3-5で使う．

## 3-2 構文と概念

次の2つのノートを読む．

- [場合の多い定義と証明](../../../docs/lean/iteration-3.md)
- [値と行き詰まり](../../../docs/semantics/iteration-3.md)

読み終えたら，`Scratch.lean`で次の課題を試す．

1. ノートの`addOpt`を書き写し，`addOpt none (some 1)`の結果を予想してから`#eval`で確かめる．
2. `addOpt_comm`を書き写し，`rcases`の後に分かれた4つの場合をInfoviewで確かめる．
3. `(5 == 5) = true`と`(5 : Nat) ≠ 6`を証明する．

## 3-3 テストリスト

### 要件

- 真偽値`true`と`false`，条件式`if c then t else e`，自然数が`0`かを調べる`iszero t`を足す．
- 評価結果は自然数か真偽値になる．
- `1 + true`のように演算できない式を評価すると，評価が行き詰まったことを表示する．

### 使用例

```text
$ lake exe mini eval "if iszero (2 - 2) then 10 else 20"
10
$ lake exe mini eval "1 + true"
実行時エラー：評価が行き詰まった(1 + true)
```

### 作るもの

| モジュール | 定義 | 内容 |
| --- | --- | --- |
| `Mini.Syntax` | `Term`の構成子`tru`，`fls`，`ite (c t e : Term)`，`iszero (t : Term)` | 新しい構文 |
| | `inductive Value`(構成子`num (n : Nat)`，`bool (b : Bool)`) | 評価の結果の値 |
| | `def Value.toTerm : Value → Term` | 値を，その値を表す式にする |
| `Mini.BigStep` | `Eval : Term → Value → Prop` | 結果を`Nat`から`Value`に変える |
| `Mini.SmallStep` | `Step`の新しい規則，`def Normal`，`def Stuck` | 正規形と行き詰まった式 |
| `Mini.Eval` | `eval : Term → Option Value` | 行き詰まると`none`を返す |
| `Mini.Pretty` | `def Value.pretty : Value → String` | 値の表示 |
| `Mini.Run` | `run` | 行き詰まったときは，行き詰まった式を表示する |

### 課題

確かめるべきことを`TESTLIST.md`に書き出す．

- 新しい構文の評価と簡約の具体例を考える．`if`で選ばれない枝は評価されるか．
- 行き詰まる式の具体例を考える．行き詰まりが式の途中で起きる例も考える．
- 既存のテストのうち，期待値や主張が変わるものを探し，「〜を〜に変える」という項目にする．Iteration 0の等価性の定理は，すべて成り立ち続けるか．
- `if`の`then`の枝を，条件より先に簡約してもよいとしたら，小ステップ意味論のどの性質が崩れるかを考える．

## 3-4 設計書

- `design/spec.md`
  - `## 構文`：BNFと対応表に，新しい構文を足す．
  - 値の集合を定める節を足す．
  - `## 意味`：大ステップ意味論の規則を，値`v`を使う形に直し，新しい構文の規則を足す．小ステップ意味論に，`if`と`iszero`の規則を足す．行き詰まった式の定義を書く．
  - `## 性質`：テストリストの性質を足し，主張の変わった性質を直す．
- `design/modules.md`：依存の矢印は変わるか．各モジュールの説明を，新しい定義に合わせて直す．

## 3-5 テストファーストの実装

### 新しい構文と構文解析器

1. `Mini/Syntax.lean`の`Term`に，構成子`tru`，`fls`，`ite`，`iszero`を足す．
2. 配布された構文解析器で`Mini/Parser.lean`を置き換える．

   ``` sh
   cp handout/Parser.lean Mini/Parser.lean
   ```

3. `lake build`を実行し，`Term`を場合分けしている関数(`eval`，`step`，`Term.pretty`など)で，新しい構成子の場合がないというエラーが出ることを確かめる．

### 値と既存のテスト

1. `Value`と`Value.toTerm`を足す．
2. 既存のテストの期待値を，テストリストのとおりに変える．このとき`lake test`は，`eval`の型が合わないなどの理由で失敗する．
3. `Eval`，`eval`，`step`，`Term.pretty`を新しい型と構文に合わせて直し，既存のテストを通す．

次のヒントを参考にする．

- `eval`の`add`の場合は，`match eval t₁, eval t₂ with`で，両方が`some (.num _)`の場合だけ値を返す．
- `Eval`の`iszero`の規則の結論は`.bool (n == 0)`とすると，`eval`と同じ形になる．
- 交換法則の証明では，`rcases eval t₁ with _ | _ | _`で値の形を場合分けする．
- `step`の`if`の場合は，`match c with`で`tru`，`fls`，それ以外に分ける．

### 新しい構文のテスト

テストリストの順に，具体例と性質のテストを足し，`Eval`，`Step`，`eval`，`step`に規則と場合を足す．

次のヒントを参考にする．

- 小ステップ意味論の`iszero`の計算の規則は，`iszero (num 0)`と`iszero (num (n + 1))`の2つに分けると，結果を`tru`と`fls`の式で直接書ける．
- 大ステップ意味論との一致では，$t \longrightarrow^{*} v$の`v`は値`Value`なので，`v.toTerm`と書く．値を表す式がその値に評価されることを，補題として先に示す．
- `then`の枝を先に簡約する意味論は，テストファイルの中で，`Step`に規則を1つ足した新しい帰納的述語として定義する．決定性が成り立たないことは，2通りに簡約できる式を反例にして示す．

### 実行時エラーの表示

統合テストを足してから`run`を直す．

次のヒントを参考にする．

- `eval`が`none`を返したら，`step`を繰り返して行き詰まった式を求め，`Term.pretty`で表示する．Iteration 2の簡約列を作る関数を使える．

最後に，使用例のとおりに表示されることを確かめる．

## 3-6 振り返り

1. 自分の`TESTLIST.md`を，`solution/TESTLIST.md`と比べる．既存のテストの変更を見落としていなかったか．
2. `eval_mul_one`は，真偽値を足したことで主張を変える必要があった．Iteration 0のほかの等価性の定理は，なぜ主張を変えずに済んだか．
3. 行き詰まった式を表示するのに，大ステップ意味論ではなく小ステップ意味論の`step`を使った．それはなぜか．
4. 設計書と実装を見比べ，`mise run check-design`で`一致`になるまで設計書を直す．

## 3-7 発展課題

真偽値の演算`t₁ && t₂`(両方が`true`なら`true`)を，構文解析器を変えずに，`if`を使った式の略記として定義する．
略記を展開する関数`Term.and : Term → Term → Term`を作る．
そのうえで，`t₁ && t₂`の値が，両辺の値の論理積になることを証明する．

これも，テストリスト，設計書，実装の順に進める．
