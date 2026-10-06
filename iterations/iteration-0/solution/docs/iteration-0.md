# Iteration 0 解説

演習の各手順の解説である．
見出しの番号は，演習の`docs/iteration-0.md`の手順に対応する．

## 0-1 準備

演習のパッケージは，`eval`と`run`が仮の実装になっている．
`eval`はどの式にも`0`を返し，`run`は空の文字列を返す．
テストファイルがないので，`lake test`は成功する．

## 0-2 構文と概念

課題1と2では，`#eval`で構文解析の結果を見る．

```text
Except.ok (Mini.Term.add (Mini.Term.num 1) (Mini.Term.mul (Mini.Term.num 2) (Mini.Term.num 3)))
Except.ok (Mini.Term.mul (Mini.Term.add (Mini.Term.num 1) (Mini.Term.num 2)) (Mini.Term.num 3))
Except.error "式が途中で終わっている"
```

`1 + 2 * 3`では`mul`が`add`の内側にあり，`*`が先に結合している．
`(1 + 2) * 3`では，かっこによって`add`が内側になる．
構文解析に失敗すると，`Except.error`に理由の文字列が入る．

課題3の式は`.add (.num 1) (.mul (.num 2) (.num 3))`である．
具体構文のかっこや演算子の強さは，抽象構文では木の形として表れる．

## 0-3 テストリスト

模範解答は`TESTLIST.md`にある．

- 単体テストでは，まず各演算子の具体例を1つずつ書いた．`-`については，引く数のほうが大きい場合を別の項目にした．
- 次に，演算子を組み合わせた式の具体例を書いた．
- 性質として，`+`と`*`の交換法則と結合法則，`t * 1`と`t`の等価性を挙げた．
- `-`については，交換法則と結合法則のどちらも成り立たない．結合法則が成り立たないことを，反例を示す定理`eval_sub_not_assoc`にした．
- 統合テストでは，文字列の入力で，結合の強さ(`1 + 2 * 3`)，かっこ，左結合(`10 - 2 - 3`)，負になる引き算，構文エラーを確かめた．
- 最後に，構文解析に成功したときの`run`の性質を`run_of_parse`とした．

## 0-4 設計書

どちらの設計書も，このIterationで最初の版を書く．

### 言語仕様書

- `## 構文`：`Term`の4つの構成子に，BNFの選択肢を1つずつ対応させた．構文とLeanの構成子の対応を表にし，具体構文での演算子の結合の規則を書き添えた．
- `## 意味`：`eval`の定義の4つの場合を，そのまま等式にした．`Nat`の引き算の性質は数式だけでは読み取りにくいので，記号$\dot{-}$を使い，その意味を文で説明した．
- `## 性質`：テストリストの性質の項目と，同じ名前と同じ順序にした．等価性の定義を最初に書き，各項目を「〜と〜は等価である」の形でそろえた．

### モジュール依存図

`import`の行から，次の依存を描いた．

- `Main`は`Mini.Run`だけを使う．
- `Mini.Run`は，構文解析の`Mini.Parser`と評価の`Mini.Eval`をつなぐ．
- `Mini.Eval`と`Mini.Parser`は，どちらも`Mini.Syntax`の`Term`を使う．

評価器と構文解析器が互いに依存しないことを，図の下に約束として書いた．
評価器は抽象構文だけを扱い，具体構文の事情を知らない．

## 0-5 テストファーストの実装

### 単体テスト

`MiniTest/Unit/EvalTest.lean`を作り，`MiniTest/Unit.lean`で`import MiniTest.Unit.EvalTest`とした．

#### 数`3`の値は`3`である

```lean
example : eval (.num 3) = 3 := by decide
```

仮の実装のままでは，`decide`が命題を偽と判定する．

```text
error: MiniTest/Unit/EvalTest.lean:13:34: Tactic `decide` proved that the proposition
  eval (Term.num 3) = 3
is false
```

`num`の場合だけを実装し，残りの場合は仮に`0`を返す．

```lean
def eval : Term → Nat
  | .num n => n
  | _ => 0
```

#### `1 + 2`の値は`3`である

```lean
example : eval (.add (.num 1) (.num 2)) = 3 := by decide
```

`add`の場合は仮の`0`を返すので，失敗する．

```text
error: MiniTest/Unit/EvalTest.lean:15:50: Tactic `decide` proved that the proposition
  eval ((Term.num 1).add (Term.num 2)) = 3
is false
```

`add`の場合を足す．部分式の値は`eval`を再帰的に呼んで求める．

```lean
def eval : Term → Nat
  | .num n => n
  | .add t₁ t₂ => eval t₁ + eval t₂
  | _ => 0
```

#### `5 - 2`の値は`3`である，`2 - 5`の値は`0`である

`sub`の場合を足す．
`Nat`の引き算は，引く数のほうが大きいとき`0`を返すので，`2 - 5`の項目は実装を足さずに成功する．

```lean
  | .sub t₁ t₂ => eval t₁ - eval t₂
```

#### `2 * 3`の値は`6`である

`mul`の場合を足すと，すべての構成子を扱うので，仮の`| _ => 0`は不要になる．
Leanは残りの場合がないことを確かめ，`| _ => 0`を残すとエラーにする．

```lean
def eval : Term → Nat
  | .num n => n
  | .add t₁ t₂ => eval t₁ + eval t₂
  | .sub t₁ t₂ => eval t₁ - eval t₂
  | .mul t₁ t₂ => eval t₁ * eval t₂
```

#### `1 + 2 * 3`を表す式の値は`7`である

再帰によって部分式を評価しているので，実装を足さずに成功する．

#### `eval_add_comm`ほかの等価性

まず主張を書き，証明を`sorry`にして失敗を確かめる．

```lean
theorem eval_add_comm (t₁ t₂ : Term) : eval (.add t₁ t₂) = eval (.add t₂ t₁) := by
  sorry
```

```text
error: MiniTest/Unit/EvalTest.lean:15:8: declaration uses `sorry`
```

`simp only [eval]`で`eval`を展開すると，ゴールは`eval t₁ + eval t₂ = eval t₂ + eval t₁`になる．
これは自然数の交換法則`Nat.add_comm`そのものである．

```lean
theorem eval_add_comm (t₁ t₂ : Term) : eval (.add t₁ t₂) = eval (.add t₂ t₁) := by
  simp only [eval]
  exact Nat.add_comm _ _
```

`_`は，Leanに推論させる引数である．
`eval_add_assoc`，`eval_mul_comm`，`eval_mul_assoc`，`eval_mul_one`も同じ形で，`Nat.add_assoc`，`Nat.mul_comm`，`Nat.mul_assoc`，`Nat.mul_one`を使う．

#### `eval_sub_not_assoc`

$(3 - 2) - 1 = 0$だが，$3 - (2 - 1) = 2$である．
この3つの数を反例として使う．

```lean
theorem eval_sub_not_assoc :
    ¬ ∀ t₁ t₂ t₃ : Term, eval (.sub (.sub t₁ t₂) t₃) = eval (.sub t₁ (.sub t₂ t₃)) := by
  intro h
  have h' := h (.num 3) (.num 2) (.num 1)
  simp [eval] at h'
```

`eval`を展開すると，仮定`h'`は`3 - 2 - 1 = 3 - (2 - 1)`になる．
`simp [eval] at h'`は両辺を計算し，この等式が偽であることから証明を終える．

### 統合テスト

`MiniTest/Integration/RunTest.lean`を作り，`MiniTest/Integration.lean`に登録した．

#### `run "1 + 2 * 3"`は`"7"`である

```lean
example : run "1 + 2 * 3" = "7" := by decide +kernel
```

仮の実装の`run`は空の文字列を返すので，失敗する．

```text
error: MiniTest/Integration/RunTest.lean:16:38: Tactic `decide` proved that the proposition
  run "1 + 2 * 3" = "7"
is false
```

`parse`の結果で場合を分け，成功したときは`eval`の値を文字列にする．

```lean
def run (s : String) : String :=
  match parse s with
  | .ok t => toString (eval t)
  | .error e => s!"構文エラー：{e}"
```

残りの具体例(かっこ，左結合，負になる引き算，構文エラー)は，この実装のまま成功する．
結合の強さと向きは構文解析器が決めるので，統合テストで確かめている．

#### `run_of_parse`

```lean
theorem run_of_parse {s : String} {t : Term} (h : parse s = .ok t) :
    run s = toString (eval t) := by
  simp [run, h]
```

`simp`は`run`を展開し，前提`h`で`parse s`を`.ok t`に書き換えてから，`match`を計算する．

### 動作の確認

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

## 0-6 振り返り

1. 見落としやすいのは，引く数のほうが大きい引き算(`2 - 5`)と，同じ強さの演算子の結合の向き(`10 - 2 - 3`)である．どちらも要件に書かれた規則で，具体例を1つ書くと確かめられる．
2. 単体テストは`eval`が各演算子を正しく計算すること，統合テストは構文解析と評価をつないだ結果を確かめた．`run`の具体例だけでは，`eval`の失敗と構文解析器の失敗を区別できない．また，`eval_add_comm`のような`eval`の性質は，`run`の具体例では書けない．
3. 具体例は有限個の式しか確かめないが，式は無限にある．定理は，すべての式について成り立つことを保証する．
4. 模範解答の設計書は，`mise run check-design`で`一致`になる．照合では，依存図の矢印とimport文，言語仕様書の性質の名前と`MiniTest/`の定理の名前を比べている．

## 0-7 発展課題

次のように調べられる．

- `t + 0`と`t`，`0 + t`と`t`，`t * 0`と`0`，`t - 0`と`t`，`0 - t`と`0`，`t - t`と`0`は，どれも等価である．`Nat.add_zero`，`Nat.zero_add`，`Nat.mul_zero`，`Nat.sub_zero`，`Nat.zero_sub`，`Nat.sub_self`で証明できる．
- 分配法則`t₁ * (t₂ + t₃)`と`t₁ * t₂ + t₁ * t₃`は等価である(`Nat.mul_add`)．
- 引き算についても，`t₁ * (t₂ - t₃)`と`t₁ * t₂ - t₁ * t₃`は等価である(`Nat.mul_sub`)．引く数のほうが大きいとき，両辺とも`0`になるからである．
