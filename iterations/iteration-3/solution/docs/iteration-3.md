# Iteration 3 解説

演習の各手順の解説である．
見出しの番号は，演習の`docs/iteration-3.md`の手順に対応する．

## 3-1 準備

演習のパッケージはIteration 2の解答と同じなので，テストはすべて通る．

## 3-2 構文と概念

課題1の結果は`none`である．
`addOpt`は，両方が`some`のときだけ値を返す．
課題3はどちらも`decide`で証明できる．

## 3-3 テストリスト

模範解答は`TESTLIST.md`にある．

- 新しい構文の具体例は，`eval`，`Eval`，`Step`，`step`のそれぞれについて書いた．`if`で選ばれない枝を評価しないことは，その枝に行き詰まる式を置いた例で確かめた．
- 行き詰まる式として，`1 + true`，条件が数の`if`，途中で行き詰まる`(1 + 2) * iszero 0`を挙げた．
- 既存のテストの変更として，`eval`の具体例の期待値，健全性と完全性などの主張，`eval_mul_one`の主張を挙げた．
- `then`の枝を先に簡約する意味論が決定的でないことを，`stepEager_not_deterministic`とした．

## 3-4 設計書

### 言語仕様書

- `## 構文`：BNFに真偽値，`if`，`iszero`を足した．算術の3つの演算子は1行にまとめた．
- `## 値`を新しく立て，値の集合と，値を式と同一視することを書いた．
- `## 意味`：大ステップ意味論の結論を値$v$にした．算術の規則の前提は「部分式の値が数」になるので，規則が当てはまらない式には値がないことを書き添えた．
- 小ステップ意味論に，`if`の3つの規則と`iszero`の3つの規則を足した．
- 正規形と行き詰まった式の定義を，`### 正規形と行き詰まった式`にまとめた．この節は規則を持たないので，見出しにLeanの名前を付けていない．
- `## 性質`：等価性の説明に「値がないことも含めて」と書き足した．`eval_mul_one`の主張を条件付きに変え，`eval_mul_one_not_equiv`，`value_normal`，`stepEager_not_deterministic`を足した．`run_of_parse`は`run_of_eval`に変えた．

### モジュール依存図

依存の矢印は変わらない．
`Mini.Syntax`に`Value`が加わったこと，`Mini.Run`が行き詰まった式を表示するために`step`を使うことを，説明に書き足した．

## 3-5 テストファーストの実装

### 新しい構文と構文解析器

`Term`に構成子を足して構文解析器を置き換えると，`Term`を場合分けしている関数がすべてエラーになる．

```text
error: Mini/Pretty.lean:19:2: Missing cases:
_, tru
_, fls
_, (ite _ _ _)
_, (iszero _)
```

```text
error: Mini/Eval.lean:14:2: Missing cases:
Term.tru
Term.fls
(Term.ite _ _ _)
(Term.iszero _)
```

Leanは，場合分けの漏れをすべて報告する．
構文を足したときに直すべき場所は，このエラーの一覧でわかる．

### 値と既存のテスト

既存の具体例の期待値を変える前は，`eval`の型が`Option Value`になったことで，期待値の数が型に合わなくなる．

```text
error: MiniTest/Unit/EvalTest.lean:15:26: failed to synthesize instance of type class
  OfNat (Option Value) 3
```

期待値を`some (.num 3)`に変え，`eval`を`match`で書き直した．

```lean
  | .add t₁ t₂ =>
    match eval t₁, eval t₂ with
    | some (.num n₁), some (.num n₂) => some (.num (n₁ + n₂))
    | _, _ => none
```

交換法則と結合法則は，部分式の値の形で場合分けして証明し直した．

```lean
theorem eval_add_comm (t₁ t₂ : Term) : eval (.add t₁ t₂) = eval (.add t₂ t₁) := by
  simp only [eval]
  rcases eval t₁ with _ | _ | _ <;> rcases eval t₂ with _ | _ | _ <;> simp [Nat.add_comm]
```

`eval_mul_one`は，主張のままでは証明できない．
$\mathsf{true} * 1$には値がないが，$\mathsf{true}$の値は$\mathrm{true}$だからである．
主張を「$t$の値が数なら」に変え，成り立たないことを`eval_mul_one_not_equiv`で示した．

```lean
theorem eval_mul_one_not_equiv : ¬ ∀ t : Term, eval (.mul t (.num 1)) = eval t := by
  intro h
  have h' := h .tru
  simp [eval] at h'
```

### 新しい構文のテスト

#### 大ステップ意味論

`if`の規則は，条件の値が`true`か`false`かで2つに分けた．
`iszero`の規則の結論は`.bool (n == 0)`である．

```lean
  | iteTrue {c t e : Term} {v : Value} : Eval c (.bool true) → Eval t v → Eval (.ite c t e) v
  | iteFalse {c t e : Term} {v : Value} : Eval c (.bool false) → Eval e v → Eval (.ite c t e) v
  | iszero {t : Term} {n : Nat} : Eval t (.num n) → Eval (.iszero t) (.bool (n == 0))
```

`1 + true`に値がないことは，導出を分解すると，`true`の値が数になる導出が必要になることから示す．

```lean
example : ¬ ∃ v, Term.add (.num 1) .tru ⇓ v := by
  intro ⟨v, h⟩
  cases h with
  | add _ h₂ => cases h₂
```

#### 健全性と完全性

`eval_sound`は，`unfold eval at h`と`split at h`で`match`の場合ごとに分け，値を返す場合に規則を当てはめた．
`none`を返す場合は，`h : none = some v`が矛盾なので`contradiction`で閉じる．

```lean
  | ite c t e ihc iht ihe =>
    unfold eval at h
    split at h
    · next hc => exact Eval.iteTrue (ihc hc) (iht h)
    · next hc => exact Eval.iteFalse (ihc hc) (ihe h)
    · contradiction
```

`next hc =>`は，`split`が加えた仮定(ここでは`eval c = some (.bool true)`)に名前を付ける．

#### 小ステップ意味論

`if`の3つの規則と`iszero`の3つの規則を足し，決定性の証明に場合を足した．
`iszero`の計算の規則は，`num 0`と`num (n + 1)`に分けた．

`then`の枝を先に簡約する意味論は，テストファイルの中で定義した．

```lean
inductive StepEager : Term → Term → Prop where
  | base {t t' : Term} : t ⟶ t' → StepEager t t'
  | iteThen {c t t' e : Term} : StepEager t t' → StepEager (.ite c t e) (.ite c t' e)
```

`stepEager_not_deterministic`は，主張を書いて`sorry`で失敗を確かめた．

```text
error: MiniTest/Unit/SmallStepTest.lean:160:8: declaration uses `sorry`
```

`if true then 1 + 2 else 0`の2通りの簡約を反例にした．
2つの結果`1 + 2`と`if true then 3 else 0`は構成子が異なるので，等式を`cases`で分解すると矛盾になる．

```lean
theorem stepEager_not_deterministic :
    ¬ ∀ t t₁ t₂, StepEager t t₁ → StepEager t t₂ → t₁ = t₂ := by
  intro h
  have := h (.ite .tru (.add (.num 1) (.num 2)) (.num 0)) (.add (.num 1) (.num 2))
    (.ite .tru (.num 3) (.num 0)) (.base .iteTrue) (.iteThen (.base .add))
  cases this
```

#### 2つの意味論の一致

主張を$t \Downarrow v \iff t \longrightarrow^{*} v.\mathit{toTerm}$に変えた．
左向きの証明の最後で使う「値を表す式はその値に評価される」を，補題`value_bigstep`として足した．
右向きの`iszero`の場合は，`n`が`0`かどうかで使う規則が変わるので，`@iszero _ n _ ih`で`n`に名前を付けて場合分けした．

### 実行時エラーの表示

`Mini.Run`に，`step`を繰り返して行き詰まった式を求める`normalize`を作り，`run`で使った．

```lean
def run (s : String) : String :=
  match parse s with
  | .ok t =>
    match eval t with
    | some v => v.pretty
    | none => s!"実行時エラー：評価が行き詰まった({(normalize t).pretty})"
  | .error e => s!"構文エラー：{e}"
```

```text
$ lake exe mini eval "if iszero (2 - 2) then 10 else 20"
10
$ lake exe mini eval "1 + true"
実行時エラー：評価が行き詰まった(1 + true)
```

## 3-6 振り返り

1. 既存のテストで変わるのは，`eval`の結果の型に関わるものと，真偽値で反例ができる等価性である．
2. 交換法則と結合法則では，両辺の値がない場合も一致する．どちらかの部分式の値が数でなければ，両辺とも`none`になるからである．$t * 1$と$t$では，$t$の値が真偽値のとき，左辺だけが`none`になる．
3. 大ステップ意味論には，行き詰まった式に値がないことしか表れない．行き詰まった式そのものは，評価の途中経過を表す小ステップ意味論でしか求められない．
4. 模範解答の設計書は，`mise run check-design`で`一致`になる．`Eval`と`Step`の新しい規則名も照合される．

## 3-7 発展課題

`t₁ && t₂`は，`if t₁ then t₂ else false`の略記として定義できる．

```lean
def Term.and (t₁ t₂ : Term) : Term := .ite t₁ t₂ .fls

theorem eval_and {t₁ t₂ : Term} {a b : Bool} (h₁ : eval t₁ = some (.bool a)) (h₂ : eval t₂ = some (.bool b)) :
    eval (Term.and t₁ t₂) = some (.bool (a && b)) := by
  cases a <;> simp [Term.and, eval, h₁, h₂]
```

この略記では，`t₁`が`false`なら`t₂`を評価しない．
`false && (1 + true)`の値は`false`になり，行き詰まらない．
