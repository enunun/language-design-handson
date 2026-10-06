# Iteration 6 解説

演習の各手順の解説である．
見出しの番号は，演習の`docs/iteration-6.md`の手順に対応する．

## 6-1 準備

演習のパッケージはIteration 5の解答と同じなので，テストはすべて通る．

## 6-2 構文と概念

課題2の簡約列は，完成した`mini steps`で確かめられる．

```text
$ lake exe mini steps "(fun (f : Nat -> Nat) => f (f 1)) (fun (x : Nat) => x + 1)"
(fun (f : Nat → Nat) => f (f 1)) (fun (x : Nat) => x + 1)
⟶ (fun (x : Nat) => x + 1) ((fun (x : Nat) => x + 1) 1)
⟶ (fun (x : Nat) => x + 1) (1 + 1)
⟶ (fun (x : Nat) => x + 1) 2
⟶ 2 + 1
⟶ 3
```

2ステップ目では，外側の適用の関数が値なので，引数$(\mathsf{fun}\ (x : \mathsf{Nat}) \Rightarrow x + 1)\ 1$を先に簡約する．
課題3の型は$\mathsf{Nat}$である．
左の関数は$(\mathsf{Nat} \rightarrow \mathsf{Nat}) \rightarrow \mathsf{Nat}$型で，右の関数は$\mathsf{Nat} \rightarrow \mathsf{Nat}$型である．

## 6-3 テストリスト

模範解答は`TESTLIST.md`にある．

- 関数そのものの値は，その関数自身である．大ステップ意味論の規則`lam`で確かめた．
- 関数適用の具体例は，評価，簡約，型付け，型検査器，表示，`run`のそれぞれで挙げた．高階関数の例は`run`で確かめた．
- 型エラーは，引数の型が合わない場合と，関数でない式を適用する場合を挙げた．
- 既存の定理では，決定性，2つの意味論の一致，`step`の健全性と完全性，型検査器の健全性と完全性，弱化，置換補題，進行，保存に場合を足した．

## 6-4 設計書

### 言語仕様書

- `## 構文`に関数と関数適用を足した．関数も変数を束縛することを書いた．
- `## 値`に関数を足し，値を表す式の規則`lam`を足した．
- `### 置換`に関数の場合を足した．`let`の本体と同じく，束縛する名前が`x`なら置換しない．
- 大ステップ意味論に`lam`と`app`の規則を，小ステップ意味論に`app1`，`app2`，`beta`の規則を足した．
- `## 型`に関数型と，`lam`と`app`の型付け規則を足した．

### モジュール依存図

依存の矢印は変わらない．
関数の値を，その関数を表す式として表示することを，`Mini.Pretty`の説明に書き足した．

## 6-5 テストファーストの実装

### 構文と構文解析器

構成子を足して構文解析器を置き換えると，場合の足りない定理はすべてエラーになる．

```text
error: MiniTest/Unit/BigStepTest.lean:63:2: Alternative `lam` has not been provided
error: MiniTest/Unit/BigStepTest.lean:63:2: Alternative `app` has not been provided
error: MiniTest/Unit/SmallStepTest.lean:62:4: Alternative `lam` has not been provided
```

このエラーの一覧が，場合を足すべき定理の一覧になる．

### 意味論と評価器

小ステップ意味論の関数適用の規則は，`let`と同じく値を表す式を前提にとる．

```lean
  | app1 {t₁ t₁' t₂ : Term} : Step t₁ t₁' → Step (.app t₁ t₂) (.app t₁' t₂)
  | app2 {v₁ t₂ t₂' : Term} : IsValue v₁ → Step t₂ t₂' → Step (.app v₁ t₂) (.app v₁ t₂')
  | beta {x : String} {A : Ty} {b v : Term} : IsValue v → Step (.app (.lam x A b) v) (subst x v b)
```

`step`は，関数と引数がそれぞれ値かどうかで場合を分けた．

```lean
  | .app t₁ t₂ =>
    match t₁.toValue?, t₂.toValue? with
    | some (.lam x _ b), some _ => some (subst x t₂ b)
    | some _, some _ => none
    | some _, none => (step t₂).map (.app t₁)
    | none, _ => (step t₁).map (.app · t₂)
```

`step_sound`の関数適用の場合は，`split at h`の1つ目の場合に，名前のない仮定が8つある．
`next _ _ x A b _ hv₁ hv₂`で，最後の6つに名前を付けた．

```lean
    · next _ _ x A b _ hv₁ hv₂ =>
      cases h
      rw [toValue?_some hv₁]
      exact .beta (toValue?_isValue hv₂)
```

### 型付け

関数型の標準形補題を足した．

```lean
theorem canonical_arrow {Γ : Ctx} {v : Value} {A B : Ty} (h : HasType Γ v.toTerm (.arrow A B)) :
    ∃ x b, v = .lam x A b := by
  cases v with
  | num n => cases h
  | bool b => cases b <;> cases h
  | lam x A' t => cases h; exact ⟨x, t, rfl⟩
```

保存のβ簡約の場合は，関数の型付けを`cases`で分解して本体の型付け`hb`を取り出し，置換補題に渡した．

```lean
    | beta _ =>
      cases h₁ with
      | lam hb => exact subst_typing hb h₂
```

### 表示と`run`

型の表示は，`→`の強さを`0`とし，左の型を1つ強い位置に置いて右結合にした．
関数適用は，関数を強さ`3`の位置に，引数を強さ`4`の位置に置いて左結合にした．

```text
$ lake exe mini eval "let double = fun (x : Nat) => x + x in double 21"
42
$ lake exe mini check "fun (x : Nat) => iszero x"
Nat → Bool
$ lake exe mini steps "(fun (x : Nat) => x + 1) 2"
(fun (x : Nat) => x + 1) 2
⟶ 2 + 1
⟶ 3
```

## 6-6 振り返り

1. 既存の定理に場合を足す作業が多い．構文を足したときに直すべき場所は，Leanのエラーの一覧からわかる．
2. 置換補題は，置換する式が閉じた値であれば，置換される式の形によらない．`let`の本体も関数の本体も，束縛された変数を1つ持つ式なので，同じ補題が使える．
3. 関数適用の型付け規則`app`は，関数の側に関数型$A \rightarrow B$を求める．`1`の型は`Nat`なので，`1 2`はこの規則に当てはまらない．
4. 模範解答の設計書は，`mise run check-design`で`一致`になる．

## 6-7 発展課題

名前呼びのβ簡約を足した簡約は，次のように定義できる．

```lean
inductive StepByName : Term → Term → Prop where
  | base {t t' : Term} : t ⟶ t' → StepByName t t'
  | betaN {x : String} {A : Ty} {b u : Term} : StepByName (.app (.lam x A b) u) (subst x u b)
```

$(\mathsf{fun}\ (x : \mathsf{Nat}) \Rightarrow 1)\ (1 + \mathsf{true})$は，名前呼びでは1ステップで$1$になる．
値呼びでは，引数$1 + \mathsf{true}$が行き詰まるので，式全体も行き詰まる．

```lean
example : StepByName (.app (.lam "x" .nat (.num 1)) (.add (.num 1) .tru)) (.num 1) := .betaN

example : Stuck (.app (.lam "x" .nat (.num 1)) (.add (.num 1) .tru)) := by
  constructor
  · intro t h
    cases h with
    | app1 h => cases h
    | app2 _ h =>
      cases h with
      | addL h => cases h
      | addR h => cases h
    | beta hv => cases hv
  · intro v h
    cases v with
    | num n => cases h
    | bool b => cases b <;> cases h
    | lam x A t => cases h
```

この式には型が付かない．
引数$1 + \mathsf{true}$に型が付かないからである．
型の付く式では，このIterationの言語の2つの戦略は同じ値を与える．
違いが現れるのは，Iteration 7で評価の終わらない式を扱うときである．
