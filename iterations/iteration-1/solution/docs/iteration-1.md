# Iteration 1 解説

演習の各手順の解説である．
見出しの番号は，演習の`docs/iteration-1.md`の手順に対応する．

## 1-1 準備

演習のパッケージはIteration 0の解答と同じなので，テストはすべて通る．

## 1-2 構文と概念

課題1の証明は`SumOf.cons (SumOf.cons (SumOf.cons SumOf.nil))`である．
課題3は，`intro h`の後に`cases h`とするだけでよい．
`[]`を結論に持つ規則は`nil`だけで，その値は`0`である．
`cases`は`1 = 0`という等式を解こうとして失敗し，その場合がありえないと判断する．

## 1-3 テストリスト

模範解答は`TESTLIST.md`にある．

- `Eval`の単体テストでは，Iteration 0の`eval`の具体例と同じ式について，導出の例を書いた．
  導出できない例として，$1 + 2 \Downarrow 4$を挙げた．
- `eval`と`Eval`の関係として，健全性`eval_sound`と完全性`eval_complete`を挙げた．
  どちらも`eval`の性質なので，`EvalTest.lean`に置いた．
- 決定性`eval_deterministic`は，完全性から導くので，同じ`EvalTest.lean`に置いた．
- 既存のテストの期待値は変わらない．

## 1-4 設計書

### 言語仕様書

- `## 意味`：`eval`の4つの等式を，大ステップ意味論の4つの推論規則に置き換えた．
  規則の形は等式と同じで，部分式の値を前提に，式全体の値を結論に書いた．
- `eval`は意味論を計算する実装であることを，`## 意味`の最後に書いた．
- `## 性質`：等価性の説明に，`eval`が意味論に従うことを書き足した．
  性質に`eval_sound`，`eval_complete`，`eval_deterministic`を足した．

### モジュール依存図

`Mini.BigStep`は`Term`を使うので，`Mini.Syntax`だけに依存する．
実装のモジュールは`Mini.BigStep`を使わない．
仕様と実装は，テストの定理で結び付けている．
このことを図の下に約束として書いた．

## 1-5 テストファーストの実装

### `Mini.BigStep`

`Mini/BigStep.lean`を作り，`Eval`を構成子なしで宣言した．

```lean
inductive Eval : Term → Nat → Prop

@[inherit_doc] infix:50 " ⇓ " => Eval
```

#### $3 \Downarrow 3$と$1 + 2 \Downarrow 3$を導出できる

```lean
example : Term.num 3 ⇓ 3 := Eval.num

example : Term.add (.num 1) (.num 2) ⇓ 3 := Eval.add Eval.num Eval.num
```

規則がまだないので，構成子が見つからないというエラーになる．
次は，`num`の規則だけを足した時点の2つ目の例のエラーである．

```text
error: MiniTest/Unit/BigStepTest.lean:15:44: Unknown constant `Mini.Eval.add`
```

`num`と`add`の規則を足す．

```lean
inductive Eval : Term → Nat → Prop where
  | num {n : Nat} : Eval (.num n) n
  | add {t₁ t₂ : Term} {n₁ n₂ : Nat} : Eval t₁ n₁ → Eval t₂ n₂ → Eval (.add t₁ t₂) (n₁ + n₂)
```

#### $1 + 2 * 3 \Downarrow 7$，$2 - 5 \Downarrow 0$を導出できる

`mul`と`sub`の規則を，`add`と同じ形で足す．
導出は，規則を組み合わせた木になる．

```lean
example : Term.add (.num 1) (.mul (.num 2) (.num 3)) ⇓ 7 :=
  Eval.add Eval.num (Eval.mul Eval.num Eval.num)
```

#### $1 + 2 \Downarrow 4$は導出できない

まず，`1 + 2`の値はどんな`n`でも`3`であることを`have`で示し，それを`4`に当てはめる．

```lean
example : ¬ Term.add (.num 1) (.num 2) ⇓ 4 := by
  have h3 : ∀ n, Term.add (.num 1) (.num 2) ⇓ n → n = 3 := by
    intro n h
    cases h with
    | add h₁ h₂ =>
      cases h₁
      cases h₂
      rfl
  intro h
  have := h3 4 h
  contradiction
```

### `Mini.Eval`の性質

#### `eval_sound`

主張を書き，証明を`sorry`にして失敗を確かめた．

```text
error: MiniTest/Unit/EvalTest.lean:58:8: declaration uses `sorry`
```

`subst h`で`n`を`eval t`に置き換えると，ゴールは`t ⇓ eval t`になる．
`t`についての帰納法で，各場合に対応する規則を当てはめる．
`eval (.add t₁ t₂)`は定義から`eval t₁ + eval t₂`なので，`Eval.add ih₁ ih₂`がそのまま当てはまる．

```lean
theorem eval_sound {t : Term} {n : Nat} (h : eval t = n) : t ⇓ n := by
  subst h
  induction t with
  | num n => exact Eval.num
  | add t₁ t₂ ih₁ ih₂ => exact Eval.add ih₁ ih₂
  | sub t₁ t₂ ih₁ ih₂ => exact Eval.sub ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ => exact Eval.mul ih₁ ih₂
```

#### `eval_complete`

導出`h`についての帰納法で証明する．
`add`の場合，帰納法の仮定は`eval t₁ = n₁`と`eval t₂ = n₂`である．

```lean
theorem eval_complete {t : Term} {n : Nat} (h : t ⇓ n) : eval t = n := by
  induction h with
  | num => rfl
  | add _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | sub _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
```

#### `eval_deterministic`

完全性から，`n`と`m`はどちらも`eval t`に等しい．

```lean
theorem eval_deterministic {t : Term} {n m : Nat} (h₁ : t ⇓ n) (h₂ : t ⇓ m) : n = m := by
  rw [← eval_complete h₁, ← eval_complete h₂]
```

## 1-6 振り返り

1. 導出の例と，健全性・完全性の3つの性質がそろっていれば，`eval`と`Eval`は互いに確かめ合える．
2. 健全性だけでは，評価器が値を返したときにそれが正しいことしかわからない．
   このIterationの`eval`は必ず値を返すので，健全性だけでも`eval`の誤りは見つかる．
   しかし，評価器が値を返さないことのある言語(Iteration 3以降)では，完全性がなければ「何も返さない評価器」も健全になってしまう．
3. 導出についての帰納法で直接証明する．
   `t ⇓ n`の導出で帰納法を行い，各場合でもう一方の導出`t ⇓ m`を`cases`によって分解する．
   このとき，帰納法の仮定を任意の`m`について使えるように一般化する必要がある．
   Iteration 2で，この形の証明を書く．
4. 模範解答の設計書は，`mise run check-design`で`一致`になる．
   規則名`num`，`add`，`sub`，`mul`が`Eval`の構成子と一致していることも照合される．

## 1-7 発展課題

`simplify`は，まず部分式を簡単にする．そのうえで，右の部分式が`0`や`1`になったかを調べる．

```lean
def simplify : Term → Term
  | .num n => .num n
  | .add t₁ t₂ =>
    match simplify t₂ with
    | .num 0 => simplify t₁
    | u₂ => .add (simplify t₁) u₂
  | .sub t₁ t₂ => .sub (simplify t₁) (simplify t₂)
  | .mul t₁ t₂ =>
    match simplify t₂ with
    | .num 1 => simplify t₁
    | u₂ => .mul (simplify t₁) u₂
```

まず`eval (simplify t) = eval t`を`t`についての帰納法で示す．
`simplify`の定義の中の`match`は，`split`で場合分けできる．
`split`は，ゴールの中の`match`や`if`を，その場合ごとのゴールに分けるtacticである．

```lean
theorem eval_simplify (t : Term) : eval (simplify t) = eval t := by
  induction t with
  | num n => rfl
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [simplify]
    split
    · next h => rw [h] at ih₂; simp [eval, ih₁, ← ih₂]
    · simp [eval, ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => simp [simplify, eval, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ =>
    simp only [simplify]
    split
    · next h => rw [h] at ih₂; simp [eval, ih₁, ← ih₂]
    · simp [eval, ih₁, ih₂]
```

$t \Downarrow n$と$\mathit{simplify}(t) \Downarrow n$の同値は，健全性と完全性を使って`eval`の等式に直せば，`eval_simplify`から従う．
