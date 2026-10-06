# Iteration 7 解説

演習の各手順の解説である．
見出しの番号は，演習の`docs/iteration-7.md`の手順に対応する．

## 7-1 準備

演習のパッケージはIteration 6の解答と同じなので，テストはすべて通る．

## 7-2 構文と概念

課題2の簡約列は，完成した`mini steps`で確かめられる．

```text
$ lake exe mini steps "(fix f (n : Nat) : Nat => if iszero n then 0 else f (n - 1)) 1"
(fix f (n : Nat) : Nat => if iszero n then 0 else f (n - 1)) 1
⟶ if iszero 1 then 0 else (fix f (n : Nat) : Nat => if iszero n then 0 else f (n - 1)) (1 - 1)
⟶ if false then 0 else (fix f (n : Nat) : Nat => if iszero n then 0 else f (n - 1)) (1 - 1)
⟶ (fix f (n : Nat) : Nat => if iszero n then 0 else f (n - 1)) (1 - 1)
⟶ (fix f (n : Nat) : Nat => if iszero n then 0 else f (n - 1)) 0
⟶ if iszero 0 then 0 else (fix f (n : Nat) : Nat => if iszero n then 0 else f (n - 1)) (0 - 1)
⟶ if true then 0 else (fix f (n : Nat) : Nat => if iszero n then 0 else f (n - 1)) (0 - 1)
⟶ 0
```

1ステップ目で，本体の`n`が`1`に，`f`が再帰関数自身に置き換わる．
課題3の型は$\mathsf{Nat} \rightarrow \mathsf{Nat}$である．
本体の型は，文脈$(n : \mathsf{Nat}), (f : \mathsf{Nat} \rightarrow \mathsf{Nat})$のもとで求める．

## 7-3 テストリスト

模範解答は`TESTLIST.md`にある．

- 再帰関数そのものの値は，その再帰関数自身である．大ステップ意味論の規則`fix`で確かめた．
- `loop 0`について，大ステップ意味論では値がないこと，小ステップ意味論では自分自身にしか簡約されないこと，評価器ではどれだけ燃料を与えても燃料切れになること，型付けでは型`Nat`が付くことを確かめた．
- 型エラーは，本体の型が結果の型の注釈と合わない場合を挙げた．
- 関数型の標準形補題`canonical_arrow`は，主張が「関数型を持つ値は関数か再帰関数である」に変わる．ほかの既存の定理は，主張が変わらず，証明に場合が加わる．

## 7-4 設計書

### 言語仕様書

- `## 構文`に再帰関数を足した．`fix`は`f`と`x`の2つの名前を束縛することを書いた．
- `## 値`に再帰関数を足し，値を表す式の規則`fix`を足した．
- `### 置換`に再帰関数の場合を足した．`f`と`x`のどちらかが置き換える変数と同じなら，本体を置き換えない．
- 大ステップ意味論に`fix`と`appFix`の規則を，小ステップ意味論に`betaFix`の規則を足した．
- `## 型`に再帰関数の型付け規則を足した．本体の型を求める前に`f`の型が要るので，結果の型を注釈で与える．
- `### 評価器`に，評価が終わらない式はどれだけ燃料を与えても燃料切れになることを書いた．

### モジュール依存図

依存の矢印は変わらない．
`Mini.Pretty`の説明に，再帰関数の値も表示することを書き足した．

## 7-5 テストファーストの実装

### 構文と構文解析器

構成子を足して構文解析器を置き換えると，場合の足りない定義がエラーになる．

```text
error: Mini/Pretty.lean:29:2: Missing cases:
error: Mini/Pretty.lean:49:2: Missing cases:
error: Mini/Typing.lean:52:2: Missing cases:
error: Mini/Subst.lean:15:2: Missing cases:
```

### 意味論と評価器

置換では，`fix`が束縛する2つの名前のどちらかが`x`なら，本体を置き換えない．

```lean
  | .fix g y A B u => .fix g y A B (if g = x ∨ y = x then u else subst x v u)
```

再帰関数の適用は，本体の`x`を引数の値で置き換えてから，`f`を再帰関数自身で置き換える．

```lean
  | betaFix {f x : String} {A B : Ty} {b v : Term} :
      IsValue v → Step (.app (.fix f x A B b) v) (subst f (.fix f x A B b) (subst x v b))
```

`loop 0`に値がないことは，`suffices`で主張を一般化してから，導出についての帰納法で示した．
`appFix`の場合では，`t₁ ⇓ fix …`と`t₂ ⇓ v₂`を`cases`で分解すると，3つ目の前提が`loop 0`の導出になる．
その導出についての帰納法の仮定から矛盾が出る．

```lean
example : ¬ ∃ v, loopApp ⇓ v := by
  suffices h : ∀ t v, t ⇓ v → t ≠ loopApp by
    intro ⟨v, hv⟩
    exact h _ _ hv rfl
  intro t v h
  induction h with
  | app h₁ _ _ _ _ _ =>
    intro heq
    cases heq
    cases h₁
  | appFix h₁ h₂ _ _ _ ih =>
    intro heq
    cases heq
    cases h₁
    cases h₂
    exact ih rfl
  | _ => intro heq; cases heq
```

`loop 0`がどれだけ燃料を与えても燃料切れになることは，燃料についての帰納法で示した．
`eval`を1段展開すると，`step loopApp = some loopApp`なので，燃料が1つ少ない場合に帰着する．

```lean
example (k : Nat) : eval k loopApp = .error .outOfFuel := by
  induction k with
  | zero => rfl
  | succ k ih => rw [eval]; exact ih
```

### 型付け

関数型の標準形補題は，主張に再帰関数の場合が加わる．

```lean
theorem canonical_arrow {Γ : Ctx} {v : Value} {A B : Ty} (h : HasType Γ v.toTerm (.arrow A B)) :
    (∃ x b, v = .lam x A b) ∨ (∃ f x b, v = .fix f x A B b) := by
```

置換補題の再帰関数の場合は，`f`と`x`のどちらかが置き換える変数と同じかどうかで分けた．
同じ場合は，`rcases hgy with rfl | rfl`で等式を取り出してから，文脈の包含を示した．

```lean
  | fix g y A' B' b ih =>
    cases hu with
    | fix hb =>
      by_cases hgy : g = x ∨ y = x
      · simp only [subst, hgy, ite_true]
        refine .fix (weaken hb ?_)
        intro z D hz
        rcases hgy with rfl | rfl <;>
          by_cases hzy : z = y <;> by_cases hzg : z = g <;> simp_all [Ctx.lookup]
      · simp only [subst, hgy, ite_false]
        refine .fix (ih (weaken hb ?_))
        intro z D hz
        by_cases hzy : z = y <;> by_cases hzg : z = g <;> by_cases hzx : z = x <;> simp_all [Ctx.lookup]
```

保存の`betaFix`の場合は，置換補題を2回使った．
1回目で`x`を引数の値で，2回目で`f`を再帰関数自身で置き換える．
2回目には再帰関数の型付けが要るので，`cases`で分解する前に`hf`として残しておく．

```lean
    | betaFix _ =>
      have hf := h₁
      cases h₁ with
      | fix hb => exact subst_typing (subst_typing hb h₂) hf
```

### 表示と`run`

再帰関数は，`fun`と同じく強さ`0`で表示する．

```text
$ lake exe mini eval "(fix fact (n : Nat) : Nat => if iszero n then 1 else n * fact (n - 1)) 5"
120
$ lake exe mini eval --fuel 1000 "(fix loop (n : Nat) : Nat => loop n) 0"
燃料切れ：1000ステップで評価が終わらなかった
$ lake exe mini steps --fuel 2 "(fix loop (n : Nat) : Nat => loop n) 0"
(fix loop (n : Nat) : Nat => loop n) 0
⟶ (fix loop (n : Nat) : Nat => loop n) 0
⟶ (fix loop (n : Nat) : Nat => loop n) 0
$ lake exe mini check "fix f (x : Nat) : Bool => x"
型エラー：再帰関数の本体の型が合わない(期待：Bool，実際：Nat)
```

## 7-6 振り返り

1. 既存の定理のうち，主張が変わったのは`canonical_arrow`だけである．型安全性の定理は，主張を変えないまま再帰関数まで広がった．
2. 型安全性は，`loop 0`が行き詰まらないことを保証する．`loop 0`は，値に着かないが，いつでも1ステップ簡約できる．
3. 言えない．燃料切れは，その燃料では値に着かなかったことしか表さない．`fact 5`も，燃料が少なければ燃料切れになる．
4. 模範解答の設計書は，`mise run check-design`で`一致`になる．

## 7-7 発展課題

Iteration 6と同じく，名前呼びのβ簡約を足した簡約を定義する．
$(\mathsf{fun}\ (x : \mathsf{Nat}) \Rightarrow 1)\ (\mathit{loop}\ 0)$は，名前呼びでは1ステップで$1$になる．
値呼びでは，引数$\mathit{loop}\ 0$を簡約し続けるので，式全体も自分自身にしか簡約されない．

```lean
inductive StepByName : Term → Term → Prop where
  | base {t t' : Term} : t ⟶ t' → StepByName t t'
  | betaN {x : String} {A : Ty} {b u : Term} : StepByName (.app (.lam x A b) u) (subst x u b)

/-- `(fun (x : Nat) => 1) (loop 0)`． -/
def constLoop : Term := .app (.lam "x" .nat (.num 1)) loopApp

example : StepByName constLoop (.num 1) := .betaN

example {t : Term} (h : constLoop ⟶* t) : t = constLoop := by
  suffices ∀ s, s ⟶* t → s = constLoop → t = constLoop from this _ h rfl
  clear h
  intro s hs
  induction hs with
  | refl => exact id
  | step h₁ _ ih =>
    intro heq
    subst heq
    exact ih (step_deterministic h₁ (Step.app2 IsValue.lam (Step.betaFix IsValue.num)))
```

この式には型$\mathsf{Nat}$が付く．

```lean
example : HasType [] constLoop .nat := .app (.lam .num) (.app (.fix (.app (.var rfl) (.var rfl))) .num)
```

型の付く式でも，評価戦略によって値に着くかどうかが変わる．
値呼びの型安全性は，この式が行き詰まらないことを保証するが，値に着くことは保証しない．
