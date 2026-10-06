import Mini.BigStep

/-!
# `Mini.BigStep`の単体テスト
-/

namespace MiniTest.BigStepTest

open Mini

/-! ## 導出の例 -/

example : Term.num 3 ⇓ .num 3 := Eval.num

example : Term.add (.num 1) (.num 2) ⇓ .num 3 := Eval.add Eval.num Eval.num

/-- `1 + 2 * 3`の導出．規則を組み合わせた木になる． -/
example : Term.add (.num 1) (.mul (.num 2) (.num 3)) ⇓ .num 7 :=
  Eval.add Eval.num (Eval.mul Eval.num Eval.num)

/-- 引き算の結果が負になるときは`0`になる． -/
example : Term.sub (.num 2) (.num 5) ⇓ .num 0 := Eval.sub Eval.num Eval.num

/-- `1 + 2`を評価しても`4`にはならない． -/
example : ¬ Term.add (.num 1) (.num 2) ⇓ .num 4 := by
  have h3 : ∀ v, Term.add (.num 1) (.num 2) ⇓ v → v = .num 3 := by
    intro v h
    cases h with
    | add h₁ h₂ =>
      cases h₁
      cases h₂
      rfl
  intro h
  have := h3 _ h
  contradiction

example : Term.ite .tru (.num 1) (.num 2) ⇓ .num 1 := Eval.iteTrue Eval.tru Eval.num

example : Term.ite (.iszero (.num 0)) (.num 1) (.num 2) ⇓ .num 1 :=
  Eval.iteTrue (Eval.iszero Eval.num) Eval.num

example : Term.iszero (.num 5) ⇓ .bool false := Eval.iszero Eval.num

/-- `1 + true`には値がない． -/
example : ¬ ∃ v, Term.add (.num 1) .tru ⇓ v := by
  intro ⟨v, h⟩
  cases h with
  | add _ h₂ => cases h₂

/-- `let x = 1 + 2 in x * x`の導出．本体の`x`を値`3`で置き換えた`3 * 3`を評価する． -/
example : Term.let_ "x" (.add (.num 1) (.num 2)) (.mul (.var "x") (.var "x")) ⇓ .num 9 :=
  Eval.let_ (Eval.add Eval.num Eval.num) (Eval.mul Eval.num Eval.num)

/-- 関数はそれ自身が値である． -/
example : Term.lam "x" .nat (.var "x") ⇓ .lam "x" .nat (.var "x") := Eval.lam

/-- `(fun (x : Nat) => x + 1) 2`の導出．本体の`x`を値`2`で置き換えた`2 + 1`を評価する． -/
example : Term.app (.lam "x" .nat (.add (.var "x") (.num 1))) (.num 2) ⇓ .num 3 :=
  Eval.app Eval.lam Eval.num (Eval.add Eval.num Eval.num)

/-- 自由な変数には値がない． -/
example : ¬ ∃ v, Term.var "x" ⇓ v := by
  intro ⟨v, h⟩
  cases h

/-- 自分自身を呼び続ける再帰関数`fix loop (n : Nat) : Nat => loop n`． -/
def loopFn : Term := .fix "loop" "n" .nat .nat (.app (.var "loop") (.var "n"))

/-- `loop 0`．評価が終わらない． -/
def loopApp : Term := .app loopFn (.num 0)

/-- 階乗を計算する再帰関数`fix fact (n : Nat) : Nat => if iszero n then 1 else n * fact (n - 1)`． -/
def factFn : Term :=
  .fix "fact" "n" .nat .nat
    (.ite (.iszero (.var "n")) (.num 1) (.mul (.var "n") (.app (.var "fact") (.sub (.var "n") (.num 1)))))

/-- 再帰関数はそれ自身が値である． -/
example : loopFn ⇓ .fix "loop" "n" .nat .nat (.app (.var "loop") (.var "n")) := Eval.fix

/--
`fact 1`の導出．本体の`n`を`1`で，`fact`を再帰関数自身で置き換えた式を評価する．
`refine`で，導出の木を根から順に組み立てる．
-/
example : Term.app factFn (.num 1) ⇓ .num 1 := by
  refine Eval.appFix Eval.fix Eval.num ?_
  refine Eval.iteFalse (Eval.iszero Eval.num) ?_
  refine Eval.mul (n₁ := 1) (n₂ := 1) Eval.num ?_
  refine Eval.appFix Eval.fix (Eval.sub Eval.num Eval.num) ?_
  exact Eval.iteTrue (Eval.iszero Eval.num) Eval.num

/-- `loop 0`には値がない．導出があれば，その中にもっと小さい`loop 0`の導出があるはずだからである． -/
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

/-- `(1 + 2, true)`の導出．組の2つの成分をそれぞれ評価する． -/
example : Term.pair (.add (.num 1) (.num 2)) .tru ⇓ .pair (.num 3) (.bool true) :=
  Eval.pair (Eval.add Eval.num Eval.num) Eval.tru

example : Term.fst (.pair (.add (.num 1) (.num 2)) .tru) ⇓ .num 3 :=
  Eval.fst (Eval.pair (Eval.add Eval.num Eval.num) Eval.tru)

/-- 組の成分の評価は省けない．2つ目の成分に値がなければ，`fst`にも値がない． -/
example : ¬ ∃ v, Term.fst (.pair (.num 1) (.add (.num 1) .tru)) ⇓ v := by
  intro ⟨v, h⟩
  cases h with
  | fst h =>
    cases h with
    | pair _ h₂ =>
      cases h₂ with
      | add _ h => cases h

/-- 組でない値からは，成分を取り出せない． -/
example : ¬ ∃ v, Term.fst (.num 1) ⇓ v := by
  intro ⟨v, h⟩
  cases h with
  | fst h => cases h

/-! ## 決定性 -/

/-- 大ステップ意味論は決定的である． -/
theorem bigstep_deterministic {t : Term} {v w : Value} (h₁ : t ⇓ v) (h₂ : t ⇓ w) : v = w := by
  induction h₁ generalizing w with
  | num => cases h₂; rfl
  | add _ _ ih₁ ih₂ =>
    cases h₂ with
    | add h₁' h₂' =>
      cases ih₁ h₁'
      cases ih₂ h₂'
      rfl
  | sub _ _ ih₁ ih₂ =>
    cases h₂ with
    | sub h₁' h₂' =>
      cases ih₁ h₁'
      cases ih₂ h₂'
      rfl
  | mul _ _ ih₁ ih₂ =>
    cases h₂ with
    | mul h₁' h₂' =>
      cases ih₁ h₁'
      cases ih₂ h₂'
      rfl
  | tru => cases h₂; rfl
  | fls => cases h₂; rfl
  | iteTrue _ _ ihc iht =>
    cases h₂ with
    | iteTrue _ ht' => exact iht ht'
    | iteFalse hc' _ => cases ihc hc'
  | iteFalse _ _ ihc ihe =>
    cases h₂ with
    | iteTrue hc' _ => cases ihc hc'
    | iteFalse _ he' => exact ihe he'
  | iszero _ ih =>
    cases h₂ with
    | iszero h' =>
      cases ih h'
      rfl
  | let_ _ _ ih₁ ih₂ =>
    cases h₂ with
    | let_ h₁' h₂' =>
      cases ih₁ h₁'
      exact ih₂ h₂'
  | lam => cases h₂; rfl
  | app _ _ _ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | app h₁' h₂' h₃' =>
      cases ih₁ h₁'
      cases ih₂ h₂'
      exact ih₃ h₃'
    | appFix h₁' _ _ => cases ih₁ h₁'
  | fix => cases h₂; rfl
  | appFix _ _ _ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | app h₁' _ _ => cases ih₁ h₁'
    | appFix h₁' h₂' h₃' =>
      cases ih₁ h₁'
      cases ih₂ h₂'
      exact ih₃ h₃'
  | pair _ _ ih₁ ih₂ =>
    cases h₂ with
    | pair h₁' h₂' =>
      cases ih₁ h₁'
      cases ih₂ h₂'
      rfl
  | fst _ ih =>
    cases h₂ with
    | fst h' =>
      cases ih h'
      rfl
  | snd _ ih =>
    cases h₂ with
    | snd h' =>
      cases ih h'
      rfl

/-! ## 式の等価性

式`t`と`u`が同じ値に評価される(どちらも値がない場合も含む)とき，`t`と`u`は等価であるという．
-/

theorem add_comm {t₁ t₂ : Term} {v : Value} : Term.add t₁ t₂ ⇓ v ↔ Term.add t₂ t₁ ⇓ v := by
  constructor
  · intro h
    cases h with
    | add h₁ h₂ => rw [Nat.add_comm]; exact .add h₂ h₁
  · intro h
    cases h with
    | add h₁ h₂ => rw [Nat.add_comm]; exact .add h₂ h₁

theorem add_assoc {t₁ t₂ t₃ : Term} {v : Value} :
    Term.add (.add t₁ t₂) t₃ ⇓ v ↔ Term.add t₁ (.add t₂ t₃) ⇓ v := by
  constructor
  · intro h
    cases h with
    | add h₁₂ h₃ =>
      cases h₁₂ with
      | add h₁ h₂ => rw [Nat.add_assoc]; exact .add h₁ (.add h₂ h₃)
  · intro h
    cases h with
    | add h₁ h₂₃ =>
      cases h₂₃ with
      | add h₂ h₃ => rw [← Nat.add_assoc]; exact .add (.add h₁ h₂) h₃

theorem mul_comm {t₁ t₂ : Term} {v : Value} : Term.mul t₁ t₂ ⇓ v ↔ Term.mul t₂ t₁ ⇓ v := by
  constructor
  · intro h
    cases h with
    | mul h₁ h₂ => rw [Nat.mul_comm]; exact .mul h₂ h₁
  · intro h
    cases h with
    | mul h₁ h₂ => rw [Nat.mul_comm]; exact .mul h₂ h₁

theorem mul_assoc {t₁ t₂ t₃ : Term} {v : Value} :
    Term.mul (.mul t₁ t₂) t₃ ⇓ v ↔ Term.mul t₁ (.mul t₂ t₃) ⇓ v := by
  constructor
  · intro h
    cases h with
    | mul h₁₂ h₃ =>
      cases h₁₂ with
      | mul h₁ h₂ => rw [Nat.mul_assoc]; exact .mul h₁ (.mul h₂ h₃)
  · intro h
    cases h with
    | mul h₁ h₂₃ =>
      cases h₂₃ with
      | mul h₂ h₃ => rw [← Nat.mul_assoc]; exact .mul (.mul h₁ h₂) h₃

/-- `t`の値が数なら，`t * 1`の値もその数である． -/
theorem mul_one {t : Term} {n : Nat} (h : t ⇓ .num n) : Term.mul t (.num 1) ⇓ .num n := by
  have := Eval.mul h (Eval.num (n := 1))
  rw [Nat.mul_one] at this
  exact this

/-- `t * 1`と`t`は，等価とは限らない．`true`の値は`true`だが，`true * 1`には値がない． -/
theorem mul_one_not_equiv : ¬ ∀ (t : Term) (v : Value), Term.mul t (.num 1) ⇓ v ↔ t ⇓ v := by
  intro h
  have := (h .tru (.bool true)).mpr Eval.tru
  cases this

/-- `-`は結合法則を満たさない．`(3 - 2) - 1`の値は`0`だが，`3 - (2 - 1)`の値は`2`である． -/
theorem sub_not_assoc :
    ¬ ∀ (t₁ t₂ t₃ : Term) (v : Value), Term.sub (.sub t₁ t₂) t₃ ⇓ v ↔ Term.sub t₁ (.sub t₂ t₃) ⇓ v := by
  intro h
  have h₀ : Term.sub (.sub (.num 3) (.num 2)) (.num 1) ⇓ .num 0 :=
    Eval.sub (Eval.sub Eval.num Eval.num) Eval.num
  have h₂ : Term.sub (.num 3) (.sub (.num 2) (.num 1)) ⇓ .num 2 :=
    Eval.sub Eval.num (Eval.sub Eval.num Eval.num)
  have := bigstep_deterministic ((h _ _ _ _).mp h₀) h₂
  cases this

end MiniTest.BigStepTest
