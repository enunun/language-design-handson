/-!
# 第4章 単純型付きラムダ計算

関数を値として扱える言語，単純型付きラムダ計算(STLC)を定義し，
第2章と同じ型安全性を証明する．

関数を持つ言語では，関数適用`(fun x => t) v`の簡約で，本体`t`の中の`x`を`v`で置き換える．
この置換(substitution)を正しく定義し，置換が型を保つことを示すのが，この章の山場である．

変数は名前ではなくde Bruijnインデックスで表す．
`var n`は「内側から数えて`n`番目の`lam`が束縛する変数」を指す．
たとえば`fun x => fun y => x`は`lam A (lam B (var 1))`と書く．
名前を使わないので，変数の付け替え(α同値)を考えずに済む．
-/

namespace Handson.Ch4

/-! ## 構文 -/

inductive Ty where
  | bool
  /-- 関数型`A ⇒ B`． -/
  | arrow (A B : Ty)
  deriving Repr, DecidableEq

@[inherit_doc] infixr:70 " ⇒ " => Ty.arrow

/-- 項．`lam A t`は引数の型が`A`の関数`fun (x : A) => t`を表す． -/
inductive Term where
  | var (x : Nat)
  | lam (A : Ty) (t : Term)
  | app (t u : Term)
  | tru
  | fls
  | ite (c t e : Term)
  deriving Repr, DecidableEq

open Term

/-! ## 名前の付け替えと置換

変数の付け替え`ρ : Nat → Nat`と置換`σ : Nat → Term`を，項全体に一斉に適用する．
`lam`の内側に入るときは，新しく束縛される変数`var 0`を避けるため，`ext`と`exts`で
写像をずらす．
-/

/-- 付け替えを`lam`の内側用にずらす．`0`は`0`のまま，`n + 1`は`ρ n + 1`へ移す． -/
def ext (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def rename (ρ : Nat → Nat) : Term → Term
  | var x => var (ρ x)
  | lam A t => lam A (rename (ext ρ) t)
  | app t u => app (rename ρ t) (rename ρ u)
  | tru => tru
  | fls => fls
  | .ite c t e => .ite (rename ρ c) (rename ρ t) (rename ρ e)

/-- 置換を`lam`の内側用にずらす．`0`は`var 0`のまま，`n + 1`には`σ n`の自由変数を1つずらしたものを返す． -/
def exts (σ : Nat → Term) : Nat → Term
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)

def subst (σ : Nat → Term) : Term → Term
  | var x => σ x
  | lam A t => lam A (subst (exts σ) t)
  | app t u => app (subst σ t) (subst σ u)
  | tru => tru
  | fls => fls
  | .ite c t e => .ite (subst σ c) (subst σ t) (subst σ e)

/-- `var 0`を`u`で置き換え，残りの変数を1つ詰める置換． -/
def single (u : Term) : Nat → Term
  | 0 => u
  | n + 1 => var n

/-- 関数適用の簡約で使う置換`t[u]`． -/
def subst1 (t u : Term) : Term := subst (single u) t

/-! ## 小ステップ意味論(値呼び) -/

inductive Value : Term → Prop where
  | lam {A : Ty} {t : Term} : Value (lam A t)
  | tru : Value tru
  | fls : Value fls

/-- 値呼び(call-by-value)の簡約．関数と引数を左から順に値にしてから適用する． -/
inductive Step : Term → Term → Prop where
  | beta {A : Ty} {t v : Term} : Value v → Step (app (lam A t) v) (subst1 t v)
  | app1 {t t' u : Term} : Step t t' → Step (app t u) (app t' u)
  | app2 {v u u' : Term} : Value v → Step u u' → Step (app v u) (app v u')
  | iteTrue {t e : Term} : Step (ite tru t e) t
  | iteFalse {t e : Term} : Step (ite fls t e) e
  | ite {c c' t e : Term} : Step c c' → Step (ite c t e) (ite c' t e)

@[inherit_doc] infix:50 " ⟶ " => Step

/-- 0ステップ以上の簡約`t ⟶* t'`． -/
inductive Steps : Term → Term → Prop where
  | refl {t : Term} : Steps t t
  | step {t u v : Term} : Step t u → Steps u v → Steps t v

@[inherit_doc] infix:50 " ⟶* " => Steps

/-! ## 型付け規則

文脈`Γ : List Ty`の`n`番目の要素が，変数`var n`の型である．
-/

abbrev Ctx := List Ty

inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ : Ctx} {x : Nat} {A : Ty} : Γ[x]? = some A → HasType Γ (var x) A
  | lam {Γ : Ctx} {A B : Ty} {t : Term} : HasType (A :: Γ) t B → HasType Γ (lam A t) (A ⇒ B)
  | app {Γ : Ctx} {A B : Ty} {t u : Term} :
      HasType Γ t (A ⇒ B) → HasType Γ u A → HasType Γ (app t u) B
  | tru {Γ : Ctx} : HasType Γ tru .bool
  | fls {Γ : Ctx} : HasType Γ fls .bool
  | ite {Γ : Ctx} {T : Ty} {c t e : Term} :
      HasType Γ c .bool → HasType Γ t T → HasType Γ e T → HasType Γ (ite c t e) T

def Normal (t : Term) : Prop := ∀ t', ¬ t ⟶ t'

def Stuck (t : Term) : Prop := Normal t ∧ ¬ Value t

/-! ## 例 -/

/-- 恒等関数`fun (x : Bool) => x`． -/
def idBool : Term := lam .bool (var 0)

/-- 否定`fun (x : Bool) => if x then false else true`． -/
def notBool : Term := lam .bool (ite (var 0) fls tru)

example : HasType [] idBool (.bool ⇒ .bool) := .lam (.var rfl)

/-- 演習4-1：`notBool`の型を導出する． -/
example : HasType [] notBool (.bool ⇒ .bool) := by
  sorry

/-- 演習4-2：`notBool (idBool true)`は`false`に簡約される．
ヒント：`subst1`は`rfl`で計算できる．各ステップを`Steps.step`でつなぐ． -/
example : app notBool (app idBool tru) ⟶* fls := by
  unfold notBool idBool
  sorry

/-- 型の付かない項は行き詰まりうる．`true true`は関数でないものを適用している． -/
example : Stuck (app tru tru) ∧ ¬ ∃ A, HasType [] (app tru tru) A := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro t h
    cases h with
    | app1 h => cases h
    | app2 _ h => cases h
  · intro h; cases h
  · intro ⟨A, h⟩
    cases h with
    | app ht _ => cases ht

/-! ## 標準形補題 -/

theorem canonical_bool {v : Term} (hv : Value v) (ht : HasType [] v .bool) :
    v = tru ∨ v = fls := by
  cases hv with
  | lam => cases ht
  | tru => exact .inl rfl
  | fls => exact .inr rfl

theorem canonical_arrow {v : Term} {A B : Ty} (hv : Value v) (ht : HasType [] v (A ⇒ B)) :
    ∃ t, v = lam A t := by
  cases hv with
  | lam => cases ht; exact ⟨_, rfl⟩
  | tru => cases ht
  | fls => cases ht

/-! ## 進行 -/

/-- 演習4-3：空の文脈で型の付く項は，値であるか，1ステップ簡約できる．
ヒント：文脈が空なので，`var`の場合は`[][x]? = some A`から矛盾を導ける．
帰納法の前に`generalize`で文脈を変数にしておく必要がある． -/
theorem progress {t : Term} {A : Ty} (h : HasType [] t A) : Value t ∨ ∃ t', t ⟶ t' := by
  sorry

/-! ## 付け替えと置換は型を保つ

保存の証明の中心は，関数適用の簡約`(lam A t) v ⟶ t[v]`で型が保たれること，
すなわち置換補題`subst1_typing`である．
これを，一般の付け替え・置換についての補題から導く．
-/

/-- 文脈`Γ`の変数を，付け替え`ρ`で文脈`Δ`の同じ型の変数へ移せる，という条件． -/
def RenameOk (ρ : Nat → Nat) (Γ Δ : Ctx) : Prop :=
  ∀ x A, Γ[x]? = some A → Δ[ρ x]? = some A

/-- 文脈`Γ`の変数を，置換`σ`で文脈`Δ`の同じ型の項へ移せる，という条件． -/
def SubstOk (σ : Nat → Term) (Γ Δ : Ctx) : Prop :=
  ∀ x A, Γ[x]? = some A → HasType Δ (σ x) A

theorem RenameOk.ext {ρ : Nat → Nat} {Γ Δ : Ctx} {B : Ty} (h : RenameOk ρ Γ Δ) :
    RenameOk (ext ρ) (B :: Γ) (B :: Δ) := by
  intro x A hx
  cases x with
  | zero => exact hx
  | succ x => exact h x A hx

/-- 演習4-4：付け替えは型を保つ．
ヒント：型付けの導出に関する帰納法を，`ρ`と`Δ`を一般化して行う．`lam`の場合で`RenameOk.ext`を使う． -/
theorem rename_typing {ρ : Nat → Nat} {Γ Δ : Ctx} {t : Term} {A : Ty}
    (hρ : RenameOk ρ Γ Δ) (h : HasType Γ t A) : HasType Δ (rename ρ t) A := by
  sorry

/-- 文脈の先頭に変数を1つ足しても，型は保たれる(弱化)． -/
theorem weaken {Γ : Ctx} {t : Term} {A B : Ty} (h : HasType Γ t A) :
    HasType (B :: Γ) (rename Nat.succ t) A :=
  rename_typing (fun _ _ hx => hx) h

theorem SubstOk.exts {σ : Nat → Term} {Γ Δ : Ctx} {B : Ty} (h : SubstOk σ Γ Δ) :
    SubstOk (exts σ) (B :: Γ) (B :: Δ) := by
  intro x A hx
  cases x with
  | zero => exact .var hx
  | succ x => exact weaken (h x A hx)

/-- 演習4-5：置換は型を保つ．
ヒント：`rename_typing`と同じ形の帰納法で，`lam`の場合に`SubstOk.exts`を使う． -/
theorem subst_typing {σ : Nat → Term} {Γ Δ : Ctx} {t : Term} {A : Ty}
    (hσ : SubstOk σ Γ Δ) (h : HasType Γ t A) : HasType Δ (subst σ t) A := by
  sorry

/-- 置換補題．`A`型の変数を持つ項に`A`型の項を代入しても，型は保たれる． -/
theorem subst1_typing {Γ : Ctx} {t u : Term} {A B : Ty}
    (ht : HasType (A :: Γ) t B) (hu : HasType Γ u A) : HasType Γ (subst1 t u) B := by
  apply subst_typing _ ht
  intro x C hx
  cases x with
  | zero =>
    simp at hx
    rw [← hx]
    exact hu
  | succ x => exact .var hx

/-! ## 保存と型安全性 -/

/-- 演習4-6：簡約しても型は変わらない．
ヒント：`beta`の場合は，関数の型付けを`cases`で分解してから`subst1_typing`を使う． -/
theorem preservation {Γ : Ctx} {t t' : Term} {A : Ty}
    (h : HasType Γ t A) (hs : t ⟶ t') : HasType Γ t' A := by
  sorry

/-- 演習4-7：空の文脈で型の付く項は，何ステップ簡約しても行き詰まらない． -/
theorem type_safety {t t' : Term} {A : Ty}
    (h : HasType [] t A) (hs : t ⟶* t') : ¬ Stuck t' := by
  sorry

/-! ## 決定性 -/

theorem value_normal {v : Term} (hv : Value v) : Normal v := by
  intro t h
  cases hv <;> cases h

/-- 演習4-8：値呼びの簡約は決定的である． -/
theorem step_deterministic {t u u' : Term} (h₁ : t ⟶ u) (h₂ : t ⟶ u') : u = u' := by
  sorry

end Handson.Ch4
