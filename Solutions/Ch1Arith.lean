/-!
# 第1章 算術式と小ステップ意味論

真偽値と自然数だけを持つ小さな言語を定義し，その振る舞いを小ステップ意味論
(1ステップずつ式を書き換える規則)で与える．
この章で確かめる性質は次の2つである．

* 値はそれ以上簡約されない(`value_normal`)．
* 簡約は決定的である．すなわち，ある式から1ステップで進める先はたかだか1つである
  (`step_deterministic`)．

最後に，評価規則を1つ足しただけで決定性が崩れる例を見て，
規則の設計が性質を左右することを確かめる．
-/

namespace Solutions.Ch1

/-! ## 構文 -/

/-- 項．`ite c t e`は`if c then t else e`を表す． -/
inductive Term where
  | tru
  | fls
  | ite (c t e : Term)
  | zero
  | succ (t : Term)
  | pred (t : Term)
  | iszero (t : Term)
  deriving Repr, DecidableEq

open Term

/-! ## 値 -/

/-- 数値．`zero`に`succ`を0回以上適用したもの． -/
inductive NumVal : Term → Prop where
  | zero : NumVal zero
  | succ {n : Term} : NumVal n → NumVal (succ n)

/-- 値．評価が終わった結果として認める項． -/
inductive Value : Term → Prop where
  | tru : Value tru
  | fls : Value fls
  | num {n : Term} : NumVal n → Value n

/-! ## 小ステップ意味論 -/

/-- 1ステップの簡約`t ⟶ t'`．
`ite`，`succ`，`pred`，`iszero`の引数は，左から順に値になるまで簡約する． -/
inductive Step : Term → Term → Prop where
  | iteTrue {t e : Term} : Step (ite tru t e) t
  | iteFalse {t e : Term} : Step (ite fls t e) e
  | ite {c c' t e : Term} : Step c c' → Step (ite c t e) (ite c' t e)
  | succ {t t' : Term} : Step t t' → Step (succ t) (succ t')
  | predZero : Step (pred zero) zero
  | predSucc {n : Term} : NumVal n → Step (pred (succ n)) n
  | pred {t t' : Term} : Step t t' → Step (pred t) (pred t')
  | iszeroZero : Step (iszero zero) tru
  | iszeroSucc {n : Term} : NumVal n → Step (iszero (succ n)) fls
  | iszero {t t' : Term} : Step t t' → Step (iszero t) (iszero t')

@[inherit_doc] infix:50 " ⟶ " => Step

/-- 0ステップ以上の簡約`t ⟶* t'`(`Step`の反射推移閉包)． -/
inductive Steps : Term → Term → Prop where
  | refl {t : Term} : Steps t t
  | step {t u v : Term} : Step t u → Steps u v → Steps t v

@[inherit_doc] infix:50 " ⟶* " => Steps

/-- 正規形．これ以上簡約できない項． -/
def Normal (t : Term) : Prop := ∀ t', ¬ t ⟶ t'

/-! ## 多ステップ簡約の基本性質 -/

theorem Steps.single {t u : Term} (h : t ⟶ u) : t ⟶* u :=
  .step h .refl

theorem Steps.trans {t u v : Term} (h₁ : t ⟶* u) (h₂ : u ⟶* v) : t ⟶* v := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-! ## 例 -/

/-- 演習1-1：`if iszero (pred (succ 0)) then 0 else succ 0`は`0`に簡約される．
`Steps.step`と`Step`の各規則を組み合わせて，簡約列を1ステップずつ書く． -/
example : ite (iszero (pred (succ zero))) zero (succ zero) ⟶* zero := by
  -- 演習ここから
  apply Steps.step (Step.ite (Step.iszero (Step.predSucc NumVal.zero)))
  apply Steps.step (Step.ite Step.iszeroZero)
  apply Steps.step Step.iteTrue
  exact Steps.refl
  -- 演習ここまで

/-! ## 値は正規形である -/

theorem numVal_normal {n : Term} (hn : NumVal n) : Normal n := by
  induction hn with
  | zero => intro t h; cases h
  | succ _ ih =>
    intro t h
    cases h with
    | succ h => exact ih _ h

/-- 演習1-2：値はそれ以上簡約されない．
ヒント：`Value`の場合分けをし，数値の場合は`numVal_normal`を使う． -/
theorem value_normal {v : Term} (hv : Value v) : Normal v := by
  -- 演習ここから
  cases hv with
  | tru => intro t h; cases h
  | fls => intro t h; cases h
  | num hn => exact numVal_normal hn
  -- 演習ここまで

/-! ## 決定性 -/

/-- 演習1-3：簡約は決定的である．
ヒント：`h₁`に関する帰納法を，`u'`を一般化して行い，各場合で`h₂`を場合分けする．
一方の規則が値を簡約しようとしている組み合わせは，`numVal_normal`で矛盾を導く． -/
theorem step_deterministic {t u u' : Term} (h₁ : t ⟶ u) (h₂ : t ⟶ u') : u = u' := by
  -- 演習ここから
  induction h₁ generalizing u' with
  | iteTrue =>
    cases h₂ with
    | iteTrue => rfl
    | ite h => cases h
  | iteFalse =>
    cases h₂ with
    | iteFalse => rfl
    | ite h => cases h
  | ite h ih =>
    cases h₂ with
    | iteTrue => cases h
    | iteFalse => cases h
    | ite h' => rw [ih h']
  | succ _ ih =>
    cases h₂ with
    | succ h' => rw [ih h']
  | predZero =>
    cases h₂ with
    | predZero => rfl
    | pred h => cases h
  | predSucc hn =>
    cases h₂ with
    | predSucc => rfl
    | pred h => exact absurd h (numVal_normal (.succ hn) _)
  | pred h ih =>
    cases h₂ with
    | predZero => cases h
    | predSucc hn => exact absurd h (numVal_normal (.succ hn) _)
    | pred h' => rw [ih h']
  | iszeroZero =>
    cases h₂ with
    | iszeroZero => rfl
    | iszero h => cases h
  | iszeroSucc hn =>
    cases h₂ with
    | iszeroSucc => rfl
    | iszero h => exact absurd h (numVal_normal (.succ hn) _)
  | iszero h ih =>
    cases h₂ with
    | iszeroZero => cases h
    | iszeroSucc hn => exact absurd h (numVal_normal (.succ hn) _)
    | iszero h' => rw [ih h']
  -- 演習ここまで

/-- 決定性から，正規形への簡約の結果は1つに決まる． -/
theorem steps_normal_unique {t u u' : Term}
    (h₁ : t ⟶* u) (hu : Normal u) (h₂ : t ⟶* u') (hu' : Normal u') : u = u' := by
  induction h₁ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | step h _ => exact absurd h (hu _)
  | step h _ ih =>
    cases h₂ with
    | refl => exact absurd h (hu' _)
    | step h' hs =>
      rw [step_deterministic h h'] at *
      exact ih hu hs

/-! ## 設計の失敗例：`if`の枝を先に簡約する

`Step`に，`if`の`then`節を条件より先に簡約してよい規則を加えた言語`StepEager`を考える．
規則を1つ足しただけで，決定性が成り立たなくなる．
-/

/-- `Step`に`then`節の簡約を許す規則`iteThen`を加えた簡約． -/
inductive StepEager : Term → Term → Prop where
  | base {t u : Term} : t ⟶ u → StepEager t u
  | iteThen {c t t' e : Term} : StepEager t t' → StepEager (ite c t e) (ite c t' e)

/-- 演習1-4：`StepEager`は決定的ではない．
ヒント：`ite tru (pred zero) zero`は2通りに簡約できる． -/
theorem stepEager_not_deterministic :
    ¬ ∀ t u u', StepEager t u → StepEager t u' → u = u' := by
  -- 演習ここから
  intro h
  have := h (ite tru (pred zero) zero) (pred zero) (ite tru zero zero)
    (.base .iteTrue) (.iteThen (.base .predZero))
  cases this
  -- 演習ここまで

end Solutions.Ch1
