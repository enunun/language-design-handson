import Solutions.Ch1Arith

/-!
# 第2章 型システムと型安全性

第1章の言語には，`succ tru`のように値でもないのに簡約できない項がある．
このような項を「行き詰まった(stuck)項」と呼ぶ．
この章では型システムを定義し，型の付く項は決して行き詰まらないこと
(型安全性)を証明する．

型安全性は，次の2つの補題に分けて示すのが定石である．

* 進行(progress)：型の付く項は，値であるか，1ステップ簡約できる．
* 保存(preservation)：型の付く項を簡約しても，型は変わらない．
-/

namespace Solutions.Ch2

open Solutions.Ch1
open Term

/-! ## 型と型付け規則 -/

inductive Ty where
  | bool
  | nat
  deriving Repr, DecidableEq

/-- 型付け関係`HasType t T`．「項`t`は型`T`を持つ」と読む． -/
inductive HasType : Term → Ty → Prop where
  | tru : HasType tru .bool
  | fls : HasType fls .bool
  | ite {c t e : Term} {T : Ty} :
      HasType c .bool → HasType t T → HasType e T → HasType (ite c t e) T
  | zero : HasType zero .nat
  | succ {t : Term} : HasType t .nat → HasType (succ t) .nat
  | pred {t : Term} : HasType t .nat → HasType (pred t) .nat
  | iszero {t : Term} : HasType t .nat → HasType (iszero t) .bool

/-- 行き詰まった項．正規形だが値ではない． -/
def Stuck (t : Term) : Prop := Normal t ∧ ¬ Value t

/-! ## 型システムが除外するもの -/

/-- `succ tru`は行き詰まっている． -/
example : Stuck (succ tru) := by
  constructor
  · intro t h
    cases h with
    | succ h => cases h
  · intro h
    cases h with
    | num hn =>
      cases hn with
      | succ hn => cases hn

/-- 演習2-1：`succ tru`には型が付かない． -/
example : ¬ ∃ T, HasType (succ tru) T := by
  -- 演習ここから
  intro ⟨T, h⟩
  cases h with
  | succ h => cases h
  -- 演習ここまで

/-- 型システムは安全側に倒した近似である．
`if true then 0 else false`は値`0`に簡約されるのに，型が付かない． -/
example : ite tru zero fls ⟶* zero ∧ ¬ ∃ T, HasType (ite tru zero fls) T := by
  constructor
  · exact .single .iteTrue
  · intro ⟨T, h⟩
    cases h with
    | ite _ ht he =>
      cases ht
      cases he

/-! ## 型の一意性 -/

/-- 演習2-2：項の型は1つに決まる． -/
theorem type_unique {t : Term} {T T' : Ty} (h : HasType t T) (h' : HasType t T') : T = T' := by
  -- 演習ここから
  induction h generalizing T' with
  | tru => cases h'; rfl
  | fls => cases h'; rfl
  | ite _ _ _ _ iht _ =>
    cases h' with
    | ite _ ht' _ => exact iht ht'
  | zero => cases h'; rfl
  | succ => cases h'; rfl
  | pred => cases h'; rfl
  | iszero => cases h'; rfl
  -- 演習ここまで

/-! ## 標準形補題

型から値の形が分かる．進行の証明で使う．
-/

theorem canonical_bool {v : Term} (hv : Value v) (ht : HasType v .bool) : v = tru ∨ v = fls := by
  cases hv with
  | tru => exact .inl rfl
  | fls => exact .inr rfl
  | num hn => cases hn <;> cases ht

theorem canonical_nat {v : Term} (hv : Value v) (ht : HasType v .nat) : NumVal v := by
  cases hv with
  | tru => cases ht
  | fls => cases ht
  | num hn => exact hn

/-! ## 進行 -/

/-- 演習2-3：型の付く項は，値であるか，1ステップ簡約できる．
ヒント：型付けの導出に関する帰納法を使う．部分項が値の場合は標準形補題で形を絞る． -/
theorem progress {t : Term} {T : Ty} (h : HasType t T) : Value t ∨ ∃ t', t ⟶ t' := by
  -- 演習ここから
  induction h with
  | tru => exact .inl .tru
  | fls => exact .inl .fls
  | zero => exact .inl (.num .zero)
  | ite hc _ _ ihc _ _ =>
    rcases ihc with hv | ⟨c', hs⟩
    · rcases canonical_bool hv hc with rfl | rfl
      · exact .inr ⟨_, .iteTrue⟩
      · exact .inr ⟨_, .iteFalse⟩
    · exact .inr ⟨_, .ite hs⟩
  | succ ht ih =>
    rcases ih with hv | ⟨t', hs⟩
    · exact .inl (.num (.succ (canonical_nat hv ht)))
    · exact .inr ⟨_, .succ hs⟩
  | pred ht ih =>
    rcases ih with hv | ⟨t', hs⟩
    · cases canonical_nat hv ht with
      | zero => exact .inr ⟨_, .predZero⟩
      | succ hn => exact .inr ⟨_, .predSucc hn⟩
    · exact .inr ⟨_, .pred hs⟩
  | iszero ht ih =>
    rcases ih with hv | ⟨t', hs⟩
    · cases canonical_nat hv ht with
      | zero => exact .inr ⟨_, .iszeroZero⟩
      | succ hn => exact .inr ⟨_, .iszeroSucc hn⟩
    · exact .inr ⟨_, .iszero hs⟩
  -- 演習ここまで

/-! ## 保存 -/

/-- 数値には自然数型が付く． -/
theorem numVal_typed {n : Term} (hn : NumVal n) : HasType n .nat := by
  induction hn with
  | zero => exact .zero
  | succ _ ih => exact .succ ih

/-- 演習2-4：簡約しても型は変わらない．
ヒント：型付けの導出に関する帰納法を，`t'`を一般化して行い，各場合で簡約を場合分けする． -/
theorem preservation {t t' : Term} {T : Ty} (h : HasType t T) (hs : t ⟶ t') : HasType t' T := by
  -- 演習ここから
  induction h generalizing t' with
  | tru => cases hs
  | fls => cases hs
  | zero => cases hs
  | ite hc ht he ihc _ _ =>
    cases hs with
    | iteTrue => exact ht
    | iteFalse => exact he
    | ite hs => exact .ite (ihc hs) ht he
  | succ _ ih =>
    cases hs with
    | succ hs => exact .succ (ih hs)
  | pred ht ih =>
    cases hs with
    | predZero => exact .zero
    | predSucc hn => exact numVal_typed hn
    | pred hs => exact .pred (ih hs)
  | iszero _ ih =>
    cases hs with
    | iszeroZero => exact .tru
    | iszeroSucc _ => exact .fls
    | iszero hs => exact .iszero (ih hs)
  -- 演習ここまで

/-! ## 型安全性 -/

/-- 演習2-5：型の付く項は，何ステップ簡約しても行き詰まらない．
ヒント：多ステップ簡約に関する帰納法を使い，進行と保存を組み合わせる． -/
theorem type_safety {t t' : Term} {T : Ty} (h : HasType t T) (hs : t ⟶* t') : ¬ Stuck t' := by
  -- 演習ここから
  induction hs with
  | refl =>
    intro ⟨hn, hv⟩
    rcases progress h with hv' | ⟨u, hu⟩
    · exact hv hv'
    · exact hn u hu
  | step s _ ih => exact ih (preservation h s)
  -- 演習ここまで

end Solutions.Ch2
