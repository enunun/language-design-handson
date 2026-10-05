import Solutions.Ch1Arith

/-!
# 第3章 大ステップ意味論と小ステップ意味論の一致

同じ言語の意味を，別の流儀で定義することもできる．
大ステップ意味論は，「項`t`を評価すると値`v`になる」という関係`t ⇓ v`を，
評価の途中経過を書かずに直接定義する．

インタプリタの実装に近いのは大ステップ意味論，証明で扱いやすいのは小ステップ意味論である．
2つを両方定義したなら，それらが同じ意味を与えていることを確かめておく必要がある．
この章の目標は次の定理である．

* `t ⇓ v`であることと，`t ⟶* v`かつ`v`が値であることは同値である(`eval_iff_steps`)．
-/

namespace Solutions.Ch3

open Solutions.Ch1
open Term

/-! ## 大ステップ意味論 -/

/-- 評価関係`t ⇓ v`． -/
inductive Eval : Term → Term → Prop where
  | value {v : Term} : Value v → Eval v v
  | iteTrue {c t e v : Term} : Eval c tru → Eval t v → Eval (ite c t e) v
  | iteFalse {c t e v : Term} : Eval c fls → Eval e v → Eval (ite c t e) v
  | succ {t n : Term} : NumVal n → Eval t n → Eval (succ t) (succ n)
  | predZero {t : Term} : Eval t zero → Eval (pred t) zero
  | predSucc {t n : Term} : NumVal n → Eval t (succ n) → Eval (pred t) n
  | iszeroZero {t : Term} : Eval t zero → Eval (iszero t) tru
  | iszeroSucc {t n : Term} : NumVal n → Eval t (succ n) → Eval (iszero t) fls

@[inherit_doc] infix:50 " ⇓ " => Eval

/-! ## 評価結果の性質 -/

/-- 評価の結果は値である． -/
theorem eval_value {t v : Term} (h : t ⇓ v) : Value v := by
  induction h with
  | value hv => exact hv
  | iteTrue _ _ _ ih => exact ih
  | iteFalse _ _ _ ih => exact ih
  | succ hn _ _ => exact .num (.succ hn)
  | predZero _ _ => exact .num .zero
  | predSucc hn _ _ => exact .num hn
  | iszeroZero _ _ => exact .tru
  | iszeroSucc _ _ _ => exact .fls

/-- 値を評価すると，その値自身になる． -/
theorem eval_of_value {v w : Term} (hv : Value v) (h : v ⇓ w) : w = v := by
  induction h with
  | value => rfl
  | iteTrue => cases hv with | num hn => cases hn
  | iteFalse => cases hv with | num hn => cases hn
  | succ _ _ ih =>
    cases hv with
    | num hn =>
      cases hn with
      | succ hn => rw [ih (.num hn)]
  | predZero => cases hv with | num hn => cases hn
  | predSucc => cases hv with | num hn => cases hn
  | iszeroZero => cases hv with | num hn => cases hn
  | iszeroSucc => cases hv with | num hn => cases hn

/-! ## 多ステップ簡約の合同性

部分項の多ステップ簡約を，外側の項の多ステップ簡約に持ち上げる補題．
-/

theorem Steps.ite {c c' t e : Term} (h : c ⟶* c') : ite c t e ⟶* ite c' t e := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.ite s) ih

theorem Steps.succ {t t' : Term} (h : t ⟶* t') : succ t ⟶* succ t' := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.succ s) ih

theorem Steps.pred {t t' : Term} (h : t ⟶* t') : pred t ⟶* pred t' := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.pred s) ih

theorem Steps.iszero {t t' : Term} (h : t ⟶* t') : iszero t ⟶* iszero t' := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.iszero s) ih

/-! ## 大ステップから小ステップへ -/

/-- 演習3-1：`t ⇓ v`ならば`t ⟶* v`である．
ヒント：評価の導出に関する帰納法を使い，合同性の補題と`Steps.trans`で簡約列をつなぐ． -/
theorem eval_steps {t v : Term} (h : t ⇓ v) : t ⟶* v := by
  -- 演習ここから
  induction h with
  | value => exact .refl
  | iteTrue _ _ ihc iht => exact (Steps.ite ihc).trans (.step .iteTrue iht)
  | iteFalse _ _ ihc ihe => exact (Steps.ite ihc).trans (.step .iteFalse ihe)
  | succ _ _ ih => exact Steps.succ ih
  | predZero _ ih => exact (Steps.pred ih).trans (.single .predZero)
  | predSucc hn _ ih => exact (Steps.pred ih).trans (.single (.predSucc hn))
  | iszeroZero _ ih => exact (Steps.iszero ih).trans (.single .iszeroZero)
  | iszeroSucc hn _ ih => exact (Steps.iszero ih).trans (.single (.iszeroSucc hn))
  -- 演習ここまで

/-! ## 小ステップから大ステップへ -/

/-- 値でない項の評価は`Eval.value`では終わらない，という場合分けを省くための補題． -/
theorem not_value_ite {c t e : Term} : ¬ Value (ite c t e) := by
  intro h; cases h with | num hn => cases hn

theorem not_value_pred {t : Term} : ¬ Value (pred t) := by
  intro h; cases h with | num hn => cases hn

theorem not_value_iszero {t : Term} : ¬ Value (iszero t) := by
  intro h; cases h with | num hn => cases hn

/-- 演習3-2：1ステップ簡約した後の項が`v`に評価されるなら，簡約前の項も`v`に評価される．
ヒント：`hs`に関する帰納法を，`v`を一般化して行い，各場合で`h`を場合分けする．
`h`が`Eval.value`の場合は，`not_value_ite`などで矛盾を導くか，`eval_of_value`で`v`を特定する． -/
theorem step_eval {t t' v : Term} (hs : t ⟶ t') (h : t' ⇓ v) : t ⇓ v := by
  -- 演習ここから
  induction hs generalizing v with
  | iteTrue => exact .iteTrue (.value .tru) h
  | iteFalse => exact .iteFalse (.value .fls) h
  | ite _ ih =>
    cases h with
    | value hv => exact absurd hv not_value_ite
    | iteTrue hc ht => exact .iteTrue (ih hc) ht
    | iteFalse hc he => exact .iteFalse (ih hc) he
  | succ _ ih =>
    cases h with
    | value hv =>
      cases hv with
      | num hn =>
        cases hn with
        | succ hn => exact .succ hn (ih (.value (.num hn)))
    | succ hn h => exact .succ hn (ih h)
  | predZero =>
    rw [eval_of_value (.num .zero) h]
    exact .predZero (.value (.num .zero))
  | predSucc hn =>
    rw [eval_of_value (.num hn) h]
    exact .predSucc hn (.value (.num (.succ hn)))
  | pred _ ih =>
    cases h with
    | value hv => exact absurd hv not_value_pred
    | predZero h => exact .predZero (ih h)
    | predSucc hn h => exact .predSucc hn (ih h)
  | iszeroZero =>
    rw [eval_of_value .tru h]
    exact .iszeroZero (.value (.num .zero))
  | iszeroSucc hn =>
    rw [eval_of_value .fls h]
    exact .iszeroSucc hn (.value (.num (.succ hn)))
  | iszero _ ih =>
    cases h with
    | value hv => exact absurd hv not_value_iszero
    | iszeroZero h => exact .iszeroZero (ih h)
    | iszeroSucc hn h => exact .iszeroSucc hn (ih h)
  -- 演習ここまで

/-- 演習3-3：`t ⟶* v`で`v`が値ならば`t ⇓ v`である． -/
theorem steps_eval {t v : Term} (hs : t ⟶* v) (hv : Value v) : t ⇓ v := by
  -- 演習ここから
  induction hs with
  | refl => exact .value hv
  | step s _ ih => exact step_eval s (ih hv)
  -- 演習ここまで

/-! ## 2つの意味論の一致 -/

theorem eval_iff_steps {t v : Term} : t ⇓ v ↔ t ⟶* v ∧ Value v :=
  ⟨fun h => ⟨eval_steps h, eval_value h⟩, fun ⟨hs, hv⟩ => steps_eval hs hv⟩

/-- 一致の帰結として，大ステップ意味論も決定的である．
小ステップ意味論の決定性(`steps_normal_unique`)から直ちに従う． -/
theorem eval_deterministic {t v v' : Term} (h : t ⇓ v) (h' : t ⇓ v') : v = v' :=
  steps_normal_unique (eval_steps h) (value_normal (eval_value h))
    (eval_steps h') (value_normal (eval_value h'))

end Solutions.Ch3
