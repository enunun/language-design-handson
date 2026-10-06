import Mini.Syntax

/-!
# 置換

式の中の変数を，別の式で置き換える．
-/

namespace Mini

/-- `subst x v t`は，式`t`の中の自由な変数`x`を，すべて`v`で置き換えた式である．
`let y = … in u`の`u`と`fun (y : A) => u`の`u`の中では，`y`が`x`と同じなら`x`は束縛されているので置き換えない．
`v`は自由な変数を持たない式(値)で使う．そのため，`v`の中の変数が束縛されてしまうことはない． -/
def subst (x : String) (v : Term) : Term → Term
  | .num n => .num n
  | .add t₁ t₂ => .add (subst x v t₁) (subst x v t₂)
  | .sub t₁ t₂ => .sub (subst x v t₁) (subst x v t₂)
  | .mul t₁ t₂ => .mul (subst x v t₁) (subst x v t₂)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (subst x v c) (subst x v t) (subst x v e)
  | .iszero t => .iszero (subst x v t)
  | .var y => if y = x then v else .var y
  | .let_ y t u => .let_ y (subst x v t) (if y = x then u else subst x v u)
  | .lam y A u => .lam y A (if y = x then u else subst x v u)
  | .app t u => .app (subst x v t) (subst x v u)

end Mini
