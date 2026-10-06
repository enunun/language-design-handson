import Mini.Eval
import Mini.Parser
import Mini.Pretty
import Mini.Typing

/-!
# 実行

構文解析と評価をつなぎ，コマンド`mini`が表示する文字列を作る．
-/

namespace Mini

/-- `t`から始めて，簡約できなくなるまで`step`を繰り返した式の列．`fuel`は繰り返しの上限である． -/
def trace : Nat → Term → List Term
  | 0, t => [t]
  | fuel + 1, t =>
    match step t with
    | some t' => t :: trace fuel t'
    | none => [t]

/-- 型エラーを文字列にする． -/
def TypeError.message : TypeError → String
  | .mismatch what expected actual => s!"{what}の型が合わない(期待：{expected.pretty}，実際：{actual.pretty})"
  | .branches thenTy elseTy => s!"ifの2つの枝の型が合わない(then：{thenTy.pretty}，else：{elseTy.pretty})"
  | .unbound x => s!"変数{x}が定義されていない"
  | .notFunction T => s!"関数でない式を適用している(型：{T.pretty})"

/-- 評価が値に着かなかった理由を文字列にする．`fuel`は使った燃料である． -/
def EvalError.message (fuel : Nat) : EvalError → String
  | .stuck t => s!"実行時エラー：評価が行き詰まった({t.pretty})"
  | .outOfFuel => s!"燃料切れ：{fuel}ステップで評価が終わらなかった"

/-- 文字列`s`を構文解析し，型を検査してから評価し，表示する文字列を返す．
型が付かない式は評価しない．`fuel`は評価するステップ数の上限である． -/
def run (s : String) (fuel : Nat := 1000) : String :=
  match parse s with
  | .ok t =>
    match typeOf [] t with
    | .ok _ =>
      match eval fuel t with
      | .ok v => v.pretty
      | .error err => err.message fuel
    | .error err => s!"型エラー：{err.message}"
  | .error e => s!"構文エラー：{e}"

/-- 文字列`s`を構文解析して型を検査し，型を表示する文字列を返す． -/
def runCheck (s : String) : String :=
  match parse s with
  | .ok t =>
    match typeOf [] t with
    | .ok T => T.pretty
    | .error err => s!"型エラー：{err.message}"
  | .error e => s!"構文エラー：{e}"

/-- 文字列`s`を構文解析し，簡約列を1行に1つずつ表示する文字列を返す．2行目からは先頭に`⟶ `を付ける．
`fuel`は表示するステップ数の上限である． -/
def runSteps (s : String) (fuel : Nat := 1000) : String :=
  match parse s with
  | .ok t =>
    match trace fuel t with
    | [] => ""
    | t₀ :: ts => "\n".intercalate (t₀.pretty :: ts.map (fun t => s!"⟶ {t.pretty}"))
  | .error e => s!"構文エラー：{e}"

end Mini
