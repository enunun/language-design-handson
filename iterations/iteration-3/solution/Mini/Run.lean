import Mini.Eval
import Mini.Parser
import Mini.Pretty

/-!
# 実行

構文解析と評価をつなぎ，コマンド`mini`が表示する文字列を作る．
-/

namespace Mini

/-- 式の大きさ．1ステップ簡約するたびに1以上減るので，簡約列の長さの上限になる． -/
def Term.size : Term → Nat
  | .num _ => 0
  | .add t₁ t₂ => t₁.size + t₂.size + 1
  | .sub t₁ t₂ => t₁.size + t₂.size + 1
  | .mul t₁ t₂ => t₁.size + t₂.size + 1
  | .tru => 0
  | .fls => 0
  | .ite c t e => c.size + t.size + e.size + 1
  | .iszero t => t.size + 1

/-- `t`から始めて，簡約できなくなるまで`step`を繰り返した式の列．`fuel`は繰り返しの上限である． -/
def trace : Nat → Term → List Term
  | 0, t => [t]
  | fuel + 1, t =>
    match step t with
    | some t' => t :: trace fuel t'
    | none => [t]

/-- 簡約できなくなるまで簡約した式． -/
def normalize (t : Term) : Term :=
  (trace t.size t).getLast?.getD t

/-- 文字列`s`を構文解析して評価し，表示する文字列を返す．
評価が行き詰まったときは，行き詰まった式を表示する． -/
def run (s : String) : String :=
  match parse s with
  | .ok t =>
    match eval t with
    | some v => v.pretty
    | none => s!"実行時エラー：評価が行き詰まった({(normalize t).pretty})"
  | .error e => s!"構文エラー：{e}"

/-- 文字列`s`を構文解析し，簡約列を1行に1つずつ表示する文字列を返す．2行目からは先頭に`⟶ `を付ける． -/
def runSteps (s : String) : String :=
  match parse s with
  | .ok t =>
    match trace t.size t with
    | [] => ""
    | t₀ :: ts => "\n".intercalate (t₀.pretty :: ts.map (fun t => s!"⟶ {t.pretty}"))
  | .error e => s!"構文エラー：{e}"

end Mini
