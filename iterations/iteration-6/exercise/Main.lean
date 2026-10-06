import Mini.Run

/-!
# コマンド`mini`

`mini eval <式>`で式を評価した結果を，`mini steps <式>`で簡約列を，`mini check <式>`で式の型を表示する．
`eval`と`steps`には，`--fuel <数>`で評価するステップ数の上限を指定できる．
-/

open Mini

def usage : String :=
  "使い方：mini eval [--fuel <数>] <式> | mini steps [--fuel <数>] <式> | mini check <式>"

/-- `--fuel <数>`があれば，その数と残りの引数を返す．なければ既定の燃料`1000`を使う． -/
def parseFuel : List String → Option (Nat × List String)
  | "--fuel" :: n :: rest => n.toNat?.map (·, rest)
  | rest => some (1000, rest)

def main (args : List String) : IO UInt32 := do
  match args with
  | "eval" :: rest =>
    match parseFuel rest with
    | some (fuel, [s]) =>
      IO.println (run s fuel)
      return 0
    | _ =>
      IO.eprintln usage
      return 1
  | "steps" :: rest =>
    match parseFuel rest with
    | some (fuel, [s]) =>
      IO.println (runSteps s fuel)
      return 0
    | _ =>
      IO.eprintln usage
      return 1
  | ["check", s] =>
    IO.println (runCheck s)
    return 0
  | _ =>
    IO.eprintln usage
    return 1
