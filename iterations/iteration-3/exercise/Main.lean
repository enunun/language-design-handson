import Mini.Run

/-!
# コマンド`mini`

`mini eval <式>`で式を評価した結果を，`mini steps <式>`で簡約列を表示する．
-/

open Mini

def usage : String :=
  "使い方：mini eval <式> | mini steps <式>"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["eval", s] =>
    IO.println (run s)
    return 0
  | ["steps", s] =>
    IO.println (runSteps s)
    return 0
  | _ =>
    IO.eprintln usage
    return 1
