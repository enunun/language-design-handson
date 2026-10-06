import Mini.Run

/-!
# コマンド`mini`

`mini eval <式>`で，式を評価した結果を表示する．
-/

open Mini

def usage : String :=
  "使い方：mini eval <式>"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["eval", s] =>
    IO.println (run s)
    return 0
  | _ =>
    IO.eprintln usage
    return 1
