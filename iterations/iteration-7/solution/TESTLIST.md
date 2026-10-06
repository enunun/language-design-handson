# テストリスト

このIterationで足すテストと，場合を足す既存のテストを並べる．

## 単体テスト

### `Mini.BigStep`(`MiniTest/Unit/BigStepTest.lean`)

- [x] 再帰関数はそれ自身が値である．
- [x] `fact 1`の値は`1`である．
- [x] `loop 0`には値がない．
- [x] `bigstep_deterministic`に再帰関数の場合を足す．

### `Mini.SmallStep`(`MiniTest/Unit/SmallStepTest.lean`)

- [x] 再帰関数の適用は，引数の変数と関数の名前の両方を置き換える．`loop 0`は1ステップで自分自身に戻る．
- [x] `loop 0`から簡約して着く式は，`loop 0`だけである．
- [x] 値を表す式についての補題に，再帰関数の場合を足す．
- [x] `step_deterministic`と`bigstep_iff_steps`を再帰関数に広げる．

### `Mini.Eval`(`MiniTest/Unit/EvalTest.lean`)

- [x] `fact 3`の値は`6`である．
- [x] `loop 0`は，どれだけ燃料を与えても燃料切れになる．
- [x] `step`は`loop 0`を`loop 0`に簡約する．
- [x] `step_sound`と`step_complete`を再帰関数に広げる．

### `Mini.Typing`(`MiniTest/Unit/TypingTest.lean`)

- [x] `fact`は型`Nat → Nat`を持つ．
- [x] 評価が終わらない`loop 0`にも型が付く．
- [x] `typeOf`は，本体の型が注釈した結果の型と合わない再帰関数に型エラーを返す．
- [x] `typeOf_sound`，`typeOf_complete`，`weaken`，`subst_typing`を再帰関数に広げる．
- [x] 関数型の標準形補題：関数型を持つ値は，関数か再帰関数である．
- [x] `progress`と`preservation`を再帰関数の適用に広げる．

### `Mini.Pretty`(`MiniTest/Unit/PrettyTest.lean`)

- [x] 再帰関数の表示．
- [x] 関数適用の関数が`fix`なら，かっこを付ける．

## 統合テスト

### `Mini.Run`(`MiniTest/Integration/RunTest.lean`)

- [x] `run "(fix fact (n : Nat) : Nat => if iszero n then 1 else n * fact (n - 1)) 5"`は`"120"`である．
- [x] 評価が終わらない式は，燃料切れになる．
- [x] 本体の型が合わない再帰関数は型エラーになる．
- [x] `runCheck`は再帰関数の型を表示する．
- [x] `runSteps`は，`loop 0`が自分自身に簡約され続けることを表示する．
