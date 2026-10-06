# テストリスト

このIterationで足すテストと，場合を足す既存のテストを並べる．

## 単体テスト

### `Mini.BigStep`(`MiniTest/Unit/BigStepTest.lean`)

- [x] 関数はそれ自身が値である．
- [x] `(fun (x : Nat) => x + 1) 2`の値は`3`である．
- [x] `bigstep_deterministic`に関数と関数適用の場合を足す．

### `Mini.SmallStep`(`MiniTest/Unit/SmallStepTest.lean`)

- [x] 関数適用は，引数を値まで簡約してから，本体の変数を置き換える．
- [x] 関数でない値の適用`1 2`は行き詰まっている．
- [x] 値を表す式についての補題に，関数の場合を足す．
- [x] `step_deterministic`と`bigstep_iff_steps`を関数適用に広げる．

### `Mini.Eval`(`MiniTest/Unit/EvalTest.lean`)

- [x] `step_sound`と`step_complete`を関数適用に広げる．

### `Mini.Typing`(`MiniTest/Unit/TypingTest.lean`)

- [x] `fun (x : Nat) => iszero x`は型`Nat → Bool`を持つ．
- [x] `(fun (x : Nat) => x) 1`は型`Nat`を持つ．
- [x] `(fun (x : Nat) => x) true`には型が付かない．
- [x] `typeOf`は，引数の型が合わない適用と，関数でない式の適用に型エラーを返す．
- [x] `typeOf_sound`，`typeOf_complete`，`weaken`，`subst_typing`を関数と関数適用に広げる．
- [x] 関数型の標準形補題：関数型を持つ値は関数である．
- [x] `progress`と`preservation`を関数適用に広げる．

### `Mini.Pretty`(`MiniTest/Unit/PrettyTest.lean`)

- [x] 関数の表示．
- [x] 関数適用の関数が`fun`なら，かっこを付ける．
- [x] 関数適用は左に結合し，`*`より強く結合する．
- [x] `→`は右に結合する．左の型が関数型なら，かっこを付ける．

## 統合テスト

### `Mini.Run`(`MiniTest/Integration/RunTest.lean`)

- [x] `run "let double = fun (x : Nat) => x + x in double 21"`は`"42"`である．
- [x] 関数を引数として受け取る関数を評価できる．
- [x] 関数の値は，その関数を表す式として表示する．
- [x] 引数の型が合わない適用と，関数でない式の適用は型エラーになる．
- [x] `runCheck`は関数型を表示する．
- [x] `runSteps`は関数適用の簡約列を表示する．
