# テストリスト

このIterationで足すテストと，場合を足す既存のテストを並べる．
組の規則は，成分を左から順に値まで評価する設計(先行評価)で確かめる．

## 単体テスト

### `Mini.BigStep`(`MiniTest/Unit/BigStepTest.lean`)

- [x] `(1 + 2, true)`の値は`(3, true)`である．
- [x] `fst (1 + 2, true)`の値は`3`である．
- [x] 2つ目の成分に値がなければ，`fst`にも値がない．
- [x] 組でない値からは，成分を取り出せない．
- [x] `bigstep_deterministic`に組と射影の場合を足す．

### `Mini.SmallStep`(`MiniTest/Unit/SmallStepTest.lean`)

- [x] 値を表す式の組は，値を表す式である．
- [x] 組は左の成分から簡約する．
- [x] 組の成分がすべて値になるまで，成分を取り出さない．
- [x] 組でない値の射影`fst 1`は行き詰まっている．
- [x] 値を表す式についての補題を，組に広げる．値が再帰的になるので，`cases`を帰納法に変える．
- [x] `step_deterministic`と`bigstep_iff_steps`を組と射影に広げる．

### `Mini.Eval`(`MiniTest/Unit/EvalTest.lean`)

- [x] 組の値は，成分の値の組である．
- [x] 値を表す組は，`step`で簡約できない．
- [x] `step_sound`と`step_complete`を組と射影に広げる．

### `Mini.Typing`(`MiniTest/Unit/TypingTest.lean`)

- [x] `(1, true)`は型`Nat × Bool`を持つ．
- [x] `fun (p : Nat × Bool) => if snd p then fst p else 0`は型`Nat × Bool → Nat`を持つ．
- [x] `fst 1`には型が付かない．`typeOf`は，組でない式の射影に型エラーを返す．
- [x] `typeOf_sound`，`typeOf_complete`，`weaken`，`subst_typing`を組と射影に広げる．
- [x] 組の型の標準形補題：組の型を持つ値は，値の組である．
- [x] `progress`と`preservation`を組と射影に広げる．

### `Mini.Pretty`(`MiniTest/Unit/PrettyTest.lean`)

- [x] 組はいつもかっこで囲む．
- [x] `fst`と`snd`は関数適用と同じ強さで結合する．
- [x] 組の値の表示．
- [x] `×`は`→`より強く結合し，右に結合する．

## 統合テスト

### `Mini.Run`(`MiniTest/Integration/RunTest.lean`)

- [x] `run "fst (1 + 2, true)"`は`"3"`である．
- [x] 組の値は，成分の値の組として表示する．
- [x] 組を受け取って組を返す関数を評価できる．
- [x] 組でない式の射影は型エラーになる．
- [x] `runCheck`は組の型を表示する．`×`は`*`とも書ける．
- [x] `runSteps`は，組の成分を左から簡約してから成分を取り出す簡約列を表示する．
