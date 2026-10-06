# テストリスト

このIterationで足すテストを並べる．
Iteration 1までのテストは，主張を変えずにそのまま残す．

## 単体テスト

### `Mini.SmallStep`(`MiniTest/Unit/SmallStepTest.lean`)

- [x] $(1 + 2) * (3 + 4) \longrightarrow 3 * (3 + 4)$である(左の部分式から簡約する)．
- [x] $3 * (3 + 4) \longrightarrow 3 * 7$である(左が数になったら右を簡約する)．
- [x] $3 * 7 \longrightarrow 21$である．
- [x] $(1 + 2) + (3 + 4) \longrightarrow (1 + 2) + 7$ではない(左が数になるまで右は簡約しない)．
- [x] $(1 + 2) * (3 + 4) \longrightarrow^{*} 21$である．
- [x] `num_normal`：数はそれ以上簡約できない．
- [x] `step_deterministic`：1ステップで簡約した結果は1つに決まる．
- [x] `bigstep_iff_steps`：$t \Downarrow n$と$t \longrightarrow^{*} n$は同値である．

### `Mini.Eval`(`MiniTest/Unit/EvalTest.lean`)

- [x] `step`は$(1 + 2) * (3 + 4)$を$3 * (3 + 4)$にする．
- [x] `step`は$3 * (3 + 4)$を$3 * 7$にする．
- [x] `step`は数に`none`を返す．
- [x] `step_sound`：`step t = some t'`ならば$t \longrightarrow t'$である．
- [x] `step_complete`：$t \longrightarrow t'$ならば`step t = some t'`である．

### `Mini.Pretty`(`MiniTest/Unit/PrettyTest.lean`)

- [x] 数`21`は`"21"`と表示する．
- [x] `1 + 2 * 3`を表す式は`"1 + 2 * 3"`と表示する(かっこは要らない)．
- [x] `(1 + 2) * (3 + 4)`を表す式は，かっこを付けて表示する．
- [x] `10 - 2 - 3`(左結合)を表す式は，かっこを付けずに表示する．
- [x] `10 - (2 - 3)`を表す式は，右にかっこを付けて表示する．

## 統合テスト

### `Mini.Run`(`MiniTest/Integration/RunTest.lean`)

- [x] `runSteps "(1 + 2) * (3 + 4)"`は4行の簡約列を表示する．
- [x] `runSteps "10 - 2 - 3"`は左の引き算から簡約する．
- [x] `runSteps "7"`は1行だけ表示する．
- [x] `runSteps "1 +"`は構文エラーを表示する．
