# テストリスト

このIterationで足すテストと，期待値を変える既存のテストを並べる．

## 単体テスト

### `Mini.Eval`(`MiniTest/Unit/EvalTest.lean`)

- [x] 既存の`eval`の具体例の期待値を，`n`から`some (.num n)`に変える．
- [x] `true`の値は$\mathrm{true}$である．
- [x] `if true then 1 else 2`の値は`1`，`if false then 1 else 2`の値は`2`である．
- [x] `iszero (2 - 2)`の値は$\mathrm{true}$，`iszero 5`の値は$\mathrm{false}$である．
- [x] `1 + true`は評価が行き詰まる(`none`)．
- [x] `if 1 then 2 else 3`は評価が行き詰まる．
- [x] `if true then 1 else (1 + true)`の値は`1`である(選ばれない枝を評価しない)．
- [x] 交換法則と結合法則の定理の証明を，値が数でない場合も扱うように直す．
- [x] `eval_mul_one`の主張を「$t$の値が数なら，$t * 1$の値もその数である」に変える．
- [x] `eval_mul_one_not_equiv`：$t * 1$と$t$は等価とは限らない．
- [x] `eval_sound`，`eval_complete`，`eval_deterministic`の主張を，値`v`を使う形に変える．
- [x] `step`は`if`の条件を簡約し，条件が`true`なら`then`の枝を返す．
- [x] `step`は`1 + true`に`none`を返す．
- [x] `step_sound`，`step_complete`を新しい規則に広げる．

### `Mini.BigStep`(`MiniTest/Unit/BigStepTest.lean`)

- [x] 既存の導出の例の値を，`n`から`.num n`に変える．
- [x] `if true then 1 else 2`と`if iszero 0 then 1 else 2`の導出．
- [x] `iszero 5`の値が$\mathrm{false}$であることの導出．
- [x] `1 + true`には値がない．

### `Mini.SmallStep`(`MiniTest/Unit/SmallStepTest.lean`)

- [x] `if`は条件を先に簡約する．条件が真偽値になると枝を選ぶ．
- [x] `iszero 5`は`false`に簡約される．
- [x] 条件が真偽値になるまで，`if`の枝は簡約しない．
- [x] `1 + true`は行き詰まっている(`Stuck`)．
- [x] `value_normal`：値を表す式は正規形である．
- [x] `step_deterministic`を新しい規則に広げる．
- [x] `stepEager_not_deterministic`：`then`の枝を先に簡約してもよいとすると，決定性が成り立たない．
- [x] `bigstep_iff_steps`の主張を，$t \Downarrow v$と$t \longrightarrow^{*} v$の同値に変える．

### `Mini.Pretty`(`MiniTest/Unit/PrettyTest.lean`)

- [x] `if`と`iszero`を含む式の表示．
- [x] `if`を演算子の左に置くときは，かっこを付ける．
- [x] `iszero 0 * 2`は，かっこを付けずに表示する．
- [x] 値の表示(`3`，`false`)．

## 統合テスト

### `Mini.Run`(`MiniTest/Integration/RunTest.lean`)

- [x] `run "if iszero (2 - 2) then 10 else 20"`は`"10"`である．
- [x] `run "iszero 3"`は`"false"`である．
- [x] `run "1 + true"`は，行き詰まった式`1 + true`を表示する実行時エラーになる．
- [x] `run "(1 + 2) * iszero 0"`は，行き詰まるまで簡約した式`3 * true`を表示する．
- [x] `run "if 1 then 2 else 3"`は実行時エラーになる．
- [x] `run "1 + x"`は構文エラーになる．
- [x] `run_of_parse`を`run_of_eval`(構文解析と評価に成功したら，値を表示する)に変える．
- [x] `runSteps`は`if`の簡約列を表示する．
- [x] `runSteps "1 + true"`は1行だけ表示する．
