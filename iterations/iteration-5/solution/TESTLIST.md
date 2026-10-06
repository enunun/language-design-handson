# テストリスト

このIterationで足すテストと，主張や期待値を変える既存のテストを並べる．

## 単体テスト

### `Mini.Subst`(`MiniTest/Unit/SubstTest.lean`)

- [x] 自由な変数`x`を置き換え，ほかの変数は残す．
- [x] `x`を束縛する`let`の本体の中は置き換えない(束縛する式の中は置き換える)．
- [x] 別の名前を束縛する`let`の本体の中は置き換える．

### `Mini.BigStep`(`MiniTest/Unit/BigStepTest.lean`)

- [x] `let x = 1 + 2 in x * x`の値は`9`である．
- [x] 自由な変数には値がない．
- [x] `bigstep_deterministic`：大ステップ意味論は決定的である(導出についての帰納法で直接証明する)．
- [x] 等価性の定理(`add_comm`，`add_assoc`，`mul_comm`，`mul_assoc`，`mul_one`，`mul_one_not_equiv`，`sub_not_assoc`)を，`EvalTest`から移し，大ステップ意味論で述べ直す．

### `Mini.SmallStep`(`MiniTest/Unit/SmallStepTest.lean`)

- [x] `let`は，束縛する式を値まで簡約してから，本体の変数を置き換える．
- [x] 自由な変数は行き詰まっている．
- [x] 値を表す式についての補題(`IsValue`と`Value.toTerm`と`Term.toValue?`の関係)．
- [x] `step_deterministic`と`bigstep_iff_steps`を`let`に広げる．

### `Mini.Eval`(`MiniTest/Unit/EvalTest.lean`)

- [x] `eval`の具体例に燃料の引数を足し，期待値を`.ok v`の形に変える．
- [x] `eval`は行き詰まった式を返す(`1 + true`，自由な変数)．
- [x] 燃料が足りないと燃料切れを返し，足りれば値を返す．
- [x] `step`の具体例と`step_sound`，`step_complete`を`let`と変数に広げる．
- [x] `eval_sound`：燃料$k$で`eval`が値$v$を返すならば，$t \Downarrow v$である．
- [x] `eval_complete`：$t \Downarrow v$ならば，ある燃料$k$で`eval`は$v$を返す．
- [x] `eval_stuck`：`eval`が行き詰まったと返すなら，その式に簡約され，その式は行き詰まっている．

### `Mini.Typing`(`MiniTest/Unit/TypingTest.lean`)

- [x] 型付けの具体例を空の文脈`[]`で書き直す．
- [x] `let`の本体は，束縛した変数の型を文脈に加えて型を付ける．
- [x] 文脈にない変数には型が付かない．
- [x] `typeOf`は定義されていない変数に型エラーを返す．
- [x] 内側の`let`が外側の束縛を隠す．
- [x] `typeOf_sound`，`typeOf_complete`，`type_unique`を文脈つきに広げる．
- [x] `weaken`：文脈を広げても型付けは保たれる．
- [x] `subst_typing`：置換補題．
- [x] `progress`，`preservation`，`type_safety`を，空の文脈の式について述べ直し，`let`に広げる．
- [x] `eval_of_hasType`を`eval_not_stuck`(型の付く式の評価は行き詰まらない)に変える．

### `Mini.Pretty`(`MiniTest/Unit/PrettyTest.lean`)

- [x] `let`の表示．演算子の左に置くときは，かっこを付ける．

## 統合テスト

### `Mini.Run`(`MiniTest/Integration/RunTest.lean`)

- [x] `run "let x = 1 + 2 in x * x"`は`"9"`である．
- [x] 内側の`let`が外側の`x`を隠す．
- [x] `run "let x = 1 in y"`は型エラーになる．
- [x] `run "1 + x"`の期待値を，構文エラーから型エラーに変える．
- [x] 燃料が足りないと燃料切れを表示し，足りれば値を表示する．
- [x] `run_of_eval`と`run_well_typed`を，燃料のある評価器に合わせて述べ直す．`run_well_typed`は，値が表示されるか燃料切れになることを示す．
- [x] `runCheck`は`let`を含む式の型を表示する．
- [x] `runSteps`は`let`の簡約列を表示する．表示するステップ数の上限を指定できる．
