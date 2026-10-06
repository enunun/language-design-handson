# テストリスト

このIterationで足すテストと，期待値を変える既存のテストを並べる．

## 単体テスト

### `Mini.Typing`(`MiniTest/Unit/TypingTest.lean`)

- [x] $1 + 2 : \mathsf{Nat}$を導出できる．
- [x] $\mathsf{if}\ \mathsf{iszero}\ 0\ \mathsf{then}\ 1\ \mathsf{else}\ 2 : \mathsf{Nat}$を導出できる．
- [x] $1 + \mathsf{true}$には型が付かない．
- [x] $\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{false}$は値に評価されるが，型が付かない．
- [x] `typeOf`は`if iszero 0 then 1 else 2`に`Nat`を返す．
- [x] `typeOf`は`1 + true`に，`+`の右辺の型が合わないという型エラーを返す．
- [x] `typeOf`は，条件が数の`if`に型エラーを返す．
- [x] `typeOf`は，枝の型が異なる`if`に型エラーを返す．
- [x] `typeOf_sound`：`typeOf t = .ok T`ならば$t : T$である．
- [x] `typeOf_complete`：$t : T$ならば`typeOf t = .ok T`である．
- [x] `type_unique`：式の型は1つに決まる．
- [x] `progress`：型の付く式は，値であるか，1ステップ簡約できる．
- [x] `preservation`：型の付く式を1ステップ簡約しても，型は変わらない．
- [x] `type_safety`：型の付く式は，何ステップ簡約しても行き詰まらない．
- [x] `eval_of_hasType`：型の付く式は必ず値に評価され，値の型は式の型と同じである．

### `Mini.Pretty`(`MiniTest/Unit/PrettyTest.lean`)

- [x] 型`Nat`と`Bool`の表示．

## 統合テスト

### `Mini.Run`(`MiniTest/Integration/RunTest.lean`)

- [x] `run "1 + true"`の期待値を，実行時エラーから型エラーに変える．
- [x] `run "(1 + 2) * iszero 0"`と`run "if 1 then 2 else 3"`の期待値を，型エラーに変える．
- [x] `run "if true then 0 else false"`は型エラーになる(評価すれば値になる式でも評価しない)．
- [x] `runCheck`は，`if iszero 0 then 1 else 2`に`Nat`を，`iszero (1 + 2)`に`Bool`を表示する．
- [x] `runCheck "1 + true"`は型エラーを，`runCheck "1 +"`は構文エラーを表示する．
- [x] `run_of_eval`の前提に，型検査に成功したことを足す．
- [x] `run_well_typed`：型検査を通った文字列を`run`すると，実行時エラーにならず，値が表示される．
