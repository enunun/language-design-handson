# テストリスト

このIterationで足すテストを並べる．
Iteration 0のテストは，主張を変えずにそのまま残す．

## 単体テスト

### `Mini.BigStep`(`MiniTest/Unit/BigStepTest.lean`)

- [x] $3 \Downarrow 3$を導出できる．
- [x] $1 + 2 \Downarrow 3$を導出できる．
- [x] $1 + 2 * 3 \Downarrow 7$を導出できる(規則を組み合わせた導出木)．
- [x] $2 - 5 \Downarrow 0$を導出できる．
- [x] $1 + 2 \Downarrow 4$は導出できない．

### `Mini.Eval`(`MiniTest/Unit/EvalTest.lean`)

- [x] `eval_sound`：`eval t = n`ならば$t \Downarrow n$である．
- [x] `eval_complete`：$t \Downarrow n$ならば`eval t = n`である．
- [x] `eval_deterministic`：$t \Downarrow n$かつ$t \Downarrow m$ならば$n = m$である．

## 統合テスト

利用者から見える振る舞いは変わらないので，統合テストは足さない．
