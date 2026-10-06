# Iteration 5 解説

演習の各手順の解説である．
見出しの番号は，演習の`docs/iteration-5.md`の手順に対応する．

## 5-1 準備

演習のパッケージはIteration 4の解答と同じなので，テストはすべて通る．

## 5-2 構文と概念

課題1の`#eval collatzFuel 100 27`の結果は`none`である．
27から1に着くまでには111回の操作が要り，燃料100では足りない．
燃料を200にすると`some 111`になる．

課題3の答えは$\mathsf{let}\ x = 3 + 1\ \mathsf{in}\ x * y$である．
束縛する式$x + 1$の$x$は外側の$x$なので置き換える．
本体の$x$は内側の$\mathsf{let}$に束縛されているので置き換えない．

## 5-3 テストリスト

模範解答は`TESTLIST.md`にある．

- 置換の具体例は，自由な変数，同じ名前の`let`，別の名前の`let`の3つを挙げた．
- `let`の具体例は，評価，簡約，型付け，型検査器，`run`のそれぞれで挙げた．内側の`let`が外側の束縛を隠す例は，型検査器と`run`で確かめた．
- 等価性の定理は，`eval`が燃料と行き詰まった式を返すようになったので，`eval`の等式のままでは成り立たない．たとえば`1 + true`と`true + 1`は，行き詰まった式が異なる．大ステップ意味論の同値として述べ直した．
- 大ステップ意味論の決定性は，`eval`の完全性からは導けなくなったので，導出についての帰納法で直接証明した．
- 「型の付く式は必ず値になる」は，燃料が足りなければ成り立たない．「型の付く式の評価は行き詰まらない」と述べ直した．
- 型安全性の証明のために，弱化と置換補題を挙げた．

## 5-4 設計書

### 言語仕様書

- `## 構文`に変数と`let`を足し，束縛，自由な変数，閉じた式の説明を書いた．
- `## 値`の下に`### 値を表す式\`IsValue\``を立て，3つの規則を書いた．
- `## 意味`に`### 置換`を立て，変数と`let`の場合を等式で書いた．置換する式を閉じた式に限ることも書いた．
- 大ステップ意味論に`let_`の規則を，小ステップ意味論に`letL`と`letV`の規則を足した．規則名の`_`は，TeXでは`\_`と書く．
- `### 評価器`を立て，燃料つきの評価器の振る舞いを書いた．
- `## 型`に型付け文脈の説明を足し，型付け規則を$\Gamma \vdash t : T$の形に書き直した．
- `## 性質`の等価性の定理の名前を，大ステップ意味論で述べ直したものに変えた．

### モジュール依存図

`Mini.Subst`は`Mini.Syntax`だけに依存する．
置換は，大ステップ意味論，小ステップ意味論，`step`が使うので，`Mini.BigStep`，`Mini.SmallStep`，`Mini.Eval`から`Mini.Subst`への矢印を足した．

## 5-5 テストファーストの実装

### 構文と構文解析器と置換

`subst`は，変数と`let`の場合だけ名前を比べる．

```lean
  | .var y => if y = x then v else .var y
  | .let_ y t u => .let_ y (subst x v t) (if y = x then u else subst x v u)
```

具体例は`decide`で証明できる．
`Term`の`DecidableEq`は，`String`の等しさの判定を使う．

### 意味論

`Step`の`let`の規則は，前提に`IsValue v`をとる．

```lean
  | letL {x : String} {t t' u : Term} : Step t t' → Step (.let_ x t u) (.let_ x t' u)
  | letV {x : String} {v u : Term} : IsValue v → Step (.let_ x v u) (subst x v u)
```

決定性の証明では，`letL`と`letV`の組み合わせを，値を表す式は簡約できないという補題`isValue_normal`で閉じた．

大ステップ意味論の決定性は，`h₁`についての帰納法を`w`を一般化して行った．
`let_`の場合，束縛する式の値が一致することを帰納法の仮定で示し，`cases`で置き換えてから本体の帰納法の仮定を使う．

```lean
  | let_ _ _ ih₁ ih₂ =>
    cases h₂ with
    | let_ h₁' h₂' =>
      cases ih₁ h₁'
      exact ih₂ h₂'
```

等価性の定理は，導出を分解して組み立て直す形で証明した．

```lean
theorem add_comm {t₁ t₂ : Term} {v : Value} : Term.add t₁ t₂ ⇓ v ↔ Term.add t₂ t₁ ⇓ v := by
  constructor
  · intro h
    cases h with
    | add h₁ h₂ => rw [Nat.add_comm]; exact .add h₂ h₁
  · intro h
    cases h with
    | add h₁ h₂ => rw [Nat.add_comm]; exact .add h₂ h₁
```

### 評価器

`eval`を作り直すと，Iteration 4の具体例は型が合わなくなる．

```text
error: MiniTest/Unit/EvalTest.lean:17:16: Unknown constant `Nat.num`

Note: Inferred this name from the expected resulting type of `.num`:
  Nat
```

`eval`の第1引数が燃料になったので，`.num 3`が燃料の`Nat`として読まれている．
具体例を`eval 100 (.num 3) = .ok (.num 3)`の形に直し，`rfl`で証明した．

```lean
def eval : Nat → Term → Except EvalError Value
  | 0, _ => .error .outOfFuel
  | fuel + 1, t =>
    match t.toValue? with
    | some v => .ok v
    | none =>
      match step t with
      | some t' => eval fuel t'
      | none => .error (.stuck t)
```

健全性は，燃料についての帰納法で，`step_sound`とIteration 2の`step_bigstep`を使って証明した．
完全性は，`bigstep_steps`で簡約列を作り，簡約列についての帰納法で必要な燃料を数えた．
`eval_stuck`は，行き詰まったと報告された式に実際に簡約され，その式が正規形で値でないことを示す．

### 型付け

#### 弱化

「文脈`Γ`の変数がすべて同じ型で文脈`Δ`にもある」を`Included Γ Δ`と定義し，型付けの導出についての帰納法で証明した．
`let_`の場合は，両方の文脈の先頭に同じ変数を足しても`Included`が保たれることを使う．

#### 置換補題

主張を書き，`sorry`で失敗を確かめた．

```text
error: MiniTest/Unit/TypingTest.lean:144:8: declaration uses `sorry`
```

`u`についての帰納法を，文脈`Γ`と型`B`を一般化して行った．
変数の場合，名前が`x`なら置換した式`v`の型付けを弱化で`Γ`に広げ，そうでなければ文脈の`x`を飛ばして型を引く．

```lean
  | var y =>
    cases hu with
    | var hy =>
      by_cases hyx : y = x
      · subst hyx
        simp [Ctx.lookup] at hy
        subst hy
        simp only [subst, ite_true]
        exact weaken hv (fun _ _ h => by simp [Ctx.lookup] at h)
      · simp only [Ctx.lookup, hyx, ite_false] at hy
        simp only [subst, hyx, ite_false]
        exact .var hy
```

`let_ y t u`の場合，`y = x`なら本体は置換しない．
本体の型付けの文脈$(y : T), (x : A), \Gamma$を，弱化で$(y : T), \Gamma$に縮める．
`y ≠ x`なら，文脈の2つの変数の順序を入れ替えてから，本体の帰納法の仮定を使う．

#### 進行と保存

どちらも空の文脈の式について述べ，`generalize hΓ : ([] : Ctx) = Γ at h`の後に帰納法を使った．
進行の変数の場合は，空の文脈に変数がないので矛盾になる．
保存の`letV`の場合は，置換補題をそのまま使う．

```lean
  | let_ h₁ h₂ ih₁ _ =>
    subst hΓ
    cases s with
    | letL s => exact .let_ (ih₁ s rfl) h₂
    | letV _ => exact subst_typing h₂ h₁
```

#### `eval_not_stuck`

`eval_stuck`で行き詰まった式への簡約列を作り，型安全性と矛盾させた．

### `run`と`--fuel`

既存の統合テストのうち，`run "1 + x"`は失敗した．

```text
error: MiniTest/Integration/RunTest.lean:45:51: Tactic `decide` proved that the proposition
  run "1 + x" = "構文エラー：知らない単語がある(x)"
is false
```

`x`が変数として読まれ，型エラーになるからである．
期待値を`型エラー：変数xが定義されていない`に変えた．

`run_well_typed`は，`eval`の結果で場合を分け，行き詰まった場合を`eval_not_stuck`で除いた．

```text
$ lake exe mini eval "let x = 1 + 2 in x * x"
9
$ lake exe mini check "let x = 1 in y"
型エラー：変数yが定義されていない
$ lake exe mini eval --fuel 2 "1 + 2 + 3"
燃料切れ：2ステップで評価が終わらなかった
```

## 5-6 振り返り

1. 既存のテストの述べ直しは，Iteration 3と4よりも多い．評価器の作り直しのように，実装の大きな変更は，テストの主張を見直すきっかけになる．
2. 置換補題の変数の場合で，置換した式`v`の型付けを，空の文脈から`Γ`に弱化で広げた．`v`が自由な変数を持つと，`Γ`の中で別の型を持つ変数と重なり，この弱化はできない．
3. 型の付く式を，燃料が十分なら必ず値に評価できること(正規化)を示す必要がある．このIterationの言語では，1ステップごとに式が小さくなることから示せる．Iteration 7で再帰を足すと，正規化は成り立たなくなる．
4. 模範解答の設計書は，`mise run check-design`で`一致`になる．

## 5-7 発展課題

```lean
def Term.hasFree (x : String) : Term → Bool
  | .num _ | .tru | .fls => false
  | .add t₁ t₂ | .sub t₁ t₂ | .mul t₁ t₂ => t₁.hasFree x || t₂.hasFree x
  | .ite c t e => c.hasFree x || t.hasFree x || e.hasFree x
  | .iszero t => t.hasFree x
  | .var y => y == x
  | .let_ y t u => t.hasFree x || (y != x && u.hasFree x)
```

`subst_not_free`は`t`についての帰納法で証明できる．
`let_ y t u`の場合，`y = x`なら本体は置換されず，`y ≠ x`なら本体に自由な`x`がないことを仮定から取り出して帰納法の仮定を使う．

```lean
  | let_ y t u iht ihu =>
    simp [Term.hasFree] at h
    by_cases hyx : y = x
    · simp [subst, hyx, iht h.1]
    · simp [subst, hyx, iht h.1, ihu (h.2 hyx)]
```

閉じた式は，どの変数についても自由な変数を持たないので，置換しても変わらない．
