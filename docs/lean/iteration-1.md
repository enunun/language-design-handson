# Iteration 1 帰納的述語と帰納法

Iteration 1で使うLeanの構文とtacticを説明する．
例には，自然数のリストの和を表す関係`SumOf`と，和を計算する関数`total`を使う．

## 帰納的述語

`inductive`で，データ型だけでなく，関係(述語)も定義できる．
型の最後を`Prop`にすると，その型の値は「関係が成り立つことの証拠」になる．

```lean
inductive SumOf : List Nat → Nat → Prop where
  | nil : SumOf [] 0
  | cons {x : Nat} {xs : List Nat} {s : Nat} : SumOf xs s → SumOf (x :: xs) (x + s)
```

`SumOf xs s`は，「リスト`xs`の和は`s`である」と読む．
各構成子が1つの推論規則に対応する．

- `nil`：空のリスト`[]`の和は`0`である．前提のない規則である．
- `cons`：`xs`の和が`s`ならば，`x :: xs`(先頭に`x`を足したリスト)の和は`x + s`である．`→`の左が前提，右が結論である．

構成子の`{x : Nat}`のような波かっこの引数は，暗黙の引数である．
規則を使うときに，Leanが結論の形から推論する．

## 構成子を組み合わせた証明

関係が成り立つことは，構成子を組み合わせた項で証明できる．
この項が，推論規則を組み合わせた導出木に対応する．

```lean
example : SumOf [1, 2] 3 := SumOf.cons (SumOf.cons SumOf.nil)
```

内側から読むと，`[]`の和が`0`，`[2]`の和が`2 + 0`，`[1, 2]`の和が`1 + (2 + 0)`である．
`1 + (2 + 0)`と`3`は計算すると等しいので，Leanはこの証明を受け入れる．

`by`の後で`exact SumOf.cons ...`と書いても同じである．
`constructor`は，ゴールの形に合う構成子を探して当てはめるtacticである．

## 場合分け：`cases`

仮定`h : SumOf xs s`があるとき，`cases h`は，`h`がどの規則で導かれたかで場合を分ける．
各場合で，規則の前提が新しい仮定として使えるようになる．

「導出できない」ことは，否定`¬`の証明になる．
導出を仮定し，`cases`ですべての規則の可能性を調べ，どれも矛盾することを示す．

```lean
example : ¬ SumOf [1] 2 := by
  have h1 : ∀ s, SumOf [1] s → s = 1 := by
    intro s h
    cases h with
    | cons h' =>
      cases h'
      rfl
  intro h
  have := h1 2 h
  contradiction
```

結論の数(ここでは`2`)を具体的な値にしたまま`cases`を使うと，Leanは`2 = 1 + s`のような等式を解こうとして失敗する．

```text
error: Dependent elimination failed: Failed to solve equation
  2 = Nat.add 1 s✝
```

そこで，まず「`[1]`の和はどんな`s`でも`1`である」を`have`で示す．
`s`は変数なので，`cases`は`s = 1 + 0`を代入として扱える．
その後で`s = 2`に当てはめると，`2 = 1`という偽の仮定が得られる．
`contradiction`は，仮定の中から矛盾を見つけて証明を終えるtacticである．

## 構造帰納法：`induction t`

すべてのリストについて成り立つことは，リストの構造についての帰納法で証明する．

```lean
theorem total_sound (xs : List Nat) : SumOf xs (total xs) := by
  induction xs with
  | nil => exact SumOf.nil
  | cons x xs ih => exact SumOf.cons ih
```

`induction xs with`は，`xs`の構成子ごとに場合を分ける．
`cons`の場合では，部分`xs`について主張が成り立つことを，仮定`ih`(帰納法の仮定)として使える．
`cons`の場合のゴールは次のとおりである．

```text
case cons
x : Nat
xs : List Nat
ih : SumOf xs (total xs)
⊢ SumOf (x :: xs) (total (x :: xs))
```

`total (x :: xs)`は定義から`x + total xs`なので，`SumOf.cons ih`がそのまま当てはまる．

構成子の引数が2つあれば，帰納法の仮定も2つ得られる．
`| add t₁ t₂ ih₁ ih₂ =>`のように，引数の名前の後に仮定の名前を並べる．

## 導出に関する帰納法：`induction h`

仮定`h : SumOf xs s`の導出の形についての帰納法も使える．
規則ごとに場合を分け，前提の導出について主張が成り立つことを帰納法の仮定として使う．

```lean
theorem total_complete {xs : List Nat} {s : Nat} (h : SumOf xs s) : total xs = s := by
  induction h with
  | nil => rfl
  | cons _ ih => simp [total, ih]
```

`cons`の場合のゴールは次のとおりである．

```text
case cons
xs : List Nat
s x✝ : Nat
xs✝ : List Nat
s✝ : Nat
a✝ : SumOf xs✝ s✝
ih : total xs✝ = s✝
⊢ total (x✝ :: xs✝) = x✝ + s✝
```

名前に`✝`が付いた変数は，Leanが自動で付けた，証明の中で名前では参照できない変数である．
`simp [total, ih]`は`total`を展開し，`ih`で`total xs✝`を`s✝`に書き換えて，両辺を一致させる．

## 等式の仮定を使う：`subst`と`rw [← h]`

仮定`h : total xs = s`があるとき，`subst h`は，ゴールの`s`をすべて`total xs`に置き換え，`s`を消す．

```lean
example (xs : List Nat) (s : Nat) (h : total xs = s) : SumOf xs s := by
  subst h
  exact total_sound xs
```

`rw [h]`は`h`の左辺を右辺に書き換える．
`rw [← h]`は逆向きに，右辺を左辺に書き換える．

## 記法`infix`

```lean
infix:50 " ⇓ " => Eval
```

は，`Eval t n`を`t ⇓ n`と書けるようにする記法の宣言である．
`50`は結合の強さで，`=`と同じ強さである．
`⇓`は，エディタで`\Downarrow`と打つと入力できる．
