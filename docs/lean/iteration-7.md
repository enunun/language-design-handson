# Iteration 7 導出を組み立てる・主張を一般化する

Iteration 7で使うLeanのtacticを説明する．
例には，自然数の上の簡約に似た関係`R`と，その0回以上の繰り返し`RStar`を使う．

```lean
inductive R : Nat → Nat → Prop where
  | spin : R 0 0
  | down {n : Nat} : R (n + 1) n

inductive RStar : Nat → Nat → Prop where
  | refl {n : Nat} : RStar n n
  | step {a b c : Nat} : R a b → RStar b c → RStar a c
```

`R`は，`0`から`0`へ，`n + 1`から`n`へ移る関係である．
`0`からは`0`にしか移れない．

## 導出を根から組み立てる：`refine`と`?_`

`refine e`は，`e`の中の`?_`を新しいゴールとして残し，`e`をゴールに当てはめるtacticである．
導出の木を根から順に組み立てるときに使う．

```lean
example : RStar 2 0 := by
  refine .step .down ?_
  refine .step .down ?_
  exact .refl
```

1行目で`RStar 2 0`を`R 2 1`と`RStar 1 0`に分け，`R 2 1`を`.down`で埋めて`RStar 1 0`を残す．
導出の木が大きく，1つの式で書くと型の推論がうまくいかないときにも，`refine`で1段ずつ組み立てれば通ることが多い．

## 帰納法の前に主張を一般化する：`suffices`

`0`から何回移っても，`0`にしか着かないことを示す．
仮定`h : RStar 0 n`について帰納法を使おうとすると，エラーになる．

```lean
theorem rstar_zero {n : Nat} (h : RStar 0 n) : n = 0 := by
  induction h with
  | refl => rfl
  | step _ _ ih => exact ih
```

```text
error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  0
```

`induction`は，`RStar a c`の`a`と`c`がどちらも変数であることを求める．
ここでは`a`が`0`に決まっているので，帰納法を使えない．

`suffices P from e`は，ゴールの代わりに`P`を示すことにするtacticである．
`e`は，`P`を表す名前`this`を使って，元のゴールを示す式である．
始点を変数`m`にし，「`m`が`0`ならば」という仮定に移した主張を示すことにする．

```lean
theorem rstar_zero' {n : Nat} (h : RStar 0 n) : n = 0 := by
  suffices ∀ m, RStar m n → m = 0 → n = 0 from this 0 h rfl
  clear h
  intro m hm
  induction hm with
  | refl => exact id
  | step hr _ ih =>
    intro hz
    subst hz
    cases hr
    exact ih rfl
```

`step`の場合では，`hr : R 0 b`を`cases`で分解すると，`b`が`0`に決まる．
そこで帰納法の仮定`ih : 0 = 0 → c = 0`が使える．
Iteration 5の`generalize`も同じ目的のtacticである．
`generalize`は式の一部を変数に置き換えるが，ゴールの中の同じ式もいっしょに置き換える．
ゴールに同じ式が現れるときは，`suffices`で主張を書き直すほうがわかりやすい．

## 要らない仮定を消す：`clear`

`clear h`は，仮定`h`を消すtacticである．
上の証明から`clear h`を除くと，エラーになる．

```text
error: Application type mismatch: The argument
  rfl
has type
  ?m.97 = ?m.97
but is expected to have type
  RStar 0 c✝
in the application
  ih rfl
```

`induction hm`は，`hm`の添字`n`に依存する仮定を，帰納法の仮定に含める．
`h : RStar 0 n`も`n`に依存するので，`ih`は`RStar 0 c → 0 = 0 → c = 0`になる．
`suffices`で使い終わった`h`を消しておけば，`ih`は求める形になる．
