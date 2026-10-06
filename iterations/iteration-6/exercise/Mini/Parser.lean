import Mini.Syntax

/-!
# 構文解析器

文字列を`Term`に変換する．この構文解析器は教材として配布するものである．

受け付ける構文は次のとおりである．`*`は`+`と`-`より強く結合し，同じ強さの演算子は左から結合する．
`if`の`else`の後の式と，`let`の`in`の後の式は，できるだけ長く読む．
変数の名前は英字で始まり，英字と数字と`_`が続く．キーワードは変数の名前にできない．

```
expr ::= "if" expr "then" expr "else" expr
       | "let" 変数 "=" expr "in" expr
       | arith
arith ::= term (("+" | "-") term)*
term ::= app ("*" app)*
app  ::= "iszero" atom | atom
atom ::= 数字の列 | "true" | "false" | 変数 | "(" expr ")"
```

どの関数も，燃料(第1引数の自然数)についての構造的な再帰で書いている．
そのため，`run "1 + 2"`のような具体例を，Leanのカーネルで評価して証明できる．
-/

namespace Mini.Parser

/-- 字句． -/
inductive Token where
  | num (n : Nat)
  | plus
  | minus
  | star
  | lparen
  | rparen
  | tru
  | fls
  | if_
  | then_
  | else_
  | iszero
  | let_
  | in_
  | eq
  | ident (x : String)
  deriving Repr, DecidableEq

/-- 先頭から続く数字を読み，その値と残りの文字列を返す．`acc`はそこまでに読んだ値である． -/
def readNat : List Char → Nat → Nat × List Char
  | c :: cs, acc => if c.isDigit then readNat cs (acc * 10 + (c.toNat - '0'.toNat)) else (acc, c :: cs)
  | [], acc => (acc, [])

/-- 先頭から続く英字と数字を読み，読んだ文字の列と残りの文字列を返す． -/
def readWord : List Char → List Char × List Char
  | c :: cs =>
    if c.isAlphanum || c == '_' then
      let (w, rest) := readWord cs
      (c :: w, rest)
    else ([], c :: cs)
  | [] => ([], [])

/-- 単語を字句にする．キーワードでなければ変数の名前にする． -/
def keyword (w : List Char) : Token :=
  if w == "true".toList then .tru
  else if w == "false".toList then .fls
  else if w == "if".toList then .if_
  else if w == "then".toList then .then_
  else if w == "else".toList then .else_
  else if w == "iszero".toList then .iszero
  else if w == "let".toList then .let_
  else if w == "in".toList then .in_
  else .ident (String.ofList w)

/-- 文字の列を字句の列に分ける． -/
def tokenize : Nat → List Char → Except String (List Token)
  | 0, _ => .error "入力が長すぎる"
  | _ + 1, [] => .ok []
  | fuel + 1, c :: cs =>
    if c == ' ' then tokenize fuel cs
    else if c == '+' then (Token.plus :: ·) <$> tokenize fuel cs
    else if c == '-' then (Token.minus :: ·) <$> tokenize fuel cs
    else if c == '*' then (Token.star :: ·) <$> tokenize fuel cs
    else if c == '(' then (Token.lparen :: ·) <$> tokenize fuel cs
    else if c == ')' then (Token.rparen :: ·) <$> tokenize fuel cs
    else if c == '=' then (Token.eq :: ·) <$> tokenize fuel cs
    else if c.isDigit then
      let (n, rest) := readNat (c :: cs) 0
      (Token.num n :: ·) <$> tokenize fuel rest
    else if c.isAlpha then
      let (w, rest) := readWord (c :: cs)
      (keyword w :: ·) <$> tokenize fuel rest
    else .error s!"使えない文字がある({c})"

/-- 構文解析の結果．読んだ式と，残りの字句の組である． -/
abbrev Result := Except String (Term × List Token)

/-- 字句の列の先頭が`tok`なら，それを読み飛ばした残りを返す． -/
def expect (tok : Token) (what : String) : List Token → Except String (List Token)
  | t :: ts => if t == tok then .ok ts else .error s!"{what}がない"
  | [] => .error s!"{what}がない"

mutual

/-- `expr`を読む． -/
def expr : Nat → List Token → Result
  | 0, _ => .error "式が深すぎる"
  | fuel + 1, .if_ :: ts => do
    let (c, ts) ← expr fuel ts
    let ts ← expect .then_ "then" ts
    let (t, ts) ← expr fuel ts
    let ts ← expect .else_ "else" ts
    let (e, ts) ← expr fuel ts
    .ok (.ite c t e, ts)
  | fuel + 1, .let_ :: .ident x :: ts => do
    let ts ← expect .eq "=" ts
    let (t, ts) ← expr fuel ts
    let ts ← expect .in_ "in" ts
    let (u, ts) ← expr fuel ts
    .ok (.let_ x t u, ts)
  | _ + 1, .let_ :: _ => .error "letの後に変数の名前がない"
  | fuel + 1, ts => arith fuel ts
termination_by structural fuel => fuel

/-- `arith`を読む． -/
def arith : Nat → List Token → Result
  | 0, _ => .error "式が深すぎる"
  | fuel + 1, ts => do
    let (t, rest) ← term fuel ts
    arithRest fuel t rest
termination_by structural fuel => fuel

/-- `arith`の2つ目以降の項を読み，`acc`に左から結合する． -/
def arithRest : Nat → Term → List Token → Result
  | 0, _, _ => .error "式が深すぎる"
  | fuel + 1, acc, .plus :: ts => do
    let (t, rest) ← term fuel ts
    arithRest fuel (.add acc t) rest
  | fuel + 1, acc, .minus :: ts => do
    let (t, rest) ← term fuel ts
    arithRest fuel (.sub acc t) rest
  | _ + 1, acc, ts => .ok (acc, ts)
termination_by structural fuel => fuel

/-- `term`を読む． -/
def term : Nat → List Token → Result
  | 0, _ => .error "式が深すぎる"
  | fuel + 1, ts => do
    let (t, rest) ← app fuel ts
    termRest fuel t rest
termination_by structural fuel => fuel

/-- `term`の2つ目以降の因子を読み，`acc`に左から結合する． -/
def termRest : Nat → Term → List Token → Result
  | 0, _, _ => .error "式が深すぎる"
  | fuel + 1, acc, .star :: ts => do
    let (t, rest) ← app fuel ts
    termRest fuel (.mul acc t) rest
  | _ + 1, acc, ts => .ok (acc, ts)
termination_by structural fuel => fuel

/-- `app`を読む． -/
def app : Nat → List Token → Result
  | 0, _ => .error "式が深すぎる"
  | fuel + 1, .iszero :: ts => do
    let (t, rest) ← atom fuel ts
    .ok (.iszero t, rest)
  | fuel + 1, ts => atom fuel ts
termination_by structural fuel => fuel

/-- `atom`を読む． -/
def atom : Nat → List Token → Result
  | 0, _ => .error "式が深すぎる"
  | _ + 1, .num n :: ts => .ok (.num n, ts)
  | _ + 1, .tru :: ts => .ok (.tru, ts)
  | _ + 1, .fls :: ts => .ok (.fls, ts)
  | _ + 1, .ident x :: ts => .ok (.var x, ts)
  | fuel + 1, .lparen :: ts => do
    let (t, rest) ← expr fuel ts
    match rest with
    | .rparen :: rest => .ok (t, rest)
    | _ => .error "閉じかっこがない"
  | _ + 1, [] => .error "式が途中で終わっている"
  | _ + 1, _ :: _ => .error "式があるべき位置に別の記号がある"
termination_by structural fuel => fuel

end

end Mini.Parser

namespace Mini

/-- 文字列を式に変換する．失敗したときは，その理由を返す． -/
def parse (s : String) : Except String Term := do
  let cs := s.toList
  let ts ← Parser.tokenize (cs.length + 1) cs
  let (t, rest) ← Parser.expr (8 * ts.length + 8) ts
  match rest with
  | [] => .ok t
  | _ => .error "式の後に余分な記号がある"

end Mini
