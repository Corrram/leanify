import Leanify.Segment

/-! # The sentence grammar

A sentence is read as a sequence of chunks: words, punctuation, inline formulas,
displays and references. The grammar is a fixed list of constructions of
mathematical English. Each has one documented reading (see `Elab`). A sentence
that matches none of them completely is prose: it is kept and shown, but it
asserts nothing checkable. A partial match is never accepted. -/
namespace Leanify

inductive Chunk where
  | w (word : Codes)
  | p (c : Nat)
  | m (toks : List MTok)
  | d (toks : List MTok) (labels : List Codes)
  | r (kind : RefKind) (arg : Codes)
  | x
  deriving Repr, Inhabited, Lean.ToExpr

namespace Grammar

def lower (c : Codes) : Codes := c.map fun x => if 65 ≤ x && x ≤ 90 then x + 32 else x

def isSig : List MTok → Bool := fun ts => ts.contains (.cmd w!"to")

/-- Drop a final period or comma of a display (it belongs to the sentence). -/
def hoist (ts : List MTok) : List MTok × Option Nat :=
  -- a final period may sit inside nested environments; a comma only at top level
  let rec go : List MTok → List MTok → Option (List MTok × Nat)
    | [], _ => none
    | t :: rest, after =>
      match t with
      | .finish _ | .rb | .row => go rest (t :: after)
      | .sym 46 => some (rest.reverse ++ after, 46)
      | .sym 44 => if after.isEmpty then some (rest.reverse ++ after, 44) else none
      | _ => none
  match go ts.reverse [] with
  | some (r, c) => (r, some c)
  | none => (ts, none)

/-- Group a sentence's tokens into chunks. -/
def chunks : Nat → List PTok → List Chunk → Option (List Chunk)
  | 0, _, _ => none
  | _ + 1, [], acc => some acc.reverse
  | f + 1, t :: ts, acc =>
    match t.tok with
    | .word w => chunks f ts (.w (lower w) :: acc)
    | .punct c => chunks f ts (.p c :: acc)
    | .ref k a => chunks f ts (.r k a :: acc)
    | .mopen =>
      let body := ts.takeWhile (fun p => p.tok != .mclose)
      match Math.simplify (body.length + 1) body with
      | some ms =>
        let (ms, punct) := hoist ms
        let acc := Chunk.m ms :: acc
        let acc := match punct with | some c => .p c :: acc | none => acc
        chunks f (ts.drop (body.length + 1)) acc
      | none => none
    | .begin e =>
      if Lex.wDisplayEnvs.contains e then
        let body := ts.takeWhile (fun p => p.tok != .finish e)
        let labels := body.filterMap fun p => match p.tok with | .ref .label l => some l | _ => none
        match Math.simplify (body.length + 1) body with
        | some ms =>
          let (ms, punct) := hoist ms
          let acc := Chunk.d ms labels :: acc
          let acc := match punct with | some c => .p c :: acc | none => acc
          chunks f (ts.drop (body.length + 1)) acc
        | none => none
      else chunks f ts (.x :: acc)
    | _ => chunks f ts (.x :: acc)

/-- A sequence of exact (lower-case) words. -/
def kw : List Codes → List Chunk → Option (List Chunk)
  | [], cs => some cs
  | w :: ws, .w v :: cs => if v == w then kw ws cs else none
  | _, _ => none

def punct (c : Nat) : List Chunk → Option (List Chunk)
  | .p d :: cs => if c == d then some cs else none
  | _ => none

def optPunct (c : Nat) (cs : List Chunk) : List Chunk := (punct c cs).getD cs

def mathChunk : List Chunk → Option (List MTok × List Chunk)
  | .m ts :: cs => some (ts, cs)
  | _ => none

/-- `a_n\to L`: the limit of the term as its index tends to `∞` (a term with a letter as
subscript). -/
def seqLimitMT (ts : List MTok) : Option MT := do
  let j ← ts.findIdx? (· == .cmd w!"to")
  let a ← Math.parseFormula (ts.take j)
  let l ← Math.parseFormula (ts.drop (j + 1))
  let rec idx : Nat → MT → Option Codes
    | 0, _ => none
    | k + 1, m => match m with
      | .sub _ (.id n) => some n
      | .sup b e => idx k b <|> idx k e
      | .add x y | .minus x y | .mul x y | .div x y | .frac x y => idx k x <|> idx k y
      | .neg x | .abs x => idx k x
      | _ => none
  let v ← idx 12 a
  let c ← Math.parseFormula [.cmd w!"infty"]
  some (.app (.id w!"@tendsto") [.limit v c a, l])

def formula (cs : List Chunk) : Option (MT × List Chunk) := do
  let (ts, rest) ← mathChunk cs
  match Math.parseDisplay ts with
  | some m => some (m, rest)
  | none =>
    -- (`$a_n\to0$`, without `as $n\to\infty$`)
    if (kw [w!"as"] rest).isNone then
      if let some m := seqLimitMT ts then return (m, rest)
    -- `$a,b>0$`: each name with the bound after the last (`a>0` and `b>0`)
    let parts := (Math.commaParts (ts.length + 1) 0 [] ts []).filter (!·.isEmpty)
    if parts.length < 2 then none else
    let last ← parts.getLast?
    let i ← last.findIdx? fun t => (Math.relOf t).isSome
    let suffix := last.drop i
    let names := parts.dropLast ++ [last.take i]
    if !names.all (fun n => match n with | [.id _] | [.cmd _] => true | _ => false) then none
    let ms ← names.mapM fun n => Math.parseFormula (n ++ suffix)
    some (.conj ms, rest)

def sig (cs : List Chunk) : Option (MT × List Chunk) := do
  let (ts, rest) ← mathChunk cs
  let m ← Math.parseSig ts
  some (m, rest)

/-- `\hat x` or `\hat{x}` (or `\widehat`) at the start of `ts`: the name `\hat{x}` and
the tokens after it. -/
def hatName : List MTok → Option (Codes × List MTok)
  | .cmd h :: .id n :: r | .cmd h :: .lb :: .id n :: .rb :: r =>
    if h == w!"hat" || h == w!"widehat" then some ([92] ++ w!"hat{" ++ n ++ [125], r) else none
  | _ => none

/-- A list of variables `x_1,\ldots,x_n` (`x_0,x_1,\dots,x_{N-1}`, `\varepsilon_1,\ldots,\varepsilon_N`):
the terms `x_i` of a sequence `x`, for the integers `i` from the first index to the last.
Its name, the tokens of the name, and the two indices. The terms written before the dots
are the first ones (`x_1,x_2,\ldots`). -/
def seqVars (ts : List MTok) : Option (Codes × List MTok × MT × MT) := do
  let parts := Math.commaParts (ts.length + 1) 0 [] ts []
  if parts.length < 3 then none else
  let first ← parts.head?
  let last ← parts.getLast?
  let mid := (parts.drop 1).dropLast
  let dots := match mid.getLast? with | some [t] => Math.isDots t | _ => false
  if !dots then none else
  let (x, lo) ← match Math.parseFormula first with
    | some (.sub (.id x) lo) => some (x, lo)
    | _ => none
  let hi ← match Math.parseFormula last with
    | some (.sub (.id y) hi) => if y == x then some hi else none
    | _ => none
  let consecutive := mid.dropLast.zipIdx.all fun (p, k) =>
    match Math.parseFormula p, lo with
    | some (.sub (.id y) (.num m)), .num l => y == x && m == l + k + 1
    | _, _ => false
  if !consecutive then none else
  some (x, first.takeWhile (· != .sym 95), lo, hi)

/-- A sequence variable with a bound written after its last term (`a_1,\ldots,a_n\ge1`):
the list, and the bound (`\ge1`; empty without one). -/
def seqBound (ts : List MTok) : Option (List MTok × List MTok) := do
  let last ← (Math.commaParts (ts.length + 1) 0 [] ts []).getLast?
  let k := (last.findIdx? fun t => (Math.relOf t).isSome).getD last.length
  let list := ts.take (ts.length - (last.length - k))
  let _ ← seqVars list
  some (list, ts.drop list.length)

/-- `independent and identically distributed` as the one word `iid` (the `and` is not
between two adjectives of the noun, `with $φ$ and …`). -/
def normIID : List Chunk → List Chunk
  | .w a :: .w b :: .w c :: .w d :: rest =>
    if a == w!"independent" && b == w!"and" && c == w!"identically" && d == w!"distributed" then .w w!"iid" :: normIID rest
    else .w a :: normIID (.w b :: .w c :: .w d :: rest)
  | c :: rest => c :: normIID rest
  | [] => []

/-- Adjectives about several variables together, among the words `ws`: `distinct`
(`pairwise distinct`), `relatively prime` or `coprime` (`pairwise …`). The other words, and
the properties found (`distinct`, `coprime`, `pairwise coprime`). -/
def collectiveWords : Nat → List Chunk → List Chunk × List Codes
  | 0, ws => (ws, [])
  | f + 1, ws =>
    let found : Option (Codes × List Chunk) :=
      ((kw [w!"pairwise", w!"distinct"] ws <|> kw [w!"distinct"] ws).map (w!"distinct", ·)) <|>
      ((kw [w!"pairwise", w!"relatively", w!"prime"] ws <|> kw [w!"pairwise", w!"coprime"] ws).map
        (w!"pairwise coprime", ·)) <|>
      ((kw [w!"relatively", w!"prime"] ws <|> kw [w!"coprime"] ws).map (w!"coprime", ·)) <|>
      -- (of random variables)
      ((kw [w!"independent", w!"and", w!"identically", w!"distributed"] ws <|> kw [w!"i.i.d."] ws <|>
        kw [w!"iid"] ws <|> kw [w!"i", w!"."] ws).map (w!"iid", ·)) <|>
      ((kw [w!"independent"] ws <|> kw [w!"mutually", w!"independent"] ws).map (w!"independent", ·)) <|>
      ((kw [w!"identically", w!"distributed"] ws).map (w!"identically distributed", ·)) <|>
      -- (of vectors: the family)
      ((kw [w!"linearly", w!"independent"] ws).map (w!"linearly independent", ·)) <|>
      ((kw [w!"linearly", w!"dependent"] ws).map (w!"linearly dependent", ·)) <|>
      -- (of vectors of an inner product space: any two; `orthogonal matrices` are each orthogonal)
      (if !(ws.any fun c => match c with | .w w => w == w!"vectors" || w == w!"elements" | _ => false) then none else
        (kw [w!"pairwise", w!"orthogonal"] ws <|> kw [w!"mutually", w!"orthogonal"] ws <|> kw [w!"orthogonal"] ws).map
          (w!"orthogonal", ·))
    match found, ws with
    | some (p, rest), _ => let (ws', ps) := collectiveWords f rest; (ws', p :: ps)
    | none, c :: rest => let (ws', ps) := collectiveWords f rest; (c :: ws', ps)
    | none, [] => ([], [])

/-- The condition the collective properties `ps` put on the variables `vars` (several
variables, each possibly with a bound, or one sequence `x_1,\ldots,x_n`): any two of
them are different (`distinct`), or have greatest common divisor `1` (`pairwise
coprime`; `coprime` of exactly two variables: of more it is ambiguous). -/
def collectiveCond (ps : List Codes) (vars : List (List MTok)) : Option MT := do
  let pairCond (p : Codes) (a b : MT) : MT :=
    if p == w!"distinct" then .chain a [(.ne, b)]
    else if p == w!"orthogonal" then .chain (.app (.id w!"@inner") [a, b]) [(.eq, .num 0)]
    else .chain (.app (.id w!"\\gcd") [.tuple [a, b]]) [(.eq, .num 1)]
  let name (v : List MTok) : List MTok := v.takeWhile fun t => (Math.relOf t).isNone
  -- (random variables: independent, identically distributed, both)
  let rvConds (p : Codes) : Option (List MT) := do
    let kinds : List Codes :=
      if p == w!"independent" then [w!"@indep"] else if p == w!"identically distributed" then [w!"@identdist"]
      else if p == w!"iid" then [w!"@indep", w!"@identdist"] else []
    if kinds.isEmpty then none
    match vars with
    | [ts] => do
      let (list, _) ← seqBound ts
      let (x, _, lo, hi) ← seqVars list
      some (kinds.map fun k => MT.app (.id (k ++ w!"seq")) [.id x, lo, hi])
    | _ => do
      let ms ← vars.mapM fun v => Math.parseFormula (name v)
      some (kinds.map fun k => MT.app (.id k) ms)
  -- (a family with an adjective of sets of the vocabulary, `linearly independent`: its terms
  -- are distinct and their set has it; `linearly dependent`: not so)
  let famCond (p : Codes) : Option MT := do
    let (adj, neg) ← if p == w!"linearly independent" then some (p, false)
      else if p == w!"linearly dependent" then some (w!"linearly independent", true) else none
    let c ← match vars with
      | [ts] => do
        let (list, _) ← seqBound ts
        let (x, _, lo, hi) ← seqVars list
        some (MT.app (.id w!"@familyseq") [.id ([64] ++ adj), .id x, lo, hi])
      | _ => do
        let ms ← vars.mapM fun v => Math.parseFormula (name v)
        some (MT.app (.id w!"@family") (.id ([64] ++ adj) :: ms))
    some (if neg then .lnot c else c)
  let conds ← ps.mapM fun p => do
    if let some c := famCond p then return c
    if let some cs := rvConds p then
      return (cs.drop 1).foldl (fun acc c => MT.land acc c) (cs.headD (.id w!"@none"))
    match vars with
    | [ts] => do
      -- a sequence: any two terms with different indices of its range
      let (list, _) ← seqBound ts
      let (x, _, lo, hi) ← seqVars list
      if p == w!"coprime" then none else
      let range (v : Codes) : MT := .setOf (.id v) (.id w!"\\mathbb{Z}") [.chain lo [(.le, .id v), (.le, hi)]]
      -- (names that are no variable of the article, and no existential threshold `@…`)
      let (i, j) := (w!"i@", w!"j@")
      some (.quant true [i] (range i) (.quant true [j] (range j)
        (.limp (.chain (.id i) [(.ne, .id j)]) (pairCond p (.sub (.id x) (.id i)) (.sub (.id x) (.id j))))))
    | _ => do
      let ms ← vars.mapM fun v => Math.parseFormula (name v)
      if p == w!"coprime" && ms.length != 2 then none else
      let pairs := ms.zipIdx.flatMap fun (a, k) => (ms.drop (k + 1)).map (a, ·)
      some (.conj (pairs.map fun (a, b) => pairCond p a b))
  match conds with
  | [c] => some c
  | cs => some (.conj cs)

/-- The name of a letter with a subscript that is a letter or a number (`d_0`, `n_k`,
`x_{12}`): one variable, as in `an integer $d_0$` and `$x_0\in A$` (a bound on it,
`$d_0\ge1$`, binds the same name). -/
def subNameOf (ts : List MTok) : Option Codes :=
  if ts.any (fun t => (Math.relOf t).isSome || t == .cmd w!"in" || t == .sym 44) then none else
  match Math.parseFormula ts with
  | some (.sub (.id k) (.id i)) => some (k ++ [95] ++ i)
  | some (.sub (.id k) (.num n)) => some (k ++ [95] ++ (Nat.toDigits 10 n).map Char.toNat)
  | _ => none

def subName (ts : List MTok) : Bool := (subNameOf ts).isSome

/-- Binder formulas `x\in A`, `u,v\in A`, or `(x,z)\in A^2` (each coordinate in `A`);
`x_1,\ldots,x_n\in A` binds the sequence `x` (`@seq lo hi A`). -/
def binderIn (ts : List MTok) : Option (List Codes × MT) := do
  let i ← ts.findIdx? (· == .cmd w!"in")
  let pre := ts.take i
  if let some (x, _, lo, hi) := seqVars pre then
    let dom ← Math.parseFormula (ts.drop (i + 1))
    return ([x], .app (.id w!"@seq") [lo, hi, dom])
  let (pre, square) := match pre with
    | .sym 40 :: r => match r.reverse with
      | .sym 41 :: r' => (r'.reverse, true)
      | _ => (pre, false)
    | _ => (pre, false)
  -- the names: letters, Greek letters, and `\hat x` (a command that is not a name, such
  -- as an accent, never is one)
  let rec names0 : Nat → List MTok → Option (List Codes)
    | _, [] => some []
    | 0, _ => none
    | f + 1, .sym 44 :: r => names0 f r
    -- `x_0`, `x_{k}`: a name with a subscript
    | f + 1, .id n :: .sym 95 :: r =>
      let sub := match r with
        | .lb :: r' => .lb :: r'.takeWhile (· != .rb) ++ [.rb]
        | t :: _ => [t]
        | [] => []
      match subNameOf (.id n :: .sym 95 :: sub) with
      | some v => (v :: ·) <$> names0 f (r.drop sub.length)
      | none => none
    | f + 1, .id n :: r => (n :: ·) <$> names0 f r
    | f + 1, .cmd n :: r =>
      match hatName (.cmd n :: r) with
      | some (v, r') => (v :: ·) <$> names0 f r'
      | none => if Math.greekNames.contains n then (([92] ++ n) :: ·) <$> names0 f r else none
    | _, _ => none
  -- `0\neq v\in V`, `0<x\in A`: an element of the domain with the relation
  if !square then
    if let some (.chain c [(r, .id v)]) := Math.parseFormula pre then
      if r == .ne || r == .lt || r == .le || r == .gt || r == .ge then
        if let some dom := Math.parseFormula (ts.drop (i + 1)) then
          return ([v], .setOf (.id v) dom [.chain c [(r, .id v)]])
  let names ← names0 (pre.length + 1) pre
  let dom ← Math.parseFormula (ts.drop (i + 1))
  let dom ← if square then
      match dom with
      | .sup d (.num k) => if k == names.length then some d else none
      | _ => none
    else some dom
  if names.isEmpty then none else some (names, dom)

/-- A binder written as a bound on one real variable: `c>0` is `c\in(0,\infty)`,
`x\ge a` is `x\in[a,\infty)`, `x<b` is `x\in(-\infty,b)`, and `a<x\le b` is
`x\in(a,b]`. -/
def boundBinder (ts : List MTok) : Option (List Codes × MT) := do
  let inf : MT := .id w!"\\infty"
  let named : MT → Option Codes := fun m => match m with
    | .id x => some x
    | .sub (.id k) (.id i) => some (k ++ [95] ++ i)
    | .sub (.id k) (.num n) => some (k ++ [95] ++ (Nat.toDigits 10 n).map Char.toNat)
    | _ => none
  match ← Math.parseFormula ts with
  -- `c_1,c_2>0`: the same bound on each variable
  | .tuple xs@(_ :: _ :: _) => do
    let (vs, last) ← match xs.reverse with
      | .chain v [(r, b)] :: rest => some (rest.reverse ++ [v], (r, b))
      | _ => none
    let ns ← vs.mapM named
    let (r, b) := last
    match r with
    | .gt => some (ns, .ival b inf true true)
    | .ge => some (ns, .ival b inf false true)
    | .lt => some (ns, .ival (.neg inf) b true true)
    | .le => some (ns, .ival (.neg inf) b true false)
    | _ => none
  | .chain (.tuple vs) [(r, b)] => do
    let xs ← vs.mapM named
    if xs.length < 2 then none else
    match r with
    | .gt => some (xs, .ival b inf true true)
    | .ge => some (xs, .ival b inf false true)
    | .lt => some (xs, .ival (.neg inf) b true true)
    | .le => some (xs, .ival (.neg inf) b true false)
    | _ => none
  | .chain v [(r, b)] =>
    let x ← named v
    match r with
    | .gt => some ([x], .ival b inf true true)
    | .ge => some ([x], .ival b inf false true)
    | .lt => some ([x], .ival (.neg inf) b true true)
    | .le => some ([x], .ival (.neg inf) b true false)
    | _ => none
  | .chain a [(r1, v), (r2, b)] =>
    let x ← named v
    if (r1 == .lt || r1 == .le) && (r2 == .lt || r2 == .le) then
      if r1 == .le && r2 == .le then some ([x], .interval a b)
      else some ([x], .ival a b (r1 == .lt) (r2 == .lt))
    else none
  | _ => none

/-- The same bound on several variables: `a,b>0`, `c_1,c_2\ge1`; on each term of a
sequence: `a_1,\ldots,a_n>0`. -/
def boundBinders (ts : List MTok) : Option (List Codes × MT) := do
  if let some (list, bound) := seqBound ts then
    let (x, _, lo, hi) ← seqVars list
    let (_, d) ← boundBinder (.id w!"x" :: bound)
    return ([x], .app (.id w!"@seq") [lo, hi, d])
  let parts := Math.commaParts (ts.length + 1) 0 [] ts []
  if parts.length < 2 then none else
  let (vs, d) ← boundBinder (parts.getLast?.getD [])
  let names ← (parts.dropLast).mapM fun p => match Math.parseFormula p with
    | some (.id x) => some x
    | some (.sub (.id k) (.id i)) => some (k ++ [95] ++ i)
    | some (.sub (.id k) (.num n)) => some (k ++ [95] ++ (Nat.toDigits 10 n).map Char.toNat)
    | _ => none
  some (names ++ vs, d)

/-- `S\subseteq A`: a variable that ranges over the subsets of `A`. -/
def binderSubset (ts : List MTok) : Option (List Codes × MT) := do
  match ts with
  | .id v :: .cmd c :: rest =>
    let proper := c == w!"subsetneq" || c == w!"subsetneqq" || c == w!"varsubsetneq" || c == w!"varsubsetneqq"
    if c != w!"subseteq" && !proper then none
    let dom ← Math.parseFormula rest
    some ([v], .app (.id (if proper then w!"@psubsets" else w!"@subsets")) [dom])
  | _ => none

/-- A binder: `x\in A`, or a bound on one real variable (`c>0`) or several (`a,b>0`). -/
def binderMath (ts : List MTok) : Option (List Codes × MT) :=
  binderIn ts <|> boundBinder ts <|> boundBinders ts <|> binderSubset ts

/-- The part of a display after its last top-level `\quad` or `\qquad`: `(head, tail)`. -/
def lastQuad : Nat → Int → List MTok → List MTok → Option (List MTok × List MTok) →
    Option (List MTok × List MTok)
  | 0, _, _, _, best => best
  | _ + 1, _, _, [], best => best
  | f + 1, d, acc, t :: ts, best =>
    let d' : Int := match t with
      | .lb | .setl | .sym 40 | .sym 91 | .begin _ => d + 1
      | .rb | .setr | .sym 41 | .sym 93 | .finish _ => d - 1
      | _ => d
    let best := if d == 0 && (t == .cmd w!"qquad" || t == .cmd w!"quad") then some (acc.reverse, ts) else best
    lastQuad f d' (t :: acc) ts best

/-- The inside of parentheses around all of `ts` (`(a)+(b)` is not one group). -/
def parenInside (ts : List MTok) : Option (List MTok) :=
  match ts with
  | .sym 40 :: r =>
    match r.reverse with
    | .sym 41 :: r' =>
      let inner := r'.reverse
      let (d, ok) := inner.foldl (fun (acc : Int × Bool) t =>
        let d := match t with | .sym 40 => acc.1 + 1 | .sym 41 => acc.1 - 1 | _ => acc.1
        (d, acc.2 && 0 ≤ d)) (0, true)
      if ok && d == 0 then some inner else none
    | _ => none
  | _ => none

/-- The words of the `\text{…}` tokens at the start of `ts`. -/
def textWords : List MTok → List Codes × List MTok
  | .text w :: ts => let (ws, r) := textWords ts; (lower w :: ws, r)
  | ts => ([], ts)

/-- The parts of `(p\in\mathbb Z,\ q\ge Q)` after a display formula, around its formula
`body`: a part binds its variables (`p\in A`, `q\ge Q`), unless one of them is already
bound in the parentheses; then it is a condition (`q\ge Q(\nu)` after `q\in\mathbb Z`). -/
def condParts : List Codes → List (List MTok) → MT → Option MT
  | _, [], body => some body
  | bound, p :: ps, body =>
    match binderMath p with
    | some (vs, dom) =>
      if vs.any bound.contains then do
        let c ← Math.parseFormula p
        some (.limp c (← condParts bound ps body))
      else do
        some (.quant true vs dom (← condParts (bound ++ vs) ps body))
    | none => do
      let c ← Math.parseFormula p
      some (.limp c (← condParts bound ps body))

/-- A display formula with what is written after it: binders and conditions in
parentheses (`\qquad(p\in\mathbb Z,\ q\ge Q)`), or in words (`\qquad\text{for every
}x\in A`, `\qquad\text{if }x>0`), read into the formula; and a noun-phrase binder
(`\qquad\text{for every integer }k\ge1`) for the clause, as `for every NP` after it. -/
def displayParts (ts : List MTok) : Option (MT × Option (List Chunk)) :=
  let ts' := match ts.reverse with
    | .sym 44 :: r | .sym 46 :: r | .sym 59 :: r => r.reverse
    | _ => ts
  let plain : Option (MT × Option (List Chunk)) := (Math.parseDisplay ts).map (·, none)
  -- `φ,\qquad\text{hence}\qquad ψ` (`so`, `thus`, `and`): both formulas
  let hence : Option (MT × Option (List Chunk)) := do
    let rec split : Nat → Int → List MTok → List MTok → Option (List MTok × List MTok)
      | 0, _, _, _ => none
      | _ + 1, _, _, [] => none
      | f + 1, d, acc, t :: rest =>
        let d' : Int := match t with
          | .lb | .setl | .sym 40 | .sym 91 | .begin _ => d + 1
          | .rb | .setr | .sym 41 | .sym 93 | .finish _ => d - 1
          | _ => d
        match t, rest with
        | .cmd q1, .text w :: .cmd q2 :: r =>
          if d == 0 && (q1 == w!"qquad" || q1 == w!"quad") && (q2 == w!"qquad" || q2 == w!"quad") &&
              [w!"hence", w!"so", w!"thus", w!"and", w!"therefore"].contains (lower w) then
            some (acc.reverse, r)
          else split f d' (t :: acc) rest
        | _, _ => split f d' (t :: acc) rest
    let (a, b) ← split (ts'.length + 1) 0 [] ts'
    let a := match a.reverse with
      | .sym 44 :: r => r.reverse
      | _ => a
    let ma ← Math.parseDisplay a
    let mb ← Math.parseDisplay b
    some (.conj [ma, mb], none)
  if hence.isSome then hence else
  match lastQuad (ts'.length + 1) 0 [] ts' none with
  | none => plain
  | some (head, tail) =>
    let head := match head.reverse with
      | .sym 44 :: r => r.reverse
      | _ => head
    match parenInside tail with
    | some inner => do
      -- (a formula in parentheses after a display is never a further claim)
      let body ← Math.parseDisplay head
      let parts := (Math.commaParts (inner.length + 1) 0 [] inner []).filter (!·.isEmpty)
      some (← condParts [] parts body, none)
    | none =>
      match textWords tail with
      | ([], _) => plain
      | (w :: ws, r) =>
        if r.isEmpty then plain
        else if w == w!"if" || w == w!"whenever" || w == w!"when" then do
          if !ws.isEmpty then none else
          let body ← Math.parseDisplay head
          let c ← Math.parseFormula r
          some (.limp c body, none)
        else if w == w!"for" then do
          let body ← Math.parseDisplay head
          let ws ← match ws with
            | q :: rest =>
              if q == w!"every" || q == w!"all" || q == w!"each" || q == w!"any" then some rest
              -- (`for some`: not a binder of every element)
              else if q == w!"some" then none else some ws
            | [] => some []
          if ws.isEmpty then do
            let (vs, dom) ← binderMath r
            some (.quant true vs dom body, none)
          else some (body, some (ws.map Chunk.w ++ [Chunk.m r]))
        else plain

def display (cs : List Chunk) : Option (MT × List Codes × List Chunk) :=
  match cs with
  | .d ts ls :: rest => do
    let (m, np) ← displayParts ts
    -- (a noun-phrase binder belongs to a clause: `displayClause`)
    if np.isSome then none else some (m, ls, rest)
  | _ => none

/-- Words until (not including) a stop word; fails if a non-word chunk occurs. -/
def wordsUntil (stop : List Codes) : Nat → List Chunk → List Codes → Option (List Codes × List Chunk)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | f + 1, .w v :: cs, acc =>
    if stop.contains v then some (acc.reverse, .w v :: cs) else wordsUntil stop f cs (v :: acc)
  | _, _, _ => none

/-- Chunks until a stop word at top level (words and formulas allowed). -/
def chunksUntil (stop : List Codes) : List Chunk → List Chunk → Option (List Chunk × List Chunk)
  | [], _ => none
  | .w v :: cs, acc =>
    if stop.contains v then some (acc.reverse, .w v :: cs) else chunksUntil stop cs (.w v :: acc)
  | c :: cs, acc =>
    match c with
    | .m _ | .p 45 => chunksUntil stop cs (c :: acc)
    | _ => none

/-- Citations: `Lemma~\ref{l}`, `Theorem~\ref{l}`, `Claim~\ref{l}`, `\eqref{l}`, `\cref{l}`. -/
def cite : List Chunk → Option (Codes × List Chunk)
  | .r .eqref l :: cs => some (l, cs)
  | .w v :: .r .ref l :: cs =>
    if [w!"lemma", w!"theorem", w!"corollary", w!"proposition", w!"equation", w!"section", w!"claim",
        w!"fact", w!"observation", w!"definition", w!"remark"].contains v then
      -- (a section is cited as `§l`: it names no result, and gives no premises)
      let l := if v == w!"section" then [167] ++ l else l
      -- (an item of it: `Section~\ref{s}~(d)`)
      match cs with
      | .p 40 :: .w i :: .p 41 :: r => if i.length ≤ 4 then some (l, r) else some (l, cs)
      | _ => some (l, cs)
    else none
  | _ => none

def isEnd : List Chunk → Bool
  | [.p 46] => true
  | _ => false

/-- Words, and formulas that state nothing (no relation: `$(U_i,V_i)$`, `$t\mapsto1-t$`), at the
start of `cs`: a reason or a description in words. The number of words, and the rest. -/
def reasonSpan (cs : List Chunk) : Nat × List Chunk :=
  let part := cs.takeWhile fun c => match c with
    | .w w => ![w!"give", w!"gives", w!"yields"].contains w
    | .p 45 | .p 39 => true
    | .m ts => match Math.parseFormula ts with
      | some (.chain _ _) | some (.land _ _) | some (.lor _ _) | some (.limp _ _) | some (.liff _ _)
      | some (.lnot _) | some (.quant ..) => false
      | _ => true
    | _ => false
  ((part.filter fun c => match c with | .w _ => true | _ => false).length, cs.drop part.length)

/-- A chunk of a description in words: a word, a hyphen, an apostrophe, or a formula that
states nothing (no relation: `$q_t$`, `$\min\{t,1-t\}$`). -/
def descChunk : Chunk → Bool
  | .w _ | .p 45 | .p 39 => true
  | .m ts => match Math.parseFormula ts with
    | some (.chain _ _) | some (.land _ _) | some (.lor _ _) | some (.limp _ _) | some (.liff _ _)
    | some (.lnot _) | some (.quant ..) | none => false
    | _ => true
  | _ => false

/-- `the function $q_t$ takes the values $1$, $0$, and $-1$ on …, so CLAUSES`: a description in
words (with formulas that state nothing, and commas) before `, so`, which asserts nothing, as a
reason in words. The chunks after `so`. -/
def descSo (cs : List Chunk) : Option (List Chunk) :=
  match cs with
  | .w _ :: _ => go 64 cs 0
  | _ => none
where
  go : Nat → List Chunk → Nat → Option (List Chunk)
    | 0, _, _ => none
    | f + 1, cs, n => match cs with
      | .p 44 :: .w s :: r =>
        -- (`, so that, by CITE, …`: the words `that` and the comma are part of `so`)
        let r := if s == w!"so" then optPunct 44 ((kw [w!"that"] r).getD r) else r
        if s == w!"so" then (if n ≥ 3 then some r else none) else go f (.w s :: r) n
      | .p 44 :: r => go f r n
      | c :: r => if descChunk c then go f r (match c with | .w _ => n + 1 | _ => n) else none
      | [] => none

/-- Words (a description, as in a reason) and then a citation: `the equality in the proof of
Theorem~\ref{t}`. The number of words before the citation, the citation, and the rest. -/
def wordsCite : Nat → List Chunk → Nat → Option (Nat × Codes × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, n =>
    match cite cs with
    | some (l, r) => some (n, l, r)
    | none => match cs with
      | c :: r => if descChunk c then wordsCite f r (match c with | .w _ => n + 1 | _ => n) else none
      | [] => none

/-- A subject in words, `the …` (with formulas that state nothing), and then the words `stop`:
the chunks after them. -/
def wordsThen (stop : List Codes) (cs : List Chunk) : Option (List Chunk) :=
  match cs with
  | .w t :: _ => if t != w!"the" then none else go 32 cs 0
  | _ => none
where
  go : Nat → List Chunk → Nat → Option (List Chunk)
    | 0, _, _ => none
    | f + 1, cs, n =>
      match kw stop cs with
      | some r => if n ≥ 2 then some r else none
      | none => match cs with
        | c :: r => if descChunk c then go f r (match c with | .w _ => n + 1 | _ => n) else none
        | [] => none

/-- A subject in words that introduces a claim: `Comparing the two terms in the maximum
shows that`, `a direct computation shows that` (at least two words, and formulas that state
nothing). It asserts nothing; the chunks after `that` (and an optional comma). -/
def showsThat (cs : List Chunk) : Option (List Chunk) :=
  match cs with
  | .w _ :: _ => go 32 cs 0
  | _ => none
where
  go : Nat → List Chunk → Nat → Option (List Chunk)
    | 0, _, _ => none
    | f + 1, cs, n =>
      match kw [w!"shows", w!"that"] cs <|> kw [w!"show", w!"that"] cs with
      | some r => if n ≥ 2 then some (optPunct 44 r) else none
      | none => match cs with
        | c :: r => if descChunk c then go f r (match c with | .w _ => n + 1 | _ => n) else none
        | [] => none

/-- Further citations after a first one: `CITE, CITE and CITE` (`By \eqref{a} and
Lemma~\ref{l}, …`). -/
def moreCites : Nat → List Chunk → List Codes × List Chunk
  | 0, cs => ([], cs)
  | f + 1, cs =>
    let next : Option (Codes × List Chunk) :=
      (kw [w!"and"] cs >>= cite) <|> (punct 44 cs >>= kw [w!"and"] >>= cite) <|> (punct 44 cs >>= cite)
    match next with
    | some (l, r) => let (ls, r') := moreCites f r; (l :: ls, r')
    | none => ([], cs)

/-- Discourse markers: they connect sentences and assert nothing. -/
def wMarkers : List (List Codes) :=
  [[w!"to", w!"make", w!"this", w!"precise"], [w!"consequently"], [w!"hence"], [w!"in", w!"particular"],
   [w!"then"], [w!"thus"], [w!"therefore"], [w!"indeed"], [w!"moreover"], [w!"furthermore"],
   [w!"in", w!"addition"], [w!"finally"], [w!"again"], [w!"conversely"], [w!"similarly"], [w!"likewise"],
   [w!"in", w!"other", w!"words"], [w!"that", w!"is"], [w!"we", w!"have"], [w!"it", w!"follows", w!"that"],
   [w!"we", w!"obtain"], [w!"note", w!"that"], [w!"we", w!"see", w!"that"], [w!"more", w!"precisely"],
   [w!"this", w!"gives"], [w!"this", w!"yields"],
   [w!"equivalently"], [w!"also"], [w!"in", w!"both", w!"cases"], [w!"in", w!"either", w!"case"],
   [w!"in", w!"all", w!"cases"], [w!"in", w!"each", w!"case"], [w!"in", w!"any", w!"case"],
   [w!"by", w!"the", w!"induction", w!"hypothesis"], [w!"by", w!"the", w!"inductive", w!"hypothesis"],
   [w!"by", w!"induction", w!"hypothesis"], [w!"by", w!"the", w!"induction", w!"assumption"]]

/-- Discourse markers have no content of their own (`For the minimum` sets a topic). -/
inductive Topic where
  | none | maximum | minimum
  deriving DecidableEq, Repr, Lean.ToExpr

/-- An item label in parentheses at the start of a sentence (`(i)`, `(iv)`, `(b)`): the
part of a proof that the sentence begins. -/
def itemLabel (cs : List Chunk) : Option (List Chunk) :=
  match cs with
  | .p 40 :: .w l :: .p 41 :: r =>
    if !l.isEmpty && l.length ≤ 4 && l.all (fun c => [105, 118, 120].contains c || (l.length == 1 && 97 ≤ c && c ≤ 104))
    then some r else none
  | _ => none

/-- A topic that is not a binder: `For Gini's gamma,` (words), `For $\Phi^2$,`, `For $M_r$,` (a
symbol, which binds nothing). -/
def topicPhrase (cs : List Chunk) : Option (List Chunk) := do
  let r ← kw [w!"for"] cs
  match r with
  | .m ts :: .p 44 :: r' =>
    -- (a formula that names a symbol: no relation, no membership)
    match Math.parseFormula ts with
    | some (.id _) | some (.sub _ _) | some (.sup _ _) => some r'
    -- `For $t=1$,` before claims that speak of the value itself (`Q_1`)
    | some (.chain (.id _) [(.eq, .num _)]) => some r'
    | _ => none
  | .w w0 :: _ =>
    if [w!"every", w!"all", w!"each", w!"any", w!"some", w!"a", w!"an", w!"the", w!"no", w!"both",
        w!"example", w!"instance"].contains w0 then none else
    let ws := r.takeWhile (fun c => match c with | .w _ => true | _ => false)
    match r.drop ws.length with
    | .p 44 :: r' => if ws.length ≤ 4 then some r' else none
    | _ => none
  | _ => none

/-- `With the Markov operator $\frac{r+g}2\id+\frac{r-g}2J$ of $C_{r,g}$,`: a reason in words
(with formulas that state nothing) before the claims; it asserts nothing. -/
def withReason (cs : List Chunk) : Option (List Chunk) := do
  let r ← kw [w!"with"] cs
  let ws := r.takeWhile descChunk
  let nw := (ws.filter fun c => match c with | .w _ => true | _ => false).length
  if nw < 2 then none else
  match r.drop ws.length with
  | .p 44 :: r' => some r'
  | _ => none

def marker (cs : List Chunk) : Topic × List Chunk :=
  let cs := (itemLabel cs).getD cs
  let cs := (topicPhrase cs).getD cs
  let cs := (withReason cs).getD cs
  let cs := (showsThat cs).getD cs
  match kw [w!"for", w!"the", w!"minimum"] cs with
  | some r => (.minimum, optPunct 44 r)
  | none =>
  match kw [w!"for", w!"the", w!"maximum"] cs with
  | some r => (.maximum, optPunct 44 r)
  | none =>
    -- up to two markers in a row (`Hence, it follows that`)
    let one (cs : List Chunk) : Option (List Chunk) := wMarkers.findSome? fun m => (kw m cs).map (optPunct 44 ·)
    let tryAll (_ : List (List Codes)) : Topic × List Chunk :=
      match one cs with
      | some r => (.none, (one r).getD r)
      | none => (.none, cs)
    -- a topic in words only: `For the second region, whose boundary has two regimes,`
    match kw [w!"for", w!"the"] cs with
    | some r =>
      match wordsTo r with
      | some r' => (.none, r')
      | none => tryAll wMarkers
    | none =>
      -- a purpose: `To describe the supporting lines of the region,`
      match purpose cs with
      | some r => (.none, r)
      | none => tryAll wMarkers
where
  /-- `To WORDS,` with at least two words. -/
  purpose (cs : List Chunk) : Option (List Chunk) := do
    let r ← kw [w!"to"] cs
    let ws := r.takeWhile (fun c => match c with | .w _ => true | _ => false)
    if ws.length < 2 then none else
    match r.drop ws.length with
    | .p 44 :: r' => some r'
    | _ => none
  /-- Words up to a comma, then relative clauses `whose|which|where WORDS,`. -/
  wordsTo (cs : List Chunk) : Option (List Chunk) :=
    let ws := cs.takeWhile (fun c => match c with | .w _ => true | _ => false)
    if ws.isEmpty then none else
    match cs.drop ws.length with
    | .p 44 :: r =>
      match r with
      | .w v :: r' =>
        if v == w!"whose" || v == w!"which" || v == w!"where" then
          let ws' := r'.takeWhile (fun c => match c with | .w _ => true | _ => false)
          match r'.drop ws'.length with
          | .p 44 :: r'' => if ws'.isEmpty then none else some r''
          | _ => none
        else some r
      | _ => some r
    | _ => none

inductive Bind where
  | every (vars : List Codes) (dom : MT)
  | noun (np : List Chunk)
  | on (dom : MT)
  /-- `If $φ$, then …`: the free variables of `φ` range over the real numbers
  subject to `φ`. -/
  | ifCond (cond : MT)
  /-- `For $x\in A$ and $y\in B$,`. -/
  | many (bs : List Bind)
  /-- A binder written as a hypothesis (`If $n$ is an even integer,`, `If $a$ and $b$ are
  positive,`): about variables that are already bound, the hypothesis that they are as it
  says; otherwise the binder. -/
  | hyp (b : Bind)
  deriving Repr, Inhabited, Lean.ToExpr

/-- Further `and $y\in B$` after a binder. -/
def moreAnd : Nat → List Chunk → List Bind → List Bind × List Chunk
  | 0, cs, acc => (acc.reverse, cs)
  | f + 1, cs, acc =>
    match (do
        let r ← kw [w!"and"] cs
        let (ts, r') ← mathChunk r
        let (vs, dom) ← binderMath ts
        some (Bind.every vs dom, r')) with
    | some (b, r) => moreAnd f r (b :: acc)
    | none => (acc.reverse, cs)

/-- `with $φ$ [and $ψ$]` or `such that $φ$` after a binder: conditions on its variables. -/
def withConds (cs : List Chunk) : Option (MT × List Chunk) := do
  let r ← kw [w!"with"] cs <|> kw [w!"such", w!"that"] cs
  let (m, r1) ← formula r
  -- `with $φ$, $ψ$, or $χ$`, `with $φ$ or $ψ$`: one of the conditions
  let rec orList : Nat → List MT → List Chunk → Option (List MT × List Chunk)
    | 0, _, _ => none
    | f + 1, acc, r =>
      match kw [w!"or"] r <|> (punct 44 r >>= kw [w!"or"]) with
      | some r' => do let (m', r'') ← formula r'; some ((m' :: acc).reverse, r'')
      | none => do
        let r' ← punct 44 r
        let (m', r'') ← formula r'
        orList f (m' :: acc) r''
  match orList 6 [m] r1 with
  | some (ms, r3) => some (ms.tail.foldl (fun a b => MT.lor a b) (ms.headD m), r3)
  | none =>
  match (do let r2 ← kw [w!"and"] r1; formula r2) with
  | some (m2, r3) => some (.conj [m, m2], r3)
  | none => some (m, r1)

/-- A binder followed by optional conditions. -/
def withBind (b : Bind) (cs : List Chunk) : Bind × List Chunk :=
  match withConds cs with
  | some (c, r) => (.many [b, .ifCond c], r)
  | none => (b, cs)

/-- A chain of smallness conditions `0<a\ll b\ll 1` (also `C^{-1}\ll …`): the variables
from right to left, each after a threshold `@c…` that is existential (there is a
threshold such that the claim holds for every value below it). `a\ll b` is `a<c\,b`;
`C^{-1}\ll b` is `C>1/(c\,b)`. The rightmost term bounds the last variable and may use
the variables bound before. -/
def smallBinder (ts : List MTok) : Option Bind := do
  let inf : MT := .id w!"\\infty"
  let m ← Math.parseFormula ts
  let (elems, rels) ← match m with
    | .chain x rs => some (x :: rs.map (·.2), rs.map (·.1))
    | _ => none
  if !rels.contains .ll then none else
  -- an optional `0<` in front
  let (elems, rels) := match elems, rels with
    | .num 0 :: es, .lt :: rs => (es, rs)
    | _, _ => (elems, rels)
  if !rels.all (· == .ll) || elems.length < 2 then none else
  let named : MT → Option (Codes × Bool) := fun e => match e with
    | .id x => some (x, false)
    | .sub (.id k) (.id i) => some (k ++ [95] ++ i, false)
    | .sup (.id x) (.neg (.num 1)) => some (x, true)
    | _ => none
  -- (variable, inverse?, the term it is small against), from right to left
  let rec pairs : List MT → List (Codes × Bool × MT) → Option (List (Codes × Bool × MT))
    | [_], acc => some acc
    | a :: b :: rest, acc => do
      let (x, inv) ← named a
      pairs (b :: rest) ((x, inv, b) :: acc)
    | [], acc => some acc
  let ps ← pairs elems []
  some (.many (ps.flatMap fun (x, inv, b) =>
    let c := w!"@c" ++ x
    -- the bound refers to the variable's own value when the term is an inverse
    let bound : MT := match b with
      | .sup (.id y) (.neg (.num 1)) => .frac (.num 1) (.id y)
      | _ => b
    [Bind.every [c] (.ival (.num 0) inf true true),
     Bind.every [x] (if inv then .ival (.frac (.num 1) (.mul (.id c) bound)) inf true true
       else .ival (.num 0) (.mul (.id c) bound) true true)]))

/-- A name for the tokens of a variable (`n`, `\varepsilon`, `s_0`). -/
def toksName (ts : List MTok) : Codes :=
  ts.flatMap fun t => match t with
    | .id c => c
    | .cmd c => 92 :: c
    | .digit d => [48 + d]
    | .sym s => [s]
    | .lb => [123]
    | .rb => [125]
    | _ => []

/-- `sufficiently large|small [fixed] [NP] $v$`, `large|small enough …`: there is a threshold
(`@N…` for a large `v`, `@d…>0` for a small one) such that the rest holds for every `v`
beyond it: `v\ge N`, or `0<v<d` (also `0\le v<d`). A small variable must be bounded below
by `0` (`$\varepsilon>0$`, or the word `positive`). -/
def sufficientBinder (cs : List Chunk) : Option (Bind × List Chunk) := do
  let (large, r) ← ((kw [w!"sufficiently", w!"large"] cs <|> kw [w!"large", w!"enough"] cs).map (true, ·)) <|>
    ((kw [w!"sufficiently", w!"small"] cs <|> kw [w!"small", w!"enough"] cs).map (false, ·))
  let r := (kw [w!"fixed"] r).getD r
  let ws := r.takeWhile fun c => match c with | .w _ | .p 45 => true | _ => false
  let (ts, r') ← mathChunk (r.drop ws.length)
  let isName (xs : List MTok) : Bool := !xs.isEmpty && xs.all fun t => match t with
    | .id _ | .digit _ | .sym 95 | .lb | .rb => true
    | .cmd c => Math.greekNames.contains c
    | _ => false
  let positive := ws.any fun c => match c with | .w w => w == w!"positive" | _ => false
  -- the variable, and whether `0\le v` (rather than `0<v`) bounds it
  let (v, closed) ← match ts.reverse with
    | .digit 0 :: .sym 62 :: rv => if isName rv.reverse then some (rv.reverse, false) else none
    | .digit 0 :: .cmd g :: rv =>
      if (g == w!"ge" || g == w!"geq") && isName rv.reverse then some (rv.reverse, true) else none
    | _ => match ts with
      | .digit 0 :: .sym 60 :: v => if isName v then some (v, false) else none
      | .digit 0 :: .cmd l :: v => if (l == w!"le" || l == w!"leq") && isName v then some (v, true) else none
      | _ => if isName ts then some (ts, false) else none
  let bounded := v.length != ts.length || positive
  let name := toksName v
  let inf : MT := .id w!"\\infty"
  if large then
    if v.length != ts.length then none else
    let t := w!"@N" ++ name
    -- (an index name without a noun is an integer, as in `\lim_{n\to\infty}`)
    let index := match v with | [.id n] => Math.indexNames.contains n | _ => false
    let vb : Bind := if ws.isEmpty then
        (if index then .every [name] (.setOf (.id name) (.id w!"\\mathbb{Z}") [.chain (.id name) [(.ge, .id t)]])
        else .every [name] (.ival (.id t) inf false true))
      else .noun (ws ++ [.m (v ++ [.cmd w!"ge", .id t])])
    some (.many [.every [t] (.id w!"\\mathbb{R}"), vb], r')
  else
    if !bounded then none else
    let t := w!"@d" ++ name
    let vb : Bind := if ws.isEmpty then .every [name] (.ival (.num 0) (.id t) (!closed) true)
      else .noun (ws ++ [.m ([.digit 0, if closed then .cmd w!"le" else .sym 60] ++ v ++ [.sym 60, .id t])])
    some (.many [.every [t] (.ival (.num 0) inf true true), vb], r')

/-- The tokens of a name (`Q`, `\nu`, `N_0`, `c_k`). -/
def nameToks : MT → Option (List MTok)
  | .id v => some (match v with | 92 :: c => [.cmd c] | _ => [.id v])
  | .sub (.id k) (.num n) =>
    some ([.id k, .sym 95] ++ (if n < 10 then [.digit n] else [.lb] ++ (Nat.toDigits 10 n).map (fun c => MTok.digit (c.toNat - 48)) ++ [.rb]))
  | .sub (.id k) (.id i) => some ([.id k, .sym 95] ++ (match i with | 92 :: c => [.cmd c] | _ => [.id i]))
  | _ => none

/-- The key of a name (`Q`, `N_0`, `c_k`). -/
def nameKey : MT → Option Codes
  | .id v => some v
  | .sub (.id k) (.num n) => some (k ++ [95] ++ (Nat.toDigits 10 n).map Char.toNat)
  | .sub (.id k) (.id i) => some (k ++ [95] ++ i)
  | _ => none

/-- A constant whose name states what it depends on: `Q(\nu)`, `Q=Q(\nu)`, `c(C)>0`,
`w_0=w_0(d,\kappa)>0`. The constant (`Q`, with its bound) and the pair of the name and the
symbol. -/
def depBinder (ts : List MTok) : Option (List MTok × MT × MT × List (Rel × MT)) := do
  let m ← Math.parseFormula ts
  let isName (x : MT) : Bool := match x with
    | .id _ | .sub (.id _) (.num _) | .sub (.id _) (.id _) => true
    | _ => false
  let dep (x : MT) : Option (MT × MT) := match x with
    | .app nm args => if isName nm && !args.isEmpty && args.all isName then some (x, nm) else none
    | _ => none
  let ((al, nm), rest) ← match m with
    | .app .. => do let a ← dep m; some (a, [])
    | .chain x rs =>
      match dep x, rs with
      | some a, _ => some (a, rs)
      | none, (.eq, y) :: rs' => do
        let a ← dep y
        if (nameKey a.2).isSome && nameKey a.2 == nameKey x then some (a, rs') else none
      | none, _ => none
    | _ => none
  let toks ← nameToks nm
  some (toks, al, nm, rest)

/-- The variable before `sufficiently large|small`: `$n$ [is] sufficiently large`, `$n$ [is] large
enough`, `$n$ is a sufficiently large integer`, `$\varepsilon>0$ is sufficiently small`; as
`sufficientBinder`. -/
def postSufficient (cs : List Chunk) : Option (Bind × List Chunk) := do
  let (ts, r) ← mathChunk cs
  let r := (kw [w!"is"] r <|> kw [w!"are"] r).getD r
  let size (r : List Chunk) : Option (Codes × List Chunk) :=
    ((kw [w!"sufficiently", w!"large"] r <|> kw [w!"large", w!"enough"] r).map (w!"large", ·)) <|>
    ((kw [w!"sufficiently", w!"small"] r <|> kw [w!"small", w!"enough"] r).map (w!"small", ·))
  (do
    -- `is a sufficiently large integer`
    let r1 ← kw [w!"a"] r <|> kw [w!"an"] r
    let (s, r2) ← size r1
    let ws := r2.takeWhile fun c => match c with
      | .w w => ![w!"then", w!"and", w!"such", w!"with", w!"we"].contains w
      | .p 45 => true
      | _ => false
    if ws.isEmpty then none else
    let (b, _) ← sufficientBinder ([.w w!"sufficiently", .w s] ++ ws ++ [.m ts])
    some (b, r2.drop ws.length)) <|> do
  let (s, r1) ← size r
  let (b, _) ← sufficientBinder [.w w!"sufficiently", .w s, .m ts]
  some (b, r1)

/-- `, $ψ$, or $χ$` or ` or $χ$` after a condition `with $φ$`: the further conditions, of
which one holds (the chunks, and the rest). -/
def orTail : Nat → List Chunk → List Chunk → Option (List Chunk × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc =>
    match cs with
    | .w o :: .m m :: rest => if o == w!"or" then some ((acc.reverse ++ [.w o, .m m]), rest) else none
    | .p 44 :: .w o :: .m m :: rest => if o == w!"or" then some ((acc.reverse ++ [.p 44, .w o, .m m]), rest) else none
    | .p 44 :: .m m :: rest => orTail f rest (.m m :: .p 44 :: acc)
    | _ => none

/-- A noun phrase of a binder, up to a comma, `and every|each|all`, `and $…$`, or `there`. -/
def npUpTo : Nat → List Chunk → List Chunk → List Chunk × List Chunk
  | 0, cs, acc => (acc.reverse, cs)
  | _ + 1, [], acc => (acc.reverse, [])
  | f + 1, c :: rest, acc =>
    let stop := match c with
      | .p 44 => true
      | .w w => w == w!"there"
      | _ => false
    let andNext := match c, rest with
      | .w a, .w e :: _ => a == w!"and" && (e == w!"every" || e == w!"each" || e == w!"all")
      | .w a, .m _ :: _ => a == w!"and"
      | _, _ => false
    if stop || andNext then (acc.reverse, c :: rest) else npUpTo f rest (c :: acc)

/-- `(a_n)`: the name of a sequence, by its terms. -/
def seqParenName (n : List MTok) : Bool :=
  n.head? == some (.sym 40) && n.getLast? == some (.sym 41) && n.length ≥ 5 &&
    (n.drop 1).dropLast.contains (.sym 95) && (n.drop 1).dropLast.all fun t => match t with
      | .id _ | .digit _ | .sym 95 | .lb | .rb => true
      | .cmd c => Math.greekNames.contains c
      | _ => false

/-- The variables of `a,b`, `a,b\ge1` or `c_1,c_2>0`, each with the bound written after the
last (`a\ge1`, `b\ge1`). -/
def splitVars (ts : List MTok) : Option (List (List MTok)) := do
  let parts := (Math.commaParts (ts.length + 1) 0 [] ts []).filter (!·.isEmpty)
  if parts.length < 2 then none else
  let last ← parts.getLast?
  let i := (last.findIdx? fun t => (Math.relOf t).isSome).getD last.length
  let (lastName, suffix) := (last.take i, last.drop i)
  let names := parts.dropLast ++ [lastName]
  -- (each is the name of one variable: no relation, no operation)
  if names.any (fun n => n.isEmpty || (!seqParenName n && n.any fun t => match t with
      | .id _ | .digit _ | .sym 95 | .lb | .rb => false
      | .cmd c => !Math.greekNames.contains c
      | _ => true)) then none
  else some (names.map (· ++ suffix))

/-- The variables of `$x$ and $y$`, `$x$, $y$ and $z$` (each formula the name of one
variable), joined as `x,y,z`; any other formula is returned as it is. -/
def joinedVars (cs : List Chunk) : Option (List MTok × List Chunk) := do
  let (ts, r) ← mathChunk cs
  let isName (n : List MTok) : Bool := seqParenName n || (!n.isEmpty && n.all fun t => match t with
    | .id _ | .digit _ | .sym 95 | .lb | .rb => true
    | .cmd c => Math.greekNames.contains c
    | _ => false)
  let rec go : Nat → List MTok → List Chunk → List MTok × List Chunk
    | 0, acc, r => (acc, r)
    | f + 1, acc, r =>
      match (punct 44 r >>= kw [w!"and"]) <|> kw [w!"and"] r <|> punct 44 r with
      | some (.m b :: r2) => if isName b then go f (acc ++ [.sym 44] ++ b) r2 else (acc, r)
      | _ => (acc, r)
  if isName ts then some (go 8 ts r) else some (ts, r)

/-- One binder after `for every|each|all`: a smallness chain, `$x\in A$` (with
conditions), or `NP $x$` (`For every LTD copula $C$`, as `For an LTD copula $C$`). -/
def everyOne (r : List Chunk) : Option (Bind × List Chunk) :=
  sufficientBinder r <|>
  (do
    let (ts, r') ← mathChunk r
    let b ← smallBinder ts
    some (b, r')) <|>
  (do
    let (ts, r') ← mathChunk r
    let (vs, dom) ← binderMath ts
    some (withBind (.every vs dom) r')) <|>
  (do
    -- `all integers $a,b\ge1$`, `all positive integers $a$ and $b$`: a binder for each
    let (np, r') := npUpTo (r.length + 1) r []
    let ws0 := np.takeWhile fun c => match c with | .w _ => true | _ => false
    -- `all distinct primes $p,q$`: a condition on all of them
    let (ws, ps) := collectiveWords 8 ws0
    if ws.isEmpty then none else
    let (vars, conds, r'') : List (List MTok) × List Bind × List Chunk ← match np.drop ws0.length, r' with
      | [.m [a]], .w w :: .m [b] :: r'' => if w == w!"and" then some ([[a], [b]], [], r'') else none
      -- `all real numbers $a$, $b$ and $c$`: names separated by commas, the last after `and`
      | [.m [a]], .p 44 :: rest =>
        let rec names : Nat → List Chunk → List (List MTok) → Option (List (List MTok) × List Chunk)
          | 0, _, _ => none
          | f + 1, cs, acc =>
            match cs with
            | .m [b] :: .p 44 :: .w w :: .m [c] :: r => if w == w!"and" then some ((acc ++ [[b], [c]]), r) else none
            | .m [b] :: .w w :: .m [c] :: r => if w == w!"and" then some ((acc ++ [[b], [c]]), r) else none
            | .m [b] :: .p 44 :: r => names f r (acc ++ [[b]])
            | _ => none
        let isName (t : MTok) : Bool := match t with | .id _ => true | .cmd c => Math.greekNames.contains c | _ => false
        let plural := match ws.getLast? with
          | some (.w w) => w.getLast? == some 115
          | _ => false
        if !plural || !isName a then none else
        let (vs, r'') ← names 8 rest [[a]]
        if !(vs.all fun v => match v with | [t] => isName t | _ => false) then none else
        some (vs, [], r'')
      | [.m ts], _ => ((seqBound ts).map fun _ => ([ts], [], r')) <|> (splitVars ts).map (·, [], r') <|>
        -- `all integers $n\ge k\ge0$`: the variables of the chain, and the chain (after a
        -- plural noun; `every integer $b\ge c$` bounds `b` by `c`)
        (do
          let plural := match ws.getLast? with
            | some (.w w) => w.getLast? == some 115
            | _ => false
          if !plural then none
          let m ← Math.parseFormula ts
          let .chain (.id x) rest := m | none
          let ys ← rest.mapM fun (_, y) => match y with
            | .id y => some (some y)
            | .num _ => some none
            | _ => none
          let ys := ys.filterMap id
          if ys.isEmpty then none
          some ((x :: ys).map fun n => [MTok.id n], [Bind.ifCond m], r'))
      -- `all real numbers $x,y$ with $y\ne0$`: a condition on all of them
      | .m ts :: post, _ => do
        let (c, rest) ← withConds post
        if !rest.isEmpty then none else
        let vars ← ((seqBound ts).map fun _ => [ts]) <|> splitVars ts
        some (vars, [Bind.ifCond c], r')
      | _, _ => none
    let together : List Bind ← if ps.isEmpty then some [] else (collectiveCond ps vars).map ([.ifCond ·])
    some (Bind.many (vars.map (fun v => Bind.noun (ws ++ [.m v])) ++ together ++ conds), r'')) <|>
  (do
    -- `every sequence $x$ in $[0,1]$`, `every probability measure $\gamma$ on $[0,1]^2$`: a
    -- noun of the vocabulary with its variable inside the phrase
    let (np, r') := npUpTo (r.length + 1) r []
    let ws := np.takeWhile fun c => match c with | .w _ => true | _ => false
    match ws.isEmpty, np.drop ws.length with
    | false, [.m [.id _], .w p, .m _] | false, [.m [.cmd _], .w p, .m _] =>
      if p == w!"in" || p == w!"on" then some (.noun np, r') else none
    | _, _ => none) <|>
  (do
    let (np, r') := npUpTo (r.length + 1) r []
    match np.head?, np.getLast? with
    | some (.w _), some (.m [.id _]) | some (.w _), some (.m [.cmd _]) => some (.noun np, r')
    -- `every integer $n\ge1$`, `every integer $n$ with $n\ge1$`: one variable with a bound
    | some (.w _), some (.m ts) =>
      -- (`every continuous map $f\colon X\to Y$`: a map with its signature)
      if (Math.parseSig ts).isSome then some (.noun np, r') else
      match binderMath ts, hatName ts with
      | some ([_], _), _ | _, some (_, []) => some (.noun np, r')
      -- `every integer $n_0$`
      | _, _ =>
        if subName ts then some (.noun np, r') else
        -- `every copula $C$ with maximal correlation $R=R(C)$`
        match Math.parseFormula ts with
        | some (.chain (.id x) [(.eq, .app (.id y) _)]) => if x == y then some (.noun np, r') else none
        -- `every prime $p\equiv1\pmod4$`: the variable, and its congruence
        | some (m@(.chain (.id x) [(.equiv, _)])) =>
          -- (`every prime $p$ with $p\equiv1\pmod4$`: the noun phrase before `with`)
          let base := match np.dropLast.reverse with
            | .w w :: rest => if w == w!"with" then rest.reverse else np.dropLast ++ [.m [.id x]]
            | _ => np.dropLast ++ [.m [.id x]]
          some (.many [.noun base, .ifCond m], r')
        | _ =>
          -- `every copula $C$ with $C^\top=C$`: a condition on the variable
          let withAt := np.findIdx? fun c => match c with | .w v => v == w!"with" | _ => false
          match withAt with
          | some i =>
            match np.drop (i + 1), np[i - 1]? with
            | [.m _], some (.m v) =>
              if i ≥ 2 && (v.length == 1 || subName v) then
                -- `with $φ$, $ψ$, or $χ$`: one of the conditions
                match orTail 6 r' [] with
                | some (tl, r'') => some (.noun (np ++ tl), r'')
                | none => some (.noun np, r')
              else none
            | _, _ => none
          | none => none
    | _, _ => none) <|>
  (do
    -- `every graph $G$ on $n$ vertices`, `every matrix $A$ of size $n\times n$`: the variable,
    -- then a phrase with numbers (a modifier of the vocabulary with arguments)
    let (np, r') := npUpTo (r.length + 1) r []
    let ws := np.takeWhile fun c => match c with | .w _ => true | _ => false
    match np.drop ws.length with
    | .m v :: .w p :: post =>
      let isVar := match v with | [.id _] | [.cmd _] => true | _ => subName v
      if ws.isEmpty || !isVar || [w!"satisfies", w!"obeys", w!"is", w!"are", w!"has", w!"have", w!"such", w!"there",
          w!"we", w!"and", w!"for", w!"where", w!"which", w!"that"].contains p then none else
      if !post.any (fun c => match c with | .m _ => true | _ => false) then none else
      -- (`with $φ$` alone is a condition, read above)
      if p == w!"with" && post.length == 1 then none else
      some (.noun np, r')
    | _ => none)

/-- `every $k$-regular graph $G$`, `every $n\times n$ matrix $A$`: a formula before the noun
(the argument of a modifier of the vocabulary), then a binder of `everyOne`. -/
def everyLead (r : List Chunk) : Option (Bind × List Chunk) :=
  match r with
  | .m t :: .p 45 :: rest@(.w _ :: _) =>
    match everyOne rest with
    | some (.noun np, r') => some (.noun ([.m t, .p 45] ++ np), r')
    | _ => none
  | .m t :: rest@(.w _ :: _) =>
    if !t.contains (.cmd w!"times") then none else
    match everyOne rest with
    | some (.noun np, r') => some (.noun (.m t :: np), r')
    | _ => none
  | _ => none

/-- The variables that a binder of a `for every` list binds, as far as its words show them:
those of a formula binder and of the first formula of a noun phrase. -/
def shallowVars (b : Bind) : List Codes :=
  let one (b : Bind) : List Codes := match b with
    | .every vs _ => vs
    | .noun np => match np.find? (fun c => match c with | .m _ => true | _ => false) with
      | some (.m ts) => ((splitVars ts).map (·.map toksName) <|> (binderMath ts).map (·.1)).getD [toksName ts]
      | _ => []
    | _ => []
  match b with
  | .many bs => bs.flatMap one
  | b => one b

/-- Further binders: `and every NP $y$`, `and $y\in B$`. A formula after `and` about
variables that the list has already bound (`for every integer $x$ with $x>1$ and $x<5$`) is
a condition on them, not a new variable with the same letter. -/
def everyMore : Nat → List Chunk → List Bind → List Bind × List Chunk
  | 0, cs, acc => (acc.reverse, cs)
  | f + 1, cs, acc =>
    let seen := acc.flatMap shallowVars
    match (do
        let r ← kw [w!"and"] cs
        let (ts, r') ← mathChunk r
        let (vs, _) ← binderMath ts
        if vs.isEmpty || !vs.all seen.contains then none else
        let φ ← Math.parseFormula ts
        some (Bind.ifCond φ, r')) with
    | some (b, r) => everyMore f r (b :: acc)
    | none =>
    let next := (kw [w!"and", w!"every"] cs <|> kw [w!"and", w!"each"] cs <|> kw [w!"and", w!"all"] cs <|>
      (do let r ← kw [w!"and"] cs; match r with | .m _ :: _ => some r | _ => none) <|>
      -- `For every $k$, every $N$ and every $x$`
      (do let r ← punct 44 cs; kw [w!"every"] r <|> kw [w!"each"] r <|> kw [w!"and", w!"every"] r))
    match next.bind (fun r => everyOne r <|> everyLead r) with
    | some (b, r) => everyMore f r (b :: acc)
    | none => (acc.reverse, cs)

/-- The binders after `for every|each|all`: one, or several joined by `and [every]`. -/
def everyBinders (r : List Chunk) : Option (Bind × List Chunk) :=
  -- (a binder with conditions is itself several: they are flattened)
  let flat (b : Bind) : List Bind := match b with | .many bs => bs | _ => [b]
  match everyOne r <|> everyLead r with
  | some (b, r') =>
    match everyMore 4 r' [b] with
    | ([_], _) => some (b, r')
    | (bs, r'') => some (.many (bs.flatMap flat), r'')
  | none => none

/-- `positive integers` after the variables `ts` of `$a,b$ are` (`be`), possibly with
conditions (`with $a<b$`): a binder for each variable (a sequence `x_1,\ldots,x_n` is one),
then the conditions. -/
def pluralNoun0 (ts : List MTok) (r : List Chunk) : Option (Bind × List Chunk) := do
  let vars ← ((seqBound ts).map fun _ => [ts]) <|> splitVars ts
  let r := normIID r
  -- (a singular noun is read where its variable is)
  if (kw [w!"a"] r).isSome || (kw [w!"an"] r).isSome then none else
  -- (`$n\times n$ matrices`, `$k$-regular graphs`: a formula before the noun)
  -- (after adjectives too: `invertible $n\times n$ matrices`)
  let adjs := r.takeWhile fun c => match c with
    | .w w => ![w!"with", w!"such", w!"then", w!"and", w!"of", w!"in", w!"on"].contains w
    | _ => false
  let lead : List Chunk := match r.drop adjs.length with
    | .m t :: .p 45 :: .w _ :: _ => adjs ++ [.m t, .p 45]
    | .m t :: .w w :: _ => if t.contains (.cmd w!"times") || w == w!"times" then adjs ++ [.m t] else []
    | _ => []
  let r := r.drop lead.length
  let ws := r.takeWhile fun c => match c with
    | .w w => w != w!"with" && w != w!"such" && w != w!"then" && w != w!"and"
    | .p 45 => true
    | _ => false
  let r1 := r.drop ws.length
  -- (`graphs on $n$ vertices`, `polynomials of degree $n$`: a phrase with a number after
  -- the noun, which follows the variable)
  let preps := [w!"on", w!"of", w!"in", w!"over", w!"to", w!"from"]
  let prepAt := (ws.zipIdx.filter fun (c, _) => match c with | .w w => preps.contains w | _ => false).getLast?.map (·.2)
  let slotted : Option (List Chunk × List Chunk × List Chunk) := match prepAt, r1 with
    | some i, .m t :: more =>
      if i == 0 then none else
      let after := more.takeWhile fun c => match c with
        | .w w => !([w!"with", w!"such", w!"then", w!"and", w!"satisfying", w!"that", w!"which", w!"whose", w!"where"].contains w)
        | _ => false
      some (ws.take i, ws.drop i ++ [.m t] ++ after, more.drop after.length)
    | _, _ => none
  if let some (head, tailPhrase, r2) := slotted then
    let (head, ps) := collectiveWords 8 head
    let together : List Bind ← if ps.isEmpty then some [] else (collectiveCond ps vars).map ([.ifCond ·])
    let nouns := vars.map fun v => Bind.noun (lead ++ head ++ [.m v] ++ tailPhrase)
    return (match withConds r2 with
      | some (c, r3) => (.many (nouns ++ together ++ [.ifCond c]), r3)
      | none => (.many (nouns ++ together), r2))
  -- `distinct`, `relatively prime`: a condition on all of them
  let (ws, ps) := collectiveWords 8 ws
  let together : List Bind ← if ps.isEmpty then some [] else (collectiveCond ps vars).map ([.ifCond ·])
  -- `$v,w\in A$ are distinct`: the variables of their domain, together
  if ws.isEmpty then
    if together.isEmpty then none else
    let (vs, d) ← binderMath ts
    return (.many (.every vs d :: together), r1)
  -- `$f$ and $g$ be probability densities with finite mean`: words after the noun (a
  -- modifier of the vocabulary), said of each of them
  -- (also with formulas, `with mean $\mu$ and variance $\sigma^2$`; not `and let`)
  let rec postOf : Nat → List Chunk → List Chunk
    | 0, _ => []
    | k + 1, cs => match cs with
      | .w a :: rest@(.w n :: _) =>
        if a == w!"and" then (if n == w!"let" || n == w!"then" then [] else .w a :: postOf k rest)
        else if a == w!"then" || a == w!"such" then [] else .w a :: postOf k rest
      | .w a :: rest => if a == w!"and" || a == w!"then" || a == w!"such" then [] else .w a :: postOf k rest
      | .m t :: rest => .m t :: postOf k rest
      | .p 45 :: rest => .p 45 :: postOf k rest
      | _ => []
  let post : List Chunk := match r1 with
    | .w w :: .w _ :: _ =>
      if w != w!"with" then [] else postOf (r1.length + 1) r1
    | _ => []
  let r1 := r1.drop post.length
  let nouns := vars.map fun v => Bind.noun (lead ++ ws ++ [.m v] ++ post)
  match withConds r1 with
  | some (c, r2) => some (.many (nouns ++ together ++ [.ifCond c]), r2)
  | none => some (.many (nouns ++ together), r1)


/-- `positive integers` after the variables of `$a,b$ are` (`pluralNoun0`); and after a chain
of inclusions, `Let $K\subseteq L\subseteq M$ be fields`: a binder for each variable, then the
chain as a condition on them. -/
def pluralNoun (ts : List MTok) (r : List Chunk) : Option (Bind × List Chunk) :=
  pluralNoun0 ts r <|> (do
    let m ← Math.parseFormula ts
    let .chain (.id a) rels := m | none
    if rels.isEmpty || !(rels.all fun (rel, _) => rel == .subset) then none
    let names ← rels.mapM fun (_, y) => match y with | .id b => some b | _ => none
    let vs := a :: names
    let joined : List MTok := (vs.map fun v => [MTok.id v]).intersperse [MTok.sym 44] |>.flatten
    let (b, r') ← pluralNoun0 joined r
    let bs := match b with | .many bs => bs | b => [b]
    some (.many (bs ++ [.ifCond m]), r'))
/-- Does a further formula follow (`, $ψ$`, `, and $χ$`, `and $χ$`)? -/
def moreFormulas (r : List Chunk) : Bool :=
  let r := (punct 44 r).getD r
  let r := (kw [w!"and"] r).getD r
  match r with
  | .m _ :: _ | .d _ _ :: _ => true
  | _ => false

/-- Sentence-initial binders: `For every $x\in A$,` `For $x\in A$,` `For a NP,`
`For every NP $x$,` `On $I$,`. -/
def binder (cs : List Chunk) : Option (Bind × List Chunk) :=
  match (kw [w!"for", w!"every"] cs <|> kw [w!"for", w!"each"] cs), kw [w!"for", w!"all"] cs with
  | some r, _ | none, some r =>
    everyBinders r
  | none, none =>
    match kw [w!"for", w!"a"] cs, kw [w!"for", w!"an"] cs with
    | some r, _ | none, some r =>
      let np := r.takeWhile (fun c => match c with | .p 44 => false | _ => true)
      some (.noun np, r.drop np.length)
    | none, none =>
      match kw [w!"for"] cs with
      | some r => sufficientBinder r <|> postSufficient r <|> (do
          let (ts, r') ← mathChunk r
          let b ← smallBinder ts
          some (b, r')) <|> do
        let (ts, r') ← mathChunk r
        let (vs, dom) ← binderMath ts
        match moreAnd 4 r' [] with
        | ([], _) => some (withBind (.every vs dom) r')
        | (bs, r'') => some (.many (.every vs dom :: bs), r'')
      | none =>
        match kw [w!"on"] cs with
        | some r => do
          let (m, r') ← formula r
          some (.on m, r')
        | none =>
          match kw [w!"if"] cs <|> kw [w!"whenever"] cs <|> kw [w!"provided", w!"that"] cs with
          | some r =>
            -- `If $n$ is sufficiently large,`
            postSufficient r <|>
            -- `If $a,b$ are positive integers,`, `If $a$ and $b$ are …`,
            -- `If $a_1,\ldots,a_k$ are nonnegative integers with $φ$,`
            (do
              let (ts, r1) ← joinedVars r
              let r2 ← kw [w!"are"] r1
              let (b, r3) ← pluralNoun ts r2
              if (punct 44 r3).isNone then none else some (.hyp b, r3)) <|>
            -- `If $C$ is an LTD copula,`: as `For an LTD copula $C$,`
            (do
              let (ts, r1) ← mathChunk r
              -- (`If $n_0$ is a positive integer,`: a name with a subscript)
              let v ← match ts with | [.id _] => some ts | _ => if subName ts then some ts else none
              let r2 ← kw [w!"is", w!"a"] r1 <|> kw [w!"is", w!"an"] r1
              let ws := r2.takeWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
              if ws.isEmpty || (punct 44 (r2.drop ws.length)).isNone then none
              else some (.hyp (.noun (ws ++ [.m v])), r2.drop ws.length)) <|>
            (do
              let (m, r') ← formula r
              -- (`If $n$ is even,`: a clause, read as a hypothesis later)
              if (kw [w!"is"] r').isSome || (kw [w!"are"] r').isSome then none else
              -- `If $x>0$ and $y>x$,`: both conditions
              let rec more : Nat → MT → List Chunk → Option (MT × List Chunk)
                | 0, m, r => some (m, r)
                | f + 1, m, r =>
                  match kw [w!"and"] r with
                  | some r1 =>
                    match formula r1 with
                    | some (m2, r2) =>
                      if (kw [w!"is"] r2).isSome || (kw [w!"are"] r2).isSome then none
                      else more f (.land m m2) r2
                    | none => some (m, r)
                  | none => some (m, r)
              let (m, r') ← more 4 m r'
              -- `If $φ$ for every $x\in A$,`: the condition binds its own variable
              match (do
                  let r1 ← kw [w!"for", w!"every"] r' <|> kw [w!"for", w!"all"] r' <|> kw [w!"for", w!"each"] r'
                  let (ts, r2) ← mathChunk r1
                  let (vs, d) ← binderMath ts
                  if (punct 44 r2).isNone then none else some (Bind.ifCond (.quant true vs d m), r2)) with
              | some res => some res
              | none =>
                -- (`If $f$ attains a maximum on $U$, …`: a verb after the formula begins a
                -- clause, read as a hypothesis later)
                match r' with
                | .w w :: _ => if w == w!"then" then some (.ifCond m, r') else none
                | _ => some (.ifCond m, r'))
          | none => none

inductive Subj where
  | math (m : MT)
  | its (name : List Codes)
  deriving Repr, Inhabited, Lean.ToExpr

inductive Obj where
  | math (m : MT)
  | named (name : List Codes) (m : Option MT)
  deriving Repr, Inhabited, Lean.ToExpr

inductive RelPart where
  | has (m : MT)
  | pred (phrase : List Codes) (obj : Obj)
  deriving Repr, Inhabited, Lean.ToExpr

/-- Monotonicity of a map: `non-increasing`, `non-decreasing`, `strictly increasing`,
`strictly decreasing`. (A plain `increasing` is ambiguous between the first two
readings, so the grammar does not read it.) -/
inductive Mono where
  | nonincreasing | nondecreasing | increasing | decreasing
  deriving Repr, Inhabited, DecidableEq, Lean.ToExpr

/-- `non-increasing`, `non-decreasing`, `strictly increasing`, `strictly decreasing`. -/
def monoWord (cs : List Chunk) : Option (Mono × List Chunk) :=
  ((kw [w!"non"] cs >>= punct 45 >>= kw [w!"increasing"]).map (Mono.nonincreasing, ·)) <|>
  ((kw [w!"nonincreasing"] cs).map (Mono.nonincreasing, ·)) <|>
  ((kw [w!"non"] cs >>= punct 45 >>= kw [w!"decreasing"]).map (Mono.nondecreasing, ·)) <|>
  ((kw [w!"nondecreasing"] cs).map (Mono.nondecreasing, ·)) <|>
  ((kw [w!"strictly", w!"increasing"] cs).map (Mono.increasing, ·)) <|>
  ((kw [w!"strictly", w!"decreasing"] cs).map (Mono.decreasing, ·))

inductive Clause where
  | fact (f : MT)
  | holds (f : MT)
  | exactlyOne (noun : List Codes) (v : Codes) (cond sat : MT)
  | onlyWith (s : Subj) (noun : List Codes) (conds : List MT) (var : Option Codes)
  | every (vars : List Codes) (dom body : MT)
  | extremum (isMax : Bool) (fv : MT) (s : Subj) (rels : List RelPart)
  | increases (f dom cod : MT)
  | deriv (d : MT) (positive : Bool) (cond : MT)
  | noOther (noun : List Codes) (x : MT) (isMax : Bool)
  | pred (s : Subj) (phrase : List Codes) (obj : Obj)
  | sends (map f g : MT)
  | onlyAttains (x : MT)
  /-- `φ`, possibly `for every x∈A`, possibly `with equality only at x=a`. -/
  | scoped (f : MT) (vars : List Codes) (dom : Option MT) (equalityAt : Option MT)
  /-- `every NP satisfies|obeys φ [for all $u,v\in A$]`. -/
  | everyNP (np : List Chunk) (body : MT) (inner : List Bind)
  /-- `the maximum V of F is attained only by S[, at which φ][, which RELS]`; without
  `of F` (`the minimum V only by S`), `F` is the function of the preceding extremum. -/
  | extremumOf (isMax : Bool) (value : MT) (f : Option MT) (s : Subj) (at_ : Option MT) (rels : List RelPart)
  /-- `both maps F and G are strictly increasing`. -/
  | increasing (maps : List MT)
  /-- `$a$ and $b$ are nonincreasing on $D$`: functions of one variable (after their
  parameters), monotone on `D`. -/
  | monoFns (fns : List MT) (dom : MT) (mono : Mono)
  /-- `$φ$ for $ψ$` with a condition `ψ` (`$a(v)=c$ for $v\ge\frac12$`): about variables
  bound before, the hypothesis `ψ`; otherwise its free variables range over the numbers
  with `ψ`. -/
  | forCond (f cond : MT)
  /-- `the first|second ranges over B`: the image of a map of the preceding sentence. -/
  | ranges (which : Nat) (target : MT)
  /-- `the maximum X [and the minimum Y] of F over all NOUNS $C$ with φ are each
  attained by exactly one NOUN`: each value is the extremum of `F` over the
  elements with `φ`, attained by exactly one of them. -/
  | extremaOver (items : List (Bool × MT)) (f : MT) (noun : List Codes) (v : Codes) (cond : MT)
  /-- `equality holds exactly on $S$` (after an inequality `a ≥ b` for every `x` in
  a domain): for every such `x`, `a = b` exactly when `x ∈ S`. -/
  | equalityOn (s : MT)
  /-- `equality holds exactly when $φ$`: for every `x`, `a = b ↔ φ`. -/
  | equalityWhen (φ : MT)
  /-- `if $φ$, CLAUSE`: the clause under the hypothesis `φ` about variables
  that are already bound. -/
  | ifThen (cond : MT) (c : Clause)
  /-- `if CLAUSE, [then] CLAUSE`: the clause under a hypothesis that is itself a clause
  about variables that are already bound (`if $n$ is even`, `if $a$ and $b$ are
  relatively prime`). -/
  | ifClause (hyp c : Clause)
  /-- `$X$ is ADJ, ADJ [on $A$] and ADJ`: standard properties of a number, of a set
  of points of the plane, of a real function (on its domain, or on `A`), of a
  quantity of functions on the unit square, or of a class of them. -/
  | adjectives (s : MT) (adjs : List (List Codes × Option MT))
  /-- `Both constants are sharp.`, `The bound is sharp.`: each inequality `a ≤ b` of
  the preceding claim about every element of a domain cannot be improved: for every
  `ε > 0`, some element has `b - a < ε`. -/
  | sharp
  /-- `$x$ is NAME[, NAME] and|or NAME`: notions the article defines (`disj`: `or`). -/
  | notions (s : MT) (names : List (List Codes)) (disj : Bool)
  /-- `every NP is NAME [and|or NAME]`. -/
  | everyIs (np : List Chunk) (names : List (List Codes)) (disj : Bool)
  /-- `every NP is MOD`, a modifier after the noun (`every vertex of $G$ is of even degree`,
  `every element of $G$ is of order $2$`). -/
  | everyMod (np : List Chunk) (mod : List Chunk)
  /-- `$φ$ if and only if $ψ$`. -/
  | iff (p q : MT)
  /-- `$X$ is [not] a|an NP`, `$X$ is [not] ADJ [and ADJ]`: a noun or adjectives of the
  vocabulary, about `X`. -/
  | isA (s : MT) (np : List Chunk) (neg : Bool)
  /-- `there is $C>0$ such that CLAUSE`: an existential binder. -/
  | thereIs (b : Bind) (c : Clause)
  /-- `such that, for every $b\ge b_0$, CLAUSE`: the clause for every value of the binder. -/
  | under (b : Bind) (c : Clause)
  /-- `CLAUSE for every NP $x$`: the clause for every object the noun phrase
  describes. -/
  | forEveryNP (c : Clause) (np : List Chunk)
  /-- `there is [exactly one|a unique] NP [such that CLAUSE]`. -/
  | existsNP (np : List Chunk) (unique : Bool) (c : Option Clause)
  /-- `$K$ has exactly two ideals` (`at least`, `at most`): the number of objects that the
  noun phrase (in the singular) describes, compared with `k` (`mode` 0 exactly, 1 at least,
  2 at most). `first` is the reading tried before it: a modifier of the vocabulary
  (`with at least $2$ leaves`). -/
  | countNP (np : List Chunk) (mode : Nat) (k : Nat) (first : Option Clause)
  /-- `there exist NP, NP, and NP [satisfying DISPLAY] [such that CLAUSE, …]`: objects
  with the conditions. -/
  | existsNPs (nps : List (List Chunk)) (conds : List Clause)
  /-- `there is no NP …`, `there are no NP, NP …`: no such objects exist. -/
  | noneExist (c : Clause)
  /-- `[the WORDS] $X$ is at most [the WORDS] $Y$` (at least, less than, greater than,
  equal to); either side may define its symbol (`the geometric mean $G\coloneqq\sqrt{ab}$`). -/
  | compare (lhs : MT) (rel : Rel) (rhs : MT)
  /-- The clause of `there is $Q=Q(\nu)$ such that CLAUSE`, in which `Q(\nu)` stands for
  `Q` (each pair: the name that states the dependence, and the symbol). -/
  | aliased (pairs : List (MT × MT)) (c : Clause)
  /-- `such that CLAUSE and CLAUSE`: both clauses. -/
  | both (cs : List Clause)
  /-- `CLAUSE if and only if CLAUSE`. -/
  | iffC (p q : Clause)
  /-- `CLAUSE or CLAUSE`. -/
  | orC (p q : Clause)
  /-- `there are infinitely many NPs [such that CLAUSE]`, `CLAUSE for infinitely many NPs`:
  the numbers the noun phrase (and the clause) describe are not finitely many. -/
  | infinitelyMany (np : List Chunk) (c : Option Clause)
  /-- `the equation $E$ has no solution in NOUNs` (`kind` 0), `has a solution in NOUNs` (1),
  `has infinitely many solutions in NOUNs` (2): the unknowns of `E` (its letters that nothing
  binds), each one of the numbers of the noun phrase (plural words). -/
  | solutions (kind : Nat) (eq : MT) (np : List Chunk)
  /-- The false statement (`This is a contradiction.`): under hypotheses, that they
  cannot all hold. -/
  | absurd
  /-- `$\sup A$ exists`, `$A$ has a maximum`: the term is defined. -/
  | exists_ (m : MT)
  /-- `the statement holds for $E$`, in the proof of a result: the statement of the
  result, with the variable of the induction replaced by `E` (the hypothesis of an
  induction, or its conclusion for `n+1`). -/
  | stmtAt (e : MT)
  /-- `the statement holds for all smaller values [of $n$]`, `… for all integers less than
  $n$`: the statement for every value of the variable of the induction below it (`v`: the
  variable, if the sentence names it). -/
  | stmtBelow (v : Option Codes)
  /-- `$T$ fixes the constants` (the field `hilbert`): `T` maps every constant function to
  itself, as an element of `L^2`. -/
  | fixesConsts (op : MT)
  /-- `$T$ maps $A$ into itself|$B$ [with norm $r$] [, with norm at most $c$ on it]`: `T` maps
  the functions of `A` into `B`, and its norm on `A` is `r` (at most `c`: `(true, c)`). -/
  | mapsInto (op dom cod : MT) (norm : Option (Bool × MT))
  /-- `$T$ is $c$ times the identity on $A$`: `\lVert Tg-cg\rVert = 0` for the `g` of `A`. -/
  | timesId (op c dom : MT)
  /-- `$F$ depends only on the first $m$ terms`: a function of a sequence that depends only
  on its terms `1, …, m` (the field `hilbert`). -/
  | dependsFirst (f m : MT)
  /-- `$Q_{r^2}$ from Lemma~\ref{l} has $R=r$ and $D=0$`: the formulas about the object, a
  function written alone applied to it (`R` is `R(Q_{r^2})`); `from` names the result whose
  definitions the object uses. -/
  | hasProps (s : MT) (fromLabel : Option Codes) (ms : List MT)
  /-- `$T$ is a function of the first $n$ observations`: a statistic of the terms below `n`. -/
  | firstObs (f n : MT)
  /-- What `stmtAt` stands for, once the proof is known: the clauses `stmt` of the
  statement, under the hypotheses `hyps` of the result that speak about its variable
  `v`, with `v` replaced by `e`. The grammar does not produce it. -/
  | inst (v : Codes) (e : MT) (hyps stmt : List Clause)
  deriving Repr, Inhabited, Lean.ToExpr

/-- `$x_1,\ldots,x_n$ are ADJ`: each term `x_i` of the sequence, for the integers `i` of
its range, is as the words say. -/
def seqEach (ts : List MTok) (ws : List Chunk) : Option Clause := do
  let (x, _, lo, hi) ← seqVars ts
  -- (a name that is no variable of the article, and not an existential threshold `@…`)
  let i := w!"i@"
  some (.under (.every [i] (.setOf (.id i) (.id w!"\\mathbb{Z}") [.chain lo [(.le, .id i), (.le, hi)]]))
    (.isA (.sub (.id x) (.id i)) ws false))

/-- A clause with the citations that justify it, its own binders
(`…, and for $b\in B$, CLAUSE`) and the definitions of a trailing `where`
(`…, where $g(x)\coloneqq x-1$`). -/
structure CClause where
  cites : List Codes
  clause : Clause
  binds : List Bind := []
  defs : List MT := []
  /-- Definitions of a trailing `for $F(x)=e$` (`We have $\beta(C)=K_F(C)$ for $F(x)=…$`):
  they are made before the clauses of the sentence and are local to it. -/
  forDefs : List MT := []
  deriving Repr, Inhabited

/-- `the kernel of $\varphi$`, `the order of $G$`, `the distance between $x$ and $y$`
before a verb: a notion of the vocabulary with its arguments, as the formula
`@the(WORDS, ARGS)` (each word a `text`, each argument a formula, in their order), which the
elaboration looks up among the notions. -/
def notionSubj (cs : List Chunk) (obj : Bool := false) : Option (MT × List Chunk) := do
  let r ← kw [w!"the"] cs
  let verbs : List Codes := [w!"is", w!"are", w!"divides", w!"equals", w!"satisfies", w!"has", w!"lies",
    w!"belongs", w!"contains", w!"coincides", w!"does", w!"can", w!"exceeds", w!"agrees", w!"holds"]
  -- (a hyphen before a word, `the number of $k$-element subsets of …`, and the commas of a list
  -- of formulas ending in `and`, `the multinomial coefficient of $n$ over $a$, $b$ and $c$`,
  -- are words of the notion)
  let rec listOf : Nat → List Chunk → Bool
    | 0, _ => false
    | _ + 1, .m _ :: .p 44 :: r => listOf 9 r
    | _ + 1, .m _ :: .w a :: .m _ :: _ => a == w!"and"
    | _, _ => false
  let rec bodyOf : Nat → List Chunk → List Chunk
    | 0, _ => []
    | f + 1, .w w :: r => if verbs.contains w then [] else .w w :: bodyOf f r
    | f + 1, .m t :: r => .m t :: bodyOf f r
    | f + 1, .p 45 :: r@(.w v :: _) =>
      if v == w!"th" || v == w!"st" || v == w!"nd" || v == w!"rd" then [] else .p 45 :: bodyOf f r
    | f + 1, .p 44 :: r => if listOf 9 r then .p 44 :: bodyOf f r else []
    | _, _ => []
  let body := bodyOf (r.length + 1) r
  let rest := r.drop body.length
  -- (an object, `… divides the order of $G$`, ends the sentence or a clause)
  match rest with
  | .w _ :: _ => pure ()
  | [] | .p _ :: _ => if !obj then none
  | _ => none
  let items ← body.mapM fun (c : Chunk) => match c with
    | .w w => some (MT.text (lower w))
    | .m ts => Math.parseFormula ts
    | .p p => some (MT.text [p])
    | _ => none
  -- (at least one word before the first argument, and an argument)
  if !(items.any fun m => match m with | .text _ => false | _ => true) then none
  -- (a preposition before the first argument: `the number $c$ is …` names its object)
  let before := items.takeWhile fun m => match m with | .text _ => true | _ => false
  let preps : List Codes := [w!"of", w!"between", w!"from", w!"in", w!"on", w!"at", w!"over", w!"to", w!"with", w!"by"]
  if !(before.any fun m => match m with | .text w => preps.contains w | _ => false) then none
  match items.head? with
  | some (.text _) => pure ()
  | _ => none
  some (.app (.id w!"@the") items, rest)

def subj (cs : List Chunk) : Option (Subj × List Chunk) :=
  match cs with
  | .m _ :: _ => do let (m, r) ← formula cs; some (.math m, r)
  | .w v :: r =>
    if v == w!"the" then (notionSubj cs).map fun (m, r) => (.math m, r) else
    if v == w!"its" then
      let ws := r.takeWhile (fun c => match c with
        | .w u => !([w!"is", w!"which", w!"attains"].contains u) | _ => false)
      some (.its (ws.filterMap (fun c => match c with | .w w => some w | _ => none)), r.drop ws.length)
    else none
  | _ => none

def obj (cs : List Chunk) : Option (Obj × List Chunk) :=
  match cs with
  | .m _ :: _ => do let (m, r) ← formula cs; some (.math m, r)
  | .w v :: r =>
    if v == w!"the" then
      let name := r.takeWhile (fun c => match c with | .w _ => true | _ => false)
      let words := name.filterMap fun c => match c with | .w w => some w | _ => none
      let r' := r.drop name.length
      match formula r' with
      | some (m, r'') => some (.named words (some m), r'')
      | none => some (.named words none, r')
    else none
  | _ => none

/-- `has $φ$` or `is <words> of OBJ` (relative clause parts joined by `and`). -/
def relParts : Nat → List Chunk → List RelPart → Option (List RelPart × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc =>
    let one : Option (RelPart × List Chunk) :=
      match kw [w!"has"] cs with
      | some r => do let (m, r') ← formula r; some (.has m, r')
      | none => do
        let r ← kw [w!"is"] cs
        let (phrase, r') ← wordsUntil [w!"of"] 8 r []
        let r'' ← kw [w!"of"] r'
        let (o, r3) ← obj r''
        some (.pred phrase o, r3)
    match one with
    | some (p, r) =>
      match kw [w!"and"] r with
      | some r' => relParts f r' (p :: acc)
      | none => some ((p :: acc).reverse, r)
    | none => none

def nounWords (cs : List Chunk) : Option (List Codes × List Chunk) :=
  wordsUntil [w!"with", w!"other"] 6 cs []

/-- A formula or a display. -/
def formulaOrDisplay (cs : List Chunk) : Option (MT × List Chunk) :=
  formula cs <|> (do let (m, _, r) ← display cs; some (m, r))

/-- Ordinal words for anaphora (`the first`, `the second`). -/
def ordinal (w : Codes) : Option Nat :=
  if w == w!"first" then some 0 else if w == w!"second" then some 1
  else if w == w!"third" then some 2 else none

/-- Map formulas joined by `and` (`$f$ and $g$`). -/
def mapList : Nat → List Chunk → List MT → Option (List MT × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc => do
    let (m, r) ← formula cs
    match kw [w!"and"] r with
    | some r' => mapList f r' (m :: acc)
    | none => some ((m :: acc).reverse, r)

/-- The standard adjectives: each pattern of words (a hyphen may join them) with
the adjective it spells. A longer pattern comes before the patterns it starts with.
`increasing` and `decreasing` alone are not read: they are used both for the strict
and for the weak property. -/
def wAdjectives : List (List Codes × List Codes) :=
  let u := [w!"with", w!"respect", w!"to", w!"uniform", w!"convergence"]
  let same (ws : List Codes) := (ws, ws)
  [ ([w!"lower", w!"semicontinuous"] ++ u, [w!"lower", w!"semicontinuous"] ++ u),
    ([w!"lower", w!"semi", w!"continuous"] ++ u, [w!"lower", w!"semicontinuous"] ++ u),
    ([w!"upper", w!"semicontinuous"] ++ u, [w!"upper", w!"semicontinuous"] ++ u),
    ([w!"upper", w!"semi", w!"continuous"] ++ u, [w!"upper", w!"semicontinuous"] ++ u),
    ([w!"continuous"] ++ u, [w!"continuous"] ++ u),
    ([w!"compact"] ++ u, [w!"compact"] ++ u),
    ([w!"closed"] ++ u, [w!"closed"] ++ u),
    same [w!"lower", w!"semicontinuous"], ([w!"lower", w!"semi", w!"continuous"], [w!"lower", w!"semicontinuous"]),
    same [w!"upper", w!"semicontinuous"], ([w!"upper", w!"semi", w!"continuous"], [w!"upper", w!"semicontinuous"]),
    same [w!"continuously", w!"differentiable"],
    same [w!"affine"],
    ([w!"lipschitz", w!"continuous"], [w!"lipschitz"]), same [w!"lipschitz"],
    same [w!"strictly", w!"increasing"], same [w!"strictly", w!"decreasing"],
    same [w!"strictly", w!"convex"], same [w!"strictly", w!"concave"],
    same [w!"nondecreasing"], ([w!"non", w!"decreasing"], [w!"nondecreasing"]),
    same [w!"nonincreasing"], ([w!"non", w!"increasing"], [w!"nonincreasing"]),
    same [w!"nonnegative"], ([w!"non", w!"negative"], [w!"nonnegative"]),
    same [w!"nonpositive"], ([w!"non", w!"positive"], [w!"nonpositive"]),
    same [w!"positive"], same [w!"negative"], same [w!"zero"],
    same [w!"compact"], same [w!"convex"], same [w!"concave"], same [w!"centrally", w!"symmetric"],
    same [w!"continuous"], same [w!"differentiable"], same [w!"injective"], same [w!"bounded"],
    same [w!"closed"], same [w!"open"], same [w!"connected"], same [w!"holomorphic"] ]

/-- Adjectives that are read here only with a domain (`constant on $I$`): alone, the
vocabulary reads them (`uniformly continuous`, Mathlib's `UniformContinuous`). -/
def wAdjectivesOn : List (List Codes) :=
  [[w!"uniformly", w!"continuous"], [w!"constant"], [w!"strictly", w!"monotone"], [w!"monotone"],
   [w!"riemann", w!"integrable"]]

/-- Exact words, where a hyphen may join two of them (`non-decreasing`). -/
def kwH : List Codes → List Chunk → Option (List Chunk)
  | [], cs => some cs
  | w :: ws, .w v :: cs =>
    if v != w then none else
    match ws, cs with
    | _ :: _, .p 45 :: cs' => kwH ws cs'
    | _, _ => kwH ws cs
  | _ :: _, _ => none

def adjective (cs : List Chunk) : Option (List Codes × List Chunk) :=
  (wAdjectives.findSome? fun (pat, a) => (kwH pat cs).map (a, ·)) <|>
  wAdjectivesOn.findSome? fun pat => (kwH pat cs).bind fun r => if (kw [w!"on"] r).isSome then some (pat, r) else none

/-- `ADJ, ADJ [on $A$] and ADJ`. -/
def adjectiveList : Nat → List Chunk → List (List Codes × Option MT) →
    Option (List (List Codes × Option MT) × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc => do
    let (a, r) ← adjective cs
    let (on, r) := match kw [w!"on"] r >>= formula with
      | some (m, r') => (some m, r')
      | none => (none, r)
    let acc := (a, on) :: acc
    let next := (punct 44 r >>= fun r' => (kw [w!"and"] r').getD r' |> some) <|> kw [w!"and"] r
    match next with
    | some r' =>
      if (adjective r').isSome then adjectiveList f r' acc else some (acc.reverse, r)
    | none => some (acc.reverse, r)

/-- Words that end the name of a notion. -/
def notionStops : List Codes :=
  [w!"if", w!"and", w!"or", w!"for", w!"of", w!"on", w!"by", w!"with", w!"then", w!"is", w!"are",
   w!"in", w!"to", w!"at", w!"from", w!"whenever", w!"where", w!"when", w!"since", w!"a", w!"an",
   w!"the", w!"every", w!"each", w!"all", w!"called", w!"not", w!"so", w!"whereas", w!"as", w!"both",
   w!"either", w!"neither"]

/-- The name of a notion: words and hyphens (`left-tail decreasing`, the hyphen as `-`). -/
def nameWords : Nat → List Chunk → List Codes → List Codes × List Chunk
  | 0, cs, acc => (acc.reverse, cs)
  | f + 1, .w v :: cs, acc =>
    if notionStops.contains v then (acc.reverse, .w v :: cs) else nameWords f cs (v :: acc)
  | f + 1, .p 45 :: cs, acc =>
    if acc.isEmpty then ([], .p 45 :: cs) else nameWords f cs (w!"-" :: acc)
  | _, cs, acc => (acc.reverse, cs)

/-- The end of a clause: the period, a comma, or a trailing citation. -/
def clauseEnd (cs : List Chunk) : Bool :=
  isEnd cs || (punct 44 cs).isSome || (kw [w!"by"] cs >>= cite).isSome

/-- A word after `and $x$` with which a phrase of the vocabulary goes on (`with coefficients $p$
and $q$ and exponent $n$`), rather than the verb of a new clause. -/
def phraseGoesOn (v : Codes) : Bool :=
  [w!"and", w!"or", w!"with", w!"from", w!"to", w!"at", w!"in", w!"on", w!"of", w!"up"].contains v

/-- A list of the arguments of a phrase goes on after a comma (`with kernel $K$, right-hand side
$g$ and parameter $\lambda$`): words, a formula, `and` and a word follow it. -/
def listContinues (cs : List Chunk) : Bool :=
  -- (`with payoffs $a$, $b$, $c$ and $d$`: formulas separated by commas, then `and` and the last,
  -- which no verb follows)
  let verbs := [w!"is", w!"are", w!"has", w!"have", w!"satisfies", w!"satisfy", w!"equals", w!"holds",
    w!"hold", w!"lies", w!"lie", w!"belongs", w!"divides", w!"does", w!"do", w!"can", w!"converges"]
  -- (formulas that state something, `$I_0(u)=1$ and $J(u)=2$`, are claims, not arguments)
  let term (ts : List MTok) : Bool := match Math.parseFormula ts with
    | some (.chain _ (_ :: _)) => false
    | some _ => true
    | none => false
  let rec formulas : Nat → List Chunk → Bool
    | 0, _ => false
    | f + 1, .p 44 :: .m ts :: r => term ts && formulas f r
    | _, .w a :: .m ts :: r =>
      a == w!"and" && term ts && (match r with
        | .w v :: _ => !verbs.contains v
        | _ => true)
    | _, _ => false
  match cs with
  | .p 44 :: .m ts :: r => term ts && formulas 8 r
  | .p 44 :: rest =>
    let ws := rest.takeWhile fun c => match c with | .w _ | .p 45 => true | _ => false
    let stop := [w!"and", w!"so", w!"which", w!"where", w!"whereas", w!"then", w!"since", w!"hence",
      w!"that", w!"for", w!"i", w!"respectively", w!"thus", w!"while", w!"but", w!"or"]
    !ws.isEmpty && (match ws.head? with | some (.w w) => !stop.contains w | _ => false) &&
      (match rest.drop ws.length with
       | .m _ :: .w a :: .w _ :: _ => a == w!"and"
       | _ => false)
  | _ => false

/-- The chunks up to the end of a clause. -/
def untilClauseEnd : Nat → List Chunk → List Chunk → Option (List Chunk × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc =>
    -- `and` before a formula starts the next clause (`$7$ is prime and $9$ is …`)
    let nextClause := match cs with
      -- (not `and $2$-regular`: a formula and a hyphen begin an adjective)
      | .w _ :: .m _ :: .p 45 :: .w _ :: _ => false
      -- (a formula that a word follows, `and $9$ is …`, or that states something, `and
      -- $x>0$`; not the last argument of a phrase, `collinear with $B$ and $C$.`)
      | .w w :: .m ts :: rest =>
        w == w!"and" && (match rest with
          -- (`with coefficients $p$ and $q$ and exponent $n$`: the phrase goes on)
          | .w v :: _ => !phraseGoesOn v
          | _ => match Math.parseFormula ts with
            | some (.chain _ (_ :: _)) => true
            | some _ => false
            | none => true)
      -- (`… and that $g$ is …`, in an assumption)
      | .w w :: .w t :: _ => w == w!"and" && t == w!"that"
      | _ => false
    if (clauseEnd cs && !listContinues cs) || (nextClause && !acc.isEmpty) then some (acc.reverse, cs) else
    match cs with
    | [] => none
    | c :: r => untilClauseEnd f r (c :: acc)

/-- `NAME[, NAME] and|or NAME`, ending a clause; `or` makes a disjunction. -/
def notionList (cs : List Chunk) : Option (List (List Codes) × Bool × List Chunk) := do
  let (n1, r1) := nameWords 8 cs []
  if n1.isEmpty then none else
  match kw [w!"and"] r1 <|> kw [w!"or"] r1 with
  | some r2 =>
    let disj := (kw [w!"or"] r1).isSome
    let (n2, r3) := nameWords 8 r2 []
    if n2.isEmpty then
      -- `and` before a formula: the next clause
      match r2 with
      -- (not `and $2$-regular`: a formula and a hyphen begin an adjective)
      | .m _ :: .p 45 :: .w _ :: _ => none
      | .m _ :: _ => if disj then none else some ([n1], false, r1)
      | _ => none
    else if !clauseEnd r3 then none else some ([n1, n2], disj, r3)
  | none => if clauseEnd r1 then some ([n1], false, r1) else none

/-- `[the WORDS] $X$`, possibly `$X\coloneqq e$`: a term named by a phrase. -/
def namedTerm (cs : List Chunk) : Option (MT × List Chunk) := do
  let r ← match kw [w!"the"] cs with
    | some r' =>
      let ws := r'.takeWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
      -- (the words name the term: `the arithmetic mean $\frac{a+b}{2}$`; after a
      -- preposition the formula is not what they name: `the probability of an exit at $-1$`)
      let preps := [w!"of", w!"at", w!"in", w!"on", w!"to", w!"for", w!"by", w!"with", w!"from",
        w!"over", w!"under", w!"between", w!"into", w!"through", w!"about", w!"near", w!"after",
        w!"before", w!"than", w!"as", w!"per", w!"via", w!"along", w!"across", w!"among", w!"within"]
      -- (or a notion of the vocabulary with its arguments: `the distance between $P$ and $Q$`)
      if ws.any (fun c => match c with | .w w => preps.contains (lower w) | _ => false) then
        return ← (notionSubj cs <|> notionSubj cs true)
      else some (r'.drop ws.length)
    | none => some cs
  formula r

/-- `is at most`, `is at least`, `is less than`, `is greater than`, `is equal to`,
`does not exceed`, `equals`. -/
def compareRel (cs : List Chunk) : Option (Rel × List Chunk) :=
  ((kw [w!"is", w!"at", w!"most"] cs).map (.le, ·)) <|> ((kw [w!"does", w!"not", w!"exceed"] cs).map (.le, ·)) <|>
  ((kw [w!"is", w!"at", w!"least"] cs).map (.ge, ·)) <|> ((kw [w!"is", w!"less", w!"than"] cs).map (.lt, ·)) <|>
  ((kw [w!"is", w!"smaller", w!"than"] cs).map (.lt, ·)) <|> ((kw [w!"is", w!"greater", w!"than"] cs).map (.gt, ·)) <|>
  ((kw [w!"is", w!"larger", w!"than"] cs).map (.gt, ·)) <|> ((kw [w!"is", w!"equal", w!"to"] cs).map (.eq, ·)) <|>
  ((kw [w!"equals"] cs).map (.eq, ·)) <|>
  -- (`the identity of $G$ lies in $H$`, `the order of $H$ divides the order of $G$`)
  ((kw [w!"lies", w!"in"] cs).map (.mem, ·)) <|> ((kw [w!"belongs", w!"to"] cs).map (.mem, ·)) <|>
  ((kw [w!"does", w!"not", w!"lie", w!"in"] cs).map (.nmem, ·)) <|> ((kw [w!"does", w!"not", w!"belong", w!"to"] cs).map (.nmem, ·)) <|>
  ((kw [w!"divides"] cs).map (.dvd, ·)) <|> ((kw [w!"does", w!"not", w!"divide"] cs).map (.ndvd, ·)) <|>
  ((kw [w!"exceeds"] cs).map (.gt, ·))

/-- `$A\to L$ as $v\to c$`, `$A\sim B$ as $v\to c$`, `$A=o(B)$ as $v\to c$`: the limit of `A`
is `L`, of `A/B` is `1`, of `A/B` is `0` (a finite limit). -/
def asLimit (cs : List Chunk) : Option (Clause × List Chunk) := do
  let (ts, r) ← mathChunk cs
  let r1 ← kw [w!"as"] r
  let (ts2, r2) ← mathChunk r1
  let i ← ts2.findIdx? (· == .cmd w!"to")
  let v ← match ts2.take i with
    | [.id v] => some v
    | [.cmd c] => if Math.greekNames.contains c then some ([92] ++ c) else none
    | _ => none
  let c ← Math.parseFormula (ts2.drop (i + 1))
  let lim (e : MT) (l : MT) : MT := .chain (.limit v c e) [(.eq, l)]
  let m ← match ts.findIdx? (· == .cmd w!"to"), ts.findIdx? (· == .cmd w!"sim") with
    | some j, _ => do
      let a ← Math.parseFormula (ts.take j)
      let l ← Math.parseFormula (ts.drop (j + 1))
      some (lim a l)
    | none, some j => do
      let a ← Math.parseFormula (ts.take j)
      let b ← Math.parseFormula (ts.drop (j + 1))
      some (lim (.frac a b) (.num 1))
    | none, none => do
      match ← Math.parseFormula ts with
      | .chain a [(.eq, .app (.id [111]) [b])] => some (lim (.frac a b) (.num 0))
      | _ => none
  some (.fact m, r2)

/-- `$a_n\to L$` without `as …`: the limit as the index of the term tends to `∞`. -/
def bareLimit (cs : List Chunk) : Option (Clause × List Chunk) := do
  let (ts, r) ← mathChunk cs
  if (kw [w!"as"] r).isSome then none
  let m ← seqLimitMT ts
  some (.fact m, r)

/-- `the statement|claim|assertion|result|lemma|… holds|is true for $E$` (`for some $n$`,
`for a given $n$`), `… for all|every|each $m<n$`, and `… for all smaller values`: the
statement of the result that is being proved, about `E`, about every `m` of the binder,
or about every value of the variable of the induction below it. -/
def stmtClause (cs : List Chunk) : Option (Clause × List Chunk) := do
  let r ← kw [w!"the"] cs
  let r ← [w!"statement", w!"claim", w!"assertion", w!"result", w!"lemma", w!"theorem", w!"proposition",
    w!"corollary", w!"formula", w!"identity", w!"inequality", w!"bound"].findSome? fun n => kw [n] r
  let r ← kw [w!"holds"] r <|> kw [w!"is", w!"true"] r <|> kw [w!"is", w!"valid"] r
  let r ← kw [w!"for"] r
  match kw [w!"all"] r <|> kw [w!"every"] r <|> kw [w!"each"] r with
  | some r1 =>
    -- `for all smaller values [of $n$]`, `for all [positive] integers less than $n$`
    let kinds : List Codes := [w!"value", w!"values", w!"integer", w!"integers", w!"number", w!"numbers",
      w!"index", w!"indices", w!"case", w!"cases"]
    let signs : List Codes := [w!"positive", w!"nonnegative", w!"non-negative", w!"natural"]
    let var (r : List Chunk) : Option (Codes × List Chunk) := match r with
      | .m [.id v] :: r' => some (v, r')
      | _ => none
    let below : Option (Clause × List Chunk) :=
      (do
        let r2 ← kw [w!"smaller"] r1
        let r2 := (signs.findSome? fun w => kw [w] r2).getD r2
        let r3 ← kinds.findSome? fun w => kw [w] r2
        match kw [w!"of"] r3 >>= var with
        | some (v, r4) => some (.stmtBelow (some v), r4)
        | none => some (.stmtBelow none, r3)) <|>
      (do
        let r2 := (signs.findSome? fun w => kw [w] r1).getD r1
        let r3 ← kinds.findSome? fun w => kw [w] r2
        let r4 ← kw [w!"less", w!"than"] r3 <|> kw [w!"smaller", w!"than"] r3 <|> kw [w!"below"] r3
        let (v, r5) ← var r4
        some (.stmtBelow (some v), r5))
    match below with
    | some res => some res
    | none =>
    let (ts, r2) ← mathChunk r1
    match binderMath ts with
    | some ([v], d) => some (.under (.every [v] d) (.stmtAt (.id v)), r2)
    | _ => none
  | none =>
    let r := (kw [w!"some"] r <|> kw [w!"a", w!"given"] r <|> kw [w!"a", w!"fixed"] r).getD r
    let (e, r2) ← formula r
    some (.stmtAt e, r2)

/-- A set as the object of an operator's phrase: a formula, or `the subspace of the component
$F_S$` (the functions whose component for `S` is all of them). -/
def opObject (cs : List Chunk) : Option (MT × List Chunk) :=
  (do
    let r ← kw [w!"the", w!"subspace", w!"of", w!"the", w!"component"] cs <|> kw [w!"the", w!"subspace", w!"of"] cs
    let (m, r1) ← formula r
    some (.app (.id w!"@hsub") [m], r1)) <|>
  formula cs

/-- The phrases of an operator (the field `hilbert`), joined by `and`: `fixes the constants`,
`maps $A$ into itself|$B$ [with norm $r$] [, with norm at most $c$ on it]`, `is $c$ times
the identity on $A$`. The subject is a formula, or `the operator $T$`. -/
def opClauses (cs : List Chunk) : Option (List Clause × List Chunk) := do
  let cs := (kw [w!"the", w!"operator"] cs).getD cs
  let (op, r) ← formula cs
  let one (r : List Chunk) : Option (Clause × List Chunk) :=
    (do
      let r1 ← kw [w!"fixes", w!"the", w!"constants"] r
      some (.fixesConsts op, r1)) <|>
    (do
      let r1 ← kw [w!"maps"] r
      let (dom, r2) ← opObject r1
      let r3 ← kw [w!"into"] r2
      let (cod, r4) ← (do let r' ← kw [w!"itself"] r3; some (dom, r')) <|> opObject r3
      -- `with norm $r$`, `, with norm at most $c$ on it`
      let r5 := (punct 44 r4 >>= fun r' => if (kw [w!"with", w!"norm"] r').isSome then some r' else none).getD r4
      match kw [w!"with", w!"norm", w!"at", w!"most"] r5 with
      | some r6 => do
        let (c, r7) ← formula r6
        let r8 := (kw [w!"on", w!"it"] r7).getD r7
        some (.mapsInto op dom cod (some (true, c)), r8)
      | none =>
        match kw [w!"with", w!"norm"] r5 with
        | some r6 => do
          let (c, r7) ← formula r6
          let r8 := (kw [w!"on", w!"it"] r7).getD r7
          some (.mapsInto op dom cod (some (false, c)), r8)
        | none => some (.mapsInto op dom cod none, r4)) <|>
    (do
      let r1 ← kw [w!"is"] r
      let (c, r2) ← formula r1
      let r3 ← kw [w!"times", w!"the", w!"identity", w!"on"] r2
      let (dom, r4) ← opObject r3
      some (.timesId op c dom, r4))
  let (c1, r1) ← one r
  let rec more : Nat → List Clause → List Chunk → List Clause × List Chunk
    | 0, acc, r => (acc.reverse, r)
    | f + 1, acc, r =>
      match kw [w!"and"] r >>= one with
      | some (c, r') => more f (c :: acc) r'
      | none => (acc.reverse, r)
  some (more 4 [c1] r1)

/-- Formulas separated by `,`, `, and` and `and`: `$X$, $Y$, and $Z$`. -/
def formulaList : Nat → List Chunk → List MT → Option (List MT × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc => do
    let (m, r) ← formula cs
    let acc := m :: acc
    match (punct 44 r >>= fun r' => (kw [w!"and"] r').getD r' |> some) <|> kw [w!"and"] r with
    | some r' => match r' with
      | .m _ :: _ => formulaList f r' acc
      | _ => some (acc.reverse, r)
    | none => some (acc.reverse, r)

/-- `the components $G_\emptyset$, $G_{\{1\}}$, and $G_{\{2\}}$ vanish`: each is zero. `Its
components are $F_\emptyset=0$, …, and $F_{\{1,2\}}=…$, with $φ$ and hence $ψ$`: the formulas,
and those after `with`. -/
def componentsClause (cs : List Chunk) : Option (Clause × List Chunk) :=
  (do
    let r := (kw [w!"the", w!"components"] cs <|> kw [w!"the", w!"functions"] cs).getD cs
    let (ms, r1) ← formulaList 8 r []
    let r2 ← kw [w!"vanish"] r1 <|> kw [w!"vanishes"] r1
    some (.both (ms.map fun m => Clause.fact (.chain m [(.eq, .num 0)])), r2)) <|>
  (do
    let r ← kw [w!"its", w!"components", w!"are"] cs <|>
      (do let r0 ← kw [w!"the", w!"components", w!"of"] cs; let (_, r1) ← formula r0; kw [w!"are"] r1)
    let (ms, r1) ← formulaList 8 r []
    -- `, with $φ$ [and hence $ψ$]`
    let (more, r2) := match punct 44 r1 >>= kw [w!"with"] with
      | some r' => match formula r' with
        | some (m1, r'') => match kw [w!"and", w!"hence"] r'' >>= formula with
          | some (m2, r3) => ([m1, m2], r3)
          | none => ([m1], r'')
        | none => ([], r1)
      | none => ([], r1)
    some (.both ((ms ++ more).map Clause.fact), r2))

/-- `$a$ at $X$ and $b$ at $Y$`: values and points. -/
def atPairs : Nat → List Chunk → List (MT × MT) → Option (List (MT × MT) × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc => do
    let (a, r1) ← formula cs
    let r2 ← kw [w!"at"] r1
    let (x, r3) ← formula r2
    let acc := (a, x) :: acc
    match kw [w!"and"] r3 with
    | some r4 =>
      match formula r4 with
      | some (_, r5) => if (kw [w!"at"] r5).isSome then atPairs f r4 acc else some (acc.reverse, r3)
      | none => some (acc.reverse, r3)
    | none => some (acc.reverse, r3)

/-- `and WORD …`, `, WORD …`: more words of a list follow. -/
def moreWords (r : List Chunk) : Bool :=
  match r with
  -- (`bounded below`, `bounded at infinity`: an adjective of the vocabulary that begins
  -- with a standard one)
  -- (`Lipschitz with respect to $d$`)
  | .w w :: .w w2 :: _ =>
    w == w!"and" || w == w!"at" || w == w!"below" || w == w!"above" || (w == w!"with" && w2 == w!"respect") ||
      -- (`Lipschitz in the second variable`)
      (w == w!"in" && w2 == w!"the")
  | .w w :: .m _ :: .p 45 :: .w _ :: _ => w == w!"and"
  -- (`open in $\tau$`, `continuous from $\tau$ to $\sigma$`: with a topology of the vocabulary)
  | .w w :: .m _ :: _ => w == w!"in" || w == w!"from"
  | .p 44 :: .w _ :: _ => true
  | .w w :: _ => w == w!"below" || w == w!"above"
  | _ => false

/-- `v` is the index of a subscript in the formula (`a_n` for `n`). -/
def mtIndexedBy (v : Codes) : Nat → MT → Bool
  | 0, _ => false
  | k + 1, m => match m with
    | .sub b i => (match i with | .id w => w == v | _ => mtIndexedBy v k i) || mtIndexedBy v k b
    | .sup b e => mtIndexedBy v k b || mtIndexedBy v k e
    | .app g xs => mtIndexedBy v k g || xs.attach.any (fun ⟨x, _⟩ => mtIndexedBy v k x)
    | .add x y | .minus x y | .mul x y | .div x y | .frac x y => mtIndexedBy v k x || mtIndexedBy v k y
    | .neg x | .abs x => mtIndexedBy v k x
    | .chain x rs => mtIndexedBy v k x || rs.attach.any (fun ⟨(_, y), _⟩ => mtIndexedBy v k y)
    | _ => false

/-- One clause, without its citations. Must be followed by a clause boundary. -/
def clause1 (cs : List Chunk) (strictAdj : Bool := false) : Option (Clause × List Chunk) :=
  match stmtClause cs with
  | some res => some res
  | none =>
  match componentsClause cs with
  | some res => some res
  | none =>
  -- `the product of … has the expectation $φ$`: the formula (the words name its subject)
  match (do
      let r ← wordsThen [w!"has", w!"the", w!"expectation"] cs
      let (m, r') ← formula r
      match m with
      | .chain _ _ => some (Clause.fact m, r')
      | _ => none) with
  | some res => some res
  | none =>
  -- `the copula $C_{r,g}$ of~\eqref{eq:Crg} has $φ$`: the formula (the words, formulas that
  -- state nothing and references name its subject)
  match (do
      let i := (cs.findIdx? fun (c : Chunk) => match c with | .w v => v == w!"has" | _ => false).getD 0
      let cs' := (cs.take i).filter (fun (c : Chunk) => match c with | .r _ _ => false | _ => true) ++ cs.drop i
      let r ← wordsThen [w!"has"] cs'
      let (m, r') ← formula r
      match m with
      | .chain _ _ => some (Clause.fact m, r')
      | _ => none) with
  | some res => some res
  | none =>
  -- `the four affine coefficients $\beta$, …, and $\rho_{\mathrm N}$ equal $r$ at $M_r$ and
  -- $-r$ at $W_r$`: each function has these values at these points
  match (do
      let ws := cs.takeWhile fun (c : Chunk) => match c with | .w _ => true | _ => false
      let (fs, r1) ← formulaList 8 (cs.drop ws.length) []
      let r2 ← kw [w!"equal"] r1 <|> kw [w!"equals"] r1
      let (pairs, r3) ← atPairs 4 r2 []
      some (Clause.both (fs.flatMap fun fn => pairs.map fun (a, x) =>
        Clause.fact (.chain (.app fn [x]) [(.eq, a)])), r3)) with
  | some res => some res
  | none =>
  -- `$Q_{r^2}$ from Lemma~\ref{l} has $R=r$ and $D=0$`
  match (do
      let (sm, r) ← formula cs
      match sm with
      | .chain _ _ => none
      | _ =>
      let (fromL, r1) := match kw [w!"from"] r >>= cite with
        | some (l, r') => (some l, r')
        | none => (none, r)
      let r2 ← kw [w!"has"] r1
      let (m1, r3) ← formula r2
      let (ms, r4) := match kw [w!"and"] r3 >>= formula with
        | some (m2, r') => ([m1, m2], r')
        | none => ([m1], r3)
      if !ms.all (fun m => match m with | .chain _ _ => true | _ => false) then none else
      some (Clause.hasProps sm fromL ms, r4)) with
  | some res => some res
  | none =>
  -- `$T$ is a function of the first $n$ observations`
  match (do
      let (fm, r) ← formula cs
      let r1 ← kw [w!"is", w!"a", w!"function", w!"of", w!"the", w!"first"] r
      let (m, r2) ← formula r1
      let r3 ← kw [w!"observations"] r2
      some (Clause.firstObs fm m, r3)) with
  | some res => some res
  | none =>
  -- `$F$ depends only on the first $m$ terms`
  match (do
      let (fm, r) ← formula cs
      let r1 ← kw [w!"depends", w!"only", w!"on", w!"the", w!"first"] r
      let (m, r2) ← formula r1
      let r3 ← kw [w!"terms"] r2
      some (Clause.dependsFirst fm m, r3)) with
  | some res => some res
  | none =>
  -- the phrases of an operator: one clause, or `both`
  match opClauses cs with
  | some ([c], r) => some (c, r)
  | some (cs', r) => some (.both cs', r)
  | none =>
  match asLimit cs <|> bareLimit cs with
  | some res => some res
  | none =>
  -- It holds that DISPLAY
  match kw [w!"it", w!"holds", w!"that"] cs with
  | some r => do let (m, _, r') ← display r; some (.holds m, r')
  | none =>
  -- $φ$ if and only if $ψ$
  match (do
      let (p, r) ← formula cs
      let r1 ← kw [w!"if", w!"and", w!"only", w!"if"] r
      let (q, r2) ← formula r1
      some (Clause.iff p q, r2)) with
  | some res => some res
  | none =>
  -- equality holds exactly on $S$ | when $φ$; it holds exactly on $S$
  -- [both|the|this|these|all] constants|bounds|inequalities are sharp
  match (do
      let r0 := ((kw [w!"both"] cs <|> kw [w!"the"] cs <|> kw [w!"this"] cs <|> kw [w!"these"] cs <|>
        kw [w!"all"] cs).getD cs)
      let r1 ← [w!"constants", w!"constant", w!"bounds", w!"bound", w!"inequalities", w!"inequality",
        w!"estimates", w!"estimate"].findSome? (fun w => kw [w] r0)
      let r2 ← kw [w!"are", w!"sharp"] r1 <|> kw [w!"is", w!"sharp"] r1
      some (Clause.sharp, r2)) with
  | some res => some res
  | none =>
  -- [the function|map|set] $X$ is ADJ, ADJ and ADJ
  match (do
      let fn := (kw [w!"the", w!"function"] cs <|> kw [w!"the", w!"map"] cs).isSome
      let cs := match kw [w!"the", w!"function"] cs <|> kw [w!"the", w!"map"] cs <|> kw [w!"the", w!"set"] cs <|>
          kw [w!"the", w!"interval"] cs <|>
          kw [w!"the", w!"number"] cs <|> kw [w!"the", w!"class"] cs with
        | some r => r | none => cs
      let (m, r) ← formula cs
      -- (`the function $f(x)=e^x$`: the map `x\mapsto e^x`)
      let m := match fn, m with
        | true, .chain (.app (.id _) [.id x]) [(.eq, e)] => MT.mapsto (.id x) e
        | _, _ => m
      let r1 ← kw [w!"is"] r
      let (adjs, r2) ← adjectiveList 16 r1 []
      -- (`strictAdj`: not when a further adjective follows that is not a standard one,
      -- `compact and perfect`: the vocabulary's adjectives are read below)
      if strictAdj && moreWords r2 then none
      -- (`continuous at $0$`: a phrase of the vocabulary with an object, below)
      if (match r2 with | .w w :: .m _ :: _ => [w!"at", w!"to", w!"from", w!"near"].contains w | _ => false) then none
      some (Clause.adjectives m adjs, r2)) with
  | some res => some res
  | none =>
  -- $X$ is NAME [and|or NAME]: notions of the article
  match (do
      let (m, r) ← formula cs
      let r1 ← kw [w!"is"] r
      let (names, disj, r2) ← notionList r1
      some (Clause.notions m names disj, r2)) with
  | some res => some res
  | none =>
  match (do
      let r ← kw [w!"equality", w!"holds", w!"exactly"] cs <|> kw [w!"it", w!"holds", w!"exactly"] cs
      match kw [w!"on"] r with
      | some r1 => do let (m, r2) ← formula r1; some (Clause.equalityOn m, r2)
      | none => do
        let r1 ← kw [w!"when"] r
        let (m, r2) ← formula r1
        some (Clause.equalityWhen m, r2)) with
  | some res => some res
  | none =>
  -- `$a$ and $b$ are nonincreasing on $(0,1)$`
  match (do
      let rec names : Nat → List Chunk → List MT → Option (List MT × List Chunk)
        | 0, _, _ => none
        | f + 1, cs, acc => do
          let (m, r) ← formula cs
          -- a name, or an application with the placeholder `\cdot` (`$h_t(u,\cdot)$`)
          let ok := match m with
            | .id _ => true
            | .app _ args => args.any fun a => match a with | .id n => n == w!"\\cdot" | _ => false
            | _ => false
          if !ok then none else
            match kw [w!"and"] r with
            | some r' => names f r' (m :: acc)
            | none => some ((m :: acc).reverse, r)
      let cs := (kw [w!"the", w!"functions"] cs <|> kw [w!"the", w!"function"] cs).getD cs
      let (fs, r1) ← names 4 cs []
      let r2 ← kw [w!"are"] r1 <|> kw [w!"is"] r1
      let (mono, r3) ← monoWord r2
      let r4 ← kw [w!"on"] r3
      let (d, r5) ← formula r4
      some (Clause.monoFns fs d mono, r5)) with
  | some res => some res
  | none =>
  -- [both] [the] [parameter] maps $f$ and $g$ are strictly increasing
  match (do
      let r0 := (kw [w!"both"] cs).getD cs
      let r1 := (kw [w!"the"] r0).getD r0
      let r2 := (kw [w!"parameter"] r1).getD r1
      let r3 ← kw [w!"maps"] r2 <|> kw [w!"map"] r2
      let (ms, r4) ← mapList 4 r3 []
      let r5 ← kw [w!"are", w!"strictly", w!"increasing"] r4 <|> kw [w!"is", w!"strictly", w!"increasing"] r4
      some (Clause.increasing ms, r5)) with
  | some res => some res
  | none =>
  -- the first|second ranges over $B$
  match (do
      let r ← kw [w!"the"] cs
      match r with
      | .w o :: r1 => do
        let k ← ordinal o
        let r2 ← kw [w!"ranges", w!"over"] r1
        let (b, r3) ← formula r2
        some (Clause.ranges k b, r3)
      | _ => none) with
  | some res => some res
  | none =>
  -- the maximum X [and the minimum Y] of F over all NOUNS $C$ with φ are each attained by exactly one NOUN
  match (do
      let item (r : List Chunk) : Option ((Bool × MT) × List Chunk) := do
        let r1 ← kw [w!"the"] r
        let (isMax, r2) ← (kw [w!"maximum"] r1).map (true, ·) <|> (kw [w!"minimum"] r1).map (false, ·)
        let (x, r3) ← formula r2
        some ((isMax, x), r3)
      let (i1, r1) ← item cs
      let (items, r2) : List (Bool × MT) × List Chunk := match (kw [w!"and"] r1).bind item with
        | some (i2, r') => ([i1, i2], r')
        | none => ([i1], r1)
      let r3 ← kw [w!"of"] r2
      let (f, r4) ← formula r3
      let r5 ← kw [w!"over", w!"all"] r4
      let ws := r5.takeWhile (fun (c : Chunk) => match c with | .w _ => true | _ => false)
      let noun := ws.filterMap (fun (c : Chunk) => match c with | .w w => some w | _ => none)
      let (vt, r6) ← mathChunk (r5.drop ws.length)
      let v ← match vt with | [.id v] => some v | _ => none
      let r7 ← kw [w!"with"] r6
      let (cond, r8) ← formula r7
      let r9 ← kw [w!"are", w!"each", w!"attained", w!"by", w!"exactly", w!"one"] r8 <|>
        kw [w!"is", w!"attained", w!"by", w!"exactly", w!"one"] r8
      let ws2 := r9.takeWhile (fun (c : Chunk) => match c with | .w _ => true | _ => false)
      if ws2.isEmpty then none else some (Clause.extremaOver items f noun v cond, r9.drop ws2.length) :
        Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- exactly one N $x$ with $φ$ satisfies $ψ$
  match kw [w!"exactly", w!"one"] cs with
  | some r => do
    let (noun, r1) ← wordsUntil [] 6 r [] <|> (do
      let words := r.takeWhile (fun c => match c with | .w _ => true | _ => false)
      some (words.filterMap (fun c => match c with | .w w => some w | _ => none), r.drop words.length))
    let (vt, r2) ← mathChunk r1
    let v ← match vt with | [.id v] => some v | _ => none
    let r3 ← kw [w!"with"] r2
    let (cond, r4) ← formula r3
    let r5 ← kw [w!"satisfies"] r4
    let (sat, r6) ← formula r5
    some (.exactlyOne noun v cond sat, r6)
  | none =>
  -- Every $x\in A$ satisfies $φ$ | Every NP satisfies|obeys φ
  match kw [w!"every"] cs with
  | some r =>
    (do
      let (ts, r1) ← mathChunk r
      let (vs, dom) ← binderMath ts
      let r2 ← kw [w!"satisfies"] r1 <|> kw [w!"obeys"] r1
      let (body, r3) ← formulaOrDisplay r2
      -- (several statements: read as `For every $x\in A$, CLAUSES`, see `everySatisfies`)
      if moreFormulas r3 then none else
      some (.every vs dom body, r3)) <|>
    (do
      let (np, r1) ← chunksUntil [w!"satisfies", w!"obeys"] r []
      let r2 ← kw [w!"satisfies"] r1 <|> kw [w!"obeys"] r1
      let (body, r3) ← formulaOrDisplay r2
      -- `… satisfies $φ$ for all $u,v\in A$`
      let (inner, r4) : List Bind × List Chunk := match (do
          let r' ← kw [w!"for", w!"all"] r3 <|> kw [w!"for", w!"every"] r3 <|> kw [w!"for", w!"each"] r3
          let (ts, r'') ← mathChunk r'
          let (vs, d) ← binderMath ts
          some (Bind.every vs d, r'')) with
        | some (b, r') => ([b], r')
        | none => ([], r3)
      if moreFormulas r4 then none else
      some (.everyNP np body inner, r4)) <|>
    (do
      let (np, r1) ← chunksUntil [w!"is"] r []
      let r2 ← kw [w!"is"] r1
      let (names, disj, r3) ← notionList r2
      some (.everyIs np names disj, r3)) <|>
    (do
      let (np, r1) ← chunksUntil [w!"is"] r []
      let r2 ← kw [w!"is"] r1
      -- (`every vertex of $G$ is of even degree`: a modifier that follows its noun)
      match r2 with
      | .w w :: _ => if ![w!"of", w!"with", w!"without"].contains w then none
      | _ => none
      let mod := r2.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"and", w!"or", w!"if", w!"then", w!"for", w!"whenever", w!"where", w!"since"].contains w
        | .m _ | .p 45 => true
        | _ => false
      if mod.isEmpty || !clauseEnd (r2.drop mod.length) then none
      some (.everyMod np mod, r2.drop mod.length))
  | none =>
  -- The maximum/minimum $F=m$ is attained only by SUBJ[, which REL]
  match kw [w!"the", w!"maximum"] cs, kw [w!"the", w!"minimum"] cs with
  | some r, _ | none, some r => do
    let isMax := (kw [w!"the", w!"maximum"] cs).isSome
    let (fv, r1) ← formula r
    -- `the maximum V of F is attained only by …`, or (after a maximum) `the minimum V only by …`
    let (ofF, r1) := match kw [w!"of"] r1 >>= formula with
      | some (fm, r') => (some fm, r')
      | none => (none, r1)
    let gapped := ofF.isNone && (kw [w!"only", w!"by"] r1).isSome
    let r2 ← kw [w!"is", w!"attained", w!"only", w!"by"] r1 <|> (if gapped then kw [w!"only", w!"by"] r1 else none)
    let (s, r3) ← subj r2
    let (atw, r3) := match punct 44 r3 >>= kw [w!"at", w!"which"] >>= formula with
      | some (m, r') => (some m, r')
      | none => (none, r3)
    let (rels, r5) ← match punct 44 r3 >>= kw [w!"which"] with
      | some r4 => relParts 4 r4 []
      | none => some ([], r3)
    if ofF.isSome || gapped || atw.isSome then some (.extremumOf isMax fv ofF s atw rels, r5)
    else some (.extremum isMax fv s rels, r5)
  | none, none =>
  -- its derivative $d$ is positive/negative for $φ$
  match kw [w!"its", w!"derivative"] cs with
  | some r => do
    let (d, r1) ← formula r
    let r2 ← kw [w!"is"] r1
    let (positive, r3) ← (match kw [w!"positive"] r2, kw [w!"negative"] r2 with
      | some r', _ => some (true, r') | none, some r' => some (false, r') | _, _ => none :
      Option (Bool × List Chunk))
    let r4 ← kw [w!"for"] r3
    let (cond, r5) ← formula r4
    some (.deriv d positive cond, r5)
  | none =>
  -- no N other than $x$ attains the maximum/minimum
  match kw [w!"no"] cs with
  | some r => do
    let (noun, r1) ← nounWords r
    let r2 ← kw [w!"other", w!"than"] r1
    let (x, r3) ← formula r2
    let r4 ← kw [w!"attains", w!"the"] r3
    let (isMax, r5) ← (match kw [w!"maximum"] r4, kw [w!"minimum"] r4 with
      | some r', _ => some (true, r') | none, some r' => some (false, r') | _, _ => none :
      Option (Bool × List Chunk))
    some (.noOther noun x isMax, r5)
  | none =>
  -- the map $λ$ sends $F$ to $G$
  match kw [w!"the", w!"map"] cs with
  | some r => do
    let (mp, r1) ← formula r
    let r2 ← kw [w!"sends"] r1
    let (fm, r3) ← formula r2
    let r4 ← kw [w!"to"] r3
    let (gm, r5) ← formula r4
    some (.sends mp fm gm, r5)
  | none =>
  -- only $x$ attains it
  match kw [w!"only"] cs with
  | some r => do
    let (x, r1) ← formula r
    let r2 ← kw [w!"attains", w!"it"] r1
    some (.onlyAttains x, r2)
  | none =>
  -- DISPLAY \qquad\text{for every NP}: the formula for every object of the noun phrase
  match (match cs with
      | .d ts _ :: rest => (displayParts ts).bind fun (m, np) => np.map fun np => (Clause.forEveryNP (.fact m) np, rest)
      | _ => none) with
  | some res => some res
  | none =>
  -- DISPLAY (and DISPLAY)*
  match display cs with
  | some (m, _, r) =>
    let rec more : Nat → List MT → List Chunk → Option (List MT × List Chunk)
      | 0, _, _ => none
      | g + 1, acc, rest =>
        match kw [w!"and"] rest >>= display with
        | some (m', _, r') => more g (m' :: acc) r'
        | none => some (acc.reverse, rest)
    match more 6 [m] r with
    | some ([m], r') => some (.fact m, r')
    | some (ms, r') => some (.fact (.conj ms), r')
    | none => none
  | none =>
  -- `$a$ and $b$ are positive`, `$x_1,\ldots,x_n$ are distinct`, `$r$ and $s$ are
  -- relatively prime`: each variable has the adjectives (or is of the noun), and the
  -- collective properties hold together
  match (do
      let (ts, r1) ← joinedVars cs
      let vars ← ((seqBound ts).bind fun (l, b) => if b.isEmpty then some [l] else none) <|> splitVars ts
      -- (a bound after the variables is not read here)
      if vars.length > 1 && vars.any (·.any fun t => (Math.relOf t).isSome) then none else
      let r2 ← kw [w!"are"] r1
      let ws0 := r2.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"then", w!"for", w!"if", w!"whenever", w!"with", w!"such", w!"to", w!"from",
            w!"of", w!"in", w!"on", w!"by"].contains w
        | .p 45 => true
        | _ => false
      let r3 := r2.drop ws0.length
      -- (`relatively prime to $n$`, `distinct from $y$`: relations to another object)
      if (kw [w!"to"] r3).isSome || (kw [w!"from"] r3).isSome then none else
      let (ws, ps) := collectiveWords 8 ws0
      let isAnd (c : Chunk) : Bool := match c with | .w w => w == w!"and" | _ => false
      let ws := ((ws.dropWhile isAnd).reverse.dropWhile isAnd).reverse
      let together : List Clause ← if ps.isEmpty then some [] else (collectiveCond ps vars).map ([Clause.fact ·])
      let each : List Clause ← if ws.isEmpty then some [] else
        match vars with
        | [v] => (seqEach v ws).map ([·])
        | _ => vars.mapM fun v => (Math.parseFormula v).map fun m => Clause.isA m ws false
      match each ++ together with
      | [] => none
      | [c] => some (c, r3)
      | cs => some (.both cs, r3)) with
  | some res => some res
  | none =>
  -- [the WORDS] $X$ is at most [the WORDS] $Y$
  match (do
      let (l, r) ← namedTerm cs
      let (rel, r1) ← compareRel r
      let (rr, r2) ← namedTerm r1
      -- (`$f$ is smaller than $g$ in the hazard rate order`: a stochastic order of the
      -- vocabulary, an adjective below)
      let isOrder := (do
        let r3 ← kw [w!"in", w!"the"] r2
        (r3.take 6).find? fun (c : Chunk) => match c with | .w w => w == w!"order" | _ => false).isSome
      if isOrder then none
      -- (membership, `lies in`, is the formula's `\in`)
      if rel == Rel.mem || rel == Rel.nmem || rel == Rel.dvd || rel == Rel.ndvd then return (Clause.fact (.chain l [(rel, rr)]), r2)
      some (Clause.compare l rel rr, r2)) with
  | some res => some res
  | none =>
  -- `the equation $x^4+y^4=z^4$ has no solution in positive integers`, `has a solution in
  -- integers`, `has infinitely many solutions in positive integers`, `has no integer
  -- solutions`: the unknowns of the equation, each a number of the noun
  match (do
      let r0 := (kw [w!"the"] cs).getD cs
      let r1 ← kw [w!"equation"] r0
      let (ts, r2) ← mathChunk r1
      let e ← Math.parseFormula ts
      let .chain _ [(.eq, _)] := e | none
      let r3 ← kw [w!"has"] r2
      let stops : List Codes := [w!"and", w!"or", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then",
        w!"whenever", w!"iff", w!"but", w!"so"]
      let inNoun (kind : Nat) (r : List Chunk) : Option (Clause × List Chunk) := do
        let r' ← kw [w!"in"] r
        let np := r'.takeWhile fun (c : Chunk) => match c with
          | .w w => !stops.contains w
          | .p 45 => true
          | _ => false
        if np.isEmpty then none
        some (Clause.solutions kind e np, r'.drop np.length)
      -- (`no integer solutions`: the numbers named before `solutions`)
      let named (kind : Nat) (r : List Chunk) : Option (Clause × List Chunk) := do
        let i ← r.findIdx? fun (c : Chunk) => match c with | .w w => w == w!"solutions" || w == w!"solution" | _ => false
        let ws := r.take i
        if ws.isEmpty || i > 2 then none
        let np : List Chunk ← match ws with
          | [.w a] =>
            if a == w!"integer" then some [.w w!"integers"]
            else if a == w!"rational" then some [.w w!"rational", .w w!"numbers"]
            else if a == w!"real" then some [.w w!"real", .w w!"numbers"]
            else none
          | [.w p, .w a] => if p == w!"positive" && a == w!"integer" then some [.w p, .w w!"integers"] else none
          | _ => none
        some (Clause.solutions kind e np, r.drop (i + 1))
      (do let r ← kw [w!"no", w!"solutions"] r3 <|> kw [w!"no", w!"solution"] r3; inNoun 0 r) <|>
      (do let r ← kw [w!"no"] r3; named 0 r) <|>
      (do let r ← kw [w!"a", w!"solution"] r3 <|> kw [w!"solutions"] r3; inNoun 1 r) <|>
      (do let r ← kw [w!"an"] r3 <|> kw [w!"a"] r3; named 1 r) <|>
      (do let r ← kw [w!"infinitely", w!"many", w!"solutions"] r3; inNoun 2 r) <|>
      (do let r ← kw [w!"infinitely", w!"many"] r3; named 2 r) : Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$f$ attains its maximum on $[a,b]$`: a point of the set where no value is larger
  match (do
      let (ts, r) ← mathChunk cs
      let f ← Math.parseFormula ts
      let r1 ← kw [w!"attains", w!"its"] r <|> kw [w!"attains", w!"a"] r
      let (isMax, r2) ← (kw [w!"maximum"] r1).map (true, ·) <|> (kw [w!"minimum"] r1).map (false, ·)
      let r3 ← kw [w!"on"] r2 <|> kw [w!"in"] r2
      let (dts, r4) ← mathChunk r3
      let d ← Math.parseFormula dts
      let c : Codes := w!"\\attained"
      let x : Codes := w!"\\attaining"
      -- (`$|f|$ attains a maximum in $U$`: the modulus of the values)
      let at_ (v : Codes) : MT := match f with
        | .abs g => .abs (.app g [.id v])
        | g => .app g [.id v]
      some (Clause.fact (.quant false [c] d (.quant true [x] d (.chain (at_ x) [(if isMax then Rel.le else Rel.ge, at_ c)]))), r4) :
      Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$\sup A$ exists`, `$A$ has a maximum` (a minimum, a supremum, an infimum): the term
  -- is defined
  match (do
      let (ts, r) ← mathChunk cs
      let m ← Math.parseFormula ts
      match kw [w!"exists"] r with
      | some r1 => some (Clause.exists_ m, r1)
      | none =>
        let r1 ← kw [w!"has", w!"a"] r
        let (t, r2) ← (kw [w!"maximum"] r1).map (MT.extr true m, ·) <|> (kw [w!"minimum"] r1).map (MT.extr false m, ·) <|>
          (kw [w!"supremum"] r1).map (MT.bound true m, ·) <|> (kw [w!"infimum"] r1).map (MT.bound false m, ·) <|>
          (kw [w!"largest", w!"element"] r1).map (MT.extr true m, ·) <|> (kw [w!"smallest", w!"element"] r1).map (MT.extr false m, ·)
        some (Clause.exists_ t, r2) : Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$T$ has at least $2$ leaves`: the modifier `with at least $2$ leaves`
  match (do
      let (ts, r) ← mathChunk cs
      let s ← Math.parseFormula ts
      let r1 ← kw [w!"has"] r
      let (q, r1') ← (kw [w!"at", w!"least"] r1).map ([Chunk.w w!"at", Chunk.w w!"least"], ·) <|>
        (kw [w!"at", w!"most"] r1).map ([Chunk.w w!"at", Chunk.w w!"most"], ·) <|>
        (kw [w!"exactly"] r1).map ([Chunk.w w!"exactly"], ·)
      let (k, r2) ← mathChunk r1'
      let ws := r2.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"and", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then", w!"whenever"].contains w
        | _ => false
      if ws.isEmpty then none
      -- (`at most $n$ roots in $K$`: the object of the last preposition)
      let ws := match ws.getLast?, r2.drop ws.length with
        | some (.w p), (.m x :: _) => if [w!"in", w!"over", w!"of", w!"on"].contains p then ws ++ [.m x] else ws
        | _, _ => ws
      let isA := Clause.isA s ([Chunk.w w!"with"] ++ q ++ [Chunk.m k] ++ ws) false
      -- (else the number of such objects of the subject, `$K$ has exactly two ideals`)
      let count : Option Clause := do
        let .num n ← Math.parseFormula k | none
        if n == 0 || n > 6 then none
        let mode := match q with
          | [.w w] => if w == w!"exactly" then 0 else 1
          | [_, .w w] => if w == w!"most" then 2 else 1
          | _ => 1
        let head := ws.takeWhile fun (c : Chunk) => match c with
          | .w w => ![w!"of", w!"with", w!"in", w!"on", w!"at", w!"over", w!"to", w!"from", w!"satisfying"].contains w
          | .p 45 => true
          | _ => false
        if head.isEmpty then none
        some (Clause.countNP (head ++ [Chunk.w w!"of", Chunk.m ts] ++ ws.drop head.length) mode n (some isA))
      -- (`elements of order $2$`: a formula after the words, which no modifier reads)
      let np' := r2.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"and", w!"or", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then", w!"whenever"].contains w
        | .m _ => true
        | .p 45 => true
        | _ => false
      if np'.length > ws.length then
        match count with
        | some (.countNP cnp mode n _) =>
          let head := cnp.takeWhile fun (c : Chunk) => match c with | .w w => w != w!"of" | _ => true
          some (Clause.countNP (head ++ [Chunk.w w!"of", Chunk.m ts] ++ np'.drop (head.length)) mode n none, r2.drop np'.length)
        | _ => some (isA, r2.drop ws.length)
      else
      some (count.getD isA, r2.drop ws.length) : Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$G$ has $n-1$ edges`: the modifier `with $n-1$ edges` of the vocabulary
  match (do
      let (ts, r) ← mathChunk cs
      let s ← Math.parseFormula ts
      let r1 ← kw [w!"has"] r
      let (k, r2) ← mathChunk r1
      let ws := r2.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"and", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then", w!"whenever"].contains w
        | _ => false
      if ws.isEmpty then none
      some (Clause.isA s ([Chunk.w w!"with", Chunk.m k] ++ ws) false, r2.drop ws.length) : Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$X$ and $Y$ are independent`, `$X_1,\ldots,X_n$ are independent and identically
  -- distributed`: the collective condition of random variables
  match (do
      let (ts, r) ← joinedVars cs
      let r1 ← kw [w!"are"] r
      let (p, r2) ← ((kw [w!"independent", w!"and", w!"identically", w!"distributed"] r1 <|> kw [w!"iid"] r1).map (w!"iid", ·)) <|>
        ((kw [w!"mutually", w!"independent"] r1 <|> kw [w!"independent"] r1).map (w!"independent", ·)) <|>
        ((kw [w!"identically", w!"distributed"] r1).map (w!"identically distributed", ·))
      let vars ← ((seqBound ts).map fun _ => [ts]) <|> splitVars ts
      let c ← collectiveCond [p] vars
      some (Clause.fact c, r2) : Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$G$ has no odd cycle`, `$G$ contains no triangle`: the modifier `without odd cycle`
  match (do
      let (ts, r) ← mathChunk cs
      let s ← Math.parseFormula ts
      let r1 ← kw [w!"has", w!"no"] r <|> kw [w!"contains", w!"no"] r <|> kw [w!"have", w!"no"] r <|> kw [w!"contain", w!"no"] r
      let ws := r1.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"and", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then", w!"whenever", w!"of", w!"in", w!"with"].contains w
        | .p 45 => true
        | _ => false
      if ws.isEmpty then none
      -- (`no cycle of odd length`: `of` and words, not an object)
      let ofWords := match r1.drop ws.length with
        | .w o :: rest@(.w _ :: _) =>
          if o != w!"of" then [] else
          .w o :: rest.takeWhile fun (c : Chunk) => match c with
            | .w w => ![w!"and", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then", w!"whenever", w!"of", w!"in", w!"with", w!"or", w!"iff"].contains w
            | _ => false
        | _ => []
      let ws := ws ++ ofWords
      -- (`no root in $K$`: with the object of `in`)
      let ws := match r1.drop ws.length with
        | .w p :: .m x :: _ => if p == w!"in" || p == w!"over" then ws ++ [.w p, .m x] else ws
        | _ => ws
      some (Clause.isA s ([Chunk.w w!"without"] ++ ws) false, r1.drop ws.length) : Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$v$ has even degree`: a modifier `with even degree` (words only, without an article)
  match (do
      let (ts, r) ← mathChunk cs
      let s ← Math.parseFormula ts
      let r1 ← kw [w!"has"] r <|> kw [w!"have"] r
      let first ← match r1 with | .w w :: _ => some w | _ => none
      if [w!"a", w!"an", w!"no", w!"the", w!"exactly", w!"at", w!"one", w!"two", w!"some", w!"infinitely",
          w!"finitely", w!"only", w!"been", w!"to", w!"order", w!"index", w!"length"].contains first then none
      let ws := r1.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"and", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then", w!"whenever", w!"of", w!"in", w!"with", w!"or", w!"iff", w!"that"].contains w
        | .p 45 => true
        | _ => false
      if ws.length < 2 then none
      let rest := r1.drop ws.length
      if (match rest with | .m _ :: _ => true | _ => false) then none
      some (Clause.isA s ([Chunk.w w!"with"] ++ ws) false, rest) : Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$G$ contains a Hamiltonian cycle`: as `has` (words only, a modifier `with a …`)
  match (do
      let (ts, r) ← mathChunk cs
      let _ ← Math.parseFormula ts
      let r1 ← kw [w!"contains"] r
      let r2 ← kw [w!"a"] r1 <|> kw [w!"an"] r1
      let ws := r2.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"and", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then", w!"whenever", w!"of", w!"in", w!"with", w!"that"].contains w
        | .p 45 => true
        | _ => false
      if ws.isEmpty then none
      let rest := r2.drop ws.length
      if (match rest with | .m _ :: _ => true | _ => false) then none
      some (Clause.existsNP (ws ++ [Chunk.w w!"of", Chunk.m ts]) false none, rest) : Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$G$ has an even number of vertices of odd degree`: the number of those objects of the
  -- subject (the notion `number of … of $G$`) is even (odd)
  match (do
      let (ts, r) ← mathChunk cs
      let s ← Math.parseFormula ts
      let r1 ← kw [w!"has", w!"an"] r
      let (parity, r2) ← (kw [w!"even", w!"number", w!"of"] r1).map (w!"even", ·) <|>
        (kw [w!"odd", w!"number", w!"of"] r1).map (w!"odd", ·)
      let ws := r2.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"and", w!"or", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then", w!"whenever", w!"iff"].contains w
        | .p 45 => true
        | _ => false
      if ws.isEmpty then none
      let items := ws.filterMap fun (c : Chunk) => match c with
        | .w w => some (MT.text (lower w))
        | _ => none
      -- (`2k` or `2k+1` for an integer `k`, whatever the vocabulary says of `even`)
      let n := MT.app (.id w!"@the") ([MT.text w!"number", .text w!"of"] ++ items ++ [.text w!"of", s])
      let k : Codes := w!"@k"
      let twoK := MT.mul (.num 2) (.id k)
      let rhs := if parity == w!"even" then twoK else MT.add twoK (.num 1)
      some (Clause.fact (.quant false [k] (.id w!"\\mathbb{Z}") (.chain n [(.eq, rhs)])), r2.drop ws.length) :
      Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$K$ has exactly two ideals`, `$G$ has at least two elements of order $2$`, `$R$ has at
  -- most one maximal ideal`: the number of such objects of the subject, a number word
  match (do
      let (ts, r) ← mathChunk cs
      let r1 ← kw [w!"has"] r
      let (mode, r2) ← (kw [w!"exactly"] r1).map (0, ·) <|> (kw [w!"at", w!"least"] r1).map (1, ·) <|>
        (kw [w!"at", w!"most"] r1).map (2, ·)
      -- (`two`, …, after `exactly`, is `$2$` already)
      let words := [w!"one", w!"two", w!"three", w!"four", w!"five", w!"six"]
      let (k, r3) ← match r2 with
        | .w nw :: r3 => (words.findIdx? (· == nw)).map fun i => (i + 1, r3)
        | .m kt :: r3 => match Math.parseFormula kt with
          | some (.num n) => if n == 0 || n > 6 then none else some (n, r3)
          | _ => none
        | _ => none
      -- (`exactly one`: the unique object, read below)
      if mode == 0 && k == 1 then none
      let np := r3.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"and", w!"or", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then", w!"whenever"].contains w
        | .m _ => true
        | .p 45 => true
        | _ => false
      let rest := r3.drop np.length
      let head := np.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"of", w!"with", w!"in", w!"on", w!"at", w!"over", w!"to", w!"from", w!"satisfying"].contains w
        | .p 45 => true
        | _ => false
      if head.isEmpty || !(head.all fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false) then none
      if (Math.parseFormula ts).isNone then none
      some (Clause.countNP (head ++ [Chunk.w w!"of", Chunk.m ts] ++ np.drop head.length) mode k none, rest) :
      Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- `$f$ has a [unique] fixed point`, `$G$ has an element of order $2$`: there is such an
  -- object of the subject (the noun's complement `of $f$`, after the noun's words)
  match (do
      let (ts, r) ← mathChunk cs
      let r1 ← kw [w!"has"] r
      let (unique, r2) ← (kw [w!"a", w!"unique"] r1).map (true, ·) <|> (kw [w!"exactly", w!"one"] r1).map (true, ·) <|>
        (kw [w!"a"] r1).map (false, ·) <|> (kw [w!"an"] r1).map (false, ·)
      -- (not past `or`, `… or $n$ is prime`: another clause)
      let np := r2.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"and", w!"or", w!"if", w!"for", w!"where", w!"since", w!"which", w!"such", w!"then", w!"whenever"].contains w
        | .m _ => true
        | .p 45 => true
        | _ => false
      let rest := r2.drop np.length
      let head := np.takeWhile fun (c : Chunk) => match c with
        | .w w => ![w!"of", w!"with", w!"in", w!"on", w!"at", w!"over", w!"to", w!"from", w!"satisfying"].contains w
        | .p 45 => true
        | _ => false
      if head.isEmpty || !(head.all fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false) then none
      -- (`$x$ has a limit`: words about the formula's value, not a noun with a complement)
      if (Math.parseFormula ts).isNone then none
      some (Clause.existsNP (head ++ [Chunk.w w!"of", Chunk.m ts] ++ np.drop head.length) unique none, rest) :
      Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- SUBJ is the only N with $φ$ (and $ψ$)* | SUBJ is <words> of OBJ
  match subj cs with
  | some (s, r) =>
    match kw [w!"is", w!"the", w!"only"] r with
    | some r1 => do
      -- `the only NOUN with $\alpha=s$`, or with a variable: `the only NOUN $C$ with $\alpha(C)=s$`
      let ws := r1.takeWhile (fun c => match c with | .w v => v != w!"with" | _ => false)
      let noun := ws.filterMap (fun c => match c with | .w w => some w | _ => none)
      let (var, r2) := match r1.drop ws.length with
        | .m [.id v] :: rest => (some v, rest)
        | rest => (none, rest)
      if noun.isEmpty then none else
      let r3 ← kw [w!"with"] r2
      let (c1, r4) ← formula r3
      match kw [w!"and"] r4 >>= formula with
      | some (c2, r5) => some (.onlyWith s noun [c1, c2] var, r5)
      | none => some (.onlyWith s noun [c1] var, r4)
    | none =>
    match kw [w!"is"] r with
    | some r1 =>
      -- `the sum of the degrees of the vertices of $G$ is twice the number of edges of $G$`:
      -- twice (three times) a notion or a formula
      let multiple : Option (Clause × List Chunk) := match s, r1 with
        | .math lhs, .w tw :: r2 => do
          let k ← if tw == w!"twice" then some 2 else if tw == w!"thrice" then some 3 else none
          let (m, r3) ← (match r2 with
            | .w _ :: _ => notionSubj r2 true
            | _ => formula r2)
          some (.fact (.chain lhs [(.eq, .mul (.num k) m)]), r3)
        | _, _ => none
      match multiple with
      | some res => some res
      | none =>
      -- `the order of $G$ is $6$`: a notion subject equal to a term
      let isTerm : Option (Clause × List Chunk) := match s, r1 with
        | .math (.app (.id t) items), .m ts :: r2 =>
          if t != w!"@the" then none else do
          let m ← Math.parseFormula ts
          match m with
          | .chain _ _ => none
          | _ =>
            let ends := match r2 with
              | [] => true
              | .p c :: _ => c != 45
              | .w w :: _ => [w!"and", w!"if", w!"for", w!"where", w!"since", w!"so", w!"because", w!"when",
                  w!"whenever", w!"then", w!"which", w!"provided"].contains w
              | _ => false
            if ends then some (.fact (.chain (.app (.id t) items) [(.eq, m)]), r2) else none
        | _, _ => none
      match isTerm with
      | some res => some res
      | none =>
      -- (`is of measure zero`, where no object follows `of`: an adjective of the
      -- vocabulary, below)
      match (do
          let (phrase, r2) ← wordsUntil [w!"of"] 8 r1 []
          -- (`is of the same order as $g$`: an adjective that begins with `of`, below)
          if phrase.isEmpty then none
          let r3 ← kw [w!"of"] r2
          let (o, r4) ← obj r3
          -- (a phrase that goes on after its object, `is a periodic point of $f$ of period
          -- $n$`, `is a minimizer of $f$ on $[a,b]$`, is a noun phrase of the vocabulary, below)
          if (kw [w!"of"] r4 <|> kw [w!"on"] r4 <|> kw [w!"with"] r4).isSome then none
          -- (`… with right-hand side $f$`: the object stopped at a hyphen; `… with coefficients
          -- $1$ and $1$`: the last argument of the phrase follows)
          if listContinues r4 then none
          if (match r4 with
              | .p 45 :: _ => true
              | .w a :: .m _ :: rest =>
                (a == w!"and" && (match rest with | .w v :: _ => phraseGoesOn v | _ => true)) ||
                -- (`… of $f$ from $a$`: the phrase goes on with a preposition)
                [w!"from", w!"to", w!"at", w!"in", w!"under", w!"over", w!"between"].contains a
              -- (`… with kernel $K$ and right-hand side $g$`: the phrase goes on with another
              -- argument)
              | .w a :: .w b :: _ =>
                (a == w!"and" && b != w!"that" && b != w!"so" && b != w!"hence" && b != w!"thus") ||
                [w!"from", w!"to", w!"at", w!"in", w!"under", w!"over", w!"between", w!"up"].contains a
              | _ => false) then none
          some (Clause.pred s phrase o, r4)) with
      | some res => some res
      | none =>
        -- `$X$ is [not] a|an NP`, `$X$ is [not] ADJ`: the vocabulary's nouns and adjectives
        match s with
        | .math f => do
          let (neg, r2) := match kw [w!"not"] r1 with | some r' => (true, r') | none => (false, r1)
          let (np, r3) ← untilClauseEnd 32 r2 []
          -- `$v$ is a solution of … and a solution of …`: two noun phrases of the same object
          let andA := (List.range np.length).find? fun i => i > 0 && match (np[i]? : Option Chunk), (np[i+1]? : Option Chunk) with
            | some (Chunk.w a), some (Chunk.w b) => a == w!"and" && (b == w!"a" || b == w!"an")
            | _, _ => false
          if let some i := andA then
            if !neg then
              return (.both [.isA f (np.take i) false, .isA f (np.drop (i + 1)) false], r3)
          -- `$Q_t$ is a copula with $D(Q_t)=0$ [and $R(Q_t)=\sqrt t$]`: what follows `with`
          -- is said of the same object, as further clauses
          let withAt := np.findIdx? fun c => match c with | .w v => v == w!"with" | _ => false
          match withAt with
          | some i =>
            match np.drop (i + 1) with
            | [.m ts] =>
              if neg || i == 0 || !(Math.parseFormula ts).isSome then
                (if np.isEmpty then none else some (.isA f np neg, r3))
              else some (.isA f (np.take i) false, [.w w!"and", .m ts] ++ r3)
            | _ => if np.isEmpty then none else some (.isA f np neg, r3)
          | none => if np.isEmpty then none else some (.isA f np neg, r3)
        | _ => none
    | none =>
    match s, kw [w!"increases", w!"bijectively", w!"from"] r with
    | .math f, some r1 => do
      let (a, r2) ← formula r1
      let r3 ← kw [w!"onto"] r2
      let (b, r4) ← formula r3
      some (.increases f a b, r4)
    | _, _ =>
    -- $φ$ [for every $x\in A$] [, with equality only at $x=a$]
    match s with
    | .math f =>
      -- `$φ$ for $ψ$`, with a relation `ψ` that is no membership (`for $v\ge\frac12$`)
      match (do
          let r1 ← kw [w!"for"] r
          let (c, r2) ← formula r1
          match c with
          | .chain _ rs =>
            if rs.all (fun (rel, _) => rel == .lt || rel == .le || rel == .gt || rel == .ge || rel == .ne)
            then some (Clause.forCond f c, r2) else none
          | _ => none) with
      | some res => some res
      | none =>
      -- (a letter without a domain, `for all $x$`: a real number, or a natural number for an
      -- index of a subscript, `a_n\ge0` for all `n`)
      let bare (ts : List MTok) : Option (List Codes × MT) :=
        let parts : List (List MTok) := (Math.commaParts (ts.length + 1) 0 [] ts []).filter (!·.isEmpty)
        match parts.mapM (fun (p : List MTok) => match p with | [MTok.id v] => some v | _ => none) with
        | some (v :: vs) =>
          let nat := (v :: vs).all fun w => mtIndexedBy w 16 f
          some (v :: vs, MT.id (if nat then w!"\\mathbb{N}" else w!"\\mathbb{R}"))
        | _ => none
      let (vars, dom, r1) := match kw [w!"for", w!"every"] r <|> kw [w!"for", w!"all"] r with
        | some r' => match mathChunk r' with
          | some (ts, r'') => match binderMath ts <|> bare ts with
            | some (vs, d) => (vs, some d, r'')
            | none => ([], none, r)
          | none => ([], none, r)
        | none => ([], none, r)
      match punct 44 r1 >>= kw [w!"with", w!"equality", w!"only", w!"at"] with
      | some r2 => do
        let (at_, r3) ← formula r2
        some (.scoped f vars dom (some at_), r3)
      | none => some (.scoped f vars dom none, r1)
    | _ => none
  | none => none

/-- The standard adjectives of a clause alone, unless the vocabulary's reading of the
whole list (`$S$ is compact and perfect`, `compact` a standard adjective and `perfect`
one of a field) reads further. -/
def clause2 (cs : List Chunk) : Option (Clause × List Chunk) :=
  match clause1 cs with
  | some (.adjectives m adjs, r2) =>
    if moreWords r2 then
      match clause1 cs true with
      | some (c', r') => if r'.length < r2.length then some (c', r') else some (.adjectives m adjs, r2)
      | none => some (.adjectives m adjs, r2)
    else some (.adjectives m adjs, r2)
  | r => r

/-- A clause, or two of them joined by `if and only if` or by `or`
(`$S$ is compact if and only if $S$ is closed and bounded`, `$G$ is cyclic or $G$ is
isomorphic to $V$`). -/
def clause (cs : List Chunk) : Option (Clause × List Chunk) :=
  let iffW := [w!"if", w!"and", w!"only", w!"if"]
  -- the two clauses around the first `if and only if` (or `or`), each read whole
  let splitAt (ws : List Codes) (mk : Clause → Clause → Clause) : Option (Clause × List Chunk) := do
    let i ← (List.range cs.length).find? fun i => (kw ws (cs.drop i)).isSome
    if i == 0 then none
    -- (the first clause as a sentence of its own, with its full stop)
    let (p, r) ← clause2 (cs.take i ++ [.p 46])
    if !(match r with | [] | [.p 46] => true | _ => false) then none
    let (q, r2) ← clause2 (cs.drop (i + ws.length))
    some (mk p q, r2)
  let split : Option (Clause × List Chunk) := splitAt iffW .iffC <|> splitAt [w!"or"] .orC
  let hasWord (np : List Chunk) (w : Codes) : Bool := np.any fun c => match c with | .w v => v == w | _ => false
  match clause2 cs with
  | some (c, r) =>
    -- (a clause that stops before the connective, or a noun phrase that has swallowed it)
    let swallowed := match c with
      | .isA _ np _ => hasWord np w!"or" || (hasWord np w!"only" && hasWord np w!"if")
      -- (`$G$ is Eulerian if and only if every vertex of $G$ …` read as `is WORDS of $G$`)
      | .pred _ ws _ => ws.contains w!"or" || (ws.contains w!"only" && ws.contains w!"if")
      | _ => false
    if (kw iffW r).isSome || (kw [w!"or"] r).isSome || swallowed then split <|> some (c, r) else some (c, r)
  | none => split

/-- `CLAUSE and CLAUSE [and CLAUSE]`, the hypothesis of `if …, then …`: each clause read on
its own (`if $f$ is continuous and $g$ is dominated by $f$, then …`). -/
def andClauses (cs : List Chunk) : Option (Clause × List Chunk) := do
  let (c, r) ← clause cs
  let rec more : Nat → List Chunk → List Clause → List Clause × List Chunk
    | 0, r, acc => (acc.reverse, r)
    | f + 1, r, acc =>
      match (do let r1 ← kw [w!"and"] r; clause r1) with
      | some (c', r2) => more f r2 (c' :: acc)
      | none => (acc.reverse, r)
  let (rest, r') := more 4 r []
  some (if rest.isEmpty then c else .both (c :: rest), r')

/-- `CLAUSE for every|all|each NP`: a trailing noun-phrase binder (a binder written as
a formula, `for every $x\in A$`, belongs to the clause itself). -/
def everyNPAfter (c : Clause) (r : List Chunk) : Clause × List Chunk :=
  -- `CLAUSE for infinitely many NPs $q$`
  match (do
      let r1 ← kw [w!"for", w!"infinitely", w!"many"] r
      let (np, r2) ← untilClauseEnd 48 r1 []
      if np.isEmpty then none else some (Clause.infinitelyMany np (some c), r2)) with
  | some res => res
  | none =>
  -- `CLAUSE for [all] sufficiently large $n$`
  match (do
      let r1 := (kw [w!"for", w!"all"] r <|> kw [w!"for", w!"every"] r <|> kw [w!"for", w!"each"] r).getD
        ((kw [w!"for"] r).getD [])
      let (b, r2) ← sufficientBinder r1
      if clauseEnd r2 then some (Clause.under b c, r2) else none) with
  | some res => res
  | none =>
  -- `CLAUSE for $n$ sufficiently large`, `… if|whenever|provided [that] $n$ is sufficiently large`
  match (do
      let r1 ← kw [w!"for"] r <|> kw [w!"if"] r <|> kw [w!"whenever"] r <|>
        kw [w!"provided", w!"that"] r <|> kw [w!"provided"] r <|> kw [w!"as", w!"long", w!"as"] r
      let (b, r2) ← postSufficient r1
      if clauseEnd r2 then some (Clause.under b c, r2) else none) with
  | some res => res
  | none =>
  match kw [w!"for", w!"every"] r <|> kw [w!"for", w!"all"] r <|> kw [w!"for", w!"each"] r <|>
      kw [w!"for", w!"any"] r with
  | some r2 =>
    match r2 with
    | .w _ :: _ =>
      match untilClauseEnd 48 r2 [] with
      | some (np, r3) =>
        -- `for every NP and every NP`: the first binds first
        let rec split : Nat → List Chunk → List Chunk → List (List Chunk) → List (List Chunk)
          | 0, _, cur, acc => (cur.reverse :: acc).reverse
          | _ + 1, [], cur, acc => (cur.reverse :: acc).reverse
          | f + 1, .w a :: .w e :: rest, cur, acc =>
            if a == w!"and" && (e == w!"every" || e == w!"all" || e == w!"each" || e == w!"any") && !cur.isEmpty then
              split f rest [] (cur.reverse :: acc)
            else split f (.w e :: rest) (.w a :: cur) acc
          | f + 1, c0 :: rest, cur, acc => split f rest (c0 :: cur) acc
        let nps := split (np.length + 1) np [] []
        -- `each of the ten coefficients $A\in S$`: the words describe the members of `S`
        let nps := nps.map fun np => match np with
          | .w o :: .w t :: rest =>
            if o == w!"of" && t == w!"the" then
              match rest.dropWhile (fun c => match c with | .w _ => true | _ => false) with
              | [.m ts] => if (binderMath ts).isSome && rest.length ≥ 2 then [Chunk.m ts] else np
              | _ => np
            else np
          | _ => np
        (nps.foldr (fun np acc => Clause.forEveryNP acc np) c, r3)
      | none => (c, r)
    | _ => (c, r)
  | none => (c, r)

/-- `[,] for every B, CLAUSE` after `such that`: the clause under the binders. -/
def underBinder (sub : List Chunk → Option (Clause × List Chunk)) (cs : List Chunk) :
    Option (Clause × List Chunk) := do
  let cs := optPunct 44 cs
  let (b, r) ← binder cs
  let r ← punct 44 r
  let (c, r') ← sub r
  some (.under b c, r')

/-- `with the following property.`, `such that the following holds:` before the sentence
that states the property: the chunks of that sentence. -/
def followingProperty (cs : List Chunk) : Option (List Chunk) := do
  let r ← kw [w!"with", w!"the", w!"following", w!"property"] cs <|>
    kw [w!"such", w!"that", w!"the", w!"following", w!"holds"] cs
  match r with
  | .p 46 :: r' | .p 58 :: r' => some r'
  | _ => none

/-- The clauses after `such that`: `CLAUSE [and CLAUSE]*`, each with the binders after it
(`for every NP`). -/
def suchThatClauses (sub : List Chunk → Option (Clause × List Chunk)) (cs : List Chunk) :
    Option (Clause × List Chunk) := do
  let (c, r) ← underBinder sub cs <|> sub cs
  let (c, r) := everyNPAfter c r
  let rec more : Nat → List Chunk → List Clause → List Clause × List Chunk
    | 0, r, acc => (acc.reverse, r)
    | f + 1, r, acc =>
      match (do
          let r1 ← kw [w!"and"] r
          let (c', r2) ← underBinder sub r1 <|> sub r1
          some (everyNPAfter c' r2)) with
      | some (c', r2) => more f r2 (c' :: acc)
      | none => (acc.reverse, r)
  let (rest, r') := more 6 r []
  some (if rest.isEmpty then c else .both (c :: rest), r')

/-- `there is|exists [a constant] $C>0$ such that CLAUSE`; `sub` reads the clauses
after `such that`. -/
def thereIsWith (sub : List Chunk → Option (Clause × List Chunk)) (cs : List Chunk) :
    Option (Clause × List Chunk) := do
  let r ← kw [w!"there", w!"is"] cs <|> kw [w!"there", w!"exists"] cs <|> kw [w!"there", w!"are"] cs <|>
    kw [w!"there", w!"exist"] cs
  let r := (kw [w!"a", w!"constant"] r <|> kw [w!"constants"] r <|> kw [w!"a", w!"number"] r <|>
    kw [w!"an", w!"absolute", w!"constant"] r <|> kw [w!"absolute", w!"constants"] r <|>
    kw [w!"a", w!"universal", w!"constant"] r <|> kw [w!"universal", w!"constants"] r <|>
    kw [w!"a", w!"real", w!"number"] r <|> kw [w!"some"] r).getD r
  -- `there is no NP …`, `there are no NPs …`
  let (none_, r) := match kw [w!"no"] r with
    | some r' => (true, r')
    | none => (false, r)
  -- `there are infinitely many NPs [such that CLAUSE]`
  match (do
      let r1 ← kw [w!"infinitely", w!"many"] r
      let rec upToMany : Nat → List Chunk → List Chunk → Option (List Chunk × List Chunk)
        | 0, _, _ => none
        | f + 1, cs, acc =>
          if (kw [w!"such", w!"that"] cs).isSome || (followingProperty cs).isSome || clauseEnd cs then
            some (acc.reverse, cs) else
          match cs with
          | [] => none
          | c :: rest => upToMany f rest (c :: acc)
      let (np, r2) ← upToMany (r1.length + 1) r1 []
      if np.isEmpty then none else
      match followingProperty r2 <|> kw [w!"such", w!"that"] r2 with
      | some r3 => do
        let (c, r4) ← suchThatClauses sub r3
        some (Clause.infinitelyMany np (some c), r4)
      | none => some (Clause.infinitelyMany np none, r2)) with
  | some res => if none_ then none else some res
  | none =>
  -- `there are integers $a,b$ with $a+b=1$`, `there are real numbers $x_1,\ldots,x_n$
  -- [with $φ$] such that CLAUSE`: a variable for each (a sequence is one); without
  -- `such that`, the condition after `with` is the clause
  -- (`there are no positive integers $x,y,z$ with $φ$`: none such)
  let noneOf (c : Clause) : Clause := if none_ then Clause.noneExist c else c
  match (do
      let ws0 := r.takeWhile fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false
      -- (`integers $x$ and $y$`, as `integers $x,y$`)
      let (ts, r1) ← joinedVars (r.drop ws0.length)
      -- `there are distinct primes $p,q$`: a condition on all of them
      let (ws, ps) := collectiveWords 8 ws0
      if ws.isEmpty then none else
      let vars ← ((seqBound ts).map fun _ => [ts]) <|> splitVars ts
      let together : List Bind ← if ps.isEmpty then some [] else (collectiveCond ps vars).map ([Bind.ifCond ·])
      let nouns : List Bind := vars.map (fun v => Bind.noun (ws ++ [Chunk.m v])) ++ together
      match withConds r1 with
      | some (φ, r2) =>
        match followingProperty r2 <|> kw [w!"such", w!"that"] r2 with
        | some r3 => do
          let (c, r4) ← suchThatClauses sub r3
          some (noneOf (Clause.thereIs (.many (nouns ++ [Bind.ifCond φ])) c), r4)
        | none => if clauseEnd r2 then some (noneOf (Clause.thereIs (.many nouns) (.fact φ)), r2) else none
      | none => do
        let r2 ← followingProperty r1 <|> kw [w!"such", w!"that"] r1
        let (c, r3) ← suchThatClauses sub r2
        some (noneOf (Clause.thereIs (.many nouns) c), r3)) with
  | some res => some res
  | none =>
  -- `there exist NP, NP, and NP [satisfying DISPLAY] [such that CLAUSE, CLAUSE]`
  match (do
      -- the noun phrases: up to `satisfying`, `such that` or the end; a comma before a
      -- word (or `, and`) separates them
      let rec nps : Nat → List Chunk → List Chunk → List (List Chunk) → Option (List (List Chunk) × List Chunk)
        | 0, _, _, _ => none
        | f + 1, cs, cur, acc =>
          let stop := (kw [w!"satisfying"] cs).isSome || (kw [w!"such", w!"that"] cs).isSome ||
            (followingProperty cs).isSome || isEnd cs || (match cs with | .p 59 :: _ => true | _ => false)
          if stop then
            if cur.isEmpty then none else some ((cur.reverse :: acc).reverse, cs)
          else match cs with
            | .p 44 :: .w a :: rest =>
              if cur.isEmpty then none else
              let rest := if a == w!"and" then rest else .w a :: rest
              nps f rest [] (cur.reverse :: acc)
            | c :: rest => nps f rest (c :: cur) acc
            | [] => none
      let (list, r1) ← nps (r.length + 1) r [] []
      -- `and` before the last one without a comma: `a set $K$ and a force $f$`
      let list := list.flatMap fun np =>
        let rec splitAnd : Nat → List Chunk → List Chunk → List (List Chunk)
          | 0, cs, cur => [cur.reverse ++ cs]
          | _ + 1, [], cur => [cur.reverse]
          | f + 1, .w a :: .w d :: rest, cur =>
            if a == w!"and" && (d == w!"a" || d == w!"an") && !cur.isEmpty then
              cur.reverse :: splitAnd f (.w d :: rest) []
            else splitAnd f (.w d :: rest) (.w a :: cur)
          | f + 1, c :: rest, cur => splitAnd f rest (c :: cur)
        splitAnd (np.length + 1) np []
      let hasSat := (kw [w!"satisfying"] r1).isSome
      let unique := match list with
        | (.w a :: .w b :: _) :: _ => (a == w!"exactly" && b == w!"one") || (a == w!"a" && b == w!"unique")
        | _ => false
      -- (each object is a noun phrase: `there is $c>0$ such that …` is read below)
      if unique || list.any (fun np => match np with | .w _ :: _ => false | _ => true) then none else
      -- `satisfying DISPLAY|$φ$`
      let (sat, r2) ← match kw [w!"satisfying"] r1 with
        | some r' =>
          match display r' with
          | some (m, _, r'') => some ([Clause.fact m], r'')
          | none => do
            let (m, r'') ← formula r'
            some ([Clause.fact m], r'')
        | none => some ([], r1)
      -- `such that CLAUSE[, CLAUSE]*` (a display is a clause)
      let rec more : Nat → List Chunk → List Clause → Option (List Clause × List Chunk)
        | 0, cs, acc => some (acc.reverse, cs)
        | f + 1, cs, acc =>
          -- `, and consequently CLAUSE`: one more condition (that follows from the others)
          let cs' := (punct 44 cs).map fun r =>
            let r := (kw [w!"and"] r).getD r
            (kw [w!"consequently"] r).getD r
          match cs' with
          | some r =>
            match display r with
            | some (m, _, r') => more f r' (Clause.fact m :: acc)
            | none =>
              match sub r with
              | some (c, r') =>
                let (c, r'') := everyNPAfter c r'
                more f r'' (c :: acc)
              | none => some (acc.reverse, cs)
          | none =>
            -- `such that $φ$ and $ψ$`: one more condition, as after one object
            match (do
                let r1 ← kw [w!"and"] cs
                let (c', r2) ← underBinder sub r1 <|> sub r1
                some (everyNPAfter c' r2)) with
            | some (c', r2) => more f r2 (c' :: acc)
            | none => some (acc.reverse, cs)
      -- (a display may end with a comma)
      let r2 := if hasSat then match punct 44 r2 with
          | some r' => if (kw [w!"such", w!"that"] r').isSome then r' else r2
          | none => r2
        else r2
      let (conds, r5) ← match followingProperty r2 <|> kw [w!"such", w!"that"] r2 with
        | some r3 => do
          let (c, r4) ← (display r3).map (fun (m, _, r') => (Clause.fact m, r')) <|> underBinder sub r3 <|> sub r3
          let (c, r4) := everyNPAfter c r4
          more 6 r4 [c]
        | none => some ([], r2)
      -- (one object with at most one condition is `there is a NP such that …` below)
      if list.length < 2 && !hasSat && !none_ && conds.isEmpty then none else
      -- `an integer $Q(\nu)$`: the variable `Q`, for which `Q(\nu)` stands in the conditions
      let rw := list.map fun np => match np.reverse with
        | .m ts :: rest =>
          match depBinder ts with
          | some (toks, al, nm, []) => ((Chunk.m toks :: rest).reverse, [(al, nm)])
          | _ => (np, [])
        | _ => (np, [])
      let list := rw.map (·.1)
      let als := rw.flatMap (·.2)
      let conds := (sat ++ conds).map fun c => if als.isEmpty then c else Clause.aliased als c
      let c := Clause.existsNPs list conds
      some (if none_ then Clause.noneExist c else c, r5)) with
  | some res => some res
  | none =>
  -- (`there is no …` is read only as above, never as an existence)
  if none_ then none else
  -- `there is exactly one NP [such that …]`, `there is a NP …`
  match (do
      let (unique, r) ← (kw [w!"exactly", w!"one"] r).map (true, ·) <|> (kw [w!"a", w!"unique"] r).map (true, ·) <|>
        (kw [w!"a"] r).map (false, ·) <|> (kw [w!"an"] r).map (false, ·) <|> (kw [w!"one"] r).map (false, ·)
      match r with
      -- `there is a unique $y\in C$ with …`: one variable with its domain
      | .m ts :: r1 =>
        if !unique then none else
        let ([_], _) ← binderMath ts | none
        match followingProperty r1 <|> kw [w!"such", w!"that"] r1 <|> kw [w!"with"] r1 with
        | some r2 => do
          let (c, r4) ← suchThatClauses sub r2
          some (Clause.existsNP [.m ts] true (some c), r4)
        | none => if clauseEnd r1 then some (Clause.existsNP [.m ts] true none, r1) else none
      | .w _ :: _ =>
        -- the noun phrase ends at `such that` or at the end of the clause
        let rec upTo : Nat → List Chunk → List Chunk → Option (List Chunk × List Chunk)
          | 0, _, _ => none
          | f + 1, cs, acc =>
            if (kw [w!"such", w!"that"] cs).isSome || (followingProperty cs).isSome || clauseEnd cs then
              some (acc.reverse, cs) else
            match cs with
            | [] => none
            | c :: rest => upTo f rest (c :: acc)
        let (np, r1) ← upTo (r.length + 1) r []
        -- `an integer $Q(\nu)$`: the variable `Q`, for which `Q(\nu)` stands
        let (np, als) := match np.reverse with
          | .m ts :: rest =>
            match depBinder ts with
            | some (toks, al, nm, []) => ((Chunk.m toks :: rest).reverse, [(al, nm)])
            | _ => (np, [])
          | _ => (np, [])
        let wrap (c : Clause) : Clause := if als.isEmpty then c else .aliased als c
        match followingProperty r1 <|> kw [w!"such", w!"that"] r1 with
        | some r2 => do
          let (c, r4) ← suchThatClauses sub r2
          some (Clause.existsNP np unique (some (wrap c)), r4)
        | none => some (Clause.existsNP np unique none, r1)
      | _ => none) with
  | some res => some res
  | none =>
  -- `there are $c_1,c_2>0$ and $b_0$ such that`: several constants, each a bound or a
  -- name (a real number)
  let one (cs : List Chunk) : Option (Bind × List (MT × MT) × List Chunk) :=
    -- `an integer $n_0\ge3$`: a noun phrase of words and its variable
    (do
      let r ← kw [w!"a"] cs <|> kw [w!"an"] cs
      let ws : List Chunk := r.takeWhile fun c => match c with
        | Chunk.w w => w != w!"such" && w != w!"and"
        | _ => false
      if ws.isEmpty then none else
      match r.drop ws.length with
      | Chunk.m ts :: r' =>
        -- `an integer $Q(\nu)$`: the variable `Q`
        match depBinder ts with
        | some (toks, al, nm, []) => some (Bind.noun (ws ++ [Chunk.m toks]), [(al, nm)], r')
        | some _ => none
        | none => some (Bind.noun (ws ++ [Chunk.m ts]), [], r')
      | _ => none) <|> do
    let (ts, r1) ← mathChunk cs
    -- `$c(C)>0$`, `$Q=Q(\nu)$`: the constant, and its name
    let (ts, als) := match depBinder ts with
      | some (toks, al, nm, rest) =>
        -- (the bound after the name, as tokens: from the formula after the first relation)
        let i := ts.findIdx? fun t => (Math.relOf t).isSome
        let boundToks := match rest, i with
          | [], _ => some []
          | _, some i =>
            -- `Q=Q(\nu)>0`: after the second relation
            let after := ts.drop (i + 1)
            if (match ts[i]? with | some t => Math.relOf t == some Rel.eq | none => false) then
              match after.findIdx? fun t => (Math.relOf t).isSome with
              | some j => some (after.drop j)
              | none => some []
            else some (ts.drop i)
          | _, none => none
        match boundToks with
        | some bt => (toks ++ bt, [(al, nm)])
        | none => (ts, [])
      | none => (ts, [])
    let b ← (do let (vs, d) ← binderMath ts; some (Bind.every vs d)) <|>
      (match Math.parseFormula ts with
        | some (.id v) => some (Bind.every [v] (.id w!"\\mathbb{R}"))
        | some (.sub (.id k) (.id i)) => some (Bind.every [k ++ [95] ++ i] (.id w!"\\mathbb{R}"))
        | some (.sub (.id k) (.num n)) =>
          some (Bind.every [k ++ [95] ++ (Nat.toDigits 10 n).map Char.toNat] (.id w!"\\mathbb{R}"))
        | _ => none)
    some (b, als, r1)
  let rec moreConsts : Nat → List Chunk → List Bind → List (MT × MT) → List Bind × List (MT × MT) × List Chunk
    | 0, cs, acc, als => (acc.reverse, als, cs)
    | f + 1, cs, acc, als =>
      match ((punct 44 cs).bind fun r => (kw [w!"and"] r).getD r |> some) <|> kw [w!"and"] cs with
      | some r =>
        match one r with
        | some (b, al, r') => moreConsts f r' (b :: acc) (als ++ al)
        | none => (acc.reverse, als, cs)
      | none => (acc.reverse, als, cs)
  let (b0, al0, r1) ← one r
  let (bs, als, r1) := moreConsts 4 r1 [] al0
  let b := match bs with
    | [] => b0
    | bs => Bind.many (b0 :: bs)
  -- `such that CLAUSE`, `with the following property. CLAUSE` (the next sentence)
  let r2 ← followingProperty r1 <|> kw [w!"such", w!"that"] r1
  let (c, r4) ← suchThatClauses sub r2
  some (.thereIs b (if als.isEmpty then c else .aliased als c), r4)

/-- `there is …` with plain clauses as its conditions. -/
def thereIs0 (cs : List Chunk) : Option (Clause × List Chunk) := thereIsWith clause cs

/-- `there is …`; a condition may itself be `there is …` (`…, and consequently there are
no NPs such that …`). -/
def thereIs (cs : List Chunk) : Option (Clause × List Chunk) :=
  thereIsWith (fun r => thereIs0 r <|> clause r) cs

/-- A reason in words up to a comma: words, and formulas that state nothing (`$(U_i,V_i)$`,
no relation), with at least two words. The chunks from the comma on. -/
def wordsReason (cs : List Chunk) : Option (List Chunk) :=
  let inReason : Chunk → Bool := fun c => match c with
    | .w _ | .p 45 => true
    | .m ts => match Math.parseFormula ts with
      | some (.chain _ _) | some (.land _ _) | some (.lor _ _) | some (.limp _ _) | some (.liff _ _)
      | some (.lnot _) | some (.quant ..) | none => false
      | _ => true
    | _ => false
  let part := cs.takeWhile inReason
  let nw := (part.filter fun c => match c with | .w _ => true | _ => false).length
  let rest := cs.drop part.length
  match rest with
  | .p 44 :: r =>
    if nw < 2 then none else
    -- (a relative clause in words after a comma belongs to the reason: `since the
    -- hypothesis applies to $C_\varepsilon$, whose maximal correlation is $1$,`)
    match r with
    | .w w :: r' =>
      if w == w!"whose" || w == w!"which" then
        match r'.dropWhile inReason with
        | .p 44 :: r'' => some (.p 44 :: r'')
        | _ => some rest
      else some rest
    | _ => some rest
  | _ => none

/-- A clause with its leading citations: `By CITE, ...`, `CITE gives ...`, trailing `by CITE`. -/
def cclause (cs : List Chunk) : Option (CClause × List Chunk) :=
  let afterBy (r' : List Chunk) : List Chunk :=
    -- `By CITE, we have $φ$`: the words after the citation assert nothing
    let r' := optPunct 44 r'
    ([[w!"we", w!"have"], [w!"we", w!"obtain"], [w!"we", w!"get"], [w!"it", w!"follows", w!"that"],
      [w!"we", w!"see", w!"that"]].findSome? fun m => kw m r').getD r'
  -- a reason in words beside the citations asserts nothing: `By \eqref{a} and the substitution
  -- $t\mapsto1-t$,`, `By independence of the two observations and \eqref{a},`, `By the
  -- intermediate value theorem,`
  let byPart : Option (List Codes × List Chunk) :=
    -- `since WORDS, CLAUSE` (`and since the first $n$ observations are independent, $φ$`)
    (do let r ← kw [w!"since"] cs
        let r ← wordsReason r
        let r ← punct 44 r
        if (clause r).isNone && (thereIs r).isNone then none else
        some ([], r)) <|> do
    let r ← kw [w!"by"] cs
    match cite r with
    | some (l, r1) =>
      let (ls, r2) := moreCites 6 r1
      let r2 := match kw [w!"and"] r2 with
        | some r3 => let (n, r4) := reasonSpan r3; if n ≥ 1 && (punct 44 r4).isSome then r4 else r2
        | none => r2
      some (l :: ls, afterBy r2)
    | none =>
      -- `By the equality in the proof of Theorem~\ref{t},`: words, then citations
      match wordsCite 24 r 0 with
      | some (n, l, r1) =>
        let (ls, r2) := moreCites 6 r1
        if n == 0 || (punct 44 r2).isNone then none else some (l :: ls, afterBy r2)
      | none =>
      let (n, r1) := reasonSpan r
      if n == 0 then none else
      -- (the words may be followed by citations: `and \eqref{a}`)
      let (ls, r2) : List Codes × List Chunk := match kw [w!"and"] r1 >>= cite with
        | some (l, r3) => let (ls, r4) := moreCites 6 r3; (l :: ls, r4)
        | none =>
          -- (a word that ends the span before `and \eqref`: the span stopped at the citation)
          match r1 with
          | .r .eqref l :: r3 => let (ls, r4) := moreCites 6 r3; (l :: ls, r4)
          | _ => ([], r1)
      if (punct 44 r2).isNone then none else
      some (ls, afterBy r2)
  let (pre, r0) : List Codes × List Chunk := byPart.getD ([], cs)
  -- CITE [with $m=1$] gives $φ$; WORDS give $φ$ (`The bounds for $D$ and $\Phi^2$ give …`)
  let givesAfter (r1 : List Chunk) : Option (List Chunk) :=
    let r1 := match kw [w!"with"] r1 with
      | some r' => match r' with
        | .m _ :: r'' => r''
        | _ => r1
      | none => r1
    kw [w!"gives"] r1 <|> kw [w!"give"] r1 <|> kw [w!"yields"] r1
  match cite r0 with
  | some (l, r1) =>
    match givesAfter r1 with
    | some r2 => do
      let (m, r3) ← formula r2
      some (⟨pre ++ [l], .fact m, [], [], []⟩, r3)
    | none => do
      -- `CITE bounds $X$ by $Y$`: `X ≤ Y`
      let r2 ← kw [w!"bounds"] r1
      let (x, r3) ← formula r2
      let r4 ← kw [w!"by"] r3
      let (y, r5) ← formula r4
      some (⟨pre ++ [l], .fact (.chain x [(.le, y)]), [], [], []⟩, r5)
  | none =>
  match (do
      let (n, r1) := reasonSpan r0
      if n < 2 then none
      let r2 ← kw [w!"gives"] r1 <|> kw [w!"give"] r1
      let (m, r3) ← formula r2
      some (m, r3)) with
  | some (m, r3) => some (⟨pre, .fact m, [], [], []⟩, r3)
  | none => do
    -- a hypothesis about bound variables: `if $φ$, CLAUSE`
    let (hyp, r0) : Option MT × List Chunk :=
      match (do
          let r ← kw [w!"if"] r0
          let (m, r') ← formula r
          let r'' ← punct 44 r'
          some (m, (kw [w!"then"] r'').getD r'')) with
      | some (m, r) => (some m, r)
      | none => (none, r0)
    -- a hypothesis that is a clause about bound variables: `if $n$ is even, CLAUSE`,
    -- `if $a$ and $b$ are relatively prime, then CLAUSE`
    let (hypC, r0) : Option Clause × List Chunk :=
      if hyp.isSome then (none, r0) else
      match (do
          let r ← kw [w!"if"] r0
          -- (`if there is $\mu\in\Gamma$ such that $\mu(K)=1$, then …`: an existence as a
          -- hypothesis)
          let (h, rest) ← andClauses r <|> thereIs r
          let r' ← punct 44 rest
          some (h, (kw [w!"then"] r').getD r')) with
      | some (h, r) => (some h, r)
      | none => (none, r0)
    -- a clause's own binder: `for $b\in B$, CLAUSE`
    let (bs, r0) : List Bind × List Chunk :=
      match kw [w!"for"] r0 >>= mathChunk with
      | some (ts, r) =>
        match binderMath ts, punct 44 r with
        | some (vs, d), some r' => ([.every vs d], r')
        | _, _ => ([], r0)
      | none => ([], r0)
    let (c, r1) ← thereIs r0 <|> clause r0
    let (c, r1) := everyNPAfter c r1
    let c := match hyp with | some m => Clause.ifThen m c | none => c
    let c := match hypC with | some h => Clause.ifClause h c | none => c
    let post := (kw [w!"by"] r1 >>= cite) <|> (kw [w!"as", w!"specified", w!"in"] r1 >>= cite)
    let (cites, r2) := match post with
      | some (l, r2) => let (ls, r2') := moreCites 6 r2; (pre ++ l :: ls, r2')
      | none => (pre, r1)
    -- `… for $F(x)=e$`: a definition for the sentence
    let (fds, r2) : List MT × List Chunk := match kw [w!"for"] r2 >>= formula with
      | some (.chain lhs [(rel, rhs)], r3) =>
        if rel != .eq && rel != .defeq then ([], r2) else
        match lhs with
        | .app (.id _) _ | .id _ => ([.chain lhs [(.defeq, rhs)]], r3)
        | _ => ([], r2)
      | _ => ([], r2)
    -- `…, where $g(x)\coloneqq x-1$ [and $h\coloneqq …$]`
    match punct 44 r2 >>= kw [w!"where"] with
    | some r3 => do
      let (ds, r4) ← whereDefs 4 r3 []
      some (⟨cites, c, bs, ds, fds⟩, r4)
    | none => some (⟨cites, c, bs, [], fds⟩, r2)
where
  /-- Definitions `$X\coloneqq e$` separated by `,` and `and`. -/
  whereDefs : Nat → List Chunk → List MT → Option (List MT × List Chunk)
    | 0, _, _ => none
    | f + 1, cs, acc => do
      let (m, r) ← formula cs
      match m with
      | .chain _ ((.defeq, _) :: _) =>
        let acc := m :: acc
        match (punct 44 r >>= fun r' => (kw [w!"and"] r').getD r' |> some) <|> kw [w!"and"] r with
        | some r' =>
          match formula r' with
          | some (.chain _ ((.defeq, _) :: _), _) => whereDefs f r' acc
          | _ => some (acc.reverse, r)
        | none => some (acc.reverse, r)
      | _ => none

/-- `in $L^2([0,1]^m)$`, `in $L^2$`: the space in which a formula of the field `hilbert` is
meant, which its operands say already. The chunks after it. -/
def spaceQualifier (cs : List Chunk) : Option (List Chunk) := do
  let r ← kw [w!"in"] cs
  match r with
  | .m ts :: r' =>
    match Math.parseFormula ts with
    | some (.sup (.id [76]) (.num 2)) => some r'
    | some (.app (.sup (.id [76]) (.num 2)) _) => some r'
    | some (.mul (.sup (.id [76]) (.num 2)) _) => some r'
    | _ => none
  | _ => none

/-- `INFORMAL, that is, FORMAL`: the words before `, that is,` (which may state things
informally, with formulas) are restated by what follows, which is read instead. The chunks
after the first `, that is,` (none if there is none, or nothing before it). -/
def skipThatIs (cs : List Chunk) : Option (List Chunk) :=
  go 96 cs 0
where
  go : Nat → List Chunk → Nat → Option (List Chunk)
    | 0, _, _ => none
    | f + 1, cs, n =>
      match cs with
      | .p 44 :: .w a :: .w b :: .p 44 :: r =>
        if a == w!"that" && b == w!"is" then (if n ≥ 1 then some r else none)
        else go f (cs.drop 1) (n + 1)
      | .p 46 :: _ => none
      | _ :: r => go f r (n + 1)
      | [] => none

/-- Clauses separated by `, and` / `, so`, ending with the final period. -/
def clauses : Nat → List Chunk → List CClause → Option (List CClause)
  | 0, _, _ => none
  | f + 1, cs0, acc0 =>
  -- (the clauses as written, or the formal restatement after `, that is,`; a local function,
  -- so that the recursion stays structural in the fuel, which the audit needs)
  let step (cs : List Chunk) (acc : List CClause) : Option (List CClause) := do
    let (c, r) ← cclause cs
    let r := (spaceQualifier r).getD r
    -- `…, which is at most $Z$` (`at least`): the last term of the claim is at most `Z`
    let (extra, r) : List CClause × List Chunk :=
      match c.clause, punct 44 r >>= kw [w!"which", w!"is", w!"at"] with
      | .fact (.chain _ rest), some r' =>
        match rest.getLast?, (kw [w!"most"] r').map (Rel.le, ·) <|> (kw [w!"least"] r').map (Rel.ge, ·) with
        | some (_, y), some (rel, r'') =>
          match formula r'' with
          | some (z, r3) => ([{ cites := [], clause := .fact (.chain y [(rel, z)]) }], r3)
          | none => ([], r)
        | _, _ => ([], r)
      | _, _ => ([], r)
    -- `…, with equality if and only if $φ$ [almost surely]`: equality in the inequality just
    -- stated holds exactly when `φ` does
    let (extra, r) : List CClause × List Chunk :=
      if !extra.isEmpty then (extra, r) else
      let ineq : Option MT := match c.clause with
        | .fact m => some m
        | .scoped m [] none none => some m
        | _ => none
      match ineq, punct 44 r >>= kw [w!"with", w!"equality", w!"if", w!"and", w!"only", w!"if"] with
      | some (.chain x [(rel, y)]), some r' =>
        if rel != .le && rel != .ge then ([], r) else
        match formula r' with
        | some (m, r3) =>
          let (m, r3) := match kw [w!"almost", w!"surely"] r3 with
            | some r4 => (MT.app (.id w!"@rae") [m], r4)
            | none => (m, r3)
          ([{ cites := [], clause := .iff (.chain x [(.eq, y)]) m }], r3)
        | none => ([], r)
      | _, _ => ([], r)
    let acc := extra ++ c :: acc
    -- a reason in words only (`…, since the square root is injective.`) asserts nothing
    -- (and formulas that state nothing: `…, since $W_r$ is the copula of $(U,1-V)$ when …`)
    let r := match punct 44 r >>= kw [w!"since"] <|> kw [w!"since"] r with
      | some r' =>
        -- (with references to sections and their items: `of Section~\ref{s}~(d)`)
        let ws := r'.takeWhile fun c => descChunk c || match c with
          | .r _ _ | .p 40 | .p 41 | .p 44 => true
          | _ => false
        if ws.any (fun c => match c with | .w _ => true | _ => false) && isEnd (r'.drop ws.length) then r'.drop ws.length else r
      | none => r
    if isEnd r then some acc.reverse
    else
      -- `, and`, `, so`, `, whereas`, or `and` between two formulas, or `,` before a
      -- formula (`$φ$, $ψ$ and $χ$`)
      let next := (do
        let r' ← punct 44 r
        (kw [w!"and"] r' >>= showsThat) <|>
        kw [w!"and"] r' <|> kw [w!"so"] r' <|> kw [w!"whereas"] r' <|>
          -- `, which gives $φ$`, `, that is, $φ$`: the next claim
          kw [w!"which", w!"gives"] r' <|> (kw [w!"that", w!"is"] r' >>= punct 44) <|>
          (match r' with | .m _ :: _ => some r' | _ => none) <|>
          -- `…, with $φ$ for $v\ge\frac12$ and …`: further claims about the same objects
          (match kw [w!"with"] r' with
           | some (.m t :: r'') => some (.m t :: r'')
           | _ => none)) <|> kw [w!"and"] r
      -- `…, and the two reflections satisfy DISPLAY, as well as DISPLAY`: words that only
      -- lead to the next formula
      let lead (r0 : List Chunk) : Option (List Chunk) :=
        let r1 := optPunct 44 r0
        (do
          let r2 ← kw [w!"as", w!"well", w!"as"] r1
          match r2 with | .m _ :: _ | .d .. :: _ => some r2 | _ => none) <|>
        (do
          let r2 ← kw [w!"and"] r1
          let ws := r2.takeWhile (fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false)
          if ws.isEmpty || ws.length > 6 then none
          if !(match ws.getLast? with
              | some (.w w) => [w!"satisfy", w!"satisfies", w!"obey", w!"obeys", w!"fulfil", w!"fulfill"].contains w
              | _ => false) then none
          match r2.drop ws.length with | .m t :: r3 => some (.m t :: r3) | .d t l :: r3 => some (.d t l :: r3) | _ => none)
      let next := lead r <|> next
      match next with
      | some r'' => clauses f r'' acc
      | none => none
  step cs0 acc0 <|> (skipThatIs cs0 >>= fun r => step r acc0)

/-- A definition item `the NAME [of $x$ ...] is DEF`. -/
structure DefItem where
  name : List Codes
  defn : MT
  labels : List Codes
  deriving Repr, Inhabited

def defItem (cs : List Chunk) : Option (DefItem × List Chunk) := do
  let r := (kw [w!"the"] cs).getD cs
  -- name words, possibly with `of $x$`, until `is`
  let rec nameWords : Nat → List Chunk → List Codes → Option (List Codes × List Chunk)
    | 0, _, _ => none
    | _ + 1, [], _ => none
    | g + 1, c :: rest, acc =>
      match c with
      | .w v => if v == w!"is" || v == w!"are" then some (acc.reverse, rest) else nameWords g rest (v :: acc)
      | .m _ => nameWords g rest acc
      | _ => none
  let (name, r1) ← nameWords 16 r []
  -- (`we have that …`, `one has …`, `it holds that …`: a claim, no name)
  if (match name.head? with | some w => [w!"we", w!"one", w!"it"].contains (lower w) | none => true) then none
  match display r1 with
  | some (m, ls, r2) => some (⟨name, m, ls⟩, r2)
  | none => do
    let (m, r2) ← formula r1
    some (⟨name, m, []⟩, r2)

/-- Trailing bibliographic remarks without mathematical content. -/
def trailer (cs : List Chunk) : List Chunk :=
  let cs' := optPunct 44 cs
  -- words without a formula to the end of the sentence: a remark that asserts nothing
  -- (`, which emphasizes the leading ranks of both variables.`)
  let wordsOnly (r : List Chunk) : Bool :=
    !r.isEmpty && (r.getLast? matches some (.p 46)) && r.dropLast.all fun c => match c with
      | .w _ | .p 44 | .p 45 | .r .cite _ => true
      | _ => false
  let tail (r : List Chunk) : List Chunk := match r with
    | .p 44 :: r' => if wordsOnly r' then [.p 46] else r
    | _ => r
  match kw [w!"as", w!"given", w!"in"] cs' <|> kw [w!"see"] cs' with
  | some (.r .cite _ :: r) => tail r
  | _ =>
    match kw [w!"from"] cs' >>= cite with
    | some (_, r) => r
    | none =>
      match punct 44 cs >>= kw [w!"which"] with
      | some r => if wordsOnly r then [.p 46] else cs
      | none => cs

/-- A piece of a definition `define $f:A\to B$ by PIECES`: a defining formula
(inline or displayed, possibly with its domain), or `on $D$, parametrically by
DISPLAY`. -/
inductive DefPiece where
  | formula (m : MT)
  | param (dom : MT) (m : MT)
  deriving Repr, Inhabited

/-- In a definition of `f` by its values, `f(x,y)=e` defines like `f(x,y)\coloneqq e`. -/
def piecesDefeq : DefPiece → DefPiece
  | .formula (.chain (.app (.id f) args) [(.eq, rhs)]) =>
    if args.all (fun a => match a with | .id _ => true | _ => false) then
      .formula (.chain (.app (.id f) args) [(.defeq, rhs)])
    else .formula (.chain (.app (.id f) args) [(.eq, rhs)])
  | p => p

/-- The condition of a notion the article defines. -/
inductive NotionCond where
  /-- `$φ$ [for all $u,v\in A$]` -/
  | formula (f : MT) (binds : List Bind)
  /-- `[for every $v\in A$,] the map $x\mapsto e$[, $x\in D$,] is non-increasing` -/
  | mono (binds : List Bind) (map : MT) (mono : Mono)
  /-- A clause about the subject: `A group $G$ is called nice if $G$ is abelian.` -/
  | clause (c : Clause)
  deriving Repr, Inhabited

/-- What a description describes: the least or the greatest of the numbers it names, or
how many there are. -/
inductive DescKind where
  | least | greatest | count
  deriving Repr, Inhabited, BEq

inductive Sent where
  | defClass (sym : MT) (plural : List Codes) (np : List Chunk)
  | defIs (bind : Bind) (items : List DefItem)
  | defReads (bind : Bind) (name : List Codes) (sig : MT) (disp : MT) (labels : List Codes)
  /-- `For B, define $f_b:A\to B$ by DISPLAY.`: a family of maps, one for each value of
  the binder's variable (`f_b`, `f^0_b`, `f_b^+`). -/
  | defByFamily (bind : Bind) (sig : MT) (pieces : List DefPiece) (labels : List Codes)
  | defBy (sig : MT) (pieces : List DefPiece) (labels : List Codes) (observe : Option (MT × List Codes × MT))
  | denotedBy (name : List Chunk) (sym : MT)
  | letDenote (bind : Bind) (sym : MT) (np : List Chunk)
  /-- `Let DISPLAY denote the NAME, NAME, and NAME NOUNS.`, `Let $f(x)\coloneqq e$ denote the
  NAME NOUN.`: definitions, each named by one of the names, of objects of the noun. The
  variables of a definition range over the arguments of the noun's objects (of a copula:
  the points of `[0,1]`), and that each defined object is such an object is a claim. -/
  | defsNamed (defs : List MT) (labels : List Codes) (np : List Chunk)
  /-- `Let $Y$ be an integrable random variable with continuous distribution function $F$`
  and `let $Z$ be uniformly distributed on $[0,1]$ and defined on the same probability
  space`: the two random variables of a result. Together they are a random pair, which
  the result is about through its joint law. -/
  | randomVar (y : Codes) (integrable : Bool) (df : Option Codes) (continuous : Bool)
  | uniformVar (z : Codes) (dom : MT)
  /-- `For B, [set $X\coloneqq e$ and] let $S$ be NP[, where $sig$ is given by DISPLAY]`. -/
  | defSteps (bind : Bind) (sets : List MT) (sym : MT) (np : List Chunk) (whereDef : Option (MT × MT × List Codes))
  | weSay (subj : List Chunk) (phrase : List Codes) (obj : List Chunk) (cond : MT)
      (vars : List Codes) (dom : MT)
  | claims (topic : Topic) (binds : List Bind) (cs : List CClause)
  /-- `Set $X\coloneqq e$.`, `Define DISPLAY.`, `The NAME is $X\coloneqq e$.`, and
  under a binder `For B, set $f(x)\coloneqq e$.`: definitions of constants (or of
  functions of the binder's variable), possibly several, each `\coloneqq`. -/
  | constDefs (bind : Option Bind) (defs : List MT) (labels : List Codes)
  /-- `[For B,] let $L$ be|denote DESC`, `Define $L$ to be|as DESC`, `[We] write $L$ for
  DESC`, `[We] denote by $L$ DESC`, where DESC is `the least|smallest|minimal NP $m$ [such
  that|for which CLAUSE]`, `the largest|greatest|maximal …` or `the number of NPs [$m$]
  [such that|for which CLAUSE]`: the definition of a symbol, or of a function of the
  variables written in it (`j(n)`), by a description. `asNotation` is the reading of `We
  write $L$ for the WORDS` as a notation for an operation of the vocabulary (`the greatest
  common divisor of $a$ and $b$`), which comes first. -/
  | defDesc (bind : Option Bind) (lhs : MT) (kind : DescKind) (np : List Chunk) (cond : Option Clause)
      (asNotation : Option (Nat × List Chunk))
  /-- `fix $B$ [and define|set|put DEFS]`: the binder stays fixed for the following
  sentences of the section (its variable names the same object until the section
  ends or the variable is fixed again); the definitions are made under it. -/
  | fix (bind : Bind) (defs : List MT) (labels : List Codes)
  /-- `Let $x\in A$.` in a result: `x` is bound for the rest of the result. -/
  | assume (bind : Bind)
  /-- Functions given by a value at one point and their derivative:
  `[For B, set DEFS, and] define continuous functions $f,g:A\to\R$ by $f(a)=c$, …,
  and DISPLAY` or `Let $f,g:A\to\R$ be continuous, normalized by $f(a)=c$ and …,
  with derivatives DISPLAY`, where the display gives `f'(x)` (piecewise). -/
  | defDeriv (bind : Option Bind) (sets : List MT) (names : List MT) (dom cod : MT) (anchors : List MT)
      (derivs : MT) (labels : List Codes)
  /-- `We call a NOUN $x$ NAME [(ABBR)] if COND.`, `[A NOUN] $x$ is called NAME [(ABBR)]
  if COND.`, `$x$ is NAME (ABBR) if COND.`: a notion of the article. `subj` is the noun
  phrase with its variable, or the variable alone (the subject of the previous notion). -/
  | defNotion (subj : List Chunk) (name : List Codes) (abbr : List Codes) (cond : NotionCond) (noun : Bool)
  /-- A notion whose condition the grammar does not read (`We call a copula $C$
  \emph{SI} if its Markov kernel can be chosen such that …`): prose, but its noun
  phrase is the subject of the notions that follow (`$C$ is \emph{LTD} if …`). -/
  | notionSubject (subj : List Chunk)
  /-- `Let $C$ be a NP[, and let $u,v\in A$][, and let $X\coloneqq e$, …].`, `Let
  $a,b\in A$, and let $X\coloneqq e$.`: variables of the rest of the result or proof,
  and definitions local to it. -/
  | assumeAll (binds : List Bind) (defs : List MT)
  /-- `Let $x$, $y$ and $z$ be as in Theorem~\ref{t}.`: the variables of the result `t`,
  with its hypotheses (the letters are all of its variables). -/
  | asIn (vars : List Codes) (label : Codes)
  /-- `Let $m$ be such that CLAUSE[, and let $X\coloneqq e$]`: a variable of the rest of the
  result or proof, chosen with the property that the clause states (a hypothesis about it),
  and definitions. -/
  | letSuchThat (v : Codes) (hyp : Clause) (defs : List MT)
  /-- `[DESCRIPTION,] we can find a NP $X$ such that CLAUSE`: an object of the noun phrase,
  chosen with the property that the clause states (a hypothesis about it). -/
  | letSuchThatNP (np : List Chunk) (hyp : Clause)
  /-- `Assume [that] CLAUSE [and CLAUSE].`, `Suppose …`, `We assume …`, `Assume further that
  …`, `Suppose, for contradiction, that …`: hypotheses of the following sentences of the
  result or proof (of the list item, inside one), until the proof or the item ends, a
  contradiction refutes them, or another case takes their place. `additive`: the words
  say that the hypothesis belongs to the one made before (`further`, `moreover`, `in
  addition`): the two end together; `caseLike`: they say that another case begins
  (`now`, `next`, `instead`, `conversely`): the hypothesis takes the place of the latest
  assumption of the proof; `contra`: made to be refuted (`for contradiction`).
  `asBinder`: the single formula `$x\in A$` as a binder, when its variable is new (as
  `Let $x\in A$.`). -/
  | suppose (hyps : List Clause) (additive caseLike contra : Bool) (asBinder : Option Bind)
  /-- `\item \emph{[Case 1:] CLAUSE [and CLAUSE].}`: the heading of a case, a hypothesis
  of the sentences of its item. -/
  | caseOf (hyps : List Clause)
  /-- `This is a contradiction.`, `We obtain a contradiction.`, `This contradicts
  Lemma~\ref{l}.`: under the hypotheses made, the false statement; it ends the
  hypothesis made for contradiction. -/
  | contradiction (cites : List Codes)
  /-- `CLAUSES, a contradiction.`, `CLAUSES, which is impossible.`: the claims, and then
  the contradiction. -/
  | claimsContra (topic : Topic) (binds : List Bind) (cs : List CClause)
  /-- `We distinguish two cases.`, `We argue by contradiction.`: a sentence of a proof that
  says how the argument is organized. It asserts nothing, and is read as such, so that
  it does not leave the proof incomplete. -/
  | organizes
  /-- `For Kendall's tau, we use the kernel $F=F_{\{1\}}+F_{\{2\}}+F_{\{1,2\}}$ from the proof of
  Theorem~\ref{l}.`: the definitions of that proof are visible in this one, and the formula
  (if it states something) is a claim. -/
  | usesFrom (label : Codes) (claim : Option MT)
  /-- `Throughout, $p$ and $q$ denote integers.`, `In this paper, the letter $t$ denotes
  an integer.`: wherever one of the letters is bound, it is an integer. -/
  | letters (vars : List Codes)
  /-- `Let $\chi(G)$ denote the chromatic number of a graph $G$.`, `We write $L$ for the
  WORDS [of NPs]`: a symbol for a quantity that neither the article nor its vocabulary
  defines. `words` name it (`chromatic number`), `args` are the noun phrases of its
  arguments. It is read so only if the sentence has no other reading. -/
  | undefined (lhs : MT) (words : List Codes) (args : List (List Chunk))
  /-- `We argue by induction on $n$.`: organizes the proof, and names the variable
  that `the statement holds for $E$` is about. -/
  | inductionOn (v : Codes)
  /-- `We write $T$ for $F$` (`kind` 0), `We write $T$ if $F$` (1), `We write $T$ for
  the NAME` (2, `rhs` the words and formulas of the name): a notation of the article. -/
  | notation (kind : Nat) (rhs : List Chunk)
  /-- `By a|an WORDS we mean a|an NP.`, `Throughout, a|an WORDS means a|an NP.` (`noun`),
  `By WORDS we mean WORDS'.`, `Throughout, WORDS means WORDS'.`: a convention of the
  article for a noun or for words. -/
  | meaning (words : List Codes) (rhs : List Chunk) (noun : Bool)
  /-- `A NP $f$ belongs to $\mathcal M_\alpha$ if $φ$ for every B.`, `We say that a NP $f$
  belongs to $\mathcal M$ if for every B, $φ$.`: a class of the article (with a parameter
  in its subscript). -/
  | defMember (subj : List Chunk) (cls : MT) (cond : MT) (binds : List Bind)
  /-- `Throughout, $C$ and $C_m$ denote positive constants.`, `In the definitions below,
  $C_{j,I}>0$ and $b_{j,I},d_{j,I}\ge0$ may depend on $j,I$ and the fixed data, and are
  uniform in $\ell$.`: generic constants, each with its sign (0 any, 1 positive, 2
  non-negative); what they may depend on (formulas and word phrases), when the sentence
  says; and what they are uniform in. -/
  | generic (syms : List (MT × Nat)) (deps : Option (List (List MTok) × List (List Codes)))
      (uniform : List (List MTok) × List (List Codes))
  deriving Repr, Inhabited

/-- `$f,g:A\to B$`: several names with one signature. -/
def namesSig (ts : List MTok) : Option (List MT × MT × MT) := do
  let i ← ts.findIdx? (· == .sym 58)
  let j ← ts.findIdx? (· == .cmd w!"to")
  if j < i then none else
  let rec split : List MTok → List MTok → List (List MTok) → List (List MTok)
    | [], cur, acc => (cur.reverse :: acc).reverse
    | t :: rest, cur, acc => if t == .sym 44 then split rest [] (cur.reverse :: acc) else split rest (t :: cur) acc
  let names ← (split (ts.take i) [] []).mapM Math.parseFormula
  let dom ← Math.parseFormula ((ts.drop (i + 1)).take (j - i - 1))
  let cod ← Math.parseFormula (ts.drop (j + 1))
  some (names, dom, cod)

/-- Formulas separated by `,`, `, and` or `and` (the values of functions at points). -/
def anchorList : Nat → List Chunk → List MT → Option (List MT × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc =>
    match formula cs with
    | some (m, r) =>
      let r' := (punct 44 r).getD r
      let r'' := (kw [w!"and"] r').getD r'
      anchorList f r'' (m :: acc)
    | none => if acc.isEmpty then none else some (acc.reverse, cs)

/-- A fixed variable: `$b\in B$`, or a condition `$\kappa>0$`. -/
def fixBinder (ts : List MTok) : Option Bind :=
  match binderMath ts with
  | some (vs, d) => some (.every vs d)
  | none =>
    match Math.parseFormula ts with
    -- `Let $\gamma$ be fixed.`: a real number
    | some (.id v) => some (.every [v] (.id w!"\\mathbb{R}"))
    | some (.sub (.id k) (.num n)) => some (.every [k ++ [95] ++ (Nat.toDigits 10 n).map Char.toNat] (.id w!"\\mathbb{R}"))
    | some (.sub (.id k) (.id i)) => some (.every [k ++ [95] ++ i] (.id w!"\\mathbb{R}"))
    | some m => some (.ifCond m)
    | none => none

/-- `X=e` after `set`: the definition `X\coloneqq e` of a symbol (`Q`, `S_*`, `\varepsilon`) or
of a function of variables (`f(x,y)`). -/
def asDefeq : MT → MT
  | .chain lhs [(.eq, rhs)] =>
    let ok := match lhs with
      | .id _ => true
      | .sub (.id _) _ => true
      | .app (.id _) args => args.all fun a => match a with | .id _ => true | _ => false
      | _ => false
    if ok then .chain lhs [(.defeq, rhs)] else .chain lhs [(.eq, rhs)]
  | m => m

def isDefeq : MT → Bool
  | .chain _ ((.defeq, _) :: _) => true
  | _ => false

/-- Definitions joined by `,` and `and`, inline or displayed (a display may hold
several, separated by `\qquad`). -/
def defList : Nat → List Chunk → List MT → List Codes → Option (List MT × List Codes × List Chunk)
  | 0, _, _, _ => none
  | f + 1, cs, acc, ls => do
    let (ms, ls', r) ← (do let (m, ls', r) ← display cs; some (m, ls', r)) <|>
      (do let (m, r) ← formula cs; some (m, [], r))
    let items := match ms with | .conj xs => xs | m => [m]
    let acc := acc ++ items
    let ls := ls ++ ls'
    let next := (punct 44 r >>= fun r' => (kw [w!"and"] r').getD r' |> some) <|> kw [w!"and"] r
    match next with
    | some r' =>
      match defList f r' acc ls with
      | some res => some res
      | none => some (acc, ls, r)
    | none => some (acc, ls, r)

/-- A range `x\in A` or `(x,z)\in A^2` as a binder. -/
def rangeBind : MT → Option Bind
  | .chain (.id x) [(.mem, d)] => some (.every [x] d)
  | .chain (.tuple xs) [(.mem, .sup d (.num k))] => do
    let vs ← xs.mapM fun x => match x with | .id v => some v | _ => none
    if vs.length == k && k ≥ 2 then some (.every vs d) else none
  | _ => none

/-- The definitions of `Set DEFS.`, `Define the NAME DISPLAY.`, and `Write DEFS for
$t\in A$.` (the binder after the definitions, as in `For $t\in A$, write DEFS.`). -/
def constDefsOf (b : Option Bind) (cs : List Chunk) : Option Sent := do
  -- `the weight`: the name of what the display defines
  let cs := match cs with
    | .w t :: rest =>
      let ws := rest.takeWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
      if t == w!"the" && ws.length ≤ 6 && (match rest.drop ws.length with | .d .. :: _ | .m _ :: _ => true | _ => false)
      then rest.drop ws.length else cs
    | _ => cs
  let (items, ls, r) ← defList 6 cs [] []
  -- (`let $K\coloneqq\{…\}$ be their contact set`: the name is not read)
  let r := match kw [w!"be", w!"the"] r <|> kw [w!"be", w!"their"] r <|> kw [w!"be", w!"its"] r with
    | some r2 =>
      let ws := r2.takeWhile (fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false)
      if !ws.isEmpty && ws.length ≤ 6 && isEnd (r2.drop ws.length) then r2.drop ws.length else r
    | none => r
  -- after `set`, `put`, `define`: `$Q=2^{-\ell}$` defines `Q` (a symbol, or a function of
  -- variables)
  let items := items.map asDefeq
  -- `b(x)\coloneqq x+1,\qquad x\in[0,1]`: the range of the variables, after the definitions
  let (items, b) := match b, items.reverse with
    | none, last :: defs@(_ :: _) =>
      match rangeBind last with
      | some bd => (defs.reverse, some bd)
      | none => (items, b)
    | _, _ => (items, b)
  if items.isEmpty || !items.all isDefeq then none else
  if isEnd (trailer r) then some (.constDefs b items ls) else
  match b, kw [w!"for"] r with
  | none, some r1 => do
    let (ts, r2) ← mathChunk ((kw [w!"every"] r1).getD r1)
    let (vs, d) ← binderMath ts
    if isEnd r2 then some (.constDefs (some (.every vs d)) items ls) else none
  | _, _ => none

/-- `class of [all]`, `set of [all]`. -/
def classOf (cs : List Chunk) : Option (List Chunk) := do
  let r ← kw [w!"class", w!"of"] cs <|> kw [w!"set", w!"of"] cs
  some ((kw [w!"all"] r).getD r)

/-- `NOUN $x$`, the noun phrase of a notion's subject with its variable, or `$x$`. -/
def nounVar (cs : List Chunk) : Option (List Chunk × List Chunk) :=
  let ws := cs.takeWhile (fun c => match c with
    | .w v => !notionStops.contains v
    | .p 45 => true
    | _ => false)
  match cs.drop ws.length with
  | .m [.id v] :: r => some (ws ++ [.m [.id v]], r)
  -- (`an element $g\in G$`: the variable with its domain)
  | .m ts :: r => match binderMath ts with
    | some ([_], _) => if ws.isEmpty then none else some (ws ++ [.m ts], r)
    | _ => none
  | _ => none

/-- `NAME [(ABBR)]`. -/
def nameAbbr (cs : List Chunk) : Option (List Codes × List Codes × List Chunk) := do
  let (name, r) := nameWords 8 cs []
  if name.isEmpty then none else
  match punct 40 r with
  | some r1 => do
    let (abbr, r2) := nameWords 4 r1 []
    let r3 ← punct 41 r2
    if abbr.isEmpty then none else some (name, abbr, r3)
  | none => some (name, [], r)

/-- `for every|all|each $x\in A$`. -/
def forBinder (cs : List Chunk) : Option (Bind × List Chunk) := do
  let r ← kw [w!"for", w!"every"] cs <|> kw [w!"for", w!"all"] cs <|> kw [w!"for", w!"each"] cs
  -- (`for all distinct $x,y\in X$`: different from each other)
  let (distinct, r) := match kw [w!"distinct"] r with | some r' => (true, r') | none => (false, r)
  let (ts, r1) ← mathChunk r
  let (vs, d) ← binderMath ts
  if !distinct then return (.every vs d, r1)
  let [x, y] := vs | none
  some (.many [.every vs d, .ifCond (.chain (.id x) [(.ne, .id y)])], r1)

/-- The condition of a notion: `[, for every $v\in A$,] [the map] M[,] is MONO`, or
`$φ$ [for all $x\in A$]`. -/
def notionCond (cs : List Chunk) : Option NotionCond :=
  let cs := optPunct 44 cs
  (do
    let (bs, r) : List Bind × List Chunk := match forBinder cs with
      | some (b, r') => match punct 44 r' with
        | some r'' => ([b], r'')
        | none => ([], cs)
      | none => ([], cs)
    let r1 := (kw [w!"the", w!"map"] r <|> kw [w!"the", w!"function"] r).getD r
    let (m, r2) ← (display r1).map (fun (m, _, r') => (m, r')) <|> formula r1
    let r3 ← kw [w!"is"] (optPunct 44 r2)
    let (mono, r4) ← monoWord r3
    if isEnd r4 then some (NotionCond.mono bs m mono) else none) <|>
  (do
    let (φ, r1) ← formula cs
    if isEnd r1 then some (NotionCond.formula φ []) else do
    let (b, r2) ← forBinder r1
    if isEnd r2 then some (NotionCond.formula φ [b]) else none) <|>
  (do
    let (c, r1) ← andClauses cs <|> clause cs
    if isEnd r1 then some (NotionCond.clause c) else none)

/-- A notion defined in the text: `We call a NOUN $x$ NAME [(ABBR)] if COND.`,
`[A NOUN] $x$ is called NAME [(ABBR)] if COND.`, `[A NOUN] $x$ is NAME [(ABBR)] if COND.` -/
def notionDefWith (notionCond : List Chunk → Option NotionCond) (cs : List Chunk) : Option Sent :=
  let article (r : List Chunk) := (kw [w!"a"] r <|> kw [w!"an"] r).getD r
  (do
    let r ← kw [w!"we", w!"call"] cs
    let (np, r1) ← nounVar (article r)
    let (name, abbr, r2) ← nameAbbr r1
    let r3 ← kw [w!"if"] r2
    withCond true false np name abbr r3) <|>
  (do
    -- (`We say that a NOUN $x$ is NAME if …`)
    let cs := (kw [w!"we", w!"say", w!"that"] cs).getD cs
    let (np, r1) ← nounVar (article cs)
    let (named, r2) ← ((kw [w!"is", w!"called"] r1 <|> kw [w!"is", w!"said", w!"to", w!"be"] r1).map (true, ·)) <|>
      ((kw [w!"is"] r1).map (false, ·))
    -- (`is called an involution`: the name of a kind of object)
    let (noun, r2) := match kw [w!"a"] r2 <|> kw [w!"an"] r2 with
      | some r => (true, r)
      | none => (false, r2)
    let (name, abbr, r3) ← nameAbbr r2
    let r4 ← kw [w!"if"] r3
    withCond named noun np name abbr r4)
where
  /-- The notion with its condition, or, when the condition is not read, the
  sentence is plainly a definition (`We call`, `is called`) and its subject is a
  noun phrase, the subject alone. -/
  withCond (named noun : Bool) (np : List Chunk) (name abbr : List Codes) (r : List Chunk) : Option Sent :=
    match notionCond r with
    | some cond => some (.defNotion np name abbr cond noun)
    | none =>
      if named && np.length ≥ 2 && (kw [w!"and", w!"only", w!"if"] r).isNone then
        some (.notionSubject np)
      else none

def notionDef (cs : List Chunk) : Option Sent := notionDefWith notionCond cs

/-- A condition on variables, `$c>0$`, `$0<x\le1$`: a chain of order relations (not a
definition, an equation or a membership). -/
def isCondition : MT → Bool
  | .chain _ rs => !rs.isEmpty && rs.all fun (r, _) => r == .lt || r == .le || r == .gt || r == .ge || r == .ne || r == .sim
  | _ => false

/-- The words of a noun phrase before its variable, with the formulas of its modifiers
(`invertible $n\times n$ matrix`, `$k$-regular graph`): a formula before a hyphen, a
product `$m\times n$` before a word, or a number before `times`. -/
def prenominalWords (cs : List Chunk) : List Chunk :=
  let rec go : Nat → List Chunk → List Chunk → List Chunk
    | 0, _, acc => acc.reverse
    | _ + 1, [], acc => acc.reverse
    | f + 1, c :: rest, acc =>
      match c, rest with
      -- (`that is bounded above`: a relative clause after the noun, not its words)
      | .w w, .w i :: _ =>
        if (w == w!"that" || w == w!"which") && (i == w!"is" || i == w!"are" || i == w!"has" || i == w!"have" || i == w!"contains") then acc.reverse
        -- (`in which every vertex has even degree`: a relative clause)
        else if (w == w!"in" || w == w!"for" || w == w!"on") && i == w!"which" then acc.reverse
        else if w == w!"whose" then acc.reverse
        else if w != w!"with" && w != w!"such" then go f rest (c :: acc) else acc.reverse
      | .w w, _ => if w != w!"with" && w != w!"such" then go f rest (c :: acc) else acc.reverse
      | .p 45, _ => go f rest (c :: acc)
      | .m _, .p 45 :: _ => go f rest (c :: acc)
      -- (`$n$ times differentiable function`: a number of times)
      | .m t, .w w :: _ =>
        if t.contains (.cmd w!"times") || w == w!"times" then go f rest (c :: acc) else acc.reverse
      | _, _ => acc.reverse
  go (cs.length + 1) cs []

/-- `$R>0$ and $h$`, `$a$, $b>1$ and $c$`: names joined by commas and `and`, some of them with
a condition (`$R>0$`: the name, then a comparison), at least one. -/
def condVars (cs : List Chunk) : Option (List (MTok × Option MT) × List Chunk) := do
  let one (ts : List MTok) : Option (MTok × Option MT) :=
    match ts with
    | [t@(.id _)] => some (t, none)
    | [t@(.cmd c)] => if Math.greekNames.contains c then some (t, none) else none
    | _ => do
      let m ← Math.parseFormula ts
      let .chain (.id x) [_] := m | none
      if !isCondition m then none
      some (.id x, some m)
  let (ts, r) ← mathChunk cs
  let first ← one ts
  let rec go : Nat → List (MTok × Option MT) → List Chunk → Option (List (MTok × Option MT) × List Chunk)
    | 0, acc, r => some (acc, r)
    | f + 1, acc, r =>
      match (punct 44 r >>= kw [w!"and"]) <|> kw [w!"and"] r <|> punct 44 r with
      | some (.m b :: r2) => do let it ← one b; go f (acc ++ [it]) r2
      | _ => some (acc, r)
  let (items, r') ← go 8 [first] r
  if items.length < 2 || items.all (·.2.isNone) then none
  some (items, r')

/-- `$x\in A$`, `$c>0$` (a condition), or `$C$ be a|an NP`: the variable of a `let`. -/
def letBinder (cs : List Chunk) : Option (Bind × List Chunk) :=
  -- `$R>0$ and $h$ be real numbers`: the names, each of the noun, and their conditions
  (do
    let (items, r) ← condVars cs
    let r1 ← kw [w!"be"] r
    let joined : List MTok := (items.map fun (t, _) => [t]).intersperse [MTok.sym 44] |>.flatten
    let (b, r2) ← pluralNoun joined r1
    let conds := items.filterMap fun (_, c) => c.map Bind.ifCond
    match b with
    | .many bs => some (.many (bs ++ conds), r2)
    | b => some (.many (b :: conds), r2)) <|>
  -- `$K\subseteq L\subseteq M$ be fields`: new variables, each an object of the plural noun,
  -- in a chain of inclusions
  (do
    let (ts, r) ← mathChunk cs
    let .chain (.id _) rels ← Math.parseFormula ts | none
    if rels.isEmpty || !(rels.all fun (rel, y) => rel == .subset && (match y with | .id _ => true | _ => false)) then none
    let r1 ← kw [w!"be"] r
    -- (the noun's words, before `with` or `such that`)
    let ws := r1.takeWhile fun c => match c with | .w w => w != w!"with" && w != w!"such" | .p 45 => true | _ => false
    let plural := match ws.getLast? with
      | some (.w w) => w.getLast? == some 115
      | _ => false
    if !plural then none
    -- (`… be fields with $[L:K]=2$`: the condition after the inclusions, which it may need)
    let (b, r2) ← pluralNoun ts (r1.take ws.length)
    match withConds (r1.drop ws.length) with
    | some (m, r3) => some (.many ((match b with | .many bs => bs | b => [b]) ++ [.ifCond m]), r3 ++ r2)
    | none => some (b, r2 ++ r1.drop ws.length)) <|>
  (do
    let (ts, r) ← mathChunk cs
    let (vs, d) ← binderMath ts
    -- (`$k\ge3$ be a fixed integer` is a noun phrase, below)
    if (kw [w!"be"] r).isSome then none else
    -- `let $C\in\mathcal C$ with $\rho(C)=r$`: a condition on the variable
    match withConds r with
    | some (m, r') => some (.many [.every vs d, .ifCond m], r')
    | none => some (.every vs d, r)) <|>
  -- `$c>0$ be fixed`
  (do
    let (ts, r) ← mathChunk cs
    let r1 ← kw [w!"be", w!"fixed"] r
    let b ← fixBinder ts
    some (b, r1)) <|>
  -- `$x\in A$ be positive`, `$a\in L$ be algebraic over $K$`: an element of the domain
  -- that is as the words say (the words before the noun `element`, or after it when they
  -- have a formula)
  (do
    let (ts, r) ← mathChunk cs
    -- (`$A\subseteq\mathbb{R}$ be finite and nonempty`: a subset of the domain)
    let (v, i, noun) ← (do
        let (vs, _) ← binderMath ts
        let [v] := vs | none
        let i ← ts.findIdx? (· == .cmd w!"in")
        some (v, i, w!"element")) <|>
      (match ts with
        | .id v :: .cmd c :: _ :: _ => if c == w!"subseteq" || c == w!"subset" then some (v, 1, w!"subset") else none
        | _ => none)
    let r1 ← kw [w!"be"] r
    -- (`$g\in G$ be an involution`: a notion of the article's, one word, of the elements)
    let r1 ← match kw [w!"a"] r1 <|> kw [w!"an"] r1 with
      | some (.w n :: rest) =>
        let ends := match rest with | [] | .p _ :: _ => true | .w w :: _ => w == w!"and" | _ => false
        -- (not of a subset: `$W\subset K$ be a subfield` is a subfield with its domain, below)
        if ends && noun != w!"subset" && ![w!"number", w!"integer", w!"point", w!"element", w!"vector", w!"function", w!"map", w!"prime",
            w!"set", w!"subset", w!"matrix", w!"polynomial", w!"sequence"].contains n then some (.w n :: rest) else none
      | some _ => none
      | none => if (kw [w!"the"] r1).isSome then none else some r1
    let dts := ts.drop (i + 1)
    -- (`and` between adjectives: `finite and nonempty`; not before a new binder, `and let`)
    let rec bodyOf : Nat → List Chunk → List Chunk → List Chunk
      | 0, _, acc => acc.reverse
      | f + 1, cs, acc => match cs with
        | .w w :: rest@(.w n :: _) =>
          if w == w!"and" then (if n == w!"let" || acc.isEmpty then acc.reverse else bodyOf f rest (.w w :: acc))
          else if [w!"with", w!"such", w!"where", w!"then", w!"fixed", w!"arbitrary", w!"given"].contains w then acc.reverse
          else bodyOf f rest (.w w :: acc)
        | .w w :: rest =>
          if [w!"and", w!"with", w!"such", w!"where", w!"then", w!"fixed", w!"arbitrary", w!"given"].contains w then acc.reverse
          else bodyOf f rest (.w w :: acc)
        | .m t :: rest => bodyOf f rest (.m t :: acc)
        | .p 45 :: rest => bodyOf f rest (.p 45 :: acc)
        | _ => acc.reverse
    let body := bodyOf (r1.length + 1) r1 []
    if body.isEmpty then none
    -- (`of finite order`: a phrase after the noun, as one with a formula)
    let hasMath := body.any (fun (c : Chunk) => match c with | .m _ => true | _ => false) ||
      (match body with | .w w :: _ => w == w!"of" | _ => false)
    -- (`finite and nonempty`: adjectives before the noun, without `and`)
    let body' := if hasMath then body else body.filter fun (c : Chunk) => match c with | .w w => w != w!"and" | _ => true
    let np : List Chunk := if hasMath then [.w noun, .m [.id v], .w w!"of", .m dts] ++ body
      else body' ++ [.w noun, .m [.id v], .w w!"of", .m dts]
    some (.noun np, r1.drop body.length)) <|>
  -- `$\varphi,\psi:[0,1]\to\mathbb{R}$ be continuous functions`: each of them is such a
  -- function
  (do
    let (ts, r) ← mathChunk cs
    let i ← ts.findIdx? (· == .sym 58)
    let (names, _, _) ← namesSig ts
    if names.length < 2 then none
    let r1 ← kw [w!"be"] r
    let ws := r1.takeWhile (fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false)
    -- (or adjectives without a noun, `$f,g\colon\mathbb{R}\to\mathbb{R}$ be differentiable`)
    let noun := match ws.getLast? with
      | some (.w w) => w == w!"functions" || w == w!"maps"
      | _ => false
    let ws := if noun then ws else ws.takeWhile fun (c : Chunk) => match c with
      | .w w => ![w!"with", w!"such", w!"and", w!"given", w!"defined", w!"a", w!"an", w!"the"].contains w
      | _ => true
    if ws.isEmpty then none
    let adjs := if noun then ws.dropLast else ws
    let rec split : List MTok → List MTok → List (List MTok) → List (List MTok)
      | [], cur, acc => (cur.reverse :: acc).reverse
      | t :: rest, cur, acc => if t == .sym 44 then split rest [] (cur.reverse :: acc) else split rest (t :: cur) acc
    let sigs := (split (ts.take i) [] []).map fun n => n ++ ts.drop i
    some (.many (sigs.map fun sg => Bind.noun (adjs ++ [.w w!"map", .m sg])), r1.drop ws.length)) <|>
  -- `$u:A\to B$ [be a map|function|field]`: a map of its signature
  (do
    let (ts, r) ← mathChunk cs
    let _ ← Math.parseSig ts
    let r' := (kw [w!"be", w!"a", w!"map"] r <|> kw [w!"be", w!"a", w!"function"] r <|>
      kw [w!"be", w!"a", w!"field"] r <|> kw [w!"be", w!"a", w!"vector", w!"field"] r).getD r
    -- `$c:[0,1]^2\to\mathbb{R}$ be a continuous function`: adjectives of the vocabulary
    -- before the noun
    let adj : Option (List Chunk × List Chunk) := do
      let r1 ← kw [w!"be", w!"a"] r <|> kw [w!"be", w!"an"] r
      let ws := r1.takeWhile (fun (c : Chunk) => match c with
        | .w w => w != w!"with" && w != w!"such" | .p 45 => true | _ => false)
      if ws.length < 2 then none
      match ws.getLast? with
      | some (.w w) => if w == w!"function" || w == w!"map" then some (ws.dropLast, r1.drop ws.length) else none
      | _ => none
    -- (conditions after it, `with $f'(x)=0$ for all $x$`, as for any noun)
    -- (`such that` with a formula only: a clause is a hypothesis of its own, `partsOf`)
    let postOf (r2 : List Chunk) : List Chunk :=
      let upTo := r2.takeWhile (fun c => match c with | .p 44 | .p 46 => false | _ => true)
      match r2 with
      | .w w :: _ =>
        if w == w!"with" then upTo
        else match r2 with
          | .w _ :: .w t :: .m _ :: rest =>
            if w == w!"such" && t == w!"that" && (match rest with | [] | .p _ :: _ => true | .w f :: _ => f == w!"for" | _ => false)
            then upTo else []
          | _ => []
      | _ => []
    -- `$f\colon[0,1]\to\mathbb{R}$ be continuous [with …]`: adjectives without a noun, of the map
    let bare : Option (List Chunk × List Chunk) := do
      let r1 ← kw [w!"be"] r
      if (kw [w!"a"] r1).isSome || (kw [w!"an"] r1).isSome || (kw [w!"the"] r1).isSome then none
      -- (`and` between adjectives, `continuous and nonnegative`; not before another binder or a
      -- hypothesis, `and let`, `and suppose`)
      let rec words : Nat → List Chunk → List Chunk → List Chunk
        | 0, _, acc => acc.reverse
        | f + 1, cs, acc => match cs with
          | .w w :: rest =>
            if w == w!"with" || w == w!"such" || w == w!"given" || w == w!"defined" then acc.reverse
            else if w == w!"and" then
              match rest with
              | .w n :: _ =>
                if acc.isEmpty || [w!"let", w!"suppose", w!"assume", w!"that", w!"with", w!"such", w!"for"].contains n then acc.reverse
                else words f rest (.w w :: acc)
              | _ => acc.reverse
            else words f rest (.w w :: acc)
          | .p 45 :: rest => words f rest (.p 45 :: acc)
          | _ => acc.reverse
      let ws := words (r1.length + 1) r1 []
      if ws.isEmpty then none
      -- (the adjectives before the noun, without `and`)
      some (ws.filter (fun (c : Chunk) => match c with | .w w => w != w!"and" | _ => true), r1.drop ws.length)
    let adj := adj <|> bare
    match adj with
    | some (adjs, r2) => let post := postOf r2; some (.noun (adjs ++ [.w w!"map", .m ts] ++ post), r2.drop post.length)
    | none =>
      -- `$\varphi\colon G\to H$ be a homomorphism`: another noun of maps, with the signature
      let other : Option (List Chunk × List Chunk) := do
        if r'.length != r.length then none
        let r1 ← kw [w!"be", w!"a"] r <|> kw [w!"be", w!"an"] r
        let ws := r1.takeWhile (fun (c : Chunk) => match c with
          | .w w => w != w!"with" && w != w!"such" | .p 45 => true | _ => false)
        if ws.isEmpty then none
        some (ws, r1.drop ws.length)
      match other with
      | some (ws, r2) => let post := postOf r2; some (.noun (ws ++ [.m ts] ++ post), r2.drop post.length)
      | none => let post := postOf r'; some (.noun ([.w w!"map", .m ts] ++ post), r'.drop post.length)) <|>
  -- `$c>0$`: a condition, assumed like a binder
  (do
    let (ts, r) ← mathChunk cs
    let m ← Math.parseFormula ts
    if (kw [w!"be"] r).isSome then none else
    if isCondition m then some (.ifCond m, r) else none) <|>
  -- `$L/K$ be a [finite] field extension`: the field `K`, and `L` an extension of it
  (do
    let (ts, r) ← mathChunk cs
    let [.id l, .sym 47, .id k] := ts | none
    let r1 ← kw [w!"be", w!"a"] r <|> kw [w!"be", w!"an"] r
    let ws := r1.takeWhile (fun (c : Chunk) => match c with
      | .w w => w != w!"with" && w != w!"such" && w != w!"and" | .p 45 => true | _ => false)
    match ws.getLast? with
    | some (.w e) => if e != w!"extension" then none
    | _ => none
    some (.many [.noun [.w w!"field", .m [.id k]], .noun (ws ++ [.m [.id l], .w w!"of", .m [.id k]])], r1.drop ws.length)) <|>
  -- `$a<b$ be real numbers`: the variables of the chain, each of the noun, and the chain
  (do
    let (ts, r) ← mathChunk cs
    let r1 ← kw [w!"be"] r
    let m ← Math.parseFormula ts
    let .chain (.id x) rest := m | none
    -- (`$n\ge k\ge0$ be integers`: numbers in the chain are bounds)
    let ys ← rest.mapM fun (_, y) => match y with
      | .id y => some (some y)
      | .num _ => some none
      | _ => none
    let ys := ys.filterMap id
    if ys.isEmpty then none
    let joined : List MTok := ((x :: ys).map fun n => [MTok.id n]).intersperse [MTok.sym 44] |>.flatten
    let (b, r2) ← pluralNoun joined r1
    match b with
    | .many bs => some (.many (bs ++ [.ifCond m]), r2)
    | b => some (.many [b, .ifCond m], r2)) <|>
  -- `$a,b$ be positive integers`, `$a$ and $b$ be positive integers`,
  -- `$x_1,\ldots,x_n$ be real numbers [with $φ$]`
  (do
    let (ts, r) ← joinedVars cs
    let r1 ← kw [w!"be"] r
    pluralNoun ts r1) <|>
  (do
    let (ts, r) ← mathChunk cs
    let v ← match ts with
      | [.id v] => some [MTok.id v]
      | [.cmd n] => some [MTok.cmd n]
      | _ => match hatName ts, binderMath ts with
        | some (_, []), _ => some ts
        -- `Let $k\ge3$ be a [fixed] integer.`
        | _, some ([_], _) => some ts
        -- `Let $n_0$ be a positive integer.`
        | _, _ => if subName ts then some ts else none
    let r0 ← kw [w!"be", w!"a"] r <|> kw [w!"be", w!"an"] r
    -- (`a $k$-regular graph`, `an $n\times n$ matrix`: a formula before the noun, the
    -- argument of a modifier of the vocabulary)
    let lead : List Chunk := match r0 with
      | .m t :: .p 45 :: .w _ :: _ => [.m t, .p 45]
      | .m t :: .w _ :: _ => if t.contains (.cmd w!"times") then [.m t] else []
      | _ => []
    let r1 := r0.drop lead.length
    -- (`… be an integer and let $x_1,\ldots,x_n$ be …`, `… and $\lambda>0$`: the next binder)
    let cut := (r1.zipIdx.find? fun (c, i) => match c, r1[i + 1]? with
      | .w w, some (.w w') => w == w!"and" && w' == w!"let"
      | .w w, some (.m _) => w == w!"and"
      | _, _ => false).map (·.2)
    let ws := prenominalWords (r1.take (cut.getD r1.length))
    -- a noun that ends in a fixed formula: `probability distribution on $\mathbb{N}_0$`
    let tail := match r1.drop ws.length with
      | .m t :: _ =>
        match ws.getLast? with
        | some (.w w) => if w == w!"on" || w == w!"in" || w == w!"over" then [Chunk.m t] else []
        | _ => []
      | _ => []
    -- words and conditions after the formula (`with zero mean`), up to a comma or the end
    let rest := r1.drop (ws.length + tail.length)
    let opensPost := match rest with
      | .w w :: _ => w == w!"with" || w == w!"of" || w == w!"such" || w == w!"that" || w == w!"which"
      | _ => false
    -- (up to a comma or the end, not into the next binder `and let`)
    let upToNext (cs : List Chunk) : List Chunk :=
      -- (or `and $(b_n)$ a sequence with …`: the next binder, with `be` left out)
      let k := (cs.zipIdx.find? fun (c, i) => match c, cs[i + 1]?, cs[i + 2]? with
        | .w a, some (.w l), _ => a == w!"and" && l == w!"let"
        | .w a, some (.m _), some (.w d) => a == w!"and" && (d == w!"a" || d == w!"an")
        | _, _, _ => false).map (·.2)
      (cs.take (k.getD cs.length)).takeWhile (fun c => match c with | .p 44 | .p 46 => false | _ => true)
    let post := if tail.isEmpty && !opensPost then [] else upToNext rest
    if ws.isEmpty then none else
    -- `a graph on $n$ vertices`, `a polynomial of degree $n$`: a phrase with a number after
    -- the noun (a modifier of the vocabulary with an argument), not a noun ending in a fixed
    -- formula; the variable follows the noun
    let simple (t : List MTok) : Bool := (!t.isEmpty && t.all fun x => match x with
      | .id n => n.length == 1 | .digit _ => true | .sym c => c == 43 || c == 45 | _ => false) ||
      (match t with | [.cmd _] => true | _ => false)
    let preps := [w!"on", w!"of", w!"in", w!"over", w!"to", w!"from", w!"modulo", w!"at", w!"by"]
    let lastPrep := (ws.zipIdx.filter fun (c, _) => match c with | .w w => preps.contains w | _ => false).getLast?
    -- (`an integer greater than [or equal to] $1$`: the variable before the comparison)
    let cmpAt : Option (Chunk × Nat) := (ws.zipIdx.find? fun (c, i) => match c, ws[i + 1]? with
      | .w w, some (.w t) => t == w!"than" && [w!"greater", w!"less", w!"larger", w!"smaller"].contains w
      | _, _ => false)
    let argPhrase : Option (List Chunk × List Chunk) := match cmpAt <|> lastPrep, r1.drop ws.length with
      | some (_, i), .m t :: more =>
        -- (after `on` or `in`, a formula that is not a number may end the noun: `on $\mathbb{N}_0$`)
        if i == 0 || (!tail.isEmpty && !simple t) then none else
        -- (`equidistant from $A$ and $B$`: two objects after `from`)
        let two : List Chunk := match ws[i]?, more with
          | some (.w p), .w a :: .m u :: _ => if p == w!"from" && a == w!"and" && simple u then [.w a, .m u] else []
          | _, _ => []
        let more := more.drop two.length
        let after := two ++ more.takeWhile (fun c => match c with | .w w => !([w!"with", w!"of", w!"such", w!"and", w!"satisfying", w!"that", w!"which", w!"whose", w!"where"].contains w) | _ => false)
        -- (`on $n$ vertices`: words after the number; `of degree $n$`: none)
        some (ws.take i ++ [.m v] ++ ws.drop i ++ [.m t] ++ after, more.drop (after.length - two.length))
      | _, _ => none
    match argPhrase with
    | some (np, rest') =>
      -- (conditions after it, `with $φ$`, as for any noun)
      -- (and another phrase of the noun, `a vector space over $K$ of dimension $3$`)
      let post' := match rest' with
        | .w w :: _ => if w == w!"with" || w == w!"such" || w == w!"of" || w == w!"that" || w == w!"which" then
            rest'.takeWhile (fun c => match c with | .p 44 | .p 46 => false | _ => true) else []
        | _ => []
      some (.noun (lead ++ np ++ post'), rest'.drop post'.length)
    | none => some (.noun (lead ++ ws ++ tail ++ [.m v] ++ post), rest.drop post.length)) <|>
  -- `$M$ be the midpoint of $A$ and $B$`: the value of a notion of the vocabulary with its
  -- arguments (the noun phrase `@the midpoint of $A$ and $B$ $M$`)
  (do
    let (v, r) ← mathChunk cs
    if !(match v with | [.id _] | [.cmd _] => true | _ => subName v) then none
    -- (`be @the`: `be the`, `denote the` or `denote` of a sentence that has no other
    -- reading, see `letTheSent`)
    let r1 ← kw [w!"be", w!"@the"] r
    let phrase := r1.takeWhile (fun c => match c with | .p 44 | .p 46 => false | _ => true)
    let cutAt := (phrase.zipIdx.find? fun (c, i) => match c, phrase[i + 1]? with
      | .w a, some (.w l) => a == w!"and" && l == w!"let"
      | _, _ => false).map (·.2)
    let phrase := phrase.take (cutAt.getD phrase.length)
    if phrase.isEmpty then none
    some (.noun ([.w w!"@the"] ++ phrase ++ [.m v]), r1.drop phrase.length))

/-- Further variables and definitions of a `let`: `, and let $u\in A$`, `and $v\in B$`,
`, and let $X\coloneqq e$`, `, $Y\coloneqq f$ and $Z\coloneqq g$`. -/
def letMore : Nat → List Chunk → List Bind → List MT → Option (List Bind × List MT × List Chunk)
  | 0, cs, bs, ds => some (bs.reverse, ds.reverse, cs)
  | f + 1, cs, bs, ds =>
    -- `Let $a$ and $b$ be integers, not both zero`: one of them is not `0`
    let notAll : Option (List Chunk × Bind) := do
      let r ← (punct 44 cs >>= kw [w!"not", w!"both", w!"zero"]) <|> (punct 44 cs >>= kw [w!"not", w!"all", w!"zero"])
      let .many nbs ← bs.head? | none
      let vs := nbs.filterMap fun b => match b with
        | .noun np => np.reverse.findSome? fun c => match c with | .m [.id v] => some v | _ => none
        | _ => none
      if vs.length < 2 || vs.length != nbs.length then none
      let ne (v : Codes) : MT := .chain (.id v) [(.ne, .num 0)]
      let v0 ← vs.head?
      some (r, .ifCond ((vs.drop 1).foldl (fun acc v => MT.lor acc (ne v)) (ne v0)))
    if let some (r, b) := notAll then letMore f r (b :: bs) ds else
    let next := (punct 44 cs >>= kw [w!"and", w!"let"]) <|> (punct 44 cs >>= kw [w!"and"]) <|>
      (punct 44 cs >>= kw [w!"let"]) <|> kw [w!"and", w!"let"] cs <|> kw [w!"and"] cs <|> punct 44 cs
    match next with
    | none => some (bs.reverse, ds.reverse, cs)
    | some r =>
      -- (`Let $R$ be a ring and $I$ an ideal of $R$`: `be` left out)
      let elided : Option (Bind × List Chunk) := match r with
        | .m v :: .w a :: rest => if a == w!"a" || a == w!"an" then letBinder (.m v :: .w w!"be" :: .w a :: rest) else none
        | _ => none
      -- (the elided `be` first: `and $T\colon V\to V$ a linear map` is no signature binder
      -- followed by words)
      match elided <|> letBinder r with
      | some (b, r') => letMore f r' (b :: bs) ds
      | none =>
        match formula r with
        | some (m, r') =>
          -- (`let $K\coloneqq\{…\}$ be their contact set`: the name is not read)
          let r' := match kw [w!"be", w!"the"] r' <|> kw [w!"be", w!"their"] r' <|> kw [w!"be", w!"its"] r' with
            | some r2 =>
              let ws := r2.takeWhile (fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false)
              if !ws.isEmpty && ws.length ≤ 6 && (match r2.drop ws.length with
                  | .p 46 :: _ | .p 44 :: _ | [] => true | _ => false) then r2.drop ws.length else r'
            | none => r'
          match m with
          | .chain _ ((.defeq, _) :: _) => letMore f r' bs (m :: ds)
          | _ => some (bs.reverse, ds.reverse, cs)
        | none => some (bs.reverse, ds.reverse, cs)

/-- The chunks between the markers of a list (`\begin{enumerate}`, `\item`, `\end`). -/
def listItems : List Chunk → List Chunk → List (List Chunk) → List (List Chunk)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | .x :: rest, cur, acc => listItems rest [] (cur.reverse :: acc)
  | c :: rest, cur, acc => listItems rest (c :: cur) acc

/-- The formula of an item: `$φ$`, or a display, with its label `[(i)]` and its
final `;`, `.`, `,` or `, and` removed. -/
def itemFormula (it : List Chunk) : Option MT :=
  let it := match it with
    | .p 91 :: rest => (rest.dropWhile (fun (c : Chunk) => match c with
        | .p 93 => false | .w _ | .p _ => true | _ => false)).drop 1
    | _ => it
  let it := match it.reverse with
    | .w a :: .p 44 :: r => if a == w!"and" then r.reverse else it
    | .w a :: r => if a == w!"and" then r.reverse else it
    | _ => it
  let it := match it.reverse with
    | .p c :: r => if c == 59 || c == 46 || c == 44 then r.reverse else it
    | _ => it
  match it with
  | [.m ts] => Math.parseFormula ts
  | [.d ts _] => Math.parseDisplay ts
  | _ => none

/-- The words that announce a list of equivalent statements. -/
def tfaeIntros : List (List Codes) :=
  [[w!"the", w!"following", w!"are", w!"equivalent"], [w!"the", w!"following", w!"statements", w!"are", w!"equivalent"],
   [w!"the", w!"following", w!"conditions", w!"are", w!"equivalent"], [w!"the", w!"following", w!"assertions", w!"are", w!"equivalent"],
   [w!"the", w!"following", w!"properties", w!"are", w!"equivalent"]]

/-- The statement of an item (`[(ii)] $f$ is continuous and bounded;`): its label and its
final `;`, `.`, `,` or `, and` removed, read as one or several clauses joined by `and`. -/
def itemClause (it : List Chunk) : Option Clause := do
  let it := match it with
    | .p 91 :: rest => (rest.dropWhile (fun (c : Chunk) => match c with
        | .p 93 => false | .w _ | .p _ => true | _ => false)).drop 1
    | _ => it
  let it := match it.reverse with
    | .w a :: .p 44 :: r => if a == w!"and" then r.reverse else it
    | .w a :: r => if a == w!"and" then r.reverse else it
    | _ => it
  let it := match it.reverse with
    | .p c :: r => if c == 59 || c == 46 || c == 44 then r.reverse else it
    | _ => it
  if it.isEmpty then none
  let (c, r) ← andClauses (it ++ [.p 46])
  if isEnd r then some c else none

/-- `the following [statements] are equivalent:` and a list of formulas, or of statements:
each is equivalent to the next (and so all are). -/
def tfae (cs : List Chunk) : Option (List CClause) := do
  let r ← tfaeIntros.findSome? (kw · cs) >>= punct 58
  let items := (listItems r [] []).filter fun it => match it with
    | [] | [.p 46] => false
    | _ => true
  match items.mapM itemFormula with
  | some fs =>
    if fs.length < 2 then none
    else some ((fs.zip (fs.drop 1)).map fun (p, q) => ({ cites := [], clause := .iff p q } : CClause))
  | none =>
    let cls ← items.mapM itemClause
    if cls.length < 2 then none
    else some ((cls.zip (cls.drop 1)).map fun (p, q) => ({ cites := [], clause := .iffC p q } : CClause))

/-- `We write $T$ for $F$.`, `We write $T$ if|when $F$.`, `We write $T$ for [the] NAME.` -/
def notationSent (cs : List Chunk) : Option Sent := do
  let r ← kw [w!"we", w!"write"] cs <|> kw [w!"let", w!"us", w!"write"] cs
  let (_, r1) ← mathChunk r
  match kw [w!"for"] r1, (kw [w!"if"] r1 <|> kw [w!"when"] r1) with
  | some r2, _ =>
    match r2 with
    | [.m _, .p 46] => some (.notation 0 [])
    | _ =>
      let name := (kw [w!"the"] r2 <|> kw [w!"a"] r2 <|> kw [w!"an"] r2).getD r2
      if name.isEmpty || !isEnd (name.drop (name.length - 1)) then none
      else some (.notation 2 name.dropLast)
  | none, some r2 =>
    match r2 with
    | [.m _, .p 46] => some (.notation 1 [])
    | _ => none
  | none, none => none

/-- `By a|an WORDS we mean …`, `Throughout[ the|this paper|article], WORDS means …`,
`In this paper|article, WORDS means …`. -/
def meaningSent (cs : List Chunk) : Option Sent := do
  let det (r : List Chunk) : Bool × List Chunk := match kw [w!"a"] r <|> kw [w!"an"] r with
    | some r' => (true, r')
    | none => (false, r)
  let (lhsNoun, ws, body) ← (do
      let r ← kw [w!"by"] cs
      let (n, r) := det r
      let (ws, r1) ← wordsUntil [w!"we"] 8 r []
      let r2 ← kw [w!"we", w!"mean"] r1
      some (n, ws, r2)) <|> (do
      let r ← (kw [w!"throughout"] cs) <|> (kw [w!"in", w!"this", w!"paper"] cs) <|> (kw [w!"in", w!"this", w!"article"] cs)
      let r := (kw [w!"the", w!"paper"] r <|> kw [w!"this", w!"paper"] r <|> kw [w!"this", w!"article"] r <|>
        kw [w!"the", w!"article"] r).getD r
      let r ← punct 44 r
      let (n, r) := det r
      let (ws, r1) ← wordsUntil [w!"means"] 8 r []
      let r2 ← kw [w!"means"] r1
      some (n, ws, r2))
  if ws.isEmpty || !isEnd (body.drop (body.length - 1)) then none else
  let rhs := body.dropLast
  let (rhsNoun, rhs) := det rhs
  if rhs.isEmpty || lhsNoun != rhsNoun then none else
  some (.meaning (ws.map lower) rhs lhsNoun)

/-- A list of formulas and word phrases (`$j,I$ and the fixed profile data`), separated by
`,` and `and`, up to `;`, the end of the sentence, or `[,] and are|is|they …`. -/
def depList (cs : List Chunk) : List (List MTok) × List (List Codes) × List Chunk :=
  let rec go : Nat → List Chunk → List Codes → List (List MTok) → List (List Codes) →
      List (List MTok) × List (List Codes) × List Chunk
    | 0, cs, cur, ms, ws => (ms.reverse, (if cur.isEmpty then ws else cur.reverse :: ws).reverse, cs)
    | f + 1, cs, cur, ms, ws =>
      let flush := if cur.isEmpty then ws else cur.reverse :: ws
      let stop := isEnd cs || (match cs with
        | .p 59 :: _ => true
        | .p 44 :: .w a :: .w b :: _ => a == w!"and" && (b == w!"are" || b == w!"is" || b == w!"they" || b == w!"may")
        | .p 44 :: .w a :: _ => a == w!"they"
        | .w a :: .w b :: _ => a == w!"and" && (b == w!"are" || b == w!"is" || b == w!"they" || b == w!"may")
        | _ => false)
      if stop then (ms.reverse, flush.reverse, cs) else
      match cs with
      | .m ts :: r => go f r [] (ts :: ms) flush
      | .p 44 :: r => go f r [] ms flush
      | .w a :: r => if a == w!"and" then go f r [] ms flush else go f r (a :: cur) ms ws
      | _ => (ms.reverse, flush.reverse, cs)
  go (cs.length + 1) cs [] [] []

/-- The parts of a formula between its commas outside brackets and braces (`u,P_{a,b}`). -/
def topCommas : Nat → Int → List MTok → List MTok → List (List MTok) → List (List MTok)
  | 0, _, cur, _, acc => (cur.reverse :: acc).reverse
  | _ + 1, _, cur, [], acc => (cur.reverse :: acc).reverse
  | f + 1, d, cur, t :: ts, acc =>
    if d == 0 && t == .sym 44 then topCommas f d [] ts (cur.reverse :: acc) else
    let d' := match t with
      | .lb | .setl | .sym 40 | .sym 91 | .begin _ => d + 1
      | .rb | .setr | .sym 41 | .sym 93 | .finish _ => d - 1
      | _ => d
    topCommas f d' (t :: cur) ts acc

/-- The symbols of a formula of constants with their sign: `C`, `C_{j,I}>0`,
`b_{j,I},d_{j,I}\ge0`. -/
def constSyms (ts : List MTok) : Option (List (MT × Nat)) := do
  let (ts, sign) := match ts.reverse with
    | .digit 0 :: .sym 62 :: r => (r.reverse, 1)
    | .digit 0 :: .cmd g :: r =>
      if g == w!"ge" || g == w!"geq" || g == w!"geqslant" then (r.reverse, 2) else (ts, 0)
    | _ => (ts, 0)
  let parts := (topCommas (ts.length + 1) 0 [] ts []).filter (!·.isEmpty)
  if parts.isEmpty then none
  parts.mapM fun p => do
    let m ← Math.parseFormula p
    match m with
    | .id _ | .sub (.id _) _ => some (m, sign)
    | _ => none

/-- `Throughout, $C$ and $C_m$ denote positive constants.`, `In the definitions below,
$C_{j,I}>0$ and $b_{j,I},d_{j,I}\ge0$ may depend on $j,I$ and the fixed profile data, and
are uniform in band, label and point.`, `Here and below, $K$ denotes a positive constant
that depends only on $n$.`: generic constants. -/
def genericSent (cs : List Chunk) : Option Sent := do
  -- where the convention holds (a convention sentence starts with it, or with `The constants`)
  let lead := (kw [w!"throughout"] cs <|> kw [w!"in", w!"this", w!"paper"] cs <|> kw [w!"in", w!"this", w!"article"] cs <|>
    kw [w!"here", w!"and", w!"below"] cs <|> kw [w!"here", w!"and", w!"in", w!"what", w!"follows"] cs <|>
    kw [w!"in", w!"what", w!"follows"] cs <|> kw [w!"in", w!"the", w!"following"] cs <|> kw [w!"below"] cs <|>
    (do
      -- `In the definitions|lemmas|estimates below`
      let r ← kw [w!"in", w!"the"] cs
      match r with
      | .w _ :: .w b :: r' => if b == w!"below" then some r' else
        match r' with
        | .w c :: r'' => if c == w!"below" then some r'' else none
        | _ => none
      | _ => none))
  let r := lead.getD cs
  let r := (kw [w!"the", w!"paper"] r <|> kw [w!"this", w!"paper"] r <|> kw [w!"this", w!"article"] r).getD r
  let r := (punct 44 r).getD r
  let (theConstants, r) := match kw [w!"the", w!"constants"] r with
    | some r' => (true, r')
    | none => (false, r)
  if lead.isNone && !theConstants then none
  -- the constants: formulas separated by `,` and `and`
  let rec syms : Nat → List Chunk → List (MT × Nat) → Option (List (MT × Nat) × List Chunk)
    | 0, _, _ => none
    | f + 1, cs, acc => do
      let (ts, r) ← mathChunk cs
      let acc := acc ++ (← constSyms ts)
      match (punct 44 r >>= fun r' => (kw [w!"and"] r').getD r' |> some) <|> kw [w!"and"] r with
      | some r' => match r' with
        | .m _ :: _ => syms f r' acc
        | _ => some (acc, r)
      | none => some (acc, r)
  let (ms, r1) ← syms 8 r []
  -- `denote[s] [positive|non-negative] constant[s]`
  let (ms, r2, named) : List (MT × Nat) × List Chunk × Bool := match kw [w!"denote"] r1 <|> kw [w!"denotes"] r1 <|>
      kw [w!"are"] r1 <|> kw [w!"is"] r1 with
    | some r' =>
      let r' := (kw [w!"a"] r').getD r'
      let (sign, r'') := match kw [w!"positive"] r' with
        | some x => (1, x)
        | none => match kw [w!"nonnegative"] r' <|> kw [w!"non", w!"negative"] r' <|> (do let x ← kw [w!"non"] r'; let x ← punct 45 x; kw [w!"negative"] x) with
          | some x => (2, x)
          | none => (0, r')
      match kw [w!"constants"] r'' <|> kw [w!"constant"] r'' <|> kw [w!"generic", w!"constants"] r'' with
      | some x => (ms.map (fun (m, s) => (m, if sign == 0 then s else sign)), x, true)
      | none =>
        -- `The constants $c$ and $c_m$ are positive [and independent of $N$]`
        if theConstants && sign != 0 then (ms.map (fun (m, s) => (m, if s == 0 then sign else s)), r'', true)
        else (ms, r1, false)
    | none => (ms, r1, false)
  -- what the constants may depend on, and what they are uniform in
  let rec clauses : Nat → List Chunk → Option (List (List MTok) × List (List Codes)) →
      (List (List MTok) × List (List Codes)) → Option (Option (List (List MTok) × List (List Codes)) ×
        (List (List MTok) × List (List Codes)))
    | 0, _, _, _ => none
    | f + 1, cs, deps, uni =>
      if isEnd cs then some (deps, uni) else
      let cs := (punct 44 cs <|> punct 59 cs).getD cs
      let cs := (kw [w!"and"] cs).getD cs
      let cs := (kw [w!"they"] cs <|> kw [w!"that"] cs <|> kw [w!"which"] cs <|> kw [w!"each"] cs).getD cs
      -- `may differ by row and` (each occurrence is its own constant)
      let cs := (do
          let x ← kw [w!"may", w!"differ", w!"by"] cs
          match x with
          | .w _ :: .w a :: x' => if a == w!"and" then some (Chunk.w w!"may" :: x') else none
          | _ => none).getD cs
      let depOn := kw [w!"may", w!"depend", w!"only", w!"on"] cs <|> kw [w!"may", w!"depend", w!"on"] cs <|>
        kw [w!"depend", w!"only", w!"on"] cs <|> kw [w!"depends", w!"only", w!"on"] cs <|>
        kw [w!"depend", w!"on"] cs <|> kw [w!"depends", w!"on"] cs <|> kw [w!"depending", w!"only", w!"on"] cs <|>
        kw [w!"depending", w!"on"] cs
      match depOn with
      | some r' =>
        let (ms, ws, rest) := depList r'
        if ms.isEmpty && ws.isEmpty then none else
        let old := deps.getD ([], [])
        clauses f rest (some (old.1 ++ ms, old.2 ++ ws)) uni
      | none =>
        let uniIn := kw [w!"are", w!"uniform", w!"in"] cs <|> kw [w!"is", w!"uniform", w!"in"] cs <|>
          kw [w!"uniform", w!"in"] cs <|> kw [w!"are", w!"independent", w!"of"] cs <|>
          kw [w!"is", w!"independent", w!"of"] cs <|> kw [w!"independent", w!"of"] cs
        match uniIn with
        | some r' =>
          let (ms, ws, rest) := depList r'
          if ms.isEmpty && ws.isEmpty then none else
          clauses f rest deps (uni.1 ++ ms, uni.2 ++ ws)
        | none => none
  let (deps, uni) ← clauses 6 r2 none ([], [])
  -- a convention says that the symbols are constants, or what they depend on
  if !named && deps.isNone && uni.1.isEmpty && uni.2.isEmpty then none
  some (.generic ms deps uni)

/-- `[Throughout,] [all] [the] implied constants [in …] are absolute.`, `… may depend [only] on
$k$ [and $\varepsilon$].`: the convention for the constant of `\ll`, `\gg` and `O(…)`, a
positive generic constant (`@ll`). -/
def impliedSent (cs : List Chunk) : Option Sent := do
  let r := ((kw [w!"throughout"] cs <|> kw [w!"in", w!"this", w!"paper"] cs <|> kw [w!"in", w!"what", w!"follows"] cs).map
    fun r => (punct 44 r).getD r).getD cs
  let r := (kw [w!"all"] r).getD r
  let r := (kw [w!"the"] r).getD r
  let r ← kw [w!"implied", w!"constants"] r <|> kw [w!"implicit", w!"constants"] r <|>
    kw [w!"implied", w!"constant"] r <|> kw [w!"implicit", w!"constant"] r
  -- (`in the $O$- and $\ll$-notation`: which notation)
  let stop (c : Chunk) : Bool := match c with
    | .w w => [w!"are", w!"is", w!"may", w!"depend", w!"depends"].contains w
    | _ => false
  let r := r.dropWhile (!stop ·)
  match kw [w!"are", w!"absolute"] r <|> kw [w!"is", w!"absolute"] r with
  | some r' => if isEnd r' then some (.generic [(.id w!"@ll", 1)] (some ([], [])) ([], [])) else none
  | none => do
    let r' ← kw [w!"may", w!"depend", w!"only", w!"on"] r <|> kw [w!"may", w!"depend", w!"on"] r <|>
      kw [w!"depend", w!"only", w!"on"] r <|> kw [w!"depends", w!"only", w!"on"] r <|>
      kw [w!"depend", w!"on"] r <|> kw [w!"depends", w!"on"] r
    let (ms, ws, rest) := depList r'
    if (ms.isEmpty && ws.isEmpty) || !isEnd rest then none else
    some (.generic [(.id w!"@ll", 1)] (some (ms, ws)) ([], []))

/-- `[We say that] a NP $f$ belongs to|is in|lies in $\mathcal M_\alpha$ if COND`, COND being
`$φ$ [for every B]` or `for every B, $φ$`. -/
def memberDef (cs : List Chunk) : Option Sent := do
  let r := (kw [w!"we", w!"say", w!"that"] cs).getD cs
  let r ← kw [w!"a"] r <|> kw [w!"an"] r
  let (np, r1) ← chunksUntil [w!"belongs", w!"is", w!"lies"] r []
  let r2 ← kw [w!"belongs", w!"to"] r1 <|> kw [w!"is", w!"in"] r1 <|> kw [w!"lies", w!"in"] r1
  let (cls, r3) ← formula r2
  match cls with
  | .id _ | .sub (.id _) (.id _) => pure ()
  | _ => none
  let r4 ← kw [w!"if"] r3
  let forEvery (cs : List Chunk) : Option (List Chunk) :=
    kw [w!"for", w!"every"] cs <|> kw [w!"for", w!"all"] cs <|> kw [w!"for", w!"each"] cs
  (do
    let r5 ← forEvery r4
    let (b, r6) ← everyBinders r5
    let r7 ← punct 44 r6
    let (φ, r8) ← (display r7).map (fun (m, _, r) => (m, r)) <|> formula r7
    if isEnd r8 then some (.defMember np cls φ [b]) else none) <|>
  (do
    let (φ, r5) ← (display r4).map (fun (m, _, r) => (m, r)) <|> formula r4
    if isEnd r5 then some (.defMember np cls φ []) else do
    let r6 ← forEvery (optPunct 44 r5)
    let (b, r7) ← everyBinders r6
    if isEnd r7 then some (.defMember np cls φ [b]) else none)

/-- `the least|smallest|minimal NP [such that|for which CLAUSE]`, `the largest|greatest|maximal
…`, `the number of NPs [such that|for which CLAUSE]` (the clause may be a display): the
kind, the noun phrase, the clause and the chunks after it. -/
def description (cs : List Chunk) : Option (DescKind × List Chunk × Option Clause × List Chunk) := do
  let r ← kw [w!"the"] cs
  let (k, r) ← match r with
    | .w w :: r' =>
      if [w!"least", w!"smallest", w!"minimal"].contains w then some (DescKind.least, r')
      else if [w!"largest", w!"greatest", w!"maximal"].contains w then some (.greatest, r')
      else if w == w!"number" then (kw [w!"of"] r').map (.count, ·)
      else none
    | _ => none
  -- the noun phrase ends at `such that`, `for which`, a comma or the end of the sentence
  let stops (cs : List Chunk) : Bool :=
    (kw [w!"such", w!"that"] cs).isSome || (kw [w!"for", w!"which"] cs).isSome || isEnd cs ||
      (punct 44 cs).isSome
  let rec upTo : Nat → List Chunk → List Chunk → Option (List Chunk × List Chunk)
    | 0, _, _ => none
    | f + 1, cs, acc =>
      if stops cs then some (acc.reverse, cs) else
      match cs with
      | [] => none
      | c :: rest => upTo f rest (c :: acc)
  let (np, r1) ← upTo (r.length + 1) r []
  if np.isEmpty then none else
  match kw [w!"such", w!"that"] r1 <|> kw [w!"for", w!"which"] r1 with
  | some r2 =>
    match display r2 with
    | some (m, _, r3) => some (k, np, some (.holds m), r3)
    | none => do
      let (c, r3) ← clause r2
      some (k, np, some c, r3)
  | none => some (k, np, none, r1)

/-- A definition by a description (`Sent.defDesc`), under the binder `b` of a `For B,` before it. -/
def descSent (b : Option Bind) (cs : List Chunk) : Option Sent :=
  let cs := (kw [w!"we"] cs).getD cs
  let finish (s : MT) (r : List Chunk) : Option Sent := do
    let (k, np, c, r') ← description r
    if isEnd r' then some (.defDesc b s k np c none) else none
  (do
    let r ← kw [w!"let"] cs <|> kw [w!"define"] cs
    let (s, r1) ← formula r
    let r2 ← kw [w!"be"] r1 <|> kw [w!"denote"] r1 <|> kw [w!"to", w!"be"] r1 <|> kw [w!"as"] r1
    finish s r2) <|>
  (do
    let r ← kw [w!"write"] cs
    let (s, r1) ← formula r
    let r2 ← kw [w!"for"] r1
    finish s r2) <|>
  (do
    let r ← kw [w!"denote", w!"by"] cs
    let (s, r1) ← formula r
    finish s r1)

/-- The first of the phrases that the chunks begin with: the rest. -/
def anyKw (ps : List (List Codes)) (cs : List Chunk) : Option (List Chunk) :=
  ps.findSome? fun p => kw p cs

/-- `Throughout, $p$ and $q$ denote integers.`, `In this paper, the letters $s,t$ always
denote integers.`, `Here and below, $d$ is an integer.`: a convention about letters. -/
def lettersSent (cs : List Chunk) : Option Sent := do
  let r ← kw [w!"throughout"] cs <|> kw [w!"in", w!"this", w!"paper"] cs <|> kw [w!"in", w!"this", w!"article"] cs <|>
    kw [w!"here", w!"and", w!"below"] cs <|> kw [w!"in", w!"what", w!"follows"] cs <|>
    kw [w!"in", w!"the", w!"following"] cs <|> kw [w!"below"] cs
  let r := (kw [w!"the", w!"paper"] r <|> kw [w!"this", w!"paper"] r <|> kw [w!"this", w!"article"] r).getD r
  let r := optPunct 44 r
  let r := (kw [w!"the", w!"letters"] r <|> kw [w!"the", w!"letter"] r).getD r
  -- the letters: formulas `$p$`, `$s,t$`, separated by `,` and `and`
  let rec vars : Nat → List Chunk → List Codes → Option (List Codes × List Chunk)
    | 0, _, _ => none
    | f + 1, cs, acc => do
      let (ts, r) ← mathChunk cs
      let names ← ((ts.splitBy fun a b => a != .sym 44 && b != .sym 44).filter (· != [.sym 44])).mapM fun p =>
        match p with
        | [.id v] => some v
        | _ => none
      let acc := acc ++ names
      match (punct 44 r >>= fun r' => some ((kw [w!"and"] r').getD r')) <|> kw [w!"and"] r with
      | some r' => match r' with
        | .m _ :: _ => vars f r' acc
        | _ => some (acc, r)
      | none => some (acc, r)
  let (vs, r1) ← vars 8 r []
  let r1 := (kw [w!"always"] r1).getD r1
  let r2 ← anyKw [[w!"denote", w!"integers"], [w!"denotes", w!"an", w!"integer"], [w!"are", w!"integers"],
    [w!"is", w!"an", w!"integer"], [w!"stand", w!"for", w!"integers"], [w!"stands", w!"for", w!"an", w!"integer"]] r1
  if vs.isEmpty || !isEnd r2 then none else some (.letters vs)

/-! ### Hypotheses of a proof: assumptions, cases and contradictions -/

/-- `CLAUSE [and CLAUSE]`, `CLAUSE, and that CLAUSE`: the hypotheses of an assumption or
of the heading of a case. -/
def hypClauses : Nat → List Chunk → List Clause → Option (List Clause × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc => do
    let (h, r) ← clause cs
    let more (r : List Chunk) : Option (List Chunk) := kw [w!"and", w!"that"] r <|> kw [w!"and"] r
    match more r <|> (punct 44 r >>= more) with
    | some r' => hypClauses f r' (h :: acc)
    | none => some ((h :: acc).reverse, r)

/-- Words that add a hypothesis to those made before. -/
def wAdditive : List (List Codes) :=
  [[w!"further"], [w!"furthermore"], [w!"moreover"], [w!"also"], [w!"additionally"],
   [w!"in", w!"addition"]]
/-- Words that begin another case: the hypothesis takes the place of the one before it. -/
def wCaseLike : List (List Codes) :=
  [[w!"now"], [w!"next"], [w!"instead"], [w!"second"], [w!"secondly"], [w!"third"], [w!"thirdly"],
   [w!"conversely"], [w!"otherwise"], [w!"finally"], [w!"lastly"], [w!"on", w!"the", w!"other", w!"hand"]]
/-- Words that announce a first case: the hypothesis is an assumption like any other
(the case after it takes its place). -/
def wFirst : List (List Codes) := [[w!"first"], [w!"firstly"]]
/-- Words that say a hypothesis is made to be refuted. -/
def wForContradiction : List (List Codes) :=
  [[w!"for", w!"the", w!"sake", w!"of", w!"a", w!"contradiction"],
   [w!"for", w!"the", w!"sake", w!"of", w!"contradiction"], [w!"for", w!"a", w!"contradiction"],
   [w!"for", w!"contradiction"], [w!"by", w!"way", w!"of", w!"contradiction"],
   [w!"by", w!"contradiction"], [w!"to", w!"the", w!"contrary"], [w!"on", w!"the", w!"contrary"],
   [w!"towards", w!"a", w!"contradiction"], [w!"toward", w!"a", w!"contradiction"]]

/-- The words around `assume`: whether they add a hypothesis, begin a case, or make the
hypothesis for contradiction; and the rest. -/
def supposeMods : Nat → List Chunk → Bool × Bool × Bool → (Bool × Bool × Bool) × List Chunk
  | 0, cs, fl => (fl, cs)
  | f + 1, cs, (a, k, x) =>
    let cs' := optPunct 44 cs
    match anyKw wForContradiction cs' with
    | some r => supposeMods f r (a, k, true)
    | none =>
      match anyKw wAdditive cs' with
      | some r => supposeMods f r (true, k, x)
      | none =>
        match anyKw wCaseLike cs' with
        | some r => supposeMods f r (a, true, x)
        | none =>
          match anyKw wFirst cs' with
          | some r => supposeMods f r (a, k, x)
          | none => ((a, k, x), cs)

/-- `Assume [that] CLAUSE [and CLAUSE].`, `Suppose …`, `We assume …`, `Let us assume …`,
`Without loss of generality, assume …`, `We may assume …`, with the words of
`supposeMods` before or after the verb. -/
def supposeSent (cs : List Chunk) : Option Sent := do
  let (fl, r) := supposeMods 3 cs (false, false, false)
  let r := optPunct 44 r
  -- (`Without loss of generality, assume …`, `We may assume …`: a hypothesis like any
  -- other. That it costs nothing is not a sentence of the proof: the result has to
  -- follow in Lean from the steps made under it)
  let wlog (r : List Chunk) : List Chunk :=
    optPunct 44 ((anyKw [[w!"without", w!"loss", w!"of", w!"generality"], [w!"without", w!"restriction"],
      [w!"wlog"]] r).getD r)
  let r := wlog r
  let r := (anyKw [[w!"let", w!"us"], [w!"we", w!"may", w!"and", w!"do"], [w!"we", w!"may", w!"therefore"],
    [w!"we", w!"may", w!"thus"], [w!"we", w!"may"], [w!"we", w!"can"], [w!"one", w!"may"], [w!"we"]] r).getD r
  let r := wlog r
  let r ← kw [w!"assume"] r <|> kw [w!"suppose"] r
  let ((additive, caseLike, contra), r) := supposeMods 3 r fl
  let r := wlog (optPunct 44 r)
  let r := (kw [w!"that"] r).getD r
  let asBinder : Option Bind := match r with
    | [.m ts, .p 46] => (binderMath ts).map fun (vs, d) => Bind.every vs d
    | _ => none
  -- `Suppose that $a$ and $b$ are positive integers.`: of new variables, as `Let`
  let plural : Option Bind := do
    let (ts, r1) ← joinedVars r
    let r2 ← kw [w!"are"] r1
    let (b, r3) ← pluralNoun ts r2
    if isEnd r3 then some b else none
  -- `Suppose that $n$ is a positive integer.`
  let singular : Option Bind := do
    let (ts, r1) ← mathChunk r
    let v ← match ts with | [.id _] => some ts | _ => if subName ts then some ts else none
    let r2 ← kw [w!"is", w!"a"] r1 <|> kw [w!"is", w!"an"] r1
    let ws := r2.takeWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
    if ws.isEmpty || !isEnd (r2.drop ws.length) then none else some (.noun (ws ++ [.m v]))
  -- `Suppose $f\colon\mathbb{R}\to\mathbb{R}$ is differentiable [and $f'$ is bounded]`: the
  -- map with the adjectives, then the other hypotheses (the binder in `many`, see `supposeIn`)
  let sigForm : Option (Bind × List Chunk) := do
    let (ts, r1) ← mathChunk r
    let _ ← Math.parseSig ts
    let r2 ← kw [w!"is"] r1
    let ws := r2.takeWhile (fun (c : Chunk) => match c with
      | .w w => w != w!"and" && w != w!"such" && w != w!"with" | .p 45 => true | _ => false)
    if ws.isEmpty || (kw [w!"a"] r2).isSome || (kw [w!"an"] r2).isSome then none
    some (Bind.noun (ws ++ [.w w!"map", .m ts]), r2.drop ws.length)
  if let some (b, rest) := sigForm then
    if isEnd rest then return .suppose [] additive caseLike contra (some (.many [b]))
    let r' ← kw [w!"and"] rest
    let (hs, r1) ← hypClauses 4 r' []
    if isEnd r1 then return .suppose hs additive caseLike contra (some (.many [b])) else none
  let asBinder := asBinder <|> (plural <|> singular).map Bind.hyp
  let (hs, r1) ← hypClauses 4 r []
  if isEnd r1 then some (.suppose hs additive caseLike contra asBinder) else none

/-- The words of a contradiction. -/
def wContradiction : List (List Codes) :=
  [[w!"this", w!"is", w!"a", w!"contradiction"], [w!"this", w!"is", w!"absurd"],
   [w!"this", w!"is", w!"impossible"], [w!"this", w!"gives", w!"a", w!"contradiction"],
   [w!"this", w!"yields", w!"a", w!"contradiction"], [w!"this", w!"contradicts"],
   [w!"we", w!"get", w!"a", w!"contradiction"], [w!"we", w!"reach", w!"a", w!"contradiction"],
   [w!"we", w!"have", w!"a", w!"contradiction"], [w!"we", w!"arrive", w!"at", w!"a", w!"contradiction"],
   [w!"we", w!"obtain", w!"a", w!"contradiction"], [w!"a", w!"contradiction"], [w!"contradiction"]]

/-- `[Hence] this is a contradiction.`, `We obtain a contradiction.`, `This contradicts
Lemma~\ref{l}.`, `This is a contradiction to \eqref{l}.`, `This contradicts our
assumption.` -/
def contradictionSent (cs : List Chunk) : Option Sent := do
  let (_, cs) := marker cs
  let cs := match kw [w!"but"] cs with
    | some r => optPunct 44 r
    | none => cs
  let r ← anyKw wContradiction cs
  let r := (kw [w!"with"] r <|> kw [w!"to"] r).getD r
  match cite r with
  | some (l, r') => if isEnd r' then some (.contradiction [l]) else none
  | none =>
    let r := (anyKw [[w!"our", w!"assumption"], [w!"the", w!"assumption"], [w!"our", w!"hypothesis"],
      [w!"the", w!"hypothesis"]] r).getD r
    if isEnd r then some (.contradiction []) else none

/-- The sentence without a final `, a contradiction.` (`, which is a contradiction.`, `,
which is absurd.`, `, which is impossible.`), if it ends so. -/
def stripContradiction (cs : List Chunk) : Option (List Chunk) :=
  let strip (ws : List Codes) : Option (List Chunk) :=
    let n := ws.length + 2
    if cs.length ≤ n then none else
    match cs.drop (cs.length - n) with
    | .p 44 :: r =>
      match kw ws r with
      | some [.p 46] => some (cs.take (cs.length - n) ++ [.p 46])
      | _ => none
    | _ => none
  [[w!"a", w!"contradiction"], [w!"which", w!"is", w!"a", w!"contradiction"],
    [w!"which", w!"is", w!"absurd"], [w!"which", w!"is", w!"impossible"]].findSome? strip

/-- The heading of a case, after `\item`: `\emph{$x\ge0$.}`, `\emph{Case 1: $x\ge0$ and
$y<0$.}`, `\emph{Case (b): $n$ is even.}` -/
def caseHeading (cs : List Chunk) : Option Sent := do
  -- the cases of an induction: `Base case: $n=1$.` and `Induction step: $n\ge2$.` are
  -- cases, `Induction step.` a heading without a hypothesis (the hypothesis of the
  -- induction is a sentence)
  if let some r := anyKw [[w!"induction", w!"step"], [w!"inductive", w!"step"]] cs then
    if isEnd r then return .caseOf []
  let cs := match anyKw [[w!"base", w!"case"], [w!"induction", w!"base"], [w!"base"],
      [w!"induction", w!"step"], [w!"inductive", w!"step"]] cs with
    | some (.p 58 :: r) => r
    | some r => r
    | none => cs
  let r := match kw [w!"case"] cs with
    | some r =>
      match r with
      | .p 40 :: .w _ :: .p 41 :: .p 58 :: r' => r'
      | .w _ :: .p 58 :: r' => r'
      | .p 58 :: r' => r'
      | r' => r'
    | none => cs
  let (hs, r1) ← hypClauses 4 r []
  if isEnd r1 then some (.caseOf hs) else none

/-- `We distinguish|consider [the following] two cases[.:]`, `There are three cases.`, `We
argue by cases.`, `We argue|proceed by contradiction.`, `The proof is by contradiction.`,
`We argue|proceed by induction on $n$.` -/
def organizeSent (cs : List Chunk) : Option Sent :=
  let (_, cs) := marker cs
  let done (r : List Chunk) : Bool := match r with
    | [.p 46] | [.p 58] => true
    | _ => false
  let caseWords : List Codes := [w!"two", w!"three", w!"four", w!"five", w!"six", w!"several",
    w!"the", w!"following", w!"different", w!"separate", w!"cases"]
  let cases : Option Sent := do
    let r ← anyKw [[w!"we", w!"distinguish"], [w!"we", w!"consider"], [w!"there", w!"are"],
      [w!"we", w!"argue", w!"by"], [w!"we", w!"distinguish", w!"between"]] cs
    let ws := r.takeWhile fun c => match c with
      | .w v => caseWords.contains v
      | _ => false
    let named := ws.any fun c => match c with
      | .w v => v == w!"cases"
      | _ => false
    if named && done (r.drop ws.length) then some .organizes else none
  let contra : Option Sent := do
    let r ← anyKw [[w!"we", w!"argue", w!"by", w!"contradiction"], [w!"we", w!"proceed", w!"by", w!"contradiction"],
      [w!"the", w!"proof", w!"is", w!"by", w!"contradiction"],
      [w!"we", w!"argue", w!"by", w!"way", w!"of", w!"contradiction"]] cs
    if done r then some .organizes else none
  -- `We argue by induction on $n$.`
  let induction : Option Sent := do
    let r ← anyKw [[w!"we", w!"argue", w!"by", w!"induction", w!"on"], [w!"we", w!"proceed", w!"by", w!"induction", w!"on"],
      [w!"the", w!"proof", w!"is", w!"by", w!"induction", w!"on"], [w!"we", w!"use", w!"induction", w!"on"],
      [w!"by", w!"induction", w!"on"]] cs
    match r with
    | .m [.id v] :: r' => if done r' then some (.inductionOn v) else none
    | _ => none
  -- `Then the following hold.` before a list whose items are sentences
  let announces : Option Sent := do
    let r ← anyKw [[w!"the", w!"following", w!"hold"], [w!"the", w!"following", w!"holds"],
      [w!"the", w!"following", w!"statements", w!"hold"], [w!"the", w!"following", w!"assertions", w!"hold"],
      [w!"the", w!"following", w!"are", w!"true"]] cs
    if done r then some .organizes else none
  -- `For S⊆…, let $F_S$ denote the component of $F$ in its Hoeffding decomposition, that is, …`:
  -- the notation `F_S` of the field `hilbert`, which reads it for every kernel
  let hoeffNote : Option Sent := do
    let rec find : Nat → List Chunk → Option (List Chunk)
      | 0, _ => none
      | _, [] => none
      | f + 1, c :: r => match kw [w!"denote", w!"the", w!"component", w!"of"] (c :: r) with
        | some r' => some r'
        | none => find f r
    let r ← find cs.length cs
    let (_, r1) ← formula r
    let _ ← kw [w!"in", w!"its"] r1 >>= fun r2 => match r2 with
      | .w h :: .w d :: _ => if lower h == w!"hoeffding" && d == w!"decomposition" then some () else none
      | _ => none
    some .organizes
  -- `[For WORDS,] we use the WORDS $φ$ from the proof of Theorem~\ref{l}.`
  let usesFrom : Option Sent := do
    let r0 := match kw [w!"for"] cs with
      | some r => match r.dropWhile (fun c => match c with | .w _ | .p 39 | .p 45 => true | _ => false) with
        | .p 44 :: r' => r'
        | _ => cs
      | none => cs
    let r1 ← kw [w!"we", w!"use", w!"the"] r0
    let ws := r1.takeWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
    let (φ, r3) ← formula (r1.drop ws.length)
    let r4 ← kw [w!"from", w!"the", w!"proof", w!"of"] r3
    let r5 := match r4 with | .w _ :: r => r | _ => r4
    match r5 with
    | .r _ l :: r6 =>
      if done r6 then some (.usesFrom l (match φ with | .chain _ _ => some φ | _ => none)) else none
    | _ => none
  -- `Here $A_a$ is the ordinal sum of Section~\ref{sec:prelim}.`: a reminder of a definition
  let reminder : Option Sent := do
    let r ← kw [w!"here"] cs
    let (m, r1) ← formula r
    match m with
    | .chain _ _ => none
    | _ =>
    let r2 ← kw [w!"is", w!"the"] r1
    let ws := r2.takeWhile (fun c => match c with | .w v => v != w!"of" | .p 45 => true | _ => false)
    let r4 ← kw [w!"of"] (r2.drop ws.length)
    match r4 with
    | .w _ :: .r _ _ :: r5 => if done r5 then some .organizes else none
    | .r _ _ :: r5 => if done r5 then some .organizes else none
    | _ => none
  -- `Letting $\varepsilon\to0$ gives the claim.`, `$\varepsilon\to0$ gives the assertion.`
  let limitEnd : Option Sent := do
    let r := (kw [w!"letting"] cs).getD cs
    match r with
    | .m ts :: r1 => if !(ts.contains (.cmd w!"to")) then none else
      let r2 ← kw [w!"gives"] r1 <|> kw [w!"yields"] r1 <|> kw [w!"proves"] r1
      let r3 ← kw [w!"the", w!"claim"] r2 <|> kw [w!"the", w!"assertion"] r2 <|> kw [w!"the", w!"theorem"] r2
      if done r3 then some .organizes else none
    | _ => none
  cases <|> contra <|> induction <|> announces <|> hoeffNote <|> usesFrom <|> reminder <|> limitEnd

def sentenceCore (cs : List Chunk) : Option Sent :=
  match descSent none cs with
  | some (.defDesc b s k np c _) =>
    some (.defDesc b s k np c (match notationSent cs with
      | some (.notation k' rhs) => some (k', rhs)
      | _ => none))
  | some s => some s
  | none =>
  match notationSent cs with
  | some s => some s
  | none =>
  match lettersSent cs <|> impliedSent cs <|> genericSent cs with
  | some s => some s
  | none =>
  match memberDef cs with
  | some s => some s
  | none =>
  match meaningSent cs with
  | some s => some s
  | none =>
  -- `[Since REASON,] we can find $c>0$ such that CLAUSE.`: as `Let $c>0$ be such that CLAUSE.`
  -- (a description in words before it, `Keeping …, spreading …, and moving …,`, is a reason)
  let finds : List (List Codes) := [[w!"we", w!"can", w!"find"], [w!"we", w!"may", w!"choose"],
    [w!"we", w!"can", w!"choose"], [w!"we", w!"may", w!"find"], [w!"we", w!"fix"], [w!"we", w!"choose"],
    [w!"we", w!"obtain"]]
  let skipDesc : List Chunk → Option (List Chunk) := fun cs0 =>
    let rec go : Nat → List Chunk → Option (List Chunk)
      | 0, _ => none
      | f + 1, cs => match anyKw finds cs with
        | some _ => some cs
        | none => match cs with
          | c :: r => if descChunk c || (match (c : Chunk) with | .p 44 | .r _ _ | .p 40 | .p 41 => true | _ => false)
              then go f r else none
          | [] => none
    go 96 cs0
  match (do
      let r0 ← skipDesc cs
      let r ← anyKw finds r0
      -- `a copula $C_\varepsilon\in\mathcal B$ such that CLAUSE`
      let r := match r with
        | .w a :: r' => if a == w!"a" || a == w!"an" then r' else r
        | _ => r
      let ws := r.takeWhile fun (c : Chunk) => match c with | .w v => v != w!"such" | _ => false
      if ws.isEmpty then none else
      let (np, r1) : List Chunk × List Chunk := match r.drop ws.length with
        | .m t :: r' => (ws ++ [Chunk.m t], r')
        | r' => (ws, r')
      if !(np.any fun (c : Chunk) => match c with | .m _ => true | _ => false) then none else
      let r2 ← kw [w!"such", w!"that"] r1
      let r2 := optPunct 44 r2
      let (cl, r3) ← suchThatClauses (fun r => thereIs r <|> clause r) r2
      if isEnd r3 then some (Sent.letSuchThatNP np cl) else none) with
  | some s => some s
  | none =>
  match (do
      let r0 := match kw [w!"since"] cs >>= wordsReason with
        | some r => optPunct 44 r
        | none => cs
      let r ← anyKw finds r0
      let (ts, r1) ← mathChunk r
      let (v, cond) ← match Math.parseFormula ts with
        | some (.id v) => some (v, none)
        | some (.chain (.id v) [rel]) => some (v, some (MT.chain (.id v) [rel]))
        | _ => none
      let r2 ← kw [w!"such", w!"that"] r1
      let r2 := optPunct 44 r2
      let (cl, r3) ← clause r2 <|> thereIs r2 <|> suchThatClauses (fun r => thereIs r <|> clause r) r2
      let cl := match cond with
        | some m => Clause.both [.fact m, cl]
        | none => cl
      if isEnd r3 then some (Sent.letSuchThat v cl []) else none) with
  | some s => some s
  | none =>
  let (topic, cs) := marker cs
  match tfae cs with
  | some ps => some (.claims topic [] ps)
  | none =>
  match notionDef cs with
  | some s => some s
  | none =>
  -- let $S$ denote the class of NOUNS, that is, NP.
  match kw [w!"let"] cs with
  | some r =>
    -- `Let $a,b,c$ be the side lengths of a triangle.` (`the sides of a triangle`, `the lengths
    -- of the sides of a triangle`): positive numbers with the triangle inequalities
    (do
      -- (the letters in one formula, `$a,b,c$`, or in three, `$a$, $b$, and $c$`)
      let (vs, r1) ← (do
          let (ts, r1) ← mathChunk r
          let parts := (Math.commaParts (ts.length + 1) 0 [] ts []).filter (!·.isEmpty)
          let vs ← parts.mapM (fun (p : List MTok) => match p with | [.id v] => some v | _ => none)
          if vs.length == 3 then some (vs, r1) else none) <|> (do
          let rec letters : Nat → List Chunk → List Codes → Option (List Codes × List Chunk)
            | 0, _, _ => none
            | f + 1, cs, acc => match cs with
              | .m [.id v] :: rest =>
                let rest' := ((punct 44 rest).getD rest)
                let rest' := (kw [w!"and"] rest').getD rest'
                if rest'.length == rest.length then some ((v :: acc).reverse, rest) else letters f rest' (v :: acc)
              | _ => none
          letters 4 r [])
      let [a, b, c] := vs | none
      let r2 ← kw [w!"be", w!"the", w!"side", w!"lengths", w!"of", w!"a", w!"triangle"] r1 <|>
        kw [w!"be", w!"the", w!"sides", w!"of", w!"a", w!"triangle"] r1 <|>
        kw [w!"be", w!"the", w!"lengths", w!"of", w!"the", w!"sides", w!"of", w!"a", w!"triangle"] r1
      if !isEnd r2 then none
      let lt (x y : MT) : MT := .chain x [(.lt, y)]
      let (x, y, z) := (MT.id a, MT.id b, MT.id c)
      some (.assumeAll [.every [a, b, c] (.id w!"\\mathbb{R}"),
        .ifCond (.conj [lt (.num 0) x, lt (.num 0) y, lt (.num 0) z, lt x (.add y z), lt y (.add x z), lt z (.add x y)])] [])) <|>
    -- `Let $Y$ be an integrable random variable [with [continuous] distribution function $F$]`
    (do
      let (ts, r1) ← mathChunk r
      let y ← match ts with | [.id v] => some v | _ => none
      let (integ, r2) ← (do let r' ← kw [w!"be", w!"an", w!"integrable", w!"random", w!"variable"] r1; some (true, r')) <|>
        (do let r' ← kw [w!"be", w!"a", w!"random", w!"variable"] r1; some (false, r'))
      let (df, cont, r3) : Option Codes × Bool × List Chunk :=
        match kw [w!"with", w!"continuous", w!"distribution", w!"function"] r2,
            kw [w!"with", w!"distribution", w!"function"] r2 with
        | some (.m [.id fv] :: r'), _ => (some fv, true, r')
        | _, some (.m [.id fv] :: r') => (some fv, false, r')
        | _, _ => (none, false, r2)
      if isEnd r3 then some (Sent.randomVar y integ df cont) else none) <|>
    -- `let $Z$ be uniformly distributed on $[0,1]$ [and defined on the same probability space]`
    (do
      let (ts, r1) ← mathChunk r
      let z ← match ts with | [.id v] => some v | _ => none
      let r2 ← kw [w!"be", w!"uniformly", w!"distributed", w!"on"] r1
      let (dom, r3) ← formula r2
      let r4 := (kw [w!"and", w!"defined", w!"on", w!"the", w!"same", w!"probability", w!"space"] r3).getD r3
      if isEnd r4 then some (Sent.uniformVar z dom) else none) <|>
    -- `Let $f:A\to B$ be given|defined by $f(x,y)=e$.`
    (do
      let (s, r1) ← sig r
      let r2 ← kw [w!"be", w!"given", w!"by"] r1 <|> kw [w!"be", w!"defined", w!"by"] r1
      let (pieces, ls, r3) ← defPieces 6 r2 [] []
      if isEnd (trailer r3) then some (.defBy s (pieces.map piecesDefeq) ls none) else none) <|>
    -- `Let $c>0$ be fixed.`, `Let $\gamma$ be fixed.`: as `Fix $c>0$.`
    (do
      let (ts, r1) ← mathChunk r
      let r2 ← kw [w!"be", w!"fixed"] r1
      let b ← fixBinder ts
      if isEnd r2 then some (.fix b [] []) else none) <|>
    -- `Let $0<\varepsilon\ll1$.`
    (do
      let (ts, r1) ← mathChunk r
      let b ← smallBinder ts
      if isEnd r1 then some (.assume b) else none) <|>
    -- `Let $x\in A$.`
    (do
      let (ts, r1) ← mathChunk r
      let (vs, d) ← binderMath ts
      if isEnd r1 then some (.assume (.every vs d)) else none) <|>
    -- `Let $c>0$.`: a condition, assumed for the rest of the result or proof
    (do
      let (ts, r1) ← mathChunk r
      let m ← Math.parseFormula ts
      if isEnd r1 && isCondition m then some (.assume (.ifCond m)) else none) <|>
    -- `Let $m$ be such that CLAUSE[, and let $X\coloneqq e$, …]`
    (do
      let (ts, r1) ← mathChunk r
      -- (`Let $c>0$ be such that …`: the condition is part of the property)
      let (v, cond) ← match Math.parseFormula ts with
        | some (.id v) => some (v, none)
        | some (.chain (.id v) [rel]) => some (v, some (MT.chain (.id v) [rel]))
        | _ => none
      let r2 ← kw [w!"be", w!"such", w!"that"] r1
      let r2 := optPunct 44 r2
      let (cl, r3) ← clause r2 <|> thereIs r2 <|> suchThatClauses (fun r => thereIs r <|> clause r) r2
      let cl := match cond with
        | some m => Clause.both [.fact m, cl]
        | none => cl
      let (bs, ds, r4) ← letMore 6 r3 [] []
      if isEnd r4 && bs.isEmpty then some (.letSuchThat v cl ds) else none) <|>
    -- `Let $C$ be a|an NP[, and let …]`, `Let $a,b\in A$, and let $X\coloneqq e$, ….`
    (do
      let (b1, r1) ← letBinder r
      let (bs, ds, r2) ← letMore 6 r1 [b1] []
      let isNoun := match b1 with | .noun _ | .many _ => true | _ => false
      if isEnd r2 && (isNoun || bs.length > 1 || !ds.isEmpty) then some (.assumeAll bs ds) else none) <|>
    -- `Let $X\coloneqq e$.`, `Let $h(k)=e$.`: as `set`
    constDefsOf none r <|>
    -- `Let DISPLAY denote the NAME, NAME, and NAME NOUNS.`
    (do
      let (items, ls, r1) ← defList 6 r [] []
      if items.isEmpty || !items.all isDefeq then none else
      let r2 ← kw [w!"denote", w!"the"] r1 <|> kw [w!"be", w!"the"] r1
      if r2.length < 2 || !isEnd (r2.drop (r2.length - 1)) then none else
      let np := r2.dropLast
      if !np.all (fun c => match c with | .w _ | .p 44 | .p 45 | .m _ => true | _ => false) then none else
      some (.defsNamed items ls np)) <|>
    -- `Let $f,g:A\to B$ be continuous, normalized by …, with derivatives DISPLAY.`
    (do
      let (ts, r1) ← mathChunk r
      let (names, dom, cod) ← namesSig ts
      let r2 ← kw [w!"be", w!"continuous"] r1
      let r3 ← punct 44 r2 >>= kw [w!"normalized", w!"by"]
      let (anchors, r4) ← anchorList 6 r3 []
      let r5 ← kw [w!"with", w!"derivatives"] r4
      let (m, ls, r6) ← display r5
      if isEnd r6 then some (.defDeriv none [] names dom cod anchors m ls) else none) <|>
    (do
    let (sym, r1) ← formula r
    let r2 ← kw [w!"denote", w!"the"] r1
    let r2 ← classOf r2
    -- `let $\mathcal F$ denote the class of functions $f:[0,1]\to\mathbb{R}$ with $φ$ and
    -- $ψ$.`: the class of the objects that a noun phrase with a variable describes
    let described := r2.any fun c => match c with | .m ts => isSig ts | _ => false
    if described && isEnd (r2.drop (r2.length - 1)) then some (.defClass sym [] r2.dropLast) else
    let (plural, r3) ← wordsUntil [] 6 r2 [] <|> (do
      let ws := r2.takeWhile (fun c => match c with | .w _ => true | _ => false)
      some (ws.filterMap (fun c => match c with | .w w => some w | _ => none), r2.drop ws.length))
    -- `let $S$ denote the class of NOUNS.`: a class of the vocabulary
    if isEnd r3 then some (.defClass sym plural []) else do
    let r4 ← punct 44 r3 >>= kw [w!"that", w!"is"] >>= punct 44
    let np := r4.dropLast
    if isEnd (r4.drop np.length) then some (.defClass sym plural np) else none)
  | none =>
  -- `[We] denote by $S$ the class of NOUNS.`, `[We] denote the class of NOUNS by $S$.`
  let cs1 := (kw [w!"we"] cs).getD cs
  match kw [w!"denote", w!"by"] cs1, kw [w!"denote", w!"the"] cs1 with
  | some r, _ => do
    let (sym, r1) ← formula r
    let r2 ← kw [w!"the"] r1 >>= classOf
    let ws := r2.takeWhile (fun c => match c with | .w _ => true | _ => false)
    let plural := ws.filterMap (fun c => match c with | .w w => some w | _ => none)
    if isEnd (r2.drop ws.length) && !plural.isEmpty then some (.defClass sym plural []) else none
  | none, some r => do
    let r1 ← classOf r
    let ws := r1.takeWhile (fun c => match c with | .w v => v != w!"by" | _ => false)
    let plural := ws.filterMap (fun c => match c with | .w w => some w | _ => none)
    let r2 ← kw [w!"by"] (r1.drop ws.length)
    let (sym, r3) ← formula r2
    if isEnd r3 && !plural.isEmpty then some (.defClass sym plural []) else none
  | none, none =>
  -- define $sig$ by DISPLAY [and observe that $φ$ for every $x\in A$].
  match kw [w!"define"] cs with
  | some r => (do
    let (s, r1) ← sig r
    let r2 ← kw [w!"by"] r1
    let (pieces, ls, r3) ← defPieces 6 r2 [] []
    let pieces := pieces.map piecesDefeq
    if isEnd r3 then some (.defBy s pieces ls none)
    else do
      let r4 ← kw [w!"and", w!"observe", w!"that"] r3
      let (φ, r5) ← formula r4
      let r6 ← kw [w!"for", w!"every"] r5
      let (ts, r7) ← mathChunk r6
      let (vs, dom) ← binderMath ts
      if isEnd r7 then some (.defBy s pieces ls (some (φ, vs, dom))) else none) <|>
    constDefsOf none r
  | none =>
  match kw [w!"set"] cs <|> kw [w!"put"] cs <|> kw [w!"write"] cs <|> kw [w!"we", w!"set"] cs <|>
      kw [w!"we", w!"put"] cs <|> kw [w!"let", w!"us", w!"set"] cs <|> kw [w!"we", w!"write"] cs <|>
      kw [w!"we", w!"therefore", w!"set"] cs <|> kw [w!"we", w!"therefore", w!"define"] cs <|>
      kw [w!"we", w!"therefore", w!"put"] cs <|> kw [w!"we", w!"define"] cs with
  | some r => constDefsOf none r
  | none =>
  -- fix $B$ [and define|set|put DEFS].
  match kw [w!"fix"] cs with
  | some r =>
    -- `Fix a sufficiently large $R$.`, `Fix a sufficiently small $\eta>0$.`
    (do
      let r1 ← kw [w!"a"] r <|> kw [w!"an"] r
      let (b, r2) ← sufficientBinder r1
      if isEnd r2 then some (.fix b [] []) else none) <|>
    -- `Fix an integer $k\ge3$ and $\lambda>0$.`
    (do
      let r1 ← kw [w!"a"] r <|> kw [w!"an"] r
      let k ← r1.zipIdx.findSome? fun (c, i) => match c, r1[i + 1]? with
        | .w w, some (.m _) => if w == w!"and" then some i else none
        | _, _ => none
      let np := r1.take k
      if np.isEmpty || np.any (fun c => match c with | .p 44 | .p 46 => true | _ => false) then none else
      let (bs, r2) := moreAnd 4 (r1.drop k) []
      if bs.isEmpty || !isEnd r2 then none else
      some (.fix (.many (.noun np :: bs)) [] [])) <|>
    -- `Fix an integer $k\ge3$.`
    (do
      let r1 ← kw [w!"a"] r <|> kw [w!"an"] r
      let np := r1.takeWhile (fun c => match c with | .p 46 | .p 44 => false | _ => true)
      if np.isEmpty || !isEnd (r1.drop np.length) then none else
      some (.fix (.noun np) [] [])) <|> do
    let (ts, r1) ← mathChunk r
    let b ← fixBinder ts
    if isEnd r1 then some (.fix b [] []) else
    -- `Fix $a>0$, $b\in A$ and $c$.`: several binders
    let rec more : Nat → List Chunk → List Bind → List Bind × List Chunk
      | 0, r, acc => (acc.reverse, r)
      | f + 1, r, acc =>
        match (do
            let r' ← kw [w!"and"] r <|> (do let r'' ← punct 44 r; some ((kw [w!"and"] r'').getD r''))
            let (ts', r2) ← mathChunk r'
            let b' ← fixBinder ts'
            some (b', r2)) with
        | some (b', r2) => more f r2 (b' :: acc)
        | none => (acc.reverse, r)
    let (bs, rb) := more 6 r1 []
    if !bs.isEmpty && isEnd rb then some (.fix (.many (b :: bs)) [] []) else do
    let r2 ← kw [w!"and"] r1
    let r3 ← kw [w!"define"] r2 <|> kw [w!"set"] r2 <|> kw [w!"put"] r2
    let (items, ls, r4) ← defList 6 r3 [] []
    if isEnd (trailer r4) && !items.isEmpty && items.all isDefeq then some (.fix b items ls) else none
  | none =>
  -- `The boundary of the region is described by the function $\Phi:[-1,1]\to[-1,1]$ given by
  -- DISPLAY[, which satisfies $φ$ for every $r\in[-1,1]$].`: as `Define $sig$ by DISPLAY [and
  -- observe that …]`; the words before the function describe it
  match (do
      let i ← cs.findIdx? fun (c : Chunk) => match c with | .m ts => isSig ts | _ => false
      let pre := cs.take i
      if pre.length < 2 || pre.length > 16 || !pre.all (fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false) then none
      if !(match pre.getLast? with
          | some (.w w) => w == w!"function" || w == w!"map" || w == w!"mapping"
          | _ => false) then none
      let (sg, r1) ← sig (cs.drop i)
      let r2 ← kw [w!"given", w!"by"] r1 <|> kw [w!"defined", w!"by"] r1
      let (pieces, ls, r3) ← defPieces 6 r2 [] []
      let pieces := pieces.map piecesDefeq
      if isEnd r3 then some (Sent.defBy sg pieces ls none)
      else do
        let r4 ← kw [w!"which", w!"satisfies"] (optPunct 44 r3)
        let (φ, r5) ← formula r4
        let r6 ← kw [w!"for", w!"every"] r5 <|> kw [w!"for", w!"all"] r5
        let (ts, r7) ← mathChunk r6
        let (vs, dom) ← binderMath ts
        if isEnd r7 then some (Sent.defBy sg pieces ls (some (φ, vs, dom))) else none) with
  | some s => some s
  | none =>
  -- `The copulas $M(u,v)\coloneqq…$, $W(u,v)\coloneqq…$, and $\Pi(u,v)\coloneqq uv$ describe
  -- comonotonicity, countermonotonicity, and independence, respectively.`: as `Let DEFS
  -- denote the NAME, NAME, and NAME NOUNS.`
  match (do
      let r ← kw [w!"the"] cs
      let ws := r.takeWhile (fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false)
      if ws.isEmpty || ws.length > 3 then none
      let (items, ls, r1) ← defList 6 (r.drop ws.length) [] []
      if items.isEmpty || !items.all isDefeq then none
      let r2 ← kw [w!"describe"] r1 <|> kw [w!"describes"] r1 <|> kw [w!"represent"] r1 <|>
        kw [w!"represents"] r1 <|> kw [w!"model"] r1 <|> kw [w!"models"] r1 <|>
        kw [w!"correspond", w!"to"] r1 <|> kw [w!"corresponds", w!"to"] r1
      if !(r2.getLast? matches some (.p 46)) then none
      let body := r2.dropLast
      let body := match body.reverse with
        | .w w :: .p 44 :: rest => if w == w!"respectively" then rest.reverse else body
        | .w w :: rest => if w == w!"respectively" then rest.reverse else body
        | _ => body
      if body.isEmpty || !body.all (fun (c : Chunk) => match c with | .w _ | .p 44 | .p 45 => true | _ => false) then none
      some (Sent.defsNamed items ls (body ++ ws))) with
  | some s => some s
  | none =>
  -- We say that a N $x$ is PHRASE of a ADJ $sig$ if $φ$ for all $u,v\in A$.
  match kw [w!"we", w!"say", w!"that", w!"a"] cs with
  | some r => do
    let (sbj, r1) ← chunksUntil [w!"is"] r []
    let r2 ← kw [w!"is"] r1
    let (phrase, r3) ← wordsUntil [w!"of"] 8 r2 []
    let r4 ← kw [w!"of", w!"a"] r3 <|> kw [w!"of", w!"an"] r3
    let (o, r5) ← chunksUntil [w!"if"] r4 []
    let r6 ← kw [w!"if"] r5
    let (φ, r7) ← formula r6
    let r8 ← kw [w!"for", w!"all"] r7
    let (ts, r9) ← mathChunk r8
    let (vs, dom) ← binderMath ts
    if isEnd r9 then some (.weSay sbj phrase o φ vs dom) else none
  | none =>
  -- NAME is denoted by $S$.
  match chunksUntil [w!"is"] cs [] with
  | some (name, r) =>
    match kw [w!"is", w!"denoted", w!"by"] r with
    | some r1 => do
      let (s, r2) ← formula r1
      if isEnd r2 then some (.denotedBy name s) else none
    | none => claimsOrDefs topic cs
  | none => claimsOrDefs topic cs
where
  /-- `$S$ be NP[, where $sig$ is given by DISPLAY].` -/
  letBe (b : Bind) (sets : List MT) (cs : List Chunk) : Option Sent := do
    let (sym, r1) ← formula cs
    let r2 ← kw [w!"be"] r1
    let np := r2.takeWhile (fun c => match c with | .p 46 | .p 44 => false | _ => true)
    let r3 := r2.drop np.length
    if isEnd r3 then some (.defSteps b sets sym np none)
    else do
      let r4 ← punct 44 r3 >>= kw [w!"where"]
      let (sg, r5) ← sig r4
      let r6 ← kw [w!"is", w!"given", w!"by"] r5
      let (m, ls, r7) ← display r6
      if isEnd r7 then some (.defSteps b sets sym np (some (sg, m, ls))) else none
  /-- The pieces of a definition, separated by `,` and `, and`. -/
  defPieces : Nat → List Chunk → List DefPiece → List Codes → Option (List DefPiece × List Codes × List Chunk)
    | 0, _, _, _ => none
    | f + 1, cs, acc, ls => do
      let (p, ls', r) ← (do
          -- on $D$, parametrically by DISPLAY
          let r1 ← kw [w!"on"] cs
          let (d, r2) ← formula r1
          let r3 ← punct 44 r2
          let r4 ← kw [w!"parametrically", w!"by"] r3
          let (m, ls', r5) ← display r4
          some (DefPiece.param d m, ls', r5)) <|>
        (do let (m, ls', r1) ← display cs; some (DefPiece.formula m, ls', r1)) <|>
        (do let (m, r1) ← formula cs; some (DefPiece.formula m, [], r1))
      let acc := p :: acc
      let ls := ls ++ ls'
      match punct 44 r with
      | some r' =>
        match kw [w!"and"] r' with
        | some r'' =>
          if (kw [w!"observe"] r'').isSome then some (acc.reverse, ls, r)
          else defPieces f (optPunct 44 r'') acc ls
        | none => defPieces f r' acc ls
      | none =>
        match kw [w!"and"] r with
        | some r' =>
          if (kw [w!"observe"] r').isSome then some (acc.reverse, ls, r)
          else defPieces f (optPunct 44 r') acc ls
        | none => some (acc.reverse, ls, r)
  claimsOrDefs (topic : Topic) (cs : List Chunk) : Option Sent :=
    -- `Since $φ$ [and $ψ$], [it follows that] CLAUSES.`: the reasons are claims too
    match kw [w!"since"] cs with
    | some r =>
      (do
        let (facts, r1) ← sinceFacts 4 r []
        let r2 ← punct 44 r1
        let (_, r3) := marker r2
        let rest ← clauses 24 r3 []
        some (.claims topic [] (facts.map (fun m => ({ cites := [], clause := .fact m } : CClause)) ++ rest))) <|>
      (do
        -- `Since the pairs $(U_i,V_i)$ are independent, CLAUSES`: a reason in words, whose
        -- formulas state nothing (no relation), asserts nothing, as after the claims
        let r1 ← wordsReason r
        let r2 ← punct 44 r1
        let (_, r3) := marker r2
        let rest ← clauses 24 r3 []
        some (.claims topic [] rest))
    | none =>
    match binder cs with
    | some (b, r) =>
      -- `For every $r\in(-1,1)$ and $s\coloneqq e$, CLAUSES`: definitions with the binder,
      -- made with the first clause
      let (bdefs, r) := binderDefs 4 r []
      -- `For every NP there is …` needs no comma
      -- (`For B there is …`, `For B set …`: the comma is optional before a verb)
      let r := match r with
        | .w w :: _ =>
          let w := lower w
          if [w!"there", w!"set", w!"define", w!"write", w!"put", w!"let", w!"we", w!"consider"].contains w
          then Chunk.p 44 :: r else r
        | _ => r
      match (punct 44 r).map fun r1 => (kw [w!"then"] r1).getD r1 with
      | some r1 =>
        match descSent (some b) r1 with
        | some s => some s
        | none =>
        -- For B, let $S$ denote NP.
        match kw [w!"let"] r1 with
        | some r2 =>
          (do
            let (s, r3) ← formula r2
            let r4 ← kw [w!"denote"] r3
            let np := r4.takeWhile (fun c => match c with
              | .p 46 => false | .w v => v != w!"from" | _ => true)
            let rest := trailer (r4.drop np.length)
            if isEnd rest then some (.letDenote b s np) else none) <|>
          letBe b [] r2 <|>
          -- For B, let $h(k)=e$.: as `set`
          constDefsOf (some b) r2
        | none =>
        -- For B, define $f_b:A\to B$ by DISPLAY.
        match (do
            let r2 ← kw [w!"define"] r1
            -- (`define the corresponding rank map $\zeta_c:[0,1]\to[0,1]$ by`: the words name
            -- the map)
            let r2 := match r2 with
              | .w t :: rest =>
                let ws := rest.takeWhile (fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false)
                if t == w!"the" && ws.length ≤ 6 && (match rest.drop ws.length with
                    | .m ts :: _ => isSig ts | _ => false) then rest.drop ws.length else r2
              | _ => r2
            let (sg, r3) ← sig r2
            let r4 ← kw [w!"by"] r3
            let (pieces, ls, r5) ← defPieces 6 r4 [] []
            if isEnd (trailer r5) then some (Sent.defByFamily b sg pieces ls) else none) with
        | some st => some st
        | none =>
        -- For B, set $X\coloneqq e$ and let $S$ be NP[, where …].
        match kw [w!"set"] r1 <|> kw [w!"write"] r1 <|> kw [w!"put"] r1 <|> kw [w!"we", w!"set"] r1 <|>
            kw [w!"we", w!"put"] r1 <|> kw [w!"we", w!"write"] r1 with
        | some r2 =>
          -- `we write $C^\top(u,v)\coloneqq C(v,u)$ for the transpose of $C$`: the name is
          -- not read
          let r2' := r2
          let r2 := match r2 with
            | .m ts :: r3 =>
              let named := (kw [w!"for", w!"the"] r3 <|> kw [w!"for", w!"its"] r3).isSome &&
                (r3.getLast? matches some (.p 46)) && r3.dropLast.all (fun c => match c with
                  | .w _ | .p 45 => true
                  | .m t => (match Math.parseFormula t with | some (.id _) => true | _ => false)
                  | _ => false) &&
                (match Math.parseFormula ts with | some m => isDefeq m | none => false)
              if named then [Chunk.m ts, .p 46] else r2
            | _ => r2
          -- (an operation on the binder's variable keeps its name: `its transpose` is then
          -- read)
          let namedOp : Option Sent := match r2', r2 with
            | .m ts :: r3, [.m _, .p 46] =>
              match Math.parseFormula ts with
              | some m =>
                let onVar := match m with
                  | .chain (.app h _) _ | .chain h _ => (match h with
                    | .sup (.id _) (.id _) | .hat (.id _) | .sup (.sub (.id _) (.num _)) (.id _) => true
                    | _ => false)
                  | _ => false
                let name := (r3.drop 2).filterMap fun (c : Chunk) => match c with | .w w => some w | _ => none
                if onVar && !name.isEmpty then some (.defIs b [⟨name, m, []⟩]) else none
              | none => none
            | _, _ => none
          if let some sn := namedOp then some sn else
          (do
          let (m, r3) ← formula r2
          let r4 ← kw [w!"and", w!"let"] r3
          letBe b [m] r4) <|> derivAfterSet b r2 <|> constDefsOf (some b) r2
        | none =>
        -- For B, the NAME $sig$ reads DISPLAY.
        match defReads b r1 with
        | some s => some s
        | none =>
        -- For B, the NAME is DEF (, and the NAME is DEF)*.
        match defItems 4 r1 [] with
        | some items => some (.defIs b items)
        | none => do
          -- For B, (For B,)* CLAUSES.
          let (bs, r2) ← moreBinders 3 r1 [b]
          -- (`For B, we have CLAUSES`: words that join the binder to its clause)
          let r2 := (kw [w!"we", w!"have", w!"that"] r2 <|> kw [w!"we", w!"have"] r2 <|>
            kw [w!"one", w!"has"] r2 <|> kw [w!"it", w!"holds", w!"that"] r2).getD r2
          -- `For B, since $φ$, $ψ$, and $χ$, we obtain DISPLAY`: the reasons are claims too
          let sincePart : Option (List CClause × List Chunk) := do
            let r ← kw [w!"since"] r2
            let (facts, r1) ← sinceFacts 4 r []
            let r3 ← punct 44 r1
            let r3 := (kw [w!"we", w!"obtain"] r3 <|> kw [w!"we", w!"have"] r3 <|> kw [w!"we", w!"get"] r3).getD r3
            some (facts.map (fun m => ({ cites := [], clause := .fact m } : CClause)), r3)
          let (pre, r2) := sincePart.getD ([], r2)
          -- (`For B, the function $q_t$ takes the values …, so CLAUSES`: the description asserts
          -- nothing)
          let cs ← clauses 24 r2 [] <|> (descSo r2 >>= fun r' => clauses 24 r' [])
          let cs := pre ++ cs
          let cs := match cs with
            | c :: rest => { c with defs := bdefs ++ c.defs } :: rest
            | [] => []
          some (.claims topic bs cs)
      | none => none
    | none =>
      (do
        let items ← defItems 4 cs []
        let ds := items.flatMap fun it => match it.defn with | .conj xs => xs | m => [m]
        if ds.all isDefeq then some (.constDefs none ds (items.flatMap (·.labels))) else none) <|>
      (do
        let cs ← clauses 24 cs [] <|> (descSo cs >>= fun r' => clauses 24 r' [])
        some (.claims topic [] cs))
  /-- `and $s\coloneqq e$` after a binder: definitions made with the sentence's binders. -/
  binderDefs : Nat → List Chunk → List MT → List MT × List Chunk
    | 0, cs, acc => (acc.reverse, cs)
    | f + 1, cs, acc =>
      match kw [w!"and"] cs >>= formula with
      | some (m, r) => if isDefeq m then binderDefs f r (m :: acc) else (acc.reverse, cs)
      | none => (acc.reverse, cs)
  /-- `$φ$[, $ψ$] [and $χ$]` before the comma of `since`. -/
  sinceFacts : Nat → List Chunk → List MT → Option (List MT × List Chunk)
    | 0, _, _ => none
    | f + 1, cs, acc => do
      let (m, r) ← formula cs
      -- `$φ$ for $u\in[0,1]$`: for every `u`
      let (m, r) := match kw [w!"for"] r >>= (fun r' => mathChunk ((kw [w!"all"] r' <|> kw [w!"every"] r').getD r')) with
        | some (ts, r') => match binderMath ts with
          | some (vs, d) => (MT.quant true vs d m, r')
          | none => (m, r)
        | none => (m, r)
      let acc := m :: acc
      match kw [w!"and"] r with
      | some r' => sinceFacts f r' acc
      | none =>
        match r with
        | .p 44 :: .m t :: r' => sinceFacts f (.m t :: r') acc
        | .p 44 :: .w a :: .m t :: r' => if a == w!"and" then sinceFacts f (.m t :: r') acc else some (acc.reverse, r)
        | _ => some (acc.reverse, r)
  /-- `set DEFS, and define continuous functions $f,g:A\to B$ by ANCHORS, and DISPLAY.` -/
  derivAfterSet (b : Bind) (cs : List Chunk) : Option Sent := do
    let (items, _, r1) ← defList 6 cs [] []
    if !items.all isDefeq then none else
    let r2 ← (punct 44 r1 >>= kw [w!"and"]) <|> kw [w!"and"] r1
    let r3 ← kw [w!"define", w!"continuous", w!"functions"] r2
    let (ts, r4) ← mathChunk r3
    let (names, dom, cod) ← namesSig ts
    let r5 ← kw [w!"by"] r4
    let (anchors, r6) ← anchorList 6 r5 []
    let (m, ls, r7) ← display r6
    if isEnd r7 then some (.defDeriv (some b) items names dom cod anchors m ls) else none
  defReads (b : Bind) (cs : List Chunk) : Option Sent := do
    let r ← kw [w!"the"] cs
    let (name, r1) ← wordsUntil [] 6 r [] <|> (do
      let ws := r.takeWhile (fun c => match c with | .w _ => true | _ => false)
      some (ws.filterMap (fun c => match c with | .w w => some w | _ => none), r.drop ws.length))
    let (s, r2) ← sig r1
    let r3 ← kw [w!"reads"] r2
    let (m, ls, r4) ← display r3
    if isEnd r4 then some (.defReads b name s m ls) else none
  defItems : Nat → List Chunk → List DefItem → Option (List DefItem)
    | 0, _, _ => none
    | f + 1, cs, acc => do
      let (it, r) ← defItem cs
      let r := trailer r
      if isEnd r then some (it :: acc).reverse
      else do
        let r' ← punct 44 r >>= kw [w!"and"]
        defItems f r' (it :: acc)
  moreBinders : Nat → List Chunk → List Bind → Option (List Bind × List Chunk)
    | 0, cs, acc => some (acc.reverse, cs)
    | f + 1, cs, acc =>
      match binder cs with
      | some (b, r) =>
        -- (`For B, if $φ$, then CLAUSES`)
        match punct 44 r with
        | some r' => moreBinders f ((kw [w!"then"] r').getD r') (b :: acc)
        | none => some (acc.reverse, cs)
      | none => some (acc.reverse, cs)

/-- A sentence that runs through a list (`Then \begin{enumerate}[(i)] \item $φ$, $ψ$,
\item $χ$. \end{enumerate}`): the same sentence with its items one after the other,
joined by `, and`. An item is what stands between two markers of the list, without its
label and its final comma, semicolon or `and`. Words that only announce the list (`the
following hold:`) are dropped. -/
def joinList (cs : List Chunk) : Option (List Chunk) :=
  let isX (c : Chunk) : Bool := match c with | .x => true | _ => false
  if !cs.any isX then none else
  match listItems cs [] [] with
  | pre :: rest =>
    let tail := rest.getLast?.getD []
    -- (the option of the list, `[(i)]`, and the label of an item)
    let unlabel (it : List Chunk) : List Chunk := match it with
      | .p 91 :: r => (r.dropWhile (fun (c : Chunk) => match c with
          | .p 93 => false | .w _ | .p _ => true | _ => false)).drop 1
      | _ => it
    let clean (it : List Chunk) : List Chunk :=
      let it := unlabel it
      let it := match it.reverse with
        | .w a :: .p 44 :: r => if a == w!"and" then r.reverse else it
        | .w a :: r => if a == w!"and" then r.reverse else it
        | _ => it
      match it.reverse with
      | .p c :: r => if c == 59 || c == 46 || c == 44 then r.reverse else it
      | _ => it
    let items := (rest.dropLast.map clean).filter (!·.isEmpty)
    if items.isEmpty then none else
    -- (a list ends its sentence, or the sentence ends after it)
    if !(tail.isEmpty || isEnd tail) then none else
    let pre := match pre.reverse with
      | .p 58 :: r => r.reverse
      | _ => pre
    let announce : List (List Codes) :=
      [[w!"the", w!"following", w!"hold"], [w!"the", w!"following", w!"holds"],
       [w!"the", w!"following", w!"statements", w!"hold"], [w!"the", w!"following", w!"assertions", w!"hold"],
       [w!"the", w!"following", w!"are", w!"true"], [w!"the", w!"following", w!"is", w!"true"]]
    let pre := match announce.find? (fun a => pre.length ≥ a.length &&
        (kw a (pre.drop (pre.length - a.length))).any (·.isEmpty)) with
      | some a => pre.take (pre.length - a.length)
      | none => pre
    let joined := items.foldl (fun acc it => if acc.isEmpty then it else acc ++ [.p 44, .w w!"and"] ++ it) []
    some (pre ++ joined ++ [.p 46])
  | [] => none

/-- `Every NP satisfies CLAUSES` as `For every NP, CLAUSES` (several statements about each
object of the noun phrase: `Every copula $C$ satisfies $φ$, $ψ$, and $χ$.`). -/
def everySatisfies (cs : List Chunk) : Option (List Chunk) := do
  let r ← kw [w!"every"] cs
  let (np, r1) ← chunksUntil [w!"satisfies", w!"obeys"] r []
  let r2 ← kw [w!"satisfies"] r1 <|> kw [w!"obeys"] r1
  some ([.w w!"for", .w w!"every"] ++ np ++ [.p 44] ++ r2)

/-- `Every NP $x$ is …` as `For every NP $x$, $x$ is …` (`Every cyclic group $G$ is
abelian.`): the noun phrase ends with its variable. -/
def everyIsSent (cs : List Chunk) : Option (List Chunk) := do
  let r ← kw [w!"every"] cs
  let (np, r1) ← chunksUntil [w!"is"] r []
  let _ ← kw [w!"is"] r1
  -- (the variable: the first formula, after the noun; a modifier may follow it, `every point
  -- $P$ lying on $\Gamma$ is …`)
  -- (a formula after a preposition is a complement, `every subgroup of $G$ is normal`: the
  -- object has a variable of its own)
  let preps := [w!"of", w!"in", w!"on", w!"over", w!"to", w!"from", w!"with", w!"at", w!"by", w!"for"]
  let firstAfterPrep : Bool := match np.findIdx? (fun c => match c with | .m _ => true | _ => false) with
    | some (i + 1) => match np[i]? with
      | some (.w w) => preps.contains w
      | _ => false
    | _ => false
  if firstAfterPrep && (np.head?.map (fun c => match c with | .w _ => true | _ => false)).getD false then
    let v : Codes := w!"ve"
    -- (with a formula after the complement, `every subgroup of $G$ of order $p$`, the variable
    -- follows the noun's words: `subgroup $x$ of $G$ of order $p$`)
    let rec headLen : Nat → List Chunk → Nat
      | 0, _ => 0
      | f + 1, cs => match cs with
        | .w w :: r => if preps.contains w || [w!"that", w!"which", w!"such", w!"whose"].contains w then 0 else headLen f r + 1
        | .p 45 :: r => headLen f r + 1
        | .m _ :: .p 45 :: r => headLen f r + 2
        | _ => 0
    let k := headLen (np.length + 1) np
    let afterComp := (np.drop k).drop 2
    if afterComp.any (fun c => match c with | .m _ => true | _ => false) then
      return [.w w!"for", .w w!"every"] ++ np.take k ++ [.m [.id v]] ++ np.drop k ++ [.p 44, .m [.id v]] ++ r1
    return [.w w!"for", .w w!"every"] ++ np ++ [.m [.id v], .p 44, .m [.id v]] ++ r1
  match np.find? (fun c => match c with | .m _ => true | _ => false) with
  | some (.m [.id v]) => some ([.w w!"for", .w w!"every"] ++ np ++ [.p 44, .m [.id v]] ++ r1)
  | some (.m [.cmd v]) => some ([.w w!"for", .w w!"every"] ++ np ++ [.p 44, .m [.cmd v]] ++ r1)
  -- (`every integer $n\ge2$ is …`: the variable of the condition)
  | some (.m ts) =>
    match Math.parseFormula ts with
    | some (.chain (.id v) (_ :: _)) => some ([.w w!"for", .w w!"every"] ++ np ++ [.p 44, .m [.id v]] ++ r1)
    | _ =>
      -- (`every prime $p\equiv1\pmod4$ is …`: the variable of the congruence)
      match ts with
      | .id v :: .cmd e :: _ => if e == w!"equiv" then some ([.w w!"for", .w w!"every"] ++ np ++ [.p 44, .m [.id v]] ++ r1) else none
      | _ => none
  | some _ => none
  | none =>
    -- `Every Harshad number is a positive integer.`: a noun after `is a`, of an object
    -- that the sentence does not name (a variable of its own)
    let r2 ← kw [w!"is"] r1
    -- (or an adjective with a formula, `is $2$-colorable`)
    let _ ← kw [w!"a"] r2 <|> kw [w!"an"] r2 <|> (match r2 with
      | .m _ :: .p 45 :: .w _ :: _ => some r2
      | _ => none)
    if np.isEmpty then none
    let v : Codes := w!"ve"
    some ([.w w!"for", .w w!"every"] ++ np ++ [.m [.id v], .p 44, .m [.id v]] ++ r1)

/-- `Every NP has a NOUN …` as `For every NP $x$, $x$ has a NOUN …` (`Every bounded
sequence of real numbers has a convergent subsequence.`): the noun phrase's variable, or one
of its own. -/
def everyHasSent (cs : List Chunk) : Option (List Chunk) := do
  let r ← kw [w!"every"] cs
  let (np, r1) ← chunksUntil [w!"has"] r [] <|> chunksUntil [w!"contains"] r []
  let _ ← kw [w!"has"] r1 <|> kw [w!"contains"] r1
  if np.isEmpty then none
  -- (a formula after a preposition is a complement, `every countable subset of
  -- $\mathbb{R}$ has …`: the object has a variable of its own)
  let preps := [w!"of", w!"in", w!"on", w!"over", w!"to", w!"from", w!"with", w!"at", w!"by", w!"for"]
  let afterPrep : Bool := match np.reverse with
    | .m _ :: .w p :: _ => preps.contains p
    | _ => false
  if afterPrep then
    let v : Codes := w!"ve"
    return [.w w!"for", .w w!"every"] ++ np ++ [.m [.id v], .p 44, .m [.id v]] ++ r1
  match np.getLast? with
  | some (.m [.id v]) => some ([.w w!"for", .w w!"every"] ++ np ++ [.p 44, .m [.id v]] ++ r1)
  -- (a variable with a bound, `Every integer $n>1$ has …`)
  | some (.m (.id v :: t :: _)) =>
    if (Math.relOf t).isSome then some ([.w w!"for", .w w!"every"] ++ np ++ [.p 44, .m [.id v]] ++ r1)
    else
      let v : Codes := w!"ve"
      some ([.w w!"for", .w w!"every"] ++ np ++ [.m [.id v], .p 44, .m [.id v]] ++ r1)
  | _ =>
    let v : Codes := w!"ve"
    some ([.w w!"for", .w w!"every"] ++ np ++ [.m [.id v], .p 44, .m [.id v]] ++ r1)

/-- `[Then] CLAUSE if CLAUSE'.` as `If CLAUSE', then CLAUSE.`: a condition after the claim
(not `if and only if`, `only if`, `even if`). -/
def postIfSent (cs : List Chunk) : Option (List Chunk) := do
  let (cs, stop) : List Chunk × List Chunk := match cs.getLast? with
    | some (.p 46) => (cs.dropLast, [.p 46])
    | _ => (cs, [])
  let body := (kw [w!"then"] cs).getD cs
  let i ← (List.range body.length).find? fun i => match (body[i]? : Option Chunk) with
    | some (Chunk.w w) => w == w!"if" && i > 0 &&
      (match (body[i - 1]? : Option Chunk) with
        | some (Chunk.w p) => p != w!"only" && p != w!"even" && p != w!"and"
        | _ => true) &&
      (match (body[i + 1]? : Option Chunk) with
        | some (Chunk.w a) => a != w!"and"
        | _ => true)
    | _ => false
  let a := (body.take i).reverse.dropWhile (fun c => match c with | .p 44 => true | _ => false) |>.reverse
  let b := body.drop (i + 1)
  if a.isEmpty || b.isEmpty then none
  -- (one condition: no second `if`)
  if b.any (fun c => match c with | .w w => w == w!"if" | _ => false) then none
  -- (not a claim that binds variables of its own, which the condition may be about)
  let binding := [w!"there", w!"exists", w!"exist", w!"such", w!"some", w!"every", w!"all", w!"each", w!"any", w!"unique"]
  if a.any (fun c => match c with | .w w => binding.contains w | _ => false) then none
  some ([.w w!"if"] ++ b ++ [.p 44, .w w!"then"] ++ a ++ stop)

/-- `[Then] CLAUSE for $φ$.` with a condition `φ` of order relations (`for $0<k<p$`) as
`If $φ$, then CLAUSE.`: for every value of its new variables. -/
def postForSent (cs : List Chunk) : Option (List Chunk) := do
  let (cs, stop) : List Chunk × List Chunk := match cs.getLast? with
    | some (.p 46) => (cs.dropLast, [.p 46])
    | _ => (cs, [])
  let body := (kw [w!"then"] cs).getD cs
  let n := body.length
  if n < 3 then none
  let .w fw := body[n - 2]! | none
  if fw != w!"for" then none
  let .m ts := body[n - 1]! | none
  let c ← Math.parseFormula ts
  match c with
  | .chain _ rs =>
    if !(rs.all fun (rel, _) => rel == .lt || rel == .le || rel == .gt || rel == .ge || rel == .ne) then none
  | _ => none
  let a := (body.take (n - 2)).reverse.dropWhile (fun c => match c with | .p 44 => true | _ => false) |>.reverse
  if a.isEmpty then none
  -- (not a clause that binds variables of its own, which the condition may be about:
  -- `there exists $\delta>0$ such that … for $|x-1|<\delta$`)
  let binding := [w!"there", w!"exists", w!"exist", w!"such", w!"some", w!"every", w!"all", w!"each", w!"any", w!"unique"]
  if a.any (fun c => match c with | .w w => binding.contains w | _ => false) then none
  some ([.w w!"if", .m ts, .p 44, .w w!"then"] ++ a ++ stop)

/-- `Every bounded monotone sequence converges.`, `Every NP diverges`, `… vanishes …`, `…
divides $n$`: as `For every NP $v$, $v$ converges.` (a verb of the third person, without a
variable after the noun phrase: a fresh one). -/
def everyVerbSent (cs : List Chunk) : Option (List Chunk) := do
  let r ← kw [w!"every"] cs
  let verbs : List Codes := [w!"converges", w!"diverges", w!"vanishes", w!"divides", w!"satisfies",
    w!"attains", w!"admits", w!"lies", w!"belongs", w!"equals", w!"exceeds", w!"commutes"]
  let i ← (List.range r.length).find? fun i => match (r[i]? : Option Chunk) with
    | some (Chunk.w w) => verbs.contains w
    | _ => false
  let np := r.take i
  if np.isEmpty then none
  -- (`converges`, `diverges` as the text before reads them after a formula: `is convergent`,
  -- `is converging to $l$`)
  let tail : List Chunk := match r.drop i with
    | .w v :: .w t :: rest => if v == w!"converges" && t == w!"to" then .w w!"is" :: .w w!"converging" :: .w t :: rest else r.drop i
    | .w v :: rest =>
      let atEnd := match rest with | [] | .p _ :: _ => true | _ => false
      if (v == w!"converges" || v == w!"diverges") && atEnd then
        .w w!"is" :: .w (if v == w!"converges" then w!"convergent" else w!"divergent") :: rest
      else r.drop i
    | _ => r.drop i
  -- (a noun phrase of words, and possibly its variable at the end)
  if !(np.dropLast.all fun c => match c with | .w _ | .p 45 => true | _ => false) then none
  match np.getLast? with
  | some (.m [.id v]) => some ([.w w!"for", .w w!"every"] ++ np ++ [.p 44, .m [.id v]] ++ tail)
  | some (.w _) =>
    -- (a letter that the sentence does not use)
    let used (c : Codes) : Bool := cs.any fun ch => match ch with
      | .m ts => ts.contains (.id c)
      | _ => false
    let v ← [w!"x", w!"y", w!"z", w!"u", w!"w", w!"t", w!"s"].find? (!used ·)
    some ([.w w!"for", .w w!"every"] ++ np ++ [.m [.id v], .p 44, .m [.id v]] ++ tail)
  | _ => none

/-- `[Consequently,] [the functions] $\rho$, $\nu$, and $\eta$ are affine on $\mathcal C$.` as
`$\rho$ is affine on $\mathcal C$ and $\nu$ is … and $\eta$ is ….`: what is said of several
symbols is said of each. -/
def pluralSubjSent (cs : List Chunk) : Option (List Chunk) := do
  let (_, cs) := marker cs
  let cs := (kw [w!"the", w!"functions"] cs <|> kw [w!"the", w!"maps"] cs <|> kw [w!"the", w!"coefficients"] cs <|>
    kw [w!"the", w!"quantities"] cs).getD cs
  -- the symbols, separated by `,`, `and` and `, and`
  let rec subjects : Nat → List Chunk → List (List MTok) → Option (List (List MTok) × List Chunk)
    | 0, _, _ => none
    | f + 1, cs, acc =>
      match cs with
      | Chunk.m ts :: r =>
        let single := match Math.parseFormula ts with | some (.id _) => true | _ => false
        if !single then none else
        let acc := ts :: acc
        match r with
        | Chunk.p 44 :: Chunk.w a :: r' => if a == w!"and" then subjects f r' acc else none
        | Chunk.p 44 :: r' => subjects f r' acc
        | Chunk.w a :: r' =>
          if a == w!"and" then subjects f r' acc
          else if a == w!"are" then some (acc.reverse, r') else none
        | _ => none
      | _ => none
  let (subs, rest) ← subjects 8 cs []
  if subs.length < 2 then none
  let (body, stop) : List Chunk × List Chunk := match rest.getLast? with
    | some (Chunk.p 46) => (rest.dropLast, [Chunk.p 46])
    | _ => (rest, [])
  -- (one statement: no further clause, and no plural predicate about them together)
  if body.isEmpty || body.any (fun (c : Chunk) => match c with
      | Chunk.p _ => true
      | Chunk.w w => [w!"and", w!"or", w!"equal", w!"distinct", w!"disjoint", w!"independent", w!"the", w!"each",
          w!"mutually", w!"pairwise", w!"inverse", w!"inverses", w!"transposes"].contains w
      | _ => false) then none
  let parts := subs.map fun ts => [Chunk.m ts, Chunk.w w!"is"] ++ body
  some ((parts.intersperse [Chunk.w w!"and"]).flatten ++ stop)

/-- `… is ADJ, ADJ and ADJ.` as `… is ADJ and ADJ and ADJ.`: a list of adjectives with
commas, to the end of the sentence (words only, none of which starts another clause). -/
def adjCommaSent (cs : List Chunk) : Option (List Chunk) := do
  let isIs (c : Chunk) : Bool := match c with | Chunk.w w => w == w!"is" | _ => false
  let i ← (List.range cs.length).reverse.find? fun i => match cs[i]? with | some c => isIs c | none => false
  let rest := cs.drop (i + 1)
  let (body, stop) : List Chunk × List Chunk := match rest.getLast? with
    | some (Chunk.p 46) => (rest.dropLast, [Chunk.p 46])
    | _ => (rest, [])
  let isComma (c : Chunk) : Bool := match c with | Chunk.p 44 => true | _ => false
  let isW (c : Chunk) : Bool := match c with | Chunk.w _ => true | _ => false
  -- (a formula only before a hyphen, `$2$-regular`)
  let isHy (c : Chunk) : Bool := match c with | Chunk.p 45 => true | _ => false
  let okPairs := (body.zip (body.drop 1 ++ [Chunk.p 46])).all fun (c, next) =>
    isW c || isComma c || isHy c || (match c with | Chunk.m _ => isHy next | _ => false)
  if body.isEmpty || !okPairs || !body.any isComma then none
  let ws : List Codes := body.filterMap fun (c : Chunk) => match c with | Chunk.w w => some w | _ => none
  let stopWords := [w!"hence", w!"so", w!"where", w!"which", w!"since", w!"because", w!"as", w!"then", w!"but",
    w!"if", w!"while", w!"for", w!"with", w!"that", w!"a", w!"an", w!"the", w!"is", w!"are", w!"has", w!"we",
    w!"it", w!"there", w!"by", w!"or", w!"not"]
  if !ws.contains w!"and" || ws.any (fun w => stopWords.contains w) then none
  -- (each part has a word)
  if (match body.head? with | some c => isComma c | none => true) ||
      (match body.getLast? with | some c => isComma c | none => true) ||
      (body.zip (body.drop 1)).any (fun (a, b) => isComma a && isComma b) then none
  let ands : List Chunk := (body.zip (body.drop 1 ++ [Chunk.p 46])).filterMap fun (c, next) =>
    if isComma c then (match next with
      | Chunk.w w => if w == w!"and" then none else some (Chunk.w w!"and")
      | _ => none)
    else some c
  some (cs.take (i + 1) ++ ands ++ stop)

/-- `Let $M$ be the NOTION …`, `let $\varphi$ denote [the] NOTION`: for a sentence with no
other reading, the variable is the value of a notion of the vocabulary (`letBinder`). -/
def letTheSent (cs : List Chunk) : Option (List Chunk) :=
  -- `Let $\varphi$ denote Euler's totient function.`: a name without arguments, for the
  -- article (as `We write $\varphi$ for Euler's totient function.`)
  let named : Option (List Chunk) := match cs with
    | Chunk.w a :: Chunk.m v :: Chunk.w b :: rest =>
      if a == w!"let" && b == w!"denote" && !rest.isEmpty &&
          rest.all (fun c => match c with | Chunk.w _ | Chunk.p 46 | Chunk.p 45 => true | _ => false) then
        some ([Chunk.w w!"we", .w w!"write", .m v, .w w!"for"] ++ rest)
      else none
    | _ => none
  if named.isSome then named else
  let rec go : Nat → List Chunk → Bool → List Chunk → Option (List Chunk)
    | 0, _, _, _ => none
    | _ + 1, [], hit, acc => if hit then some acc.reverse else none
    | f + 1, Chunk.w a :: Chunk.m v :: Chunk.w b :: rest, hit, acc =>
      if a == w!"let" && (b == w!"be" || b == w!"denote") then
        match rest with
        | Chunk.w t :: rest' =>
          if t == w!"the" then go f rest' true ([Chunk.w w!"@the", .w w!"be", .m v, .w a] ++ acc)
          else if b == w!"denote" then go f rest true ([Chunk.w w!"@the", .w w!"be", .m v, .w a] ++ acc)
          else go f (Chunk.m v :: Chunk.w b :: rest) hit (Chunk.w a :: acc)
        | _ => go f (Chunk.m v :: Chunk.w b :: rest) hit (Chunk.w a :: acc)
      else go f (Chunk.m v :: Chunk.w b :: rest) hit (Chunk.w a :: acc)
    | f + 1, c :: rest, hit, acc => go f rest hit (c :: acc)
  go (cs.length + 1) cs false []

/-- A sentence: an assumption, a contradiction, or one of the other forms, possibly
ending in a contradiction. -/
def sentence0 (cs : List Chunk) : Option Sent :=
  match supposeSent cs <|> contradictionSent cs <|> organizeSent cs with
  | some s => some s
  | none =>
    match stripContradiction cs with
    | some cs' =>
      match sentenceCore cs' with
      | some (.claims topic binds cls) => some (.claimsContra topic binds cls)
      | _ => none
    | none => sentenceCore cs

/-- The condition of a notion as a statement: whatever is read as a claim (`for all
$x,y\in X$ there is an isometry $f\colon X\to X$ with $f(x)=y$`), its binders around its
clauses. -/
def claimCond (r : List Chunk) : Option NotionCond := do
  let r := optPunct 44 r
  let .claims _ binds cls ← sentenceCore r | none
  if cls.isEmpty || cls.any (fun c => !c.defs.isEmpty || !c.forDefs.isEmpty || !c.cites.isEmpty) then none
  let each := cls.map fun c => c.binds.foldr (fun b acc => Clause.under b acc) c.clause
  let body := match each with | [c] => c | cs => Clause.both cs
  some (.clause (binds.foldr (fun b acc => Clause.under b acc) body))

/-- A notion whose condition is a statement that is read as a claim, where the forms of
`notionCond` do not read it. -/
def notionDefWide (cs : List Chunk) : Option Sent :=
  let (_, cs) := marker cs
  match notionDefWith (fun r => notionCond r <|> claimCond r) cs with
  | some (.defNotion np name abbr cond noun) => some (.defNotion np name abbr cond noun)
  | _ => none

/-! ## The forms of a definition in words

An article names a notion in many ways: `A NP $x$ is called NAME if COND.`, `We say that
$x$ is NAME when COND.`, `If COND, then $x$ is said to be NAME.`, `A NP $x$ such that COND
is called a NAME.`, `A NAME is a NP $x$ such that COND.`, `A NP is NAME provided COND.`
(the subject without a variable: `it` in the condition). Each of them has a subject, a
name and a condition: the parts of a `DefForm`, which is read as `SUBJECT is called NAME if
COND.` A form without a verb that names (`is called`, `we say`, `is said to be`: `A NP $x$
is NAME if COND`, `A NAME is a NP …`) is a definition only in a definition. -/

/-- A definition of a notion in words, in the parts that every form of it has. -/
structure DefForm where
  /-- The subject: `[a] NOUN $x$` or `$x$`; of a subject without a variable (`a metric
  space`), the noun phrase with a variable of its own. -/
  subj : List Chunk
  /-- The name, as the sentence writes it: words and hyphens, `(ABBR)`. -/
  name : List Chunk
  /-- `is called a NAME`: the name of a kind of object. -/
  noun : Bool
  /-- The condition, with the full stop; empty when the sentence gives none. -/
  cond : List Chunk
  deriving Repr, Inhabited

namespace DefForm

/-- `SUBJECT is called [a] NAME if COND.` -/
def canon (f : DefForm) : List Chunk :=
  f.subj ++ [.w w!"is", .w w!"called"] ++ (if f.noun then [.w w!"a"] else []) ++ f.name ++ [.w w!"if"] ++ f.cond

/-- The verbs that name. -/
def verbs : List (List Codes) :=
  [[w!"is", w!"said", w!"to", w!"be"], [w!"are", w!"said", w!"to", w!"be"], [w!"will", w!"be", w!"said", w!"to", w!"be"],
   [w!"is", w!"called"], [w!"are", w!"called"], [w!"will", w!"be", w!"called"], [w!"shall", w!"be", w!"called"],
   [w!"is", w!"also", w!"called"], [w!"is", w!"then", w!"called"], [w!"is", w!"often", w!"called"],
   [w!"is", w!"usually", w!"called"], [w!"is", w!"simply", w!"called"], [w!"is", w!"termed"], [w!"are", w!"termed"],
   [w!"is", w!"known", w!"as"], [w!"are", w!"known", w!"as"], [w!"is", w!"referred", w!"to", w!"as"],
   [w!"is", w!"defined", w!"to", w!"be"], [w!"is", w!"then", w!"said", w!"to", w!"be"]]

/-- The words between the name and the condition. -/
def conns : List (List Codes) :=
  [[w!"if", w!"and", w!"only", w!"if"], [w!"if"], [w!"iff"], [w!"when"], [w!"whenever"], [w!"provided", w!"that"],
   [w!"provided"], [w!"in", w!"case"], [w!"precisely", w!"when"], [w!"exactly", w!"when"], [w!"precisely", w!"if"],
   [w!"exactly", w!"if"], [w!"as", w!"soon", w!"as"]]

/-- The words that begin the condition of a relative clause. -/
def rels : List (List Codes) :=
  [[w!"such", w!"that"], [w!"satisfying"], [w!"with"], [w!"for", w!"which"], [w!"so", w!"that"], [w!"having"],
   [w!"which", w!"satisfies"], [w!"that", w!"satisfies"], [w!"where"]]

/-- The first place of `cs` where one of the phrases begins (the earliest phrase of the list
there), and what follows the phrase. -/
def firstAt (pats : List (List Codes)) (cs : List Chunk) : Option (Nat × List Chunk) :=
  (List.range cs.length).findSome? fun i => pats.findSome? fun p => (kw p (cs.drop i)).map (i, ·)

/-- `[a|an] NAME [(ABBR)]`, and nothing else: is the name of a kind of object, and the name. -/
def nameOf (cs : List Chunk) : Option (Bool × List Chunk) :=
  let (noun, r) := match kw [w!"a"] cs <|> kw [w!"an"] cs with
    | some r => (true, r)
    | none => (false, cs)
  match nameAbbr r with
  | some (_, _, []) => some (noun, r)
  | _ => none

/-- Words that only lead to the definition. -/
def leads : List (List Codes) :=
  [[w!"recall", w!"that"], [w!"here"], [w!"further"], [w!"now"], [w!"more", w!"generally"], [w!"in", w!"this", w!"case"],
   [w!"as", w!"usual"], [w!"and"], [w!"in", w!"general"], [w!"accordingly"], [w!"henceforth"]]

def stripLead : Nat → List Chunk → List Chunk
  | 0, cs => cs
  | f + 1, cs =>
    match cs with
    | .w v :: .r .cite _ :: r => if v == w!"following" then stripLead f (optPunct 44 r) else cs
    | _ =>
      match leads.findSome? (kw · cs) with
      | some r => stripLead f (optPunct 44 r)
      | none => cs

/-- Without the citations of the sentence: `(cf. \cite{a})`, `, see \cite{a}`, `\cite{a}`. -/
def dropCites : Nat → List Chunk → List Chunk
  | 0, cs => cs
  | _, [] => []
  | f + 1, c :: cs =>
    let isCite (y : Chunk) : Bool := match y with | .r .cite _ => true | _ => false
    match c with
    | .p 40 =>
      let inner := cs.takeWhile fun y => match y with | .p 41 => false | _ => true
      if inner.length < cs.length && inner.length ≤ 8 && inner.any isCite then dropCites f (cs.drop (inner.length + 1))
      else c :: dropCites f cs
    | .p 44 =>
      match cs with
      | .w v :: y :: r => if (v == w!"see" || v == w!"cf") && isCite y then dropCites f r else c :: dropCites f cs
      | _ => c :: dropCites f cs
    | .w v =>
      match cs with
      | y :: r => if (v == w!"see" || v == w!"cf") && isCite y then dropCites f r else c :: dropCites f cs
      | _ => c :: dropCites f cs
    | _ => if isCite c then dropCites f cs else c :: dropCites f cs

/-- The singular of a plural by rule: `classes`, `families`, `maps`. -/
def singular (w : Codes) : Option Codes :=
  match w.reverse with
  | 115 :: 101 :: 105 :: r => some ((121 :: r).reverse)
  | 115 :: 101 :: 115 :: 115 :: r => some ((115 :: 115 :: r).reverse)
  | 115 :: 101 :: 120 :: r => some ((120 :: r).reverse)
  | 115 :: 101 :: 104 :: r => some ((104 :: r).reverse)
  | 115 :: 115 :: _ => none
  | 115 :: r => if r.length < 3 then none else some r.reverse
  | _ => none

/-- A sentence without the adverbs inside its verb: `is then called`, `will also be said to
be`. -/
def dropAdverbs : List Chunk → List Chunk
  | .w a :: .w b :: .w c :: r =>
    if [w!"is", w!"are", w!"be", w!"will", w!"shall"].contains a &&
        [w!"then", w!"also", w!"often", w!"usually", w!"simply", w!"sometimes", w!"commonly", w!"henceforth", w!"thus", w!"now"].contains b &&
        [w!"called", w!"said", w!"termed", w!"be", w!"known", w!"referred"].contains c
    then .w a :: dropAdverbs (.w c :: r) else .w a :: dropAdverbs (.w b :: .w c :: r)
  | c :: r => c :: dropAdverbs r
  | [] => []

/-- A letter that the sentence does not use. -/
def freshVar (cs : List Chunk) : Codes :=
  let used : List Codes := cs.flatMap fun c => match c with
    | .m ts | .d ts _ => ts.filterMap fun t => match t with | .id v => some v | _ => none
    | _ => []
  ([w!"X", w!"Y", w!"Z", w!"W", w!"V", w!"U", w!"T", w!"S", w!"Q", w!"P"].find? (!used.contains ·)).getD w!"X"

/-- The words at which the noun phrase after `its` ends. -/
def itsStops : List Codes :=
  [w!"is", w!"are", w!"has", w!"have", w!"acts", w!"act", w!"satisfies", w!"satisfy", w!"coincides", w!"equals",
   w!"contains", w!"exists", w!"converges", w!"vanishes", w!"lies", w!"belongs", w!"admits", w!"does", w!"can",
   w!"and", w!"or", w!"if", w!"of", w!"in", w!"on", w!"with", w!"for", w!"to", w!"its", w!"it"]

/-- `it` as the variable of the subject, `its WORDS` as `the WORDS of` it. -/
def resolveIt (v : Codes) : Nat → List Chunk → List Chunk
  | 0, cs => cs
  | _, [] => []
  | f + 1, .w w :: cs =>
    if w == w!"it" then .m [.id v] :: resolveIt v f cs
    else if w == w!"its" then
      let ws := cs.takeWhile fun c => match c with
        | .w u => !itsStops.contains u
        | .p 45 => true
        | _ => false
      if ws.isEmpty then .w w :: resolveIt v f cs
      else [.w w!"the"] ++ ws ++ [.w w!"of", .m [.id v]] ++ resolveIt v f (cs.drop ws.length)
    else .w w :: resolveIt v f cs
  | f + 1, c :: cs => c :: resolveIt v f cs

/-- The subject of a definition, where `cs` is nothing else: `[a|an] NOUN $x$`, `$x$`; or
`[a|an|the|such a|this|any|every] NOUN`, without a variable (then: the variable it is given). -/
def subjectOf (fresh : Codes) (cs : List Chunk) : Option (List Chunk × Option Codes) :=
  let art := (kw [w!"a"] cs <|> kw [w!"an"] cs).getD cs
  match nounVar art with
  | some (np, []) => some (np, none)
  | _ =>
    let r := ([[w!"such", w!"a"], [w!"such", w!"an"], [w!"a"], [w!"an"], [w!"the"], [w!"this"], [w!"any"], [w!"every"]].findSome?
      (kw · cs)).getD cs
    let words := r.all fun c => match c with
      | .w v => !notionStops.contains v
      | .p 45 => true
      | _ => false
    if r.isEmpty || !words || r.length > 5 then none else some (r ++ [.m [.id fresh]], some fresh)

/-- The forms of the sentence as a definition, the likeliest first. `inDef`: the sentence is
in a definition, where `A NP $x$ is NAME if COND` and `A NAME is a NP $x$ such that COND`
define too. -/
def forms (inDef : Bool) (cs0 : List Chunk) : List DefForm :=
  let (_, cs) := marker cs0
  let cs := dropAdverbs (dropCites (cs.length + 1) (stripLead 4 cs))
  let fresh := freshVar cs
  let noStop (r : List Chunk) : List Chunk := match r.getLast? with
    | some (.p 46) => r.dropLast
    | _ => r
  let withIt (v : Option Codes) (cond : List Chunk) : List Chunk := match v with
    | some v => resolveIt v (cond.length + 1) cond
    | none => cond
  -- `We call SUBJECT NAME if COND.`
  let weCall : Option DefForm := do
    let r ← [[w!"we", w!"call"], [w!"we", w!"will", w!"call"], [w!"we", w!"shall", w!"call"], [w!"let", w!"us", w!"call"]].findSome? (kw · cs)
    let (np, r1) ← nounVar ((kw [w!"a"] r <|> kw [w!"an"] r).getD r)
    let (j, r2) ← firstAt conns r1
    let (noun, name) ← nameOf (r1.take j)
    some { subj := np, name, noun, cond := r2 }
  -- the sentence after `We say that`
  let said : Option (List Chunk) := [[w!"we", w!"say", w!"that"], [w!"we", w!"say"], [w!"we", w!"will", w!"say", w!"that"],
    [w!"we", w!"shall", w!"say", w!"that"], [w!"one", w!"says", w!"that"]].findSome? (kw · cs)
  let body := said.getD cs
  -- `BEFORE is called NAME …`, with the verb that names; or, after `We say that` and in a
  -- definition, `BEFORE is NAME …`
  let atVerb (pats : List (List Codes)) : List DefForm :=
    match firstAt pats body with
    | none => []
    | some (i, after) =>
      let before := body.take i
      -- `SUBJECT is called NAME if COND.`; without a condition last (the name alone)
      let plain : List DefForm := match subjectOf fresh before with
        | none => []
        | some (np, v) =>
          (match firstAt conns after with
            | some (j, r2) => (match nameOf (after.take j) with
              | some (noun, name) => [{ subj := np, name, noun, cond := withIt v r2 }]
              | none => [])
            | none => []) ++
          (match nameOf (noStop after) with
            | some (noun, name) => [{ subj := np, name, noun, cond := [] }]
            | none => [])
      -- `A NP $x$ such that COND is called [a] NAME.`
      let relative : List DefForm := (do
        let (np, r) ← nounVar ((kw [w!"a"] before <|> kw [w!"an"] before).getD before)
        let r1 ← rels.findSome? (kw · (optPunct 44 r))
        if r1.isEmpty then none
        let (noun, name) ← nameOf (noStop after)
        some ({ subj := np, name, noun, cond := r1 ++ [Chunk.p 46] } : DefForm)).toList
      plain.take 1 ++ relative ++ plain.drop 1
  -- `If COND, [then] [we say that] SUBJECT is called NAME.` (`is NAME`, after `we say that`
  -- and in a definition)
  let condFirst : List DefForm := (do
    let r ← [[w!"if"], [w!"when"], [w!"whenever"]].findSome? (kw · cs)
    -- (the clause that names, after the last comma that leaves one)
    (List.range r.length).reverse.findSome? fun k =>
      match (r[k]? : Option Chunk) with
      | some (Chunk.p 44) =>
        if k == 0 then none else
        let s := r.drop (k + 1)
        let s := (kw [w!"then"] s).getD s
        let (s, weSay) := match [[w!"we", w!"say", w!"that"], [w!"we", w!"say"]].findSome? (kw · s) with
          | some s' => (s', true)
          | none => (s, false)
        match firstAt verbs s <|> (if weSay || inDef then firstAt [[w!"is"]] s else none) with
        | none => none
        | some (i, after) =>
          match subjectOf fresh (s.take i), nameOf (noStop after) with
          | some (np, v), some (noun, name) =>
            let cond := r.take k
            -- (`If a group $G$ is abelian, then $G$ is called NAME`: the subject is the noun
            -- phrase of the condition)
            let (np, cond) : List Chunk × List Chunk := match np with
              | [Chunk.m [.id x]] =>
                ((List.range cond.length).findSome? fun i =>
                  match kw [w!"a"] (cond.drop i) <|> kw [w!"an"] (cond.drop i) with
                  | some r1 => match nounVar r1 with
                    | some (np', r2) =>
                      if np'.length ≥ 2 && (np'.getLast?.any fun c => match c with | Chunk.m [.id y] => y == x | _ => false)
                      then some (np', cond.take i ++ [Chunk.m [.id x]] ++ r2) else none
                    | none => none
                  | none => none).getD (np, cond)
              | _ => (np, cond)
            some ({ subj := np, name, noun, cond := withIt v (cond ++ [Chunk.p 46]) } : DefForm)
          | _, _ => none
      | _ => none).toList
  let named := atVerb verbs
  let byIs := if said.isSome || inDef then atVerb [[w!"is"]] else []
  -- `A NAME is a NP $x$ such that COND.` (`By a NAME we mean a NP …`, `We define a NAME to be
  -- a NP …`)
  let nounDef : Option DefForm := do
    let (r, sure) ← ((kw [w!"by"] cs).map (·, true)) <|> ((kw [w!"we", w!"define"] cs).map (·, true)) <|> some (cs, false)
    if !(sure || inDef) then none
    let r ← kw [w!"a"] r <|> kw [w!"an"] r
    let (i, after) ← firstAt (if sure then [[w!"we", w!"mean", w!"a"], [w!"we", w!"mean", w!"an"], [w!"to", w!"be", w!"a"],
      [w!"to", w!"be", w!"an"], [w!"as", w!"a"], [w!"as", w!"an"]] else [[w!"is", w!"a"], [w!"is", w!"an"]]) r
    let (_, name) ← nameOf (r.take i)
    let (np, r1) ← nounVar after
    let r2 ← rels.findSome? (kw · (optPunct 44 r1))
    some { subj := np, name, noun := true, cond := r2 }
  weCall.toList ++ condFirst ++ named ++ byIs ++ nounDef.toList

/-- What a sentence that names a notion says of it, where its condition (or its subject) is
not read: the words of the kind of object that it is about (`geodesic space`; none, when
the subject is a formula alone), whether they follow an article (`A NP`, `the NP`; or are a plural),
the name, and whether the name is of a kind of object (`is called a NAME`). -/
structure Shape where
  genus : List Codes
  indefinite : Bool
  name : List Codes
  noun : Bool
  deriving Repr, Inhabited

/-- Words that are not part of a name. -/
def nameStops : List Codes :=
  notionStops ++ [w!"provided", w!"iff", w!"precisely", w!"exactly", w!"denoted", w!"written", w!"which", w!"that",
    w!"where", w!"see", w!"cf", w!"respectively", w!"resp", w!"over", w!"between", w!"under", w!"it", w!"its", w!"this",
    w!"these", w!"such", w!"we", w!"also", w!"simply", w!"called", w!"said", w!"has", w!"have", w!"be", w!"following",
    w!"whose", w!"their", w!"his", w!"her", w!"our", w!"those", w!"both", w!"will", w!"shall", w!"then"]

/-- The shapes of the sentence as one that names a notion (`… SUBJECT is called [a] NAME …`,
`we call SUBJECT [a] NAME`), read more freely than `forms`: the subject after the last comma
before the verb, `[a|an|the|any|every|such a] WORDS [$x$] [of …]`; the name, up to the
first word that is not of a name. -/
def shapes (cs0 : List Chunk) : List Shape :=
  let (_, cs) := marker cs0
  let cs := dropAdverbs (dropCites (cs.length + 1) (stripLead 4 cs))
  let dets : List (List Codes × Bool) :=
    [([w!"such", w!"a"], true), ([w!"such", w!"an"], true), ([w!"a"], true), ([w!"an"], true), ([w!"any"], true),
     ([w!"every"], true), ([w!"each"], true), ([w!"the"], true), ([w!"this"], true)]
  -- the words of the kind of object at the start of a subject, and whether they introduce one
  let genusOf (s : List Chunk) : Option (List Codes × Bool × List Chunk) :=
    let (s, indef) := match dets.findSome? (fun (d, i) => (kw d s).map (·, i)) with
      | some r => r
      | none => (s, false)
    let ws := s.takeWhile fun c => match c with
      | .w v => !nameStops.contains v
      | .p 45 => true
      | _ => false
    let words := ws.map fun c => match c with | .w v => v | _ => w!"-"
    if (words.filter (· != w!"-")).length > 4 || words.head? == some w!"-" || words.getLast? == some w!"-" then none
    else some (words, indef, s.drop ws.length)
  -- the name at the start of `r`
  let nameAt (r : List Chunk) : Option (Bool × List Codes) :=
    let (noun, r) := match kw [w!"a"] r <|> kw [w!"an"] r with
      | some r' => (true, r')
      | none => (false, r)
    let ws := r.takeWhile fun c => match c with
      | .w v => !nameStops.contains v
      | .p 45 => true
      | _ => false
    let name := ws.map fun c => match c with | .w v => v | _ => w!"-"
    let n := (name.filter (· != w!"-")).length
    if n == 0 || n > 5 || name.head? == some w!"-" || name.getLast? == some w!"-" then none else
    -- (a formula right after the words belongs to the name: `$n$-th syzygy`, not read)
    match r.drop ws.length with
    | .m _ :: _ => none
    | .p 45 :: _ => none
    | _ => some (noun, name)
  let afterLast (before : List Chunk) : List Chunk :=
    let k := (List.range before.length).reverse.find? fun i => match (before[i]? : Option Chunk) with
      | some (Chunk.p 44) | some (Chunk.p 59) | some (Chunk.p 58) => true
      | some (Chunk.w v) => v == w!"then" || v == w!"that" || v == w!"and"
      | _ => false
    match k with
    | some i => before.drop (i + 1)
    | none => before
  -- (each verb that names: `…, and $B$ is said to be NAME' if …`)
  let byVerb : List Shape := (List.range cs.length).filterMap fun i => do
    let after ← verbs.findSome? fun p => kw p (cs.drop i)
    let subj := afterLast (cs.take i)
    let (genus, indef, rest) ← genusOf subj
    -- (`Finite-dimensional algebras $A$ with … are called …`: the objects of the plural)
    let plural := (kw [w!"are"] (cs.drop i)).isSome
    let (genus, indef) : List Codes × Bool :=
      if !plural then (genus, indef) else
      match genus.getLast? with
      | some w => (match singular w with
          | some w' => (genus.dropLast ++ [w'], true)
          | none => (genus, indef))
      | none => (genus, indef)
    -- (after the words: the variable, and what is said of it; no second formula alone)
    let okRest := match rest with
      | [] => !genus.isEmpty
      | [.m _] => true
      | .m _ :: .w v :: _ => [w!"of", w!"in", w!"on", w!"over", w!"with", w!"such", w!"satisfying", w!"from", w!"for",
          w!"at", w!"whose", w!"which", w!"that"].contains v
      | .w v :: _ => !genus.isEmpty && [w!"of", w!"in", w!"on", w!"over", w!"with", w!"such", w!"satisfying", w!"whose"].contains v
      | _ => false
    if !okRest then none
    let (noun, name) ← nameAt after
    -- (`These maps are called pullbacks`: the name of a kind of object, in the plural)
    let (noun, name) : Bool × List Codes :=
      if !plural || noun then (noun, name) else
      match name.getLast? >>= singular with
      | some w' => if (name.getLast?.any fun w => w.reverse.take 3 == [115, 117, 111] || w.reverse.take 2 == [115, 117]) then (noun, name)
          else (true, name.dropLast ++ [w'])
      | none => (noun, name)
    some ({ genus, indefinite := indef, name, noun } : Shape)
  let byCall : List Shape := (do
    let r ← [[w!"we", w!"call"], [w!"we", w!"will", w!"call"], [w!"we", w!"shall", w!"call"]].findSome? (kw · cs)
    let (genus, indef, rest) ← genusOf r
    match rest with
    | .m _ :: r1 =>
      let (noun, name) ← nameAt r1
      some ({ genus, indefinite := indef, name, noun } : Shape)
    | _ => none).toList
  byVerb ++ byCall

end DefForm

/-- A sentence that one of the forms of a definition reads, with its condition: the reading
of a sentence that is otherwise not read, or whose reading does not compile. -/
def defAlt (s : Sentence) : Option Sent := do
  if s.ctx.kind == .proof then none
  let cs ← chunks (s.toks.length + 1) s.toks []
  let inDef := match s.ctx.kind with | .result e => e.take 3 == w!"def" | _ => false
  (DefForm.forms inDef cs).findSome? fun f => if f.cond.isEmpty then none else notionDefWide f.canon

/-- A sentence that one of the forms of a definition reads, with its condition. -/
def defSentence (inDef : Bool) (cs : List Chunk) : Option Sent :=
  (DefForm.forms inDef cs).findSome? fun f => if f.cond.isEmpty then none else notionDefWide f.canon

/-- `Let $x$, $y$ and $z$ be as in Theorem~\ref{t}.`, `Let $x,y$ be as in \cref{t}.` -/
def asInSent (cs : List Chunk) : Option Sent := do
  let r ← kw [w!"let"] cs
  -- the letters: `$x$, $y$, and $z$`, `$x,y,z$`
  let letters (ts : List MTok) : Option (List Codes) :=
    ((Math.commaParts (ts.length + 1) 0 [] ts []).filter (!·.isEmpty)).mapM fun p =>
      match Math.parseFormula p with
      | some (.id v) => some v
      | _ => none
  let rec vars : Nat → List Chunk → List Codes → Option (List Codes × List Chunk)
    | 0, _, _ => none
    | f + 1, cs, acc => do
      let (ts, r1) ← mathChunk cs
      let vs ← letters ts
      let acc := acc ++ vs
      match r1 with
      | .p 44 :: .w a :: rest@(.m _ :: _) => if a == w!"and" then vars f rest acc else none
      | .p 44 :: rest@(.m _ :: _) => vars f rest acc
      | .w a :: rest@(.m _ :: _) => if a == w!"and" then vars f rest acc else none
      | _ => some (acc, r1)
  let (vs, r1) ← vars 8 r []
  let r2 ← kw [w!"be", w!"as", w!"in"] r1
  let (l, r3) ← cite r2 <|> (match r2 with
    | .r .ref l :: rest => some (l, rest)
    | _ => none)
  if vs.isEmpty || !isEnd r3 then none
  some (.asIn vs l)

/-- `[In particular,] the NOUN $x$ is …`, `the WORDS $x$ has …`: the clause about `x`, with what
`the NOUN` says of it (`x` is a NOUN) as a part of what is stated. -/
def theNounSubjSent (cs : List Chunk) : Option Sent := do
  let (topic, cs) := marker cs
  let r ← kw [w!"the"] cs
  let ws := r.takeWhile fun c => match c with
    | .w w => !notionStops.contains w
    | .p 45 => true
    | _ => false
  let nw := (ws.filter fun c => match c with | .w _ => true | _ => false).length
  if nw == 0 || nw > 4 then none
  let rest := r.drop ws.length
  let (ts, r1) ← mathChunk rest
  -- (a symbol: a letter, a command, with indices)
  let single := match Math.parseFormula ts with
    | some (.id _) | some (.sub (.id _) _) | some (.sup (.id _) _) => true
    | _ => false
  if !single then none
  let v ← r1.head?
  if !(match v with
      | .w w => [w!"is", w!"are", w!"has", w!"have", w!"contains", w!"satisfies", w!"admits", w!"lies", w!"belongs", w!"does"].contains w
      | _ => false) then none
  let (pre, e1) ← clause ([.m ts, .w w!"is", .w w!"a"] ++ ws ++ [.p 46])
  if !isEnd e1 then none
  let (c, e2) ← andClauses ([.m ts] ++ r1)
  if !isEnd e2 then none
  some (.claims topic [] [{ cites := [], clause := .both [pre, c] }])

/-- `Neither $A$ nor $B$ is REST.`: `$A$ is not REST` and `$B$ is not REST`. -/
def neitherNorSent (cs : List Chunk) : Option Sent := do
  let (topic, cs) := marker cs
  let r ← kw [w!"neither"] cs
  let i ← r.findIdx? fun c => match c with | .w w => w == w!"nor" | _ => false
  let a := r.take i
  let r1 := r.drop (i + 1)
  let j ← r1.findIdx? fun c => match c with | .w w => w == w!"is" || w == w!"are" | _ => false
  let b := r1.take j
  if a.isEmpty || b.isEmpty then none
  let rest := r1.drop (j + 1)
  if (kw [w!"not"] rest).isSome then none
  let (c1, e1) ← clause (a ++ [.w w!"is", .w w!"not"] ++ rest)
  let (c2, e2) ← clause (b ++ [.w w!"is", .w w!"not"] ++ rest)
  if !isEnd e1 || !isEnd e2 then none
  some (.claims topic [] [{ cites := [], clause := .both [c1, c2] }])

/-- `We denote by $Z$ the WORDS.`, `Let $Z$ denote the WORDS.`, `The WORDS is denoted by $Z$.`:
as `Let $Z$ be the WORDS.` (a symbol for an object that the words name). -/
def denoteAsLet (cs : List Chunk) : Option (List Chunk) :=
  (do
    let r ← kw [w!"we", w!"denote", w!"by"] cs <|> kw [w!"denote", w!"by"] cs <|>
      kw [w!"let", w!"us", w!"denote", w!"by"] cs <|> kw [w!"we", w!"will", w!"denote", w!"by"] cs
    let (ts, r1) ← mathChunk r
    let r2 ← kw [w!"the"] r1
    some ([.w w!"let", .m ts, .w w!"be", .w w!"the"] ++ r2)) <|>
  (do
    let r ← kw [w!"let"] cs
    let (ts, r1) ← mathChunk r
    let r2 ← kw [w!"denote", w!"the"] r1
    some ([.w w!"let", .m ts, .w w!"be", .w w!"the"] ++ r2)) <|>
  -- `We denote the spectrum of $M$ by $\sigma(M)$.`
  (do
    let r ← kw [w!"we", w!"denote", w!"the"] cs <|> kw [w!"denote", w!"the"] cs <|> kw [w!"we", w!"will", w!"denote", w!"the"] cs
    let i ← (List.range r.length).reverse.find? fun i => (match (r[i]? : Option Chunk) with
      | some (Chunk.w b) => b == w!"by"
      | _ => false)
    let pre := r.take i
    let (ts, r2) ← mathChunk (r.drop (i + 1))
    if pre.isEmpty || !isEnd r2 || pre.any (fun c => match c with | .p 44 | .p 46 => true | _ => false) then none
    some ([.w w!"let", .m ts, .w w!"be", .w w!"the"] ++ pre ++ [.p 46])) <|>
  (do
    let r ← kw [w!"the"] cs
    let i ← r.findIdx? fun c => match c with | .w w => w == w!"denoted" | _ => false
    if i < 2 then none
    let pre := r.take (i - 1)
    let verb := r[i - 1]?
    if !(match verb with | some (Chunk.w w) => w == w!"is" | _ => false) then none
    let r1 ← kw [w!"by"] (r.drop (i + 1))
    let (ts, r2) ← mathChunk r1
    if !isEnd r2 then none
    if pre.any (fun c => match c with | .p 44 | .p 46 => true | _ => false) then none
    some ([.w w!"let", .m ts, .w w!"be", .w w!"the"] ++ pre ++ [.p 46]))

def sentence1 (cs : List Chunk) : Option Sent :=
  -- (`Then CLAUSE if CLAUSE'.`: the condition first, before the words after `is` would take it)
  let postIf : Option Sent := if (kw [w!"then"] cs).isSome then postIfSent cs >>= sentence0 else none
  -- (`Then CLAUSE for $0<k<p$.`, a clause in words: the condition first; a formula keeps
  -- `for` as its own condition)
  let postIf := postIf <|> (do
    let r ← kw [w!"then"] cs
    let words := r.any fun c => match c with | .w w => w != w!"for" | _ => false
    if !words then none
    postForSent cs >>= sentence0)
  match postIf with
  | some s => some s
  | none =>
  -- (a notion with a statement as its condition, where the sentence is otherwise only known
  -- to be a definition, or not read)
  let s0 := match sentence0 cs with
    | some (.notionSubject np) => (notionDefWide cs).orElse fun _ => some (.notionSubject np)
    | none => notionDefWide cs <|> asInSent cs <|> neitherNorSent cs <|> theNounSubjSent cs <|>
      (denoteAsLet cs >>= fun cs' => sentence0 cs' <|> (letTheSent cs' >>= sentence0))
    | s => s
  match s0 with
  | some s => some s
  | none =>
    -- `INFORMAL, that is, FORMAL`: the formal restatement (a sentence of its own)
    match skipThatIs cs >>= sentence0 with
    | some s => some s
    | none =>
    -- (a sentence through a list, as one sentence; `Every NP satisfies` several statements)
    let flat := (joinList cs).getD cs
    let (_, body) := marker flat
    -- (`If $φ$, then every NP satisfies …`: the same after the hypothesis)
    let afterIf : Option (List Chunk) := do
      let r ← kw [w!"if"] body
      match r with
      | .m ts :: r1 =>
        let r2 ← punct 44 r1
        let r3 := (kw [w!"then"] r2).getD r2
        let cs' ← everySatisfies r3
        some ([.w w!"if", .m ts, .p 44, .w w!"then"] ++ cs')
      | _ => none
    match everySatisfies body <|> afterIf with
    | some cs' => sentence0 cs'
    | none =>
      match (if (joinList cs).isSome then sentence0 flat else none) with
      | some s => some s
      | none =>
        match everyIsSent body >>= sentence0 with
        | some s => some s
        | none =>
        match everyHasSent body >>= sentence0 with
        | some s => some s
        | none =>
        match everyVerbSent body >>= sentence0 with
        | some s => some s
        | none =>
        match postIfSent cs >>= sentence0 with
        | some s => some s
        | none =>
        match postForSent cs >>= sentence0 with
        | some s => some s
        | none =>
          match adjCommaSent cs >>= sentence0 with
          | some s => some s
          | none =>
            match letTheSent cs >>= sentence0 with
            | some s => some s
            | none => pluralSubjSent cs >>= sentence0

/-- `Sylow $p$-subgroup[s] [of $G$]` as `subgroup[s] [of $G$] with $p$ as Sylow prime`: the noun
`subgroup` with its complement, and the modifier that says it is a Sylow `p`-subgroup of it
(not after `number of`, a notion of its own). -/
def sylowForms : Nat → List Chunk → List Chunk → List Chunk
  | 0, _, cs => cs
  | f + 1, prev, cs =>
    match cs with
    | .w s :: .m p :: .p 45 :: .w n :: rest =>
      let afterNumber := match prev with
        | .w o :: .w nb :: _ => o == w!"of" && nb == w!"number"
        | _ => false
      if lower s == w!"sylow" && (n == w!"subgroup" || n == w!"subgroups") && !afterNumber then
        -- (a variable after the noun, `Sylow $p$-subgroup $P$ of $G$`, stays there)
        let (var, rest) : List Chunk × List Chunk := match rest with
          | .m v :: .w o :: r => if o == w!"of" then ([.m v], .w o :: r) else ([], rest)
          | _ => ([], rest)
        let (comp, rest') : List Chunk × List Chunk := match rest with
          | .w o :: .m x :: r => if o == w!"of" then ([.w o, .m x], r) else ([], rest)
          | _ => ([], rest)
        let out : List Chunk := (.w n :: var ++ comp) ++ [.w w!"with", .m p, .w w!"as", .w w!"sylow", .w w!"prime"]
        out ++ sylowForms f (out.reverse ++ prev) rest'
      else .w s :: sylowForms f (.w s :: prev) (.m p :: .p 45 :: .w n :: rest)
    | c :: rest => c :: sylowForms f (c :: prev) rest
    | [] => []

/-- `in which every chain has an upper bound` (the hypothesis of Zorn's lemma) as the modifier
`with chains bounded above`: words that do not end the noun phrase at `has`. -/
def chainForms : Nat → List Chunk → List Chunk
  | 0, cs => cs
  | f + 1, cs =>
    match cs with
    | .w a :: .w b :: .w c :: .w d :: .w e :: .w g :: .w h :: .w i :: rest =>
      if [a, b, c, d, e, g, h, i] == [w!"in", w!"which", w!"every", w!"chain", w!"has", w!"an", w!"upper", w!"bound"] then
        [.w w!"with", .w w!"chains", .w w!"bounded", .w w!"above"] ++ chainForms f rest
      else .w a :: chainForms f (.w b :: .w c :: .w d :: .w e :: .w g :: .w h :: .w i :: rest)
    | c :: rest => c :: chainForms f rest
    | [] => []

/-- `the symmetric group $S_n$`, `the alternating group $A_n$`, `the cyclic group $C_n$`: the
group with its standard name, as `the symmetric group of degree $n$` (`of order $n$` for the
cyclic group). Only the letter of that group's name is read so. -/
def namedGroupForms : Nat → List Chunk → List Chunk
  | 0, cs => cs
  | f + 1, cs =>
    match cs with
    | .w a :: .w g :: .m ts :: rest =>
      let idx : Option (Codes × List MTok) := match ts with
        | .id k :: .sym 95 :: .lb :: r => if r.getLast? == some .rb then some (k, r.dropLast) else none
        | [.id k, .sym 95, t] => some (k, [t])
        | _ => none
      let named : Option (List Chunk) := do
        let (k, x) ← idx
        if g != w!"group" || x.isEmpty then none
        if a == w!"symmetric" && k == [83] then some [.w a, .w g, .w w!"of", .w w!"degree", .m x]
        else if a == w!"alternating" && k == [65] then some [.w a, .w g, .w w!"of", .w w!"degree", .m x]
        else if a == w!"cyclic" && k == [67] then some [.w a, .w g, .w w!"of", .w w!"order", .m x]
        else none
      match named with
      | some n => n ++ namedGroupForms f rest
      | none => .w a :: namedGroupForms f (.w g :: .m ts :: rest)
    | c :: rest => c :: namedGroupForms f rest
    | [] => []

/-- A sentence; or, of `INFORMAL, that is, FORMAL`, the formal restatement read with the
forms that rewrite a sentence (`…, that is, if $φ$, then every NP satisfies …`). -/
def sentence (cs : List Chunk) : Option Sent :=
  let cs := if cs.any (fun c => match c with | .w s => s == w!"group" | _ => false) then
    namedGroupForms (cs.length + 1) cs else cs
  -- (`Let $a\in G$ have order $n$`, read `Let $a\in G$ are of order $n$` by the forms of `have`:
  -- `be of order $n$`)
  let cs : List Chunk := match cs with
    | .w l :: .m x :: .w a :: .w o :: rest =>
      if lower l == w!"let" && a == w!"are" && o == w!"of" then Chunk.w l :: Chunk.m x :: Chunk.w w!"be" :: Chunk.w o :: rest else cs
    | _ => cs
  let cs := if cs.any (fun c => match c with | .w s => lower s == w!"sylow" | _ => false) then
    sylowForms (cs.length + 1) [] cs else cs
  let cs := if cs.any (fun c => match c with | .w s => s == w!"chain" | _ => false) then
    chainForms (cs.length + 1) cs else cs
  match sentence1 cs with
  | some s => some s
  | none => skipThatIs cs >>= sentence1

/-- `[We] let $L$ denote|be the WORDS [of NP [and|of NP]]`, `[we] write $L$ for the WORDS …`,
`[we] denote by $L$ the WORDS …`: a symbol for a quantity that the article does not
define (`Sent.undefined`). Each noun phrase of an argument ends with its variable
(`a graph $G$`); the words before the first of them name the quantity. -/
def undefinedSent (cs : List Chunk) : Option Sent := do
  let cs := (kw [w!"we"] cs).getD cs
  let (lhs, r) ←
    (do
      let r ← kw [w!"let"] cs
      let (s, r1) ← formula r
      let r2 ← kw [w!"denote"] r1 <|> kw [w!"be"] r1
      some (s, r2)) <|>
    (do
      let r ← kw [w!"write"] cs
      let (s, r1) ← formula r
      let r2 ← kw [w!"for"] r1
      some (s, r2)) <|>
    (do
      let r ← kw [w!"denote", w!"by"] cs
      let (s, r1) ← formula r
      some (s, r1))
  let r ← kw [w!"the"] r
  -- the noun phrases of the arguments: `[a|an|the] WORDS $x$`, joined by `and`, `of` or commas
  let rec argsOf : Nat → List Chunk → List (List Chunk) → Option (List (List Chunk))
    | 0, _, _ => none
    | f + 1, cs, acc =>
      let cs := (kw [w!"a"] cs <|> kw [w!"an"] cs <|> kw [w!"the"] cs).getD cs
      let ws := cs.takeWhile fun c => match c with | .w w => w != w!"of" && w != w!"and" | _ => false
      -- (`graphs $G$ and $H$`: the noun of the phrase before)
      let noun : List Chunk := if !ws.isEmpty then ws else
        match acc.head? with
        | some np => np.dropLast
        | none => []
      match cs.drop ws.length with
      | .m ts :: rest =>
        if noun.isEmpty then none else
        let acc := (noun ++ [.m ts]) :: acc
        if isEnd rest then some acc.reverse else
        match (punct 44 rest >>= kw [w!"and"]) <|> kw [w!"and"] rest <|> kw [w!"of"] rest <|> punct 44 rest with
        | some rest' => argsOf f rest' acc
        | none => none
      | _ => none
  -- the words of the name: up to an `of` after which the rest is the arguments (the last
  -- such `of`: `the number of vertices of a graph $G$`), or up to the end
  let ws := r.takeWhile fun c => match c with | .w _ => true | _ => false
  let words := ws.filterMap fun c => match c with | .w w => some w | _ => none
  if words.isEmpty then none else
  if isEnd (r.drop ws.length) then
    if words.contains w!"of" then none else some (.undefined lhs words [])
  else
    let cuts := ((List.range words.length).filter fun i => words[i]? == some w!"of" && i > 0).reverse
    cuts.findSome? fun i =>
      (argsOf (r.length + 1) (r.drop (i + 1)) []).map fun args => .undefined lhs (words.take i) args

/-- The reading of a sentence as the introduction of a quantity that the article does not
define, if it has the words of one (it begins with `let`, `we`, `write` or `denote`). -/
def undefinedOf (s : Sentence) : Option Sent :=
  let first := s.toks.findSome? fun p => match p.tok with | .word w => some (lower w) | _ => none
  if !(first.any fun w => [w!"let", w!"we", w!"write", w!"denote"].contains w) then none else
  (chunks (s.toks.length + 1) s.toks []).bind undefinedSent

/-- `The center of $G$ is denoted by $C$.`, `We denote by $C$ the …`: the reading `Let $C$ be the
center of $G$.`, for a sentence whose reading (`NAME is denoted by $S$`, a constant of the
vocabulary) does not compile. -/
def denoteAlt (s : Sentence) : Option Sent := do
  if s.ctx.kind == .proof then none
  let cs ← chunks (s.toks.length + 1) s.toks []
  let cs' ← denoteAsLet cs
  sentence0 cs' <|> (letTheSent cs' >>= sentence0)

/-- The words at which the noun phrase after the `a` of a nested indefinite ends (`every
subgroup of a cyclic group is …`). -/
def nestStops : List Codes :=
  [w!"is", w!"are", w!"has", w!"have", w!"contains", w!"contain", w!"satisfies", w!"satisfy", w!"admits",
   w!"admit", w!"attains", w!"attain", w!"can", w!"does", w!"do", w!"converges", w!"converge", w!"lies",
   w!"lie", w!"belongs", w!"belong", w!"with", w!"such", w!"that", w!"which", w!"whose", w!"and", w!"or",
   w!"if", w!"iff", w!"to", w!"from", w!"of", w!"in", w!"on", w!"over", w!"for", w!"then", w!"where",
   w!"under", w!"at", w!"into", w!"onto", w!"be", w!"must", w!"will", w!"equals", w!"divides", w!"maps",
   w!"generates", w!"acts", w!"act", w!"extends", w!"extend", w!"embeds", w!"embed", w!"splits", w!"vanishes"]

/-- The noun phrase of a nested indefinite: its words (with hyphens, and a formula before a
hyphen, `$p$-group`), up to a stop; and the chunks after it. -/
def nestNP : Nat → List Chunk → List Chunk → List Chunk × List Chunk
  | 0, acc, cs => (acc.reverse, cs)
  | f + 1, acc, cs =>
    match cs with
    | .w w :: r => if nestStops.contains w then (acc.reverse, cs) else nestNP f (.w w :: acc) r
    | .p 45 :: r => nestNP f (.p 45 :: acc) r
    | .m ts :: .p 45 :: r => nestNP f (.p 45 :: .m ts :: acc) r
    | _ => (acc.reverse, cs)

/-- The words of a noun phrase before a complement (`compact subset` of `compact subset of a
Hausdorff space`): words and hyphens only. -/
def plainWords (cs : List Chunk) : Bool :=
  !cs.isEmpty && cs.all fun c => match c with
    | .w w => !nestStops.contains w
    | .p 45 => true
    | _ => false

/-- The first `PREP a NP` after the words of a noun phrase, with `PREP` one of `of`, `on`,
`in`, `over`, `from`: the words before it, the preposition, the inner noun phrase, the
variable written after it (if any), and the chunks after. -/
def nestSplit (cs : List Chunk) : Option (List Chunk × Codes × List Chunk × Option Codes × List Chunk) := do
  let i ← cs.findIdx? fun c => match c with
    | .w w => [w!"of", w!"on", w!"in", w!"over", w!"from"].contains w
    | .p 45 => false
    | _ => true
  let front := cs.take i
  if !plainWords front then none
  let .w prep := (← cs[i]?) | none
  let det ← cs[i + 1]?
  if !(match det with | .w d => d == w!"a" || d == w!"an" | _ => false) then none
  let (np, after) := nestNP (cs.length + 1) [] (cs.drop (i + 2))
  if !(match np.getLast? with | some (.w _) => true | _ => false) then none
  match after with
  | .m [.id v] :: r => some (front, prep, np, some v, r)
  | _ => some (front, prep, np, none, after)

/-- A letter for the object of a nested indefinite: not among `avoid` nor in the sentence. -/
def nestVar (avoid : List Codes) (cs : List Chunk) (k : Nat := 0) : Codes :=
  let used : List Codes := avoid ++ cs.flatMap fun c => match c with
    | .m ts | .d ts _ => ts.filterMap fun t => match t with | .id v => some v | _ => none
    | _ => []
  let free := [w!"X", w!"Y", w!"Z", w!"W", w!"U", w!"V", w!"T", w!"S", w!"Q", w!"P", w!"M", w!"N"].filter (!used.contains ·)
  free[k]?.getD w!"X"

/-- `a`, `an`. -/
def isIndef (c : Chunk) : Bool := match c with
  | .w d => d == w!"a" || d == w!"an"
  | _ => false

/-- The complements after a nested noun phrase that introduce their own objects (`of a
topological space` after `connected subset`), each with its letter if written: the chunks of
the chain, and the chunks after it. -/
def nestChain : Nat → List Chunk → List Chunk × List Chunk
  | 0, cs => ([], cs)
  | f + 1, cs =>
    match cs with
    | .w p :: a :: r =>
      if [w!"of", w!"on", w!"in", w!"over"].contains p && isIndef a then
        let (np, after) := nestNP (r.length + 1) [] r
        if !(match np.getLast? with | some (.w _) => true | _ => false) then ([], cs) else
        let (v, after) : List Chunk × List Chunk := match after with
          | .m [.id x] :: r' => ([.m [.id x]], r')
          | _ => ([], after)
        let (more, rest) := nestChain f after
        ([.w p, a] ++ np ++ v ++ more, rest)
      else ([], cs)
    | _ => ([], cs)

/-- The variables of `Let $u$ and $v$ be …` (formulas joined by `and` and commas): their
chunks, and the chunks after them. -/
def letVars : Nat → List Chunk → List Chunk → Option (List Chunk × List Chunk)
  | 0, _, _ => none
  | f + 1, acc, cs =>
    match cs with
    | .m [.id v] :: .w a :: r => if a == w!"and" then letVars f (acc ++ [.m [.id v], .w a]) r
        else if acc.isEmpty then none else some (acc ++ [.m [.id v]], .w a :: r)
    | .m [.id v] :: .p 44 :: r => letVars f (acc ++ [.m [.id v], .p 44]) r
    | _ => none

/-- The nouns of maps whose signature's letters are objects of a kind (`Let
$\varphi\colon G\to H$ be a group homomorphism`: `G` and `H` are groups). -/
def sigKinds : List (List Codes × List Codes) :=
  [([w!"group", w!"homomorphism"], [w!"group"]), ([w!"homomorphism", w!"of", w!"groups"], [w!"group"]),
   ([w!"group", w!"isomorphism"], [w!"group"]), ([w!"isomorphism", w!"of", w!"groups"], [w!"group"]),
   ([w!"ring", w!"homomorphism"], [w!"ring"]), ([w!"homomorphism", w!"of", w!"rings"], [w!"ring"]),
   ([w!"ring", w!"isomorphism"], [w!"ring"]),
   ([w!"linear", w!"map"], [w!"vector", w!"space"]), ([w!"linear", w!"transformation"], [w!"vector", w!"space"]),
   ([w!"linear", w!"operator"], [w!"vector", w!"space"]), ([w!"linear", w!"isomorphism"], [w!"vector", w!"space"]),
   ([w!"continuous", w!"map"], [w!"topological", w!"space"]), ([w!"homeomorphism"], [w!"topological", w!"space"]),
   ([w!"continuous", w!"bijection"], [w!"topological", w!"space"]), ([w!"open", w!"map"], [w!"topological", w!"space"]),
   ([w!"isometry"], [w!"metric", w!"space"]), ([w!"isometric", w!"embedding"], [w!"metric", w!"space"]),
   ([w!"contraction"], [w!"metric", w!"space"]),
   ([w!"monotone", w!"map"], [w!"partially", w!"ordered", w!"set"]),
   ([w!"order-preserving", w!"map"], [w!"partially", w!"ordered", w!"set"])]

/-- The formula of `the OP of two NOUNS` for its two objects: `$X\cap Y$`. -/
def twoOp (op : Codes) (x y : Codes) : Option (List MTok) :=
  if op == w!"intersection" then some [.id x, .cmd w!"cap", .id y]
  else if op == w!"union" then some [.id x, .cmd w!"cup", .id y]
  else if op == w!"product" then some [.id x, .cmd w!"times", .id y]
  else if op == w!"sum" then some [.id x, .sym 43, .id y]
  else if op == w!"difference" then some [.id x, .sym 45, .id y]
  else none

/-- One step of reading nested indefinites and the idioms around them, as sentences with
more variables. An indefinite inside `every`, `let` or `the` is universal: its object is one
more variable, bound as widely as the noun phrase around it.

* `Every subgroup of a cyclic group is cyclic.`: `For every cyclic group $X$, every subgroup
  of $X$ is cyclic.`; `every continuous map from a compact space to a Hausdorff space …`:
  `for every compact space $X$ and every Hausdorff space $Y$, every continuous map
  $f\colon X\to Y$ …`;
* `The center of a group $G$ is …`: `For every group $G$, the center of $G$ is …`;
* `For every subgroup $H$ of a cyclic group, …`: `For every cyclic group $X$ and every
  subgroup $H$ of $X$, …`;
* `Let $H$ be a subgroup of a cyclic group.`: `Let $X$ be a cyclic group and let $H$ be a
  subgroup of $X$.`; `Let $f\colon X\to Y$ be a continuous bijection from a compact space to a
  Hausdorff space.`, `Let $T\colon V\to V$ be a linear operator on a finite-dimensional
  vector space.`: the letters of the signature are those objects;
* `Let $\varphi\colon G\to H$ be a group homomorphism.`, with `G` and `H` new letters: `Let
  $G$ be a group, let $H$ be a group and let …` (`sigKinds`);
* `Let $G$ be a group of order $p^2$, where $p$ is a prime.`: `Let $p$ be a prime and let $G$
  be a group of order $p^2$.`; `Let $p$ be a prime dividing $n$.`: `… with $p\mid n$`;
* `The intersection of two normal subgroups of $G$ is …`: `For all normal subgroups $X$ and
  $Y$ of $G$, $X\cap Y$ is …` (`union`, `product`);
* `The continuous image of a compact space is compact.`: `For every compact space $X$, every
  topological space $Y$ and every continuous map $f\colon X\to Y$, the image of $f$ is
  compact.`;
* in a statement, `A metric space is compact if and only if it is sequentially compact.`:
  `For every metric space $X$, $X$ is compact if and only if $X$ is sequentially compact.`

`avoid`: the letters in use; `generic`: the sentence states a result (not a definition). -/
def nestedIndef (avoid : List Codes) (generic : Bool) (cs : List Chunk) : Option (List Chunk) :=
  let sig (f x y : Codes) : Chunk := .m [.id f, .sym 58, .id x, .cmd w!"to", .id y]
  let fresh (k : Nat) : Codes := nestVar avoid cs k
  let mapLetter (xs : List Codes) : Codes := ([w!"f", w!"g", w!"h", w!"\\varphi"].find? fun c =>
    !(avoid ++ xs).contains c && !cs.any (fun ch => match ch with | .m ts => ts.contains (.id c) | _ => false)).getD w!"f"
  let plain (ws : List Chunk) : List Codes := ws.filterMap fun c => match c with | .w w => some w | _ => none
  -- `every NP1 PREP a NP2 …`
  let quant : Option (List Chunk) := do
    let .w q :: rest := cs | none
    if ![w!"every", w!"each", w!"any"].contains q then none
    let (front, prep, np, v?, after) ← nestSplit rest
    let x := v?.getD (fresh 0)
    if prep == w!"from" then
      let .w t :: a2 :: r2 := after | none
      if t != w!"to" || !isIndef a2 then none
      let (np2, after2) := nestNP (r2.length + 1) [] r2
      if np2.isEmpty then none
      let (y, after2) := match after2 with
        | .m [.id v] :: r => (v, r)
        | _ => (fresh 1, after2)
      some ([.w w!"for", .w w!"every"] ++ np ++ [.m [.id x], .w w!"and", .w w!"every"] ++ np2 ++ [.m [.id y], .p 44, .w q] ++
        front ++ [sig (mapLetter [x, y]) x y] ++ after2)
    else
      let (chain, after) := nestChain 4 after
      -- (the object of the noun phrase, with a letter: `For every cyclic group $X$ and every
      -- subgroup $Y$ of $X$, $Y$ is cyclic.`)
      let y := fresh 1
      some ([.w w!"for", .w w!"every"] ++ np ++ [.m [.id x]] ++ chain ++ [.w w!"and", .w w!"every"] ++ front ++
        [.m [.id y], .w prep, .m [.id x], .p 44, .m [.id y]] ++ after)
  -- `the continuous image of a NP is …`
  let image : Option (List Chunk) := do
    let r ← kw [w!"the", w!"continuous", w!"image", w!"of"] cs
    let .w a :: r1 := r | none
    if !isIndef (.w a) then none
    let (np, after) := nestNP (r1.length + 1) [] r1
    if np.isEmpty then none
    let x := fresh 0
    let y := fresh 1
    let f := mapLetter [x, y]
    some ([.w w!"for", .w w!"every"] ++ np ++ [.m [.id x], .p 44, .w w!"every", .w w!"topological", .w w!"space", .m [.id y],
      .w w!"and", .w w!"every", .w w!"continuous", .w w!"map", sig f x y, .p 44, .w w!"the", .w w!"image", .w w!"of", .m [.id f]] ++ after)
  -- `the OP of two NOUNS [of $G$] …`
  let two : Option (List Chunk) := do
    let .w t :: .w op :: .w o :: .w n :: r := cs | none
    if t != w!"the" || o != w!"of" || n != w!"two" then none
    let (np, after) := nestNP (r.length + 1) [] r
    if np.isEmpty then none
    -- (the complement of the noun, `of $G$`, or a chain `of a group`)
    let (comp, after) : List Chunk × List Chunk := match after with
      | .w p :: .m g :: r' => if [w!"of", w!"in", w!"over"].contains p then ([.w p, .m g], r') else ([], after)
      | _ => nestChain 4 after
    let x := fresh 0
    let y := fresh 1
    -- (the object of an indefinite complement, `of a topological space`: one, for both)
    let (pre, comp) : List Chunk × List Chunk := match comp with
      | .w p :: a :: rest =>
        if !isIndef a then ([], comp) else
        let words := rest.takeWhile fun ch => match ch with | .w _ | .p 45 => true | _ => false
        let (z, more) := match rest.drop words.length with
          | .m [.id v] :: m => (v, m)
          | m => (fresh 2, m)
        if !more.isEmpty then ([], comp) else
        ([.w w!"for", .w w!"every"] ++ words ++ [.m [.id z], .w w!"and"], [.w p, .m [.id z]])
      | _ => ([], comp)
    let fm ← twoOp op x y
    -- (each object with its own binder: `for every normal subgroup $X$ of $G$ and every
    -- normal subgroup $Y$ of $G$`)
    let .w last := (← np.getLast?) | none
    let one := np.dropLast ++ [.w ((DefForm.singular last).getD last)]
    let lead := if pre.isEmpty then [.w w!"for", .w w!"every"] else pre ++ [.w w!"every"]
    some (lead ++ one ++ [.m [.id x]] ++ comp ++ [.w w!"and", .w w!"every"] ++ one ++ [.m [.id y]] ++ comp ++
      [.p 44, .m fm] ++ after)
  -- `the FRONT of a NP …`
  let theOf : Option (List Chunk) := do
    let .w t :: rest := cs | none
    if t != w!"the" then none
    let (front, prep, np, v?, after) ← nestSplit rest
    if prep != w!"of" then none
    if [[w!"set"], [w!"class"], [w!"number"], [w!"continuous", w!"image"]].contains (plain front) then none
    let x := v?.getD (fresh 0)
    let (chain, after) := nestChain 4 after
    -- (`the square of an odd integer`: `$X^2$`, `the cube`: `$X^3$`)
    let power : Option Nat := match plain front with
      | [f] => if f == w!"square" then some 2 else if f == w!"cube" then some 3 else none
      | _ => none
    if let some k := power then
      return [.w w!"for", .w w!"every"] ++ np ++ [.m [.id x]] ++ chain ++ [.p 44, .m [.id x, .sym 94, .digit k]] ++ after
    some ([.w w!"for", .w w!"every"] ++ np ++ [.m [.id x]] ++ chain ++ [.p 44, .w w!"the"] ++ front ++ [.w w!"of", .m [.id x]] ++ after)
  -- `for every NP1 $v$ PREP a NP3 …, …`
  let forEvery : Option (List Chunk) := do
    let .w fo :: .w q :: rest := cs | none
    if fo != w!"for" || ![w!"every", w!"each", w!"all", w!"any"].contains q then none
    let i ← rest.findIdx? fun c => match c with | .m _ => true | _ => false
    let np1 := rest.take i
    if !plainWords np1 then none
    let (vars, r1) ← match letVars 6 [] (rest.drop i) with
      | some (vs, r) => some (vs, r)
      | none => match rest.drop i with
        | .m [.id v] :: r => some ([Chunk.m [.id v]], r)
        | _ => none
    let .w prep :: a :: r2 := r1 | none
    if ![w!"of", w!"on", w!"in", w!"over"].contains prep || !isIndef a then none
    let (np3, after) := nestNP (r2.length + 1) [] r2
    if !(match np3.getLast? with | some (.w _) => true | _ => false) then none
    let (y, after) := match after with
      | .m [.id v] :: r => (v, r)
      | _ => (fresh 0, after)
    let (chain, after) := nestChain 4 after
    -- (several variables: each with its own binder, `every vector $x$ in $X$ and every vector $y$
    -- in $X$`)
    let names := vars.filterMap fun c => match c with | .m [.id v] => some v | _ => none
    if names.length > 1 then
      let .w last := (← np1.getLast?) | none
      let one := np1.dropLast ++ [.w ((DefForm.singular last).getD last)]
      let each := names.map fun v => [.w w!"every"] ++ one ++ [.m [.id v], .w prep, .m [.id y]]
      some ([.w w!"for", .w w!"every"] ++ np3 ++ [.m [.id y]] ++ chain ++ [.w w!"and"] ++
        (each.intersperse [.w w!"and"]).flatten ++ after)
    else
    some ([.w w!"for", .w w!"every"] ++ np3 ++ [.m [.id y]] ++ chain ++ [.w w!"and", .w q] ++ np1 ++ vars ++ [.w prep, .m [.id y]] ++ after)
  -- `Let VARS be a NP1 PREP a NP2 …`
  let letB : Option (List Chunk) := do
    let r ← kw [w!"let"] cs
    let (vars, r1) ← match letVars 6 [] r with
      | some (vs, r') => some (vs, r')
      | none => match r with
        | .m ts :: r' => some ([Chunk.m ts], r')
        | _ => none
    let r2 ← kw [w!"be"] r1
    let .w det :: r3 := r2 | none
    let indef := det == w!"a" || det == w!"an"
    -- (several variables: a plural noun phrase without an article)
    let (det?, r3) : List Chunk × List Chunk := if indef then ([.w det], r3) else ([], .w det :: r3)
    if vars.length > 1 && indef then none
    let one : Option (List MTok) := match vars with
      | [.m ts] => some ts
      | _ => none
    -- `Let $T\colon V\to W$ be a linear map between finite-dimensional vector spaces`: both
    -- letters of the signature objects of the noun (in the singular), then the map
    let between : Option (List Chunk) := do
      let .sig _ (.id d) (.id c) ← one.bind Math.parseSig | none
      if d == c then none
      let i ← r3.findIdx? fun ch => match ch with | .w w => w == w!"between" | _ => false
      let front := r3.take i
      let np := (r3.drop (i + 1)).takeWhile fun ch => match ch with | .w w => w != w!"and" && w != w!"with" | .p 45 => true | _ => false
      let after := (r3.drop (i + 1)).drop np.length
      let .w last ← np.getLast? | none
      if !(last.length > 1 && last.getLast? == some 115) then none
      let sing := np.dropLast ++ [.w last.dropLast]
      some ([.w w!"let", .m [.id d], .w w!"be", .w w!"a"] ++ sing ++ [.p 44, .w w!"let", .m [.id c], .w w!"be", .w w!"a"] ++ sing ++
        [.w w!"and", .w w!"let", .m (one.getD []), .w w!"be"] ++ det? ++ front ++ after)
    if let some r := between then return r
    let (front, prep, np, v?, after) ← nestSplit r3
    match one.bind Math.parseSig with
    | some (.sig _ (.id d) (.id c)) =>
      let vts := one.getD []
      if prep == w!"from" then
        let .w t :: a2 :: r4 := after | none
        if t != w!"to" || !isIndef a2 || d == c then none
        let (np2, after2) := nestNP (r4.length + 1) [] r4
        if np2.isEmpty || v?.isSome then none
        some ([.w w!"let", .m [.id d], .w w!"be", .w w!"a"] ++ np ++ [.p 44, .w w!"let", .m [.id c], .w w!"be", .w w!"a"] ++
          np2 ++ [.w w!"and", .w w!"let", .m vts, .w w!"be"] ++ det? ++ front ++ after2)
      else if prep == w!"on" && d == c && v?.isNone then
        some ([.w w!"let", .m [.id d], .w w!"be", .w w!"a"] ++ np ++ [.w w!"and", .w w!"let", .m vts, .w w!"be"] ++ det? ++
          front ++ after)
      else none
    | _ =>
      if prep == w!"from" then none
      let x := v?.getD (fresh 0)
      let (chain, after) := nestChain 4 after
      -- (`a linear operator on a vector space`: a map of it into itself)
      let endo := prep == w!"on" && (match front.getLast? with
        | some (.w w) => [w!"operator", w!"endomorphism", w!"transformation", w!"automorphism"].contains w
        | _ => false)
      match vars, endo with
      | [.m [.id v]], true =>
        some ([.w w!"let", .m [.id x], .w w!"be", .w w!"a"] ++ np ++ chain ++ [.w w!"and", .w w!"let", sig v x x, .w w!"be"] ++ det? ++
          front ++ after)
      | _, _ =>
        some ([.w w!"let", .m [.id x], .w w!"be", .w w!"a"] ++ np ++ chain ++ [.w w!"and", .w w!"let"] ++ vars ++ [.w w!"be"] ++ det? ++
          front ++ [.w prep, .m [.id x]] ++ after)
  -- `Let $\varphi\colon G\to H$ be a group homomorphism`, with new letters `G`, `H` (also in a later
  -- `let`, `… and let $T\colon V\to W$ be a linear map`)
  let sigLet : Option (List Chunk) := do
    let k ← (List.range cs.length).find? fun k => match (cs[k]? : Option Chunk), (cs[k + 1]? : Option Chunk) with
      | some (.w l), some (.m ts) => l == w!"let" && (Math.parseSig ts).isSome
      | _, _ => false
    let .m vts := (← cs[k + 1]?) | none
    let .sig _ (.id d) (.id c) ← Math.parseSig vts | none
    let r2 ← kw [w!"be"] (cs.drop (k + 2))
    let .w det :: r3 := r2 | none
    if !isIndef (.w det) then none
    let ws := r3.takeWhile fun ch => match ch with | .w _ | .p 45 => true | _ => false
    let words := (plain ws).filter (· != w!"-")
    let kind ← sigKinds.findSome? fun (n, k) => if words.length ≥ n.length && words.drop (words.length - n.length) == n then some k else none
    let before : List Codes := (cs.take k).flatMap fun ch => match ch with
      | .m ts => ts.filterMap fun t => match t with | .id v => some v | _ => none
      | _ => []
    let news := ([d, c].eraseDups).filter fun v => !avoid.contains v && !before.contains v
    if news.isEmpty then none
    let kindCs : List Chunk := kind.map Chunk.w
    let lets := news.flatMap fun v => [.w w!"let", .m [.id v], .w w!"be", .w w!"a"] ++ kindCs ++ [.p 44]
    some (cs.take k ++ lets.dropLast ++ [.w w!"and"] ++ cs.drop k)
  -- `Let …, where $v$ is a NP.`
  let whereB : Option (List Chunk) := do
    let _ ← kw [w!"let"] cs
    let i ← (List.range cs.length).find? fun i => match (cs[i]? : Option Chunk), (cs[i + 1]? : Option Chunk) with
      | some (.p 44), some (.w w) => w == w!"where"
      | _, _ => false
    let head := cs.take i
    -- (each part, `$v$ is a NP` or a condition `$n\ge1$`, joined by `and`: `where $p$ is a
    -- prime and $n\ge1$`)
    let rec parts : Nat → List Chunk → Option (List (List Chunk))
      | 0, _ => none
      | k + 1, r =>
        let one : Option (List Chunk × List Chunk) := match r with
          | .m [.id v] :: .w is :: a :: r1 =>
            if is != w!"is" || !isIndef a then none else
            let np := r1.takeWhile fun ch => match ch with | .w w => w != w!"and" | .p 45 => true | _ => false
            if np.isEmpty then none else some ([.w w!"let", .m [.id v], .w w!"be", a] ++ np, r1.drop np.length)
          | .m ts :: r1 => some ([.w w!"let", .m ts], r1)
          | _ => none
        match one with
        | some (p, rest) =>
          if isEnd rest then some [p] else
          match rest with
          | .w w :: rest' => if w == w!"and" then (parts k rest').map (p :: ·) else none
          | _ => none
        | none => none
    let ps ← parts 6 (cs.drop (i + 2))
    -- (a condition on the letter of the part before, `where $G$ is a finite group and $|G|=6$`:
    -- `with` it)
    let ids (ts : List MTok) : List Codes := ts.filterMap fun t => match t with | .id v => some v | _ => none
    let merged := ps.foldl (fun (acc : List (List Chunk)) p => match p, acc.getLast? with
      | [.w _, .m ts], some prev =>
        let bound := prev.filterMap fun ch => match ch with | .m [.id v] => some v | _ => none
        if !(ids ts).isEmpty && (ids ts).all bound.contains && prev.length > 2 then acc.dropLast ++ [prev ++ [.w w!"with", .m ts]]
        else acc ++ [p]
      | _, _ => acc ++ [p]) []
    let lets := merged.foldr (fun p acc => p ++ [.w w!"and"] ++ acc) []
    some (lets ++ head ++ [.p 46])
  -- `Let $p$ be a NP dividing $X$.`
  let dividing : Option (List Chunk) := do
    let _ ← kw [w!"let"] cs
    let i ← cs.findIdx? fun ch => match ch with | .w w => w == w!"dividing" | _ => false
    -- (the variable of the latest `let $v$ be` before it)
    let j ← (List.range i).reverse.find? fun j => match (cs[j]? : Option Chunk), (cs[j + 1]? : Option Chunk), (cs[j + 2]? : Option Chunk) with
      | some (.w l), some (.m [.id _]), some (.w b) => l == w!"let" && b == w!"be"
      | _, _, _ => false
    let .m [.id v] := (← cs[j + 1]?) | none
    let .m x :: rest := cs.drop (i + 1) | none
    some (cs.take i ++ [.w w!"with", .m ([.id v, .cmd w!"mid"] ++ x)] ++ rest)
  -- `A NP is …`, `A NP $X$ is … if and only if it is …` (in a statement)
  let genericB : Option (List Chunk) := do
    if !generic then none
    let .w a :: rest := cs | none
    if !isIndef (.w a) then none
    let j ← rest.findIdx? fun ch => match ch with | .w w => w == w!"is" | .m _ => false | .p 45 => false | _ => true
    let np := rest.take j
    let .w is :: _ := rest.drop j | none
    if is != w!"is" then none
    let (np, x) : List Chunk × Codes := match np.getLast? with
      | some (.m [.id v]) => (np.dropLast, v)
      | _ => (np, fresh 0)
    if !plainWords np then none
    let body := DefForm.resolveIt x (rest.length + 1) (rest.drop j)
    some ([.w w!"for", .w w!"every"] ++ np ++ [.m [.id x], .p 44, .m [.id x]] ++ body)
  -- `$f$ attains its maximum on $D$`, `every continuous function $f\colon D\to\mathbb{R}$ attains its
  -- maximum and its minimum`: a point of `D` where the value is largest (smallest)
  let attains : Option (List Chunk) := do
    let i ← cs.findIdx? fun ch => match ch with | .w w => w == w!"attains" | _ => false
    let used : List Codes := avoid ++ cs.flatMap fun c => match c with
      | .m ts => ts.filterMap fun t => match t with | .id v => some v | _ => none
      | _ => []
    let lows := [w!"c", w!"x", w!"t", w!"s", w!"u", w!"y"].filter (!used.contains ·)
    let c ← lows[0]?
    let x ← lows[1]?
    let ext (r : List Chunk) : Option (Bool × List Chunk) := match r with
      | .w a :: .w m :: r' =>
        if (a == w!"its" || a == w!"a") && (m == w!"maximum" || m == w!"minimum") then some (m == w!"maximum", r') else none
      | _ => none
    let (mx1, r1) ← ext (cs.drop (i + 1))
    let (two, r2) : List Bool × List Chunk := match r1 with
      | .w a :: r => if a == w!"and" then match ext r with
          | some (mx2, r') => ([mx1, mx2], r')
          | none => ([mx1], r1)
        else ([mx1], r1)
      | _ => ([mx1], r1)
    let (onD, r3) : Option (List MTok) × List Chunk := match r2 with
      | .w o :: .m d :: r => if o == w!"on" || o == w!"over" || o == w!"in" then (some d, r) else (none, r2)
      | _ => (none, r2)
    if !isEnd r3 then none
    -- (after binders, `for every compact interval $X$ and every continuous function $Y$ on $X$,
    -- $Y$ attains …`: the domain of the function there)
    let pre : List Chunk := match cs.head? with
      | some (.w fo) =>
        if fo != w!"for" then [] else
        match ((cs.take i).zipIdx.filter fun (c, _) => match c with | .p 44 => true | _ => false).getLast? with
        | some (_, k) => cs.take (k + 1)
        | none => []
      | _ => []
    let subj := (cs.take i).drop pre.length
    let domIn (f : Codes) : Option (List MTok) := (List.range pre.length).findSome? fun k =>
      match (pre[k]? : Option Chunk), (pre[k + 1]? : Option Chunk), (pre[k + 2]? : Option Chunk) with
      | some (.m [.id g]), some (.w o), some (.m d) => if g == f && o == w!"on" then some d else none
      | _, _, _ => none
    let (lead, fn, dom) ← match subj with
      | [.m [.id f]] => (onD <|> domIn f).map fun d => (pre, f, d)
      | [.w t, .m [.id f]] => if t == w!"then" then onD.map fun d => (pre ++ [.w t], f, d) else none
      | .w q :: rest =>
        if ![w!"every", w!"each", w!"any"].contains q then none else
        -- (`every continuous function on $[a,b]$`: a function `f` of that domain)
        let onDom : Option (List Chunk × Codes × List MTok) := match rest.reverse with
          | .m d :: .w o :: words =>
            if o != w!"on" || !plainWords words.reverse || words.isEmpty || used.contains w!"f" then none else
            some (pre ++ [.w w!"for", .w w!"every"] ++ words.reverse ++
              [.m ([.id w!"f", .sym 58] ++ d ++ [.cmd w!"to", .id w!"\\mathbb{R}"]), .p 44], w!"f", onD.getD d)
          | _ => none
        let bySig : Option (List Chunk × Codes × List MTok) := do
          let some (.m sg) := rest.getLast? | none
          let some (.sig (.id f) _ _) := Math.parseSig sg | none
          let i' ← sg.findIdx? (· == .sym 58) <|> sg.findIdx? (· == .cmd w!"colon")
          let j ← sg.findIdx? (· == .cmd w!"to")
          let d := (sg.drop (i' + 1)).take (j - i' - 1)
          if !plainWords rest.dropLast then none
          some (pre ++ [.w w!"for", .w w!"every"] ++ rest ++ [.p 44], f, onD.getD d)
        onDom <|> bySig
      | _ => none
    let app (v : Codes) : List MTok := [.id fn, .sym 40, .id v, .sym 41]
    let clause (mx : Bool) : List Chunk :=
      [.w w!"there", .w w!"is", .m ([.id c, .cmd w!"in"] ++ dom), .w w!"such", .w w!"that",
       .m ((if mx then app x else app c) ++ [.cmd w!"le"] ++ (if mx then app c else app x)),
       .w w!"for", .w w!"all", .m ([.id x, .cmd w!"in"] ++ dom)]
    let body := match two with
      | [a, b] => clause a ++ [.p 44, .w w!"and"] ++ clause b
      | _ => clause mx1
    some (lead ++ body ++ [.p 46])
  -- `SUBJ is [either] X or Y`: `SUBJ is X or SUBJ is Y`
  let eitherOr : Option (List Chunk) := do
    -- (after the binders of `For every NP $X$, …`)
    let (pre, cs) : List Chunk × List Chunk := match cs with
      | .w f :: _ =>
        if f != w!"for" then ([], cs) else
        match cs.findIdx? (fun ch => match ch with | .p 44 => true | _ => false) with
        | some c => (cs.take (c + 1), cs.drop (c + 1))
        | none => ([], cs)
      | _ => ([], cs)
    let i ← cs.findIdx? fun ch => match ch with | .w w => w == w!"is" | _ => false
    let subj := cs.take i
    if subj.isEmpty then none
    let r := cs.drop (i + 1)
    let r := (kw [w!"either"] r).getD r
    let j ← r.findIdx? fun ch => match ch with | .w w => w == w!"or" | _ => false
    let x := r.take j
    let rest := r.drop (j + 1)
    let k ← rest.findIdx? fun ch => match ch with | .p 46 => true | _ => false
    let y := rest.take k
    if x.isEmpty || y.isEmpty || k + 1 != rest.length then none
    if (cs.filter fun ch => match ch with | .w w => w == w!"is" || w == w!"or" | _ => false).length != 2 then none
    some (pre ++ subj ++ [.w w!"is"] ++ x ++ [.w w!"or"] ++ subj ++ [.w w!"is"] ++ y ++ [.p 46])
  -- `The number $\sqrt2$ is irrational.`, `The polynomial $x^2-2$ is …`: what the noun says of the
  -- formula, and the claim (`$\sqrt2$ is a number and $\sqrt2$ is irrational`)
  let appositive : Option (List Chunk) := do
    let .w t :: rest := cs | none
    if t != w!"the" then none
    let ws := rest.takeWhile fun ch => match ch with | .w w => !nestStops.contains w | .p 45 => true | _ => false
    if ws.isEmpty then none
    let .m f :: after := rest.drop ws.length | none
    -- (not a letter: `the group $G$` is read on its own)
    if (match f with | [.id _] => true | _ => false) then none
    let .w v :: _ := after | none
    if ![w!"is", w!"are", w!"has", w!"divides", w!"converges", w!"diverges", w!"satisfies"].contains v then none
    let trivial := [[w!"number"], [w!"real", w!"number"], [w!"integer"]].contains (plain ws)
    if trivial then some ([.m f] ++ after)
    else some ([.m f, .w w!"is", .w (if (match (plain ws).head? >>= List.head? with
        | some ch => [97, 101, 105, 111, 117].contains ch | none => false) then w!"an" else w!"a")] ++ ws ++ [.w w!"and", .m f] ++ after)
  -- `In a principal ideal domain, every irreducible element is prime.`: `For every principal ideal
  -- domain $X$, every irreducible element of $X$ is prime.`
  let inA : Option (List Chunk) := do
    let .w i :: a :: r := cs | none
    if i != w!"in" || !isIndef a then none
    let np := r.takeWhile fun ch => match ch with | .w w => !nestStops.contains w | .p 45 => true | _ => false
    if np.isEmpty then none
    let (x, r1) := match r.drop np.length with
      | .m [.id v] :: r' => (v, r')
      | r' => (fresh 0, r')
    let r2 ← punct 44 r1
    let .w q :: r3 := r2 | none
    if ![w!"every", w!"each", w!"any", w!"all"].contains q then none
    let np1 := r3.takeWhile fun ch => match ch with | .w w => !nestStops.contains w | .p 45 => true | _ => false
    if np1.isEmpty then none
    let after := r3.drop np1.length
    let comp : List Chunk := match after with
      | .w p :: _ => if [w!"of", w!"in", w!"over"].contains p then [] else [.w w!"of", .m [.id x]]
      | _ => [.w w!"of", .m [.id x]]
    some ([.w w!"for", .w w!"every"] ++ np ++ [.m [.id x], .p 44, .w q] ++ np1 ++ comp ++ after)
  -- `Let $T$ be a linear operator between normed spaces.`: `Let $X$ be a normed space, let $Y$
  -- be a normed space and let $T\colon X\to Y$ be a linear operator.`
  let between : Option (List Chunk) := do
    let r ← kw [w!"let"] cs
    let .m [.id v] :: .w be :: .w det :: r1 := r | none
    if be != w!"be" || !isIndef (.w det) then none
    let i ← r1.findIdx? fun ch => match ch with | .w w => w == w!"between" | _ => false
    let front := r1.take i
    if !plainWords front then none
    let (np2, after) := nestNP (r1.length + 1) [] (r1.drop (i + 1))
    let .w last := (← np2.getLast?) | none
    let one := np2.dropLast ++ [.w ((DefForm.singular last).getD last)]
    let x := fresh 0
    let y := fresh 1
    some ([.w w!"let", .m [.id x], .w w!"be", .w w!"a"] ++ one ++ [.p 44, .w w!"let", .m [.id y], .w w!"be", .w w!"a"] ++ one ++
      [.w w!"and", .w w!"let", sig v x y, .w w!"be", .w det] ++ front ++ after)
  -- `Every subgroup of index $2$ is normal.`: of every group, `For every group $X$, every subgroup
  -- of $X$ of index $2$ in $X$ is normal.`
  let ofIndex : Option (List Chunk) := do
    let .w q :: rest := cs | none
    if ![w!"every", w!"each", w!"any"].contains q then none
    let i ← rest.findIdx? fun ch => match ch with | .w w => w == w!"of" | _ => false
    let front := rest.take i
    if !(plain front == [w!"subgroup"] || plain front == [w!"normal", w!"subgroup"]) then none
    let .w ix :: .m n :: after := rest.drop (i + 1) | none
    if ix != w!"index" then none
    let x := fresh 0
    let h := fresh 1
    some ([.w w!"for", .w w!"every", .w w!"group", .m [.id x], .w w!"and", .w w!"every"] ++ front ++
      [.m [.id h], .w w!"of", .m [.id x], .w w!"of", .w w!"index", .m n, .w w!"in", .m [.id x], .p 44, .m [.id h]] ++ after)
  -- `Let $G$ be a finite $p$-group.`, with a new letter `p`: `Let $p$ be a prime and let $G$ be …`
  let pGroup : Option (List Chunk) := do
    let i ← (List.range cs.length).find? fun i => match (cs[i]? : Option Chunk), (cs[i + 1]? : Option Chunk), (cs[i + 2]? : Option Chunk) with
      | some (.m [.id _]), some (.p 45), some (.w g) => g == w!"group" || g == w!"groups" || g == w!"subgroup" || g == w!"subgroups"
      | _, _, _ => false
    let .m [.id p] := (← cs[i]?) | none
    let before : List Codes := (cs.take i).flatMap fun ch => match ch with
      | .m ts => ts.filterMap fun t => match t with | .id v => some v | _ => none
      | _ => []
    if avoid.contains p || before.contains p then none
    let .w l :: _ := cs | none
    if l == w!"let" then some ([.w w!"let", .m [.id p], .w w!"be", .w w!"a", .w w!"prime", .w w!"and"] ++ cs)
    else if [w!"every", w!"each", w!"any"].contains l then some ([.w w!"for", .w w!"every", .w w!"prime", .m [.id p], .p 44] ++ cs)
    else none
  image <|> two <|> forEvery <|> quant <|> theOf <|> sigLet <|> letB <|> whereB <|> dividing <|> attains <|> inA <|>
    between <|> ofIndex <|> pGroup <|> genericB <|> appositive <|> eitherOr

/-- The readings of `nestedIndef`, one step after another (the last first), as readings of
the sentence where its own reading does not compile. -/
def nestedAlts (avoid : List Codes) (s : Sentence) : List Sent := Id.run do
  if s.ctx.kind == .proof then return []
  let some cs := chunks (s.toks.length + 1) s.toks [] | return []
  let generic := match s.ctx.kind with
    | .result e => e.take 3 != w!"def"
    | _ => false
  -- (`Then …`: the rest, after `then`)
  let (lead, cs) : List Chunk × List Chunk := match cs with
    | .w t :: rest => if t == w!"then" then ([.w t], rest) else ([], cs)
    | _ => ([], cs)
  let mut cur := cs
  let mut out : List Sent := []
  let mut nested : List (List Chunk) := []
  for _ in [0:5] do
    match nestedIndef avoid generic cur with
    | some cs' =>
      cur := cs'
      nested := nested ++ [cs']
      if let some sn := sentence (lead ++ cs') then out := sn :: out
    | none => break
  -- `The set of nilpotent elements of $R$ is an ideal of $R$.`: the set, bound as `Let $X$ be the
  -- set of …` binds it, and the claim about it
  let theSet : Option Sent := do
    let .w t :: .w st :: .w o :: rest := cs | none
    if t != w!"the" || !(st == w!"set" || st == w!"class") || o != w!"of" then none
    let i ← rest.findIdx? fun ch => match ch with | .w w => w == w!"is" || w == w!"are" | _ => false
    let members := rest.take i
    if members.isEmpty || members.any (fun ch => match ch with | .p _ => true | _ => false) then none
    let x := nestVar avoid cs 0
    let .claims tp bs cls ← sentence (lead ++ .m [.id x] :: rest.drop i) | none
    some (.claims tp (.noun ([.w w!"@the", .w st, .w o] ++ members ++ [.m [.id x]]) :: bs) cls)
  -- `$X$ and $Y$ are isomorphic`: `$X$ is isomorphic to $Y$` (also `with`, `from`), the
  -- relation of the two said of one of them about the other
  let single (ts : List MTok) : Bool := match Math.parseFormula ts with | some (.id _) => true | _ => false
  let stops := [w!"then", w!"and", w!"or", w!"if", w!"iff", w!"for", w!"since", w!"so", w!"but", w!"to", w!"with",
    w!"from", w!"in", w!"of", w!"on", w!"as", w!"than", w!"by", w!"at", w!"distinct", w!"equal", w!"disjoint",
    w!"orthogonal", w!"coprime", w!"independent", w!"pairwise", w!"mutually", w!"both", w!"not"]
  let rec pairForm (prep : Codes) : Nat → List Chunk → Option (List Chunk)
    | 0, _ => none
    | f + 1, cs =>
      match cs with
      | .m x :: .w a :: .m y :: .w are :: rest =>
        let ws := rest.takeWhile fun c => match c with
          | .w w => !stops.contains w
          | .p 45 => true
          | _ => false
        let after := rest.drop ws.length
        let ends := match after with
          | [] | .p _ :: _ => true
          | .w w :: _ => [w!"then", w!"and", w!"or", w!"if", w!"iff", w!"since", w!"so", w!"but"].contains w
          | _ => false
        if a == w!"and" && are == w!"are" && single x && single y && !ws.isEmpty && ends then
          some ([.m x, .w w!"is"] ++ ws ++ [.w prep, .m y] ++ ((pairForm prep f after).getD after))
        else (pairForm prep f (.w a :: .m y :: .w are :: rest)).map (.m x :: ·)
      | c :: rest => (pairForm prep f rest).map (c :: ·)
      | [] => none
  let pairs : List Sent := [w!"to", w!"with", w!"from"].filterMap fun prep => do
    let cs' ← pairForm prep (cs.length + 1) cs
    sentence (lead ++ cs')
  -- `$A$ and $B$ have the same characteristic polynomial`: `the characteristic polynomial of
  -- $A$ equals the characteristic polynomial of $B$`
  let rec sameForm : Nat → List Chunk → Option (List Chunk)
    | 0, _ => none
    | f + 1, cs =>
      match cs with
      | .m x :: .w a :: .m y :: .w h :: .w t :: .w sm :: rest =>
        let ws := rest.takeWhile fun c => match c with
          | .w w => !stops.contains w
          | .p 45 => true
          | _ => false
        let after := rest.drop ws.length
        if a == w!"and" && h == w!"have" && t == w!"the" && sm == w!"same" && single x && single y && !ws.isEmpty then
          some ([.w w!"the"] ++ ws ++ [.w w!"of", .m x, .w w!"equals", .w w!"the"] ++ ws ++ [.w w!"of", .m y] ++ after)
        else (sameForm f (.w a :: .m y :: .w h :: .w t :: .w sm :: rest)).map (.m x :: ·)
      | c :: rest => (sameForm f rest).map (c :: ·)
      | [] => none
  -- (alone, and after the pairs of the same sentence: `if $A$ and $B$ are similar, then $A$ and
  -- $B$ have the same …`)
  let same : List Sent := ((cs :: [w!"to", w!"with", w!"from"].filterMap fun prep => pairForm prep (cs.length + 1) cs).filterMap fun c =>
    (sameForm (c.length + 1) c).bind fun cs' => sentence (lead ++ cs'))
  -- `Let $A$ and $B$ be similar matrices`: the matrix `A`, and a matrix `B` similar to `A` (also
  -- `with`, `from`)
  let letPair : List Sent := match cs with
    | .w l :: .m x :: .w a :: .m y :: .w be :: .w adj :: rest@(.w _ :: _) =>
      if lower l != w!"let" || a != w!"and" || be != w!"be" || !single x || !single y || stops.contains adj then [] else
      let np := rest.takeWhile fun c => match c with | .w w => !stops.contains w | .p 45 => true | _ => false
      let after := rest.drop np.length
      if np.isEmpty || !(match after with | [] | [.p 46] => true | _ => false) then [] else
      -- (the first object, then the second with the relation to it: `matrices $B$ similar to $A$`)
      [w!"to", w!"with", w!"from"].map fun prep =>
        Sent.assumeAll [.noun (np ++ [.m x]), .noun (np ++ [.m y, .w adj, .w prep, .m x])] []
    | _ => []
  -- `Similar matrices have the same characteristic polynomial.`: for every matrix `X` and every
  -- matrix `Y` similar to `X`, the characteristic polynomial of `X` equals that of `Y`
  let genericSame : List Sent := match cs with
    | .w adj :: rest =>
      if !generic || stops.contains (lower adj) then [] else
      let np := rest.takeWhile fun c => match c with | .w w => w != w!"have" && !stops.contains w | .p 45 => true | _ => false
      match rest.drop np.length with
      | .w h :: .w t :: .w sm :: rest2 =>
        if np.isEmpty || h != w!"have" || t != w!"the" || sm != w!"same" then [] else
        let ws := rest2.takeWhile fun c => match c with | .w w => !stops.contains w | .p 45 => true | _ => false
        let after := rest2.drop ws.length
        if ws.isEmpty || !(match after with | [] | [.p 46] => true | _ => false) then [] else
        let x := nestVar avoid cs 0
        let y := nestVar avoid cs 1
        let claim := [.w w!"the"] ++ ws ++ [.w w!"of", .m [.id x], .w w!"equals", .w w!"the"] ++ ws ++ [.w w!"of", .m [.id y]] ++ after
        [w!"to", w!"with", w!"from"].filterMap fun prep => do
          let .claims tp bs cls ← sentence claim | none
          some (.claims tp ([.noun (np ++ [.m [.id x]]), .noun (np ++ [.m [.id y], .w (lower adj), .w prep, .m [.id x]])] ++ bs) cls)
      | _ => []
    | _ => []
  -- `Any two bases of $V$ have the same number of elements.`: for every two objects of the
  -- noun, the notion of one equals that of the other
  let anyTwoAt (lead cs : List Chunk) : List Sent := match cs with
    | .w a :: .w t :: rest =>
      if lower a != w!"any" || t != w!"two" then [] else
      let np0 := rest.takeWhile fun c => match c with | .w w => w != w!"have" && w != w!"are" | .m _ => true | .p 45 => true | _ => false
      let x := nestVar avoid cs 0
      let y := nestVar avoid cs 1
      -- the claims about `x` and `y`: `the WORDS of $x$ equals the WORDS of $y$`, or `$x$ is WORDS
      -- to (with, from) $y$`
      let claims : List (List Chunk) := match rest.drop np0.length with
        | .w h :: .w th :: .w sm :: rest2 =>
          if h != w!"have" || th != w!"the" || sm != w!"same" then [] else
          -- (`the same number of elements`: words, `of` included)
          let ws := rest2.takeWhile fun c => match c with | .w w => w == w!"of" || !stops.contains w | .p 45 => true | _ => false
          let after := rest2.drop ws.length
          if ws.isEmpty || !(match after with | [] | [.p 46] => true | _ => false) then [] else
          [[.w w!"the"] ++ ws ++ [.w w!"of", .m [.id x], .w w!"equals", .w w!"the"] ++ ws ++ [.w w!"of", .m [.id y]] ++ after]
        | .w are :: rest2 =>
          if are != w!"are" then [] else
          let ws := rest2.takeWhile fun c => match c with | .w w => !stops.contains w | .p 45 => true | _ => false
          let after := rest2.drop ws.length
          if ws.isEmpty || !(match after with | [] | [.p 46] => true | _ => false) then [] else
          [w!"to", w!"with", w!"from"].map fun prep => [.m [.id x], .w w!"is"] ++ ws ++ [.w prep, .m [.id y]] ++ after
        | _ => []
      if np0.isEmpty then [] else
      -- (`of a finite-dimensional vector space`: one space for both, bound before them)
      let art := np0.findIdx? fun c => match c with | .w w => w == w!"a" || w == w!"an" | _ => false
      let (pre, np) : List Chunk × List Chunk := match art with
        | some k =>
          if k == 0 || (match np0[k - 1]? with | some (.w o) => o != w!"of" | _ => true) then ([], []) else
          let z := nestVar avoid cs 2
          ([.w w!"for", .w w!"every"] ++ np0.drop (k + 1) ++ [.m [.id z], .p 44], np0.take k ++ [.m [.id z]])
        | none => ([], np0)
      if np.isEmpty then [] else
      -- (the variable after the noun phrase, as `Let $B$ be bases of $V$` has it)
      let withVar (v : Codes) : List Chunk := np ++ [.m [.id v]]
      -- (also each object of the noun in the singular, `every basis $X$ of $Z$`: the
      -- plural's last word, by the rules of English plurals)
      let head := (np.findIdx? fun c => match c with | .w w => w == w!"of" | _ => false).getD np.length
      let sings : List (List Chunk) := match np[head - 1]? with
        | some (.w w) =>
          let ends (e : Codes) : Bool := w.length > e.length && w.drop (w.length - e.length) == e
          let stem (k : Nat) : Codes := w.take (w.length - k)
          let cands : List Codes :=
            (if ends w!"ices" then [stem 4 ++ w!"ex", stem 4 ++ w!"ix"] else []) ++
            (if ends w!"ses" then [stem 3 ++ w!"sis"] else []) ++
            (if ends w!"ies" then [stem 3 ++ w!"y"] else []) ++
            (if ends w!"es" then [stem 2] else []) ++
            (if ends w!"s" then [stem 1] else [])
          cands.map fun sg => (np.take (head - 1) ++ [.w sg]) ++ np.drop head
        | _ => []
      let atVar (n : List Chunk) (v : Codes) : List Chunk :=
        let ws0 := n.takeWhile fun c => match c with | .w w => w != w!"of" | .p 45 => true | .m _ => true | _ => false
        ws0 ++ [.m [.id v]] ++ n.drop ws0.length
      claims.flatMap fun claim =>
        match sentence (lead ++ pre ++ claim) with
        | some (.claims tp bs cls) =>
          -- (one binder list, each object after the ones it refers to)
          let flat := bs.flatMap fun b => match b with | .many bs' => bs' | b => [b]
          let mk (x' y' : List Chunk) : Sent :=
            let nouns := [Bind.noun x', Bind.noun y']
            .claims tp (if flat.isEmpty then nouns else [.many (flat ++ nouns)]) cls
          (sings.map fun n => mk (atVar n x) (atVar n y)) ++ [mk (withVar x) (withVar y)]
        | _ => []
    | _ => []
  -- `$U\cap W$ and $U+W$ are subspaces of $V$`, `$a^2$ and $b^2$ are nonnegative`: each of the
  -- two is (a) … (not a relation of the two: `distinct`, `isomorphic`, …)
  let bothIs : List Sent := match cs with
    | .m x :: .w a :: .m y :: .w are :: rest =>
      if a != w!"and" || are != w!"are" then [] else
      let pred := match rest.getLast? with | some (.p 46) => rest.dropLast | _ => rest
      let relational := [w!"isomorphic", w!"homeomorphic", w!"conjugate", w!"similar", w!"congruent", w!"equivalent",
        w!"parallel", w!"perpendicular", w!"adjacent", w!"comparable", w!"equinumerous", w!"related", w!"orthogonal",
        w!"distinct", w!"equal", w!"disjoint", w!"coprime", w!"independent", w!"pairwise", w!"mutually", w!"both",
        w!"different", w!"identical", w!"opposite", w!"complementary", w!"dual", w!"inverse", w!"inverses", w!"permutable"]
      if pred.isEmpty || pred.any (fun c => match c with | .w w => relational.contains (lower w) | .p p => p != 45 | _ => false) then [] else
      let mk (p : List Chunk) : List Chunk := [.m x, .w w!"is"] ++ p ++ [.w w!"and", .m y, .w w!"is"] ++ p ++ [.p 46]
      -- (a plural noun: its head word in the singular, after an article)
      let head := (pred.findIdx? fun c => match c with | .w w => w == w!"of" || w == w!"in" || w == w!"with" | .m _ => true | _ => false).getD pred.length
      let nouns : List (List Chunk) := match (pred[head - 1]? : Option Chunk) with
        | some (Chunk.w w) =>
          let ends (e : Codes) : Bool := w.length > e.length && w.drop (w.length - e.length) == e
          let stem (k : Nat) : Codes := w.take (w.length - k)
          let cands : List Codes :=
            (if ends w!"ices" then [stem 4 ++ w!"ex", stem 4 ++ w!"ix"] else []) ++
            (if ends w!"ses" then [stem 3 ++ w!"sis"] else []) ++
            (if ends w!"ies" then [stem 3 ++ w!"y"] else []) ++
            (if ends w!"es" then [stem 2] else []) ++
            (if ends w!"s" then [stem 1] else [])
          cands.map fun sg =>
            let p := pred.take (head - 1) ++ [Chunk.w sg] ++ pred.drop head
            let art := match p.head? with
              | some (.w f) => if (f.head?.map fun ch => [97, 101, 105, 111, 117].contains ch).getD false then w!"an" else w!"a"
              | _ => w!"a"
            Chunk.w art :: p
        | _ => []
      (pred :: nouns).filterMap fun p => sentence (lead ++ mk p)
    | _ => []
  -- (also after the binder of an indefinite object, `Any two bases of a finite-dimensional vector
  -- space …`: `for every finite-dimensional vector space $X$, any two bases of $X$ …`)
  let anyTwo : List Sent := anyTwoAt lead cs ++ nested.flatMap fun cs' =>
    match cs'.findIdx? (fun c => match c with | .p 44 => true | _ => false) with
    | some k => if (match cs' with | .w f :: _ => f == w!"for" | _ => false) then anyTwoAt (lead ++ cs'.take (k + 1)) (cs'.drop (k + 1)) else []
    | none => []
  -- `$N$ contains $H$`, `$N$ contains the commutator subgroup of $G$`: `… is a subset of $N$`;
  -- `$A$ contains $x$`: `$x\in A$`
  let rec containsForm (asMember : Bool) : Nat → List Chunk → Option (List Chunk)
    | 0, _ => none
    | f + 1, cs =>
      match cs with
      | .m x :: .w c :: rest =>
        if c != w!"contains" || !single x then (containsForm asMember f (.w c :: rest)).map (.m x :: ·) else
        let obj := rest.takeWhile fun ch => match ch with
          | .w w => ![w!"and", w!"or", w!"if", w!"iff", w!"then", w!"since", w!"so", w!"but", w!"for", w!"whenever"].contains w
          | .m _ | .p 45 => true
          | _ => false
        let after := rest.drop obj.length
        match obj with
        | [.m y] =>
          if asMember then some ([.m (y ++ [.cmd w!"in"] ++ x)] ++ after)
          else some ([.m (y ++ [.cmd w!"subseteq"] ++ x)] ++ after)
        | .w t :: _ =>
          if asMember || t != w!"the" then none else
          some (obj ++ [.w w!"is", .w w!"a", .w w!"subset", .w w!"of", .m x] ++ after)
        | _ => none
      | c :: rest => (containsForm asMember f rest).map (c :: ·)
      | [] => none
  let contains : List Sent := [false, true].filterMap fun asMember => do
    let cs' ← containsForm asMember (cs.length + 1) cs
    sentence (lead ++ cs')
  -- `For all $n\in\mathbb{N}$, the number of subsets of a set of $n$ elements is $2^n$`, in a
  -- result: the claim about the notion of the binder's variables (`For …, we have that …`), when
  -- it is no definition of the words
  let binderClaim : List Sent := Id.run do
    let .w f :: _ := cs | return []
    if !generic || lower f != w!"for" then return []
    let some k := cs.findIdx? (fun c => match c with | .p 44 => true | _ => false) | return []
    let .w t :: _ := cs.drop (k + 1) | return []
    if lower t != w!"the" then return []
    (sentence (lead ++ cs.take (k + 1) ++ [.w w!"we", .w w!"have", .w w!"that"] ++ cs.drop (k + 1))).toList
  -- `A compact subset of a Hausdorff space is closed.`, in a result: a statement about every
  -- object of the noun phrase (`Every compact subset …`)
  -- `Every ideal $M$ of $R$ is maximal if and only if $R/M$ is a field.`: `For every ideal $M$
  -- of $R$, $M$ is maximal if and only if …`, the letter bound for the whole sentence
  let everyVar (cs : List Chunk) : Option (List Chunk) := do
    let .w e :: rest := cs | none
    if !(e == w!"every" || e == w!"each") then none
    let vi ← rest.findIdx? fun c => match c with | .m [.id _] => true | _ => false
    let .m [.id x] ← rest[vi]? | none
    if vi == 0 || !((rest.take vi).all fun c => match c with | .w _ | .p 45 => true | _ => false) then none
    let ii ← rest.findIdx? fun c => match c with
      | .w w => [w!"is", w!"has", w!"satisfies", w!"divides", w!"lies", w!"belongs", w!"contains", w!"equals"].contains w
      | _ => false
    if ii <= vi then none
    if (rest.take ii).any (fun c => match c with | .p _ => true | _ => false) && !((rest.take ii).all fun c => match c with | .p 45 | .w _ | .m _ => true | _ => false) then none
    some ([.w w!"for", .w w!"every"] ++ rest.take ii ++ [.p 44, .m [.id x]] ++ rest.drop ii)
  let everyV : List Sent := if !generic then [] else
    ((everyVar cs).bind fun cs' => sentence (lead ++ cs')).toList
  -- `Every increasing sequence that is bounded above converges.`: `Every increasing sequence
  -- bounded above converges.`, the words after `that is` after the noun
  let relFree : List Sent := Id.run do
    let some i := (List.range cs.length).find? fun i => match (cs[i]? : Option Chunk), (cs[i + 1]? : Option Chunk), (cs[i + 2]? : Option Chunk), (cs[i + 3]? : Option Chunk) with
        | some (.w t), some (.w b), some (.w _), some _ => i > 1 && (t == w!"that" || t == w!"which") && (b == w!"is" || b == w!"are")
        | _, _, _, _ => false
      | return []
    -- (only inside a subject that a quantifier or an article opens)
    let some (.w q) := (cs[0]? : Option Chunk) | return []
    if ![w!"every", w!"each", w!"any", w!"a", w!"an", w!"all"].contains (lower q) then return []
    let cs' := cs.take i ++ cs.drop (i + 2)
    let mut acc := (sentence (lead ++ cs')).toList
    if generic && (lower q == w!"a" || lower q == w!"an") then
      acc := acc ++ (sentence (lead ++ .w w!"every" :: cs'.drop 1)).toList
    -- (or the words of the clause before the noun, as adjectives: `Every bounded above increasing
    -- sequence converges.`; the relative clause ends before the last verb)
    if generic && (lower q != w!"all") then
      let verbs := [w!"is", w!"are", w!"has", w!"have", w!"converges", w!"converge", w!"contains", w!"lies", w!"attains",
        w!"divides", w!"equals", w!"satisfies", w!"admits", w!"diverges"]
      let after := cs.drop (i + 2)
      if let some (_, j) := (after.zipIdx.filter fun (c, _) => match c with | .w w => verbs.contains w | _ => false).getLast? then
        let rel := after.take j
        let np := (cs.take i).drop 1
        if !rel.isEmpty && rel.all (fun c => match c with | .w _ | .p 45 => true | _ => false) &&
            np.all (fun c => match c with | .w _ | .p 45 => true | _ => false) then
          acc := acc ++ (sentence (lead ++ [.w w!"every"] ++ rel ++ np ++ after.drop j)).toList
    return acc
  let generic' : List Sent := Id.run do
    if !generic then return []
    let .w a :: rest := cs | return []
    if !(lower a == w!"a" || lower a == w!"an") then return []
    let ev := .w w!"every" :: rest
    let mut acc := (sentence (lead ++ ev)).toList ++
      ((everyVar ev).bind fun cs' => sentence (lead ++ cs')).toList
    -- (and its nested indefinites: `A compact subset of a Hausdorff space is closed.`)
    -- (`A continuous image of a connected space is connected.`: the image of every such map,
    -- as `The continuous image of …`)
    let starts := if rest.any (fun c => match c with | .w w => w == w!"image" | _ => false) then [ev, .w w!"the" :: rest] else [ev]
    for st in starts do
      let mut cur := st
      for _ in [0:5] do
        match nestedIndef avoid generic cur with
        | some cs' =>
          cur := cs'
          if let some sn := sentence (lead ++ cs') then acc := acc ++ [sn]
        | none => break
    return acc
  return out ++ theSet.toList ++ pairs ++ same ++ letPair ++ genericSame ++ anyTwo ++ bothIs ++ contains ++ binderClaim ++ everyV ++ relFree ++ generic'

/-- The formal restatement of `INFORMAL, that is, FORMAL`, read on its own: the reading of the
sentence when its reading as a whole does not compile. -/
def thatIsSentence (s : Sentence) : Option Sent := do
  let cs ← chunks (s.toks.length + 1) s.toks []
  let r ← skipThatIs cs
  sentence0 r

def parseSentence (s : Sentence) : Option Sent := do
  match s.toks with
  -- the heading of a case (`\item \emph{…}`)
  | ⟨.cmd h, _, _⟩ :: rest =>
    if h == w!"@heading" then caseHeading (← chunks (rest.length + 1) rest [])
    -- the heading of a paragraph of a proof (`\emph{Signed coefficients.}`) organizes it
    else if h == w!"@paraheading" then
      if rest.all (fun p => match p.tok with | .word _ | .punct _ => true | _ => false) then some .organizes
      else sentence (← chunks (rest.length + 1) rest [])
    else sentence (← chunks (s.toks.length + 1) s.toks [])
  | _ =>
    let cs ← chunks (s.toks.length + 1) s.toks []
    -- (the forms of a definition, where the sentence is otherwise not read; not in a proof)
    let inDef := match s.ctx.kind with | .result e => e.take 3 == w!"def" | _ => false
    let define (_ : Unit) : Option Sent := if s.ctx.kind == .proof then none else defSentence inDef cs
    match sentence cs with
    | some (.notionSubject np) => (define ()).orElse fun _ => some (.notionSubject np)
    | none => define ()
    | r => r


/-! ## Sentences of several parts

A sentence that no form reads as a whole may be several sentences in one. Each of the
following is read as the sentences it is made of, one after the other, and only if each
of them is read:

* parts joined by `, and` before a word that begins a definition (`let`, `set`, `put`,
  `define`, `we`, `write`, `denote`, `fix`): `Let $\mathcal C$ denote the set of
  copulas, and let DISPLAY denote …`. A binder at the start of the sentence (`For
  $x\in A$,`) is the binder of each part;
* a part after `, and` that is a formula continues the verb of the part before it:
  `For a NOUN $C$, we write $C^\top(u,v)\coloneqq C(v,u)$, and $h_C$ for the NAME of
  $C$.` is `… we write …` twice;
* `, where $S$ is the WORDS.` at the end: the notation `We write $S$ for the WORDS.`,
  made before the rest of the sentence;
* `We [further] consider WORDS of a NOUN $x$, DISPLAY`: the definitions of the display
  for every NOUN $x$, as `For a NOUN $x$, set DISPLAY`. The words name what is defined. -/

/-- The words that begin a definition. -/
def coordStarts : List Codes :=
  [w!"let", w!"set", w!"put", w!"define", w!"we", w!"write", w!"denote", w!"fix"]

/-- The verbs that a formula after `, and` continues. -/
def coordVerbs : List (List Codes) :=
  [[w!"we", w!"write"], [w!"let", w!"us", w!"write"], [w!"we", w!"set"], [w!"set"], [w!"let"],
   [w!"put"], [w!"we", w!"put"], [w!"define"], [w!"write"]]

/-- The lower-case word of a token of the sentence's own text. -/
def textWord (t : PTok) : Option Codes :=
  if t.math then none else match t.tok with
    | .word w => some (lower w)
    | _ => none

def isTextComma (t : PTok) : Bool := !t.math && t.tok == .punct 44

/-- A token that begins a formula or a display. -/
def opensMath (t : PTok) : Bool :=
  match t.tok with
  | .mopen => true
  | .begin e => Lex.wDisplayEnvs.contains e
  | _ => false

/-- Each token of a sentence with the token before it and the two after it. -/
def windows (prev : Option PTok) : List PTok → List (Option PTok × PTok × Option PTok × Option PTok)
  | [] => []
  | t :: rest => (prev, t, rest.head?, (rest.drop 1).head?) :: windows (some t) rest

/-- Split at the positions of `, and` that begin a part: before a word that begins a
definition, or before a formula. -/
def coordSegments (ts : List PTok) : List (List PTok) :=
  let cuts := (windows none ts).map fun (_, a, b, c) =>
    match b, c with
    | some b, some c =>
      isTextComma a && textWord b == some w!"and" && ((textWord c).any coordStarts.contains || opensMath c)
    | _, _ => false
  -- (the `and` after a cut is dropped with it)
  let (segs, cur, _) := (ts.zip cuts).foldl (fun (acc : List (List PTok) × List PTok × Bool) (t, cut) =>
      let (segs, cur, skip) := acc
      if cut then (cur.reverse :: segs, [], true)
      else if skip then (segs, cur, false)
      else (segs, t :: cur, false)) ([], [], false)
  (cur.reverse :: segs).reverse

/-- The binder at the start of a part (`For $x\in A$,`: up to the first comma of the
text), and the rest. -/
def leadingBinder (ts : List PTok) : List PTok × List PTok :=
  match ts.head? >>= textWord with
  | some w =>
    if w != w!"for" then ([], ts) else
    match ts.findIdx? isTextComma with
    | some k => (ts.take (k + 1), ts.drop (k + 1))
    | none => ([], ts)
  | none => ([], ts)

/-- The verb before the first formula of a part (`we write`, `set`, `let`), if it is one
that a later formula may continue. -/
def leadingVerb (ts : List PTok) : List PTok :=
  let ws := ts.takeWhile fun t => (textWord t).isSome
  if coordVerbs.contains (ws.filterMap textWord) && (ts.drop ws.length).head?.any opensMath then ws else []

/-- `, where $S$ is the WORDS` at the end of the sentence (before its period): the rest
of the sentence and the notation `We write $S$ for the WORDS.` -/
def whereNotation (ts : List PTok) : Option (List PTok × List PTok) := do
  -- the end of a display whose last token is a comma
  let displayComma (prev : Option PTok) (a : PTok) : Bool :=
    (match a.tok with | .finish e => Lex.wDisplayEnvs.contains e | _ => false) &&
      prev.any fun b => b.tok == .punct 44 || b.tok == .msym 44
  -- the last comma of the text that is followed by `where` and a formula (or the comma
  -- that ends a display before them)
  let hits := ((windows none ts).zipIdx.filter fun ((prev, a, b, c), _) =>
      match b, c with
      | some b, some c => (isTextComma a || displayComma prev a) && textWord b == some w!"where" && c.tok == .mopen
      | _, _ => false)
  let ((prev, a, _, _), k) ← hits.getLast?
  let tail := ts.drop (k + 2)
  -- the formula, then `is the|a|an WORDS.`
  let fm := tail.takeWhile fun t => t.math
  let rest := tail.drop fm.length
  -- (the name may contain formulas: `the binomial distribution with parameters $n$ and $p$`)
  match rest.getLast? with
  | some p =>
    let name := rest.dropLast
    let words := name.filterMap textWord
    let d := (words[1]?).getD []
    if fm.isEmpty || words.length < 3 || (name.head? >>= textWord) != some w!"is" ||
      !(d == w!"the" || d == w!"a" || d == w!"an") || p.tok != .punct 46 || p.math then none else
    let nt := [⟨.word w!"we", a.pos, false⟩, ⟨.word w!"write", a.pos, false⟩] ++ fm ++
      [⟨.word w!"for", a.pos, false⟩] ++ (name.drop 1) ++ [p]
    -- (the rest ends with a period: in its display, if a display ended with the comma)
    let rest := match prev with
      | some b => if displayComma prev a then ts.take (k - 1) ++ [{ b with tok := .msym 46 }, a]
        else ts.take k ++ [⟨.punct 46, a.pos, false⟩]
      | none => ts.take k ++ [⟨.punct 46, a.pos, false⟩]
    some (rest, nt)
  | none => none

/-- `We [further|also] consider WORDS of a|an NP, DISPLAY …` as `For a|an NP, set DISPLAY …`
(the noun phrase `NP` with its variable, `a copula $C$`, `a distribution $\nu$ on
$\mathbb N_0$`, ends at the comma before the display). -/
def considerAsSet (ts : List PTok) : Option (List PTok) := do
  let ws := ts.takeWhile fun t => (textWord t).isSome
  let words := ws.filterMap textWord
  let start ← if words.head? != some w!"we" then none
    else if words[1]? == some w!"consider" then some 2
    else if (words[1]? == some w!"further" || words[1]? == some w!"also") && words[2]? == some w!"consider" then some 3
    else none
  -- the last `of a|an` among the words, then the noun phrase up to a comma before a display
  let k ← (List.range ws.length).reverse.find? fun i =>
    i ≥ start && words[i]? == some w!"of" && (words[i + 1]? == some w!"a" || words[i + 1]? == some w!"an")
  let after := ts.drop (k + 1)
  let hit ← ((windows none after).zipIdx.find? fun ((_, a, b, _), _) =>
    isTextComma a && b.any opensMath)
  let j := hit.2
  let np := after.take j
  let c ← after[j]?
  if !(np.any fun t => t.math) then none else
  let pos := (ts.head?.map (·.pos)).getD 0
  some ([⟨.word w!"for", pos, false⟩] ++ np ++ [c, ⟨.word w!"set", c.pos, false⟩] ++ after.drop (j + 1))

/-- The sentences that a sentence of several parts is made of, if each of them is read
(see above). -/
def partsOfAt : Nat → Sentence → Option (List Sentence)
  | fuel, s => do
  let parses (ts : List PTok) : Bool := (parseSentence { s with toks := ts }).isSome
  -- (a part that is a sentence, or, with fuel left, the sentences it is made of)
  let accept (ts : List PTok) : Option (List (List PTok)) :=
    if parses ts then some [ts] else
    match fuel with
    | 0 => none
    | f + 1 => (partsOfAt f { s with toks := ts }).map (·.map (·.toks))
  -- `Let $(a_n)$ be a sequence such that $\sum a_n$ converges.`: the binder, then the
  -- hypothesis `Suppose that $\sum a_n$ converges.` (a condition that is a clause)
  let suchThat : Option (List (List PTok)) := do
    if (s.toks.head? >>= textWord) != some w!"let" then none
    let k ← (List.range s.toks.length).find? fun i =>
      (s.toks[i]? >>= textWord) == some w!"such" && (s.toks[i + 1]? >>= textWord) == some w!"that"
    let pos := (s.toks[k]?.map (·.pos)).getD 0
    let pre := (s.toks.take k).reverse.dropWhile isTextComma |>.reverse
    let p1 := pre ++ [⟨.punct 46, pos, false⟩]
    let p2 := [⟨.word w!"suppose", pos, false⟩, ⟨.word w!"that", pos, false⟩] ++ s.toks.drop (k + 2)
    if parses p1 && parses p2 then some [p1, p2] else none
  if let some ps := suchThat then return ps.map fun ts => { s with toks := ts }
  -- `Let $V$ be a vector space, let $v_1,\ldots,v_n\in V$, and suppose that CLAUSE.`: the
  -- binders, then the hypothesis `Suppose that CLAUSE.` (`assume`, with or without `that`)
  let andSuppose : Option (List (List PTok)) := do
    if (s.toks.head? >>= textWord) != some w!"let" then none
    let k ← (List.range s.toks.length).find? fun i =>
      (s.toks[i]? >>= textWord) == some w!"and" &&
        ((s.toks[i + 1]? >>= textWord) == some w!"suppose" || (s.toks[i + 1]? >>= textWord) == some w!"assume")
    let pos := (s.toks[k]?.map (·.pos)).getD 0
    let pre := (s.toks.take k).reverse.dropWhile isTextComma |>.reverse
    let p1 := pre ++ [⟨.punct 46, pos, false⟩]
    let p2 := s.toks.drop (k + 1)
    if parses p1 && parses p2 then some [p1, p2] else none
  if let some ps := andSuppose then return ps.map fun ts => { s with toks := ts }
  -- `Let $f\colon[a,b]\to\mathbb{R}$ be continuous on $[a,b]$ and differentiable on $(a,b)$.`,
  -- `… be continuous at $0$`: the map, then the hypothesis `Suppose that $f$ is continuous on
  -- $[a,b]$ and …`
  let sigOn : Option (List (List PTok)) := do
    if (s.toks.head? >>= textWord) != some w!"let" then none
    -- (the signature after a `let`, the first or a later one: `Let $a<b$ and let $f\colon…$ be …`)
    let sigAt (j : Nat) : Bool :=
      (s.toks[j]?.map (·.tok == .mopen)).getD false && j > 0 && (s.toks[j - 1]? >>= textWord) == some w!"let" &&
        ((s.toks.drop (j + 1)).takeWhile (·.tok != .mclose)).any fun t => t.tok == .cmd w!"colon" || t.tok == .msym 58
    let j ← (List.range s.toks.length).find? sigAt
    let t1 ← s.toks[j]?
    let body := (s.toks.drop (j + 1)).takeWhile (·.tok != .mclose)
    let k := j + 1 + body.length
    let ci ← body.findIdx? fun t => t.tok == .cmd w!"colon" || t.tok == .msym 58
    let name := body.take ci
    if name.isEmpty then none
    if (s.toks[k + 1]? >>= textWord) != some w!"be" then none
    let rest := s.toks.drop (k + 2)
    let first ← rest.head? >>= textWord
    if [w!"a", w!"an", w!"the"].contains first then none
    if !(rest.any fun t => textWord t == some w!"on" || textWord t == some w!"at") then none
    let pos := t1.pos
    let w (c : Codes) : PTok := ⟨.word c, pos, false⟩
    let p1 := s.toks.take (k + 1) ++ [w w!"be", w w!"a", w w!"function", ⟨.punct 46, pos, false⟩]
    let p2 := [w w!"suppose", w w!"that", t1] ++ name ++ [⟨.mclose, pos, true⟩, w w!"is"] ++ rest
    if parses p1 && parses p2 then some [p1, p2] else
    -- (`… differentiable on $(a,b)$ with $f(a)=f(b)$`: the condition, a hypothesis of its own)
    let wi ← rest.findIdx? fun t => textWord t == some w!"with"
    let p2 := [w w!"suppose", w w!"that", t1] ++ name ++ [⟨.mclose, pos, true⟩, w w!"is"] ++ rest.take wi ++ [⟨.punct 46, pos, false⟩]
    let p3 := [w w!"suppose", w w!"that"] ++ rest.drop (wi + 1)
    if parses p1 && parses p2 && parses p3 then some [p1, p2, p3] else none
  if let some ps := sigOn then return ps.map fun ts => { s with toks := ts }
  -- `Let $G$ be a finite group whose order is divisible by $p$.`: the binder, then the
  -- hypothesis `Suppose that the order of $G$ is divisible by $p$.`
  let whose : Option (List (List PTok)) := do
    if (s.toks.head? >>= textWord) != some w!"let" then none
    let toks : List PTok := s.toks
    let k : Nat ← (List.range toks.length).find? fun i => (toks[i]? >>= textWord) == some w!"whose"
    let pos : Nat := (toks[k]?.map fun (t : PTok) => t.pos).getD 0
    -- (the variable: the formula before `whose`, or the one after `let`)
    let mathAt (i : Nat) : Option (List PTok) := do
      let t : PTok ← toks[i]?
      if t.tok != Tok.mopen then none
      let body := (toks.drop (i + 1)).takeWhile fun (u : PTok) => u.tok != Tok.mclose
      let close : PTok ← toks[i + 1 + body.length]?
      some ([t] ++ body ++ [close])
    let before : Option (List PTok) := do
      let t : PTok ← toks[k - 1]?
      if t.tok != Tok.mclose || k == 0 then none
      let j ← (List.range (k - 1)).reverse.find? fun i => (toks[i]?.map fun (u : PTok) => u.tok) == some Tok.mopen
      mathAt j
    -- (the variable of the last binder before it: `let $G$ be …`)
    let lastBe : Option (List PTok) := do
      let i ← (List.range k).reverse.find? fun i =>
        match mathAt i with
        | some m => (toks[i + m.length]? >>= textWord) == some w!"be"
        | none => false
      mathAt i
    let v ← before <|> lastBe
    let after : List PTok := toks.drop (k + 1)
    let j : Nat ← after.findIdx? fun t => textWord t == some w!"is" || textWord t == some w!"are"
    if j == 0 then none
    let pre : List PTok := ((toks.take k).reverse.dropWhile isTextComma).reverse
    let p1 : List PTok := pre ++ [⟨.punct 46, pos, false⟩]
    let p2 : List PTok := [⟨.word w!"suppose", pos, false⟩, ⟨.word w!"that", pos, false⟩, ⟨.word w!"the", pos, false⟩] ++
      after.take j ++ [⟨.word w!"of", pos, false⟩] ++ v ++ after.drop j
    if parses p1 && parses p2 then some [p1, p2] else none
  if let some ps := whose then return ps.map fun ts => { s with toks := ts }
  -- `Let $G$ be a connected graph in which every vertex has even degree.`: the binder,
  -- then `Suppose that every vertex of $G$ has even degree.`
  let inWhich : Option (List (List PTok)) := do
    if (s.toks.head? >>= textWord) != some w!"let" then none
    let toks : List PTok := s.toks
    let k : Nat ← (List.range toks.length).find? fun i =>
      (toks[i]? >>= textWord) == some w!"in" && (toks[i + 1]? >>= textWord) == some w!"which"
    let pos : Nat := (toks[k]?.map fun (t : PTok) => t.pos).getD 0
    let mathAt (i : Nat) : Option (List PTok) := do
      let t : PTok ← toks[i]?
      if t.tok != Tok.mopen then none
      let body := (toks.drop (i + 1)).takeWhile fun (u : PTok) => u.tok != Tok.mclose
      let close : PTok ← toks[i + 1 + body.length]?
      some ([t] ++ body ++ [close])
    let i ← (List.range k).reverse.find? fun i =>
      match mathAt i with
      | some m => (toks[i + m.length]? >>= textWord) == some w!"be"
      | none => false
    let v ← mathAt i
    let after : List PTok := toks.drop (k + 2)
    -- (`every vertex` is of the object: `every vertex of $G$`)
    let q ← after.head? >>= textWord
    if ![w!"every", w!"each", w!"no", w!"all"].contains q then none
    let nounLen := ((after.drop 1).takeWhile fun (t : PTok) => (textWord t).isSome &&
      ![w!"has", w!"have", w!"is", w!"are", w!"lies", w!"belongs"].contains ((textWord t).getD [])).length
    if nounLen == 0 then none
    -- (`has even degree`: `is of even degree`, as after a formula)
    let tail0 := after.drop (1 + nounLen)
    let tail : List PTok := match tail0 with
      | verb :: nxt :: more =>
        let vw := textWord verb
        let quantity := [w!"even", w!"odd", w!"finite", w!"infinite", w!"prime", w!"positive", w!"degree", w!"order",
          w!"characteristic", w!"dimension", w!"index"]
        if (vw == some w!"has" || vw == some w!"have") && ((textWord nxt).map quantity.contains).getD false then
          [⟨.word (if vw == some w!"has" then w!"is" else w!"are"), verb.pos, false⟩, ⟨.word w!"of", verb.pos, false⟩, nxt] ++ more
        else tail0
      | _ => tail0
    let clause : List PTok := after.take (1 + nounLen) ++ [⟨.word w!"of", pos, false⟩] ++ v ++ tail
    let pre : List PTok := ((toks.take k).reverse.dropWhile isTextComma).reverse
    let p1 : List PTok := pre ++ [⟨.punct 46, pos, false⟩]
    let p2 : List PTok := [⟨.word w!"suppose", pos, false⟩, ⟨.word w!"that", pos, false⟩] ++ clause
    if parses p1 && parses p2 then some [p1, p2] else none
  if let some ps := inWhich then return ps.map fun ts => { s with toks := ts }
  -- `Let $G$ and $H$ be groups, with $H$ abelian.`: the binders, then `Suppose that $H$ is
  -- abelian.` (`, with $x$ WORDS [and $y$ WORDS]`, or `, with $φ$`)
  let withAbs : Option (List (List PTok)) := do
    if (s.toks.head? >>= textWord) != some w!"let" then none
    let toks : List PTok := s.toks
    let k ← (List.range toks.length).reverse.find? fun i =>
      (toks[i]?.map isTextComma).getD false && (toks[i + 1]? >>= textWord) == some w!"with" &&
        (toks[i + 2]?.map fun (t : PTok) => t.tok == Tok.mopen).getD false
    let pos : Nat := (toks[k]?.map fun (t : PTok) => t.pos).getD 0
    let w (c : Codes) : PTok := ⟨.word c, pos, false⟩
    -- (the parts `$x$ WORDS`, joined by `and` or `,`)
    let rec parts : Nat → List PTok → List (List PTok) → Option (List (List PTok))
      | 0, _, _ => none
      | f + 1, ts, acc => do
        let t ← ts.head?
        if t.tok != Tok.mopen then none
        let body := (ts.drop 1).takeWhile fun (u : PTok) => u.tok != Tok.mclose
        let cls ← ts[1 + body.length]?
        let rest := ts.drop (2 + body.length)
        let words := rest.takeWhile fun (u : PTok) => !u.math && (match u.tok with
          | .word v => Grammar.lower v != w!"and"
          | .punct 45 => true
          | _ => false)
        let part := [t] ++ body ++ [cls] ++ (if words.isEmpty then [] else [w w!"is"] ++ words)
        let rest := rest.drop words.length
        match rest with
        | [] => some ((part :: acc).reverse)
        | [u] => if !u.math && u.tok == .punct 46 then some ((part :: acc).reverse) else none
        | u :: v :: more =>
          if !u.math && textWord u == some w!"and" then parts f (v :: more) (part :: acc)
          else if isTextComma u then parts f ((if textWord v == some w!"and" then more else v :: more)) (part :: acc)
          else none
    let ps ← parts 6 (toks.drop (k + 2)) []
    -- (a part without words is a condition alone; with several parts, each has its words)
    if ps.length > 1 && ps.any (fun p => !(p.any fun (u : PTok) => textWord u == some w!"is")) then none
    let pre : List PTok := toks.take k
    let p1 : List PTok := pre ++ [⟨.punct 46, pos, false⟩]
    let p2 : List PTok := [w w!"suppose", w w!"that"] ++ (ps.intersperse [w w!"and"]).flatten ++ [⟨.punct 46, pos, false⟩]
    let a1 ← accept p1
    let a2 ← accept p2
    some (a1 ++ a2)
  if let some ps := withAbs then return ps.map fun ts => { s with toks := ts }
  -- `Assume that $a>0$ and let $n$ be …`: the hypothesis, then the binder
  let assumeLet : Option (List (List PTok)) := do
    let w0 ← s.toks.head? >>= textWord
    if w0 != w!"assume" && w0 != w!"suppose" then none
    let toks : List PTok := s.toks
    let k ← (List.range toks.length).find? fun i =>
      (toks[i]? >>= textWord) == some w!"and" && (toks[i + 1]? >>= textWord) == some w!"let"
    let pos : Nat := (toks[k]?.map fun (t : PTok) => t.pos).getD 0
    let pre : List PTok := ((toks.take k).reverse.dropWhile isTextComma).reverse
    let p1 : List PTok := pre ++ [⟨.punct 46, pos, false⟩]
    let p2 : List PTok := toks.drop (k + 1)
    let a1 ← accept p1
    let a2 ← accept p2
    some (a1 ++ a2)
  if let some ps := assumeLet then return ps.map fun ts => { s with toks := ts }
  -- `For a group $G$, let $H$ be …`, `Given $x\in A$, let …`: in a result or a proof, the
  -- object (`Let $G$ be a group.`), then the rest
  let forLet : Option (List (List PTok)) := do
    if s.ctx.kind == .text then none
    let w0 ← s.toks.head? >>= textWord
    if w0 != w!"for" && w0 != w!"given" then none
    let toks : List PTok := s.toks
    let k ← (List.range toks.length).find? fun i =>
      (toks[i]?.map isTextComma).getD false && ((toks[i + 1]? >>= textWord).map ([w!"let", w!"we"].contains ·)).getD false
    let mid : List PTok := (toks.take k).drop 1
    let pos : Nat := (toks[k]?.map fun (t : PTok) => t.pos).getD 0
    let w (c : Codes) : PTok := ⟨.word c, pos, false⟩
    let first ← mid.head?
    let binder : List PTok ← if first.tok == Tok.mopen then some ([w w!"let"] ++ mid ++ [⟨.punct 46, pos, false⟩]) else do
      let a ← textWord first
      if ![w!"a", w!"an", w!"any", w!"some"].contains a then none
      -- (the variable: the first formula, a letter)
      let i ← mid.findIdx? fun (t : PTok) => t.tok == Tok.mopen
      let body := (mid.drop (i + 1)).takeWhile fun (u : PTok) => u.tok != Tok.mclose
      let var := (mid.drop i).take (body.length + 2)
      some ([w w!"let"] ++ var ++ [w w!"be", w (if a == w!"an" then w!"an" else w!"a")] ++ (mid.take i).drop 1 ++
        mid.drop (i + body.length + 2) ++ [⟨.punct 46, pos, false⟩])
    let rest : List PTok := toks.drop (k + 1)
    let a1 ← accept binder
    let a2 ← accept rest
    some (a1 ++ a2)
  if let some ps := forLet then return ps.map fun ts => { s with toks := ts }
  -- `Let $Q\in\mathbb{R}^{n\times m}$ have orthonormal columns.`: the binder, then `Suppose
  -- that $Q$ has orthonormal columns.` (`have`, `satisfy`, `contain`, `admit`, `lie`, `belong`)
  let letVerb : Option (List (List PTok)) := do
    let toks : List PTok := s.toks
    let verbs : List (Codes × Codes) := [(w!"have", w!"has"), (w!"satisfy", w!"satisfies"), (w!"contain", w!"contains"),
      (w!"admit", w!"admits"), (w!"lie", w!"lies"), (w!"belong", w!"belongs")]
    let closeAfter (i : Nat) : Nat := i + 2 + ((toks.drop (i + 2)).takeWhile fun (u : PTok) => u.tok != Tok.mclose).length
    let i ← (List.range toks.length).find? fun i =>
      (toks[i]? >>= textWord) == some w!"let" && (toks[i + 1]?.map fun (t : PTok) => t.tok == Tok.mopen).getD false &&
        ((toks[closeAfter i + 1]? >>= textWord).map fun v => (verbs.lookup v).isSome).getD false
    let k := closeAfter i
    let body : List PTok := (toks.drop (i + 2)).take (k - i - 2)
    let v ← toks[k + 1]? >>= textWord
    let third ← verbs.lookup v
    -- (the variable: the letter before `\in`, `\colon`, `:` or `\subseteq`)
    let cut ← body.findIdx? fun (t : PTok) => t.tok == .cmd w!"in" || t.tok == .cmd w!"colon" || t.tok == .msym 58 || t.tok == .cmd w!"subseteq"
    if cut == 0 || (body.take cut).any (fun (t : PTok) => t.tok == .msym 44) then none
    let opn ← toks[i + 1]?
    let pos : Nat := (toks[k + 1]?.map fun (t : PTok) => t.pos).getD 0
    let w (c : Codes) : PTok := ⟨.word c, pos, false⟩
    let p1 : List PTok := toks.take (k + 1) ++ [⟨.punct 46, pos, false⟩]
    let p2 : List PTok := [w w!"suppose", w w!"that", opn] ++ body.take cut ++ [⟨.mclose, pos, true⟩, w third] ++ toks.drop (k + 2)
    let a1 ← accept p1
    let a2 ← accept p2
    some (a1 ++ a2)
  if let some ps := letVerb then return ps.map fun ts => { s with toks := ts }
  let (ts, pre) := match whereNotation s.toks with
    | some (rest, nt) => (rest, [nt])
    | none => (s.toks, [])
  let consider := considerAsSet ts
  let ts := consider.getD ts
  let segs := coordSegments ts
  if segs.length < 2 && pre.isEmpty && consider.isNone then none else
  let (binder, main0) := leadingBinder (segs.head?.getD [])
  let verb := leadingVerb main0
  let n := segs.length
  let parts ← (segs.zipIdx.mapM fun (seg, i) => do
    -- (each part but the last ends with a period)
    let seg := if i + 1 < n then
      match seg.getLast? with
      | some t => seg ++ [⟨.punct 46, t.pos, false⟩]
      | none => seg
      else seg
    if i == 0 then (if parses seg then some seg else none) else
    let cands : List (List PTok) :=
      if seg.head?.any opensMath then
        (if verb.isEmpty then [] else (if binder.isEmpty then [] else [binder ++ verb ++ seg]) ++ [verb ++ seg])
      else (if binder.isEmpty then [] else [binder ++ seg]) ++ [seg]
    cands.find? parses)
  let all := pre ++ parts
  if all.length < 2 && consider.isNone then none else
  some (all.map fun ts => { s with toks := ts })

/-- The sentences a sentence is made of (see `partsOfAt`): a part may itself be made of
sentences, once. -/
def partsOf (s : Sentence) : Option (List Sentence) := partsOfAt 1 s

end Grammar
end Leanify
