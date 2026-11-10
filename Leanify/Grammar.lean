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

def formula (cs : List Chunk) : Option (MT × List Chunk) := do
  let (ts, rest) ← mathChunk cs
  let m ← Math.parseDisplay ts
  some (m, rest)

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
      ((kw [w!"relatively", w!"prime"] ws <|> kw [w!"coprime"] ws).map (w!"coprime", ·))
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
    else .chain (.app (.id w!"\\gcd") [.tuple [a, b]]) [(.eq, .num 1)]
  let name (v : List MTok) : List MTok := v.takeWhile fun t => (Math.relOf t).isNone
  let conds ← ps.mapM fun p => do
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
    | f + 1, .id n :: r => (n :: ·) <$> names0 f r
    | f + 1, .cmd n :: r =>
      match hatName (.cmd n :: r) with
      | some (v, r') => (v :: ·) <$> names0 f r'
      | none => if Math.greekNames.contains n then (([92] ++ n) :: ·) <$> names0 f r else none
    | _, _ => none
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

/-- A binder: `x\in A`, or a bound on one real variable (`c>0`) or several (`a,b>0`). -/
def binderMath (ts : List MTok) : Option (List Codes × MT) :=
  binderIn ts <|> boundBinder ts <|> boundBinders ts

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
    | .m _ => chunksUntil stop cs (c :: acc)
    | _ => none

/-- Citations: `Lemma~\ref{l}`, `Theorem~\ref{l}`, `Claim~\ref{l}`, `\eqref{l}`, `\cref{l}`. -/
def cite : List Chunk → Option (Codes × List Chunk)
  | .r .eqref l :: cs => some (l, cs)
  | .w v :: .r .ref l :: cs =>
    if [w!"lemma", w!"theorem", w!"corollary", w!"proposition", w!"equation", w!"section", w!"claim",
        w!"fact", w!"observation", w!"definition", w!"remark"].contains v then
      some (l, cs) else none
  | _ => none

def isEnd : List Chunk → Bool
  | [.p 46] => true
  | _ => false

/-- Discourse markers: they connect sentences and assert nothing. -/
def wMarkers : List (List Codes) :=
  [[w!"to", w!"make", w!"this", w!"precise"], [w!"consequently"], [w!"hence"], [w!"in", w!"particular"],
   [w!"then"], [w!"thus"], [w!"therefore"], [w!"indeed"], [w!"moreover"], [w!"furthermore"],
   [w!"in", w!"addition"], [w!"finally"], [w!"again"], [w!"conversely"], [w!"similarly"],
   [w!"in", w!"other", w!"words"], [w!"that", w!"is"], [w!"we", w!"have"], [w!"it", w!"follows", w!"that"],
   [w!"we", w!"obtain"], [w!"note", w!"that"], [w!"we", w!"see", w!"that"], [w!"more", w!"precisely"],
   [w!"equivalently"], [w!"also"], [w!"in", w!"both", w!"cases"], [w!"in", w!"either", w!"case"],
   [w!"in", w!"all", w!"cases"], [w!"in", w!"each", w!"case"], [w!"in", w!"any", w!"case"],
   [w!"by", w!"the", w!"induction", w!"hypothesis"], [w!"by", w!"the", w!"inductive", w!"hypothesis"],
   [w!"by", w!"induction", w!"hypothesis"], [w!"by", w!"the", w!"induction", w!"assumption"]]

/-- Discourse markers have no content of their own (`For the minimum` sets a topic). -/
inductive Topic where
  | none | maximum | minimum
  deriving DecidableEq, Repr, Lean.ToExpr

def marker (cs : List Chunk) : Topic × List Chunk :=
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
  if names.any (fun n => n.isEmpty || n.any fun t => match t with
      | .id _ | .digit _ | .sym 95 | .lb | .rb => false
      | .cmd c => !Math.greekNames.contains c
      | _ => true) then none
  else some (names.map (· ++ suffix))

/-- The variables of `$x$ and $y$`, `$x$, $y$ and $z$` (each formula the name of one
variable), joined as `x,y,z`; any other formula is returned as it is. -/
def joinedVars (cs : List Chunk) : Option (List MTok × List Chunk) := do
  let (ts, r) ← mathChunk cs
  let isName (n : List MTok) : Bool := !n.isEmpty && n.all fun t => match t with
    | .id _ | .digit _ | .sym 95 | .lb | .rb => true
    | .cmd c => Math.greekNames.contains c
    | _ => false
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
      | [.m ts], _ => ((seqBound ts).map fun _ => ([ts], [], r')) <|> (splitVars ts).map (·, [], r')
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
    let (np, r') := npUpTo (r.length + 1) r []
    match np.head?, np.getLast? with
    | some (.w _), some (.m [.id _]) | some (.w _), some (.m [.cmd _]) => some (.noun np, r')
    -- `every integer $n\ge1$`, `every integer $n$ with $n\ge1$`: one variable with a bound
    | some (.w _), some (.m ts) =>
      match binderMath ts, hatName ts with
      | some ([_], _), _ | _, some (_, []) => some (.noun np, r')
      | _, _ => none
    | _, _ => none)

/-- Further binders: `and every NP $y$`, `and $y\in B$`. -/
def everyMore : Nat → List Chunk → List Bind → List Bind × List Chunk
  | 0, cs, acc => (acc.reverse, cs)
  | f + 1, cs, acc =>
    let next := (kw [w!"and", w!"every"] cs <|> kw [w!"and", w!"each"] cs <|> kw [w!"and", w!"all"] cs <|>
      (do let r ← kw [w!"and"] cs; match r with | .m _ :: _ => some r | _ => none) <|>
      -- `For every $k$, every $N$ and every $x$`
      (do let r ← punct 44 cs; kw [w!"every"] r <|> kw [w!"each"] r <|> kw [w!"and", w!"every"] r))
    match next.bind everyOne with
    | some (b, r) => everyMore f r (b :: acc)
    | none => (acc.reverse, cs)

/-- The binders after `for every|each|all`: one, or several joined by `and [every]`. -/
def everyBinders (r : List Chunk) : Option (Bind × List Chunk) :=
  -- (a binder with conditions is itself several: they are flattened)
  let flat (b : Bind) : List Bind := match b with | .many bs => bs | _ => [b]
  match everyOne r with
  | some (b, r') =>
    match everyMore 4 r' [] with
    | ([], _) => some (b, r')
    | (bs, r'') => some (.many ((b :: bs).flatMap flat), r'')
  | none => none

/-- `positive integers` after the variables `ts` of `$a,b$ are` (`be`), possibly with
conditions (`with $a<b$`): a binder for each variable (a sequence `x_1,\ldots,x_n` is one),
then the conditions. -/
def pluralNoun (ts : List MTok) (r : List Chunk) : Option (Bind × List Chunk) := do
  let vars ← ((seqBound ts).map fun _ => [ts]) <|> splitVars ts
  -- (a singular noun is read where its variable is)
  if (kw [w!"a"] r).isSome || (kw [w!"an"] r).isSome then none else
  let ws := r.takeWhile fun c => match c with
    | .w w => w != w!"with" && w != w!"such" && w != w!"then" && w != w!"and"
    | .p 45 => true
    | _ => false
  let r1 := r.drop ws.length
  -- `distinct`, `relatively prime`: a condition on all of them
  let (ws, ps) := collectiveWords 8 ws
  let together : List Bind ← if ps.isEmpty then some [] else (collectiveCond ps vars).map ([.ifCond ·])
  -- `$v,w\in A$ are distinct`: the variables of their domain, together
  if ws.isEmpty then
    if together.isEmpty then none else
    let (vs, d) ← binderMath ts
    return (.many (.every vs d :: together), r1)
  let nouns := vars.map fun v => Bind.noun (ws ++ [.m v])
  match withConds r1 with
  | some (c, r2) => some (.many (nouns ++ together ++ [.ifCond c]), r2)
  | none => some (.many (nouns ++ together), r1)

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
              let v ← match ts with | [.id v] => some v | _ => none
              let r2 ← kw [w!"is", w!"a"] r1 <|> kw [w!"is", w!"an"] r1
              let ws := r2.takeWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
              if ws.isEmpty || (punct 44 (r2.drop ws.length)).isNone then none
              else some (.hyp (.noun (ws ++ [.m [.id v]])), r2.drop ws.length)) <|>
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
              some (.ifCond m, r'))
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
  /-- `there are infinitely many NPs [such that CLAUSE]`, `CLAUSE for infinitely many NPs`:
  the numbers the noun phrase (and the clause) describe are not finitely many. -/
  | infinitelyMany (np : List Chunk) (c : Option Clause)
  /-- The false statement (`This is a contradiction.`): under hypotheses, that they
  cannot all hold. -/
  | absurd
  /-- `the statement holds for $E$`, in the proof of a result: the statement of the
  result, with the variable of the induction replaced by `E` (the hypothesis of an
  induction, or its conclusion for `n+1`). -/
  | stmtAt (e : MT)
  /-- `the statement holds for all smaller values [of $n$]`, `… for all integers less than
  $n$`: the statement for every value of the variable of the induction below it (`v`: the
  variable, if the sentence names it). -/
  | stmtBelow (v : Option Codes)
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
  deriving Repr, Inhabited

def subj (cs : List Chunk) : Option (Subj × List Chunk) :=
  match cs with
  | .m _ :: _ => do let (m, r) ← formula cs; some (.math m, r)
  | .w v :: r =>
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
    ([w!"lipschitz", w!"continuous"], [w!"lipschitz"]), same [w!"lipschitz"],
    same [w!"strictly", w!"increasing"], same [w!"strictly", w!"decreasing"],
    same [w!"strictly", w!"convex"], same [w!"strictly", w!"concave"],
    same [w!"nondecreasing"], ([w!"non", w!"decreasing"], [w!"nondecreasing"]),
    same [w!"nonincreasing"], ([w!"non", w!"increasing"], [w!"nonincreasing"]),
    same [w!"nonnegative"], ([w!"non", w!"negative"], [w!"nonnegative"]),
    same [w!"nonpositive"], ([w!"non", w!"positive"], [w!"nonpositive"]),
    same [w!"positive"], same [w!"negative"],
    same [w!"compact"], same [w!"convex"], same [w!"concave"], same [w!"centrally", w!"symmetric"],
    same [w!"continuous"], same [w!"differentiable"], same [w!"injective"], same [w!"bounded"],
    same [w!"closed"], same [w!"open"], same [w!"connected"] ]

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
  wAdjectives.findSome? fun (pat, a) => (kwH pat cs).map (a, ·)

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

/-- The chunks up to the end of a clause. -/
def untilClauseEnd : Nat → List Chunk → List Chunk → Option (List Chunk × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc =>
    -- `and` before a formula starts the next clause (`$7$ is prime and $9$ is …`)
    let nextClause := match cs with | .w w :: .m _ :: _ => w == w!"and" | _ => false
    if clauseEnd cs || (nextClause && !acc.isEmpty) then some (acc.reverse, cs) else
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
      if ws.any (fun c => match c with | .w w => preps.contains (lower w) | _ => false) then none
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
  ((kw [w!"equals"] cs).map (.eq, ·))

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

/-- One clause, without its citations. Must be followed by a clause boundary. -/
def clause (cs : List Chunk) : Option (Clause × List Chunk) :=
  match stmtClause cs with
  | some res => some res
  | none =>
  match asLimit cs with
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
      let cs := match kw [w!"the", w!"function"] cs <|> kw [w!"the", w!"map"] cs <|> kw [w!"the", w!"set"] cs <|>
          kw [w!"the", w!"number"] cs <|> kw [w!"the", w!"class"] cs with
        | some r => r | none => cs
      let (m, r) ← formula cs
      let r1 ← kw [w!"is"] r
      let (adjs, r2) ← adjectiveList 16 r1 []
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
      some (.everyNP np body inner, r4)) <|>
    (do
      let (np, r1) ← chunksUntil [w!"is"] r []
      let r2 ← kw [w!"is"] r1
      let (names, disj, r3) ← notionList r2
      some (.everyIs np names disj, r3))
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
      some (Clause.compare l rel rr, r2)) with
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
      match wordsUntil [w!"of"] 8 r1 [] with
      | some (phrase, r2) => do
        let r3 ← kw [w!"of"] r2
        let (o, r4) ← obj r3
        some (.pred s phrase o, r4)
      | none =>
        -- `$X$ is [not] a|an NP`, `$X$ is [not] ADJ`: the vocabulary's nouns and adjectives
        match s with
        | .math f => do
          let (neg, r2) := match kw [w!"not"] r1 with | some r' => (true, r') | none => (false, r1)
          let (np, r3) ← untilClauseEnd 32 r2 []
          if np.isEmpty then none else some (.isA f np neg, r3)
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
      let (vars, dom, r1) := match kw [w!"for", w!"every"] r <|> kw [w!"for", w!"all"] r with
        | some r' => match mathChunk r' with
          | some (ts, r'') => match binderMath ts with
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
  match (do
      if none_ then none else
      let ws0 := r.takeWhile fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false
      let (ts, r1) ← mathChunk (r.drop ws0.length)
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
          some (Clause.thereIs (.many (nouns ++ [Bind.ifCond φ])) c, r4)
        | none => if clauseEnd r2 then some (Clause.thereIs (.many nouns) (.fact φ), r2) else none
      | none => do
        let r2 ← followingProperty r1 <|> kw [w!"such", w!"that"] r1
        let (c, r3) ← suchThatClauses sub r2
        some (Clause.thereIs (.many nouns) c, r3)) with
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

/-- A clause with its leading citations: `By CITE, ...`, `CITE gives ...`, trailing `by CITE`. -/
def cclause (cs : List Chunk) : Option (CClause × List Chunk) :=
  let (pre, r0) : List Codes × List Chunk :=
    match kw [w!"by"] cs >>= cite with
    | some (l, r) => ([l], optPunct 44 r)
    | none => ([], cs)
  -- CITE gives $φ$
  match cite r0 with
  | some (l, r1) =>
    match kw [w!"gives"] r1 with
    | some r2 => do
      let (m, r3) ← formula r2
      some (⟨pre ++ [l], .fact m, [], []⟩, r3)
    | none => none
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
          let (h, rest) ← clause r
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
      | some (l, r2) => (pre ++ [l], r2)
      | none => (pre, r1)
    -- `…, where $g(x)\coloneqq x-1$ [and $h\coloneqq …$]`
    match punct 44 r2 >>= kw [w!"where"] with
    | some r3 => do
      let (ds, r4) ← whereDefs 4 r3 []
      some (⟨cites, c, bs, ds⟩, r4)
    | none => some (⟨cites, c, bs, []⟩, r2)
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

/-- Clauses separated by `, and` / `, so`, ending with the final period. -/
def clauses : Nat → List Chunk → List CClause → Option (List CClause)
  | 0, _, _ => none
  | f + 1, cs, acc => do
    let (c, r) ← cclause cs
    -- a reason in words only (`…, since the square root is injective.`) asserts nothing
    let r := match punct 44 r >>= kw [w!"since"] with
      | some r' =>
        let ws := r'.takeWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
        if !ws.isEmpty && isEnd (r'.drop ws.length) then r'.drop ws.length else r
      | none => r
    if isEnd r then some (c :: acc).reverse
    else
      -- `, and`, `, so`, `, whereas`, or `and` between two formulas, or `,` before a
      -- formula (`$φ$, $ψ$ and $χ$`)
      let next := (do
        let r' ← punct 44 r
        kw [w!"and"] r' <|> kw [w!"so"] r' <|> kw [w!"whereas"] r' <|>
          (match r' with | .m _ :: _ => some r' | _ => none)) <|> kw [w!"and"] r
      match next with
      | some r'' => clauses f r'' (c :: acc)
      | none => none

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
  match display r1 with
  | some (m, ls, r2) => some (⟨name, m, ls⟩, r2)
  | none => do
    let (m, r2) ← formula r1
    some (⟨name, m, []⟩, r2)

/-- Trailing bibliographic remarks without mathematical content. -/
def trailer (cs : List Chunk) : List Chunk :=
  let cs' := optPunct 44 cs
  match kw [w!"as", w!"given", w!"in"] cs' <|> kw [w!"see"] cs' with
  | some (.r .cite _ :: r) => r
  | _ =>
    match kw [w!"from"] cs' >>= cite with
    | some (_, r) => r
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

/-- Monotonicity of a map: `non-increasing`, `non-decreasing`, `strictly increasing`,
`strictly decreasing`. (A plain `increasing` is ambiguous between the first two
readings, so the grammar does not read it.) -/
inductive Mono where
  | nonincreasing | nondecreasing | increasing | decreasing
  deriving Repr, Inhabited, DecidableEq

/-- The condition of a notion the article defines. -/
inductive NotionCond where
  /-- `$φ$ [for all $u,v\in A$]` -/
  | formula (f : MT) (binds : List Bind)
  /-- `[for every $v\in A$,] the map $x\mapsto e$[, $x\in D$,] is non-increasing` -/
  | mono (binds : List Bind) (map : MT) (mono : Mono)
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
  | defNotion (subj : List Chunk) (name : List Codes) (abbr : List Codes) (cond : NotionCond)
  /-- A notion whose condition the grammar does not read (`We call a copula $C$
  \emph{SI} if its Markov kernel can be chosen such that …`): prose, but its noun
  phrase is the subject of the notions that follow (`$C$ is \emph{LTD} if …`). -/
  | notionSubject (subj : List Chunk)
  /-- `Let $C$ be a NP[, and let $u,v\in A$][, and let $X\coloneqq e$, …].`, `Let
  $a,b\in A$, and let $X\coloneqq e$.`: variables of the rest of the result or proof,
  and definitions local to it. -/
  | assumeAll (binds : List Bind) (defs : List MT)
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
  /-- `Throughout, $p$ and $q$ denote integers.`, `In this paper, the letter $t$ denotes
  an integer.`: wherever one of the letters is bound, it is an integer. -/
  | letters (vars : List Codes)
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

/-- `non-increasing`, `non-decreasing`, `strictly increasing`, `strictly decreasing`. -/
def monoWord (cs : List Chunk) : Option (Mono × List Chunk) :=
  ((kw [w!"non"] cs >>= punct 45 >>= kw [w!"increasing"]).map (Mono.nonincreasing, ·)) <|>
  ((kw [w!"nonincreasing"] cs).map (Mono.nonincreasing, ·)) <|>
  ((kw [w!"non"] cs >>= punct 45 >>= kw [w!"decreasing"]).map (Mono.nondecreasing, ·)) <|>
  ((kw [w!"nondecreasing"] cs).map (Mono.nondecreasing, ·)) <|>
  ((kw [w!"strictly", w!"increasing"] cs).map (Mono.increasing, ·)) <|>
  ((kw [w!"strictly", w!"decreasing"] cs).map (Mono.decreasing, ·))

/-- `for every|all|each $x\in A$`. -/
def forBinder (cs : List Chunk) : Option (Bind × List Chunk) := do
  let r ← kw [w!"for", w!"every"] cs <|> kw [w!"for", w!"all"] cs <|> kw [w!"for", w!"each"] cs
  let (ts, r1) ← mathChunk r
  let (vs, d) ← binderMath ts
  some (.every vs d, r1)

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
    if isEnd r2 then some (NotionCond.formula φ [b]) else none)

/-- A notion defined in the text: `We call a NOUN $x$ NAME [(ABBR)] if COND.`,
`[A NOUN] $x$ is called NAME [(ABBR)] if COND.`, `[A NOUN] $x$ is NAME [(ABBR)] if COND.` -/
def notionDef (cs : List Chunk) : Option Sent :=
  let article (r : List Chunk) := (kw [w!"a"] r <|> kw [w!"an"] r).getD r
  (do
    let r ← kw [w!"we", w!"call"] cs
    let (np, r1) ← nounVar (article r)
    let (name, abbr, r2) ← nameAbbr r1
    let r3 ← kw [w!"if"] r2
    withCond true np name abbr r3) <|>
  (do
    let (np, r1) ← nounVar (article cs)
    let (named, r2) ← ((kw [w!"is", w!"called"] r1 <|> kw [w!"is", w!"said", w!"to", w!"be"] r1).map (true, ·)) <|>
      ((kw [w!"is"] r1).map (false, ·))
    let (name, abbr, r3) ← nameAbbr r2
    let r4 ← kw [w!"if"] r3
    withCond named np name abbr r4)
where
  /-- The notion with its condition, or, when the condition is not read, the
  sentence is plainly a definition (`We call`, `is called`) and its subject is a
  noun phrase, the subject alone. -/
  withCond (named : Bool) (np : List Chunk) (name abbr : List Codes) (r : List Chunk) : Option Sent :=
    match notionCond r with
    | some cond => some (.defNotion np name abbr cond)
    | none =>
      if named && np.length ≥ 2 && (kw [w!"and", w!"only", w!"if"] r).isNone then
        some (.notionSubject np)
      else none

/-- A condition on variables, `$c>0$`, `$0<x\le1$`: a chain of order relations (not a
definition, an equation or a membership). -/
def isCondition : MT → Bool
  | .chain _ rs => !rs.isEmpty && rs.all fun (r, _) => r == .lt || r == .le || r == .gt || r == .ge || r == .ne
  | _ => false

/-- `$x\in A$`, `$c>0$` (a condition), or `$C$ be a|an NP`: the variable of a `let`. -/
def letBinder (cs : List Chunk) : Option (Bind × List Chunk) :=
  (do
    let (ts, r) ← mathChunk cs
    let (vs, d) ← binderMath ts
    -- (`$k\ge3$ be a fixed integer` is a noun phrase, below)
    if (kw [w!"be"] r).isSome then none else
    some (.every vs d, r)) <|>
  -- `$c>0$ be fixed`
  (do
    let (ts, r) ← mathChunk cs
    let r1 ← kw [w!"be", w!"fixed"] r
    let b ← fixBinder ts
    some (b, r1)) <|>
  -- `$u:A\to B$ [be a map|function|field]`: a map of its signature
  (do
    let (ts, r) ← mathChunk cs
    let _ ← Math.parseSig ts
    let r' := (kw [w!"be", w!"a", w!"map"] r <|> kw [w!"be", w!"a", w!"function"] r <|>
      kw [w!"be", w!"a", w!"field"] r <|> kw [w!"be", w!"a", w!"vector", w!"field"] r).getD r
    some (.noun [.w w!"map", .m ts], r')) <|>
  -- `$c>0$`: a condition, assumed like a binder
  (do
    let (ts, r) ← mathChunk cs
    let m ← Math.parseFormula ts
    if (kw [w!"be"] r).isSome then none else
    if isCondition m then some (.ifCond m, r) else none) <|>
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
        | _, _ => none
    let r1 ← kw [w!"be", w!"a"] r <|> kw [w!"be", w!"an"] r
    -- (`… be an integer and let $x_1,\ldots,x_n$ be …`, `… and $\lambda>0$`: the next binder)
    let cut := (r1.zipIdx.find? fun (c, i) => match c, r1[i + 1]? with
      | .w w, some (.w w') => w == w!"and" && w' == w!"let"
      | .w w, some (.m _) => w == w!"and"
      | _, _ => false).map (·.2)
    let ws := (r1.take (cut.getD r1.length)).takeWhile (fun c => match c with
      | .w w => w != w!"with" && w != w!"such" | .p 45 => true | _ => false)
    -- a noun that ends in a fixed formula: `probability distribution on $\mathbb{N}_0$`
    let tail := match r1.drop ws.length with
      | .m t :: _ =>
        match ws.getLast? with
        | some (.w w) => if w == w!"on" || w == w!"in" then [Chunk.m t] else []
        | _ => []
      | _ => []
    -- words and conditions after the formula (`with zero mean`), up to a comma or the end
    let rest := r1.drop (ws.length + tail.length)
    let opensPost := match rest with
      | .w w :: _ => w == w!"with" || w == w!"of" || w == w!"such"
      | _ => false
    let post := if tail.isEmpty && !opensPost then [] else
      rest.takeWhile (fun c => match c with | .p 44 | .p 46 => false | _ => true)
    if ws.isEmpty then none else some (.noun (ws ++ tail ++ [.m v] ++ post), rest.drop post.length))

/-- Further variables and definitions of a `let`: `, and let $u\in A$`, `and $v\in B$`,
`, and let $X\coloneqq e$`, `, $Y\coloneqq f$ and $Z\coloneqq g$`. -/
def letMore : Nat → List Chunk → List Bind → List MT → Option (List Bind × List MT × List Chunk)
  | 0, cs, bs, ds => some (bs.reverse, ds.reverse, cs)
  | f + 1, cs, bs, ds =>
    let next := (punct 44 cs >>= kw [w!"and", w!"let"]) <|> (punct 44 cs >>= kw [w!"and"]) <|>
      (punct 44 cs >>= kw [w!"let"]) <|> kw [w!"and", w!"let"] cs <|> kw [w!"and"] cs <|> punct 44 cs
    match next with
    | none => some (bs.reverse, ds.reverse, cs)
    | some r =>
      match letBinder r with
      | some (b, r') => letMore f r' (b :: bs) ds
      | none =>
        match formula r with
        | some (m, r') =>
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

/-- `the following are equivalent:` and a list of formulas: each is equivalent to
the next (and so all are). -/
def tfae (cs : List Chunk) : Option (List (MT × MT)) := do
  let r ← kw [w!"the", w!"following", w!"are", w!"equivalent"] cs >>= punct 58
  let items := (listItems r [] []).filter fun it => match it with
    | [] | [.p 46] => false
    | _ => true
  let fs ← items.mapM itemFormula
  if fs.length < 2 then none else some (fs.zip (fs.drop 1))

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
    let v ← match ts with | [.id v] => some v | _ => none
    let r2 ← kw [w!"is", w!"a"] r1 <|> kw [w!"is", w!"an"] r1
    let ws := r2.takeWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
    if ws.isEmpty || !isEnd (r2.drop ws.length) then none else some (.noun (ws ++ [.m [.id v]]))
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
  cases <|> contra <|> induction

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
  let (topic, cs) := marker cs
  match tfae cs with
  | some ps => some (.claims topic [] (ps.map fun (p, q) => ({ cites := [], clause := .iff p q } : CClause)))
  | none =>
  match notionDef cs with
  | some s => some s
  | none =>
  -- let $S$ denote the class of NOUNS, that is, NP.
  match kw [w!"let"] cs with
  | some r =>
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
    -- `Let $C$ be a|an NP[, and let …]`, `Let $a,b\in A$, and let $X\coloneqq e$, ….`
    (do
      let (b1, r1) ← letBinder r
      let (bs, ds, r2) ← letMore 6 r1 [b1] []
      let isNoun := match b1 with | .noun _ | .many _ => true | _ => false
      if isEnd r2 && (isNoun || bs.length > 1 || !ds.isEmpty) then some (.assumeAll bs ds) else none) <|>
    -- `Let $X\coloneqq e$.`, `Let $h(k)=e$.`: as `set`
    constDefsOf none r <|>
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
      kw [w!"we", w!"put"] cs <|> kw [w!"let", w!"us", w!"set"] cs with
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
    if isEnd r1 then some (.fix b [] []) else do
    let r2 ← kw [w!"and"] r1
    let r3 ← kw [w!"define"] r2 <|> kw [w!"set"] r2 <|> kw [w!"put"] r2
    let (items, ls, r4) ← defList 6 r3 [] []
    if isEnd (trailer r4) && !items.isEmpty && items.all isDefeq then some (.fix b items ls) else none
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
    | some r => do
      let (facts, r1) ← sinceFacts 4 r []
      let r2 ← punct 44 r1
      let (_, r3) := marker r2
      let rest ← clauses 8 r3 []
      some (.claims topic [] (facts.map (fun m => ({ cites := [], clause := .fact m } : CClause)) ++ rest))
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
            let (sg, r3) ← sig r2
            let r4 ← kw [w!"by"] r3
            let (pieces, ls, r5) ← defPieces 6 r4 [] []
            if isEnd (trailer r5) then some (Sent.defByFamily b sg pieces ls) else none) with
        | some st => some st
        | none =>
        -- For B, set $X\coloneqq e$ and let $S$ be NP[, where …].
        match kw [w!"set"] r1 <|> kw [w!"write"] r1 <|> kw [w!"put"] r1 <|> kw [w!"we", w!"set"] r1 <|>
            kw [w!"we", w!"put"] r1 with
        | some r2 => (do
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
          let cs ← clauses 8 r2 []
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
        let cs ← clauses 8 cs []
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
      let acc := m :: acc
      match kw [w!"and"] r with
      | some r' => sinceFacts f r' acc
      | none =>
        match r with
        | .p 44 :: .m t :: r' => sinceFacts f (.m t :: r') acc
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

/-- A sentence: an assumption, a contradiction, or one of the other forms, possibly
ending in a contradiction. -/
def sentence (cs : List Chunk) : Option Sent :=
  match supposeSent cs <|> contradictionSent cs <|> organizeSent cs with
  | some s => some s
  | none =>
    match stripContradiction cs with
    | some cs' =>
      match sentenceCore cs' with
      | some (.claims topic binds cls) => some (.claimsContra topic binds cls)
      | _ => none
    | none => sentenceCore cs

def parseSentence (s : Sentence) : Option Sent := do
  match s.toks with
  -- the heading of a case (`\item \emph{…}`)
  | ⟨.cmd h, _, _⟩ :: rest =>
    if h == w!"@heading" then caseHeading (← chunks (rest.length + 1) rest [])
    else sentence (← chunks (s.toks.length + 1) s.toks [])
  | _ => sentence (← chunks (s.toks.length + 1) s.toks [])

end Grammar
end Leanify
