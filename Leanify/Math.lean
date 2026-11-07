import Leanify.Lex

/-! # Parsing mathematical formulas

A total precedence parser from math-mode tokens to formula trees. It follows TeX
argument conventions (`\frac14`, `c^3`, `D_{1/2}`), standard precedence, and
reads juxtaposition as multiplication or application. Whether `f(x)` is an
application or a product is decided later by types. -/
namespace Leanify

inductive Rel where
  | eq | lt | le | gt | ge | mem | defeq | ne
  /-- `A\subseteq B` and `A\supseteq B`. -/
  | subset | supset
  /-- `x\notin A`. -/
  | nmem
  /-- `a\ll b`: `a/b` sufficiently small (read only in binders). -/
  | ll
  deriving DecidableEq, Repr, Lean.ToExpr

inductive MT where
  | id (n : Codes)
  | num (n : Nat)
  | sub (b i : MT)
  | sup (b e : MT)
  | hat (x : MT)
  | app (f : MT) (args : List MT)
  | add (x y : MT) | minus (x y : MT) | mul (x y : MT) | div (x y : MT)
  | neg (x : MT) | abs (x : MT) | frac (x y : MT)
  | minm (args : List MT) | maxm (args : List MT)
  | int (lo hi body : MT) (v : Codes)
  | tuple (xs : List MT)
  | interval (a b : MT)
  /-- An interval with open ends: `(a,b]` is `ival a b true false`. -/
  | ival (a b : MT) (lopen ropen : Bool)
  | setOf (pat dom : MT) (conds : List MT)
  /-- `{pat : conds}`: the variables of `pat` that are not yet bound range over
  the real numbers subject to `conds`. -/
  | setCond (pat : MT) (conds : List MT)
  | image (elem : MT) (v : Codes) (dom : MT)
  | mapsto (pat body : MT)
  | chain (x : MT) (rest : List (Rel × MT))
  | cases (rows : List (MT × MT))
  | sig (name dom cod : MT)
  | conj (xs : List MT)
  /-- `φ, equivalently ψ` in a display: `φ`, and `φ ↔ ψ`. -/
  | equiv (x y : MT)
  /-- `\text{word}` between the formulas of a display (e.g. `where`). -/
  | text (w : Codes)
  /-- `\max\{e : …\}`, `\max_{x\in A} e` (and `\min`): the largest (smallest)
  element of a set of numbers. -/
  | extr (isMax : Bool) (set : MT)
  /-- `\sup S` and `\inf S` (`\sup\{e : …\}`, `\sup_{x\in A} e`): the least upper
  (greatest lower) bound of a set of numbers. -/
  | bound (isSup : Bool) (set : MT)
  /-- `\sum_{v=lo}^{hi} body` and `\prod_{v=lo}^{hi} body`. -/
  | bigop (isSum : Bool) (v : Codes) (lo hi body : MT)
  /-- Connectives between formulas: `\neg`, `\land`, `\lor`, `\Rightarrow`, `\iff`. -/
  | lnot (x : MT) | land (x y : MT) | lor (x y : MT) | limp (x y : MT) | liff (x y : MT)
  /-- `\forall x,y\in A: φ` and `\exists x\in A: φ`. -/
  | quant (isAll : Bool) (vars : List Codes) (dom body : MT)
  /-- A finite set of numbers `\{a,b\}`. -/
  | finset (xs : List MT)
  /-- `\lim_{v\to target} body`. -/
  | limit (v : Codes) (target body : MT)
  deriving Repr, Inhabited, Lean.ToExpr

/-- Math tokens after removing typesetting. -/
inductive MTok where
  | id (n : Codes)
  | digit (d : Nat)
  | sym (c : Nat)
  | cmd (n : Codes)
  | lb | rb
  | setl | setr
  | row
  | diff
  /-- `\text{words}` (letters only). -/
  | text (w : Codes)
  | begin (e : Codes) | finish (e : Codes)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

namespace MT

/-- Replace the variable `v` by `k` (for the terms of a sum with numeral bounds).
Binders of `v` (an integral or image over `v`, a sum over `v`) are left alone. -/
def substId (v : Codes) (k : MT) : Nat → MT → MT
  | 0, m => m
  | f + 1, m =>
    let go := substId v k f
    match m with
    | .id n => if n == v then k else .id n
    | .num n => .num n
    | .sub b i => .sub (go b) (go i)
    | .sup b e => .sup (go b) (go e)
    | .hat x => .hat (go x)
    | .app g args => .app (go g) (args.map go)
    | .add x y => .add (go x) (go y)
    | .minus x y => .minus (go x) (go y)
    | .mul x y => .mul (go x) (go y)
    | .div x y => .div (go x) (go y)
    | .neg x => .neg (go x)
    | .abs x => .abs (go x)
    | .frac x y => .frac (go x) (go y)
    | .minm xs => .minm (xs.map go)
    | .maxm xs => .maxm (xs.map go)
    | .int lo hi body w => .int (go lo) (go hi) (if w == v then body else go body) w
    | .tuple xs => .tuple (xs.map go)
    | .interval a b => .interval (go a) (go b)
    | .ival a b l r => .ival (go a) (go b) l r
    | .setOf pat dom conds => .setOf pat (go dom) conds
    | .setCond pat conds => .setCond pat conds
    | .image e w dom => .image (if w == v then e else go e) w (go dom)
    | .mapsto pat body => .mapsto pat body
    | .chain x rest => .chain (go x) (rest.map fun (r, y) => (r, go y))
    | .cases rows => .cases (rows.map fun (a, b) => (go a, go b))
    | .sig n d c => .sig n d c
    | .conj xs => .conj (xs.map go)
    | .equiv x y => .equiv (go x) (go y)
    | .text w => .text w
    | .extr b st => .extr b (go st)
    | .bound b st => .bound b (go st)
    | .bigop b w lo hi body => .bigop b w (go lo) (go hi) (if w == v then body else go body)
    | .lnot x => .lnot (go x)
    | .land x y => .land (go x) (go y)
    | .lor x y => .lor (go x) (go y)
    | .limp x y => .limp (go x) (go y)
    | .liff x y => .liff (go x) (go y)
    | .quant b vs dom body => .quant b vs (go dom) (if vs.contains v then body else go body)
    | .finset xs => .finset (xs.map go)
    | .limit w t body => .limit w (go t) (if w == v then body else go body)

end MT

namespace Math

/-- Standard functions of a real variable (`\ln` is `\log`). -/
def wFunctions : List Codes := [w!"exp", w!"log", w!"ln", w!"sin", w!"cos", w!"tan"]

def isReals : MT → Bool
  | .id n => n == w!"\\mathbb{R}"
  | _ => false

def isNats : MT → Bool
  | .id n => n == w!"\\mathbb{N}"
  | _ => false

/-- `\mathbb{N}_0`: the natural numbers with `0`. -/
def natsSub : List MTok → Option (Codes × List MTok)
  | .digit 0 :: rest => some (w!"\\mathbb{N}_0", rest)
  | .lb :: .digit 0 :: .rb :: rest => some (w!"\\mathbb{N}_0", rest)
  | _ => none

/-- The subscript of a ray of real numbers: `\mathbb{R}_+`, `_{>0}`, `_{\ge0}`. -/
def realsSub : List MTok → Option (Codes × List MTok)
  | .sym 43 :: rest => some (w!"\\mathbb{R}_{\\ge0}", rest)
  | .lb :: .sym 62 :: .digit 0 :: .rb :: rest => some (w!"\\mathbb{R}_{>0}", rest)
  | .lb :: .cmd c :: .digit 0 :: .rb :: rest =>
    if c == w!"ge" || c == w!"geq" then some (w!"\\mathbb{R}_{\\ge0}", rest) else none
  | _ => none

/-- Connectives between formulas, from the loosest. -/
def wIff : List Codes := [w!"iff", w!"Leftrightarrow", w!"Longleftrightarrow"]
def wImp : List Codes := [w!"Rightarrow", w!"implies", w!"Longrightarrow"]
def wOr : List Codes := [w!"lor", w!"vee"]
def wAnd : List Codes := [w!"land", w!"wedge"]
def wConnectives : List Codes := wIff ++ wImp ++ wOr ++ wAnd ++ [w!"neg", w!"lnot", w!"forall", w!"exists"]

def wFonts : List Codes := [w!"mathcal", w!"mathbb", w!"mathbf", w!"mathrm", w!"operatorname", w!"mathit"]

/-- Accents that make a new symbol (`\overline{\rho}` is not `\rho`). -/
def decorations : List Codes := [w!"overline", w!"bar", w!"tilde", w!"underline", w!"check"]

/-- Join font commands with their letters; `\mathrm{d}` is a differential. -/
def simplify : Nat → List PTok → Option (List MTok)
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, t :: ts =>
    match t.tok with
    | .mvar c => (MTok.id [c] :: ·) <$> simplify f ts
    | .mnum d => (MTok.digit d :: ·) <$> simplify f ts
    | .msym c => (MTok.sym c :: ·) <$> simplify f ts
    | .lbrace => (MTok.lb :: ·) <$> simplify f ts
    | .rbrace => (MTok.rb :: ·) <$> simplify f ts
    | .csym 123 => (MTok.setl :: ·) <$> simplify f ts
    | .csym 125 => (MTok.setr :: ·) <$> simplify f ts
    | .csym 124 => (MTok.sym 124 :: ·) <$> simplify f ts
    | .csym 92 => (MTok.row :: ·) <$> simplify f ts
    | .begin e => (MTok.begin e :: ·) <$> simplify f ts
    | .finish e => (MTok.finish e :: ·) <$> simplify f ts
    | .ref _ _ => simplify f ts
    | .cmd n =>
      if n == w!"longmapsto" then (MTok.cmd w!"mapsto" :: ·) <$> simplify f ts
      else if n == w!"text" then
        match ts with
        | ⟨.lbrace, _, _⟩ :: rest =>
          let inner := rest.takeWhile (fun p => p.tok != .rbrace)
          let word := inner.filterMap (fun p => match p.tok with | .mvar c => some c | _ => none)
          if word.length != inner.length then none
          else (MTok.text word :: ·) <$> simplify f (rest.drop (inner.length + 1))
        | _ => none
      else if wFonts.contains n then
        match ts with
        | ⟨.lbrace, _, _⟩ :: rest =>
          let letters := rest.takeWhile (fun p => match p.tok with | .mvar _ => true | _ => false)
          let word := letters.filterMap (fun p => match p.tok with | .mvar c => some c | _ => none)
          match rest.drop letters.length with
          | ⟨.rbrace, _, _⟩ :: rest' =>
            if n == w!"mathrm" && word == w!"d" then (MTok.diff :: ·) <$> simplify f rest'
            else if n == w!"mathrm" || n == w!"operatorname" then (MTok.id word :: ·) <$> simplify f rest'
            else (MTok.id ([92] ++ n ++ [123] ++ word ++ [125]) :: ·) <$> simplify f rest'
          | _ => none
        -- `\mathbb R`: a single letter without braces
        | ⟨.mvar c, _, _⟩ :: rest =>
          if n == w!"mathrm" || n == w!"operatorname" then (MTok.id [c] :: ·) <$> simplify f rest
          else (MTok.id ([92] ++ n ++ [123, c, 125]) :: ·) <$> simplify f rest
        | _ => none
      else if n == w!"tfrac" || n == w!"dfrac" then (MTok.cmd w!"frac" :: ·) <$> simplify f ts
      -- a decorated symbol `\overline{\rho}` is a name of its own
      else if decorations.contains n then
        match ts with
        | ⟨.lbrace, _, _⟩ :: ⟨inner, _, _⟩ :: ⟨.rbrace, _, _⟩ :: rest =>
          let name : Option Codes := match inner with
            | .mvar c => some [c]
            | .cmd m => some ([92] ++ m)
            | _ => none
          match name with
          | some nm => (MTok.id ([92] ++ n ++ [123] ++ nm ++ [125]) :: ·) <$> simplify f rest
          | none => (MTok.cmd n :: ·) <$> simplify f ts
        -- `\bar x`: a single letter without braces
        | ⟨.mvar c, _, _⟩ :: rest => (MTok.id ([92] ++ n ++ [123, c, 125]) :: ·) <$> simplify f rest
        | _ => (MTok.cmd n :: ·) <$> simplify f ts
      else (MTok.cmd n :: ·) <$> simplify f ts
    | _ => none

def isDigitTok : MTok → Bool | .digit _ => true | _ => false

def relOf : MTok → Option Rel
  | .sym 61 => some .eq
  | .sym 60 => some .lt
  | .sym 62 => some .gt
  | .cmd n =>
    if n == w!"le" || n == w!"leq" then some .le
    else if n == w!"ge" || n == w!"geq" then some .ge
    else if n == w!"in" then some .mem
    else if n == w!"coloneqq" then some .defeq
    else if n == w!"neq" || n == w!"ne" then some .ne
    else if n == w!"notin" then some .nmem
    else if n == w!"subseteq" || n == w!"subseteqq" then some .subset
    else if n == w!"supseteq" || n == w!"supseteqq" then some .supset
    else if n == w!"ll" then some .ll
    else none
  | _ => none

/-- Tokens that may begin an implicit product factor. -/
def startsFactor : MTok → Bool
  | .id _ | .digit _ | .lb | .setl => true
  | .sym 40 => true
  | .cmd n => n == w!"frac" || n == w!"int" || n == w!"min" || n == w!"max" || n == w!"sup" ||
      n == w!"inf" || n == w!"sum" || n == w!"prod" || n == w!"lim" || n == w!"binom" ||
      n == w!"tbinom" || n == w!"dbinom" || n == w!"widehat"
      || n == w!"hat" || (!(relOf (.cmd n)).isSome && n != w!"mapsto" && n != w!"to" &&
        n != w!"cdot" && n != w!"qquad" && n != w!"quad" && n != w!"times" && n != w!"top" && n != w!"perp" &&
        n != w!"cup" && n != w!"cap" && n != w!"circ" && n != w!"setminus" && !wConnectives.contains n && n != w!"rfloor" && n != w!"rceil" &&
        n != w!"approx" && n != w!"ldots")
  | _ => false

/-- Heads that may be applied to a parenthesized argument list. -/
def appHead : MT → Bool
  -- `n!` and `\binom{n}{k}` are values, not functions (`k!\,(n-k)!` is a product)
  | .app (.id (64 :: _)) _ => false
  | .id _ | .sub _ _ | .hat _ | .app _ _ => true
  -- `f'(x)`, `R_b^-(z)`
  | .sup _ (.id n) => n == w!"\\top" || n == w!"\\perp" || n == [39] || n == [45] || n == [43]
  -- the inverse function `f^{-1}`
  | .sup (.id _) (.neg (.num 1)) => true
  | _ => false

inductive Mode where
  | top              -- relations, chains, mapsto
  | additive (bar : Bool)
  | product (bar : Bool)
  | factor (bar : Bool)
  | postfix (bar : Bool) (x : MT)
  | atom (bar : Bool)
  | number (acc : Nat)
  | args (acc : List MT)
  | group              -- a braced group or single token (TeX argument)
  | casesRows (acc : List (MT × MT))
  | list (sep : Nat) (acc : List MT)   -- comma separated items until a closer
  deriving Inhabited

abbrev R := Option (MT × List MTok)

def expect (t : MTok) : List MTok → Option (List MTok)
  | u :: us => if u == t then some us else none
  | [] => none

/-- One structurally recursive parser with explicit modes (kernel-reducible). -/
def run : Nat → Mode → List MTok → R
  | 0, _, _ => none
  | f + 1, .top, ts => do
    let (x, rest) ← run f (.additive false) ts
    match rest with
    | .cmd n :: rest' =>
      if n == w!"mapsto" then
        let (b, rest'') ← run f .top rest'
        some (.mapsto x b, rest'')
      else if n == w!"to" then none
      else chainRest f x [] rest
    | _ => chainRest f x [] rest
  | f + 1, .additive bar, ts => do
    let (x, rest) ← run f (.product bar) ts
    addRest f bar x rest
  | f + 1, .product bar, ts => do
    let (x, rest) ← run f (.factor bar) ts
    mulRest f bar x rest
  | f + 1, .factor bar, ts =>
    match ts with
    | .sym 45 :: rest => do
      let (x, rest') ← run f (.product bar) rest
      some (.neg x, rest')
    -- a unary plus, as in the upper sign of `\pm1`
    | .sym 43 :: rest => run f (.product bar) rest
    | _ => do
      let (x, rest) ← run f (.atom bar) ts
      run f (.postfix bar x) rest
  | f + 1, .postfix bar x, ts =>
    match ts with
    -- `f'`: the derivative, written as the superscript `'`
    | .sym 39 :: rest => run f (.postfix bar (.sup x (.id [39]))) rest
    -- `n!`
    | .sym 33 :: rest => run f (.postfix bar (.app (.id w!"@factorial") [x])) rest
    | .sym 94 :: rest => do
      let (e, rest') ← run f .group rest
      run f (.postfix bar (.sup x e)) rest'
    | .sym 95 :: rest =>
      -- `\mathbb{R}_+`, `\mathbb{R}_{>0}`, `\mathbb{R}_{\ge0}`
      match (if isReals x then realsSub rest else if isNats x then natsSub rest else none) with
      | some (name, rest') => run f (.postfix bar (.id name)) rest'
      | none => do
      let (i, rest') ← run f .group rest
      -- `T^0_q` is `T_q^0`, as typeset, and `\widehat S_s` is the hat of `S_s`
      let x' := match x with
        | .sup b e => MT.sup (.sub b i) e
        | .hat b => MT.hat (.sub b i)
        | _ => .sub x i
      run f (.postfix bar x') rest'
    | .sym 40 :: rest =>
      if !appHead x then some (x, ts) else do
        let (m, rest') ← run f (.list 41 []) rest
        match m with
        | .conj as => run f (.postfix bar (.app x as)) rest'
        | _ => none
    | _ => some (x, ts)
  | f + 1, .atom bar, ts =>
    match ts with
    | .digit d :: rest => run f (.number d) rest
    | .id n :: rest => some (.id n, rest)
    | .sym 40 :: rest =>
      (do
        let (m, rest') ← run f (.list 41 []) rest
        match m with
        | .conj [x] => some (x, rest')
        | .conj xs => some (.tuple xs, rest')
        | _ => none) <|>
      (do
        -- `(a,b]`
        let (a, r1) ← run f (.additive false) rest
        let r2 ← expect (.sym 44) r1
        let (b, r3) ← run f (.additive false) r2
        let r4 ← expect (.sym 93) r3
        some (.ival a b true false, r4))
    | .sym 91 :: rest => do
      let (a, r1) ← run f (.additive false) rest
      let r2 ← expect (.sym 44) r1
      let (b, r3) ← run f (.additive false) r2
      match r3 with
      | .sym 93 :: r4 => some (.interval a b, r4)
      | .sym 41 :: r4 => some (.ival a b false true, r4)
      | _ => none
    | .sym 124 :: rest =>
      if bar then none else do
        let (x, r1) ← run f (.additive true) rest
        let r2 ← expect (.sym 124) r1
        some (.abs x, r2)
    | .lb :: rest => do
      let (x, r1) ← run f .top rest
      let r2 ← expect .rb r1
      some (x, r2)
    | .setl :: rest =>
      setBuilder f rest <|>
      (do
        -- a finite set `\{0,2\}`
        let (m, r1) ← run f (.list 125 []) rest
        match m with
        | .conj xs => if xs.length ≥ 2 then some (.finset xs, r1) else none
        | _ => none) <|>
      (do
        -- braces as parentheses: `4\int_0^1\{C(u,u)+C(u,1-u)\}\de u`
        let (x, r1) ← run f .top rest
        let r2 ← expect .setr r1
        some (x, r2))
    | .cmd n :: rest =>
      if n == w!"frac" then do
        let (a, r1) ← run f .group rest
        let (b, r2) ← run f .group r1
        some (.frac a b, r2)
      else if n == w!"widehat" || n == w!"hat" then do
        let (a, r1) ← run f .group rest
        some (.hat a, r1)
      else if n == w!"sqrt" then
        match rest with
        | .sym 91 :: r => do
          -- `\sqrt[3]{x}`
          let (k, r1) ← run f (.additive false) r
          let r2 ← expect (.sym 93) r1
          let (a, r3) ← run f .group r2
          some (.sup a (.frac (.num 1) k), r3)
        | _ => do
          let (a, r1) ← run f .group rest
          some (.sup a (.frac (.num 1) (.num 2)), r1)
      else if wFunctions.contains n then do
        -- `\exp(x)`, `\log x`, `\sin^2 x` (the square of `\sin x`)
        let (pow, r1) ← match rest with
          | .sym 94 :: r => do let (e, r') ← run f .group r; some (some e, r')
          | r => some (none, r)
        let (arg, r2) ← match r1 with
          | .sym 40 :: r => do
            let (m, r') ← run f (.list 41 []) r
            match m with
            | .conj [x] => some (x, r')
            | _ => none
          | r => do
            let (x0, r') ← run f (.atom false) r
            run f (.postfix false x0) r'
        let name := if n == w!"ln" then w!"log" else n
        let app := MT.app (.id ([92] ++ name)) [arg]
        some (match pow with | some e => .sup app e | none => app, r2)

      else if n == w!"sum" || n == w!"prod" then
        match rest with
        | .sym 95 :: r => do
          -- `\sum_{j=1}^{3} e`
          let (b, r1) ← run f .group r
          let r2 ← expect (.sym 94) r1
          let (hi, r3) ← run f .group r2
          match b with
          | .chain (.id v) [(.eq, lo)] => do
            let (body, r4) ← run f (.product false) r3
            some (.bigop (n == w!"sum") v lo hi body, r4)
          | _ => none
        | _ => none
      else if n == w!"sup" || n == w!"inf" then
        let isSup := n == w!"sup"
        match rest with
        | .setl :: r =>
          (do
            let (m, r') ← run f (.list 125 []) r
            match m with
            | .conj xs => some (if isSup then .maxm xs else .minm xs, r')
            | _ => none) <|>
          (do
            let (st, r') ← setBuilder f r
            some (.bound isSup st, r'))
        | .sym 95 :: r => do
          -- `\sup_{x\in A} e`
          let (b, r1) ← run f .group r
          match b with
          | .chain (.id v) [(.mem, dom)] => do
            let (body, r2) ← run f (.product false) r1
            some (.bound isSup (.image body v dom), r2)
          | _ => none
        | _ => do
          -- `\sup A` for a named set
          let (a, r1) ← run f (.atom false) rest
          some (.bound isSup a, r1)
      else if n == w!"lim" then
        match rest with
        | .sym 95 :: .lb :: .id v :: .cmd t :: r => do
          -- `\lim_{n\to\infty} a_n`, `\lim_{x\to0} f(x)`
          if t != w!"to" then none else
          let (target, r1) ← run f (.additive false) r
          let r2 ← expect .rb r1
          let (body, r3) ← run f (.product false) r2
          some (.limit v target body, r3)
        | _ => none
      else if n == w!"binom" || n == w!"tbinom" || n == w!"dbinom" then do
        let (a, r1) ← run f .group rest
        let (b, r2) ← run f .group r1
        some (.app (.id w!"@binom") [a, b], r2)
      else if n == w!"lfloor" || n == w!"lceil" then do
        -- `\lfloor x\rfloor`, `\lceil x\rceil`
        let (x, r1) ← run f (.additive false) rest
        let r2 ← expect (.cmd (if n == w!"lfloor" then w!"rfloor" else w!"rceil")) r1
        some (.app (.id (if n == w!"lfloor" then w!"@floor" else w!"@ceil")) [x], r2)
      else if n == w!"min" || n == w!"max" then
        match rest with
        | .sym 40 :: r => do
          -- `\max(a,b)`
          let (m, r') ← run f (.list 41 []) r
          match m with
          | .conj xs => if xs.length < 2 then none else some (if n == w!"min" then .minm xs else .maxm xs, r')
          | _ => none
        | .setl :: r =>
          (do
            let (m, r') ← run f (.list 125 []) r
            match m with
            | .conj xs => some (if n == w!"min" then .minm xs else .maxm xs, r')
            | _ => none) <|>
          (do
            let (st, r') ← setBuilder f r
            some (.extr (n == w!"max") st, r'))
        | .sym 95 :: r => do
          -- `\max_{x\in A} e`
          let (b, r1) ← run f .group r
          match b with
          | .chain (.id v) [(.mem, dom)] => do
            let (body, r2) ← run f (.product false) r1
            some (.extr (n == w!"max") (.image body v dom), r2)
          | _ => none
        | _ => none
      else if n == w!"int" then
        match rest with
        | .sym 95 :: r => do
          let (lo, r1) ← run f .group r
          let r2 ← expect (.sym 94) r1
          let (hi, r3) ← run f .group r2
          integralBody f lo hi r3
        | _ => none
      else if (relOf (.cmd n)).isSome || n == w!"mapsto" || n == w!"to" || n == w!"qquad" || n == w!"quad" ||
          n == w!"approx" || n == w!"ldots" || wConnectives.contains n || n == w!"rfloor" ||
          n == w!"rceil" then none
      else some (.id ([92] ++ n), rest)
    | .begin e :: rest =>
      if e == w!"cases" then run f (.casesRows []) rest else none
    | _ => none
  | f + 1, .number acc, ts =>
    match ts with
    | .digit d :: rest => run f (.number (10 * acc + d)) rest
    | _ => some (.num acc, ts)
  | f + 1, .group, ts =>
    match ts with
    | .lb :: rest =>
      (do
        let (x, r1) ← run f .top rest
        let r2 ← expect .rb r1
        some (x, r2)) <|>
      (do
        -- a list index `\Omega_{\rho,\gamma}`
        let (m, r1) ← run f (.list 0 []) rest
        match m with
        | .conj xs => some (.tuple xs, r1)
        | _ => none)
    | .digit d :: rest => some (.num d, rest)
    | .id n :: rest => some (.id n, rest)
    | .cmd n :: rest => some (.id ([92] ++ n), rest)
    -- `g_*`, `R^-`, `R^+`
    | .sym 42 :: rest => some (.id [42], rest)
    | .sym 45 :: rest => some (.id [45], rest)
    | .sym 43 :: rest => some (.id [43], rest)
    | _ => none
  | _ + 1, .args acc, ts => some (.tuple acc.reverse, ts)
  | f + 1, .list close acc, ts => do
    let (x, r1) ← run f .top ts
    match r1 with
    | .sym 44 :: r2 => run f (.list close (x :: acc)) r2
    | t :: r2 =>
      if (close == 41 && t == .sym 41) || (close == 125 && t == .setr) || (close == 0 && t == .rb) then
        some (MT.conj (x :: acc).reverse, r2)
      else none
    | [] => none
  | f + 1, .casesRows acc, ts =>
    match ts with
    | .finish e :: rest => if e == w!"cases" then some (.cases acc.reverse, rest) else none
    | _ => do
      let (v, r1) ← run f (.additive false) ts
      let r1 := match r1 with | .sym 44 :: r => r | r => r
      let r2 ← expect (.sym 38) r1
      let (c, r3) ← run f .top r2
      let r4 := match r3 with | .sym 44 :: r => r | .sym 46 :: r => r | r => r
      match r4 with
      | .row :: r5 => run f (.casesRows ((v, c) :: acc)) r5
      | _ => run f (.casesRows ((v, c) :: acc)) r4
where
  chainRest : Nat → MT → List (Rel × MT) → List MTok → R
    | 0, _, _, _ => none
    | g + 1, x, acc, ts =>
      match ts with
      | t :: rest =>
        match relOf t with
        | some r => do
          let (y, rest') ← run g (.additive false) rest
          chainRest g x ((r, y) :: acc) rest'
        | none =>
          -- `\approx 0.4002`: a numerical illustration, which asserts nothing
          if t == .cmd w!"approx" then
            let rest' := rest.dropWhile fun u => match u with
              | .digit _ | .sym 46 | .cmd [108, 100, 111, 116, 115] | .cmd [100, 111, 116, 115] => true
              | _ => false
            some (if acc.isEmpty then x else .chain x acc.reverse, rest')
          else some (if acc.isEmpty then x else .chain x acc.reverse, ts)
      | [] => some (if acc.isEmpty then x else .chain x acc.reverse, ts)
  addRest : Nat → Bool → MT → List MTok → R
    | 0, _, _, _ => none
    | g + 1, bar, x, ts =>
      match ts with
      | .sym 43 :: rest => do
        let (y, rest') ← run g (.product bar) rest
        addRest g bar (.add x y) rest'
      | .sym 45 :: rest => do
        let (y, rest') ← run g (.product bar) rest
        addRest g bar (.minus x y) rest'
      -- `A\cup B`
      | .cmd [99, 117, 112] :: rest => do
        let (y, rest') ← run g (.product bar) rest
        addRest g bar (.app (.id w!"\\cup") [x, y]) rest'
      -- `A\setminus B`
      | .cmd [115, 101, 116, 109, 105, 110, 117, 115] :: rest => do
        let (y, rest') ← run g (.product bar) rest
        addRest g bar (.app (.id w!"\\setminus") [x, y]) rest'
      | _ => some (x, ts)
  mulRest : Nat → Bool → MT → List MTok → R
    | 0, _, _, _ => none
    | g + 1, bar, x, ts =>
      match ts with
      | .sym 42 :: rest | .cmd [99, 100, 111, 116] :: rest => do
        let (y, rest') ← run g (.factor bar) rest
        mulRest g bar (.mul x y) rest'
      | .sym 47 :: rest => do
        let (y, rest') ← run g (.factor bar) rest
        mulRest g bar (.div x y) rest'
      -- `A\times B`
      | .cmd [116, 105, 109, 101, 115] :: rest => do
        let (y, rest') ← run g (.factor bar) rest
        mulRest g bar (.app (.id w!"\\times") [x, y]) rest'
      -- `A\cap B`
      | .cmd [99, 97, 112] :: rest => do
        let (y, rest') ← run g (.factor bar) rest
        mulRest g bar (.app (.id w!"\\cap") [x, y]) rest'
      -- `f\circ g`
      | .cmd [99, 105, 114, 99] :: rest => do
        let (y, rest') ← run g (.factor bar) rest
        mulRest g bar (.app (.id w!"\\circ") [x, y]) rest'
      | t :: _ =>
        if startsFactor t || (t == .sym 124 && !bar) then
          match run g (.atom bar) ts with
          | some (y0, rest') => do
            let (y, rest'') ← run g (.postfix bar y0) rest'
            mulRest g bar (.mul x y) rest''
          | none => some (x, ts)
        else some (x, ts)
      | [] => some (x, ts)
  integralBody : Nat → MT → MT → List MTok → R
    | 0, _, _, _ => none
    | g + 1, lo, hi, ts => do
      let (body, r1) ← run g (.product false) ts
      match r1 with
      | .diff :: .id v :: r2 => some (.int lo hi body v, r2)
      | _ =>
        -- `\int_0^1 x\,dx`: a plain `d` before the variable at the end
        match body with
        | .mul (.mul b (.id [100])) (.id v) => some (.int lo hi b v, r1)
        | .mul (.id [100]) (.id v) => some (.int lo hi (.num 1) v, r1)
        | _ => none
  setBuilder : Nat → List MTok → R
    | 0, _ => none
    | g + 1, ts => do
      -- `{pat ∈ dom : conds}` or `{elem : v ∈ dom}`
      let (head, r1) ← run g (.additive false) ts
      match r1 with
      | .cmd n :: r2 =>
        if n == w!"in" then do
          let (dom, r3) ← run g (.additive false) r2
          let r4 ← expect (.sym 58) r3
          let (conds, r5) ← run g (.list 125 []) r4
          match conds with
          | .conj cs => some (.setOf head dom cs, r5)
          | _ => none
        else none
      | .sym 58 :: r2 =>
        (do
          let (v, r3) ← (match r2 with | .id v :: r => some (v, r) | _ => none : Option (Codes × List MTok))
          let r4 ← expect (.cmd w!"in") r3
          let (dom, r5) ← run g (.additive false) r4
          let r6 ← expect .setr r5
          some (.image head v dom, r6)) <|>
        (do
          let (conds, r3) ← run g (.list 125 []) r2
          match conds with
          | .conj cs => some (.setCond head cs, r3)
          | _ => none)
      | _ => none

/-- Displays: aligned rows and formula lists separated by `,\qquad`.
A row beginning with a relation continues the previous row's chain. -/
def splitTop : Nat → List MTok → List MTok → Nat → List (List MTok) → List (List MTok)
  | 0, cur, _, _, acc => (cur.reverse :: acc).reverse
  | _ + 1, cur, [], _, acc => (cur.reverse :: acc).reverse
  | f + 1, cur, t :: ts, depth, acc =>
    let depth' := match t with
      | .lb | .setl | .sym 40 | .sym 91 | .begin _ => depth + 1
      | .rb | .setr | .sym 41 | .sym 93 | .finish _ => depth - 1
      | _ => depth
    if depth == 0 && (t == .row || t == .cmd w!"qquad") then
      let cur' := match cur with | .sym 44 :: c => c | c => c
      if cur'.isEmpty then splitTop f [] ts depth' acc
      else splitTop f [] ts depth' (cur'.reverse :: acc)
    else if depth == 0 && t == .sym 38 then
      -- `a, & b`: a column of equations; otherwise an alignment point
      match cur with
      | .sym 44 :: c => if c.isEmpty then splitTop f [] ts depth' acc else splitTop f [] ts depth' (c.reverse :: acc)
      | _ => splitTop f cur ts depth' acc
    else if depth == 0 && (match t with | .text _ => true | _ => false) then
      let cur' := match cur with | .sym 44 :: c => c | c => c
      let acc := if cur'.isEmpty then acc else cur'.reverse :: acc
      splitTop f [] ts depth' ([t] :: acc)
    else splitTop f (t :: cur) ts depth' acc

def stripEnv : List MTok → List MTok
  | .begin e :: ts =>
    if e == w!"aligned" || e == w!"gathered" || e == w!"split" then
      match ts.reverse with
      | .finish e' :: r => if e' == e then r.reverse else .begin e :: ts
      | _ => .begin e :: ts
    else .begin e :: ts
  | ts => ts

/-- Split at the first token with `isOp` outside brackets and braces. -/
def splitTop1 (isOp : MTok → Bool) : Nat → Int → List MTok → List MTok → Option (List MTok × List MTok)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | f + 1, d, acc, t :: ts =>
    if d == 0 && isOp t then some (acc.reverse, ts) else
    match t with
    | .lb | .setl | .sym 40 | .sym 91 | .begin _ => splitTop1 isOp f (d + 1) (t :: acc) ts
    | .rb | .setr | .sym 41 | .sym 93 | .finish _ => splitTop1 isOp f (d - 1) (t :: acc) ts
    | _ => splitTop1 isOp f d (t :: acc) ts

def isCmdIn (ops : List Codes) : MTok → Bool
  | .cmd n => ops.contains n
  | _ => false

/-- The variables of a quantifier, `x,y\in`: their names and the tokens after `\in`. -/
def quantVars : List MTok → Option (List Codes × List MTok)
  | .id v :: .sym 44 :: rest => do let (vs, r) ← quantVars rest; some (v :: vs, r)
  | .id v :: .cmd i :: rest => if i == w!"in" then some ([v], rest) else none
  | _ => none

/-- The whole token list as one chain (or term). -/
def wholeTop (ts : List MTok) : Option MT :=
  match run (8 * ts.length + 64) .top ts with
  | some (x, []) => some x
  | _ => none

/-- A formula with connectives and quantifiers: `\forall x\in A: φ`, `φ\Rightarrow ψ`,
`φ\iff ψ`, `φ\lor ψ`, `φ\land ψ`, `\neg φ`; its atoms are chains. A quantifier's
domain ends at the first `:` or `,`, and its body extends to the end. -/
def logic : Nat → List MTok → Option MT
  | 0, _ => none
  | f + 1, ts =>
    let quant : Option MT := match ts with
      | .cmd q :: rest =>
        if q == w!"forall" || q == w!"exists" then do
          let (vs, r) ← quantVars rest
          let (dts, bts) ← splitTop1 (fun t => t == .sym 58 || t == .sym 44) (r.length + 1) 0 [] r
          let dom ← match run (8 * dts.length + 64) (.additive false) dts with
            | some (x, []) => some x
            | _ => none
          let body ← logic f bts
          some (.quant (q == w!"forall") vs dom body)
        else none
      | _ => none
    match quant with
    | some m => some m
    | none =>
    let split (ops : List Codes) := splitTop1 (isCmdIn ops) (ts.length + 1) 0 [] ts
    match split wIff with
    | some (a, b) => do some (.liff (← logic f a) (← logic f b))
    | none =>
    match split wImp with
    | some (a, b) => do some (.limp (← logic f a) (← logic f b))
    | none =>
    match split wOr with
    | some (a, b) => do some (.lor (← logic f a) (← logic f b))
    | none =>
    match split wAnd with
    | some (a, b) => do some (.land (← logic f a) (← logic f b))
    | none =>
    match ts with
    | .cmd n :: rest => if n == w!"neg" || n == w!"lnot" then (logic f rest).map .lnot else wholeTop ts
    | _ => wholeTop ts

def parseFormula (ts : List MTok) : Option MT :=
  match run (8 * ts.length + 64) .top ts with
  | some (x, []) => some x
  | _ => if ts.any (isCmdIn wConnectives) then logic (ts.length + 2) ts else none

def joinRows : List MT → Option (List MT)
  | [] => some []
  | x :: rest => do
    let rs ← joinRows rest
    match rs with
    | .chain (.id []) more :: rs' =>
      match x with
      | .chain y acc => some (.chain y (acc ++ more) :: rs')
      | y => some (.chain y more :: rs')
    | _ => some (x :: rs)

/-- `\pm` and `\mp` read as `+` and `-` (`upper`), or as `-` and `+`. -/
def pmAs (upper : Bool) : List MTok → List MTok :=
  List.map fun t =>
    if t == .cmd w!"pm" then .sym (if upper then 43 else 45)
    else if t == .cmd w!"mp" then .sym (if upper then 45 else 43)
    else t

/-- Parse the content of a display or inline formula. A formula with `\pm` or `\mp` stands for two formulas,
the upper and the lower signs: `x_\pm(c)\coloneqq c\pm1` defines `x_+` and `x_-`. -/
def parseDisplay (ts : List MTok) : Option MT := do
  let ts := stripEnv ts
  let parts := splitTop (ts.length + 1) [] ts 0 []
  let parts := parts.filter (!·.isEmpty)
  let parts := if ts.any (fun t => t == .cmd w!"pm" || t == .cmd w!"mp") then
      parts.map (pmAs true) ++ parts.map (pmAs false) else parts
  -- `φ, \text{equivalently} ψ`
  match parts with
  | [p, [.text w], q] =>
    if w == w!"equivalently" then do
      let a ← parseFormula p
      let b ← parseFormula q
      some (.equiv a b)
    else none
  | _ => do
  let ms ← parts.mapM fun p =>
    match p with
    | [.text w] => some (MT.text w)
    | t :: _ => if (relOf t).isSome then parseFormula (.id [] :: p) else parseFormula p
    | [] => none
  let ms ← joinRows ms
  match ms with
  | [m] => some m
  | ms => some (.conj ms)

/-- Function signature `f : A \to B`. -/
def parseSig (ts : List MTok) : Option MT := do
  let i ← ts.findIdx? (· == .sym 58)
  let j ← ts.findIdx? (· == .cmd w!"to")
  let name ← parseFormula (ts.take i)
  let dom ← parseFormula ((ts.drop (i + 1)).take (j - i - 1))
  let cod ← parseFormula (ts.drop (j + 1))
  some (.sig name dom cod)

end Math
end Leanify
