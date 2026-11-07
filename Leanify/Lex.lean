import Leanify.Codes

/-! # Lexing TeX source

A total lexer from code points to tokens. It distinguishes text mode from math
mode, expands the article's own parameterless `\newcommand` macros, reads
labels, references and citations, and records the source offset of every token.
Typesetting-only material (spacing, delimiter sizes, emphasis) is dropped.
Anything it does not understand becomes an ordinary token, so that the grammar,
not the lexer, decides whether a sentence has a mathematical reading. -/
namespace Leanify

inductive RefKind where
  | label | ref | eqref | cite
  deriving DecidableEq, Repr, Lean.ToExpr

inductive Tok where
  | word (w : Codes)
  | punct (c : Nat)
  | par
  | mopen | mclose
  | mvar (c : Nat)
  | mnum (n : Nat)
  | msym (c : Nat)
  | cmd (name : Codes)
  | csym (c : Nat)
  | lbrace | rbrace
  | begin (env : Codes)
  | finish (env : Codes)
  | ref (kind : RefKind) (arg : Codes)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure PTok where
  tok : Tok
  pos : Nat
  math : Bool
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

abbrev Macros := List (Codes × Codes)

namespace Lex

def isLetter (c : Nat) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def isSpace (c : Nat) : Bool := c == 32 || c == 9 || c == 13 || c == 10 || c == 126
/-- Letters of text words: ASCII letters, digits, apostrophes and accented Latin letters. -/
def isWordChar (c : Nat) : Bool :=
  isLetter c || isDigit c || c == 39 || c == 8217 || (192 ≤ c && c ≤ 591)

def takeWhile (p : Nat → Bool) : Codes → Codes × Codes
  | [] => ([], [])
  | c :: cs => if p c then let (a, b) := takeWhile p cs; (c :: a, b) else ([], c :: cs)

/-- Read a balanced `{...}` group (the opening brace already consumed). -/
def group : Nat → Nat → Codes → Codes → Option (Codes × Codes × Nat)
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => none
  | f + 1, depth, c :: cs, acc =>
    if c == 92 then
      match cs with
      | d :: ds => group f depth ds (d :: c :: acc)
      | [] => none
    else if c == 123 then group f (depth + 1) cs (c :: acc)
    else if c == 125 then
      if depth == 0 then some (acc.reverse, cs, acc.length + 1) else group f (depth - 1) cs (c :: acc)
    else group f depth cs (c :: acc)

/-- Skip whitespace, returning the number of skipped code points. -/
def spaces : Codes → Codes × Nat
  | c :: cs => if isSpace c then let (r, n) := spaces cs; (r, n + 1) else (c :: cs, 0)
  | [] => ([], 0)

/-- An optional `[...]` argument (without nesting), skipped. -/
def optArg : Codes → Codes × Nat
  | 91 :: cs =>
    let (a, b) := takeWhile (· != 93) cs
    match b with
    | 93 :: r => (r, a.length + 2)
    | _ => (91 :: cs, 0)
  | cs => (cs, 0)

def wDisplayEnvs : List Codes :=
  [w!"equation", w!"equation*", w!"align", w!"align*", w!"gather", w!"gather*", w!"multline",
   w!"multline*", w!"displaymath"]
def wListEnvs : List Codes := [w!"enumerate", w!"itemize", w!"description"]
/-- Environments of drawings and verbatim text, skipped to their end. -/
def wSkipEnvs : List Codes :=
  [w!"tikzpicture", w!"pgfpicture", w!"picture", w!"tikzcd", w!"verbatim", w!"lstlisting",
   w!"minted", w!"comment"]
def wDropText : List Codes :=
  [w!"emph", w!"textit", w!"textbf", w!"textup", w!"noindent", w!"centering", w!"medskip",
   w!"smallskip", w!"bigskip", w!"par", w!"newline", w!"protect", w!"relax", w!"null",
   w!"leavevmode", w!"sloppy", w!"fussy", w!"indent", w!"hfill", w!"vfill", w!"allowbreak",
   w!"linebreak", w!"nolinebreak", w!"pagebreak", w!"nopagebreak", w!"goodbreak", w!"newpage",
   w!"clearpage"]
def wDropMath : List Codes :=
  [w!"bigl", w!"bigr", w!"Bigl", w!"Bigr", w!"biggl", w!"biggr", w!"big", w!"Big", w!"left",
   w!"right", w!"displaystyle", w!"textstyle", w!"limits", w!"nolimits", w!"notag", w!"nonumber"]
/-- Commands of formulas that are another spelling of a symbol the grammar reads:
`\colon` is `:`, `\leqslant` is `\le`, `\lvert` is `|`. -/
def mathAlias (n : Codes) : Option Tok :=
  if n == w!"colon" || n == w!"mid" then some (.msym 58)
  else if n == w!"leqslant" || n == w!"leqq" then some (.cmd w!"le")
  else if n == w!"geqslant" || n == w!"geqq" then some (.cmd w!"ge")
  else if n == w!"lvert" || n == w!"rvert" || n == w!"vert" then some (.msym 124)
  else if n == w!"lbrace" then some (.csym 123)
  else if n == w!"rbrace" then some (.csym 125)
  else none

/-- References that print the kind of what they refer to (`\cref{l}` is `Lemma 2.1`). -/
def wSelfRefs : List Codes := [w!"cref", w!"Cref", w!"autoref", w!"Autoref"]
/-- Commands whose braced arguments are layout or metadata, skipped with the command kept. -/
def wSkipArgs : List Codes :=
  [w!"section", w!"subsection", w!"subsubsection", w!"section*", w!"caption", w!"includegraphics",
   w!"bibliographystyle", w!"bibliography", w!"vspace", w!"hspace", w!"thanks", w!"title",
   w!"author", w!"date", w!"address", w!"email", w!"keywords", w!"maketitle", w!"Needspace",
   w!"texorpdfstring", w!"tag", w!"tag*"]

/-! ### Theorem environments

Articles declare their own result environments: `\newtheorem{thm}{Theorem}`,
`\newtheorem{lem}[thm]{Lemma}`, `\newtheorem*{claim*}{Claim}`. The lexer reads
`\begin{thm}` as `\begin{theorem}`: the printed name decides the kind. A claim, a
fact or an observation is read as a lemma, a statement proved where it stands; a
question, a problem or a hypothesis as a conjecture, a statement not asserted; a
notation as a definition; a note, a heuristic or a principle as a remark. The
common abbreviations (`thm`, `lem`, `prop`, `cor`, `defn`, `rem`, …) are read the
same way when the preamble does not declare them, since they usually come from a
style file. The aliases are kept with the macros, under the environment name
prefixed by `{` (no command name starts with a brace). -/

/-- The words of a printed theorem name, and the kind of result they name. -/
def kindWords : List (Codes × Codes) :=
  [(w!"theorem", w!"theorem"), (w!"theorems", w!"theorem"),
   (w!"lemma", w!"lemma"), (w!"lemmas", w!"lemma"), (w!"sublemma", w!"lemma"), (w!"claim", w!"lemma"),
   (w!"fact", w!"lemma"), (w!"observation", w!"lemma"),
   (w!"proposition", w!"proposition"), (w!"corollary", w!"corollary"),
   (w!"definition", w!"definition"), (w!"definitions", w!"definition"), (w!"notation", w!"definition"),
   (w!"remark", w!"remark"), (w!"remarks", w!"remark"), (w!"note", w!"remark"),
   (w!"heuristic", w!"remark"), (w!"principle", w!"remark"),
   (w!"example", w!"example"), (w!"examples", w!"example"),
   (w!"conjecture", w!"conjecture"), (w!"question", w!"conjecture"), (w!"problem", w!"conjecture"),
   (w!"hypothesis", w!"conjecture")]

/-- Abbreviated environment names, read when the preamble does not declare them. -/
def kindAbbrevs : List (Codes × Codes) :=
  [(w!"thm", w!"theorem"), (w!"theo", w!"theorem"), (w!"lem", w!"lemma"), (w!"lemm", w!"lemma"),
   (w!"lmm", w!"lemma"), (w!"prop", w!"proposition"), (w!"cor", w!"corollary"),
   (w!"coro", w!"corollary"), (w!"corr", w!"corollary"), (w!"defn", w!"definition"),
   (w!"defi", w!"definition"), (w!"dfn", w!"definition"), (w!"defin", w!"definition"),
   (w!"rem", w!"remark"), (w!"rmk", w!"remark"), (w!"ex", w!"example"), (w!"exa", w!"example"),
   (w!"exm", w!"example"), (w!"conj", w!"conjecture"), (w!"obs", w!"lemma")] ++ kindWords

def lower (c : Nat) : Nat := if 65 ≤ c && c ≤ 90 then c + 32 else c

/-- The letter runs of a printed name that are not command names, in lower case. -/
def nameWords : Codes → Bool → List Codes → Codes → List Codes
  | [], _, acc, cur => (if cur.isEmpty then acc else cur.reverse :: acc).reverse
  | c :: cs, cmd, acc, cur =>
    if isLetter c then
      if cmd then nameWords cs true acc cur else nameWords cs false acc (lower c :: cur)
    else
      let acc := if cur.isEmpty then acc else cur.reverse :: acc
      nameWords cs (c == 92) acc []

/-- The kind of result a printed theorem name names, if any. -/
def kindOf (printed : Codes) : Option Codes :=
  (nameWords printed false [] []).findSome? (fun w => kindWords.lookup w)

/-- The environment an article's environment name stands for: its declared alias,
an abbreviation, or the name itself (a starred result environment is the result). -/
def envAlias (macros : Macros) (env : Codes) : Codes :=
  let base := if env.getLast? == some 42 then env.dropLast else env
  match macros.lookup (123 :: env) with
  | some k => k
  | none =>
    match macros.lookup (123 :: base) with
    | some k => k
    | none =>
      if kindWords.any (·.2 == base) then base
      else match kindAbbrevs.lookup base with
        | some k => if macros.any (·.1 == 123 :: base) then env else k
        | none => env

/-- One undelimited macro argument: a braced group, a control sequence or a
character, after spaces; with the number of code points read. -/
def readArg (cs : Codes) : Codes × Codes × Nat :=
  let (r, sp) := spaces cs
  match r with
  | 123 :: r' =>
    match group 100000 0 r' [] with
    | some (a, r'', n) => (a, r'', sp + 1 + n)
    | none => ([], r, sp)
  | 92 :: r' =>
    let (m, r'') := takeWhile isLetter r'
    if m.isEmpty then (92 :: r'.take 1, r'.drop 1, sp + 2) else (92 :: m, r'', sp + 1 + m.length)
  | c :: r' => ([c], r', sp + 1)
  | [] => ([], [], sp)

/-- The arguments of a macro of arity `k`, the first optional with default `d`. -/
def readArgs : Nat → Option Codes → Codes → List Codes × Codes × Nat
  | 0, _, cs => ([], cs, 0)
  | k + 1, some d, cs =>
    let (r, sp) := spaces cs
    let (a, r', m) := match r with
      | 91 :: r1 => let (a, b) := takeWhile (· != 93) r1; (a, b.drop 1, sp + a.length + 2)
      | _ => (d, cs, 0)
    let (as, r'', m') := readArgs k none r'
    (a :: as, r'', m + m')
  | k + 1, none, cs =>
    let (a, r, m) := readArg cs
    let (as, r', m') := readArgs k none r
    (a :: as, r', m + m')

/-- The body of a macro with `#1`…`#9` replaced by its arguments (and `##` by `#`). -/
def substArgs (as : List Codes) : Codes → Codes
  | [] => []
  | 35 :: 35 :: r => 35 :: substArgs as r
  | 35 :: d :: r => if 49 ≤ d && d ≤ 57 then as.getD (d - 49) [] ++ substArgs as r else 35 :: substArgs as (d :: r)
  | c :: r => c :: substArgs as r

/-- A macro's expansion at a use: the body with its arguments, the rest of the
input and the number of code points the arguments took. -/
def expand (macros : Macros) (name body rest : Codes) : Codes × Codes × Nat :=
  match body with
  | 35 :: d :: b =>
    if 49 ≤ d && d ≤ 57 then
      let (as, r, k) := readArgs (d - 48) (macros.lookup (name ++ [35])) rest
      (substArgs as b, r, k)
    else (body, rest, 0)
  | _ => (body, rest, 0)

/-- Sectioning commands. -/
def wSections : List Codes :=
  [w!"section", w!"section*", w!"subsection", w!"subsubsection", w!"paragraph"]

/-- The label of the result a section title such as `Proof of Theorem~\ref{l}`
or `The proof of \cref{l}` announces the proof of. -/
def proofOfTitle (title : Codes) : Option Codes :=
  let ws := nameWords title false [] []
  let opens := ws.take 2 == [w!"proof", w!"of"] || ws.take 2 == [w!"proofs", w!"of"] ||
    ws.take 3 == [w!"the", w!"proof", w!"of"]
  let rec findRef : Nat → Codes → Option Codes
    | 0, _ => none
    | _, [] => none
    | f + 1, c :: cs =>
      if c == 92 then
        let (m, r) := takeWhile isLetter cs
        if (m == w!"ref" || wSelfRefs.contains m) && r.head? == some 123 then
          some (takeWhile (· != 125) (r.drop 1)).1
        else findRef f r
      else findRef f cs
  if opens then findRef title.length title else none

/-- Directly after `\item` (or `\item[…]`): the emitted tokens, latest first. -/
def afterItem (out : List PTok) : Bool :=
  match out with
  | ⟨.cmd i, _, _⟩ :: _ => i == w!"item"
  | ⟨.punct 93, _, _⟩ :: rest =>
    match rest.dropWhile (fun p => p.tok != .cmd w!"item" && p.tok != .par) with
    | ⟨.cmd i, _, _⟩ :: _ => i == w!"item" && (rest.takeWhile (·.tok != .cmd w!"item")).length ≤ 8
    | _ => false
  | _ => false

/-- Lexer state: the remaining input, its offset and the mode stack (`true` entries
are math modes opened by `$`, `false` by other delimiters). -/
def lexAux (macros : Macros) : Nat → Codes → Nat → List Bool → List PTok →
    Option (List PTok × List Bool)
  | 0, _, _, _, _ => none
  | _ + 1, [], _, st, out => some (out.reverse, st)
  | f + 1, c :: cs, pos, st, out =>
    let math := !st.isEmpty
    let emit (t : Tok) (rest : Codes) (n : Nat) (st' : List Bool) :=
      lexAux macros f rest (pos + n) st' (⟨t, pos, math⟩ :: out)
    -- comments
    if c == 37 then
      let (_, rest) := takeWhile (· != 10) cs
      lexAux macros f (rest.drop 1) (pos + 1 + (cs.length - rest.length) + (if rest.isEmpty then 0 else 1)) st out
    else if isSpace c then
      -- a blank line in text mode is a paragraph break
      if c == 10 && !math then
        let (rest, n) := spaces cs
        let blank := (cs.take n).any (· == 10)
        if blank then lexAux macros f rest (pos + 1 + n) st (⟨.par, pos, false⟩ :: out)
        else lexAux macros f rest (pos + 1 + n) st out
      else lexAux macros f cs (pos + 1) st out
    else if c == 36 then
      match st, cs with
      | true :: st', _ => lexAux macros f cs (pos + 1) st' (⟨.mclose, pos, true⟩ :: out)
      -- `$$…$$` is a display, like `\[…\]`
      | [], 36 :: ds =>
        lexAux macros f ds (pos + 2) [false] (⟨.begin w!"displaymath", pos, false⟩ :: out)
      | false :: st', 36 :: ds =>
        lexAux macros f ds (pos + 2) st' (⟨.finish w!"displaymath", pos, true⟩ :: out)
      | _, _ => lexAux macros f cs (pos + 1) (true :: st) (⟨.mopen, pos, true⟩ :: out)
    else if c == 92 then
      match cs with
      | [] => none
      | d :: ds =>
        if !isLetter d then
          -- control symbols
          if d == 40 then lexAux macros f ds (pos + 2) (false :: st) (⟨.mopen, pos, true⟩ :: out)
          else if d == 91 then
            lexAux macros f ds (pos + 2) (false :: st) (⟨.begin w!"displaymath", pos, math⟩ :: out)
          else if d == 41 then
            match st with
            | false :: st' => lexAux macros f ds (pos + 2) st' (⟨.mclose, pos, true⟩ :: out)
            | _ => none
          else if d == 93 then
            match st with
            | false :: st' => lexAux macros f ds (pos + 2) st' (⟨.finish w!"displaymath", pos, true⟩ :: out)
            | _ => none
          else if d == 44 || d == 33 || d == 59 || d == 58 || d == 32 || d == 10 then
            lexAux macros f ds (pos + 2) st out
          else if d == 92 then
            let (rest, n) := optArg ds
            emit (.csym 92) rest (2 + n) st
          else emit (.csym d) ds 2 st
        else
          let (name0, rest0) := takeWhile isLetter cs
          let (name, rest) := match rest0 with
            | 42 :: r => if name0 == w!"section" then (name0 ++ [42], r) else (name0, rest0)
            | _ => (name0, rest0)
          let n := name.length + 1
          match macros.lookup name with
          | some body0 =>
            let (body, rest, k) := expand macros name body0 rest
            -- (the body without the macro itself: `\let\old\longmapsto` and then
            -- `\renewcommand{\longmapsto}{…\old…}` uses the original `\longmapsto`)
            match lexAux (macros.filter (·.1 != name)) f body pos st [] with
            -- (a macro may open or close a formula: `\newcommand{\be}{\begin{equation}}`)
            | some (ts, st') => lexAux macros f rest (pos + n + k) st' (ts.reverse ++ out)
            -- a body the lexer cannot read (layout code with `\makeatletter` internals) is an
            -- unknown command
            | none => lexAux macros f rest (pos + n + k) st (⟨.cmd name, pos, math⟩ :: out)
          | none =>
          if name == w!"begin" || name == w!"end" then
            match rest with
            | 123 :: r =>
              let (env0, r') := takeWhile (· != 125) r
              let len := n + env0.length + 2
              let env := envAlias macros env0
              let isDisplay := wDisplayEnvs.contains env
              -- drawings and verbatim text are not prose: skipped to their end
              if name == w!"begin" && wSkipEnvs.contains env0 then
                let close := w!"\\end{" ++ env0 ++ w!"}"
                let rec find : Nat → Codes → Nat → Option (Codes × Nat)
                  | 0, _, _ => none
                  | _ + 1, [], _ => none
                  | g + 1, d :: ds, k =>
                    if (d :: ds).take close.length == close then some ((d :: ds).drop close.length, k + close.length)
                    else find g ds (k + 1)
                match find (r'.length + 1) (r'.drop 1) 0 with
                | some (r'', k) => lexAux macros f r'' (pos + len + k) st out
                | none => none
              else
              if name == w!"begin" then
                -- the options of a list environment are layout
                let (r'', k) := if wListEnvs.contains env then optArg (r'.drop 1) else (r'.drop 1, 0)
                emit (.begin env) r'' (len + k) (if isDisplay then false :: st else st)
              else
                let st' := if isDisplay then st.drop 1 else st
                lexAux macros f (r'.drop 1) (pos + len) st' (⟨.finish env, pos, math⟩ :: out)
            | _ => none
          else if name == w!"label" || name == w!"ref" || name == w!"eqref" || name == w!"cite"
              || name == w!"citep" || name == w!"citet" || wSelfRefs.contains name then
            -- (`\ref*{l}`, `\cref*{l}`: the starred forms print the same reference)
            let (rest, nStar) := match rest with
              | 42 :: r => (r, 1)
              | _ => (rest, 0)
            let (r1, n1) := optArg rest
            -- (spaces and a line break may stand before the braces: `\cite[Lemma~2]` at the
            -- end of a line, `{key}` on the next)
            let sp := (r1.takeWhile fun c => c == 32 || c == 10 || c == 9).length
            let (r1, n1) := (r1.drop sp, n1 + nStar + sp)
            match r1 with
            | 123 :: r =>
              let (arg, r') := takeWhile (· != 125) r
              -- `\cref{l}` prints its own noun (`Lemma 2.1`): it cites like `\eqref{l}`
              let kind := if name == w!"label" then RefKind.label else if name == w!"ref" then .ref
                else if name == w!"eqref" || wSelfRefs.contains name then .eqref else .cite
              emit (.ref kind arg) (r'.drop 1) (n + n1 + arg.length + 2) st
            -- (`\label` as a name in drawing code: `\foreach \x/\label in …`)
            | _ => emit (.cmd name) rest n st
          else if wSkipArgs.contains name then
            -- skip an optional argument and all directly following braced groups
            let rec skip : Nat → Codes → Nat → Option (Codes × Nat)
              | 0, r, k => some (r, k)
              | g + 1, r, k =>
                let (r1, n1) := optArg r
                match r1 with
                | 123 :: r2 =>
                  match group 100000 0 r2 [] with
                  | some (_, r3, n3) => skip g r3 (k + n1 + 1 + n3)
                  | none => none
                | _ => some (r1, k + n1)
            -- `\subsection{Proof of Theorem~\ref{l}}`: a proof of the result `l`
            let proofOf : Option Codes :=
              if wSections.contains name then
                match (optArg rest).1 with
                | 123 :: r => match group 100000 0 r [] with
                  | some (title, _, _) => proofOfTitle title
                  | none => none
                | _ => none
              else none
            match skip 4 rest 0, proofOf with
            | some (r, k), some l =>
              lexAux macros f r (pos + n + k) st
                (⟨.ref .ref l, pos, math⟩ :: ⟨.begin w!"@proofsec", pos, math⟩ :: ⟨.cmd name, pos, math⟩ :: out)
            | some (r, k), none =>
              -- an equation tag is layout
              if name == w!"tag" then lexAux macros f r (pos + n + k) st out
              else emit (.cmd name) r (n + k) st
            | none, _ => none
          else if !math && wDropText.contains name then
            -- `\item \emph{$A\ge z$ and $B\le1+z$.}`: the heading of a case, not a claim
            if afterItem out && (name == w!"emph" || name == w!"textit" || name == w!"textbf") then
              emit (.cmd w!"@heading") rest n st
            else lexAux macros f rest (pos + n) st out
          else if math && wDropMath.contains name then lexAux macros f rest (pos + n) st out
          else if math && (name == w!"text" || name == w!"textup" || name == w!"textrm" ||
              name == w!"mbox" || name == w!"textnormal") then
            -- `\text{for every integer }`: words, as in the running text (anything but words
            -- and punctuation keeps the letters, as before)
            match rest with
            | 123 :: r =>
              match group 100000 0 r [] with
              | some (inner, r', k) =>
                match lexAux macros f inner (pos + n + 1) [] [] with
                | some (ts, []) =>
                  if !ts.isEmpty && ts.all (fun p => match p.tok with | .word _ | .punct _ => true | _ => false) then
                    lexAux macros f r' (pos + n + 1 + k) st
                      (⟨.rbrace, pos + n + k, true⟩ :: (ts.reverse.map fun p => { p with math := true }) ++
                        ⟨.lbrace, pos + n, true⟩ :: ⟨.cmd w!"text", pos, true⟩ :: out)
                  else emit (.cmd name) rest n st
                | _ => emit (.cmd name) rest n st
              | none => emit (.cmd name) rest n st
            | _ => emit (.cmd name) rest n st
          else if math then
            match mathAlias name with
            | some t => emit t rest n st
            | none => emit (.cmd name) rest n st
          else emit (.cmd name) rest n st
    else if c == 123 then
      if math then emit .lbrace cs 1 st else lexAux macros f cs (pos + 1) st out
    else if c == 125 then
      if math then emit .rbrace cs 1 st else lexAux macros f cs (pos + 1) st out
    else if math then
      if isLetter c then emit (.mvar c) cs 1 st
      -- digits are separate tokens, as in TeX (`\frac14`); the grammar groups numerals
      else if isDigit c then emit (.mnum (c - 48)) cs 1 st
      else emit (.msym c) cs 1 st
    else if isWordChar c then
      let (w, rest) := takeWhile isWordChar (c :: cs)
      emit (.word w) rest w.length st
    else emit (.punct c) cs 1 st

/-! ### Macros

The preamble's macros are expanded where they are used: `\newcommand`,
`\renewcommand` and `\providecommand` (starred or not, with or without braces
around the name), with up to nine arguments and an optional first argument,
`\def` with undelimited arguments, `\DeclareMathOperator` (an operator name) and
`\let`. A macro with arguments is kept with its body prefixed by `#n` (a
parameterless body never starts with `#`), and the default of an optional first
argument under the name followed by `#`. -/

/-- A control sequence name after optional spaces: `\name`, `{\name}`, or a
control symbol. -/
def csName (cs : Codes) : Option (Codes × Codes) :=
  match (spaces cs).1 with
  | 123 :: r =>
    match (spaces r).1 with
    | 92 :: r =>
      let (m, r') := takeWhile isLetter r
      let (m, r') := if m.isEmpty then (r.take 1, r.drop 1) else (m, r')
      match (spaces r').1 with
      | 125 :: r'' => some (m, r'')
      | _ => none
    | _ => none
  | 92 :: r =>
    let (m, r') := takeWhile isLetter r
    if m.isEmpty then some (r.take 1, r.drop 1) else some (m, r')
  | _ => none

/-- The arity marker of a macro body, `#n`. -/
def arityMark (n : Nat) : Codes := if n == 0 then [] else [35, 48 + n]

/-- `[n]` and `[default]` of a `\newcommand`, then the braced body: the body with
its arity marker, the default of an optional first argument, and the rest. -/
def macroDef (r : Codes) : Option (Codes × Option Codes × Codes) :=
  let r := (spaces r).1
  let (n, r) := match r with
    | 91 :: d :: 93 :: r => if isDigit d then (d - 48, r) else (0, 91 :: d :: 93 :: r)
    | r => (0, r)
  let r := (spaces r).1
  let (dflt, r) := match n, r with
    | _ + 1, 91 :: r => let (a, b) := takeWhile (· != 93) r; (some a, b.drop 1)
    | _, r => (none, r)
  match (spaces r).1 with
  | 123 :: body =>
    match group 100000 0 body [] with
    | some (b, r', _) => some (arityMark n ++ b, dflt, r')
    | none => none
  | _ => none

/-- The parameters of a `\def`: `#1#2…` up to the body; `none` for delimited parameters. -/
def defParams : Codes → Nat → Option (Nat × Codes)
  | 123 :: r, n => some (n, 123 :: r)
  | 35 :: d :: r, n => if d == 49 + n then defParams r (n + 1) else none
  | _, _ => none

/-- Add a definition; a later definition of the same name replaces the earlier one. -/
def define (m b : Codes) (acc : Macros) : Macros := (m, b) :: acc.filter (·.1 != m)

/-- The macros and theorem environments of a preamble. -/
def macrosAux : Nat → Codes → Macros → Option Macros
  | 0, _, _ => none
  | _ + 1, [], acc => some acc.reverse
  | f + 1, c :: cs, acc =>
    if c == 92 then
      let (name, rest) := takeWhile isLetter cs
      if name == w!"newtheorem" then
        -- `\newtheorem{env}[counter]{Printed}[within]`, `\newtheorem*{env}{Printed}`
        let r := (spaces (match rest with | 42 :: r => r | r => r)).1
        match r with
        | 123 :: r =>
          let (env, r1) := takeWhile (· != 125) r
          let (r2, _) := optArg (spaces (r1.drop 1)).1
          match (spaces r2).1 with
          | 123 :: r3 =>
            match group 100000 0 r3 [] with
            | some (printed, r4, _) =>
              match kindOf printed with
              | some k => macrosAux f r4 ((123 :: env, k) :: acc)
              | none => macrosAux f r4 acc
            | none => macrosAux f r3 acc
          | r2 => macrosAux f r2 acc
        | r => macrosAux f r acc
      else if name == w!"declaretheorem" then
        -- `\declaretheorem[name=Printed, …]{env}`, `\declaretheorem{theorem}`
        let (opts, r) := match rest with
          | 91 :: r => let (a, b) := takeWhile (· != 93) r; (a, b.drop 1)
          | r => ([], r)
        match (spaces r).1 with
        | 123 :: r =>
          let (env, r1) := takeWhile (· != 125) r
          match kindOf opts <|> kindOf env with
          | some k => macrosAux f (r1.drop 1) ((123 :: env, k) :: acc)
          | none => macrosAux f (r1.drop 1) acc
        | r => macrosAux f r acc
      else if name == w!"newcommand" || name == w!"renewcommand" || name == w!"providecommand" then
        let r := match rest with | 42 :: r => r | r => r
        match csName r with
        | some (m, r') =>
          match macroDef r' with
          | some (b, dflt, r'') =>
            if name == w!"providecommand" && acc.any (·.1 == m) then macrosAux f r'' acc
            else
              let acc := (define m b acc).filter (·.1 != m ++ [35])
              let acc := match dflt with | some d => (m ++ [35], d) :: acc | none => acc
              macrosAux f r'' acc
          | none => macrosAux f r' acc
        | none => macrosAux f rest acc
      else if name == w!"def" then
        match csName rest with
        | some (m, r') =>
          match defParams r' 0 with
          | some (n, 123 :: body) =>
            match group 100000 0 body [] with
            | some (b, r'', _) => macrosAux f r'' (define m (arityMark n ++ b) acc)
            | none => macrosAux f r' acc
          | _ => macrosAux f r' acc
        | none => macrosAux f rest acc
      else if name == w!"DeclareMathOperator" then
        let r := match rest with | 42 :: r => r | r => r
        match csName r with
        | some (m, r') =>
          match (spaces r').1 with
          | 123 :: body =>
            match group 100000 0 body [] with
            | some (b, r'', _) => macrosAux f r'' (define m (w!"\\operatorname{" ++ b ++ [125]) acc)
            | none => macrosAux f r' acc
          | _ => macrosAux f r' acc
        | none => macrosAux f rest acc
      else if name == w!"let" then
        match csName rest with
        | some (m, r') =>
          let r' := match (spaces r').1 with | 61 :: r => r | r => r
          match csName r' with
          | some (t, r'') =>
            -- `\let\a\b` makes `\a` the current meaning of `\b`
            let b := match acc.lookup t with | some b => b | none => 92 :: t
            if t.all isLetter || t.length == 1 then macrosAux f r'' (define m b acc) else macrosAux f r'' acc
          | none => macrosAux f r' acc
        | none => macrosAux f rest acc
      else macrosAux f rest acc
    else macrosAux f cs acc

end Lex

def macrosOf (preamble : Codes) : Option Macros := Lex.macrosAux (preamble.length + 1) preamble []

def lex (macros : Macros) (input : Codes) (offset : Nat := 0) : Option (List PTok) :=
  match Lex.lexAux macros (4 * input.length + 16) input offset [] [] with
  | some (ts, []) => some ts
  | _ => none

/-! ## Source and paragraph blocks

The source is the list of its lines, each a list of code points. Blank lines
separate paragraph blocks. Each block is lexed on its own, with positions
relative to the block's start, so that the lexing of a block depends only on
its text, the preamble macros and the math mode it starts in. -/

abbrev Source := List Codes

/-- The text of lines, each followed by a newline. -/
def joinLines (ls : List Codes) : Codes := (ls.map fun l => l ++ [10]).flatten

/-- Offset just after the given lines (each followed by a newline). -/
def linesOffset (ls : List Codes) : Nat := ls.foldl (fun a l => a + l.length + 1) 0

def blankLine (l : Codes) : Bool := l.all Lex.isSpace

/-- The number of occurrences of `pat` in `l`. -/
def countSub (pat : Codes) : Codes → Nat
  | [] => 0
  | c :: cs => (if (c :: cs).take pat.length == pat then 1 else 0) + countSub pat cs

/-- Do the lines open a drawing or verbatim environment that they do not close (a
blank line inside it does not end the block)? -/
def openSkip (ls : List Codes) : Bool :=
  Lex.wSkipEnvs.any fun e =>
    let b := ls.foldl (fun n l => n + countSub (w!"\\begin{" ++ e ++ w!"}") l) 0
    let d := ls.foldl (fun n l => n + countSub (w!"\\end{" ++ e ++ w!"}") l) 0
    d < b

/-- Group lines into paragraph blocks (start offset, lines); blank lines separate
blocks, except inside a drawing or verbatim environment. -/
def blocksOf : List Codes → Nat → Option (Nat × List Codes) → List (Nat × List Codes) → List (Nat × List Codes)
  | [], _, cur, acc => (cur.toList ++ acc).reverse
  | l :: ls, pos, cur, acc =>
    if blankLine l && !(cur.any fun (_, c) => openSkip c) then blocksOf ls (pos + l.length + 1) none (cur.toList ++ acc)
    else match cur with
      | none => blocksOf ls (pos + l.length + 1) (some (pos, [l])) acc
      | some (p, c) => blocksOf ls (pos + l.length + 1) (some (p, c ++ [l])) acc

/-- Lex one paragraph block (positions relative to its start), continuing the
math-mode stack. -/
def lexBlock (macros : Macros) (block : Codes) (st : List Bool) : Option (List PTok × List Bool) :=
  Lex.lexAux macros (4 * block.length + 16) block 0 st []

/-- The paragraph break after a block (none inside an open formula). -/
def blockBreak (st : List Bool) : List PTok := if st.isEmpty then [⟨.par, 0, false⟩] else []

/-- The key of a block's lexing: the macros, the math-mode stack it starts in and
its text determine its tokens. Equal keys name the same cached certificate (the
kernel still compares the literals, so a collision cannot cause harm). -/
def lexKey (macros : Macros) (st : List Bool) (block : Codes) : String :=
  let enc (c : Codes) : String := Codes.toString c
  let ms := String.intercalate "\u0001" (macros.map fun (n, b) => enc n ++ "\u0002" ++ enc b)
  let s := ms ++ "\u0003" ++ String.ofList (st.map fun b => if b then '1' else '0') ++ "\u0003" ++ enc block
  let h := s.toUTF8.foldl (fun (h : UInt64) b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325
  let hex := String.ofList (Nat.toDigits 16 h.toNat)
  String.ofList (List.replicate (16 - hex.length) '0') ++ hex

/-- Shift token positions by a block's start offset. -/
def PTok.shift (base : Nat) (t : PTok) : PTok := { t with pos := t.pos + base }

end Leanify
