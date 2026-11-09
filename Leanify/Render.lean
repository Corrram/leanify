import Leanify.Doc

/-! # Formal readings

Renders compiled terms as explicit mathematics: quantifiers, domains and
definedness guards are written out. This rendering is for reading only; it is
not part of any certificate. -/
namespace Leanify

def Ty.tex : Ty → String
  | .real => "\\mathbb{R}"
  | .unit => "[0,1]"
  | .prop => "\\mathrm{Prop}"
  | .fn a b => (match a with | .fn .. => "(" ++ a.tex ++ ")" | _ => a.tex) ++ "\\to " ++ b.tex
  | .base k => s!"\\mathsf\{T}_\{{k}}"

def varNames : List String := ["x", "y", "z", "s", "t", "a", "b", "p", "q", "w", "k", "m"] ++
  (List.range 40).map fun i => s!"v_\{{i + 1}}"

def FnProp.word : FnProp → String
  | .convex => "convex" | .strictConvex => "strictly\\ convex" | .strictConcave => "strictly\\ concave"
  | .strictAnti => "decreasing" | .monotone => "nondecreasing" | .antitone => "nonincreasing"
  | .bounded => "bounded" | .nonneg => "nonnegative" | .pos => "positive"
  | .differentiable => "differentiable" | .contDiff => "C^1" | .injective => "injective"
  | .lowerSemicont => "lsc" | .upperSemicont => "usc" | .lipschitz => "Lipschitz"

def SetProp.word : SetProp → String
  | .closed => "closed" | .isOpen => "open" | .bounded => "bounded" | .connected => "connected"

def SqProp.word : SqProp → String
  | .convex => "convex" | .concave => "concave" | .lowerUniform => "lsc\\ (uniform)"
  | .upperUniform => "usc\\ (uniform)" | .contUniform => "continuous\\ (uniform)"

def ClassProp.word : ClassProp → String
  | .convex => "convex" | .compactUniform => "compact\\ (uniform)" | .closedUniform => "closed\\ (uniform)"

def Prim.tex : Prim → String
  | .rpow => "\\operatorname{pow}" | .min => "\\min" | .max => "\\max"
  | .leb => "\\lambda" | .borel => "\\operatorname{Borel}"
  | .measurableSet1 | .measurableSet2 => "\\operatorname{Meas}"
  | .integrable => "\\operatorname{Int}" | .hasDerivWithin => "\\operatorname{HasDeriv}"
  | .intervalIntegral => "\\int" | .intervalIntegrable => "\\operatorname{Int}"
  | .compact2 => "\\operatorname{compact}" | .convex2 => "\\operatorname{convex}"
  | .symm2 => "\\operatorname{symmetric}" | .continuousOn => "\\operatorname{continuous}"
  | .concaveOn => "\\operatorname{concave}" | .strictMonoOn => "\\operatorname{increasing}"
  | .fnProp k => "\\operatorname{" ++ k.word ++ "}"
  | .setProp k => "\\operatorname{" ++ k.word ++ "}"
  | .sqProp k => "\\operatorname{" ++ k.word ++ "}"
  | .classProp k => "\\operatorname{" ++ k.word ++ "}"
  | .realFn k => match k with
    | .exp => "\\exp" | .log => "\\log" | .sin => "\\sin" | .cos => "\\cos" | .tan => "\\tan"
  | .pi => "\\pi"
  | .isInt => "\\mathbb{Z}" | .isNat => "\\mathbb{N}"
  | .floor => "\\operatorname{floor}" | .ceil => "\\operatorname{ceil}"
  | .finSum => "\\sum" | .finProd => "\\prod" | .series => "\\sum"
  | .seriesConv => "\\operatorname{converges}" | .limAt | .limTop => "\\lim"
  | .limAtConv | .limTopConv => "\\operatorname{exists}"
  | .factorial => "\\operatorname{factorial}" | .binom => "\\binom" | .zpow => "\\operatorname{pow}"
  | .smoothN _ => "\\operatorname{smooth}" | .compactSuppIn _ => "\\operatorname{compactSupportIn}"
  | .supportIn _ => "\\operatorname{supportIn}" | .isCompactN _ => "\\operatorname{compact}"
  | .l2NormN _ => "\\operatorname{L2norm}" | .supNormN _ => "\\operatorname{supnorm}"
  | .integralN _ => "\\operatorname{integral}" | .partialMulti _ => "\\operatorname{partials}"
  | .cardIs => "\\operatorname{card}"

/-- Binding strength for parentheses: propositions (1–4), relations (5), sums (6),
products (7), signs (8), atoms (9). -/
def Tm.prec : Tm → Nat
  | .iff .. => 1 | .imp .. => 2 | .or .. => 3 | .and .. => 4
  | .all .. | .ex .. | .the .. => 0
  -- a predicate applied to an argument is read as its body
  | .app (.app (.lam _ _ (.lam _ _ b)) _) _ => b.prec
  | .app (.lam _ _ b) _ => b.prec
  | .eq .. | .lt .. | .le .. => 5
  | .add .. | .sub .. => 6
  | .mul .. | .div .. => 7
  | .neg .. => 8
  | _ => 9

/-- A numeral or a quotient of numerals (displayed without its coercion to `[0,1]`). -/
def Tm.isNumeral : Tm → Bool
  | .num _ => true
  | .div x y => x.isNumeral && y.isNumeral
  | _ => false

/-- The domain of a limit at infinity, when it is the natural numbers (the limit of a
sequence): the reading says so, since `\lim_{n\to\infty}` and `\lim_{x\to\infty}` are
different limits. -/
def seqDom (D : Tm) (v : String) : String :=
  match D with
  | .lam _ _ (.and (.app (.prim .isNat) (.loc 0)) _) => ",\\ " ++ v ++ "\\in \\mathbb{N}"
  | _ => ""

partial def Tm.tex (cs gs : List String) (ls : List String) : Tm → String
  | .glob i => gs.getD i s!"g_{i}"
  | .loc i => ls.getD i s!"v_{i}"
  | .prim p => p.tex
  | .const i => cs.getD i s!"c_{i}"
  | .app (.app (.app (.prim .finSum) a) b) (.lam _ _ body) =>
    let v := varNames.getD ls.length "k"
    "\\sum_{" ++ v ++ "=" ++ a.tex cs gs ls ++ "}^{" ++ b.tex cs gs ls ++ "}" ++ body.tex cs gs (v :: ls)
  | .app (.app (.app (.prim .finProd) a) b) (.lam _ _ body) =>
    let v := varNames.getD ls.length "k"
    "\\prod_{" ++ v ++ "=" ++ a.tex cs gs ls ++ "}^{" ++ b.tex cs gs ls ++ "}" ++ body.tex cs gs (v :: ls)
  | .app (.app (.prim .series) a) (.lam _ _ body) =>
    let v := varNames.getD ls.length "k"
    "\\sum_{" ++ v ++ "=" ++ a.tex cs gs ls ++ "}^{\\infty}" ++ body.tex cs gs (v :: ls)
  | .app (.app (.prim .seriesConv) a) (.lam _ _ body) =>
    let v := varNames.getD ls.length "k"
    "\\sum_{" ++ v ++ "=" ++ a.tex cs gs ls ++ "}^{\\infty}" ++ body.tex cs gs (v :: ls) ++ "\\text{ converges}"
  | .app (.app (.app (.prim .limAt) a) _) (.lam _ _ body) =>
    let v := varNames.getD ls.length "x"
    "\\lim_{" ++ v ++ "\\to " ++ a.tex cs gs ls ++ "}" ++ body.tex cs gs (v :: ls)
  | .app (.app (.app (.prim .limAtConv) a) _) (.lam _ _ body) =>
    let v := varNames.getD ls.length "x"
    "\\lim_{" ++ v ++ "\\to " ++ a.tex cs gs ls ++ "}" ++ body.tex cs gs (v :: ls) ++ "\\text{ exists}"
  | .app (.app (.prim .limTop) D) (.lam _ _ body) =>
    let v := varNames.getD ls.length "x"
    "\\lim_{" ++ v ++ "\\to\\infty" ++ seqDom D v ++ "}" ++ body.tex cs gs (v :: ls)
  | .app (.app (.prim .limTopConv) D) (.lam _ _ body) =>
    let v := varNames.getD ls.length "x"
    "\\lim_{" ++ v ++ "\\to\\infty" ++ seqDom D v ++ "}" ++ body.tex cs gs (v :: ls) ++ "\\text{ exists}"
  | .app (.prim .factorial) x => wrap 9 x ++ "!"
  | .app (.app (.prim .binom) x) y => "\\binom{" ++ x.tex cs gs ls ++ "}{" ++ y.tex cs gs ls ++ "}"
  | .app (.guard _ (.app (.prim .binom) x)) y => "\\binom{" ++ x.tex cs gs ls ++ "}{" ++ y.tex cs gs ls ++ "}"
  | .app (.app (.prim .zpow) x) y => "{" ++ wrap 9 x ++ "}^{" ++ y.tex cs gs ls ++ "}"
  | .app (.prim .isInt) x => x.tex cs gs ls ++ "\\in \\mathbb{Z}"
  | .app (.prim .isNat) x => x.tex cs gs ls ++ "\\in \\mathbb{N}"
  | .app (.prim .floor) x => "\\lfloor " ++ x.tex cs gs ls ++ "\\rfloor"
  | .app (.prim .ceil) x => "\\lceil " ++ x.tex cs gs ls ++ "\\rceil"
  | .app (.app (.prim .rpow) x) y => "{" ++ wrap 9 x ++ "}^{" ++ y.tex cs gs ls ++ "}"
  | .app (.app (.prim .min) x) y => "\\min\\{" ++ x.tex cs gs ls ++ "," ++ y.tex cs gs ls ++ "\\}"
  | .app (.app (.prim .max) x) y => "\\max\\{" ++ x.tex cs gs ls ++ "," ++ y.tex cs gs ls ++ "\\}"
  | .app (.app (.app (.app (.prim .hasDerivWithin) f) s) x) d =>
      "(" ++ f.tex cs gs ls ++ ")'(" ++ x.tex cs gs ls ++ ")=" ++ d.tex cs gs ls ++ "\\text{ within }" ++ s.tex cs gs ls
  | .app (.prim .leb) s => "\\lambda\\bigl(" ++ s.tex cs gs ls ++ "\\bigr)"
  -- a property of a function on a domain: `continuous(f) on {x : …}`
  | .app (.app (.prim .continuousOn) f) (.lam _ _ body) =>
      let v := varNames.getD ls.length "t"
      Prim.continuousOn.tex ++ "(" ++ f.tex cs gs ls ++ ")\\text{ on }\\{" ++ v ++ ":" ++ body.tex cs gs (v :: ls) ++ "\\}"
  | .app (.app (.prim .concaveOn) f) (.lam _ _ body) =>
      let v := varNames.getD ls.length "t"
      Prim.concaveOn.tex ++ "(" ++ f.tex cs gs ls ++ ")\\text{ on }\\{" ++ v ++ ":" ++ body.tex cs gs (v :: ls) ++ "\\}"
  | .app (.app (.prim .strictMonoOn) f) (.lam _ _ body) =>
      let v := varNames.getD ls.length "t"
      Prim.strictMonoOn.tex ++ "(" ++ f.tex cs gs ls ++ ")\\text{ on }\\{" ++ v ++ ":" ++ body.tex cs gs (v :: ls) ++ "\\}"
  | .app (.app (.prim (.fnProp k)) f) (.lam _ _ body) =>
      let v := varNames.getD ls.length "t"
      Prim.tex (.fnProp k) ++ "(" ++ f.tex cs gs ls ++ ")\\text{ on }\\{" ++ v ++ ":" ++ body.tex cs gs (v :: ls) ++ "\\}"
  | .app (.app (.prim (.sqProp k)) f) d =>
      Prim.tex (.sqProp k) ++ "(" ++ f.tex cs gs ls ++ ")\\text{ on }" ++ d.tex cs gs ls
  | .app (.app (.app (.prim .intervalIntegral) a) b) (.lam _ _ body) =>
      let v := varNames.getD ls.length "t"
      "\\int_{" ++ a.tex cs gs ls ++ "}^{" ++ b.tex cs gs ls ++ "}" ++ body.tex cs gs (v :: ls) ++ "\\,d" ++ v
  -- a constant of the vocabulary named by an operator (a method of a type: `+` on the
  -- complex numbers) is written as that operator: `+`, `-`, `\cdot`, `/` between its
  -- arguments, `^` as a power, `\sum` and `\prod` as sums; `#` in its name stands for
  -- its argument (`\lvert#\rvert`), and an empty name is its argument (a real number
  -- as an element of the type)
  | .app (.app (.app (.const i) a) b) (.lam ty d body) =>
    let n := cs.getD i s!"c_{i}"
    if n == "\\sum" || n == "\\prod" then
      let v := varNames.getD ls.length "k"
      n ++ "_{" ++ v ++ "=" ++ a.tex cs gs ls ++ "}^{" ++ b.tex cs gs ls ++ "}" ++ cwrap 7 body (v :: ls)
    else (Tm.app (.app (.const i) a) b).tex cs gs ls ++ "(" ++ (Tm.lam ty d body).tex cs gs ls ++ ")"
  | .app (.app (.const i) x) y =>
    let n := cs.getD i s!"c_{i}"
    match n with
    | "+" => cwrap 6 x ls ++ "+" ++ cwrap 7 y ls
    | "-" => cwrap 6 x ls ++ "-" ++ cwrap 7 y ls
    | "\\cdot" => cwrap 7 x ls ++ "\\," ++ cwrap 8 y ls
    | "/" => "\\frac{" ++ x.tex cs gs ls ++ "}{" ++ y.tex cs gs ls ++ "}"
    | "^" => "{" ++ cwrap 9 x ls ++ "}^{" ++ y.tex cs gs ls ++ "}"
    | _ => (Tm.app (.const i) x).tex cs gs ls ++ "(" ++ y.tex cs gs ls ++ ")"
  | .app (.const i) x =>
    let n := cs.getD i s!"c_{i}"
    if n.isEmpty then x.tex cs gs ls
    else if n == "-" then "-" ++ cwrap 8 x ls
    else if (n.splitOn "#").length > 1 then "".intercalate (n.splitOn "#" |>.intersperse (x.tex cs gs ls))
    else n ++ "(" ++ x.tex cs gs ls ++ ")"
  -- a domain predicate applied to an argument: read it about the argument
  | .app (.app (.lam _ _ (.lam _ _ b)) x) y => b.tex cs gs (y.tex cs gs ls :: x.tex cs gs ls :: ls)
  | .app (.lam _ _ b) x => b.tex cs gs (x.tex cs gs ls :: ls)
  -- a function of several variables: `f(x,y)` (definedness guards are not shown)
  -- a partial derivative of multi-index order at a point: `\partial^{(i,j)}f(x,y)`
  | .app (.app f x) y =>
    let rec mspine : Nat → Tm → List Tm → Option (Nat × Tm × List Tm)
      | 0, _, _ => none
      | k + 1, .app g a, acc => mspine k g (a :: acc)
      | k + 1, .guard _ e, acc => mspine k e acc
      | _ + 1, .the _ (.app (.app (.prim (.partialMulti n)) F) (.loc 0)), acc => some (n, F, acc)
      | _ + 1, _, _ => none
    let multi : Option String := match mspine 32 f [x, y] with
      | some (n, F, args) =>
        if n < args.length then
          let v := varNames.getD ls.length "v"
          some ("\\partial^{(" ++ ",".intercalate ((args.take n).map (·.tex cs gs ls)) ++ ")}" ++
            F.tex cs gs (v :: ls) ++ "(" ++ ",".intercalate ((args.drop n).map (·.tex cs gs ls)) ++ ")")
        else none
      | none => none
    match multi with
    | some s => s
    | none =>
    let rec spine : Nat → Tm → List Tm → Option (Nat × List Tm)
      | 0, _, _ => none
      | k + 1, .app g a, acc => spine k g (a :: acc)
      | k + 1, .guard _ e, acc => spine k e acc
      | _ + 1, .glob i, acc => some (i, acc)
      | _ + 1, .loc i, acc => some (1000000 + i, acc)
      | _ + 1, _, _ => none
    match spine 16 f [x, y] with
    | some (i, args) =>
      let n := if i ≥ 1000000 then ls.getD (i - 1000000) "?" else gs.getD i s!"g_{i}"
      if n.startsWith "^" || n == "\\widehat" then
        (Tm.app f x).tex cs gs ls ++ "(" ++ y.tex cs gs ls ++ ")"
      else n ++ "(" ++ ",".intercalate (args.map (·.tex cs gs ls)) ++ ")"
    | none => (Tm.app f x).tex cs gs ls ++ "(" ++ y.tex cs gs ls ++ ")"
  | .app (.glob i) x =>
    let n := gs.getD i s!"g_{i}"
    if n.startsWith "^" then "{" ++ wrap 9 x ++ "}" ++ n
    else if n == "\\widehat" then "\\widehat{" ++ x.tex cs gs ls ++ "}"
    else n ++ "(" ++ x.tex cs gs ls ++ ")"
  | .app f x => (match f with
      | .lam .. => "(" ++ f.tex cs gs ls ++ ")"
      | _ => f.tex cs gs ls) ++ "(" ++ x.tex cs gs ls ++ ")"
  | .lam t d b =>
    let v := varNames.getD ls.length "v"
    let dom := match d with | .tt => "" | d => "\\,[" ++ d.tex cs gs (v :: ls) ++ "]"
    "(" ++ v ++ "\\in " ++ t.tex ++ dom ++ "\\mapsto " ++ b.tex cs gs (v :: ls) ++ ")"
  | .num n => toString n
  | .ofUnit x => x.tex cs gs ls
  | .toUnit x => if x.isNumeral then x.tex cs gs ls else "\\langle " ++ x.tex cs gs ls ++ "\\rangle_{[0,1]}"
  | .add x y => wrap 6 x ++ "+" ++ wrap 7 y
  | .sub x y => wrap 6 x ++ "-" ++ wrap 7 y
  | .mul x y => wrap 7 x ++ "\\," ++ wrap 8 y
  | .div x y => "\\frac{" ++ x.tex cs gs ls ++ "}{" ++ y.tex cs gs ls ++ "}"
  | .neg x => "-" ++ wrap 8 x
  | .abs x => "\\lvert " ++ x.tex cs gs ls ++ "\\rvert"
  | .powNat x n => "{" ++ wrap 9 x ++ "}^{" ++ toString n ++ "}"
  | .cases c v r => "\\begin{cases}" ++ v.tex cs gs ls ++ "&" ++ c.tex cs gs ls ++ "\\\\" ++
      (cases r) ++ "\\end{cases}"
  | .undef _ => "\\bot"
  | .eq x y => wrap 1 x ++ "=" ++ wrap 1 y
  | .lt x y => wrap 1 x ++ "<" ++ wrap 1 y
  | .le x y => wrap 1 x ++ "\\le " ++ wrap 1 y
  | .tt => "\\top"
  -- an infinite set: it has no number of elements
  | .not (.ex .real (.app (.app (.prim .cardIs) (.lam _ _ b)) (.loc 0))) =>
    let v := varNames.getD (ls.length + 1) "u"
    "\\#\\{" ++ v ++ " : " ++ b.tex cs gs (v :: "" :: ls) ++ "\\}=\\infty"
  | .not .tt => "\\bot"
  | .not p => "\\neg " ++ wrap 9 p
  | .and p q => wrap 5 p ++ "\\land " ++ wrap 4 q
  | .or p q => wrap 4 p ++ "\\lor " ++ wrap 3 q
  | .imp p q => wrap 3 p ++ "\\Rightarrow " ++ wrap 2 q
  | .iff p q => wrap 2 p ++ "\\Leftrightarrow " ++ wrap 2 q
  | .all t b => let v := varNames.getD ls.length "v"
    "\\forall " ++ v ++ "\\in " ++ t.tex ++ ",\\ " ++ b.tex cs gs (v :: ls)
  | .ex t b => let v := varNames.getD ls.length "v"
    "\\exists " ++ v ++ "\\in " ++ t.tex ++ ",\\ " ++ b.tex cs gs (v :: ls)
  | .integral b => let v := varNames.getD ls.length "v"
    let s := b.tex cs gs (v :: ls)
    "\\int_0^1 " ++ (if b.prec < 7 then "(" ++ s ++ ")" else s) ++ "\\,d" ++ v
  | .guard _ e => e.tex cs gs ls
  -- the least upper (greatest lower) bound of a set, as `\sup` and `\inf` compile
  | .the .real (.and (.all .real (.imp p (.le (.loc 0) (.loc 1))))
      (.all .real (.imp (.all .real (.imp _ (.le (.loc 0) (.loc 1)))) (.le (.loc 1) (.loc 0))))) =>
    let v := varNames.getD ls.length "v"
    "\\sup\\{" ++ v ++ "\\in \\mathbb{R} : " ++ p.tex cs gs (v :: "\\_" :: ls) ++ "\\}"
  | .the .real (.and (.all .real (.imp p (.le (.loc 1) (.loc 0))))
      (.all .real (.imp (.all .real (.imp _ (.le (.loc 1) (.loc 0)))) (.le (.loc 0) (.loc 1))))) =>
    let v := varNames.getD ls.length "v"
    "\\inf\\{" ++ v ++ "\\in \\mathbb{R} : " ++ p.tex cs gs (v :: "\\_" :: ls) ++ "\\}"
  -- a (partial) derivative: `\frac{d}{ds} f(s,y)|_{s=x}`
  | .the .real (.app (.app (.app (.app (.prim .hasDerivWithin) (.lam _ _ body)) (.lam _ _ .tt)) x) (.loc 0)) =>
    let z := varNames.getD ls.length "z"
    let v := varNames.getD (ls.length + 1) "v"
    "\\tfrac{\\mathrm{d}}{\\mathrm{d}" ++ v ++ "}" ++ body.tex cs gs (v :: z :: ls) ++
      "\\big|_{" ++ v ++ "=" ++ x.tex cs gs (z :: ls) ++ "}"
  -- the partial derivatives of every order of `f`
  | .the _ (.app (.app (.prim (.partialMulti _)) f) (.loc 0)) =>
    let v := varNames.getD ls.length "v"
    "\\partial^{\\bullet}" ++ f.tex cs gs (v :: ls)
  -- a norm or an integral over `ℝⁿ`
  | .the .real (.app (.app (.prim p) f) (.loc 0)) =>
    let v := varNames.getD ls.length "v"
    let fs := f.tex cs gs (v :: ls)
    match p with
    | .l2NormN _ => "\\lVert " ++ fs ++ "\\rVert_{L^2}"
    | .supNormN _ => "\\lVert " ++ fs ++ "\\rVert_{L^\\infty}"
    | .integralN n => "\\int_{\\mathbb{R}^{" ++ toString n ++ "}} " ++ fs
    -- the number of elements of a set
    | .cardIs => match f with
      | .lam _ _ b =>
        let u := varNames.getD (ls.length + 1) "u"
        "\\#\\{" ++ u ++ " : " ++ b.tex cs gs (u :: v :: ls) ++ "\\}"
      | _ => "\\#" ++ fs
    | _ => "\\iota " ++ v ++ "\\in \\mathbb{R}.\\ " ++ (Tm.app (.app (.prim p) f) (.loc 0)).tex cs gs (v :: ls)
  -- a derivative within a domain (one-sided at an end point)
  | .the .real (.app (.app (.app (.app (.prim .hasDerivWithin) (.lam _ _ body)) dom) x) (.loc 0)) =>
    let z := varNames.getD ls.length "z"
    let v := varNames.getD (ls.length + 1) "v"
    "\\tfrac{\\mathrm{d}}{\\mathrm{d}" ++ v ++ "}" ++ body.tex cs gs (v :: z :: ls) ++
      "\\big|_{" ++ v ++ "=" ++ x.tex cs gs (z :: ls) ++ "}^{" ++ (Tm.app dom (.loc 0)).tex cs gs (v :: z :: ls) ++ "}"
  | .the t b => let v := varNames.getD ls.length "v"
    "\\iota " ++ v ++ "\\in " ++ t.tex ++ ".\\ " ++ b.tex cs gs (v :: ls)
where
  /-- `t`, parenthesized when it binds more loosely than `p`. -/
  wrap (p : Nat) (t : Tm) : String :=
    let s := t.tex cs gs ls
    if t.prec < p then "(" ++ s ++ ")" else s
  /-- The binding strength of a term, with the constants named by operators. -/
  cprec (t : Tm) : Nat := match t with
    | .app (.app (.const i) _) _ => match cs.getD i "" with
      | "+" | "-" => 6
      | "\\cdot" => 7
      | _ => t.prec
    | .app (.const i) x =>
      let n := cs.getD i ""
      if n == "-" then 8 else if n.isEmpty then cprec x else t.prec
    | .guard _ e => cprec e
    | _ => t.prec
  /-- `t` in the names `ls`, in parentheses if it binds less than `p`. -/
  cwrap (p : Nat) (t : Tm) (ls : List String) : String :=
    let s := t.tex cs gs ls
    if cprec t < p then "(" ++ s ++ ")" else s
  cases : Tm → String
    | .cases c v r => v.tex cs gs ls ++ "&" ++ c.tex cs gs ls ++ "\\\\" ++ cases r
    | _ => ""

/-- A phrase as text: words separated by spaces, hyphens joined (`left-tail`). -/
def phraseText (ws : List Codes) : String :=
  let parts := ws.map Codes.toString
  (parts.zip ((none :: parts.map some).take parts.length)).foldl (fun acc (w, prev) =>
    if acc.isEmpty || w == "-" || prev == some "-" then acc ++ w else acc ++ " " ++ w) ""

/-- The abbreviation among the names of a definition (`LTD`, beside
`left-tail decreasing`): one short word, next to a name of several words. Words are
read in lower case, so it is set in capitals. -/
def abbreviation? (named : List (List Codes)) : Option String :=
  if named.any (·.length ≥ 2) then
    named.findSome? fun ws => match ws with
      | [w] => let s := Codes.toString w
        if s.length ≤ 6 then some (s.map Char.toUpper) else none
      | _ => none
  else none

/-- The symbol of each definition: its key, or for a definition named by a phrase
its abbreviation (`\operatorname{LTD}`), its word, or its phrase set as text. -/
def Doc.globNames (d : Doc) : List String :=
  (d.globs.zip (List.range d.globs.length)).map fun (g, i) =>
    if g.key.isEmpty then
      let named := (d.names.filter (·.2 == i)).map (·.1)
      match abbreviation? named, named.head? with
      | some a, _ => "\\operatorname{" ++ a ++ "}"
      | none, some [w] => "\\operatorname{" ++ Codes.toString w ++ "}"
      | none, some ws => "\\text{" ++ phraseText ws ++ "}"
      | none, none => s!"\\mathrm\{op}_\{{i}}"
    else Codes.toString g.key

/-- A Lean-identifier name for a definition: from the phrase that introduced it
(`the transpose of $C$` gives `transpose`, the class of `bivariate copulas`
gives `copulas`), or else from its symbol (`\nu` gives `nu`). -/
def defNameRaw (d : Doc) (i : Nat) : String :=
  let g := (d.globs[i]?).getD default
  let key := Codes.toString g.key
  let clean (s : String) : String := String.ofList ((s.replace "*" "Star").toList.filter Char.isAlphanum)
  let phrase := (d.names.find? (·.2 == i)).map (·.1.map (fun w => clean (Codes.toString w)))
  let camel (ps : List String) : String := match ps with
    | [] => s!"def{i}"
    | p :: ps => String.join (p :: ps.map String.capitalize)
  if key.isEmpty then (phrase.map camel).getD s!"def{i}"
  else if key.startsWith "^" || key == "\\widehat" || key == "\\hat" || key == "\\overline" then
    match phrase with
    | some (w :: _) => w
    | _ => clean key
  -- a decorated symbol: `\overline{\rho}` is `rhoBar`
  else if key.startsWith "\\overline{" || key.startsWith "\\bar{" then
    clean ((key.dropWhile (· != '{')).toString) ++ "Bar"
  else if key.startsWith "\\tilde{" then clean ((key.dropWhile (· != '{')).toString) ++ "Tilde"
  else if key.contains '{' then
    match phrase with
    | some ws@(_ :: _) => ws.getLast!
    | _ => clean key
  -- `\gamma^T` next to `\gamma_T`
  else if key.endsWith "^" then clean key ++ "Upper"
  -- `R_b^-`, `z_+`
  else if key.endsWith "^-" || key.endsWith "_-" then clean key ++ "Minus"
  else if key.endsWith "^+" || key.endsWith "_+" then clean key ++ "Plus"
  else clean key

/-- Names that `#leanify_article`, `#leanify_semantics` and `#leanify_certify`
declare in an article's namespace. -/
def reservedNames : List String :=
  ["G", "assembled", "b", "blocks", "bodyLine", "certificate", "claim", "claimCount", "claimRanks",
   "compiled", "definitionCount", "doc", "env", "envs", "envsEq", "finished", "lex", "lexSegmented",
   "macros", "mode", "model", "next", "paragraphs", "preamble", "ranAll", "ranChain", "rankedOk",
   "segFinished", "sentences", "sentencesRaw", "sentsSplit", "source", "sourceHash", "start", "t",
   "verifiedClaims", "vocab"]

/-- Prefixes of the numbered names they declare (`claim3`, `wellDefined0`, …). -/
def generatedPrefixes : List String :=
  ["claim", "meaningful", "obligation", "wellDefined", "welldef", "holds", "verified", "refuted", "lex",
   "defined", "proof", "refute"]

def isReservedName (n : String) : Bool :=
  reservedNames.contains n || generatedPrefixes.any fun p =>
    n.startsWith p && n.length > p.length && (n.drop p.length).all Char.isDigit

/-- The Lean name of definition `i`: its symbol, or its phrase, made unique by the
definition's index when an earlier definition has the same name. -/
def defName (d : Doc) (i : Nat) : String :=
  let n := defNameRaw d i
  let n := if (List.range i).any (fun j => defNameRaw d j == n) then s!"{n}{i}" else n
  -- a symbol whose name the commands use for themselves (`G`) gets a suffix
  if isReservedName n then n ++ "Def" else n

end Leanify
