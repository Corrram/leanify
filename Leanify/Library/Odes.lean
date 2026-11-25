import Leanify.Library.Core

/-! # Vocabulary: classical ordinary differential equations

The classical first- and second-order equations by their coefficient functions, and the
Wronskian (`$y$ is a solution of the Bernoulli equation with coefficients $p$ and $q$ and
exponent $n$`). The equations with a right-hand side `f(t, y)` and the numerical methods are in
the field `odesolvers`.

* adjectives of functions: `solution of the first-order linear equation with coefficients $a$
  and $b$` (`y' = a(t) y + b(t)`), `solution of the separable equation with factors $g$ and $h$`
  (`y' = g(t) h(y)`), `solution of the Bernoulli equation with coefficients $p$ and $q$ and
  exponent $n$` (`y' + p(t) y = q(t) y^n`), `solution of the Riccati equation with coefficients
  $p$, $q$ and $r$` (`y' = p(t) + q(t) y + r(t) y²`), `solution of the second-order linear
  equation with coefficients $p$ and $q$` (`y'' + p(t) y' + q(t) y = 0`), `solution of the
  Euler-Cauchy equation with coefficients $a$ and $b$` (`t² y'' + a t y' + b y = 0` for `t > 0`),
  `solution of the harmonic oscillator equation with frequency $\omega$` (`y'' + ω² y = 0`),
  `solution of the damped oscillator equation with damping $c$ and frequency $\omega$`
  (`y'' + 2c y' + ω² y = 0`), each everywhere (`t > 0` for Euler–Cauchy) with the derivatives
  existing;
* notions: the Wronskian of `f` and `g` at `t` (`f g' - f' g`).

Derivatives are descriptions; every meaning is a term of the core language. -/

namespace Leanify.Odes
open Build Core

abbrev F : Ty := Ty.rfun

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def deriv (f x : B) : B := theR fun d => hasDeriv f x d
def diffAt (f x : B) : B := exR fun d => hasDeriv f x d
def d1 (f : B) : B := lamR fun t => deriv f t
def diff (f : B) : B := allR fun t => diffAt f t
def twice (f : B) : B := and (diff f) (diff (d1 f))
def everywhere (body : B → B) : B := allR fun t => body t
def rpow (x y : B) : B := app2 (prim .rpow) x y
def any (_ : B) : B := tt
def y' (y t : B) : B := deriv y t
def y'' (y t : B) : B := deriv (d1 y) t
def sol (p : Phrase) (pred : Tm) (doc : String) : Modifier := { phrase := p, prenominal := false, ty := F, pred, doc }

def vocab : Vocab where
  mods := [
    sol phrase!"solution of the first-order linear equation with coefficients $v$ and $v$"
      (close <| lamT F any fun a => lamT F any fun b => lamT F any fun y =>
        and (diff y) (everywhere fun t => eq (y' y t) (add (mul (app a t) (app y t)) (app b t))))
      "`y' = a(t) y + b(t)` everywhere",
    sol phrase!"solution of the separable equation with factors $v$ and $v$"
      (close <| lamT F any fun g => lamT F any fun h => lamT F any fun y =>
        and (diff y) (everywhere fun t => eq (y' y t) (mul (app g t) (app h (app y t)))))
      "`y' = g(t) h(y)` everywhere",
    sol phrase!"solution of the Bernoulli equation with coefficients $v$ and $v$ and exponent $v$"
      (close <| lamT F any fun p => lamT F any fun q => lamR fun n => lamT F any fun y =>
        and (diff y) (everywhere fun t => eq (add (y' y t) (mul (app p t) (app y t))) (mul (app q t) (rpow (app y t) n))))
      "`y' + p(t) y = q(t) y^n` everywhere",
    sol phrase!"solution of the Riccati equation with coefficients $v$, $v$ and $v$"
      (close <| lamT F any fun p => lamT F any fun q => lamT F any fun r => lamT F any fun y =>
        and (diff y) (everywhere fun t => eq (y' y t) (add (add (app p t) (mul (app q t) (app y t))) (mul (app r t) (mul (app y t) (app y t))))))
      "`y' = p(t) + q(t) y + r(t) y²` everywhere",
    sol phrase!"solution of the second-order linear equation with coefficients $v$ and $v$"
      (close <| lamT F any fun p => lamT F any fun q => lamT F any fun y =>
        and (twice y) (everywhere fun t => eq (add (add (y'' y t) (mul (app p t) (y' y t))) (mul (app q t) (app y t))) (num 0)))
      "`y'' + p(t) y' + q(t) y = 0` everywhere",
    sol phrase!"solution of the Euler-Cauchy equation with coefficients $v$ and $v$"
      (close <| lamR fun a => lamR fun b => lamT F any fun y =>
        and (twice y) (allR fun t => imp (lt (num 0) t)
          (eq (add (add (mul (mul t t) (y'' y t)) (mul (mul a t) (y' y t))) (mul b (app y t))) (num 0))))
      "`t² y'' + a t y' + b y = 0` for `t > 0`",
    sol phrase!"solution of the harmonic oscillator equation with frequency $v$"
      (close <| lamR fun w => lamT F any fun y =>
        and (twice y) (everywhere fun t => eq (add (y'' y t) (mul (mul w w) (app y t))) (num 0)))
      "`y'' + ω² y = 0` everywhere",
    sol phrase!"solution of the damped oscillator equation with damping $v$ and frequency $v$"
      (close <| lamR fun c => lamR fun w => lamT F any fun y =>
        and (twice y) (everywhere fun t => eq (add (add (y'' y t) (mul (mul (num 2) c) (y' y t))) (mul (mul w w) (app y t))) (num 0)))
      "`y'' + 2c y' + ω² y = 0` everywhere"]
  notions := [
    { name := phrase!"Wronskian of $v$ and $v$ at $v$", ty := F ⟶ F ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun f g t => and (diffAt f t) (diffAt g t)],
      doc := "`f(t) g'(t) - f'(t) g(t)`",
      value := close <| lamT F any fun f => lamT F any fun g => lamT .real (fun t => and (diffAt f t) (diffAt g t)) fun t =>
        sub (mul (app f t) (deriv g t)) (mul (deriv f t) (app g t)) }]

end Leanify.Odes
