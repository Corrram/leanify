import Leanify.Library.Core

/-! # Vocabulary: elementary quantum mechanics

Energy levels, wavelengths and densities of the exactly solvable systems, with the constants of
nature as arguments (`We write $E(n,m,L,h)$ for the energy of the $n$th level of a particle of
mass $m$ in a box of length $L$ with Planck constant $h$.`).

* notions: the levels `n²h²/(8mL²)` of a particle in a box, `ħω(n + 1/2)` of a harmonic
  oscillator and `-R/n²` of the hydrogen atom; the probability density `(2/L) sin²(nπx/L)` of the
  `n`th state in a box; the de Broglie wavelength `h/p`; the photon energy `hf`; the wavelength
  `1/(R(1/m² - 1/n²))` of the hydrogen transition from level `n` to `m < n` (Rydberg); the
  Compton shift `λ_C(1 - cos θ)`.

Every meaning is a term of the core language. -/

namespace Leanify.Quantum
open Build Core

def pos (x : B) : B := lt (num 0) x
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def sin (x : B) : B := app (prim (.realFn .sin)) x
def cos (x : B) : B := app (prim (.realFn .cos)) x
def pi : B := prim .pi
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => body x y }

def vocab : Vocab where
  notions := [
    { name := phrase!"energy of the $v$th level of a particle of mass $v$ in a box of length $v$ with Planck constant $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun _ m => pos m, dom3 .real fun _ _ l => pos l, dom4 .real fun _ _ _ h => pos h],
      doc := "`n²h²/(8mL²)`",
      value := close <| lamT .real posInt fun n => lamT .real pos fun m => lamT .real pos fun l => lamT .real pos fun h =>
        div (mul (mul n n) (mul h h)) (mul (num 8) (mul m (mul l l))) },
    { name := phrase!"energy of the $v$th level of the harmonic oscillator with angular frequency $v$ and reduced Planck constant $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ w => pos w, dom3 .real fun _ _ h => pos h],
      doc := "`ħω(n + 1/2)`",
      value := close <| lamT .real natP fun n => lamT .real pos fun w => lamT .real pos fun h =>
        mul (mul h w) (add n (div (num 1) (num 2))) },
    { name := phrase!"energy of the $v$th level of the hydrogen atom with Rydberg energy $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun _ r => pos r],
      doc := "`-R/n²`",
      value := close <| lamT .real posInt fun n => lamT .real pos fun r => neg (div r (mul n n)) },
    { name := phrase!"probability density of the $v$th state of a particle in a box of length $v$ at $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun _ l => pos l, dom3 .real fun _ l x => and (le (num 0) x) (le x l)],
      doc := "`(2/L) sin²(nπx/L)` on `[0, L]`",
      value := close <| lamT .real posInt fun n => lamT .real pos fun l => lamT .real (fun x => and (le (num 0) x) (le x l)) fun x =>
        mul (div (num 2) l) (mul (sin (div (mul n (mul pi x)) l)) (sin (div (mul n (mul pi x)) l))) },
    two phrase!"de Broglie wavelength for momentum $v$ with Planck constant $v$" (fun p h => div h p) "`h/p`",
    two phrase!"energy of a photon of frequency $v$ with Planck constant $v$" (fun f h => mul h f) "`hf`",
    { name := phrase!"wavelength of the hydrogen transition from level $v$ to level $v$ with Rydberg constant $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun n m => and (posInt m) (lt m n), dom3 .real fun _ _ r => pos r],
      doc := "`1/(R(1/m² - 1/n²))`, from level `n` down to `m < n` (Rydberg's formula)",
      value := close <| lamT .real posInt fun n => lamT .real (fun m => and (posInt m) (lt m n)) fun m => lamT .real pos fun r =>
        div (num 1) (mul r (sub (div (num 1) (mul m m)) (div (num 1) (mul n n)))) },
    { name := phrase!"Compton shift for the scattering angle $v$ with Compton wavelength $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ l => pos l],
      doc := "`λ_C(1 - cos θ)`",
      value := close <| lamR fun t => lamT .real pos fun l => mul l (sub (num 1) (cos t)) }]

end Leanify.Quantum
