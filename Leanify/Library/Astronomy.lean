import Leanify.Library.Core

/-! # Vocabulary: astronomy

Distances, magnitudes and the radiation of stars, with the constants of nature as arguments
(`We write $\mu(d)$ for the distance modulus at the distance of $d$ parsecs.`). Orbits are in
the field `mechanics`.

* notions: the distance `1/p` in parsecs for a parallax of `p` arcseconds; the distance modulus
  `5 log₁₀(d/10)`; the magnitude difference `-2.5 log₁₀ r` for a flux ratio `r`; the redshift
  `(λ_o - λ_e)/λ_e`; the recession speed `H₀d` (Hubble's law) and the Hubble time `1/H₀`; the
  Schwarzschild radius `2GM/c²`; the luminosity `4πR²σT⁴` of a star; the peak wavelength `b/T`
  (Wien's law).

Every meaning is a term of the core language. -/

namespace Leanify.Astronomy
open Build Core

def pos (x : B) : B := lt (num 0) x
def log10 (x : B) : B := div (app (prim (.realFn .log)) x) (app (prim (.realFn .log)) (num 10))
def pi : B := prim .pi
def one (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real pos], doc, value := close <| lamT .real pos body }
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => body x y }
def three (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y, dom3 .real fun _ _ z => pos z], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => lamT .real pos fun z => body x y z }

def vocab : Vocab where
  notions := [
    one phrase!"distance in parsecs for the parallax of $v$ arcseconds" (fun p => div (num 1) p) "`1/p`",
    one phrase!"distance modulus at the distance of $v$ parsecs" (fun d => mul (num 5) (log10 (div d (num 10)))) "`5 log₁₀(d/10)`: `m - M`",
    one phrase!"magnitude difference for the flux ratio $v$" (fun r => neg (mul (div (num 5) (num 2)) (log10 r)))
      "`-2.5 log₁₀ r`: `m₁ - m₂` for `F₁/F₂ = r`",
    two phrase!"redshift for the emitted wavelength $v$ and the observed wavelength $v$" (fun e o => div (sub o e) e) "`(λ_o - λ_e)/λ_e`",
    { name := phrase!"recession speed at the distance $v$ for the Hubble constant $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun d => le (num 0) d, dom2 .real fun _ h => pos h], doc := "`H₀d` (Hubble's law)",
      value := close <| lamT .real (fun d => le (num 0) d) fun d => lamT .real pos fun h => mul h d },
    one phrase!"Hubble time for the Hubble constant $v$" (fun h => div (num 1) h) "`1/H₀`",
    three phrase!"Schwarzschild radius of the mass $v$ with gravitational constant $v$ and the speed of light $v$"
      (fun m g c => div (mul (num 2) (mul g m)) (mul c c)) "`2GM/c²`",
    three phrase!"luminosity of a star of radius $v$ and temperature $v$ with Stefan-Boltzmann constant $v$"
      (fun r t s => mul (mul (num 4) pi) (mul (mul r r) (mul s (mul (mul t t) (mul t t))))) "`4πR²σT⁴`",
    two phrase!"peak wavelength at the temperature $v$ with Wien's constant $v$" (fun t b => div b t) "`b/T` (Wien's displacement law)"]

end Leanify.Astronomy
