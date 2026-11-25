import Leanify.Library.Core

/-! # Vocabulary: geometric and wave optics

Images, resolution, diffraction and polarization, by their parameters (`We write $f(n,a,b)$ for the focal length by the lensmaker's equation for refractive index $n$
and radii $a$ and $b$.`). Snell's law, critical angles and the thin-lens focal length from the
object and image distances are in the field `waves`.

* notions: the focal length `1/((n-1)(1/R₁ - 1/R₂))` (lensmaker's equation); the image distance
  `1/(1/f - 1/d_o)` and the magnification `-d_i/d_o` of a thin lens; the Rayleigh angle
  `1.22λ/D` of a circular aperture; the angle of the `m`th order of a grating (`d sin θ = mλ`),
  of the `m`th minimum of a single slit (`a sin θ = mλ`) and of Bragg reflection
  (`2d sin θ = nλ`), as angles in `[0, π/2]`; the transmitted intensity `I₀cos²θ` (Malus's
  law).

Every meaning is a term of the core language. -/

namespace Leanify.Optics
open Build Core

def pos (x : B) : B := lt (num 0) x
def sin (x : B) : B := app (prim (.realFn .sin)) x
def cos (x : B) : B := app (prim (.realFn .cos)) x
def pi : B := prim .pi
def nz (x : B) : B := ne x (num 0)
def angle (t : B) : B := and (le (num 0) t) (le t (div pi (num 2)))
/-- The angle `θ ∈ [0, π/2]` with `sin θ = s`. -/
def asinAngle (s : B) : B := theR fun t => and (angle t) (eq (sin t) s)
def order (name : Phrase) (k : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real fun m => and (isInt m) (le (num 0) m), dom2 .real fun _ l => pos l,
      dom3 .real fun m l d => and (pos d) (le (mul m l) (mul (num k) d))], doc,
    value := close <| lamT .real (fun m => and (isInt m) (le (num 0) m)) fun m => lamT .real pos fun l =>
      lamT .real (fun d => and (pos d) (le (mul m l) (mul (num k) d))) fun d => asinAngle (div (mul m l) (mul (num k) d)) }

def vocab : Vocab where
  notions := [
    { name := phrase!"focal length by the lensmaker's equation for refractive index $v$ and radii $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun n => lt (num 1) n, dom2 .real fun _ a => nz a, dom3 .real fun _ a b => and (nz b) (ne a b)],
      doc := "`1/((n-1)(1/R₁ - 1/R₂))`, with signed radii",
      value := close <| lamT .real (fun n => lt (num 1) n) fun n => lamT .real nz fun a => lamT .real (fun b => and (nz b) (ne a b)) fun b =>
        div (num 1) (mul (sub n (num 1)) (sub (div (num 1) a) (div (num 1) b))) },
    { name := phrase!"image distance of a thin lens of focal length $v$ for the object distance $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real nz, dom2 .real fun f o => and (pos o) (ne o f)],
      doc := "`1/(1/f - 1/d_o)` (thin lens equation)",
      value := close <| lamT .real nz fun f => lamT .real (fun o => and (pos o) (ne o f)) fun o => div (num 1) (sub (div (num 1) f) (div (num 1) o)) },
    { name := phrase!"magnification for the object distance $v$ and the image distance $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, none], doc := "`-d_i/d_o`",
      value := close <| lamT .real pos fun o => lamR fun i => neg (div i o) },
    { name := phrase!"Rayleigh angle for the wavelength $v$ and the aperture diameter $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ d => pos d], doc := "`1.22λ/D` (small angles)",
      value := close <| lamT .real pos fun l => lamT .real pos fun d => div (mul (div (num 122) (num 100)) l) d },
    order phrase!"angle of the $v$th order of a grating for the wavelength $v$ and the spacing $v$" 1
      "the `θ ∈ [0, π/2]` with `d sin θ = mλ`",
    order phrase!"angle of the $v$th minimum of a single slit for the wavelength $v$ and the width $v$" 1
      "the `θ ∈ [0, π/2]` with `a sin θ = mλ`",
    order phrase!"Bragg angle of order $v$ for the wavelength $v$ and the spacing $v$" 2
      "the `θ ∈ [0, π/2]` with `2d sin θ = nλ`",
    { name := phrase!"transmitted intensity for the intensity $v$ at the polarizer angle $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun i => le (num 0) i, none], doc := "`I₀cos²θ` (Malus's law)",
      value := close <| lamT .real (fun i => le (num 0) i) fun i => lamR fun t => mul i (mul (cos t) (cos t)) }]

end Leanify.Optics
