import Leanify.Library.Core

/-! # Vocabulary: public-key cryptography

The arithmetic of RSA, Diffie–Hellman and ElGamal by their parameters
(`We write $d$ for the RSA decryption exponent for the primes $p$ and $q$ and the encryption
exponent $e$.`). The residue `x mod n` is `x - n⌊x/n⌋`.

* notions: the residue of `x` modulo `n`; the modular power `a^k mod n`; the RSA modulus `pq`
  and its totient `(p-1)(q-1)`; the RSA decryption exponent (the `d ∈ [1, (p-1)(q-1)]` with
  `ed ≡ 1`, for `e` coprime to `(p-1)(q-1)`); the RSA ciphertext `m^e mod pq`; the discrete
  logarithm of `h` to the base `g` modulo `p` (the least `k ≥ 0` with `g^k ≡ h`, where there is
  one); the Diffie–Hellman shared key `g^{ab} mod p`.

Every meaning is a term of the core language. -/

namespace Leanify.Cryptography
open Build Core

def natP (k : B) : B := and (isInt k) (le (num 0) k)
def posInt (k : B) : B := and (isInt k) (le (num 1) k)
def modulus (n : B) : B := and (isInt n) (le (num 2) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def res (x n : B) : B := sub x (mul n (floor (div x n)))
def congr (x y n : B) : B := isInt (div (sub x y) n)
def phi (p q : B) : B := mul (sub p (num 1)) (sub q (num 1))
def coprime (a b : B) : B := allR fun d => imp (and (posInt d) (and (isInt (div a d)) (isInt (div b d)))) (eq d (num 1))
def rsaD (p q e : B) : B :=
  theR fun d => and (posInt d) (and (le d (phi p q)) (congr (mul e d) (num 1) (phi p q)))
def dlog (g h p : B) : B :=
  theR fun k => and (natP k) (and (congr (zpow g k) h p) (allR fun j => imp (and (natP j) (lt j k)) (not (congr (zpow g j) h p))))

def vocab : Vocab where
  notions := [
    { name := phrase!"residue of $v$ modulo $v$", ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real isInt, dom1 .real posInt],
      doc := "`x - n⌊x/n⌋ ∈ {0, …, n-1}`", value := close <| lamT .real isInt fun x => lamT .real posInt fun n => res x n },
    { name := phrase!"modular power $v$ to the $v$ modulo $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real isInt, dom1 .real natP, dom1 .real posInt],
      doc := "`a^k mod n`", value := close <| lamT .real isInt fun a => lamT .real natP fun k => lamT .real posInt fun n => res (zpow a k) n },
    { name := phrase!"RSA modulus for the primes $v$ and $v$", ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real modulus, dom1 .real modulus],
      doc := "`n = pq`", value := close <| lamT .real modulus fun p => lamT .real modulus fun q => mul p q },
    { name := phrase!"RSA totient for the primes $v$ and $v$", ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real modulus, dom1 .real modulus],
      doc := "`(p-1)(q-1)`", value := close <| lamT .real modulus fun p => lamT .real modulus fun q => phi p q },
    { name := phrase!"RSA decryption exponent for the primes $v$ and $v$ and the encryption exponent $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real modulus, dom1 .real modulus, dom3 .real fun p q e => and (posInt e) (coprime e (phi p q))],
      doc := "the `d ∈ [1, (p-1)(q-1)]` with `ed ≡ 1 (mod (p-1)(q-1))`",
      value := close <| lamT .real modulus fun p => lamT .real modulus fun q =>
        lamT .real (fun e => and (posInt e) (coprime e (phi p q))) fun e => rsaD p q e },
    { name := phrase!"RSA ciphertext of $v$ for the modulus $v$ and the exponent $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom1 .real modulus, dom1 .real posInt],
      doc := "`m^e mod n`", value := close <| lamT .real natP fun m => lamT .real modulus fun n => lamT .real posInt fun e => res (zpow m e) n },
    { name := phrase!"discrete logarithm of $v$ to the base $v$ modulo $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real isInt, dom1 .real isInt, dom3 .real fun h g p => and (modulus p) (exR fun k => and (natP k) (congr (zpow g k) h p))],
      doc := "the least `k ≥ 0` with `g^k ≡ h (mod p)`, where there is one",
      value := close <| lamT .real isInt fun h => lamT .real isInt fun g =>
        lamT .real (fun p => and (modulus p) (exR fun k => and (natP k) (congr (zpow g k) h p))) fun p => dlog g h p },
    { name := phrase!"Diffie-Hellman key for the base $v$, the modulus $v$ and the exponents $v$ and $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real isInt, dom1 .real modulus, dom1 .real posInt, dom1 .real posInt],
      doc := "`g^{ab} mod p`",
      value := close <| lamT .real isInt fun g => lamT .real modulus fun p => lamT .real posInt fun a => lamT .real posInt fun b =>
        res (zpow g (mul a b)) p }]

end Leanify.Cryptography
