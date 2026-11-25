import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `cryptography`: residues and modular powers, RSA moduli, totients, decryption exponents and ciphertexts, discrete logarithms and Diffie-Hellman keys. After editing the article, run

    lake exe leanify prepare tests/Cryptography/article.tex --lean tests/Cryptography/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `cryptography`. -/
def Cryptography.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["cryptography"]

#leanify_article Cryptography "article.tex" "fnv1a64:6a241cb6258b7f61" with Cryptography.vocabulary
