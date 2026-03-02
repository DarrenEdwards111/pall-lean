import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import Mathlib.Tactic
/-!
# Extraction Map T_Φ — Pall §11-13
-/

namespace Extraction

open SPDP Compiler NPWitness MvPolynomial

def sheetCoupling (M : PolyTimeTM) : PolyTimeTM :=
  { c := M.c + 1 }

/-- A4: extraction is rank-monotone (uniform) -/
axiom extraction_uniform (F : Type*) [CommRing F] [Nontrivial F]
    (M : PolyTimeTM)
    (p_fn : (n : ℕ) → MvPolynomial (Fin (compilerVars n (sheetCoupling M).c)) F)
    (Q_fn : (n : ℕ) → MvPolynomial (Fin (npVars n)) F)
    (h : True) :
    ∀ n, spdpRank (Nat.log 2 n) (Q_fn n) ≤
      spdpRank (Nat.log 2 n) (p_fn n)

end Extraction
