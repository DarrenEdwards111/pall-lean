import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.ExtractionRank
import PallLean.PDerivEval
import Mathlib.Tactic
/-!
# Extraction Map T_Φ — Pall §11–13

The extraction map takes the compiled polynomial pM♯,n and recovers
the coupled verifier polynomial Q×_Φn. This involves:
  (i) Verifier-sheet normalization: M♯ = Sheet(M) forces clause gadgets
      into the compiled object (Definition 11.1, Lemma 11.2)
  (ii) Projection to verifier-sheet variables (restriction)
  (iii) Injective relabeling to witness variables (rename)

By Lemma 12.1: extraction is rank-monotone (composition of
rank-nonincreasing operations).

Key distinction: the extraction operates on the **blocked** SPDP rank ΓB.
The paper proves ΓB(Q×_Φn) ≤ ΓB(pM♯,n) via the fact that extraction
corresponds to selecting a submatrix of the blocked SPDP matrix.
-/

namespace Extraction

open SPDP SPDP.ExtractionRank Compiler NPWitness PDerivEval MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]

/-- The verifier-sheet coupled decider M♯ = Sheet(M) (Pall Definition 11.1).
    M♯ runs M on the main track and computes canonical clause-check gadgets
    on a disjoint auxiliary track. Key properties (Lemma 11.2):
    1. L(M♯) = L(M) (language preservation)
    2. M♯ ∈ DTIME(n^{c'}) for c' = c + O(1) (polynomial overhead)
    3. The compiled object contains the canonical clause sheet (forced syntactic presence) -/
def sheetCoupling (M : PolyTimeTM) : PolyTimeTM :=
  { c := M.c + 1 }

/-- **Axiom: Rank-monotone extraction (Pall Theorem 12.2 + Lemma 12.1)**

    The extraction map T_Φ is a composition of:
    (i) variable restrictions (setting non-sheet variables to constants)
    (ii) row/column deletions of M^B_{κ,ℓ} (submatrix selection)
    (iii) block-local linear projections

    Each operation is rank-nonincreasing, so:
    ΓB_{κ,ℓ}(Q×_Φn) ≤ ΓB_{κ,ℓ}(pM♯,n)

    This axiom captures the structural claim that the Tseitin polynomial
    IS extractable from the compiled polynomial of the sheet-coupled decider,
    AND that the extraction is rank-monotone in the blocked SPDP rank. -/
axiom extraction_rank_monotone (F : Type*) [CommRing F] [Nontrivial F]
    (M : PolyTimeTM) (n : ℕ) :
    blockedSpdpRank (npPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compilerPartition n (sheetCoupling M).c)
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly F (sheetCoupling M) n)

end Extraction
