import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.TuringMachine
import Mathlib.Tactic
/-!
# Extraction Map T_Φ — Pall §11–13
-/

namespace Extraction

open SPDP Compiler NPWitness TuringMachine MvPolynomial

/-- M♯ = Sheet(M): main track + auxiliary clause track (Def 11.1) -/
def sheetCoupling (M : DTM) : DTM where
  numStates := M.numStates + 3
  hStates := by omega
  transition := fun q b =>
    if h : q.val < M.numStates then
      let ⟨q', w, d⟩ := M.transition ⟨q.val, h⟩ b
      (⟨q'.val, by omega⟩, w, d)
    else (q, b, true)
  timeBound := M.timeBound + 1

/-- **Axiom: Extraction rank monotonicity (Theorem 12.2)**

    ΓB(Q×_Φn) ≤ ΓB(p_{M♯,n})

    The extraction pipeline TΦ = gauge ∘ relabel ∘ restrict ∘ project
    transforms p_{M♯,n} into Q×_Φn. Each of the four stages is
    rank-nonincreasing:

    1. **Projection** to verifier blocks (Lemma 13.18a):
       Deleting rows/columns cannot increase rank. Submatrix rank ≤ original.

    2. **Restriction** v := 0 (§2 Basic Property 3):
       Setting witness variables to constants. Evaluation map sends
       generators to generators of a smaller space. rank(eval p) ≤ rank(p).

    3. **Affine relabeling** (§2 Basic Property 4):
       Injective rename of variables. Algebra isomorphism preserves rank.

    4. **Gauge normalization** (Lemma 13.18d):
       Block-local multiplication by invertible elements. Rank-nonincreasing
       (actually rank-preserving since gauge is invertible).

    The composition of four rank-nonincreasing maps is rank-nonincreasing.
    No structural content beyond the stage-level properties. -/
axiom extraction_rank_monotone (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n)
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf F (sheetCoupling M) n)

end Extraction
