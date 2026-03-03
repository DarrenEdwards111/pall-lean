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

/-- **Extraction rank monotonicity (Theorem 12.2)**

    ΓB(Q×_Φn) ≤ ΓB(p_{M♯,n})

    The extraction pipeline (projection, restriction, relabeling, gauge)
    transforms p_{M♯,n} into Q×_Φn. Each stage is rank-nonincreasing:
    - Projection: subspace containment → finrank ≤
    - Restriction: setting variables → rank monotone
    - Relabeling: injective rename → rank invariant
    - Gauge normalization: rank nonincreasing

    The extraction map TΦ is the composition of four rank-nonincreasing stages:
    (i)   Projection to verifier blocks — row/column deletion
    (ii)  Witness-free restriction v := 0 — variable restriction
    (iii) Affine relabeling — injective rename (rank-preserving)
    (iv)  Block-local gauge normalization — rank-nonincreasing

    Each stage satisfies: Γ^B(output) ≤ Γ^B(input) by:
    - (i): submatrix has rank ≤ original (Lemma 13.18(a))
    - (ii): restriction monotonicity (§2 Basic Property 3)
    - (iii): injective rename preserves rank (§2 Basic Property 4)
    - (iv): gauge normalization is block-local linear (Lemma 13.18(d)) -/
theorem extraction_rank_monotone (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n)
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf F (sheetCoupling M) n) := by
  -- Thm 12.2: extraction pipeline TΦ = gauge ∘ relabel ∘ restrict ∘ project
  -- Each stage is rank-nonincreasing, so composition is rank-nonincreasing.
  -- Q×_Φ = TΦ(p_{M♯,n}), hence Γ^B(Q×) ≤ Γ^B(p_{M♯,n}).
  sorry

end Extraction
