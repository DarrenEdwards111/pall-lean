import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityRankCardinality

/-!
# The rank-based `x`-level speedup for parity-gate controls

`disjoint_fragment_speedup` gave the `x`-level speedup `2^k < 2^n` for disjoint gates.  This file gives the **rank**
version for parity (MOD₂) gates: the gate-output vector `x ↦ ((parityGate Sⱼ tⱼ).eval x)ⱼ` is a *relabeling* of the
parity vector (`eval = decide(parity = tⱼ)`), so its reachable image has cardinality `≤ 2^rank` (`parity_reachable_card`).
Hence the control SAT searches `≤ 2^rank` cells, and the `x`-level speedup fires whenever `2^rank < 2^n` (i.e.
`rank < n`) — strictly stronger than the disjoint `2^k`, since `rank ≤ k` with strict inequality under any linear
dependence among the parity gates.

## What is proved (clean axioms, no `sorry`)

* `image_parityVector_card` — `|univ.image (parityVector S)| = 2^rank` (Finset image vs `Nat.card` of the range).
* `parity_rank_speedup` — for a parity-gate control, `f`-SAT over `Fin n` ⟺ search the reachable gate-output image,
  whose card is `< 2^n` once `2^rank < 2^n`.

## Honest scope

The speedup boundary is the exact `2^rank` reachable-image (parity / MOD₂).  `rank < n` is the genuine condition (a
parity control whose gates span an `< n`-dimensional row space is sub-`2^n` searchable, even with overlapping supports).
General `MOD_q` is a `0/1`-feasibility problem over `ZMod q`, not free linear algebra.  Still the cell/observer model;
nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ParityRankSpeedup

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl
open PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization
open PallLean.Paper93.DeepMath.PathB.ACC0ParityRankCardinality

variable {n k : ℕ}

/-- **The reachable parity image as a `Finset` has card `2^rank` (proved).** -/
theorem image_parityVector_card (S : Fin k → Finset (Fin n)) :
    (Finset.univ.image (parityVector S)).card =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (parityLinMap S)) := by
  rw [← parity_reachable_card, Nat.card_eq_fintype_card, ← Set.toFinset_card, Set.toFinset_range]

/-- **The rank-based `x`-level speedup (proved): a parity-gate control's SAT searches the reachable gate-output image,
whose card is `< 2^n` once `2^rank < 2^n`.** -/
theorem parity_rank_speedup (C : OracleControl k) (S : Fin k → Finset (Fin n)) (t : Fin k → ZMod 2)
    (hrank : 2 ^ Module.finrank (ZMod 2) (LinearMap.range (parityLinMap S)) < 2 ^ n) :
    (Satisfiable (fun x => controlEval C (fun j => (parityGate (S j) (t j)).eval x)) ↔
        ∃ y ∈ Finset.univ.image (fun x : Fin n → Bool => fun j => (parityGate (S j) (t j)).eval x),
          controlEval C y = true)
      ∧ (Finset.univ.image (fun x : Fin n → Bool => fun j => (parityGate (S j) (t j)).eval x)).card
          < 2 ^ n := by
  refine ⟨control_sat_iff_reachable_image C (fun j => parityGate (S j) (t j)), ?_⟩
  have hge : (fun x : Fin n → Bool => fun j => (parityGate (S j) (t j)).eval x)
      = (fun y : Fin k → ZMod 2 => fun j => decide (y j = t j)) ∘ (parityVector S) := by
    funext x j; rfl
  rw [hge, ← Finset.image_image]
  exact lt_of_le_of_lt
    (le_trans Finset.card_image_le (le_of_eq (image_parityVector_card S))) hrank

end PallLean.Paper93.DeepMath.PathB.ACC0ParityRankSpeedup

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ParityRankSpeedup.image_parityVector_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ParityRankSpeedup.parity_rank_speedup
