import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHighOverlapAmortization
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MODResidualObserver

/-!
# Semantic transfer stress test: duplicate wide parity gates

The high-overlap engine proves that querying a high-degree variable destroys many syntactic incidences.  This file
tests the missing semantic transfer on the densest possible `MOD₂` family: `k` gates with the same wide support.

The result is an exact two-sided diagnosis:

* **semantic-inertia no-go:** while even one supported variable remains free, *every one* of the `k` parity gates is
  nonconstant.  Thus incidence surplus—even arbitrarily large surplus—does not imply gate elimination;
* **semantic quotient escape:** all duplicate gates compute exactly the same residual function, so their `k` copies
  quotient to one semantic profile.

Therefore the next viable potential must be measured **after semantic deduplication** (distinct residual
support/modulus/target profiles), not on syntactic gate occurrences.  High overlap among duplicate gates is fake
surplus; only high overlap among pairwise distinct residual functions could drive a genuine transfer theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.SemanticOverlapTransferNoGo

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel
open PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver
open PallLean.Paper93.DeepMath.PathB.FanoutAwareIncidencePotential

variable {n k : ℕ}

/-- The `k`-gate family in which every parity gate has the same support `S`. -/
def duplicateSupport (S : Finset (Fin n)) : Fin k → Finset (Fin n) := fun _ => S

/-- Live supported variables under restriction `ρ`. -/
def liveSupported (ρ : Restriction n) (S : Finset (Fin n)) : Finset (Fin n) :=
  freeSet ρ ∩ S

/-- Duplicate-wide incidence is the full gate/live product. -/
theorem duplicate_incidence_eq (ρ : Restriction n) (S : Finset (Fin n)) :
    incidenceCredit (Finset.univ : Finset (Fin k)) (duplicateSupport S) (liveSupported ρ S)
      = k * (liveSupported ρ S).card := by
  have hsub : liveSupported ρ S ⊆ S := by
    intro i hi
    exact (Finset.mem_inter.mp hi).2
  have hinter : S ∩ liveSupported ρ S = liveSupported ρ S := inter_eq_right.mpr hsub
  simp [incidenceCredit, duplicateSupport, hinter]

/-- **Semantic inertia.**  If one supported variable is still free, every duplicate parity gate remains
nonconstant—no matter how many incidences were destroyed elsewhere. -/
theorem duplicate_parity_all_nonconstant (ρ : Restriction n) (S : Finset (Fin n))
    (hlive : (liveSupported ρ S).Nonempty) :
    ∀ j : Fin k, ¬ ParityConstant ρ (duplicateSupport S j) := by
  obtain ⟨i, hi⟩ := hlive
  have hiParts : i ∈ freeSet ρ ∩ S := by simpa [liveSupported] using hi
  obtain ⟨hiFreeSet, hiS⟩ := Finset.mem_inter.mp hiParts
  have hifree : ρ i = none := by
    simpa [freeSet] using hiFreeSet
  intro j hconst
  have hfixed := (parity_constant_iff_support_fully_fixed ρ (duplicateSupport S j)).mp hconst
  exact (hfixed i (by simpa [duplicateSupport] using hiS)) hifree

/-- **Arbitrarily positive syntactic surplus with zero gate elimination.**  With at least two duplicate gates and a
live supported variable, incidence exceeds the live-variable budget, yet all gates remain nonconstant. -/
theorem duplicate_high_overlap_semantically_inert (ρ : Restriction n) (S : Finset (Fin n))
    (hk : 2 ≤ k) (hlive : (liveSupported ρ S).Nonempty) :
    (liveSupported ρ S).card
        < incidenceCredit (Finset.univ : Finset (Fin k)) (duplicateSupport S) (liveSupported ρ S)
      ∧ ∀ j : Fin k, ¬ ParityConstant ρ (duplicateSupport S j) := by
  constructor
  · rw [duplicate_incidence_eq]
    have hpos : 0 < (liveSupported ρ S).card := card_pos.mpr hlive
    nlinarith
  · exact duplicate_parity_all_nonconstant ρ S hlive

/-- **Semantic quotient escape.**  Duplicate gates agree on every residual assignment, so the apparent `k`-fold
overlap represents only one residual function. -/
theorem duplicate_parity_semantically_equal (ρ : Restriction n) (S : Finset (Fin n))
    (x : Fin n → Bool) (i j : Fin k) :
    parityVal ρ (duplicateSupport S i) x = parityVal ρ (duplicateSupport S j) x := by
  rfl

end PallLean.Paper93.DeepMath.PathB.SemanticOverlapTransferNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.SemanticOverlapTransferNoGo.duplicate_parity_all_nonconstant
#print axioms PallLean.Paper93.DeepMath.PathB.SemanticOverlapTransferNoGo.duplicate_high_overlap_semantically_inert
#print axioms PallLean.Paper93.DeepMath.PathB.SemanticOverlapTransferNoGo.duplicate_parity_semantically_equal
