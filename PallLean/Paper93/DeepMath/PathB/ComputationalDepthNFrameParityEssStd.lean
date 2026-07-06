import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityStdCode

/-!
# N-Frame: the standard essentials — the `2N` baseline, concrete

Work package 2, essentiality layer (… → standard codebook → **standard essentials**).  At
the standard codebook the essentiality instantiation needs `K = ∅` and `RS = ∅` — no pins at
all, the scaffold alone carries the pair `{a₀, a₀ + e_j}` — so every singleton position is an
essential variable of the parity family UNCONDITIONALLY:

  `parity_essential_std` — **PROVED, NO HYPOTHESES beyond the layout dimensions**: every
        position `xbit c (sIdx j b)` is an essential variable of
        `parityFamilyBits (stdCode v) hfit`.
  `stdESS` / `stdESS_card` / `stdESS_essential` — **PROVED**: the explicit essential set of
        all `m·2v` singleton positions, with its exact cardinality and the witness data in
        `connectivity_fanout`'s shape — the `2N` baseline of the headline, concrete.

## Honest scope

With this, the headline's `ESS`-half is discharged: `2·(2·m·v) + |V| ≤ length + 2` for any
circuit computing the standard-codebook parity family, given the cut/drag package.  The
remaining named conditions: the liveness/kill-accounting for `|V| = Θ(T)` (the expander
long-pole) and the parity root-shape fact (for `hj` via the generic wire cut).  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityEssStd

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityHeadline
open PallLean.Paper93.DeepMath.PathB.NFrameParityStdCode

variable {v m N : ℕ}

set_option maxHeartbeats 1600000 in
/-- **The unconditional essentiality (proved)**: every singleton position of the standard
codebook is an essential variable of the parity family. -/
theorem parity_essential_std (hv : 0 < v) (hfit : m * stdL v ≤ N)
    (cstar : Fin m) (j : Fin v) (b : ZMod 2) :
    ∃ x₁ x₀ : Fin N → Bool,
      (∀ p : Fin N, x₁ p ≠ x₀ p → p = xbit hfit cstar (sIdx v j b))
      ∧ parityFamilyBits (stdCode v hv) hfit x₁
        ≠ parityFamilyBits (stdCode v hv) hfit x₀ := by
  classical
  have h := parity_essential (stdCode v hv) hfit (tautIdxStd v)
    (∅ : Finset (Fin m)) (cstar, sIdx v j b)
    (fun _ => tautIdxStd v)
    ((Finset.univ \ {j}).image (fun j' => sIdx v j' 1))
    j b (∅ : Finset (Fin v)) (fun _ => 0)
    (sIdx_ne_taut v j b)
    (Finset.notMem_empty cstar)
    (stdCode_taut v hv)
    (stdCode_sIdx v hv j b)
    (Finset.notMem_empty j)
    (fun c hc => absurd hc (Finset.notMem_empty c))
    (fun j' hj' => absurd hj' (Finset.notMem_empty j'))
    (by
      intro hmem
      obtain ⟨j', hj', heq⟩ := Finset.mem_image.mp hmem
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hj'
      exact hj'.2 (sIdx_inj v heq.symm).1.symm)
    (by
      intro i hi
      obtain ⟨j', hj', heq⟩ := Finset.mem_image.mp hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hj'
      intro hcon
      apply hj'.2
      rw [← heq] at hcon
      exact ((sIdx_inj v hcon).1))
    (by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro j' _
      exact stdCode_sIdx v hv j' 1)
  exact h

/-- The explicit essential set: all singleton positions. -/
def stdESS (hv : 0 < v) (hfit : m * stdL v ≤ N) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin m × Fin v × ZMod 2)).image
    (fun t => xbit hfit t.1 (sIdx v t.2.1 t.2.2))

/-- **The exact baseline count (proved)**: `|stdESS| = m · v · 2`. -/
theorem stdESS_card (hv : 0 < v) (hfit : m * stdL v ≤ N) :
    (stdESS (m := m) (N := N) hv hfit).card = m * (v * 2) := by
  classical
  unfold stdESS
  rw [Finset.card_image_of_injOn, Finset.card_univ]
  · rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      ZMod.card]
  · intro t _ t' _ h
    obtain ⟨h1, h2⟩ := xbit_inj hfit h
    obtain ⟨h3, h4⟩ := sIdx_inj v h2
    exact Prod.ext h1 (Prod.ext h3 h4)

/-- **The essential-witness data (proved)**: `stdESS` in `connectivity_fanout`'s shape. -/
theorem stdESS_essential (hv : 0 < v) (hfit : m * stdL v ≤ N) :
    ∀ p ∈ stdESS (m := m) (N := N) hv hfit,
      ∃ x₁ x₀ : Fin N → Bool,
        (∀ b' : Fin N, x₁ b' ≠ x₀ b' → b' = p)
        ∧ parityFamilyBits (stdCode v hv) hfit x₁
          ≠ parityFamilyBits (stdCode v hv) hfit x₀ := by
  intro p hp
  unfold stdESS at hp
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hp
  exact parity_essential_std hv hfit t.1 t.2.1 t.2.2

end PallLean.Paper93.DeepMath.PathB.NFrameParityEssStd

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityEssStd.parity_essential_std
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityEssStd.stdESS_card
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityEssStd.stdESS_essential
