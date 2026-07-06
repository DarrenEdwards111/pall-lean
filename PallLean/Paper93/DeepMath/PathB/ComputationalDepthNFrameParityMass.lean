import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityLayout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityDrag

/-!
# N-Frame: the parity mass — the Markov data designation

Rung 28f of the arc (… → parity thread → **parity mass**).  The priced-mass accounting of
the counting round, Lean side: per-block `S`-mass, the grid ledger (`|S|` is carried by the
blocks up to the remainder junk), and the Markov data designation — the heaviest `k` blocks
carry a `k/2m` fraction of the cut's mass, via the frozen `markov_select`.

  `blockMass` — the per-block `S`-mass at the parity layout.
  `parity_mass_ledger` — **PROVED, the grid ledger**: `|S| ≤ Σ_c blockMass + (N − m·L)` —
        fiberwise over the block-of-position map.
  `parity_mass_select` — **PROVED, the data designation**: for every `k ≤ m` there are `k`
        blocks with `k·(|S| − junk) ≤ 2·m·(their mass)` — the Markov selection instantiated
        at the parity layout.

## Honest scope

This is the mass half of `|V| = Θ(T)`.  The remaining counting inputs are the kill/capacity
accounting (the expander-ratio hypothesis: killed coordinate-values cost `(1+c_d·d)·R·m/2`
reserve bits and unlock `R·m/2` data capacity — priced ≥ `|S|(ratio−1)/(2·ratio)`) and the
per-block matroid transversal (`rank ≥ mass/12`), then the drag assembly and rung 29.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityMass

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

/-- The per-block `S`-mass at the parity layout. -/
def blockMass (hfit : m * L ≤ N) (S : Finset (Fin N)) (c : Fin m) : ℕ :=
  (Finset.univ.filter (fun i : Fin L => xbit hfit c i ∈ S)).card

set_option maxHeartbeats 1600000 in
/-- **The grid ledger (proved)**: the cut's mass is carried by the blocks, up to the
remainder junk. -/
theorem parity_mass_ledger (hfit : m * L ≤ N) (hL : 0 < L) (hm : 0 < m)
    (S : Finset (Fin N)) :
    S.card ≤ (∑ c : Fin m, blockMass hfit S c) + (N - m * L) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := S)
    (p := fun p : Fin N => p.val < m * L)
  -- the junk bound
  have hjunk : (S.filter (fun p : Fin N => ¬ p.val < m * L)).card ≤ N - m * L := by
    have hsub : S.filter (fun p : Fin N => ¬ p.val < m * L)
        ⊆ Finset.univ.filter (fun p : Fin N => ¬ p.val < m * L) :=
      Finset.filter_subset_filter _ (Finset.subset_univ S)
    have himg : Finset.univ.filter (fun p : Fin N => p.val < m * L)
        = (Finset.univ : Finset (Fin (m * L))).image
            (fun q => (⟨q.val, lt_of_lt_of_le q.isLt hfit⟩ : Fin N)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hp
        exact ⟨⟨p.val, hp⟩, Fin.ext rfl⟩
      · rintro ⟨q, rfl⟩
        exact q.isLt
    have hcard1 : (Finset.univ.filter (fun p : Fin N => p.val < m * L)).card
        = m * L := by
      rw [himg, Finset.card_image_of_injOn, Finset.card_univ, Fintype.card_fin]
      intro q _ q' _ h
      injection h with h1
      exact Fin.ext h1
    have hcov := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N))) (p := fun p : Fin N => p.val < m * L)
    rw [Finset.card_univ, Fintype.card_fin, hcard1] at hcov
    have h2 := Finset.card_le_card hsub
    omega
  -- the grid bound, fiberwise over the block of each position
  have hgrid : (S.filter (fun p : Fin N => p.val < m * L)).card
      ≤ ∑ c : Fin m, blockMass hfit S c := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun p : Fin N => (⟨p.val / L % m, Nat.mod_lt _ hm⟩ : Fin m))
      (s := S.filter (fun p : Fin N => p.val < m * L))
      (t := (Finset.univ : Finset (Fin m)))
      (fun p _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    rw [hfib]
    apply Finset.sum_le_sum
    intro c _
    unfold blockMass
    apply Finset.card_le_card_of_injOn
      (fun p => (⟨p.val % L, Nat.mod_lt _ hL⟩ : Fin L))
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      obtain ⟨hpS, hfib⟩ := hp
      rw [Finset.mem_filter] at hpS
      obtain ⟨hpS, hgridp⟩ := hpS
      have hdivlt : p.val / L < m := (Nat.div_lt_iff_lt_mul hL).mpr hgridp
      have hcval : p.val / L = c.val := by
        have h0 : p.val / L % m = c.val := congrArg Fin.val hfib
        rw [Nat.mod_eq_of_lt hdivlt] at h0
        exact h0
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hxp : xbit hfit c ⟨p.val % L, Nat.mod_lt _ hL⟩ = p := by
        apply Fin.ext
        show c.val * L + p.val % L = p.val
        have hdm := Nat.div_add_mod p.val L
        have hcm : c.val * L = L * (p.val / L) := by
          rw [hcval]
          ring
        omega
      rw [hxp]
      exact hpS
    · intro p hp p' hp' h
      rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
      have hg : p.val < m * L := (Finset.mem_filter.mp hp.1).2
      have hg' : p'.val < m * L := (Finset.mem_filter.mp hp'.1).2
      have hdlt : p.val / L < m := (Nat.div_lt_iff_lt_mul hL).mpr hg
      have hdlt' : p'.val / L < m := (Nat.div_lt_iff_lt_mul hL).mpr hg'
      have hc : p.val / L = c.val := by
        have h0 : p.val / L % m = c.val := congrArg Fin.val hp.2
        rw [Nat.mod_eq_of_lt hdlt] at h0
        exact h0
      have hc' : p'.val / L = c.val := by
        have h0 : p'.val / L % m = c.val := congrArg Fin.val hp'.2
        rw [Nat.mod_eq_of_lt hdlt'] at h0
        exact h0
      have hm : p.val % L = p'.val % L := congrArg Fin.val h
      apply Fin.ext
      have hdm := Nat.div_add_mod p.val L
      have hdm' := Nat.div_add_mod p'.val L
      have h1 : L * (p.val / L) = L * (p'.val / L) := by
        rw [hc, hc']
      omega
  omega

/-- **The data designation (proved)**: the heaviest `k` blocks carry a `k/2m` fraction of
the cut's mass — `markov_select` at the parity layout. -/
theorem parity_mass_select (hfit : m * L ≤ N) (hL : 0 < L) (hm : 0 < m)
    (S : Finset (Fin N)) (k : ℕ) (hk : k ≤ m) :
    ∃ D : Finset (Fin m), D ⊆ Finset.univ ∧ D.card = k ∧
      k * (S.card - (N - m * L)) ≤ 2 * (m * ∑ c ∈ D, blockMass hfit S c) := by
  classical
  obtain ⟨D, hD1, hD2, hD3⟩ := markov_select (Finset.univ : Finset (Fin m))
    (blockMass hfit S) k
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hk)
  refine ⟨D, hD1, hD2, ?_⟩
  have hled := parity_mass_ledger hfit hL hm S
  have h1 : k * (S.card - (N - m * L))
      ≤ k * ∑ c : Fin m, blockMass hfit S c :=
    Nat.mul_le_mul_left k (by omega)
  rw [Finset.card_univ, Fintype.card_fin] at hD3
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameParityMass

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityMass.parity_mass_ledger
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityMass.parity_mass_select
