import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATSlackSeed
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCbudgetConeBound

/-!
# Floor census: at the cone floor, the circuit inventory is forced

First half of the floor-attainment structure theorem.  If a circuit of length
exactly `2d − 1` computes a function with `d` dependent coordinates, every
inequality in the cone counting is tight, and tightness forces the census:

* **`floor_census` (proved)** — the cone is the whole circuit, there are exactly
  `d` cone `var` gates, and every non-`var` cone gate is **binary** (`inSlots = 2`):
  no `un` gates, no `cst` gates, `d − 1` binary combiners.

Second half (next brick): tightness of the parent-edge injection makes it a
bijection — every non-output gate is read exactly once (fanout one) — extracting
the read-once tree; with `SAT_embeds_allEq3` and `allEq3_no_split_a/b/c`, a
floor-attaining circuit for an AllEqual₃-triple restriction is refuted, giving the
first above-floor slack `cbudget ≥ 2·deps` on SAT slices.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

/-- **The floor census (proved).**  A circuit of length exactly `2d − 1` computing a
`d`-dependent function has: cone = whole circuit, exactly `d` cone `var` gates, and
every non-`var` cone gate binary. -/
theorem floor_census {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f)
    (hlen : c.length + 1 = 2 * (depSet f).card) :
    (cone c).card = c.length ∧ (coneVars c).card = (depSet f).card ∧
    ∀ w ∈ cone c, (¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i') →
      inSlots (c.getD w (.cst false)) = 2 := by
  classical
  have hs : 0 < c.length := by omega
  have h1 := cone_card_le c hs
  have h2 := depSet_card_le_coneVars f c hcomp hs
  have h3 : (cone c).card ≤ c.length :=
    le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))
  have hsplit : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false))
      + ∑ w ∈ (cone c).filter
          (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
          inSlots (c.getD w (.cst false))
      = ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    rw [coneVars]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hvar0 : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [coneVars, Finset.mem_filter] at hw
    obtain ⟨_, i', hi'⟩ := hw
    rw [hi']
    rfl
  have hrest : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      ≤ 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ 2 (fun w _ => inSlots_le_two _)) ?_
    rw [smul_eq_mul]
    omega
  have hpart : (coneVars c).card
      + ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card
      = (cone c).card := by
    rw [coneVars]
    exact Finset.card_filter_add_card_filter_not (s := cone c)
      (p := fun w => ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')
  -- tightness
  have hconeEq : (cone c).card = c.length := by omega
  have hvarsEq : (coneVars c).card = (depSet f).card := by omega
  refine ⟨hconeEq, hvarsEq, ?_⟩
  have hsumEq : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      = 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card := by
    omega
  intro w hw hnv
  have hwmem : w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i') :=
    Finset.mem_filter.mpr ⟨hw, hnv⟩
  by_contra hne2
  have hlt : inSlots (c.getD w (.cst false)) < 2 :=
    lt_of_le_of_ne (inSlots_le_two _) hne2
  have hstrict : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      < ∑ _w ∈ (cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'), 2 :=
    Finset.sum_lt_sum (fun i _ => inSlots_le_two _) ⟨w, hwmem, hlt⟩
  rw [Finset.sum_const, smul_eq_mul] at hstrict
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.floor_census
