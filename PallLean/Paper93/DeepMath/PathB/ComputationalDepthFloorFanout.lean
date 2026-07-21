import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFloorCensus

/-!
# Floor fanout: at the cone floor, every wire is read at most once

Second half of the floor-attainment structure theorem.  At length `2d − 1` the
parent-edge counting is tight, so a wire with two distinct readers would add an
edge beyond the injection's image — `|E| ≥ |cone|` against `|E| ≤ Σ inSlots =
|cone| − 1`:

* **`floor_fanout_le_one` (proved)** — in a floor-attaining circuit, any non-output
  cone wire has at most one cone reader.

With the census (`d` var gates, `d − 1` binary gates, nothing else) this pins the
read-once tree; the remaining extraction (tree shape → top-level split → refutation
by `allEq3_no_split`) is the final assembly toward `cbudget ≥ 2·deps` on the SAT
slices.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

/-- **Floor fanout (proved).**  In a floor-attaining circuit, a non-output cone wire
has at most one cone reader. -/
theorem floor_fanout_le_one {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hlen : c.length + 1 = 2 * (depSet f).card)
    (j : ℕ) (hj : j ∈ cone c) (hjr : j ≠ c.length - 1)
    (w₁ w₂ : ℕ) (h₁ : w₁ ∈ cone c) (h₂ : w₂ ∈ cone c)
    (hr₁ : j ∈ gateReads (c.getD w₁ (.cst false)))
    (hr₂ : j ∈ gateReads (c.getD w₂ (.cst false))) : w₁ = w₂ := by
  classical
  by_contra hne
  have hs : 0 < c.length := by omega
  obtain ⟨hconeEq, hvarsEq, -⟩ := floor_census f c hcomp hlen
  -- the sum is exactly length − 1
  have h1 := cone_card_le c hs
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
  -- injection scaffold
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hex : ∀ x ∈ (cone c).erase (c.length - 1),
      ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w := by
    intro x hx
    obtain ⟨hxne, hxc⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxlt, hxcone⟩ := mem_cone.mp hxc
    cases hxcone with
    | root => exact absurd rfl hxne
    | step hw hjm hjw => exact ⟨_, hw, hjm, hjw⟩
  have hjmem : j ∈ (cone c).erase (c.length - 1) := Finset.mem_erase.mpr ⟨hjr, hj⟩
  have hjd : ∃ w, InCone c w ∧ j ∈ gateReads (c.getD w (.cst false)) ∧ j < w :=
    hex j hjmem
  -- the injection's image and the extra edge
  have himg_sub : ((cone c).erase (c.length - 1)).image
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))
      ⊆ (cone c).biUnion
        (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t))) := by
    intro pr hpr
    obtain ⟨x, hx, hφ⟩ := Finset.mem_image.mp hpr
    obtain ⟨w, hw⟩ := hex x hx
    rw [← hφ, dif_pos ⟨w, hw⟩]
    have hspec := Classical.choose_spec
      (⟨w, hw⟩ : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w)
    rw [Finset.mem_biUnion]
    exact ⟨_, mem_cone.mpr ⟨inCone_lt hs hspec.1, hspec.1⟩,
      Finset.mem_image.mpr ⟨x, hspec.2.1, rfl⟩⟩
  have hinj : Set.InjOn
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))
      ((cone c).erase (c.length - 1)) := by
    intro a _ b _ hab
    exact congrArg Prod.snd hab
  have himg_card : (((cone c).erase (c.length - 1)).image
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))).card
      = (cone c).card - 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hroot]
  -- the bad reader distinct from the chosen consumer
  have hbad : ∃ wb, wb ∈ cone c ∧ j ∈ gateReads (c.getD wb (.cst false)) ∧
      wb ≠ Classical.choose hjd := by
    by_cases h1c : w₁ = Classical.choose hjd
    · exact ⟨w₂, h₂, hr₂, fun h => hne (h1c.trans h.symm)⟩
    · exact ⟨w₁, h₁, hr₁, h1c⟩
  obtain ⟨wb, hwbc, hwbr, hwbne⟩ := hbad
  have hextra_mem : (wb, j) ∈ (cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t))) := by
    rw [Finset.mem_biUnion]
    exact ⟨wb, hwbc, Finset.mem_image.mpr ⟨j, hwbr, rfl⟩⟩
  have hextra_not : (wb, j) ∉ ((cone c).erase (c.length - 1)).image
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x)) := by
    intro hmem
    obtain ⟨x, hx, hφ⟩ := Finset.mem_image.mp hmem
    have hxj : x = j := congrArg Prod.snd hφ
    subst hxj
    have hφ1 : (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0) = wb := congrArg Prod.fst hφ
    rw [dif_pos hjd] at hφ1
    exact hwbne hφ1.symm
  have hcard2 : (cone c).card - 1 + 1 ≤ ((cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t)))).card := by
    rw [← himg_card, ← Finset.card_insert_of_notMem hextra_not]
    exact Finset.card_le_card (Finset.insert_subset hextra_mem himg_sub)
  have hEle : ((cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t)))).card
      ≤ ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_)
    intro w _
    exact le_trans Finset.card_image_le (gateReads_card_le _)
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.floor_fanout_le_one
