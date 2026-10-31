import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATThreeGadget

/-!
# The two-spare-unit structure: the `(X, W)` split at budget `≤ 2·deps + 1`

Brick 2 of the multi-wire campaign — the general accounting that shapes every
`+3` case.  Two units above the floor leave exactly three shapes:

* **`spare_bound2` (proved, general)** — excess `≤ 2`, `deps ≤ |coneVars| ≤
  deps + 1`, at most TWO reconvergence wires — and the var-gate budget and the
  excess trade off exactly: an extra var gate (`|coneVars| = deps + 1`) forces
  excess `0` (no reconvergence at all);
* **`dup_at_most_one` (proved, general)** — at `|coneVars| ≤ deps + 1`, no two
  distinct dependent variables can BOTH have duplicated cone gates: the
  choice-image plus one extra gate per duplicated variable would need
  `deps + 2` var gates.

So at budget `≤ 2d + 1` an optimal circuit is one of: (i) reconvergence-free
with ONE duplicated variable, (ii) one reconvergence wire (fanout 2 or 3) with
unique gates, or (iii) two reconvergence wires with unique gates — the case
list the `k = 2` kills must cover.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor

/-- **The two-spare-unit split (proved, general)**: the var-gate surplus and the
read excess trade off within two units. -/
theorem spare_bound2 {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet f).card + 1) :
    excessX c ≤ 2 ∧ (depSet f).card ≤ (coneVars c).card
      ∧ (coneVars c).card ≤ (depSet f).card + 1
      ∧ (reconvR c).card ≤ 2
      ∧ ((depSet f).card + 1 ≤ (coneVars c).card → excessX c = 0) := by
  have hdW := depSet_card_le_coneVars f c hcomp hs
  have hslot := cone_ge_slot c hs
  have hcone := cone_card_le_length c
  have hrX := reconvR_card_le c
  exact ⟨by omega, hdW, by omega, by omega, fun h => by omega⟩

/-- **At most one duplicated variable (proved, general)**: with var-gate budget
`deps + 1`, two distinct dependencies cannot both own two cone gates. -/
theorem dup_at_most_one {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hs : 0 < c.length)
    (hWd : (coneVars c).card ≤ (depSet f).card + 1)
    {i j : Fin n} (hdi : i ∈ depSet f) (hdj : j ∈ depSet f) (hij : i ≠ j)
    {qi₁ qi₂ qj₁ qj₂ : ℕ}
    (hqi₁c : qi₁ ∈ cone c) (hqi₁g : c.getD qi₁ (.cst false) = CGate.var i)
    (hqi₂c : qi₂ ∈ cone c) (hqi₂g : c.getD qi₂ (.cst false) = CGate.var i)
    (hqi : qi₁ ≠ qi₂)
    (hqj₁c : qj₁ ∈ cone c) (hqj₁g : c.getD qj₁ (.cst false) = CGate.var j)
    (hqj₂c : qj₂ ∈ cone c) (hqj₂g : c.getD qj₂ (.cst false) = CGate.var j)
    (hqj : qj₁ ≠ qj₂) : False := by
  classical
  have hex := dep_var_gate f c hcomp hs
  let φ : Fin n → ℕ := fun a =>
    if h : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var a
    then Classical.choose h else 0
  have hφspec : ∀ a ∈ depSet f,
      φ a ∈ cone c ∧ c.getD (φ a) (.cst false) = CGate.var a := by
    intro a ha
    obtain ⟨w, hw⟩ := hex a ha
    have hex' : ∃ w, w ∈ cone c ∧ c.getD w (.cst false) = CGate.var a := ⟨w, hw⟩
    have hdef : φ a = Classical.choose hex' := dif_pos hex'
    rw [hdef]
    exact Classical.choose_spec hex'
  have hinj : Set.InjOn φ (depSet f) := by
    intro a ha b hb hab
    have hsa := (hφspec a (Finset.mem_coe.mp ha)).2
    have hsb := (hφspec b (Finset.mem_coe.mp hb)).2
    rw [hab] at hsa
    exact CGate.var.inj (hsa.symm.trans hsb)
  have himg : (depSet f).image φ ⊆ coneVars c := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hc1, hc2⟩ := hφspec a ha
    rw [coneVars, Finset.mem_filter]
    exact ⟨hc1, ⟨a, hc2⟩⟩
  -- pick the extra gate of `i` (the one that is not the chosen gate)
  obtain ⟨ei, heic, heig, heiφ⟩ :
      ∃ e, e ∈ cone c ∧ c.getD e (.cst false) = CGate.var i ∧ e ≠ φ i := by
    by_cases h1 : qi₁ = φ i
    · exact ⟨qi₂, hqi₂c, hqi₂g, fun he => hqi (h1.trans he.symm)⟩
    · exact ⟨qi₁, hqi₁c, hqi₁g, h1⟩
  obtain ⟨ej, hejc, hejg, hejφ⟩ :
      ∃ e, e ∈ cone c ∧ c.getD e (.cst false) = CGate.var j ∧ e ≠ φ j := by
    by_cases h1 : qj₁ = φ j
    · exact ⟨qj₂, hqj₂c, hqj₂g, fun he => hqj (h1.trans he.symm)⟩
    · exact ⟨qj₁, hqj₁c, hqj₁g, h1⟩
  have hei_notin : ei ∉ (depSet f).image φ := by
    intro hmem
    obtain ⟨a, ha, hφa⟩ := Finset.mem_image.mp hmem
    have hga := (hφspec a ha).2
    rw [hφa] at hga
    have hai : a = i := CGate.var.inj (hga.symm.trans heig)
    rw [hai] at hφa
    exact heiφ hφa.symm
  have hej_notin : ej ∉ (depSet f).image φ := by
    intro hmem
    obtain ⟨a, ha, hφa⟩ := Finset.mem_image.mp hmem
    have hga := (hφspec a ha).2
    rw [hφa] at hga
    have haj : a = j := CGate.var.inj (hga.symm.trans hejg)
    rw [haj] at hφa
    exact hejφ hφa.symm
  have heij : ei ≠ ej := by
    intro he
    rw [he] at heig
    exact hij (CGate.var.inj (heig.symm.trans hejg))
  have hsub : insert ei (insert ej ((depSet f).image φ)) ⊆ coneVars c := by
    intro q hq
    rcases Finset.mem_insert.mp hq with h | h
    · rw [h, coneVars, Finset.mem_filter]
      exact ⟨heic, ⟨i, heig⟩⟩
    rcases Finset.mem_insert.mp h with h' | h'
    · rw [h', coneVars, Finset.mem_filter]
      exact ⟨hejc, ⟨j, hejg⟩⟩
    · exact himg h'
  have hcard1 : ((depSet f).image φ).card = (depSet f).card :=
    Finset.card_image_of_injOn hinj
  have hei_notin2 : ei ∉ insert ej ((depSet f).image φ) := by
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact heij h'
    · exact hei_notin h'
  have hcard3 : (insert ei (insert ej ((depSet f).image φ))).card
      = (depSet f).card + 2 := by
    rw [Finset.card_insert_of_notMem hei_notin2,
      Finset.card_insert_of_notMem hej_notin, hcard1]
  have hle := Finset.card_le_card hsub
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.spare_bound2
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.dup_at_most_one
