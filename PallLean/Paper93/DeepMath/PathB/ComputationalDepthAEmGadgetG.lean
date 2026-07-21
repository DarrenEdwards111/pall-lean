import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGTreeSplit

/-!
# Brick I' of the ∀m `SlackComposes` campaign: the general-position gadget lemma

Every gadget of `AEm m` under the all-true completion is `AllEqual₃`:

* **`AEm_gadget_g` (proved)** — the coordinate-`(3g, 3g+1, 3g+2)` restriction of
  `AEm m` at the all-true completion equals `allEq3`, for every gadget index
  `g < m`.  Generalizes `AEm_gadget_allEq3` (gadget 0) and `AEm_gadget2_allEq3`
  (gadget 1 at m = 2) with symbolic gadget arithmetic.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- **The general gadget lemma (proved)**: gadget `g` of `AEm m` under the
all-true completion is exactly `AllEqual₃`. -/
theorem AEm_gadget_g (m g : ℕ) (hg : g < m)
    (ha : 3 * g < 3 * m) (hb : 3 * g + 1 < 3 * m) (hc : 3 * g + 2 < 3 * m) :
    (fun a b c => AEm m (Function.update (Function.update (Function.update
        (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
        ⟨3 * g + 2, hc⟩ c))
      = allEq3 := by
  funext a b c
  have hval3 : ∀ (t : ℕ) (h : t < 3 * m),
      (Function.update (Function.update (Function.update
        (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
        ⟨3 * g + 2, hc⟩ c) ⟨t, h⟩
      = if t = 3 * g + 2 then c else if t = 3 * g + 1 then b
        else if t = 3 * g then a else true := by
    intro t h
    by_cases ht2 : t = 3 * g + 2
    · rw [if_pos ht2]
      have he : (⟨t, h⟩ : Fin (3 * m)) = ⟨3 * g + 2, hc⟩ := Fin.ext ht2
      rw [he, Function.update_self]
    · have hne2 : (⟨t, h⟩ : Fin (3 * m)) ≠ ⟨3 * g + 2, hc⟩ :=
        fun he => ht2 (congrArg Fin.val he)
      have e2 : (Function.update (Function.update (Function.update
          (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
          ⟨3 * g + 2, hc⟩ c) ⟨t, h⟩
          = (Function.update (Function.update
            (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b) ⟨t, h⟩ :=
        Function.update_of_ne hne2 c (Function.update (Function.update
          (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
      rw [if_neg ht2, e2]
      by_cases ht1 : t = 3 * g + 1
      · rw [if_pos ht1]
        have he : (⟨t, h⟩ : Fin (3 * m)) = ⟨3 * g + 1, hb⟩ := Fin.ext ht1
        rw [he, Function.update_self]
      · have hne1 : (⟨t, h⟩ : Fin (3 * m)) ≠ ⟨3 * g + 1, hb⟩ :=
          fun he => ht1 (congrArg Fin.val he)
        have e1 : (Function.update (Function.update
            (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b) ⟨t, h⟩
            = (Function.update (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨t, h⟩ :=
          Function.update_of_ne hne1 b
            (Function.update (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a)
        rw [if_neg ht1, e1]
        by_cases ht0 : t = 3 * g
        · rw [if_pos ht0]
          have he : (⟨t, h⟩ : Fin (3 * m)) = ⟨3 * g, ha⟩ := Fin.ext ht0
          rw [he, Function.update_self]
        · have hne0 : (⟨t, h⟩ : Fin (3 * m)) ≠ ⟨3 * g, ha⟩ :=
            fun he => ht0 (congrArg Fin.val he)
          have e0 : (Function.update
              (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨t, h⟩ = true :=
            Function.update_of_ne hne0 a (fun _ : Fin (3 * m) => true)
          rw [if_neg ht0, e0]
  show ((List.finRange m).all _) = allEq3 a b c
  cases hv : allEq3 a b c
  · refine Bool.eq_false_iff.mpr ?_
    intro hall
    rw [List.all_eq_true] at hall
    have hgd := hall ⟨g, hg⟩ (List.mem_finRange _)
    rw [hval3, hval3, hval3] at hgd
    rw [show ((⟨g, hg⟩ : Fin m) : ℕ) = g from rfl] at hgd
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_neg (by omega), if_pos (by omega), if_pos (by omega)] at hgd
    rw [hv] at hgd
    exact absurd hgd (by decide)
  · rw [List.all_eq_true]
    intro j _
    by_cases hj : (j : ℕ) = g
    · rw [hval3, hval3, hval3]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
        if_neg (by omega), if_pos (by omega), if_pos (by omega)]
      exact hv
    · rw [hval3, hval3, hval3,
        if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.AEm_gadget_g
