import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA4a

/-!
# Shrinkage brick A4b: THE INTEGER ONE-STEP LEMMA

Subbotovskaya's shrinkage step, probability-free, by structural induction with
the invariant `deaths ≥ 3L − [literal]`:

* **`onestep_core` (proved)** — for normalized constant-free `t` supported
  on `S`:
  `Σ_{i∈S} (L₀(t↾ᵢ₌₀) + L₀(t↾ᵢ₌₁)) + 3·L₀(t) ≤ 2|S|·L₀(t) + [t literal]`.

The node case sums the pointwise `mkAnd`/`mkOr` bound and extracts slack at
each literal child's own variable via the A4a point budgets — a literal child
donates its sibling's full size there, and normalization makes the two
special points distinct when both children are literals.  The `[literal]`
indicator is exactly the `+1` the design pinned as mandatory.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- **THE INTEGER ONE-STEP (proved, Subbotovskaya Γ = 3/2 core).** -/
theorem onestep_core {n : ℕ} (S : Finset (Fin n)) :
    ∀ t : DMTreeC n, CstFree t → NormalAt t →
      (∀ i, cntC i t ≠ 0 → i ∈ S) →
      (∑ i ∈ S, ((simpC (subst1 i false t)).lsize0
        + (simpC (subst1 i true t)).lsize0))
        + 3 * t.lsize0
      ≤ 2 * S.card * t.lsize0 + litInd t := by
  classical
  intro t
  induction t with
  | cst v =>
    intro hcf _ _
    exact hcf.elim
  | lit j v =>
    intro _ _ hsupp
    have hjS : j ∈ S := hsupp j (by rw [cntC_lit_self]; omega)
    have hval : ∀ i ∈ S, ((simpC (subst1 i false (.lit j v : DMTreeC n))).lsize0
        + (simpC (subst1 i true (.lit j v : DMTreeC n))).lsize0)
        = if i = j then 0 else 2 := by
      intro i _
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, subst1_lit_self i v false, subst1_lit_self i v true]
        rfl
      · rw [if_neg hij]
        have hji : ¬ (j = i) := fun h => hij h.symm
        have hs : subst1 i false (.lit j v : DMTreeC n) = .lit j v := by
          show (if j = i then (DMTreeC.cst ((false : Bool) == v) : DMTreeC n)
            else .lit j v) = .lit j v
          rw [if_neg hji]
        have hs' : subst1 i true (.lit j v : DMTreeC n) = .lit j v := by
          show (if j = i then (DMTreeC.cst ((true : Bool) == v) : DMTreeC n)
            else .lit j v) = .lit j v
          rw [if_neg hji]
        rw [hs, hs']
        rfl
    rw [Finset.sum_congr rfl hval,
      ← Finset.add_sum_erase S _ hjS, if_pos rfl]
    have herase : ∀ i ∈ S.erase j,
        (if i = j then (0 : ℕ) else 2) = 2 := by
      intro i hi
      rw [if_neg (Finset.mem_erase.mp hi).1]
    rw [Finset.sum_congr rfl herase, Finset.sum_const, smul_eq_mul,
      Finset.card_erase_of_mem hjS]
    have hL : (DMTreeC.lit j v : DMTreeC n).lsize0 = 1 := rfl
    have hlam : litInd (DMTreeC.lit j v : DMTreeC n) = 1 := rfl
    rw [hL, hlam]
    have hcard : 0 < S.card := Finset.card_pos.mpr ⟨j, hjS⟩
    omega
  | and l r ihl ihr =>
    intro hcf hnorm hsupp
    have hsl : ∀ i, cntC i l ≠ 0 → i ∈ S := fun i hi =>
      hsupp i (by show cntC i l + cntC i r ≠ 0; omega)
    have hsr : ∀ i, cntC i r ≠ 0 → i ∈ S := fun i hi =>
      hsupp i (by show cntC i l + cntC i r ≠ 0; omega)
    have IHl := ihl hcf.1 hnorm.1 hsl
    have IHr := ihr hcf.2 hnorm.2.1 hsr
    have hpt : ∀ i ∈ S, ((simpC (subst1 i false (.and l r))).lsize0
        + (simpC (subst1 i true (.and l r))).lsize0)
        ≤ (((simpC (subst1 i false l)).lsize0
          + (simpC (subst1 i true l)).lsize0)
          + ((simpC (subst1 i false r)).lsize0
          + (simpC (subst1 i true r)).lsize0)) := by
      intro i _
      have h1 : simpC (subst1 i false (.and l r))
          = mkAnd (simpC (subst1 i false l)) (simpC (subst1 i false r)) := rfl
      have h2 : simpC (subst1 i true (.and l r))
          = mkAnd (simpC (subst1 i true l)) (simpC (subst1 i true r)) := rfl
      rw [h1, h2]
      have m1 := mkAnd_lsize0 (simpC (subst1 i false l))
        (simpC (subst1 i false r))
      have m2 := mkAnd_lsize0 (simpC (subst1 i true l))
        (simpC (subst1 i true r))
      omega
    have hnode : (∑ i ∈ S, ((simpC (subst1 i false (.and l r))).lsize0
        + (simpC (subst1 i true (.and l r))).lsize0))
        + litInd l + litInd r
        ≤ ∑ i ∈ S, (((simpC (subst1 i false l)).lsize0
          + (simpC (subst1 i true l)).lsize0)
          + ((simpC (subst1 i false r)).lsize0
          + (simpC (subst1 i true r)).lsize0)) := by
      cases l with
      | cst w => exact hcf.1.elim
      | lit j v =>
        have hjS : j ∈ S := hsl j (by rw [cntC_lit_self]; omega)
        have hcnt : cntC j r = 0 := hnorm.2.2.1 j v rfl
        have hpoint := and_lit_point j v r hcf.2 hcnt
        have hLr := cstFree_lsize0_pos r hcf.2
        cases r with
        | cst w => exact hcf.2.elim
        | lit j' v' =>
          have hne : j ≠ j' := by
            intro he
            have h0 : (if j' = j then (1 : ℕ) else 0) = 0 := hcnt
            rw [if_pos he.symm] at h0
            exact Nat.one_ne_zero h0
          have hj'S : j' ∈ S := hsr j' (by rw [cntC_lit_self]; omega)
          have hcnt' : cntC j' (.lit j v : DMTreeC n) = 0 :=
            hnorm.2.2.2 j' v' rfl
          have hpoint' := and_lit_point' j' v' (.lit j v : DMTreeC n)
            hcf.1 hcnt'
          have hLl := cstFree_lsize0_pos (.lit j v : DMTreeC n) hcf.1
          have hlaml : litInd (DMTreeC.lit j v : DMTreeC n) = 1 := rfl
          have hlamr : litInd (DMTreeC.lit j' v' : DMTreeC n) = 1 := rfl
          rw [hlaml, hlamr]
          have hslack₀ : ((simpC (subst1 j false
              (.and (.lit j v) (.lit j' v')))).lsize0
              + (simpC (subst1 j true
              (.and (.lit j v) (.lit j' v')))).lsize0) + 1
              ≤ (((simpC (subst1 j false (.lit j v : DMTreeC n))).lsize0
                + (simpC (subst1 j true (.lit j v : DMTreeC n))).lsize0)
                + ((simpC (subst1 j false (.lit j' v' : DMTreeC n))).lsize0
                + (simpC (subst1 j true (.lit j' v' : DMTreeC n))).lsize0)) := by
            have h1 := hpoint
            have h2 : 0 < (DMTreeC.lit j' v' : DMTreeC n).lsize0 := hLr
            omega
          have hslack₁ : ((simpC (subst1 j' false
              (.and (.lit j v) (.lit j' v')))).lsize0
              + (simpC (subst1 j' true
              (.and (.lit j v) (.lit j' v')))).lsize0) + 1
              ≤ (((simpC (subst1 j' false (.lit j v : DMTreeC n))).lsize0
                + (simpC (subst1 j' true (.lit j v : DMTreeC n))).lsize0)
                + ((simpC (subst1 j' false (.lit j' v' : DMTreeC n))).lsize0
                + (simpC (subst1 j' true (.lit j' v' : DMTreeC n))).lsize0)) := by
            have h1 := hpoint'
            have h2 := hLl
            omega
          have hss := sum_slack_two S _ _ 1 1 hpt j j' hne hjS hj'S hslack₀ hslack₁
          omega
        | and r1 r2 =>
          have hlaml : litInd (DMTreeC.lit j v : DMTreeC n) = 1 := rfl
          have hlamr : litInd (DMTreeC.and r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hslack : ((simpC (subst1 j false
              (.and (.lit j v) (.and r1 r2)))).lsize0
              + (simpC (subst1 j true
              (.and (.lit j v) (.and r1 r2)))).lsize0) + 1
              ≤ (((simpC (subst1 j false (.lit j v : DMTreeC n))).lsize0
                + (simpC (subst1 j true (.lit j v : DMTreeC n))).lsize0)
                + ((simpC (subst1 j false (.and r1 r2))).lsize0
                + (simpC (subst1 j true (.and r1 r2))).lsize0)) := by
            have h1 := hpoint
            have h2 := hLr
            omega
          have hss := sum_slack_one S _ _ 1 hpt j hjS hslack
          omega
        | or r1 r2 =>
          have hlaml : litInd (DMTreeC.lit j v : DMTreeC n) = 1 := rfl
          have hlamr : litInd (DMTreeC.or r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hslack : ((simpC (subst1 j false
              (.and (.lit j v) (.or r1 r2)))).lsize0
              + (simpC (subst1 j true
              (.and (.lit j v) (.or r1 r2)))).lsize0) + 1
              ≤ (((simpC (subst1 j false (.lit j v : DMTreeC n))).lsize0
                + (simpC (subst1 j true (.lit j v : DMTreeC n))).lsize0)
                + ((simpC (subst1 j false (.or r1 r2))).lsize0
                + (simpC (subst1 j true (.or r1 r2))).lsize0)) := by
            have h1 := hpoint
            have h2 := hLr
            omega
          have hss := sum_slack_one S _ _ 1 hpt j hjS hslack
          omega
      | and l1 l2 =>
        cases r with
        | cst w => exact hcf.2.elim
        | lit j' v' =>
          have hj'S : j' ∈ S := hsr j' (by rw [cntC_lit_self]; omega)
          have hcnt' : cntC j' (.and l1 l2) = 0 := hnorm.2.2.2 j' v' rfl
          have hpoint' := and_lit_point' j' v' (.and l1 l2) hcf.1 hcnt'
          have hLl := cstFree_lsize0_pos (.and l1 l2) hcf.1
          have hlaml : litInd (DMTreeC.and l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.lit j' v' : DMTreeC n) = 1 := rfl
          rw [hlaml, hlamr]
          have hslack : ((simpC (subst1 j' false
              (.and (.and l1 l2) (.lit j' v')))).lsize0
              + (simpC (subst1 j' true
              (.and (.and l1 l2) (.lit j' v')))).lsize0) + 1
              ≤ (((simpC (subst1 j' false (.and l1 l2))).lsize0
                + (simpC (subst1 j' true (.and l1 l2))).lsize0)
                + ((simpC (subst1 j' false (.lit j' v' : DMTreeC n))).lsize0
                + (simpC (subst1 j' true (.lit j' v' : DMTreeC n))).lsize0)) := by
            have h1 := hpoint'
            have h2 := hLl
            omega
          have hss := sum_slack_one S _ _ 1 hpt j' hj'S hslack
          omega
        | and r1 r2 =>
          have hlaml : litInd (DMTreeC.and l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.and r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hss := Finset.sum_le_sum hpt
          omega
        | or r1 r2 =>
          have hlaml : litInd (DMTreeC.and l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.or r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hss := Finset.sum_le_sum hpt
          omega
      | or l1 l2 =>
        cases r with
        | cst w => exact hcf.2.elim
        | lit j' v' =>
          have hj'S : j' ∈ S := hsr j' (by rw [cntC_lit_self]; omega)
          have hcnt' : cntC j' (.or l1 l2) = 0 := hnorm.2.2.2 j' v' rfl
          have hpoint' := and_lit_point' j' v' (.or l1 l2) hcf.1 hcnt'
          have hLl := cstFree_lsize0_pos (.or l1 l2) hcf.1
          have hlaml : litInd (DMTreeC.or l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.lit j' v' : DMTreeC n) = 1 := rfl
          rw [hlaml, hlamr]
          have hslack : ((simpC (subst1 j' false
              (.and (.or l1 l2) (.lit j' v')))).lsize0
              + (simpC (subst1 j' true
              (.and (.or l1 l2) (.lit j' v')))).lsize0) + 1
              ≤ (((simpC (subst1 j' false (.or l1 l2))).lsize0
                + (simpC (subst1 j' true (.or l1 l2))).lsize0)
                + ((simpC (subst1 j' false (.lit j' v' : DMTreeC n))).lsize0
                + (simpC (subst1 j' true (.lit j' v' : DMTreeC n))).lsize0)) := by
            have h1 := hpoint'
            have h2 := hLl
            omega
          have hss := sum_slack_one S _ _ 1 hpt j' hj'S hslack
          omega
        | and r1 r2 =>
          have hlaml : litInd (DMTreeC.or l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.and r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hss := Finset.sum_le_sum hpt
          omega
        | or r1 r2 =>
          have hlaml : litInd (DMTreeC.or l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.or r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hss := Finset.sum_le_sum hpt
          omega
    have hLrfl : (DMTreeC.and l r : DMTreeC n).lsize0
        = l.lsize0 + r.lsize0 := rfl
    have hlamrfl : litInd (DMTreeC.and l r : DMTreeC n) = 0 := rfl
    have hdistrib : 2 * S.card * (l.lsize0 + r.lsize0)
        = 2 * S.card * l.lsize0 + 2 * S.card * r.lsize0 := by ring
    have hsplitAB : (∑ i ∈ S, (((simpC (subst1 i false l)).lsize0
        + (simpC (subst1 i true l)).lsize0)
        + ((simpC (subst1 i false r)).lsize0
        + (simpC (subst1 i true r)).lsize0)))
        = (∑ i ∈ S, ((simpC (subst1 i false l)).lsize0
          + (simpC (subst1 i true l)).lsize0))
          + (∑ i ∈ S, ((simpC (subst1 i false r)).lsize0
          + (simpC (subst1 i true r)).lsize0)) := Finset.sum_add_distrib
    rw [hLrfl, hlamrfl]
    omega
  | or l r ihl ihr =>
    intro hcf hnorm hsupp
    have hsl : ∀ i, cntC i l ≠ 0 → i ∈ S := fun i hi =>
      hsupp i (by show cntC i l + cntC i r ≠ 0; omega)
    have hsr : ∀ i, cntC i r ≠ 0 → i ∈ S := fun i hi =>
      hsupp i (by show cntC i l + cntC i r ≠ 0; omega)
    have IHl := ihl hcf.1 hnorm.1 hsl
    have IHr := ihr hcf.2 hnorm.2.1 hsr
    have hpt : ∀ i ∈ S, ((simpC (subst1 i false (.or l r))).lsize0
        + (simpC (subst1 i true (.or l r))).lsize0)
        ≤ (((simpC (subst1 i false l)).lsize0
          + (simpC (subst1 i true l)).lsize0)
          + ((simpC (subst1 i false r)).lsize0
          + (simpC (subst1 i true r)).lsize0)) := by
      intro i _
      have h1 : simpC (subst1 i false (.or l r))
          = mkOr (simpC (subst1 i false l)) (simpC (subst1 i false r)) := rfl
      have h2 : simpC (subst1 i true (.or l r))
          = mkOr (simpC (subst1 i true l)) (simpC (subst1 i true r)) := rfl
      rw [h1, h2]
      have m1 := mkOr_lsize0 (simpC (subst1 i false l))
        (simpC (subst1 i false r))
      have m2 := mkOr_lsize0 (simpC (subst1 i true l))
        (simpC (subst1 i true r))
      omega
    have hnode : (∑ i ∈ S, ((simpC (subst1 i false (.or l r))).lsize0
        + (simpC (subst1 i true (.or l r))).lsize0))
        + litInd l + litInd r
        ≤ ∑ i ∈ S, (((simpC (subst1 i false l)).lsize0
          + (simpC (subst1 i true l)).lsize0)
          + ((simpC (subst1 i false r)).lsize0
          + (simpC (subst1 i true r)).lsize0)) := by
      cases l with
      | cst w => exact hcf.1.elim
      | lit j v =>
        have hjS : j ∈ S := hsl j (by rw [cntC_lit_self]; omega)
        have hcnt : cntC j r = 0 := hnorm.2.2.1 j v rfl
        have hpoint := or_lit_point j v r hcf.2 hcnt
        have hLr := cstFree_lsize0_pos r hcf.2
        cases r with
        | cst w => exact hcf.2.elim
        | lit j' v' =>
          have hne : j ≠ j' := by
            intro he
            have h0 : (if j' = j then (1 : ℕ) else 0) = 0 := hcnt
            rw [if_pos he.symm] at h0
            exact Nat.one_ne_zero h0
          have hj'S : j' ∈ S := hsr j' (by rw [cntC_lit_self]; omega)
          have hcnt' : cntC j' (.lit j v : DMTreeC n) = 0 :=
            hnorm.2.2.2 j' v' rfl
          have hpoint' := or_lit_point' j' v' (.lit j v : DMTreeC n)
            hcf.1 hcnt'
          have hLl := cstFree_lsize0_pos (.lit j v : DMTreeC n) hcf.1
          have hlaml : litInd (DMTreeC.lit j v : DMTreeC n) = 1 := rfl
          have hlamr : litInd (DMTreeC.lit j' v' : DMTreeC n) = 1 := rfl
          rw [hlaml, hlamr]
          have hslack₀ : ((simpC (subst1 j false
              (.or (.lit j v) (.lit j' v')))).lsize0
              + (simpC (subst1 j true
              (.or (.lit j v) (.lit j' v')))).lsize0) + 1
              ≤ (((simpC (subst1 j false (.lit j v : DMTreeC n))).lsize0
                + (simpC (subst1 j true (.lit j v : DMTreeC n))).lsize0)
                + ((simpC (subst1 j false (.lit j' v' : DMTreeC n))).lsize0
                + (simpC (subst1 j true (.lit j' v' : DMTreeC n))).lsize0)) := by
            have h1 := hpoint
            have h2 : 0 < (DMTreeC.lit j' v' : DMTreeC n).lsize0 := hLr
            omega
          have hslack₁ : ((simpC (subst1 j' false
              (.or (.lit j v) (.lit j' v')))).lsize0
              + (simpC (subst1 j' true
              (.or (.lit j v) (.lit j' v')))).lsize0) + 1
              ≤ (((simpC (subst1 j' false (.lit j v : DMTreeC n))).lsize0
                + (simpC (subst1 j' true (.lit j v : DMTreeC n))).lsize0)
                + ((simpC (subst1 j' false (.lit j' v' : DMTreeC n))).lsize0
                + (simpC (subst1 j' true (.lit j' v' : DMTreeC n))).lsize0)) := by
            have h1 := hpoint'
            have h2 := hLl
            omega
          have hss := sum_slack_two S _ _ 1 1 hpt j j' hne hjS hj'S hslack₀ hslack₁
          omega
        | and r1 r2 =>
          have hlaml : litInd (DMTreeC.lit j v : DMTreeC n) = 1 := rfl
          have hlamr : litInd (DMTreeC.and r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hslack : ((simpC (subst1 j false
              (.or (.lit j v) (.and r1 r2)))).lsize0
              + (simpC (subst1 j true
              (.or (.lit j v) (.and r1 r2)))).lsize0) + 1
              ≤ (((simpC (subst1 j false (.lit j v : DMTreeC n))).lsize0
                + (simpC (subst1 j true (.lit j v : DMTreeC n))).lsize0)
                + ((simpC (subst1 j false (.and r1 r2))).lsize0
                + (simpC (subst1 j true (.and r1 r2))).lsize0)) := by
            have h1 := hpoint
            have h2 := hLr
            omega
          have hss := sum_slack_one S _ _ 1 hpt j hjS hslack
          omega
        | or r1 r2 =>
          have hlaml : litInd (DMTreeC.lit j v : DMTreeC n) = 1 := rfl
          have hlamr : litInd (DMTreeC.or r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hslack : ((simpC (subst1 j false
              (.or (.lit j v) (.or r1 r2)))).lsize0
              + (simpC (subst1 j true
              (.or (.lit j v) (.or r1 r2)))).lsize0) + 1
              ≤ (((simpC (subst1 j false (.lit j v : DMTreeC n))).lsize0
                + (simpC (subst1 j true (.lit j v : DMTreeC n))).lsize0)
                + ((simpC (subst1 j false (.or r1 r2))).lsize0
                + (simpC (subst1 j true (.or r1 r2))).lsize0)) := by
            have h1 := hpoint
            have h2 := hLr
            omega
          have hss := sum_slack_one S _ _ 1 hpt j hjS hslack
          omega
      | and l1 l2 =>
        cases r with
        | cst w => exact hcf.2.elim
        | lit j' v' =>
          have hj'S : j' ∈ S := hsr j' (by rw [cntC_lit_self]; omega)
          have hcnt' : cntC j' (.and l1 l2) = 0 := hnorm.2.2.2 j' v' rfl
          have hpoint' := or_lit_point' j' v' (.and l1 l2) hcf.1 hcnt'
          have hLl := cstFree_lsize0_pos (.and l1 l2) hcf.1
          have hlaml : litInd (DMTreeC.and l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.lit j' v' : DMTreeC n) = 1 := rfl
          rw [hlaml, hlamr]
          have hslack : ((simpC (subst1 j' false
              (.or (.and l1 l2) (.lit j' v')))).lsize0
              + (simpC (subst1 j' true
              (.or (.and l1 l2) (.lit j' v')))).lsize0) + 1
              ≤ (((simpC (subst1 j' false (.and l1 l2))).lsize0
                + (simpC (subst1 j' true (.and l1 l2))).lsize0)
                + ((simpC (subst1 j' false (.lit j' v' : DMTreeC n))).lsize0
                + (simpC (subst1 j' true (.lit j' v' : DMTreeC n))).lsize0)) := by
            have h1 := hpoint'
            have h2 := hLl
            omega
          have hss := sum_slack_one S _ _ 1 hpt j' hj'S hslack
          omega
        | and r1 r2 =>
          have hlaml : litInd (DMTreeC.and l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.and r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hss := Finset.sum_le_sum hpt
          omega
        | or r1 r2 =>
          have hlaml : litInd (DMTreeC.and l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.or r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hss := Finset.sum_le_sum hpt
          omega
      | or l1 l2 =>
        cases r with
        | cst w => exact hcf.2.elim
        | lit j' v' =>
          have hj'S : j' ∈ S := hsr j' (by rw [cntC_lit_self]; omega)
          have hcnt' : cntC j' (.or l1 l2) = 0 := hnorm.2.2.2 j' v' rfl
          have hpoint' := or_lit_point' j' v' (.or l1 l2) hcf.1 hcnt'
          have hLl := cstFree_lsize0_pos (.or l1 l2) hcf.1
          have hlaml : litInd (DMTreeC.or l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.lit j' v' : DMTreeC n) = 1 := rfl
          rw [hlaml, hlamr]
          have hslack : ((simpC (subst1 j' false
              (.or (.or l1 l2) (.lit j' v')))).lsize0
              + (simpC (subst1 j' true
              (.or (.or l1 l2) (.lit j' v')))).lsize0) + 1
              ≤ (((simpC (subst1 j' false (.or l1 l2))).lsize0
                + (simpC (subst1 j' true (.or l1 l2))).lsize0)
                + ((simpC (subst1 j' false (.lit j' v' : DMTreeC n))).lsize0
                + (simpC (subst1 j' true (.lit j' v' : DMTreeC n))).lsize0)) := by
            have h1 := hpoint'
            have h2 := hLl
            omega
          have hss := sum_slack_one S _ _ 1 hpt j' hj'S hslack
          omega
        | and r1 r2 =>
          have hlaml : litInd (DMTreeC.or l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.and r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hss := Finset.sum_le_sum hpt
          omega
        | or r1 r2 =>
          have hlaml : litInd (DMTreeC.or l1 l2 : DMTreeC n) = 0 := rfl
          have hlamr : litInd (DMTreeC.or r1 r2 : DMTreeC n) = 0 := rfl
          rw [hlaml, hlamr]
          have hss := Finset.sum_le_sum hpt
          omega
    have hLrfl : (DMTreeC.or l r : DMTreeC n).lsize0
        = l.lsize0 + r.lsize0 := rfl
    have hlamrfl : litInd (DMTreeC.or l r : DMTreeC n) = 0 := rfl
    have hdistrib : 2 * S.card * (l.lsize0 + r.lsize0)
        = 2 * S.card * l.lsize0 + 2 * S.card * r.lsize0 := by ring
    have hsplitAB : (∑ i ∈ S, (((simpC (subst1 i false l)).lsize0
        + (simpC (subst1 i true l)).lsize0)
        + ((simpC (subst1 i false r)).lsize0
        + (simpC (subst1 i true r)).lsize0)))
        = (∑ i ∈ S, ((simpC (subst1 i false l)).lsize0
          + (simpC (subst1 i true l)).lsize0))
          + (∑ i ∈ S, ((simpC (subst1 i false r)).lsize0
          + (simpC (subst1 i true r)).lsize0)) := Finset.sum_add_distrib
    rw [hLrfl, hlamrfl]
    omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.onestep_core
