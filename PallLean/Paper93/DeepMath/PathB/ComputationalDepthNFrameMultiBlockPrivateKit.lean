import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockPoisonBudget

/-!
# N-Frame: the private-variable kit — the stacking wall is a gadget artifact

Rung 13 of the multi-block arc (… → budget → **private kit**).  Rung 12 cornered the adversary
into stack-saturation and posed three frontiers; attacking "minimal cuts cannot stack-saturate"
head-on revealed something better: THE WALL IS OURS, NOT THEIRS.  The rung-3 kit put the clause
`{w*}` on the other data blocks — kit content depending on the reading mode — which is why kit
positions had to lie OFF `S` (the probe owns `Sᶜ`), which is what made slot-1 poison and stacked
pairs invisible.  The repair: give block `c` the kit clause `{u_c}` on a PRIVATE variable.  The
kit is then constant across modes — legitimate row content wherever `S` puts it — and the mode
moves entirely into the pin VALUES: mode `(c*, w*)` pins `w*` true, `u_c` true for `c ≠ c*`,
and `u_{c*}` false.  Stacked slot-1 bits inside `S` become row-controlled constants (set to the
kit indicator or to zero); nothing about slot 1 need lie outside `S` at pattern positions.

  `sat3KitP` — the private kit: slot-0 pattern `T c`, slot-1 clause `{u c}` on EVERY data block
        (including the designated one — designation is done by the pins now).
  `sat3KitP_read_*` — the eight data-block reads through the multi-patch.
  `sat3_private_data_clause_iff` — block `c ∈ C` is satisfied iff
        `(∃ w ∈ T c, a w) ∨ a (u c)`.
  `sat3_private_kit_neutralized` — `a (u c) = true` satisfies block `c` outright.
  `sat3_private_kit_eval` — **PROVED, the workhorse**: with pins covering patterns AND privates
        (privates injective on `C`, disjoint from all patterns and from `w*`),
        `sat3Family (patchMulti C (contextM, sat3KitP)) = decide (w* ∈ T c*)`.

Cost of the redesign: the pin pool must also cover the `|C|` privates (room becomes
`|W| + |C| + O(1) + Q ≤ m − |C|`), and privates need `|W| + |C| ≤ v` position space — both
affordable at `|C|, |W| = Θ(m)`, `v ≈ 3m`.

## Honest scope

This file is the EVAL only.  The private-kit drag (rows `2^Σ` with mode-dependent `bvec`), the
rebuilt mix transfer (no slot-1 side conditions at pattern positions), and the rebuilt
window/census chain — in which the `hkit1`/cleanliness hypotheses of rungs 5–12 DISAPPEAR and
the stacked-pair terms of the rung-12 budget should fall away — are the next rungs, not claims
of this file.  If that rebuild goes through as blueprinted, the poison budget tightens toward
`A₀ ≤ O(j) + pool-horns` with no stack term, and the band flight toward
`coneExcess = Ω(T)` up to sign-poison horns; none of that is proven yet.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The private kit -/

/-- **The private kit**: block `c` carries its pattern `T c` on slot 0 and the kit clause
`{u c}` on slot 1 — `u c` a private variable, the SAME content in every reading mode. -/
def sat3KitP (N : ℕ) (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N)) :
    Fin (sat3M N) → Fin N → Bool :=
  fun c => fun bit => decide ((∃ w ∈ T c, bit.val % sat3D N = w.val)
    ∨ bit.val % sat3D N = (sat3V N + 1) + (u c).val)

/-! ### The data-block reads -/

theorem sat3KitP_read_sel_in (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N))) (u : Fin (sat3M N) → Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) (w : Fin (sat3V N)) (hw : w ∈ T c) :
    sat3PatchMulti N C y (sat3KitP N T u)
      (sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega)) = true := by
  rw [sat3PatchMulti_own N C y (sat3KitP N T u) c hc]
  show decide _ = true
  rw [decide_eq_true_eq]
  left
  refine ⟨w, hw, ?_⟩
  rw [sat3Bit_rem]
  show (0 : ℕ) * (sat3V N + 1) + w.val = w.val
  omega

theorem sat3KitP_read_sel_out (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N))) (u : Fin (sat3M N) → Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) (i : Fin (sat3V N)) (hi : i ∉ T c) :
    sat3PatchMulti N C y (sat3KitP N T u)
      (sat3Bit N c ⟨0, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitP N T u) c hc]
  have hr : (sat3Bit N c ⟨0, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N = i.val := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, hw, hrem⟩ | hrem)
  · rw [hr] at hrem
    rw [show i = w from Fin.ext hrem] at hi
    exact hi hw
  · rw [hr] at hrem
    have := i.isLt
    omega

theorem sat3KitP_read_sign0 (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N))) (u : Fin (sat3M N) → Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) :
    sat3PatchMulti N C y (sat3KitP N T u)
      (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitP N T u) c hc]
  have hr : (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
      = sat3V N := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, -, hrem⟩ | hrem)
  · rw [hr] at hrem
    have := w.isLt
    omega
  · rw [hr] at hrem
    have := (u c).isLt
    omega

theorem sat3KitP_read_sel1_kit (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N))) (u : Fin (sat3M N) → Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) :
    sat3PatchMulti N C y (sat3KitP N T u)
      (sat3Bit N c ⟨1, by omega⟩ (u c).val
        (by have := (u c).isLt; omega)) = true := by
  rw [sat3PatchMulti_own N C y (sat3KitP N T u) c hc]
  show decide _ = true
  rw [decide_eq_true_eq]
  right
  rw [sat3Bit_rem]
  show (1 : ℕ) * (sat3V N + 1) + (u c).val = sat3V N + 1 + (u c).val
  omega

theorem sat3KitP_read_sel1_miss (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N))) (u : Fin (sat3M N) → Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) (i : Fin (sat3V N)) (hi : i ≠ u c) :
    sat3PatchMulti N C y (sat3KitP N T u)
      (sat3Bit N c ⟨1, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitP N T u) c hc]
  have hr : (sat3Bit N c ⟨1, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N = sat3V N + 1 + i.val := by
    rw [sat3Bit_rem]
    show (1 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1 + i.val
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, -, hrem⟩ | hrem)
  · rw [hr] at hrem
    have := w.isLt
    omega
  · rw [hr] at hrem
    have hiu : i.val = (u c).val := by omega
    exact hi (Fin.ext hiu)

theorem sat3KitP_read_sign1 (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N))) (u : Fin (sat3M N) → Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) :
    sat3PatchMulti N C y (sat3KitP N T u)
      (sat3Bit N c ⟨1, by omega⟩ (sat3V N) (by omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitP N T u) c hc]
  have hr : (sat3Bit N c ⟨1, by omega⟩ (sat3V N) (by omega)).val % sat3D N
      = sat3V N + 1 + sat3V N := by
    rw [sat3Bit_rem]
    show (1 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 + sat3V N
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, -, hrem⟩ | hrem)
  · rw [hr] at hrem
    have := w.isLt
    omega
  · rw [hr] at hrem
    have := (u c).isLt
    omega

theorem sat3KitP_read_slot2 (N : ℕ) (C : Finset (Fin (sat3M N))) (y : Fin N → Bool)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N))) (u : Fin (sat3M N) → Fin (sat3V N))
    (c : Fin (sat3M N)) (hc : c ∈ C) (i : Fin (sat3V N)) :
    sat3PatchMulti N C y (sat3KitP N T u)
      (sat3Bit N c ⟨2, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  rw [sat3PatchMulti_own N C y (sat3KitP N T u) c hc]
  have hr : (sat3Bit N c ⟨2, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N
      = 2 * (sat3V N + 1) + i.val := by
    rw [sat3Bit_rem]
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨w, -, hrem⟩ | hrem)
  · rw [hr] at hrem
    have := w.isLt
    omega
  · rw [hr] at hrem
    have := (u c).isLt
    omega

/-! ### The data-clause analysis -/

set_option maxHeartbeats 1600000 in
/-- **The private-kit block eval**: block `c ∈ C` is satisfied iff its pattern fires or its
private kit fires — `(∃ w ∈ T c, a w) ∨ a (u c)`. -/
theorem sat3_private_data_clause_iff (N : ℕ) (C : Finset (Fin (sat3M N)))
    (y : Fin N → Bool) (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N)) (a : Fin (sat3V N) → Bool)
    (c : Fin (sat3M N)) (hc : c ∈ C) :
    (∃ t, sat3Lit N (sat3PatchMulti N C y (sat3KitP N T u)) a c t = true) ↔
      ((∃ w ∈ T c, a w = true) ∨ a (u c) = true) := by
  constructor
  · rintro ⟨t, ht⟩
    rcases t with ⟨tv, htv⟩
    interval_cases tv
    · unfold sat3Lit at ht
      obtain ⟨i, -, hi⟩ := List.any_eq_true.mp ht
      rw [Bool.and_eq_true] at hi
      obtain ⟨hisel, hilit⟩ := hi
      have hiT : i ∈ T c := by
        by_contra hniT
        rw [sat3KitP_read_sel_out N C y T u c hc i hniT] at hisel
        exact Bool.noConfusion hisel
      rw [sat3KitP_read_sign0 N C y T u c hc] at hilit
      refine Or.inl ⟨i, hiT, ?_⟩
      cases hai : a i
      · rw [hai] at hilit
        exact Bool.noConfusion hilit
      · rfl
    · unfold sat3Lit at ht
      obtain ⟨i, -, hi⟩ := List.any_eq_true.mp ht
      rw [Bool.and_eq_true] at hi
      obtain ⟨hisel, hilit⟩ := hi
      by_cases hiu : i = u c
      · rw [hiu] at hilit
        rw [sat3KitP_read_sign1 N C y T u c hc] at hilit
        refine Or.inr ?_
        cases hau : a (u c)
        · rw [hau] at hilit
          exact Bool.noConfusion hilit
        · rfl
      · exfalso
        rw [sat3KitP_read_sel1_miss N C y T u c hc i hiu] at hisel
        exact Bool.noConfusion hisel
    · exfalso
      rw [sat3Lit_false_of_empty N (sat3PatchMulti N C y (sat3KitP N T u))
        a c ⟨2, htv⟩
        (fun i => sat3KitP_read_slot2 N C y T u c hc i)] at ht
      exact Bool.noConfusion ht
  · rintro (⟨w, hwT, haw⟩ | hau)
    · refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N
        (sat3PatchMulti N C y (sat3KitP N T u)) a c ⟨0, by omega⟩ w
        (sat3KitP_read_sel_in N C y T u c hc w hwT) ?_⟩
      rw [sat3KitP_read_sign0 N C y T u c hc, haw]
      rfl
    · refine ⟨⟨1, by omega⟩, sat3Lit_true_of_selected N
        (sat3PatchMulti N C y (sat3KitP N T u)) a c ⟨1, by omega⟩ (u c)
        (sat3KitP_read_sel1_kit N C y T u c hc) ?_⟩
      rw [sat3KitP_read_sign1 N C y T u c hc, hau]
      rfl

/-- **Neutralization**: `a (u c) = true` satisfies block `c` outright — in every reading mode,
because the kit is mode-independent. -/
theorem sat3_private_kit_neutralized (N : ℕ) (C : Finset (Fin (sat3M N)))
    (y : Fin N → Bool) (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N)) (a : Fin (sat3V N) → Bool)
    (c : Fin (sat3M N)) (hc : c ∈ C) (hau : a (u c) = true) :
    ∃ t, sat3Lit N (sat3PatchMulti N C y (sat3KitP N T u)) a c t = true :=
  (sat3_private_data_clause_iff N C y T u a c hc).mpr (Or.inr hau)

/-! ### The eval -/

set_option maxHeartbeats 1600000 in
/-- **THE PRIVATE-KIT EVAL (proved)**: with pins covering the patterns AND the privates
(privates injective on `C`, disjoint from every pattern and from `w*`), reading mode
`(c*, w*)` — pinned as `w* ↦ true`, `u_c ↦ true` for `c ≠ c*`, `u_{c*} ↦ false` — isolates the
designated pattern bit: the instance value is `decide (w* ∈ T c*)`.  No condition on where `S`
puts slot 1. -/
theorem sat3_private_kit_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (hα : Function.Injective α)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N))
    (hcov : ∀ c ∈ C, ∀ w ∈ T c, ∃ p : Fin k, α p = w)
    (hucov : ∀ c ∈ C, ∃ p : Fin k, α p = u c)
    (huinj : ∀ c ∈ C, ∀ c' ∈ C, u c = u c' → c = c')
    (hupat : ∀ c ∈ C, ∀ c' ∈ C, u c ∉ T c')
    (cstar : Fin (sat3M N)) (hcstar : cstar ∈ C)
    (wstar : Fin (sat3V N)) (pstar : Fin k) (hpstar : α pstar = wstar)
    (huw : ∀ c ∈ C, u c ≠ wstar) :
    sat3Family N (sat3PatchMulti N C
      (sat3ContextM N C hk α (fun p =>
        decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c)))
      (sat3KitP N T u))
      = decide (wstar ∈ T cstar) := by
  classical
  set bvec : Fin k → Bool := fun p =>
    decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c) with hbvec
  set x : Fin N → Bool :=
    sat3PatchMulti N C (sat3ContextM N C hk α bvec) (sat3KitP N T u) with hx
  -- the pinned value at a private
  have hbvec_u : ∀ c ∈ C, ∀ p : Fin k, α p = u c →
      bvec p = decide (c ≠ cstar) := by
    intro c hc p hp
    by_cases hne : c = cstar
    · rw [hne] at hp hc ⊢
      have : bvec p = false := by
        apply decide_eq_false
        rintro (h | ⟨c', hc', hne', h⟩)
        · exact huw cstar hc (hp.symm.trans h)
        · exact hne' (huinj cstar hc c' hc' (hp.symm.trans h)).symm
      rw [this, decide_eq_false (by simp : ¬(cstar ≠ cstar))]
    · have : bvec p = true := by
        apply decide_eq_true
        exact Or.inr ⟨c, hc, hne, hp⟩
      rw [this, decide_eq_true hne]
  by_cases hsat : wstar ∈ T cstar
  · rw [decide_eq_true hsat]
    set awit : Fin (sat3V N) → Bool :=
      fun i => if h : ∃ p : Fin k, α p = i then bvec (Classical.choose h) else true
      with hawit
    have hawit_at : ∀ p : Fin k, awit (α p) = bvec p := by
      intro p
      show (if h : ∃ p' : Fin k, α p' = α p then bvec (Classical.choose h) else true)
        = bvec p
      have hex : ∃ p' : Fin k, α p' = α p := ⟨p, rfl⟩
      rw [dif_pos hex]
      exact congrArg bvec (hα (Classical.choose_spec hex))
    have hawit_wstar : awit wstar = true := by
      rw [← hpstar, hawit_at pstar]
      exact decide_eq_true (Or.inl hpstar)
    have hawit_u : ∀ c ∈ C, c ≠ cstar → awit (u c) = true := by
      intro c hc hne
      obtain ⟨p, hp⟩ := hucov c hc
      rw [← hp, hawit_at p, hbvec_u c hc p hp]
      exact decide_eq_true hne
    rw [sat3Family_iff]
    refine ⟨awit, sat3Eval_true_of_all N x awit ?_⟩
    intro cl
    by_cases hclC : cl ∈ C
    · by_cases hclstar : cl = cstar
      · refine (sat3_private_data_clause_iff N C (sat3ContextM N C hk α bvec) T u
          awit cl hclC).mpr (Or.inl ⟨wstar, ?_, hawit_wstar⟩)
        rw [hclstar]
        exact hsat
      · exact sat3_private_kit_neutralized N C (sat3ContextM N C hk α bvec) T u
          awit cl hclC (hawit_u cl hclC hclstar)
    · by_cases hpin : ∃ p : Fin k, sat3PinClauseM N C hk p = cl
      · obtain ⟨p, rfl⟩ := hpin
        refine (sat3_multi_pin_clause_iff N C hk α bvec (sat3KitP N T u)
          awit p).mpr ?_
        rw [hawit_at p]
        cases bvec p <;> rfl
      · exact sat3_multi_taut_clause_sat N hv C hk α bvec (sat3KitP N T u)
          awit cl hclC (fun p h => hpin ⟨p, Fin.ext h.symm⟩)
  · rw [decide_eq_false hsat]
    apply decide_eq_false
    rintro ⟨A, hA⟩
    have hforce : ∀ p : Fin k, A (α p) = bvec p := by
      intro p
      exact xor_decide_eq _ _
        ((sat3_multi_pin_clause_iff N C hk α bvec (sat3KitP N T u) A p).mp
          (sat3Eval_clause_true N x A hA (sat3PinClauseM N C hk p)))
    rcases (sat3_private_data_clause_iff N C (sat3ContextM N C hk α bvec) T u
        A cstar hcstar).mp (sat3Eval_clause_true N x A hA cstar)
      with ⟨w, hwT, hAw⟩ | hAu
    · obtain ⟨p, hp⟩ := hcov cstar hcstar w hwT
      have h1 : bvec p = true := by
        rw [← hforce p, hp]
        exact hAw
      have h1' : decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c) = true := h1
      rcases of_decide_eq_true h1' with h | ⟨c', hc', -, h⟩
      · have hww : w = wstar := by
          rw [← hp]
          exact h
        rw [hww] at hwT
        exact hsat hwT
      · have hwu : w = u c' := by
          rw [← hp]
          exact h
        rw [hwu] at hwT
        exact hupat c' hc' cstar hcstar hwT
    · obtain ⟨p, hp⟩ := hucov cstar hcstar
      have h1 : bvec p = decide (cstar ≠ cstar) := hbvec_u cstar hcstar p hp
      rw [decide_eq_false (by simp : ¬(cstar ≠ cstar))] at h1
      have h2 : A (u cstar) = false := by
        rw [← hp, hforce p, h1]
      rw [hAu] at h2
      exact Bool.noConfusion h2

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_data_clause_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_kit_neutralized
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_kit_eval
