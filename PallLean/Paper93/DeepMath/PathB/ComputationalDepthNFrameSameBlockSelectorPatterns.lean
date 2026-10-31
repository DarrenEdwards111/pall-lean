import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMixedTripleEngine

/-!
# N-Frame: same-block selector patterns — the disjunctive side of the mixed engine

Track A production, item (a): same-block slot-2 selector pairs behave disjunctively at the `ZBase`
family, supplying the V1 L-triple and an odd square for `triples_kill_split_mixed`.

  `sat3_zbase_double_flip` — **PROVED**: turning on two slot-2 selectors of the designated block at
        `ZBase` satisfies the instance (either literal fires; the witness is all-true).
  `sat3_same_block_selector_odd` — **PROVED**: engine-format odd square at any same-block selector pair
        (`0, 1, 1, 1` — parity one).
  `sat3_same_block_selector_V1` — **PROVED**: engine-format sat/sat/unsat L-triple at any same-block
        selector pair with distinct variables.

## Honest scope

This is the OR/disjunctive production.  Remaining for the discharge: the cross-block V0/odd production
(needs the two-designated-block patch) and the spanning case analysis.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **DOUBLE FLIP (proved)**: two slot-2 selectors on at `ZBase` — satisfiable. -/
theorem sat3_zbase_double_flip (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (j₁ j₂ : Fin (sat3V N)) :
    sat3Family N (Function.update (Function.update (sat3ZBase N c)
      (sat3S2Sel N c j₁) true) (sat3S2Sel N c j₂) true) = true := by
  apply decide_eq_true
  refine ⟨fun _ => true, sat3Eval_true_of_all N _ _ ?_⟩
  intro cl
  by_cases hcl : cl = c
  · subst hcl
    refine ⟨⟨2, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨2, by omega⟩ j₂ ?_ ?_⟩
    · show Function.update (Function.update (sat3ZBase N cl) (sat3S2Sel N cl j₁) true)
          (sat3S2Sel N cl j₂) true (sat3S2Sel N cl j₂) = true
      rw [Function.update_self]
    · have hne₂ : sat3Bit N cl ⟨2, by omega⟩ (sat3V N) (by omega)
          ≠ sat3S2Sel N cl j₂ := by
        intro hcontra
        have hr := sat3S2Sel_rem N cl j₂
        rw [← hcontra, sat3Bit_rem] at hr
        have hv' : (2 : ℕ) * (sat3V N + 1) + sat3V N = 2 * (sat3V N + 1) + j₂.val := hr
        have := j₂.isLt
        omega
      have hne₁ : sat3Bit N cl ⟨2, by omega⟩ (sat3V N) (by omega)
          ≠ sat3S2Sel N cl j₁ := by
        intro hcontra
        have hr := sat3S2Sel_rem N cl j₁
        rw [← hcontra, sat3Bit_rem] at hr
        have hv' : (2 : ℕ) * (sat3V N + 1) + sat3V N = 2 * (sat3V N + 1) + j₁.val := hr
        have := j₁.isLt
        omega
      rw [Function.update_of_ne hne₂, Function.update_of_ne hne₁]
      have hz : sat3ZBase N cl (sat3Bit N cl ⟨2, by omega⟩ (sat3V N) (by omega))
          = false := by
        show decide _ = false
        rw [decide_eq_false_iff_not]
        rintro ⟨hmod, -, -⟩
        rw [sat3Bit_rem] at hmod
        have hv' : (2 : ℕ) * (sat3V N + 1) + sat3V N = 0 := hmod
        omega
      rw [hz]
      rfl
  · refine ⟨⟨0, by omega⟩,
      sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩ ⟨0, hv⟩ ?_ ?_⟩
    · have hne₂ : sat3Bit N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)
          ≠ sat3S2Sel N c j₂ := by
        intro hcontra
        have hr := sat3S2Sel_rem N c j₂
        rw [← hcontra, sat3Bit_rem] at hr
        have hv' : (0 : ℕ) * (sat3V N + 1) + 0 = 2 * (sat3V N + 1) + j₂.val := hr
        omega
      have hne₁ : sat3Bit N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)
          ≠ sat3S2Sel N c j₁ := by
        intro hcontra
        have hr := sat3S2Sel_rem N c j₁
        rw [← hcontra, sat3Bit_rem] at hr
        have hv' : (0 : ℕ) * (sat3V N + 1) + 0 = 2 * (sat3V N + 1) + j₁.val := hr
        omega
      rw [Function.update_of_ne hne₂, Function.update_of_ne hne₁]
      show decide _ = true
      rw [decide_eq_true_eq]
      refine ⟨?_, ?_, ?_⟩
      · rw [sat3Bit_rem]
        show (0 : ℕ) * (sat3V N + 1) + 0 = 0
        omega
      · rw [sat3Bit_clause]
        exact fun h => hcl (Fin.ext h)
      · rw [sat3Bit_clause]
        exact cl.isLt
    · have hne₂ : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)
          ≠ sat3S2Sel N c j₂ := by
        intro hcontra
        have hr := sat3S2Sel_rem N c j₂
        rw [← hcontra, sat3Bit_rem] at hr
        have hv' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 2 * (sat3V N + 1) + j₂.val := hr
        omega
      have hne₁ : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)
          ≠ sat3S2Sel N c j₁ := by
        intro hcontra
        have hr := sat3S2Sel_rem N c j₁
        rw [← hcontra, sat3Bit_rem] at hr
        have hv' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 2 * (sat3V N + 1) + j₁.val := hr
        omega
      rw [Function.update_of_ne hne₂, Function.update_of_ne hne₁]
      have hz : sat3ZBase N c (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega))
          = false := by
        show decide _ = false
        rw [decide_eq_false_iff_not]
        rintro ⟨hmod, -, -⟩
        rw [sat3Bit_rem] at hmod
        have hv' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 0 := hmod
        omega
      rw [hz]
      rfl

/-- **ODD SQUARE (proved)**: engine-format parity one at any same-block selector pair. -/
theorem sat3_same_block_selector_odd (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (j₁ j₂ : Fin (sat3V N)) :
    xor (xor (sat3Family N (sat3ZBase N c))
        (sat3Family N (Function.update (sat3ZBase N c) (sat3S2Sel N c j₁)
          (!(sat3ZBase N c (sat3S2Sel N c j₁))))))
      (xor (sat3Family N (Function.update (sat3ZBase N c) (sat3S2Sel N c j₂)
          (!(sat3ZBase N c (sat3S2Sel N c j₂)))))
        (sat3Family N (Function.update (Function.update (sat3ZBase N c)
          (sat3S2Sel N c j₁) (!(sat3ZBase N c (sat3S2Sel N c j₁))))
          (sat3S2Sel N c j₂) (!(sat3ZBase N c (sat3S2Sel N c j₂)))))) = true := by
  rw [sat3ZBase_s2 N c c j₁, sat3ZBase_s2 N c c j₂]
  rw [show (!false) = true from rfl]
  rw [sat3ZBase_unsat N c, sat3ZBase_flip_sat N hv c j₁, sat3ZBase_flip_sat N hv c j₂,
    sat3_zbase_double_flip N hv c j₁ j₂]
  rfl

/-- **V1 L-TRIPLE (proved)**: engine-format sat/sat/unsat at any same-block selector pair with
distinct variables — the base has `j₂` on; flipping it off kills, flipping `j₁` on first rescues. -/
theorem sat3_same_block_selector_V1 (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (j₁ j₂ : Fin (sat3V N)) (hj : j₁ ≠ j₂) :
    sat3Family N (Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) true) = true ∧
    sat3Family N (Function.update (Function.update
        (Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) true)
        (sat3S2Sel N c j₁)
        (!(Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) true (sat3S2Sel N c j₁))))
      (sat3S2Sel N c j₂)
      (!(Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) true (sat3S2Sel N c j₂))))
      = true ∧
    sat3Family N (Function.update
        (Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) true)
      (sat3S2Sel N c j₂)
      (!(Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) true (sat3S2Sel N c j₂))))
      = false := by
  have hne12 : sat3S2Sel N c j₁ ≠ sat3S2Sel N c j₂ := by
    intro hcon
    have h1 := sat3S2Sel_rem N c j₁
    rw [hcon, sat3S2Sel_rem] at h1
    exact hj (Fin.ext (by omega))
  refine ⟨sat3ZBase_flip_sat N hv c j₂, ?_, ?_⟩
  · -- both-flip corner: j₁ goes on, j₂ goes back off — the j₁-flipped base
    rw [show Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) true
        (sat3S2Sel N c j₁) = false from by
      rw [Function.update_of_ne hne12]
      exact sat3ZBase_s2 N c c j₁]
    rw [Function.update_self]
    rw [show (!false) = true from rfl, show (!true) = false from rfl]
    rw [show Function.update (Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) true)
        (sat3S2Sel N c j₁) true
      = Function.update (Function.update (sat3ZBase N c) (sat3S2Sel N c j₁) true)
        (sat3S2Sel N c j₂) true from Function.update_comm hne12.symm _ _ _]
    rw [Function.update_idem]
    rw [show Function.update (Function.update (sat3ZBase N c) (sat3S2Sel N c j₁) true)
        (sat3S2Sel N c j₂) false
      = Function.update (sat3ZBase N c) (sat3S2Sel N c j₁) true from by
      rw [show (false : Bool) = Function.update (sat3ZBase N c) (sat3S2Sel N c j₁) true
          (sat3S2Sel N c j₂) from by
        rw [Function.update_of_ne hne12.symm]
        exact (sat3ZBase_s2 N c c j₂).symm]
      exact Function.update_eq_self _ _]
    exact sat3ZBase_flip_sat N hv c j₁
  · -- down-flip corner: j₂ back off — ZBase, unsatisfiable
    rw [Function.update_self, show (!true) = false from rfl, Function.update_idem]
    rw [show Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) false
        = sat3ZBase N c from by
      rw [show (false : Bool) = sat3ZBase N c (sat3S2Sel N c j₂) from
        (sat3ZBase_s2 N c c j₂).symm]
      exact Function.update_eq_self _ _]
    exact sat3ZBase_unsat N c

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_zbase_double_flip
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_same_block_selector_odd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_same_block_selector_V1
