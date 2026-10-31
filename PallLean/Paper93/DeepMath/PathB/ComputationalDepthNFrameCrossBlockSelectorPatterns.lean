import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSameBlockSelectorPatterns

/-!
# N-Frame: cross-block selector patterns — the conjunctive side of the mixed engine

Track A production, item (b).  The two-designated-block base `sat3ZBase2` leaves blocks `c₁` and `c₂`
empty and every other block live — so satisfiability *requires both* selectors, an AND-interaction:
corners `0, 0, 0, 1`.

  `sat3ZBase2` — the two-block base (no patch combinator needed; the `ZBase` idiom directly).
  `sat3_zbase2_both_sat` — **PROVED**: both selectors on ⇒ satisfiable (all-true witness).
  `sat3_cross_block_selector_odd` — **PROVED**: engine-format odd square (`0,0,0,1`, parity one).
  `sat3_cross_block_selector_V0` — **PROVED**: engine-format unsat/unsat/sat L-triple — base has `c₁`'s
        selector on (`c₂` empty: unsat); flipping `c₂`'s up rescues; flipping `c₁`'s down first re-kills.

## Honest scope

Both engine sides are now produced: same-block pairs give V1 + odd, cross-block pairs give V0 + odd,
sign pairs have the two-squares kill.  What remains for `Sat3AllPinsAlignedNoSplit` is the spanning case
analysis — for every fully-sign-aligned proper cut, locate a separated odd-source, a separated V1-source,
and a separated V0-source and fire `triples_kill_split_mixed`.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The two-designated-block base: blocks `c₁, c₂` empty, every other block carries the live
variable-0 selector. -/
def sat3ZBase2 (N : ℕ) (c₁ c₂ : Fin (sat3M N)) : Fin N → Bool :=
  fun bb => decide (bb.val % sat3D N = 0 ∧ bb.val / sat3D N ≠ c₁.val ∧
    bb.val / sat3D N ≠ c₂.val ∧ bb.val / sat3D N < sat3M N)

theorem sat3ZBase2_s2 (N : ℕ) (c₁ c₂ c : Fin (sat3M N)) (j : Fin (sat3V N)) :
    sat3ZBase2 N c₁ c₂ (sat3S2Sel N c j) = false := by
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro ⟨hmod, -, -, -⟩
  rw [sat3S2Sel_rem] at hmod
  omega

theorem sat3ZBase2_block_read (N : ℕ) (c₁ c₂ cl : Fin (sat3M N))
    (hcl : cl.val = c₁.val ∨ cl.val = c₂.val) (t : Fin 3) (fI : ℕ)
    (hfI : fI < sat3V N + 1) :
    sat3ZBase2 N c₁ c₂ (sat3Bit N cl t fI hfI) = false := by
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro ⟨-, hd1, hd2, -⟩
  rw [sat3Bit_clause] at hd1 hd2
  rcases hcl with h | h
  · exact hd1 h
  · exact hd2 h

/-- A selector of one block never collides with bits of a different block. -/
theorem sat3Bit_ne_s2sel_of_clause (N : ℕ) (cl c : Fin (sat3M N))
    (hne : cl.val ≠ c.val) (t : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1)
    (j : Fin (sat3V N)) : sat3Bit N cl t fI hfI ≠ sat3S2Sel N c j := by
  intro hcontra
  have hd := sat3S2Sel_div N c j
  rw [← hcontra, sat3Bit_clause] at hd
  exact hne hd

/-- **BOTH SELECTORS ON (proved)**: satisfiable — the all-true witness fires both literals. -/
theorem sat3_zbase2_both_sat (N : ℕ) (hv : 1 ≤ sat3V N) (c₁ c₂ : Fin (sat3M N))
    (hc : c₁.val ≠ c₂.val) (j₁ j₂ : Fin (sat3V N)) :
    sat3Family N (Function.update (Function.update (sat3ZBase2 N c₁ c₂)
      (sat3S2Sel N c₁ j₁) true) (sat3S2Sel N c₂ j₂) true) = true := by
  apply decide_eq_true
  refine ⟨fun _ => true, sat3Eval_true_of_all N _ _ ?_⟩
  intro cl
  by_cases hcl1 : cl = c₁
  · subst hcl1
    refine ⟨⟨2, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨2, by omega⟩ j₁ ?_ ?_⟩
    · show Function.update (Function.update (sat3ZBase2 N cl c₂)
          (sat3S2Sel N cl j₁) true) (sat3S2Sel N c₂ j₂) true (sat3S2Sel N cl j₁) = true
      rw [Function.update_of_ne (by
        intro hcontra
        have hd := sat3S2Sel_div N c₂ j₂
        rw [← hcontra, sat3S2Sel_div] at hd
        exact hc hd)]
      rw [Function.update_self]
    · have hne₂ : sat3Bit N cl ⟨2, by omega⟩ (sat3V N) (by omega)
          ≠ sat3S2Sel N c₂ j₂ := sat3Bit_ne_s2sel_of_clause N cl c₂ hc _ _ _ j₂
      have hne₁ : sat3Bit N cl ⟨2, by omega⟩ (sat3V N) (by omega)
          ≠ sat3S2Sel N cl j₁ := by
        intro hcontra
        have hr := sat3S2Sel_rem N cl j₁
        rw [← hcontra, sat3Bit_rem] at hr
        have hv' : (2 : ℕ) * (sat3V N + 1) + sat3V N = 2 * (sat3V N + 1) + j₁.val := hr
        have := j₁.isLt
        omega
      rw [Function.update_of_ne hne₂, Function.update_of_ne hne₁]
      rw [sat3ZBase2_block_read N cl c₂ cl (Or.inl rfl) _ _ _]
      rfl
  · by_cases hcl2 : cl = c₂
    · subst hcl2
      refine ⟨⟨2, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨2, by omega⟩ j₂ ?_ ?_⟩
      · show Function.update (Function.update (sat3ZBase2 N c₁ cl)
            (sat3S2Sel N c₁ j₁) true) (sat3S2Sel N cl j₂) true (sat3S2Sel N cl j₂) = true
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
            ≠ sat3S2Sel N c₁ j₁ :=
          sat3Bit_ne_s2sel_of_clause N cl c₁ (fun h => hc h.symm) _ _ _ j₁
        rw [Function.update_of_ne hne₂, Function.update_of_ne hne₁]
        rw [sat3ZBase2_block_read N c₁ cl cl (Or.inr rfl) _ _ _]
        rfl
    · refine ⟨⟨0, by omega⟩,
        sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩ ⟨0, hv⟩ ?_ ?_⟩
      · have hne₂ : sat3Bit N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)
            ≠ sat3S2Sel N c₂ j₂ := sat3Bit_ne_s2sel_of_clause N cl c₂
          (fun h => hcl2 (Fin.ext h)) _ _ _ j₂
        have hne₁ : sat3Bit N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)
            ≠ sat3S2Sel N c₁ j₁ := sat3Bit_ne_s2sel_of_clause N cl c₁
          (fun h => hcl1 (Fin.ext h)) _ _ _ j₁
        rw [Function.update_of_ne hne₂, Function.update_of_ne hne₁]
        show decide _ = true
        rw [decide_eq_true_eq]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [sat3Bit_rem]
          show (0 : ℕ) * (sat3V N + 1) + 0 = 0
          omega
        · rw [sat3Bit_clause]
          exact fun h => hcl1 (Fin.ext h)
        · rw [sat3Bit_clause]
          exact fun h => hcl2 (Fin.ext h)
        · rw [sat3Bit_clause]
          exact cl.isLt
      · have hne₂ : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)
            ≠ sat3S2Sel N c₂ j₂ := sat3Bit_ne_s2sel_of_clause N cl c₂
          (fun h => hcl2 (Fin.ext h)) _ _ _ j₂
        have hne₁ : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)
            ≠ sat3S2Sel N c₁ j₁ := sat3Bit_ne_s2sel_of_clause N cl c₁
          (fun h => hcl1 (Fin.ext h)) _ _ _ j₁
        rw [Function.update_of_ne hne₂, Function.update_of_ne hne₁]
        have hz : sat3ZBase2 N c₁ c₂ (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega))
            = false := by
          show decide _ = false
          rw [decide_eq_false_iff_not]
          rintro ⟨hmod, -, -, -⟩
          rw [sat3Bit_rem] at hmod
          have hv' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 0 := hmod
          omega
        rw [hz]
        rfl

/-- Any point that is `sat3ZBase2`-like on block `cl ∈ {c₁, c₂}` is unsatisfiable. -/
theorem sat3_zbase2_kill (N : ℕ) (c₁ c₂ : Fin (sat3M N)) (x : Fin N → Bool)
    (cl : Fin (sat3M N)) (hcl : cl.val = c₁.val ∨ cl.val = c₂.val)
    (hx : ∀ (t : Fin 3) (i : Fin (sat3V N)),
      x (sat3Bit N cl t i.val (by have := i.isLt; omega)) = false) :
    sat3Family N x = false :=
  sat3Family_false_of_empty_clause N x cl hx

/-- **ODD SQUARE (proved)**: engine-format corners `0, 0, 0, 1` at any cross-block selector pair. -/
theorem sat3_cross_block_selector_odd (N : ℕ) (hv : 1 ≤ sat3V N)
    (c₁ c₂ : Fin (sat3M N)) (hc : c₁.val ≠ c₂.val) (j₁ j₂ : Fin (sat3V N)) :
    xor (xor (sat3Family N (sat3ZBase2 N c₁ c₂))
        (sat3Family N (Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ j₁)
          (!(sat3ZBase2 N c₁ c₂ (sat3S2Sel N c₁ j₁))))))
      (xor (sat3Family N (Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₂ j₂)
          (!(sat3ZBase2 N c₁ c₂ (sat3S2Sel N c₂ j₂)))))
        (sat3Family N (Function.update (Function.update (sat3ZBase2 N c₁ c₂)
          (sat3S2Sel N c₁ j₁) (!(sat3ZBase2 N c₁ c₂ (sat3S2Sel N c₁ j₁))))
          (sat3S2Sel N c₂ j₂) (!(sat3ZBase2 N c₁ c₂ (sat3S2Sel N c₂ j₂)))))) = true := by
  rw [sat3ZBase2_s2 N c₁ c₂ c₁ j₁, sat3ZBase2_s2 N c₁ c₂ c₂ j₂]
  rw [show (!false) = true from rfl]
  have h0 : sat3Family N (sat3ZBase2 N c₁ c₂) = false :=
    sat3_zbase2_kill N c₁ c₂ _ c₁ (Or.inl rfl)
      (fun t i => sat3ZBase2_block_read N c₁ c₂ c₁ (Or.inl rfl) t i.val
        (by have := i.isLt; omega))
  have h1 : sat3Family N (Function.update (sat3ZBase2 N c₁ c₂)
      (sat3S2Sel N c₁ j₁) true) = false := by
    apply sat3_zbase2_kill N c₁ c₂ _ c₂ (Or.inr rfl)
    intro t i
    rw [Function.update_of_ne (sat3Bit_ne_s2sel_of_clause N c₂ c₁
      (fun h => hc h.symm) _ _ _ j₁)]
    exact sat3ZBase2_block_read N c₁ c₂ c₂ (Or.inr rfl) t i.val
      (by have := i.isLt; omega)
  have h2 : sat3Family N (Function.update (sat3ZBase2 N c₁ c₂)
      (sat3S2Sel N c₂ j₂) true) = false := by
    apply sat3_zbase2_kill N c₁ c₂ _ c₁ (Or.inl rfl)
    intro t i
    rw [Function.update_of_ne (sat3Bit_ne_s2sel_of_clause N c₁ c₂ hc _ _ _ j₂)]
    exact sat3ZBase2_block_read N c₁ c₂ c₁ (Or.inl rfl) t i.val
      (by have := i.isLt; omega)
  rw [h0, h1, h2, sat3_zbase2_both_sat N hv c₁ c₂ hc j₁ j₂]
  rfl

/-- **V0 L-TRIPLE (proved)**: engine-format unsat/unsat/sat at any cross-block selector pair — base has
`c₁`'s selector on (`c₂` empty), flipping `c₂`'s up rescues, flipping `c₁`'s down first re-kills. -/
theorem sat3_cross_block_selector_V0 (N : ℕ) (hv : 1 ≤ sat3V N)
    (c₁ c₂ : Fin (sat3M N)) (hc : c₁.val ≠ c₂.val) (j₁ j₂ : Fin (sat3V N)) :
    sat3Family N (Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ j₁) true)
      = false ∧
    sat3Family N (Function.update (Function.update
        (Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ j₁) true)
        (sat3S2Sel N c₁ j₁)
        (!(Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ j₁) true
          (sat3S2Sel N c₁ j₁))))
      (sat3S2Sel N c₂ j₂)
      (!(Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ j₁) true
        (sat3S2Sel N c₂ j₂)))) = false ∧
    sat3Family N (Function.update
        (Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ j₁) true)
      (sat3S2Sel N c₂ j₂)
      (!(Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ j₁) true
        (sat3S2Sel N c₂ j₂)))) = true := by
  have hne21 : sat3S2Sel N c₂ j₂ ≠ sat3S2Sel N c₁ j₁ := by
    intro hcon
    have hd := sat3S2Sel_div N c₂ j₂
    rw [hcon, sat3S2Sel_div] at hd
    exact hc hd
  have hu0 : Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ j₁) true
      (sat3S2Sel N c₂ j₂) = false := by
    rw [Function.update_of_ne hne21]
    exact sat3ZBase2_s2 N c₁ c₂ c₂ j₂
  refine ⟨?_, ?_, ?_⟩
  · -- base: c₂ empty
    apply sat3_zbase2_kill N c₁ c₂ _ c₂ (Or.inr rfl)
    intro t i
    rw [Function.update_of_ne (sat3Bit_ne_s2sel_of_clause N c₂ c₁
      (fun h => hc h.symm) _ _ _ j₁)]
    exact sat3ZBase2_block_read N c₁ c₂ c₂ (Or.inr rfl) t i.val
      (by have := i.isLt; omega)
  · -- both flips: c₁'s selector back off, c₂'s on — c₁ empty
    rw [Function.update_self, show (!true) = false from rfl, Function.update_idem]
    rw [hu0, show (!false) = true from rfl]
    rw [show Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ j₁) false
        = sat3ZBase2 N c₁ c₂ from by
      rw [show (false : Bool) = sat3ZBase2 N c₁ c₂ (sat3S2Sel N c₁ j₁) from
        (sat3ZBase2_s2 N c₁ c₂ c₁ j₁).symm]
      exact Function.update_eq_self _ _]
    apply sat3_zbase2_kill N c₁ c₂ _ c₁ (Or.inl rfl)
    intro t i
    rw [Function.update_of_ne (sat3Bit_ne_s2sel_of_clause N c₁ c₂ hc _ _ _ j₂)]
    exact sat3ZBase2_block_read N c₁ c₂ c₁ (Or.inl rfl) t i.val
      (by have := i.isLt; omega)
  · -- t-flip alone: both on — satisfiable
    rw [hu0, show (!false) = true from rfl]
    exact sat3_zbase2_both_sat N hv c₁ c₂ hc j₁ j₂

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_zbase2_both_sat
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cross_block_selector_odd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cross_block_selector_V0
