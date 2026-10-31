import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTwoMassAssembly

/-!
# N-Frame: general-slot patterns — every selector of every slot joins the pattern graph

The `ZBase` pattern families, generalized from slot 2 to all three slots.  At `ZBase`-style points every
sign field of the designated block reads `0` (the whole block reads `0` — the div conjunct), so a slot-`t`
selector turned on contributes the free literal `a_j`, and the all-true witness fires it.

  `sat3ZBase_own` / `sat3ZBase_outside_satisfied` (+ `ZBase2` analogues) — the shared read/satisfaction
        layer, slot-generic.
  `sat3_zbase_flip_sat_t` / `sat3_zbase_double_flip_t` — **PROVED**: one or two selectors of any slots
        turned on at `ZBase` satisfy the instance.
  `sat3_same_block_odd_t` / `sat3_same_block_V1_t` — **PROVED**: engine-format odd square and V1 triple
        for any same-block selector pair, any slots.
  `sat3_zbase2_both_sat_t` / `sat3_cross_block_odd_t` / `sat3_cross_block_V0_t` — **PROVED**:
        engine-format odd square and V0 triple for any cross-block selector pair, any slots.

## Honest scope

With these, every slot-0/1 selector has killable pairs into the united mass (same-block OR pairs to
slot-2 selectors, cross-block AND pairs).  The final assembly sweeping slot-0/1 selectors into the mass,
and then the slot-1/2 sign fields (slot-`t` probes), are the named last rungs before
`2·m·D ≤ cbudget (sat3Family N)` fires unconditionally.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- `ZBase` reads `0` on every bit of the designated block. -/
theorem sat3ZBase_own (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (fI : ℕ)
    (hfI : fI < sat3V N + 1) : sat3ZBase N c (sat3Bit N c t fI hfI) = false := by
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro ⟨-, hdiv, -⟩
  rw [sat3Bit_clause] at hdiv
  exact hdiv rfl

/-- Outside clauses at `ZBase`-reading points are satisfied by the all-true witness. -/
theorem sat3ZBase_outside_satisfied (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (cl : Fin (sat3M N)) (hclv : cl.val ≠ c.val) (X : Fin N → Bool)
    (hread : ∀ (t : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
      X (sat3Bit N cl t fI hfI) = sat3ZBase N c (sat3Bit N cl t fI hfI)) :
    ∃ t, sat3Lit N X (fun _ => true) cl t = true := by
  refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨0, by omega⟩ ⟨0, hv⟩ ?_ ?_⟩
  · rw [hread]
    show decide _ = true
    rw [decide_eq_true_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + 0 = 0
      omega
    · rw [sat3Bit_clause]
      exact hclv
    · rw [sat3Bit_clause]
      exact cl.isLt
  · rw [hread]
    have hz : sat3ZBase N c (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
      show decide _ = false
      rw [decide_eq_false_iff_not]
      rintro ⟨hmod, -, -⟩
      rw [sat3Bit_rem] at hmod
      have h' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 0 := hmod
      omega
    rw [hz]
    rfl

/-- Outside clauses at `ZBase2`-reading points are satisfied by the all-true witness. -/
theorem sat3ZBase2_outside_satisfied (N : ℕ) (hv : 1 ≤ sat3V N)
    (c₁ c₂ : Fin (sat3M N)) (cl : Fin (sat3M N))
    (hcl1 : cl.val ≠ c₁.val) (hcl2 : cl.val ≠ c₂.val) (X : Fin N → Bool)
    (hread : ∀ (t : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
      X (sat3Bit N cl t fI hfI) = sat3ZBase2 N c₁ c₂ (sat3Bit N cl t fI hfI)) :
    ∃ t, sat3Lit N X (fun _ => true) cl t = true := by
  refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N X _ cl ⟨0, by omega⟩ ⟨0, hv⟩ ?_ ?_⟩
  · rw [hread]
    show decide _ = true
    rw [decide_eq_true_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + 0 = 0
      omega
    · rw [sat3Bit_clause]
      exact hcl1
    · rw [sat3Bit_clause]
      exact hcl2
    · rw [sat3Bit_clause]
      exact cl.isLt
  · rw [hread]
    have hz : sat3ZBase2 N c₁ c₂ (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega))
        = false := by
      show decide _ = false
      rw [decide_eq_false_iff_not]
      rintro ⟨hmod, -, -, -⟩
      rw [sat3Bit_rem] at hmod
      have h' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 0 := hmod
      omega
    rw [hz]
    rfl

/-- Sign fields never collide with selector fields of the same block. -/
theorem sat3_sign_ne_sel_bit (N : ℕ) (c : Fin (sat3M N)) (ts t : Fin 3)
    (j : Fin (sat3V N)) :
    sat3Bit N c ts (sat3V N) (by omega) ≠ sat3Bit N c t j.val
      (by have := j.isLt; omega) := by
  intro hcon
  have hval := congrArg Fin.val hcon
  have hj := j.isLt
  rcases ts with ⟨tsv, htsv⟩
  rcases t with ⟨tv, htv⟩
  interval_cases tsv <;> interval_cases tv
  · exact absurd (show c.val * sat3D N + 0 * (sat3V N + 1) + sat3V N
        = c.val * sat3D N + 0 * (sat3V N + 1) + j.val from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 0 * (sat3V N + 1) + sat3V N
        = c.val * sat3D N + 1 * (sat3V N + 1) + j.val from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 0 * (sat3V N + 1) + sat3V N
        = c.val * sat3D N + 2 * (sat3V N + 1) + j.val from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 1 * (sat3V N + 1) + sat3V N
        = c.val * sat3D N + 0 * (sat3V N + 1) + j.val from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 1 * (sat3V N + 1) + sat3V N
        = c.val * sat3D N + 1 * (sat3V N + 1) + j.val from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 1 * (sat3V N + 1) + sat3V N
        = c.val * sat3D N + 2 * (sat3V N + 1) + j.val from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 2 * (sat3V N + 1) + sat3V N
        = c.val * sat3D N + 0 * (sat3V N + 1) + j.val from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 2 * (sat3V N + 1) + sat3V N
        = c.val * sat3D N + 1 * (sat3V N + 1) + j.val from hval) (by omega)
  · exact absurd (show c.val * sat3D N + 2 * (sat3V N + 1) + sat3V N
        = c.val * sat3D N + 2 * (sat3V N + 1) + j.val from hval) (by omega)

/-- **SINGLE FLIP, ANY SLOT (proved)**: one selector on at `ZBase` — satisfiable. -/
theorem sat3_zbase_flip_sat_t (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (t : Fin 3) (j : Fin (sat3V N)) :
    sat3Family N (Function.update (sat3ZBase N c)
      (sat3Bit N c t j.val (by have := j.isLt; omega)) true) = true := by
  apply decide_eq_true
  refine ⟨fun _ => true, sat3Eval_true_of_all N _ _ ?_⟩
  intro cl
  by_cases hcl : cl = c
  · subst hcl
    refine ⟨t, sat3Lit_true_of_selected N _ _ cl t j ?_ ?_⟩
    · exact Function.update_self _ _ _
    · rw [Function.update_of_ne (sat3_sign_ne_sel_bit N cl t t j)]
      rw [sat3ZBase_own N cl t (sat3V N) (by omega)]
      rfl
  · exact sat3ZBase_outside_satisfied N hv c cl (fun h => hcl (Fin.ext h)) _
      (fun t' fI hfI => by
        rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _
          (fun h => hcl (Fin.ext h)))])

/-- **DOUBLE FLIP, ANY SLOTS (proved)**: two selectors on at `ZBase` — satisfiable. -/
theorem sat3_zbase_double_flip_t (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N)) :
    sat3Family N (Function.update (Function.update (sat3ZBase N c)
      (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)) true)
      (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true) = true := by
  apply decide_eq_true
  refine ⟨fun _ => true, sat3Eval_true_of_all N _ _ ?_⟩
  intro cl
  by_cases hcl : cl = c
  · subst hcl
    refine ⟨t₂, sat3Lit_true_of_selected N _ _ cl t₂ j₂ ?_ ?_⟩
    · exact Function.update_self _ _ _
    · rw [Function.update_of_ne (sat3_sign_ne_sel_bit N cl t₂ t₂ j₂),
        Function.update_of_ne (sat3_sign_ne_sel_bit N cl t₂ t₁ j₁)]
      rw [sat3ZBase_own N cl t₂ (sat3V N) (by omega)]
      rfl
  · exact sat3ZBase_outside_satisfied N hv c cl (fun h => hcl (Fin.ext h)) _
      (fun t' fI hfI => by
        rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _
            (fun h => hcl (Fin.ext h))),
          Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _
            (fun h => hcl (Fin.ext h)))])

/-- **SAME-BLOCK ODD, ANY SLOTS (proved)**: corners `0, 1, 1, 1`. -/
theorem sat3_same_block_odd_t (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N)) :
    xor (xor (sat3Family N (sat3ZBase N c))
        (sat3Family N (Function.update (sat3ZBase N c)
          (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega))
          (!(sat3ZBase N c (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)))))))
      (xor (sat3Family N (Function.update (sat3ZBase N c)
          (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
          (!(sat3ZBase N c (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))))))
        (sat3Family N (Function.update (Function.update (sat3ZBase N c)
          (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega))
          (!(sat3ZBase N c (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)))))
          (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
          (!(sat3ZBase N c (sat3Bit N c t₂ j₂.val
            (by have := j₂.isLt; omega))))))) = true := by
  rw [sat3ZBase_own N c t₁ j₁.val (by have := j₁.isLt; omega),
    sat3ZBase_own N c t₂ j₂.val (by have := j₂.isLt; omega)]
  rw [show (!false) = true from rfl]
  rw [sat3ZBase_unsat N c, sat3_zbase_flip_sat_t N hv c t₁ j₁,
    sat3_zbase_flip_sat_t N hv c t₂ j₂, sat3_zbase_double_flip_t N hv c t₁ t₂ j₁ j₂]
  rfl

/-- **SAME-BLOCK V1, ANY SLOTS (proved)**: sat/sat/unsat with the `(t₂, j₂)` selector as the down
flip. -/
theorem sat3_same_block_V1_t (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N))
    (hne : sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)
      ≠ sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) :
    sat3Family N (Function.update (sat3ZBase N c)
      (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true) = true ∧
    sat3Family N (Function.update (Function.update
        (Function.update (sat3ZBase N c)
          (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true)
        (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega))
        (!(Function.update (sat3ZBase N c)
          (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true
          (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)))))
      (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
      (!(Function.update (sat3ZBase N c)
        (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true
        (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))))) = true ∧
    sat3Family N (Function.update
        (Function.update (sat3ZBase N c)
          (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true)
      (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
      (!(Function.update (sat3ZBase N c)
        (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true
        (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))))) = false := by
  refine ⟨sat3_zbase_flip_sat_t N hv c t₂ j₂, ?_, ?_⟩
  · rw [show Function.update (sat3ZBase N c)
        (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true
        (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)) = false from by
      rw [Function.update_of_ne hne]
      exact sat3ZBase_own N c t₁ j₁.val (by have := j₁.isLt; omega)]
    rw [Function.update_self]
    rw [show (!false) = true from rfl, show (!true) = false from rfl]
    rw [show Function.update (Function.update (sat3ZBase N c)
        (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true)
        (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)) true
      = Function.update (Function.update (sat3ZBase N c)
        (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)) true)
        (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true from
      Function.update_comm hne.symm _ _ _]
    rw [Function.update_idem]
    rw [show Function.update (Function.update (sat3ZBase N c)
        (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)) true)
        (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) false
      = Function.update (sat3ZBase N c)
        (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)) true from by
      rw [show (false : Bool) = Function.update (sat3ZBase N c)
          (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)) true
          (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) from by
        rw [Function.update_of_ne hne.symm]
        exact (sat3ZBase_own N c t₂ j₂.val (by have := j₂.isLt; omega)).symm]
      exact Function.update_eq_self _ _]
    exact sat3_zbase_flip_sat_t N hv c t₁ j₁
  · rw [Function.update_self, show (!true) = false from rfl, Function.update_idem]
    rw [show Function.update (sat3ZBase N c)
        (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) false
      = sat3ZBase N c from by
      rw [show (false : Bool) = sat3ZBase N c
          (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) from
        (sat3ZBase_own N c t₂ j₂.val (by have := j₂.isLt; omega)).symm]
      exact Function.update_eq_self _ _]
    exact sat3ZBase_unsat N c

/-- **CROSS-BLOCK BOTH ON, ANY SLOTS (proved)**: both designated blocks fire — satisfiable. -/
theorem sat3_zbase2_both_sat_t (N : ℕ) (hv : 1 ≤ sat3V N) (c₁ c₂ : Fin (sat3M N))
    (hc : c₁.val ≠ c₂.val) (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N)) :
    sat3Family N (Function.update (Function.update (sat3ZBase2 N c₁ c₂)
      (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) true)
      (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega)) true) = true := by
  apply decide_eq_true
  refine ⟨fun _ => true, sat3Eval_true_of_all N _ _ ?_⟩
  intro cl
  by_cases hcl1 : cl = c₁
  · subst hcl1
    refine ⟨t₁, sat3Lit_true_of_selected N _ _ cl t₁ j₁ ?_ ?_⟩
    · rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _ hc)]
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _ hc),
        Function.update_of_ne (sat3_sign_ne_sel_bit N cl t₁ t₁ j₁)]
      rw [sat3ZBase2_block_read N cl c₂ cl (Or.inl rfl) t₁ (sat3V N) (by omega)]
      rfl
  · by_cases hcl2 : cl = c₂
    · subst hcl2
      refine ⟨t₂, sat3Lit_true_of_selected N _ _ cl t₂ j₂ ?_ ?_⟩
      · exact Function.update_self _ _ _
      · rw [Function.update_of_ne (sat3_sign_ne_sel_bit N cl t₂ t₂ j₂),
          Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _
            (fun h => hc h.symm))]
        rw [sat3ZBase2_block_read N c₁ cl cl (Or.inr rfl) t₂ (sat3V N) (by omega)]
        rfl
    · exact sat3ZBase2_outside_satisfied N hv c₁ c₂ cl
        (fun h => hcl1 (Fin.ext h)) (fun h => hcl2 (Fin.ext h)) _
        (fun t' fI hfI => by
          rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _
              (fun h => hcl2 (Fin.ext h))),
            Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _
              (fun h => hcl1 (Fin.ext h)))])

/-- **CROSS-BLOCK ODD, ANY SLOTS (proved)**: corners `0, 0, 0, 1`. -/
theorem sat3_cross_block_odd_t (N : ℕ) (hv : 1 ≤ sat3V N) (c₁ c₂ : Fin (sat3M N))
    (hc : c₁.val ≠ c₂.val) (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N)) :
    xor (xor (sat3Family N (sat3ZBase2 N c₁ c₂))
        (sat3Family N (Function.update (sat3ZBase2 N c₁ c₂)
          (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega))
          (!(sat3ZBase2 N c₁ c₂ (sat3Bit N c₁ t₁ j₁.val
            (by have := j₁.isLt; omega)))))))
      (xor (sat3Family N (Function.update (sat3ZBase2 N c₁ c₂)
          (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega))
          (!(sat3ZBase2 N c₁ c₂ (sat3Bit N c₂ t₂ j₂.val
            (by have := j₂.isLt; omega))))))
        (sat3Family N (Function.update (Function.update (sat3ZBase2 N c₁ c₂)
          (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega))
          (!(sat3ZBase2 N c₁ c₂ (sat3Bit N c₁ t₁ j₁.val
            (by have := j₁.isLt; omega)))))
          (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega))
          (!(sat3ZBase2 N c₁ c₂ (sat3Bit N c₂ t₂ j₂.val
            (by have := j₂.isLt; omega))))))) = true := by
  rw [sat3ZBase2_block_read N c₁ c₂ c₁ (Or.inl rfl) t₁ j₁.val
      (by have := j₁.isLt; omega),
    sat3ZBase2_block_read N c₁ c₂ c₂ (Or.inr rfl) t₂ j₂.val
      (by have := j₂.isLt; omega)]
  rw [show (!false) = true from rfl]
  have h0 : sat3Family N (sat3ZBase2 N c₁ c₂) = false :=
    sat3_zbase2_kill N c₁ c₂ _ c₁ (Or.inl rfl)
      (fun t i => sat3ZBase2_block_read N c₁ c₂ c₁ (Or.inl rfl) t i.val
        (by have := i.isLt; omega))
  have h1 : sat3Family N (Function.update (sat3ZBase2 N c₁ c₂)
      (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) true) = false := by
    apply sat3_zbase2_kill N c₁ c₂ _ c₂ (Or.inr rfl)
    intro t i
    rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _
      (fun h => hc h.symm))]
    exact sat3ZBase2_block_read N c₁ c₂ c₂ (Or.inr rfl) t i.val
      (by have := i.isLt; omega)
  have h2 : sat3Family N (Function.update (sat3ZBase2 N c₁ c₂)
      (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega)) true) = false := by
    apply sat3_zbase2_kill N c₁ c₂ _ c₁ (Or.inl rfl)
    intro t i
    rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _ hc)]
    exact sat3ZBase2_block_read N c₁ c₂ c₁ (Or.inl rfl) t i.val
      (by have := i.isLt; omega)
  rw [h0, h1, h2, sat3_zbase2_both_sat_t N hv c₁ c₂ hc t₁ t₂ j₁ j₂]
  rfl

/-- **CROSS-BLOCK V0, ANY SLOTS (proved)**: unsat/unsat/sat with the `c₁` selector as the down flip. -/
theorem sat3_cross_block_V0_t (N : ℕ) (hv : 1 ≤ sat3V N) (c₁ c₂ : Fin (sat3M N))
    (hc : c₁.val ≠ c₂.val) (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N)) :
    sat3Family N (Function.update (sat3ZBase2 N c₁ c₂)
      (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) true) = false ∧
    sat3Family N (Function.update (Function.update
        (Function.update (sat3ZBase2 N c₁ c₂)
          (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) true)
        (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega))
        (!(Function.update (sat3ZBase2 N c₁ c₂)
          (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) true
          (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)))))
      (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega))
      (!(Function.update (sat3ZBase2 N c₁ c₂)
        (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) true
        (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega))))) = false ∧
    sat3Family N (Function.update
        (Function.update (sat3ZBase2 N c₁ c₂)
          (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) true)
      (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega))
      (!(Function.update (sat3ZBase2 N c₁ c₂)
        (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) true
        (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega))))) = true := by
  have hu0 : Function.update (sat3ZBase2 N c₁ c₂)
      (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) true
      (sat3Bit N c₂ t₂ j₂.val (by have := j₂.isLt; omega)) = false := by
    rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _ (fun h => hc h.symm))]
    exact sat3ZBase2_block_read N c₁ c₂ c₂ (Or.inr rfl) t₂ j₂.val
      (by have := j₂.isLt; omega)
  refine ⟨?_, ?_, ?_⟩
  · apply sat3_zbase2_kill N c₁ c₂ _ c₂ (Or.inr rfl)
    intro t i
    rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _
      (fun h => hc h.symm))]
    exact sat3ZBase2_block_read N c₁ c₂ c₂ (Or.inr rfl) t i.val
      (by have := i.isLt; omega)
  · rw [Function.update_self, show (!true) = false from rfl, Function.update_idem]
    rw [hu0, show (!false) = true from rfl]
    rw [show Function.update (sat3ZBase2 N c₁ c₂)
        (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) false
      = sat3ZBase2 N c₁ c₂ from by
      rw [show (false : Bool) = sat3ZBase2 N c₁ c₂
          (sat3Bit N c₁ t₁ j₁.val (by have := j₁.isLt; omega)) from
        (sat3ZBase2_block_read N c₁ c₂ c₁ (Or.inl rfl) t₁ j₁.val
          (by have := j₁.isLt; omega)).symm]
      exact Function.update_eq_self _ _]
    apply sat3_zbase2_kill N c₁ c₂ _ c₁ (Or.inl rfl)
    intro t i
    rw [Function.update_of_ne (sat3Bit_ne_of_clause N _ _ _ _ hc)]
    exact sat3ZBase2_block_read N c₁ c₂ c₁ (Or.inl rfl) t i.val
      (by have := i.isLt; omega)
  · rw [hu0, show (!false) = true from rfl]
    exact sat3_zbase2_both_sat_t N hv c₁ c₂ hc t₁ t₂ j₁ j₂

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_zbase_double_flip_t
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_same_block_odd_t
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_same_block_V1_t
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cross_block_odd_t
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cross_block_V0_t
