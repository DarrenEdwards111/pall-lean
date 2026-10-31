import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDimThreeCost

/-!
# N-Frame: SAT-side tearing — the anchor lemmas, and the honest calibration finding

Applying the tested tearing invariant to `sat3Family` produced a **calibration finding before any construction**:

> **The scalar depth ceiling.**  Zeroing the `3v` selector bits of a single clause makes the encoded instance
> unsatisfiable on the entire remaining subcube — `sat3Family` is constant `0` there, and no odd square survives.  So
> `Robust`-depth of SAT caps at `≈ 3√N`, *below* majority's `~N/2`.  As a **scalar**, tearing depth rates SAT easier
> than majority.  The SAT-hardness signal is therefore necessarily the **structured blockwise count** (many *disjoint*
> clause-gadget tears — the Nečiporuk shape of mountain step 6), not scalar depth.  The invariant survives calibration
> by redirecting the attack, exactly what the step-5 discipline is for.

This file proves the anchor lemmas every SAT-side square construction rests on:

  `sat3Lit_false_of_empty` / `sat3Family_false_of_empty_clause` — **PROVED, the 0-corner mechanism**: a clause with
        all-zero selectors is empty, and an empty clause makes the whole instance unsatisfiable — regardless of every
        other bit.
  `sat3Lit_single` — **PROVED, the flip mechanism**: a slot with exactly one live selector evaluates to that literal
        `a_j ⊕ sign` — flipping one selector bit turns an empty slot into a genuine literal.

Together these are the two corners of the SAT odd square: the empty-clause corner (unsatisfiable) and the
single-selector corners (satisfiable by choosing the witness).  The square assembly (depth 0), its depth-1 adversarial
version (⇒ `boundaryDim (sat3Family N) = 3`), and the blockwise disjoint-tear count over the `m ≈ √N/3` clause blocks
are the named next constructions — with the scalar ceiling above as the standing honest constraint on what any of them
can claim.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The 0-corner mechanism: empty clauses kill satisfiability -/

/-- **An all-zero-selector slot is an empty literal (proved)**: it evaluates false under every assignment. -/
theorem sat3Lit_false_of_empty (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (c : Fin (sat3M N)) (t : Fin 3)
    (hsel : ∀ i : Fin (sat3V N), x (sat3Bit N c t i.val (by have := i.isLt; omega)) = false) :
    sat3Lit N x a c t = false := by
  unfold sat3Lit
  apply List.any_eq_false.mpr
  intro i _
  rw [hsel i]
  simp

/-- **An empty clause is unsatisfiable (proved)**: the instance evaluates false under every assignment. -/
theorem sat3Eval_false_of_empty_clause (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (c : Fin (sat3M N))
    (hsel : ∀ (t : Fin 3) (i : Fin (sat3V N)),
      x (sat3Bit N c t i.val (by have := i.isLt; omega)) = false) :
    sat3Eval N x a = false := by
  cases hs : sat3Eval N x a
  · rfl
  · exfalso
    have hall := List.all_eq_true.mp hs c (List.mem_finRange c)
    obtain ⟨t, -, hlit⟩ := List.any_eq_true.mp hall
    rw [sat3Lit_false_of_empty N x a c t (hsel t)] at hlit
    exact Bool.noConfusion hlit

/-- **The 0-corner (proved)**: one empty clause forces `sat3Family = false` — regardless of every other bit of the
encoding. -/
theorem sat3Family_false_of_empty_clause (N : ℕ) (x : Fin N → Bool) (c : Fin (sat3M N))
    (hsel : ∀ (t : Fin 3) (i : Fin (sat3V N)),
      x (sat3Bit N c t i.val (by have := i.isLt; omega)) = false) :
    sat3Family N x = false := by
  apply decide_eq_false
  rintro ⟨a, ha⟩
  rw [sat3Eval_false_of_empty_clause N x a c hsel] at ha
  exact Bool.noConfusion ha

/-! ### The flip mechanism: a single live selector is a genuine literal -/

/-- **The single-selector evaluation (proved)**: a slot whose only live selector is variable `j` evaluates to the
literal `a j ⊕ sign` — the mechanism by which one flipped bit turns an empty slot into a live literal. -/
theorem sat3Lit_single (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (c : Fin (sat3M N)) (t : Fin 3) (j : Fin (sat3V N))
    (hj : x (sat3Bit N c t j.val (by have := j.isLt; omega)) = true)
    (hothers : ∀ i : Fin (sat3V N), i ≠ j →
      x (sat3Bit N c t i.val (by have := i.isLt; omega)) = false) :
    sat3Lit N x a c t = xor (a j) (x (sat3Bit N c t (sat3V N) (by omega))) := by
  unfold sat3Lit
  cases hval : xor (a j) (x (sat3Bit N c t (sat3V N) (by omega)))
  · apply List.any_eq_false.mpr
    intro i _
    by_cases hij : i = j
    · subst hij
      rw [hj, hval]
      simp
    · rw [hothers i hij]
      simp
  · apply List.any_eq_true.mpr
    refine ⟨j, List.mem_finRange j, ?_⟩
    rw [hj, hval]
    simp

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Family_false_of_empty_clause
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Lit_single
