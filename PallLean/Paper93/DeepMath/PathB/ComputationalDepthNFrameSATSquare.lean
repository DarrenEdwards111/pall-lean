import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATTearing

/-!
# N-Frame: the SAT odd square — depth-0 assembly

The anchors gave the two mechanisms; this file assembles them into the first SAT-side tearing witness: an explicit odd
square for `sat3Family`.

**The construction.**  Base `z`: the gadget clause `0` is empty (all selectors zero — unsatisfiable, the 0-corner);
every other clause has one live positive literal `x₀` (selector of variable 0 in slot 0, sign 0 — satisfied by the
all-true assignment).  The two flipped bits are the variable-0 selectors of the gadget's slots 0 and 1: each flip gives
the gadget a live positive literal, making the whole instance satisfiable by all-true.  Corner pattern `(0,1,1,1)` —
odd.

  `sat3Bit_clause` — **PROVED**: the clause index of a layout bit (the cross-clause disjointness arithmetic).
  `sat3Lit_true_of_selected` / `sat3Eval_true_of_all` — **PROVED**: the satisfaction mechanisms.
  `sat3_oddSquare` — **PROVED, the witness**: an explicit odd square for `sat3Family` (`m ≥ 1`, `v ≥ 1`).

## Honest scope

Depth 0 — no adversarial fixing.  The depth-1 version (one fixed bit, case-patched gadget/filler choices — the recorded
plan) yields `boundaryDim (sat3Family N) = 3` and is the named next step; the blockwise disjoint-tear count over the
`m ≈ √N/3` clause blocks (mountain step 6) is the bridge after that, under the standing scalar-ceiling constraint.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Layout arithmetic -/

theorem sat3D_pos (N : ℕ) : 0 < sat3D N := by
  unfold sat3D
  omega

theorem sat3Bit_val (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    (sat3Bit N c t f hf).val = c.val * sat3D N + t.val * (sat3V N + 1) + f := rfl

/-- **The clause index of a layout bit (proved)** — cross-clause disjointness. -/
theorem sat3Bit_clause (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    (sat3Bit N c t f hf).val / sat3D N = c.val := by
  rw [sat3Bit_val]
  have hin : t.val * (sat3V N + 1) + f < sat3D N := by
    have ht := t.isLt
    have h2 : t.val * (sat3V N + 1) ≤ 2 * (sat3V N + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    show t.val * (sat3V N + 1) + f < 3 * (sat3V N + 1)
    omega
  rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (sat3D_pos N),
    Nat.div_eq_of_lt hin]
  omega

/-- **The in-clause remainder of a layout bit (proved).** -/
theorem sat3Bit_rem (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    (sat3Bit N c t f hf).val % sat3D N = t.val * (sat3V N + 1) + f := by
  rw [sat3Bit_val]
  have hin : t.val * (sat3V N + 1) + f < sat3D N := by
    have ht := t.isLt
    have h2 : t.val * (sat3V N + 1) ≤ 2 * (sat3V N + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    show _ < 3 * (sat3V N + 1)
    omega
  rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin]

/-! ### Satisfaction mechanisms -/

/-- **A selected live literal makes the slot true (proved).** -/
theorem sat3Lit_true_of_selected (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (c : Fin (sat3M N)) (t : Fin 3) (j : Fin (sat3V N))
    (hsel : x (sat3Bit N c t j.val (by have := j.isLt; omega)) = true)
    (hlit : xor (a j) (x (sat3Bit N c t (sat3V N) (by omega))) = true) :
    sat3Lit N x a c t = true := by
  unfold sat3Lit
  apply List.any_eq_true.mpr
  refine ⟨j, List.mem_finRange j, ?_⟩
  rw [hsel, hlit]
  simp

/-- **Clause-wise satisfaction (proved).** -/
theorem sat3Eval_true_of_all (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (h : ∀ c : Fin (sat3M N), ∃ t : Fin 3, sat3Lit N x a c t = true) :
    sat3Eval N x a = true := by
  apply List.all_eq_true.mpr
  intro c _
  obtain ⟨t, ht⟩ := h c
  exact List.any_eq_true.mpr ⟨t, List.mem_finRange t, ht⟩

/-! ### The square -/

/-- **The SAT odd square (proved)**: an explicit tearing witness for `sat3Family` — empty gadget clause at the base
(unsatisfiable), one selector flip in either gadget slot restores a live positive literal (satisfiable by all-true);
corner pattern `(0,1,1,1)`. -/
theorem sat3_oddSquare (N : ℕ) (hm : 1 ≤ sat3M N) (hv : 1 ≤ sat3V N) :
    ∃ (z : Fin N → Bool) (i₁ i₂ : Fin N), OddSquare (sat3Family N) z i₁ i₂ := by
  set c₀ : Fin (sat3M N) := ⟨0, hm⟩ with hc₀
  set j₀ : Fin (sat3V N) := ⟨0, hv⟩ with hj₀
  -- the two gadget selector bits
  set i₁ : Fin N := sat3Bit N c₀ ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega) with hi₁
  set i₂ : Fin N := sat3Bit N c₀ ⟨1, by omega⟩ j₀.val (by have := j₀.isLt; omega) with hi₂
  -- the base: one live positive literal in every non-gadget clause
  set z : Fin N → Bool := fun b =>
    decide (b.val % sat3D N = 0 ∧ b.val / sat3D N ≠ 0 ∧ b.val / sat3D N < sat3M N) with hz
  have hne : i₁ ≠ i₂ := by
    apply Fin.ne_of_val_ne
    show (0 : ℕ) * sat3D N + 0 * (sat3V N + 1) + 0
        ≠ 0 * sat3D N + 1 * (sat3V N + 1) + 0
    omega
  -- gadget bits are false at the base (clause index 0)
  have hzero_gadget : ∀ (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1),
      z (sat3Bit N c₀ t f hf) = false := by
    intro t f hf
    rw [hz]
    simp only [decide_eq_false_iff_not]
    rintro ⟨-, hdiv, -⟩
    rw [sat3Bit_clause, hc₀] at hdiv
    exact hdiv rfl
  -- non-gadget slot-0 variable-0 selectors are true at the base
  have hlive : ∀ c : Fin (sat3M N), c ≠ c₀ →
      z (sat3Bit N c ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega)) = true := by
    intro c hc
    rw [hz]
    simp only [decide_eq_true_eq]
    have hcval : c.val ≠ 0 := by
      intro h0
      exact hc (Fin.ext (by rw [h0, hc₀]))
    refine ⟨?_, ?_, ?_⟩
    · rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + 0 = 0
      omega
    · rw [sat3Bit_clause]
      exact hcval
    · rw [sat3Bit_clause]
      exact c.isLt
  -- signs are everywhere false at the base (field v ≠ 0 mod-position)
  have hsigns : ∀ (c : Fin (sat3M N)) (t : Fin 3) (x' : Fin N → Bool),
      (∀ b : Fin N, b ≠ i₁ → b ≠ i₂ → x' b = z b) →
      x' (sat3Bit N c t (sat3V N) (by omega)) = false := by
    intro c t x' hx'
    have htv : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 := by have := t.isLt; omega
    have hDval : sat3D N = 3 * (sat3V N + 1) := rfl
    have hcase : ∀ target : ℕ, target < sat3D N →
        (∀ r : ℕ, r = t.val * (sat3V N + 1) + sat3V N → r ≠ target) →
        (sat3Bit N c t (sat3V N) (by omega)).val ≠ target
          ∨ c.val = 0 ∧ t.val * (sat3V N + 1) + sat3V N = target := by
      intro target htarget hr
      exact Or.inl (fun hcontra => hr _ rfl (by
        rw [← sat3Bit_rem N c t (sat3V N) (by omega), hcontra,
          Nat.mod_eq_of_lt htarget]))
    have hne1 : sat3Bit N c t (sat3V N) (by omega) ≠ i₁ := by
      apply Fin.ne_of_val_ne
      show (sat3Bit N c t (sat3V N) (by omega)).val
          ≠ (0 : ℕ) * sat3D N + 0 * (sat3V N + 1) + 0
      intro hcontra
      have hrem := sat3Bit_rem N c t (sat3V N) (by omega)
      rw [hcontra] at hrem
      have hvpos := hv
      rcases htv with h | h | h <;> rw [h] at hrem <;>
        simp only [Nat.zero_mul, Nat.zero_add, Nat.zero_mod] at hrem <;> omega
    have hne2 : sat3Bit N c t (sat3V N) (by omega) ≠ i₂ := by
      apply Fin.ne_of_val_ne
      show (sat3Bit N c t (sat3V N) (by omega)).val
          ≠ (0 : ℕ) * sat3D N + 1 * (sat3V N + 1) + 0
      intro hcontra
      have hrem := sat3Bit_rem N c t (sat3V N) (by omega)
      rw [hcontra] at hrem
      have hvpos := hv
      have hlt : (0 : ℕ) * sat3D N + 1 * (sat3V N + 1) + 0 < sat3D N := by
        rw [hDval]
        omega
      rw [Nat.mod_eq_of_lt (by omega)] at hrem
      rcases htv with h | h | h <;> rw [h] at hrem <;> omega
    rw [hx' _ hne1 hne2, hz]
    simp only [decide_eq_false_iff_not]
    rintro ⟨hmod, -, -⟩
    rw [show (sat3Bit N c t (sat3V N) (by omega)).val
        = c.val * sat3D N + (t.val * (sat3V N + 1) + sat3V N) from by rw [sat3Bit_val]; omega]
      at hmod
    have hin : t.val * (sat3V N + 1) + sat3V N < sat3D N := by
      have ht := t.isLt
      have h2 : t.val * (sat3V N + 1) ≤ 2 * (sat3V N + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      show _ < 3 * (sat3V N + 1)
      omega
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hin] at hmod
    have := hv
    omega
  -- non-gadget clauses are satisfied by all-true at every corner
  have hsat_others : ∀ (x' : Fin N → Bool),
      (∀ b : Fin N, b ≠ i₁ → b ≠ i₂ → x' b = z b) →
      ∀ c : Fin (sat3M N), c ≠ c₀ →
        sat3Lit N x' (fun _ => true) c ⟨0, by omega⟩ = true := by
    intro x' hx' c hc
    apply sat3Lit_true_of_selected N x' _ c _ j₀
    · -- the live selector survives (it is neither flipped bit: different clause)
      have hcval : c.val ≠ 0 := fun h0 => hc (Fin.ext (by rw [h0, hc₀]))
      have hne1 : sat3Bit N c ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega) ≠ i₁ := by
        apply Fin.ne_of_val_ne
        show c.val * sat3D N + (0 : ℕ) * (sat3V N + 1) + 0
            ≠ (0 : ℕ) * sat3D N + 0 * (sat3V N + 1) + 0
        have hD := sat3D_pos N
        intro hcontra
        have : c.val * sat3D N = 0 := by omega
        rcases Nat.mul_eq_zero.mp this with h | h
        · exact hcval h
        · omega
      have hne2 : sat3Bit N c ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega) ≠ i₂ := by
        apply Fin.ne_of_val_ne
        show c.val * sat3D N + (0 : ℕ) * (sat3V N + 1) + 0
            ≠ (0 : ℕ) * sat3D N + 1 * (sat3V N + 1) + 0
        have hDval : sat3D N = 3 * (sat3V N + 1) := rfl
        have hcpos : 1 ≤ c.val := by omega
        have hgeD : sat3D N ≤ c.val * sat3D N := Nat.le_mul_of_pos_left _ hcpos
        intro hcontra
        simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.add_zero] at hcontra
        rw [hcontra] at hgeD
        rw [hDval] at hgeD
        omega
      rw [hx' _ hne1 hne2]
      exact hlive c hc
    · rw [hsigns c _ x' hx']
      rfl
  -- the base is unsatisfiable
  have hbase : sat3Family N z = false := by
    apply sat3Family_false_of_empty_clause N z c₀
    intro t i
    exact hzero_gadget t i.val (by have := i.isLt; omega)
  -- a corner with a live gadget slot is satisfiable by all-true
  have hcorner : ∀ (x' : Fin N → Bool) (t : Fin 3),
      (∀ b : Fin N, b ≠ i₁ → b ≠ i₂ → x' b = z b) →
      x' (sat3Bit N c₀ t j₀.val (by have := j₀.isLt; omega)) = true →
      sat3Family N x' = true := by
    intro x' t hx' hgad
    apply decide_eq_true
    refine ⟨fun _ => true, sat3Eval_true_of_all N x' _ ?_⟩
    intro c
    by_cases hc : c = c₀
    · subst hc
      refine ⟨t, sat3Lit_true_of_selected N x' _ c₀ t j₀ hgad ?_⟩
      rw [hsigns c₀ t x' hx']
      rfl
    · exact ⟨⟨0, by omega⟩, hsat_others x' hx' c hc⟩
  -- assemble the four corners
  refine ⟨z, i₁, i₂, hne, ?_⟩
  have e00 : sat3Family N z = false := hbase
  have e10 : sat3Family N (Function.update z i₁ true) = true := by
    refine hcorner _ ⟨0, by omega⟩ (fun b hb1 hb2 => Function.update_of_ne hb1 true z) ?_
    rw [Function.update_self]
  have e01 : sat3Family N (Function.update z i₂ true) = true := by
    refine hcorner _ ⟨1, by omega⟩ (fun b hb1 hb2 => Function.update_of_ne hb2 true z) ?_
    rw [Function.update_self]
  have e11 : sat3Family N (Function.update (Function.update z i₁ true) i₂ true) = true := by
    refine hcorner _ ⟨0, by omega⟩ (fun b hb1 hb2 => by
      rw [Function.update_of_ne hb2, Function.update_of_ne hb1]) ?_
    rw [Function.update_of_ne hne, Function.update_self]
  rw [e00, e10, e01, e11]
  rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Bit_clause
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_oddSquare
