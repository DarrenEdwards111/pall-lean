import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATSquare

/-!
# N-Frame: SAT's boundary dimension is exactly 3 — the depth-1 square

The depth-0 square upgraded to survive one adversarial fixed bit `(w, a)`, giving `HyperplaneSquares (sat3Family N)`
and the headline `boundaryDim (sat3Family N) = 3`.

**Design** (as recorded): (1) the gadget clause is chosen off `w`'s clause (`m ≥ 2`); (2) the **global slot switch** —
one bit lives in one slot of one clause, so placing every filler literal in a slot class avoiding `w`'s slot makes all
live bits *and their signs* `w`-free uniformly (the sign-safety is per-site: filler signs by the slot argument, gadget
signs by the clause argument — the split that fixes the deferred draft's flaw); (3) stray `w`-effects land in empty
slots or dead bits, provably harmless.

  `sat3Bit_slot` — **PROVED**: the slot index of a layout bit.
  `sat3_hyperplaneSquares` — **PROVED**: an odd square for `sat3Family` inside every hyperplane.
  `boundaryDim_sat3_eq_three` — **PROVED, the headline**: the definite SAT family has boundary dimension exactly 3 —
        like majority, it cannot be computed at dimension ≤ 2 at any volume.

## Honest scope

Dimension-exactness is *calibration*, not hardness — majority also sits at dimension 3.  The SAT-hardness signal
remains the open blockwise disjoint-tear count (step 6) against the open volume-cost interface.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **The slot index of a layout bit (proved).** -/
theorem sat3Bit_slot (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    ((sat3Bit N c t f hf).val % sat3D N) / (sat3V N + 1) = t.val := by
  rw [sat3Bit_rem]
  rw [show t.val * (sat3V N + 1) + f = f + t.val * (sat3V N + 1) from by omega]
  rw [Nat.add_mul_div_right _ _ (by omega : 0 < sat3V N + 1), Nat.div_eq_of_lt hf]
  omega

/-- **The depth-1 square (proved)**: `sat3Family` has an odd square inside every hyperplane. -/
theorem sat3_hyperplaneSquares (N : ℕ) (hm : 2 ≤ sat3M N) (hv : 1 ≤ sat3V N) :
    HyperplaneSquares (sat3Family N) := by
  intro w a
  have hDpos : 0 < sat3D N := sat3D_pos N
  -- the gadget clause avoids w's clause
  set c₀ : Fin (sat3M N) := if w.val / sat3D N = 0 then ⟨1, hm⟩ else ⟨0, by omega⟩ with hc₀
  have hc₀w : w.val / sat3D N ≠ c₀.val := by
    rw [hc₀]
    split
    · next h =>
        rw [h]
        show (0 : ℕ) ≠ 1
        omega
    · next h => exact h
  -- the global slot switch: the filler slot avoids w's slot
  set sstar : Fin 3 :=
    if (w.val % sat3D N) / (sat3V N + 1) = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩ with hsstar
  have hsw : (w.val % sat3D N) / (sat3V N + 1) ≠ sstar.val := by
    rw [hsstar]
    split
    · next h =>
        rw [h]
        show (0 : ℕ) ≠ 1
        omega
    · next h => exact h
  set j₀ : Fin (sat3V N) := ⟨0, hv⟩ with hj₀
  set i₁ : Fin N := sat3Bit N c₀ ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega) with hi₁
  set i₂ : Fin N := sat3Bit N c₀ ⟨1, by omega⟩ j₀.val (by have := j₀.isLt; omega) with hi₂
  set z : Fin N → Bool := fun b =>
    if b = w then a
    else decide (b.val % sat3D N = sstar.val * (sat3V N + 1) ∧
      b.val / sat3D N ≠ c₀.val ∧ b.val / sat3D N < sat3M N) with hz
  -- clean layout facts for the flip bits
  have hj0v : j₀.val = 0 := rfl
  have hi₁rem : i₁.val % sat3D N = 0 := by
    rw [hi₁, sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + j₀.val = 0
    rw [hj0v]
    omega
  have hi₂rem : i₂.val % sat3D N = sat3V N + 1 := by
    rw [hi₂, sat3Bit_rem]
    show (1 : ℕ) * (sat3V N + 1) + j₀.val = sat3V N + 1
    rw [hj0v]
    omega
  -- w-freeness
  have hwg : ∀ (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1), sat3Bit N c₀ t f hf ≠ w := by
    intro t f hf hcontra
    exact hc₀w (by rw [← hcontra, sat3Bit_clause])
  have hw_slot : ∀ (c : Fin (sat3M N)) (f : ℕ) (hf : f < sat3V N + 1),
      sat3Bit N c sstar f hf ≠ w := by
    intro c f hf hcontra
    exact hsw (by rw [← hcontra, sat3Bit_slot])
  -- base evaluations
  have hz_gadget : ∀ (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1),
      z (sat3Bit N c₀ t f hf) = false := by
    intro t f hf
    show (if sat3Bit N c₀ t f hf = w then a else decide _) = false
    rw [if_neg (hwg t f hf)]
    simp only [decide_eq_false_iff_not]
    rintro ⟨-, hdiv, -⟩
    exact hdiv (sat3Bit_clause N c₀ t f hf)
  have hz_live : ∀ c : Fin (sat3M N), c ≠ c₀ →
      z (sat3Bit N c sstar j₀.val (by have := j₀.isLt; omega)) = true := by
    intro c hc
    show (if sat3Bit N c sstar j₀.val _ = w then a else decide _) = true
    rw [if_neg (hw_slot c j₀.val (by have := j₀.isLt; omega))]
    simp only [decide_eq_true_eq]
    refine ⟨by rw [sat3Bit_rem, hj0v]; omega, ?_, ?_⟩
    · rw [sat3Bit_clause]
      exact fun h => hc (Fin.ext h)
    · rw [sat3Bit_clause]
      exact c.isLt
  -- filler signs are false (slot argument — the per-site split)
  have hz_sign_filler : ∀ c : Fin (sat3M N),
      z (sat3Bit N c sstar (sat3V N) (by omega)) = false := by
    intro c
    show (if sat3Bit N c sstar (sat3V N) _ = w then a else decide _) = false
    rw [if_neg (hw_slot c (sat3V N) (by omega))]
    simp only [decide_eq_false_iff_not]
    rintro ⟨hmod, -, -⟩
    rw [sat3Bit_rem] at hmod
    have := hv
    omega
  -- stability: corner updates never touch filler bits or gadget signs
  have hstab_filler_sel : ∀ c : Fin (sat3M N), c ≠ c₀ →
      sat3Bit N c sstar j₀.val (by have := j₀.isLt; omega) ≠ i₁ ∧
      sat3Bit N c sstar j₀.val (by have := j₀.isLt; omega) ≠ i₂ := by
    intro c hc
    constructor
    · intro hcontra
      apply hc
      apply Fin.ext
      rw [← sat3Bit_clause N c sstar j₀.val (by have := j₀.isLt; omega),
        ← sat3Bit_clause N c₀ ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega)]
      rw [hi₁] at hcontra
      rw [hcontra]
    · intro hcontra
      apply hc
      apply Fin.ext
      rw [← sat3Bit_clause N c sstar j₀.val (by have := j₀.isLt; omega),
        ← sat3Bit_clause N c₀ ⟨1, by omega⟩ j₀.val (by have := j₀.isLt; omega)]
      rw [hi₂] at hcontra
      rw [hcontra]
  have hstab_filler_sign : ∀ c : Fin (sat3M N),
      sat3Bit N c sstar (sat3V N) (by omega) ≠ i₁ ∧
      sat3Bit N c sstar (sat3V N) (by omega) ≠ i₂ := by
    intro c
    have hcase : sstar.val * (sat3V N + 1) = 0 ∨
        sat3V N + 1 ≤ sstar.val * (sat3V N + 1) := by
      cases Nat.eq_zero_or_pos sstar.val with
      | inl h => left; rw [h, Nat.zero_mul]
      | inr h => right; exact Nat.le_mul_of_pos_left _ h
    constructor
    · intro hcontra
      have h2 : (sat3Bit N c sstar (sat3V N) (by omega)).val % sat3D N = 0 := by
        rw [hcontra]
        exact hi₁rem
      rw [sat3Bit_rem] at h2
      omega
    · intro hcontra
      have h2 : (sat3Bit N c sstar (sat3V N) (by omega)).val % sat3D N = sat3V N + 1 := by
        rw [hcontra]
        exact hi₂rem
      rw [sat3Bit_rem] at h2
      omega
  have hstab_gadget_sign : ∀ t : Fin 3,
      sat3Bit N c₀ t (sat3V N) (by omega) ≠ i₁ ∧
      sat3Bit N c₀ t (sat3V N) (by omega) ≠ i₂ := by
    intro t
    have hcase : t.val * (sat3V N + 1) = 0 ∨ sat3V N + 1 ≤ t.val * (sat3V N + 1) := by
      cases Nat.eq_zero_or_pos t.val with
      | inl h => left; rw [h, Nat.zero_mul]
      | inr h => right; exact Nat.le_mul_of_pos_left _ h
    constructor
    · intro hcontra
      have h2 : (sat3Bit N c₀ t (sat3V N) (by omega)).val % sat3D N = 0 := by
        rw [hcontra]
        exact hi₁rem
      rw [sat3Bit_rem] at h2
      omega
    · intro hcontra
      have h2 : (sat3Bit N c₀ t (sat3V N) (by omega)).val % sat3D N = sat3V N + 1 := by
        rw [hcontra]
        exact hi₂rem
      rw [sat3Bit_rem] at h2
      omega
  -- filler clauses are satisfied by all-true at every corner
  have hsat_others : ∀ (x' : Fin N → Bool),
      (∀ b : Fin N, b ≠ i₁ → b ≠ i₂ → x' b = z b) →
      ∀ c : Fin (sat3M N), c ≠ c₀ →
        sat3Lit N x' (fun _ => true) c sstar = true := by
    intro x' hx' c hc
    obtain ⟨hs1, hs2⟩ := hstab_filler_sel c hc
    obtain ⟨hg1, hg2⟩ := hstab_filler_sign c
    apply sat3Lit_true_of_selected N x' _ c sstar j₀
    · rw [hx' _ hs1 hs2]
      exact hz_live c hc
    · rw [hx' _ hg1 hg2, hz_sign_filler c]
      rfl
  -- the base is unsatisfiable
  have hbase : sat3Family N z = false := by
    apply sat3Family_false_of_empty_clause N z c₀
    intro t i
    exact hz_gadget t i.val (by have := i.isLt; omega)
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
      obtain ⟨hg1, hg2⟩ := hstab_gadget_sign t
      refine ⟨t, sat3Lit_true_of_selected N x' _ c₀ t j₀ hgad ?_⟩
      rw [hx' _ hg1 hg2, hz_gadget t (sat3V N) (by omega)]
      rfl
    · exact ⟨sstar, hsat_others x' hx' c hc⟩
  -- assemble
  refine ⟨z, i₁, i₂, ?_, ?_, ?_, ?_, ?_⟩
  · -- i₁ ≠ i₂
    apply Fin.ne_of_val_ne
    show c₀.val * sat3D N + (0 : ℕ) * (sat3V N + 1) + 0
        ≠ c₀.val * sat3D N + 1 * (sat3V N + 1) + 0
    omega
  · exact fun hc => hwg ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega) (hi₁ ▸ hc)
  · exact fun hc => hwg ⟨1, by omega⟩ j₀.val (by have := j₀.isLt; omega) (hi₂ ▸ hc)
  · -- z w = a
    show (if w = w then a else _) = a
    rw [if_pos rfl]
  · -- the odd square values (0, 1, 1, 1)
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
      have hne12 : i₁ ≠ i₂ := by
        apply Fin.ne_of_val_ne
        show c₀.val * sat3D N + (0 : ℕ) * (sat3V N + 1) + 0
            ≠ c₀.val * sat3D N + 1 * (sat3V N + 1) + 0
        omega
      rw [Function.update_of_ne hne12, Function.update_self]
    rw [e00, e10, e01, e11]
    rfl

/-- **THE HEADLINE (proved)**: the definite SAT family has boundary dimension **exactly 3** — like majority, it cannot
be computed at dimension ≤ 2 at any volume. -/
theorem boundaryDim_sat3_eq_three (N : ℕ) (hm : 2 ≤ sat3M N) (hv : 1 ≤ sat3V N) :
    boundaryDim (sat3Family N) = 3 := by
  have hN : 0 < N := by
    by_contra h
    push_neg at h
    interval_cases N
    revert hm
    decide
  exact boundaryDim_eq_three_of_hyperplaneSquares hN (sat3Family N)
    (sat3_hyperplaneSquares N hm hv)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_hyperplaneSquares
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.boundaryDim_sat3_eq_three
