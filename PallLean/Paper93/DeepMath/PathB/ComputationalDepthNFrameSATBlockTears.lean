import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATSquare

/-!
# N-Frame: the blockwise disjoint-tear count for SAT — mountain step 6, the counting substrate

The scalar-depth calibration finding said SAT's hardness signal cannot be tearing *depth* (ceiling `≈ 3√N`, below
majority).  This file builds the structured replacement: **one tear per clause block, all blocks simultaneously**.

  `sat3_blockTear` — **PROVED, the per-block tear**: for *every* clause index `c`, there is an odd square whose two
        flip bits both live inside clause `c`'s own `D`-bit block (`div = c`).  The depth-0 gadget mechanism localizes
        to an arbitrary block: base = live slot-0 selectors everywhere except clause `c`, which is empty.
  `sat3_disjoint_tear_count` — **PROVED, the count**: a constructive family of `sat3M N ≈ √N/3` tears, flips labelled
        by their blocks, all flip bits pairwise distinct across blocks.
  `sat3_tear_support_card` — **PROVED, the quantitative form**: the tear family's support has *exactly* `2 · sat3M N`
        bits — `m` disjoint 2-bit tear sites aligned to the clause-block partition of the layout.

## Honest scope — what the count is and is not

The raw disjoint-tear *count* does not by itself distinguish SAT from easy functions: majority admits `~n/2` disjoint
tears (any coordinate pair over a threshold base), *more* than SAT's `√N/3`.  What is SAT-specific here is the
**block alignment**: the tears sit one-per-block in the layout's clause partition — exactly the shape a
Nečiporuk-style argument sums over.  The genuinely discriminating quantity — the number of distinct *subfunctions*
per block as the outside context varies, and the cost interface (volume `V` at dimension 3 ⇒ at most `g(V)` serviced
blocks) — remains **open** and is *not* claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **The per-block tear (proved)**: every clause block carries an odd square whose flips live in that block. -/
theorem sat3_blockTear (N : ℕ) (hv : 1 ≤ sat3V N) (c₀ : Fin (sat3M N)) :
    ∃ (z : Fin N → Bool) (i₁ i₂ : Fin N),
      i₁.val / sat3D N = c₀.val ∧ i₂.val / sat3D N = c₀.val ∧
      OddSquare (sat3Family N) z i₁ i₂ := by
  have hDpos : 0 < sat3D N := sat3D_pos N
  set j₀ : Fin (sat3V N) := ⟨0, hv⟩ with hj₀
  set i₁ : Fin N := sat3Bit N c₀ ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega) with hi₁
  set i₂ : Fin N := sat3Bit N c₀ ⟨1, by omega⟩ j₀.val (by have := j₀.isLt; omega) with hi₂
  set z : Fin N → Bool := fun b =>
    decide (b.val % sat3D N = 0 ∧ b.val / sat3D N ≠ c₀.val ∧ b.val / sat3D N < sat3M N)
    with hz
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
  -- base evaluations
  have hz_gadget : ∀ (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1),
      z (sat3Bit N c₀ t f hf) = false := by
    intro t f hf
    show decide _ = false
    simp only [decide_eq_false_iff_not]
    rintro ⟨-, hdiv, -⟩
    exact hdiv (sat3Bit_clause N c₀ t f hf)
  have hz_live : ∀ c : Fin (sat3M N), c ≠ c₀ →
      z (sat3Bit N c ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega)) = true := by
    intro c hc
    show decide _ = true
    simp only [decide_eq_true_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + j₀.val = 0
      rw [hj0v]
      omega
    · rw [sat3Bit_clause]
      exact fun h => hc (Fin.ext h)
    · rw [sat3Bit_clause]
      exact c.isLt
  have hz_sign : ∀ (c : Fin (sat3M N)) (t : Fin 3),
      z (sat3Bit N c t (sat3V N) (by omega)) = false := by
    intro c t
    show decide _ = false
    simp only [decide_eq_false_iff_not]
    rintro ⟨hmod, -, -⟩
    rw [sat3Bit_rem] at hmod
    omega
  -- stability: corner updates never touch filler selectors or any sign bit
  have hstab_sel : ∀ c : Fin (sat3M N), c ≠ c₀ →
      sat3Bit N c ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega) ≠ i₁ ∧
      sat3Bit N c ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega) ≠ i₂ := by
    intro c hc
    constructor
    · intro hcontra
      apply hc
      apply Fin.ext
      rw [← sat3Bit_clause N c ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega),
        ← sat3Bit_clause N c₀ ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega)]
      rw [hi₁] at hcontra
      rw [hcontra]
    · intro hcontra
      apply hc
      apply Fin.ext
      rw [← sat3Bit_clause N c ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega),
        ← sat3Bit_clause N c₀ ⟨1, by omega⟩ j₀.val (by have := j₀.isLt; omega)]
      rw [hi₂] at hcontra
      rw [hcontra]
  have hstab_sign : ∀ (c : Fin (sat3M N)) (t : Fin 3),
      sat3Bit N c t (sat3V N) (by omega) ≠ i₁ ∧
      sat3Bit N c t (sat3V N) (by omega) ≠ i₂ := by
    intro c t
    have hcase : t.val * (sat3V N + 1) = 0 ∨ sat3V N + 1 ≤ t.val * (sat3V N + 1) := by
      cases Nat.eq_zero_or_pos t.val with
      | inl h => left; rw [h, Nat.zero_mul]
      | inr h => right; exact Nat.le_mul_of_pos_left _ h
    constructor
    · intro hcontra
      have h2 : (sat3Bit N c t (sat3V N) (by omega)).val % sat3D N = 0 := by
        rw [hcontra]
        exact hi₁rem
      rw [sat3Bit_rem] at h2
      omega
    · intro hcontra
      have h2 : (sat3Bit N c t (sat3V N) (by omega)).val % sat3D N = sat3V N + 1 := by
        rw [hcontra]
        exact hi₂rem
      rw [sat3Bit_rem] at h2
      omega
  -- filler clauses are satisfied by all-true at every corner
  have hsat_others : ∀ (x' : Fin N → Bool),
      (∀ b : Fin N, b ≠ i₁ → b ≠ i₂ → x' b = z b) →
      ∀ c : Fin (sat3M N), c ≠ c₀ →
        sat3Lit N x' (fun _ => true) c ⟨0, by omega⟩ = true := by
    intro x' hx' c hc
    obtain ⟨hs1, hs2⟩ := hstab_sel c hc
    obtain ⟨hg1, hg2⟩ := hstab_sign c ⟨0, by omega⟩
    apply sat3Lit_true_of_selected N x' _ c ⟨0, by omega⟩ j₀
    · rw [hx' _ hs1 hs2]
      exact hz_live c hc
    · rw [hx' _ hg1 hg2, hz_sign c ⟨0, by omega⟩]
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
      obtain ⟨hg1, hg2⟩ := hstab_sign c t
      refine ⟨t, sat3Lit_true_of_selected N x' _ c t j₀ hgad ?_⟩
      rw [hx' _ hg1 hg2, hz_sign c t]
      rfl
    · exact ⟨⟨0, by omega⟩, hsat_others x' hx' c hc⟩
  -- assemble
  have hne12 : i₁ ≠ i₂ := by
    intro hcc
    have h := hi₁rem
    rw [hcc, hi₂rem] at h
    omega
  refine ⟨z, i₁, i₂, ?_, ?_, hne12, ?_⟩
  · rw [hi₁]
    exact sat3Bit_clause N c₀ ⟨0, by omega⟩ j₀.val (by have := j₀.isLt; omega)
  · rw [hi₂]
    exact sat3Bit_clause N c₀ ⟨1, by omega⟩ j₀.val (by have := j₀.isLt; omega)
  · have e00 : sat3Family N z = false := hbase
    have e10 : sat3Family N (Function.update z i₁ true) = true := by
      refine hcorner _ ⟨0, by omega⟩ (fun b hb1 hb2 => Function.update_of_ne hb1 true z) ?_
      rw [Function.update_self]
    have e01 : sat3Family N (Function.update z i₂ true) = true := by
      refine hcorner _ ⟨1, by omega⟩ (fun b hb1 hb2 => Function.update_of_ne hb2 true z) ?_
      rw [Function.update_self]
    have e11 : sat3Family N (Function.update (Function.update z i₁ true) i₂ true) = true := by
      refine hcorner _ ⟨0, by omega⟩ (fun b hb1 hb2 => by
        rw [Function.update_of_ne hb2, Function.update_of_ne hb1]) ?_
      rw [Function.update_of_ne hne12, Function.update_self]
    rw [e00, e10, e01, e11]
    rfl

/-- **The blockwise disjoint-tear count (proved)**: a constructive family of `sat3M N` odd squares, one per clause
block, whose flip bits are labelled by their blocks and pairwise distinct across blocks. -/
theorem sat3_disjoint_tear_count (N : ℕ) (hv : 1 ≤ sat3V N) :
    ∃ T : Fin (sat3M N) → (Fin N → Bool) × Fin N × Fin N,
      (∀ c, OddSquare (sat3Family N) (T c).1 (T c).2.1 (T c).2.2) ∧
      (∀ c, (T c).2.1.val / sat3D N = c.val ∧ (T c).2.2.val / sat3D N = c.val) ∧
      (∀ c c', c ≠ c' →
        (T c).2.1 ≠ (T c').2.1 ∧ (T c).2.1 ≠ (T c').2.2 ∧
        (T c).2.2 ≠ (T c').2.1 ∧ (T c).2.2 ≠ (T c').2.2) := by
  choose z i₁ i₂ hd1 hd2 hsq using sat3_blockTear N hv
  refine ⟨fun c => (z c, i₁ c, i₂ c), hsq, fun c => ⟨hd1 c, hd2 c⟩, ?_⟩
  intro c c' hcc
  have hvne : c.val ≠ c'.val := fun h => hcc (Fin.ext h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply hvne
    rw [← hd1 c, ← hd1 c']
    exact congrArg (fun b : Fin N => b.val / sat3D N) h
  · intro h
    apply hvne
    rw [← hd1 c, ← hd2 c']
    exact congrArg (fun b : Fin N => b.val / sat3D N) h
  · intro h
    apply hvne
    rw [← hd2 c, ← hd1 c']
    exact congrArg (fun b : Fin N => b.val / sat3D N) h
  · intro h
    apply hvne
    rw [← hd2 c, ← hd2 c']
    exact congrArg (fun b : Fin N => b.val / sat3D N) h

/-- **The quantitative form (proved)**: the tear family's support has *exactly* `2 · sat3M N` bits — `sat3M N ≈ √N/3`
disjoint two-bit tear sites, aligned to the clause-block partition of the layout. -/
theorem sat3_tear_support_card (N : ℕ) (hv : 1 ≤ sat3V N) :
    ∃ T : Fin (sat3M N) → (Fin N → Bool) × Fin N × Fin N,
      (∀ c, OddSquare (sat3Family N) (T c).1 (T c).2.1 (T c).2.2) ∧
      (Finset.univ.image (fun c => (T c).2.1) ∪
        Finset.univ.image (fun c => (T c).2.2)).card = 2 * sat3M N := by
  obtain ⟨T, hsq, hdiv, -⟩ := sat3_disjoint_tear_count N hv
  refine ⟨T, hsq, ?_⟩
  have hinj1 : Function.Injective (fun c => (T c).2.1) := by
    intro c c' h
    apply Fin.ext
    rw [← (hdiv c).1, ← (hdiv c').1]
    exact congrArg (fun b : Fin N => b.val / sat3D N) h
  have hinj2 : Function.Injective (fun c => (T c).2.2) := by
    intro c c' h
    apply Fin.ext
    rw [← (hdiv c).2, ← (hdiv c').2]
    exact congrArg (fun b : Fin N => b.val / sat3D N) h
  have hdisj : Disjoint (Finset.univ.image (fun c : Fin (sat3M N) => (T c).2.1))
      (Finset.univ.image (fun c : Fin (sat3M N) => (T c).2.2)) := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨c', -, heq⟩ := Finset.mem_image.mp hx2
    by_cases hcc : c' = c
    · subst hcc
      exact (hsq c').1 heq.symm
    · apply hcc
      apply Fin.ext
      rw [← (hdiv c').2, ← (hdiv c).1]
      exact congrArg (fun b : Fin N => b.val / sat3D N) heq
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj1, Finset.card_image_of_injective _ hinj2,
    Finset.card_univ, Fintype.card_fin]
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_blockTear
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_disjoint_tear_count
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_tear_support_card
