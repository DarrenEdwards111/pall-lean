import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSpira

/-!
# N-Frame: attacking the SAT game bound — selector forcing and the rectangle-cover method

Two genuine advances on the one remaining question, and an honest map of the wall.

**1. Selector forcing (proved).**  The sign-bit forcing gave `m` forced answers.  Here every *selector* bit of the
layout is forced too: for each clause `c` and variable `j`, the empty-clause base and its one-selector-flip corner
form a 1/0-pair differing **only** at selector `(c, slot 0, j)`.  That is `m·v ≈ N/3` forced outputs:

  `sat3_kw_protocol_lb_strong` — **PROVED**: any protocol solving the SAT boundary game has
        `sat3M N · sat3V N ≤ 2^cost` — communication `≥ log₂(N/3)`, doubling the previous constant.
  `sat3_kwCost_lb_strong` / `sat3_depthBudget_lb_strong` — the same at the minima.

**2. The rectangle-cover method (proved).**  `rect_partition`: a protocol of cost `c` partitions any solved family
`X × Y` into at most `2^c` *aligned rectangles* (sub-rectangles whose pairs all differ at one common coordinate).
Hence `kw_cover_lb`: if every aligned rectangle inside `X × Y` has area `≤ D`, then `|X|·|Y| ≤ 2^cost · D`.  This is
the standard communication lower-bound machinery, Trans-native: **the superlog question is now the concrete
combinatorial question** of exhibiting satisfiable/unsatisfiable encoding families where every aligned rectangle is
tiny (`D ≤ |X|·|Y| / N^{ω(1)}`).

## Honest scope — the wall, precisely

The product measure `|A|·|B|` used here is Khrapchenko's; it is classically known (Razborov's convexity argument)
that such formal-complexity measures cannot prove bounds beyond quadratic — so *this* framework alone caps at
`cost ≳ 2·log N`, and the superlog question needs a refined (non-product, non-submodular) measure on top of the
partition theorem.  That refinement — witness-coherence as a measure the partition cannot shed — is the genuine
research wall, named and not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Selector forcing: every selector bit is a forced answer -/

/-- **The selector forcing pair (proved)**: for every clause `c` and variable `j`, a 1/0-pair differing only at the
selector bit `(c, slot 0, j)` — the empty-clause base and its one-flip corner. -/
theorem sat3_selector_pair (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (j : Fin (sat3V N)) :
    ∃ x₁ x₀ : Fin N → Bool, sat3Family N x₁ = true ∧ sat3Family N x₀ = false ∧
      ∀ b : Fin N, x₁ b ≠ x₀ b →
        b = sat3Bit N c ⟨0, by omega⟩ j.val (by have := j.isLt; omega) := by
  have hDpos : 0 < sat3D N := sat3D_pos N
  set flip : Fin N := sat3Bit N c ⟨0, by omega⟩ j.val (by have := j.isLt; omega) with hflip
  set z : Fin N → Bool := fun b =>
    decide (b.val % sat3D N = 0 ∧ b.val / sat3D N ≠ c.val ∧ b.val / sat3D N < sat3M N)
    with hz
  have hflip_rem : flip.val % sat3D N = j.val := by
    rw [hflip, sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + j.val = j.val
    omega
  have hflip_div : flip.val / sat3D N = c.val := by
    rw [hflip]
    exact sat3Bit_clause N c ⟨0, by omega⟩ j.val (by have := j.isLt; omega)
  refine ⟨Function.update z flip true, z, ?_, ?_, ?_⟩
  · -- the flipped corner is satisfiable by the all-true assignment
    apply decide_eq_true
    refine ⟨fun _ => true, sat3Eval_true_of_all N _ _ ?_⟩
    intro cl
    by_cases hcl : cl = c
    · subst hcl
      refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩ j ?_ ?_⟩
      · rw [Function.update_self]
      · -- the sign bit is not the flip and reads z-false
        have hr1 : (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
            = sat3V N := by
          rw [sat3Bit_rem]
          show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
          omega
        have hne : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega) ≠ flip := by
          intro hcontra
          rw [hcontra, hflip_rem] at hr1
          have := j.isLt
          omega
        rw [Function.update_of_ne hne]
        have hzs : z (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
          show decide _ = false
          rw [decide_eq_false_iff_not]
          rintro ⟨hmod, -, -⟩
          rw [hr1] at hmod
          omega
        rw [hzs]
        rfl
    · -- other clauses: live variable-0 selector, sign 0
      refine ⟨⟨0, by omega⟩,
        sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩ ⟨0, hv⟩ ?_ ?_⟩
      · have hne : sat3Bit N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val
            (by omega) ≠ flip := by
          intro hcontra
          apply hcl
          apply Fin.ext
          rw [← sat3Bit_clause N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega),
            hcontra, hflip_div]
        rw [Function.update_of_ne hne]
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
      · have hr1 : (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
            = sat3V N := by
          rw [sat3Bit_rem]
          show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
          omega
        have hne : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega) ≠ flip := by
          intro hcontra
          rw [hcontra, hflip_rem] at hr1
          have := j.isLt
          omega
        rw [Function.update_of_ne hne]
        have hzs : z (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
          show decide _ = false
          rw [decide_eq_false_iff_not]
          rintro ⟨hmod, -, -⟩
          rw [hr1] at hmod
          omega
        rw [hzs]
        rfl
  · -- the base is unsatisfiable: clause c is empty
    apply sat3Family_false_of_empty_clause N z c
    intro t i
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro ⟨-, hdiv, -⟩
    exact hdiv (sat3Bit_clause N c t i.val (by have := i.isLt; omega))
  · -- the pair differs only at the flip
    intro b hb
    by_contra hcon
    exact hb (Function.update_of_ne hcon true z)

/-- **The strengthened protocol lower bound (proved)**: `sat3M N · sat3V N ≤ 2^cost` — every one of the `m·v ≈ N/3`
selector bits is a forced answer, so communication is at least `log₂(N/3)`. -/
theorem sat3_kw_protocol_lb_strong (N : ℕ) (hv : 1 ≤ sat3V N)
    (p : KWProt N) (hsolve : Solves p (sat3Family N)) :
    sat3M N * sat3V N ≤ 2 ^ p.cost := by
  have hmem : ∀ (c : Fin (sat3M N)) (j : Fin (sat3V N)),
      sat3Bit N c ⟨0, by omega⟩ j.val (by have := j.isLt; omega) ∈ p.outs := by
    intro c j
    obtain ⟨x₁, x₀, h1, h0, hforce⟩ := sat3_selector_pair N hv c j
    have hrun := hsolve x₁ x₀ h1 h0
    have hloc := hforce _ hrun
    rw [← hloc]
    exact run_mem_outs p x₁ x₀
  have hinj : Function.Injective (fun cj : Fin (sat3M N) × Fin (sat3V N) =>
      sat3Bit N cj.1 ⟨0, by omega⟩ cj.2.val (by have := cj.2.isLt; omega)) := by
    intro a b h
    have hr1 : (sat3Bit N a.1 ⟨0, by omega⟩ a.2.val
        (by have := a.2.isLt; omega)).val % sat3D N = a.2.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + a.2.val = a.2.val
      omega
    have hr2 : (sat3Bit N b.1 ⟨0, by omega⟩ b.2.val
        (by have := b.2.isLt; omega)).val % sat3D N = b.2.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + b.2.val = b.2.val
      omega
    have hdiv : a.1.val = b.1.val := by
      rw [← sat3Bit_clause N a.1 ⟨0, by omega⟩ a.2.val (by have := a.2.isLt; omega),
        ← sat3Bit_clause N b.1 ⟨0, by omega⟩ b.2.val (by have := b.2.isLt; omega)]
      exact congrArg (fun bit : Fin N => bit.val / sat3D N) h
    have hrem : a.2.val = b.2.val := by
      rw [← hr1, ← hr2]
      exact congrArg (fun bit : Fin N => bit.val % sat3D N) h
    exact Prod.ext (Fin.ext hdiv) (Fin.ext hrem)
  have hcard : sat3M N * sat3V N ≤ p.outs.card := by
    have himg : Finset.univ.image (fun cj : Fin (sat3M N) × Fin (sat3V N) =>
        sat3Bit N cj.1 ⟨0, by omega⟩ cj.2.val (by have := cj.2.isLt; omega)) ⊆ p.outs := by
      intro i hi
      obtain ⟨cj, -, rfl⟩ := Finset.mem_image.mp hi
      exact hmem cj.1 cj.2
    have hcardimg : (Finset.univ.image (fun cj : Fin (sat3M N) × Fin (sat3V N) =>
        sat3Bit N cj.1 ⟨0, by omega⟩ cj.2.val (by have := cj.2.isLt; omega))).card
        = sat3M N * sat3V N := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin]
    rw [← hcardimg]
    exact Finset.card_le_card himg
  exact le_trans hcard (outs_card_le p)

/-- The layout is non-degenerate whenever `1 ≤ sat3V N`. -/
theorem sat3_pos_of_hv (N : ℕ) (hv : 1 ≤ sat3V N) : 0 < N := by
  by_contra h
  push_neg at h
  interval_cases N
  revert hv
  decide

/-- **The strengthened game bound (proved)**: `sat3M N · sat3V N ≤ 2^(kwCost (sat3Family N))`. -/
theorem sat3_kwCost_lb_strong (N : ℕ) (hv : 1 ≤ sat3V N) :
    sat3M N * sat3V N ≤ 2 ^ kwCost (sat3Family N) := by
  have hN : 0 < N := sat3_pos_of_hv N hv
  have hne : {c | ∃ p : KWProt N, Solves p (sat3Family N) ∧ p.cost = c}.Nonempty := by
    refine ⟨(kwProtOf hN (dnfFor (sat3Family N))).cost,
      kwProtOf hN (dnfFor (sat3Family N)), ?_, rfl⟩
    have := kwProtOf_solves hN (dnfFor (sat3Family N))
    rw [eval_dnfFor] at this
    exact this
  obtain ⟨p, hp, hcost⟩ := Nat.sInf_mem hne
  have := sat3_kw_protocol_lb_strong N hv p hp
  show sat3M N * sat3V N
      ≤ 2 ^ sInf {c | ∃ p : KWProt N, Solves p (sat3Family N) ∧ p.cost = c}
  rw [← hcost]
  exact this

/-- **The strengthened depth bound (proved)**: `sat3M N · sat3V N ≤ 4^(depthBudget (sat3Family N))`. -/
theorem sat3_depthBudget_lb_strong (N : ℕ) (hv : 1 ≤ sat3V N) :
    sat3M N * sat3V N ≤ 4 ^ depthBudget (sat3Family N) := by
  have hN : 0 < N := sat3_pos_of_hv N hv
  have h1 := sat3_kwCost_lb_strong N hv
  have h2 := kwCost_le_two_depthBudget hN (sat3Family N)
  have h3 : (2 : ℕ) ^ kwCost (sat3Family N)
      ≤ 2 ^ (2 * depthBudget (sat3Family N)) :=
    Nat.pow_le_pow_right (by omega) h2
  have h4 : (2 : ℕ) ^ (2 * depthBudget (sat3Family N))
      = 4 ^ depthBudget (sat3Family N) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]
  omega

/-! ### The rectangle-cover method -/

/-- **The partition theorem (proved)**: a protocol of cost `c` covers any solved family `X × Y` by at most `2^c`
aligned rectangles.  If every aligned rectangle has area `≤ D`, then `|X|·|Y| ≤ 2^c · D`. -/
theorem rect_partition {n : ℕ} (p : KWProt n) :
    ∀ (X Y : Finset (Fin n → Bool)),
      (∀ x ∈ X, ∀ y ∈ Y, x (p.run x y) ≠ y (p.run x y)) →
      ∀ D : ℕ,
      (∀ (i : Fin n) (A B : Finset (Fin n → Bool)), A ⊆ X → B ⊆ Y →
        (∀ x ∈ A, ∀ y ∈ B, x i ≠ y i) → A.card * B.card ≤ D) →
      X.card * Y.card ≤ 2 ^ p.cost * D := by
  induction p with
  | out i =>
    intro X Y hsolve D hrect
    have h := hrect i X Y (Finset.Subset.refl _) (Finset.Subset.refl _)
      (fun x hx y hy => hsolve x hx y hy)
    show X.card * Y.card ≤ 2 ^ 0 * D
    rw [pow_zero, one_mul]
    exact h
  | askA q l r ihl ihr =>
    intro X Y hsolve D hrect
    have h1 := ihl (X.filter (fun x => q x = true)) Y (by
      intro x hx y hy
      have hxX := (Finset.mem_filter.mp hx).1
      have hxq := (Finset.mem_filter.mp hx).2
      have h := hsolve x hxX y hy
      rw [KWProt.run_askA, if_pos hxq] at h
      exact h) D (fun i A B hA hB hal =>
        hrect i A B (Finset.Subset.trans hA (Finset.filter_subset _ _)) hB hal)
    have h2 := ihr (X.filter (fun x => ¬(q x = true))) Y (by
      intro x hx y hy
      have hxX := (Finset.mem_filter.mp hx).1
      have hxq := (Finset.mem_filter.mp hx).2
      have h := hsolve x hxX y hy
      rw [KWProt.run_askA, if_neg hxq] at h
      exact h) D (fun i A B hA hB hal =>
        hrect i A B (Finset.Subset.trans hA (Finset.filter_subset _ _)) hB hal)
    have hsplit : (X.filter (fun x => q x = true)).card
        + (X.filter (fun x => ¬(q x = true))).card = X.card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have hXY : X.card * Y.card
        = (X.filter (fun x => q x = true)).card * Y.card
          + (X.filter (fun x => ¬(q x = true))).card * Y.card := by
      rw [← hsplit]
      ring
    have hp1 : (2 : ℕ) ^ l.cost * D ≤ 2 ^ max l.cost r.cost * D :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
    have hp2 : (2 : ℕ) ^ r.cost * D ≤ 2 ^ max l.cost r.cost * D :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    have hpow : (2 : ℕ) ^ (max l.cost r.cost + 1) * D
        = 2 ^ max l.cost r.cost * D + 2 ^ max l.cost r.cost * D := by
      rw [pow_succ]
      ring
    show X.card * Y.card ≤ 2 ^ (max l.cost r.cost + 1) * D
    omega
  | askB q l r ihl ihr =>
    intro X Y hsolve D hrect
    have h1 := ihl X (Y.filter (fun y => q y = true)) (by
      intro x hx y hy
      have hyY := (Finset.mem_filter.mp hy).1
      have hyq := (Finset.mem_filter.mp hy).2
      have h := hsolve x hx y hyY
      rw [KWProt.run_askB, if_pos hyq] at h
      exact h) D (fun i A B hA hB hal =>
        hrect i A B hA (Finset.Subset.trans hB (Finset.filter_subset _ _)) hal)
    have h2 := ihr X (Y.filter (fun y => ¬(q y = true))) (by
      intro x hx y hy
      have hyY := (Finset.mem_filter.mp hy).1
      have hyq := (Finset.mem_filter.mp hy).2
      have h := hsolve x hx y hyY
      rw [KWProt.run_askB, if_neg hyq] at h
      exact h) D (fun i A B hA hB hal =>
        hrect i A B hA (Finset.Subset.trans hB (Finset.filter_subset _ _)) hal)
    have hsplit : (Y.filter (fun y => q y = true)).card
        + (Y.filter (fun y => ¬(q y = true))).card = Y.card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have hXY : X.card * Y.card
        = X.card * (Y.filter (fun y => q y = true)).card
          + X.card * (Y.filter (fun y => ¬(q y = true))).card := by
      rw [← hsplit]
      ring
    have hp1 : (2 : ℕ) ^ l.cost * D ≤ 2 ^ max l.cost r.cost * D :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
    have hp2 : (2 : ℕ) ^ r.cost * D ≤ 2 ^ max l.cost r.cost * D :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    have hpow : (2 : ℕ) ^ (max l.cost r.cost + 1) * D
        = 2 ^ max l.cost r.cost * D + 2 ^ max l.cost r.cost * D := by
      rw [pow_succ]
      ring
    show X.card * Y.card ≤ 2 ^ (max l.cost r.cost + 1) * D
    omega

/-- **The cover lower bound (proved)**: small aligned rectangles force communication — the attack surface for the
superlog question, reduced to combinatorics of the SAT encoding. -/
theorem kw_cover_lb {n : ℕ} (f : (Fin n → Bool) → Bool) (p : KWProt n)
    (hs : Solves p f) (X Y : Finset (Fin n → Bool))
    (hX : ∀ x ∈ X, f x = true) (hY : ∀ y ∈ Y, f y = false) (D : ℕ)
    (hrect : ∀ (i : Fin n) (A B : Finset (Fin n → Bool)), A ⊆ X → B ⊆ Y →
      (∀ x ∈ A, ∀ y ∈ B, x i ≠ y i) → A.card * B.card ≤ D) :
    X.card * Y.card ≤ 2 ^ p.cost * D :=
  rect_partition p X Y (fun x hx y hy => hs x y (hX x hx) (hY y hy)) D hrect

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_pair
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_kw_protocol_lb_strong
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_kwCost_lb_strong
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_depthBudget_lb_strong
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rect_partition
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kw_cover_lb
