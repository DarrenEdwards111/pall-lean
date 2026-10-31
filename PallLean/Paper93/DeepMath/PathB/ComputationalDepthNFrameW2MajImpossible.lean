import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameW2YaoBrick4

/-!
# N-Frame: majority is impossible at dimension 2 — the rung, closed absolutely

Working the counting argument from first principles produced a stronger result than the expected super-polynomial
bound: for the boundary model's dimension-≤2 observers, majority is not computable **at any volume**.

**The argument.**  Take the *last step activated by any input at all*.  Every later step is passive on every input, so
on the codimension-1 subcube `{x : x reads the activating value at that step's variable}` the program output is a
**fixed affine function** (the activation constant XOR the suffix parity — brick 3's erasure).  If *no* step ever
activates, the program is globally affine (brick 2).  But majority is non-affine on every codimension-1 subcube: a
threshold-straddling 2×2 square realizes the AND pattern `0,0,0,1`, whose second difference is `true`, while every
affine function's vanishes (brick 2's pairing argument, generalized here to arbitrary squares).  Contradiction — with
no length hypothesis whatsoever.

  `majFn` / corner-count lemmas — the majority family and the threshold square construction.
  `progPar_square` — **PROVED**: the affine part's second difference vanishes on *every* 2-coordinate square.
  `last_globally_active_split` — **PROVED**: the program splits at the last step any input activates.
  `w2_maj_impossible` — **PROVED**: no one-bit-register program computes `majFn n` (`n ≥ 5`).
  `maj_needs_dim_three` / `boundaryDim_maj_eq_three` — **PROVED, the headline**: any observer computing majority has
        dimension `≥ 3`; with the universal `≤ 3` bound, **majority's boundary dimension is exactly 3**.

## Honest scope — why this does not contradict the classical picture

Yao's super-polynomial and BDFP's exponential bounds concern **general** width-2 branching programs, where the two
states may read *different* variables — strictly stronger than dimension-≤2 boundary observers (our `W2Prog`, where
both states read the same variable each step).  For the boundary model's dimension ladder the result is absolute:
dimension 1 cannot do `x₀ ⊕ x₁`, dimension 2 cannot do majority, dimension 3 does everything (at a volume price — the
Nečiporuk tearing).  The joint volume–dimension trade-off at dimension `≥ 3`, and the mountain target `sat3Target`,
are untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### Majority and the threshold square -/

/-- The majority family: at least `(n+1)/2` ones. -/
def majFn (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((n + 1) / 2 ≤ (Finset.univ.filter (fun i => x i = true)).card)

/-- The ones-set of an input. -/
def onesOf (x : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)

theorem onesOf_update_true (x : Fin n → Bool) (v : Fin n) (hxv : x v = false) :
    onesOf (Function.update x v true) = insert v (onesOf x) := by
  ext i
  simp only [onesOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hiv : i = v
  · subst hiv
    simp [Function.update_self]
  · rw [Function.update_of_ne hiv]
    simp [hiv]

theorem card_onesOf_update_true (x : Fin n → Bool) (v : Fin n) (hxv : x v = false) :
    (onesOf (Function.update x v true)).card = (onesOf x).card + 1 := by
  rw [onesOf_update_true x v hxv, Finset.card_insert_of_notMem (by
    simp only [onesOf, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hxv]
    simp)]

theorem majFn_eq_decide (x : Fin n → Bool) :
    majFn n x = decide ((n + 1) / 2 ≤ (onesOf x).card) := rfl

/-- Two coordinates distinct from any given one (`n ≥ 5`). -/
theorem exists_two_other (hn : 5 ≤ n) (w : Fin n) :
    ∃ i₁ i₂ : Fin n, i₁ ≠ i₂ ∧ i₁ ≠ w ∧ i₂ ≠ w := by
  by_cases h0 : w.val = 0
  · exact ⟨⟨1, by omega⟩, ⟨2, by omega⟩,
      Fin.ne_of_val_ne (show (1 : ℕ) ≠ 2 by omega),
      Fin.ne_of_val_ne (show (1 : ℕ) ≠ w.val by omega),
      Fin.ne_of_val_ne (show (2 : ℕ) ≠ w.val by omega)⟩
  · by_cases h1 : w.val = 1
    · exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩,
        Fin.ne_of_val_ne (show (0 : ℕ) ≠ 2 by omega),
        Fin.ne_of_val_ne (show (0 : ℕ) ≠ w.val by omega),
        Fin.ne_of_val_ne (show (2 : ℕ) ≠ w.val by omega)⟩
    · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩,
        Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 by omega),
        Fin.ne_of_val_ne (show (0 : ℕ) ≠ w.val by omega),
        Fin.ne_of_val_ne (show (1 : ℕ) ≠ w.val by omega)⟩

/-! ### The affine part's second difference vanishes on every square -/

/-- **The general square lemma (proved)**: `progPar`'s second difference vanishes on every 2-coordinate square — each
step reads one variable, so its contributions pair up. -/
theorem progPar_square (p : W2Prog n) (z : Fin n → Bool) (i₁ i₂ : Fin n) (hij : i₁ ≠ i₂) :
    xor (xor (progPar p z) (progPar p (Function.update z i₁ true)))
      (xor (progPar p (Function.update z i₂ true))
        (progPar p (Function.update (Function.update z i₁ true) i₂ true))) = false := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    show xor (xor (xor (s.1 false (z s.2)) (progPar p z))
        (xor (s.1 false (Function.update z i₁ true s.2)) (progPar p (Function.update z i₁ true))))
      (xor (xor (s.1 false (Function.update z i₂ true s.2))
          (progPar p (Function.update z i₂ true)))
        (xor (s.1 false (Function.update (Function.update z i₁ true) i₂ true s.2))
          (progPar p (Function.update (Function.update z i₁ true) i₂ true)))) = false
    have hpair : xor (xor (s.1 false (z s.2)) (s.1 false (Function.update z i₁ true s.2)))
        (xor (s.1 false (Function.update z i₂ true s.2))
          (s.1 false (Function.update (Function.update z i₁ true) i₂ true s.2))) = false := by
      by_cases hA : s.2 = i₁
      · have e1 : Function.update z i₁ true s.2 = true := by rw [hA, Function.update_self]
        have e2 : Function.update z i₂ true s.2 = z s.2 := by
          rw [hA]
          rw [Function.update_of_ne hij]
        have e3 : Function.update (Function.update z i₁ true) i₂ true s.2 = true := by
          rw [hA, Function.update_of_ne hij, Function.update_self]
        rw [e1, e2, e3]
        cases s.1 false (z s.2) <;> cases s.1 false true <;> rfl
      · by_cases hB : s.2 = i₂
        · have e1 : Function.update z i₁ true s.2 = z s.2 := by
            rw [hB, Function.update_of_ne (fun hc => hij hc.symm)]
          have e2 : Function.update z i₂ true s.2 = true := by rw [hB, Function.update_self]
          have e3 : Function.update (Function.update z i₁ true) i₂ true s.2 = true := by
            rw [hB, Function.update_self]
          rw [e1, e2, e3]
          cases s.1 false (z s.2) <;> cases s.1 false true <;> rfl
        · have e1 : Function.update z i₁ true s.2 = z s.2 := Function.update_of_ne hA true z
          have e2 : Function.update z i₂ true s.2 = z s.2 := Function.update_of_ne hB true z
          have e3 : Function.update (Function.update z i₁ true) i₂ true s.2 = z s.2 := by
            rw [Function.update_of_ne hB, Function.update_of_ne hA]
          rw [e1, e2, e3]
          cases s.1 false (z s.2) <;> rfl
    generalize s.1 false (z s.2) = a1 at hpair ⊢
    generalize s.1 false (Function.update z i₁ true s.2) = a2 at hpair ⊢
    generalize s.1 false (Function.update z i₂ true s.2) = a3 at hpair ⊢
    generalize s.1 false (Function.update (Function.update z i₁ true) i₂ true s.2) = a4
      at hpair ⊢
    generalize progPar p z = b1 at ih ⊢
    generalize progPar p (Function.update z i₁ true) = b2 at ih ⊢
    generalize progPar p (Function.update z i₂ true) = b3 at ih ⊢
    generalize progPar p (Function.update (Function.update z i₁ true) i₂ true) = b4 at ih ⊢
    cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;>
      cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> simp_all

/-! ### The last globally-activatable step -/

theorem stepActive_congr (s : (Bool → Bool → Bool) × Fin n) (x y : Fin n → Bool)
    (h : x s.2 = y s.2) : stepActive s x ↔ stepActive s y := by
  unfold stepActive
  rw [h]

/-- **The split at the last step any input activates (proved).** -/
theorem last_globally_active_split (p : W2Prog n) :
    (∀ x, ∀ s ∈ p, ¬ stepActive s x) ∨
    ∃ (p₁ : W2Prog n) (s : (Bool → Bool → Bool) × Fin n) (p₂ : W2Prog n),
      p = p₁ ++ s :: p₂ ∧ (∃ x, stepActive s x) ∧ ∀ x, ∀ s' ∈ p₂, ¬ stepActive s' x := by
  induction p with
  | nil =>
    left
    intro x s hs
    exact absurd hs List.not_mem_nil
  | cons a t ih =>
    rcases ih with hall | ⟨p₁, s, p₂, heq, hwit, hpass⟩
    · by_cases ha : ∃ x, stepActive a x
      · right
        exact ⟨[], a, t, rfl, ha, hall⟩
      · left
        intro x s hs
        rcases List.mem_cons.mp hs with h | h
        · intro hact
          exact ha ⟨x, h ▸ hact⟩
        · exact hall x s h
    · right
      exact ⟨a :: p₁, s, p₂, by rw [heq]; rfl, hwit, hpass⟩

/-! ### The square clash -/

/-- **The clash (proved)**: no fixed affine value `c₀ ⊕ progPar g ·` can take the AND pattern `0,0,0,1` on a square. -/
theorem affine_square_clash (g : W2Prog n) (c0 : Bool) (z : Fin n → Bool) (i₁ i₂ : Fin n)
    (hij : i₁ ≠ i₂)
    (h00 : xor c0 (progPar g z) = false)
    (h10 : xor c0 (progPar g (Function.update z i₁ true)) = false)
    (h01 : xor c0 (progPar g (Function.update z i₂ true)) = false)
    (h11 : xor c0 (progPar g (Function.update (Function.update z i₁ true) i₂ true)) = true) :
    False := by
  have hsq := progPar_square g z i₁ i₂ hij
  generalize progPar g z = b1 at h00 hsq
  generalize progPar g (Function.update z i₁ true) = b2 at h10 hsq
  generalize progPar g (Function.update z i₂ true) = b3 at h01 hsq
  generalize progPar g (Function.update (Function.update z i₁ true) i₂ true) = b4 at h11 hsq
  cases c0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    first
      | exact Bool.noConfusion h00
      | exact Bool.noConfusion h10
      | exact Bool.noConfusion h01
      | exact Bool.noConfusion h11
      | exact Bool.noConfusion hsq

/-! ### The threshold square inside a prescribed hyperplane -/

/-- **The square construction (proved)**: for `n ≥ 5`, any coordinate `w` and value `a`, there is a base point `z` with
`z w = a`, two free coordinates off `w`, both `false` at `z`, whose ones-count is exactly `(n+1)/2 − 2` — so majority
takes the AND pattern on the square. -/
theorem exists_threshold_square (hn : 5 ≤ n) (w : Fin n) (a : Bool) :
    ∃ (z : Fin n → Bool) (i₁ i₂ : Fin n), i₁ ≠ i₂ ∧ i₁ ≠ w ∧ i₂ ≠ w ∧
      z w = a ∧ z i₁ = false ∧ z i₂ = false ∧
      (onesOf z).card = (n + 1) / 2 - 2 := by
  obtain ⟨i₁, i₂, hij, h1w, h2w⟩ := exists_two_other hn w
  set K := (n + 1) / 2 - 2 with hK
  have hK1 : 1 ≤ K := by omega
  set others := (((Finset.univ : Finset (Fin n)).erase w).erase i₁).erase i₂ with hoth
  have hmem1 : i₁ ∈ (Finset.univ : Finset (Fin n)).erase w :=
    Finset.mem_erase.mpr ⟨h1w, Finset.mem_univ _⟩
  have hmem2 : i₂ ∈ ((Finset.univ : Finset (Fin n)).erase w).erase i₁ :=
    Finset.mem_erase.mpr ⟨fun hc => hij hc.symm, Finset.mem_erase.mpr ⟨h2w, Finset.mem_univ _⟩⟩
  have hcard_others : others.card = n - 3 := by
    rw [hoth, Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hmem1,
      Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, Fintype.card_fin]
    omega
  have hKle : K ≤ n - 3 := by omega
  cases a with
  | false =>
    obtain ⟨S, hS, hScard⟩ := Finset.le_card_iff_exists_subset_card.mp
      (show K ≤ others.card by omega)
    have hnotmem : ∀ j : Fin n, (j = w ∨ j = i₁ ∨ j = i₂) → j ∉ S := by
      intro j hj hc
      have := hS hc
      rw [hoth] at this
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_erase] at this
      rcases hj with h | h | h
      · exact this.2.2.1 h
      · exact this.2.1 h
      · exact this.1 h
    refine ⟨fun i => decide (i ∈ S), i₁, i₂, hij, h1w, h2w, ?_, ?_, ?_, ?_⟩
    · simp [hnotmem w (Or.inl rfl)]
    · simp [hnotmem i₁ (Or.inr (Or.inl rfl))]
    · simp [hnotmem i₂ (Or.inr (Or.inr rfl))]
    · have hones : onesOf (fun i => decide (i ∈ S)) = S := by
        ext i
        simp [onesOf]
      rw [hones, hScard]
  | true =>
    obtain ⟨S, hS, hScard⟩ := Finset.le_card_iff_exists_subset_card.mp
      (show K - 1 ≤ others.card by omega)
    have hnotmem : ∀ j : Fin n, (j = w ∨ j = i₁ ∨ j = i₂) → j ∉ S := by
      intro j hj hc
      have := hS hc
      rw [hoth] at this
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_erase] at this
      rcases hj with h | h | h
      · exact this.2.2.1 h
      · exact this.2.1 h
      · exact this.1 h
    have hwS : w ∉ S := hnotmem w (Or.inl rfl)
    refine ⟨fun i => decide (i ∈ insert w S), i₁, i₂, hij, h1w, h2w, ?_, ?_, ?_, ?_⟩
    · simp
    · have : i₁ ∉ insert w S := by
        rw [Finset.mem_insert]
        rintro (hc | hc)
        · exact h1w hc
        · exact hnotmem i₁ (Or.inr (Or.inl rfl)) hc
      simp [this]
    · have : i₂ ∉ insert w S := by
        rw [Finset.mem_insert]
        rintro (hc | hc)
        · exact h2w hc
        · exact hnotmem i₂ (Or.inr (Or.inr rfl)) hc
      simp [this]
    · have hones : onesOf (fun i => decide (i ∈ insert w S)) = insert w S := by
        ext i
        simp [onesOf]
      rw [hones, Finset.card_insert_of_notMem hwS, hScard]
      omega

/-! ### The impossibility -/

/-- **Majority is impossible at dimension 2 (proved)**: no one-bit-register program computes `majFn n` for `n ≥ 5` —
at any length. -/
theorem w2_maj_impossible (hn : 5 ≤ n) (r0 : Bool) (p : W2Prog n) :
    ¬ ∀ x, w2run p r0 x = majFn n x := by
  intro hcomp
  have hT2 : 2 ≤ (n + 1) / 2 := by omega
  -- corner values of majority on a threshold square
  have hcorners : ∀ (z : Fin n → Bool) (i₁ i₂ : Fin n), i₁ ≠ i₂ →
      z i₁ = false → z i₂ = false → (onesOf z).card = (n + 1) / 2 - 2 →
      majFn n z = false ∧ majFn n (Function.update z i₁ true) = false ∧
      majFn n (Function.update z i₂ true) = false ∧
      majFn n (Function.update (Function.update z i₁ true) i₂ true) = true := by
    intro z i₁ i₂ hij h1 h2 hcount
    have c10 : (onesOf (Function.update z i₁ true)).card = (n + 1) / 2 - 1 := by
      rw [card_onesOf_update_true z i₁ h1, hcount]
      omega
    have c01 : (onesOf (Function.update z i₂ true)).card = (n + 1) / 2 - 1 := by
      rw [card_onesOf_update_true z i₂ h2, hcount]
      omega
    have c11 : (onesOf (Function.update (Function.update z i₁ true) i₂ true)).card
        = (n + 1) / 2 := by
      rw [card_onesOf_update_true _ i₂ (by
        rw [Function.update_of_ne (fun hc => hij hc.symm)]
        exact h2), c10]
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [majFn_eq_decide, hcount]
      simp only [decide_eq_false_iff_not]
      omega
    · rw [majFn_eq_decide, c10]
      simp only [decide_eq_false_iff_not]
      omega
    · rw [majFn_eq_decide, c01]
      simp only [decide_eq_false_iff_not]
      omega
    · rw [majFn_eq_decide, c11]
      simp
  rcases last_globally_active_split p with hall | ⟨p₁, s, p₂, heq, ⟨xw, hxw⟩, hpass⟩
  · -- globally affine: clash on any threshold square
    obtain ⟨z, i₁, i₂, hij, -, -, -, h1, h2, hcount⟩ :=
      exists_threshold_square hn ⟨0, by omega⟩ false
    obtain ⟨m00, m10, m01, m11⟩ := hcorners z i₁ i₂ hij h1 h2 hcount
    have f00 := (hcomp z).symm.trans (w2run_allPassive p z (hall z) r0)
    have f10 := (hcomp (Function.update z i₁ true)).symm.trans
      (w2run_allPassive p (Function.update z i₁ true) (hall _) r0)
    have f01 := (hcomp (Function.update z i₂ true)).symm.trans
      (w2run_allPassive p (Function.update z i₂ true) (hall _) r0)
    have f11 := (hcomp (Function.update (Function.update z i₁ true) i₂ true)).symm.trans
      (w2run_allPassive p (Function.update (Function.update z i₁ true) i₂ true) (hall _) r0)
    exact affine_square_clash p r0 z i₁ i₂ hij
      (by rw [← f00, m00]) (by rw [← f10, m10]) (by rw [← f01, m01]) (by rw [← f11, m11])
  · -- split at the last globally-activatable step: clash on a square inside its hyperplane
    obtain ⟨z, i₁, i₂, hij, h1w, h2w, hzw, h1, h2, hcount⟩ :=
      exists_threshold_square hn s.2 (xw s.2)
    obtain ⟨m00, m10, m01, m11⟩ := hcorners z i₁ i₂ hij h1 h2 hcount
    have hzw10 : Function.update z i₁ true s.2 = xw s.2 := by
      rw [Function.update_of_ne (fun hc => h1w hc.symm)]
      exact hzw
    have hzw01 : Function.update z i₂ true s.2 = xw s.2 := by
      rw [Function.update_of_ne (fun hc => h2w hc.symm)]
      exact hzw
    have hzw11 : Function.update (Function.update z i₁ true) i₂ true s.2 = xw s.2 := by
      rw [Function.update_of_ne (fun hc => h2w hc.symm)]
      exact hzw10
    have hrun : ∀ y : Fin n → Bool, y s.2 = xw s.2 →
        w2run p r0 y = xor (s.1 false (xw s.2)) (progPar p₂ y) := by
      intro y hy
      have hact : stepActive s y := (stepActive_congr s y xw hy).mpr hxw
      rw [heq, w2run_after_active p₁ s p₂ y hact (fun s' hs' => hpass y s' hs') r0, hy]
    have f00 := (hcomp z).symm.trans (hrun z hzw)
    have f10 := (hcomp (Function.update z i₁ true)).symm.trans
      (hrun (Function.update z i₁ true) hzw10)
    have f01 := (hcomp (Function.update z i₂ true)).symm.trans
      (hrun (Function.update z i₂ true) hzw01)
    have f11 := (hcomp (Function.update (Function.update z i₁ true) i₂ true)).symm.trans
      (hrun (Function.update (Function.update z i₁ true) i₂ true) hzw11)
    exact affine_square_clash p₂ (s.1 false (xw s.2)) z i₁ i₂ hij
      (by rw [← f00, m00]) (by rw [← f10, m10]) (by rw [← f01, m01]) (by rw [← f11, m11])

/-! ### The headline: majority's boundary dimension is exactly 3 -/

/-- **Majority needs dimension 3 (proved)**: any observer computing `majFn n` (`n ≥ 5`) has dimension `≥ 3` — at
dimension `≤ 2` majority is impossible at every volume. -/
theorem maj_needs_dim_three (hn : 5 ≤ n) (t : Trans n) (hcomp : eval t = majFn n) :
    3 ≤ width t := by
  by_contra h
  push_neg at h
  obtain ⟨r0, q, hlen, hrun⟩ := w2_correspondence (by omega : 0 < n) t (by omega)
  exact w2_maj_impossible hn r0 q (fun x => by rw [hrun x, hcomp])

/-- **Majority's boundary dimension is exactly 3 (proved)** — the dimension ladder's middle rung, closed absolutely:
dimension 1 cannot do `x₀ ⊕ x₁`, dimension 2 cannot do majority, dimension 3 does everything. -/
theorem boundaryDim_maj_eq_three (hn : 5 ≤ n) : boundaryDim (majFn n) = 3 := by
  have hle := boundaryDim_le_three (majFn n)
  have hne : {w | ∃ t : Trans n, eval t = majFn n ∧ width t = w}.Nonempty :=
    ⟨width (dnfFor (majFn n)), dnfFor _, eval_dnfFor _, rfl⟩
  obtain ⟨t, ht, hwidth⟩ := Nat.sInf_mem hne
  have h3 := maj_needs_dim_three hn t ht
  unfold boundaryDim at hle ⊢
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.progPar_square
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.w2_maj_impossible
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.maj_needs_dim_three
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.boundaryDim_maj_eq_three
