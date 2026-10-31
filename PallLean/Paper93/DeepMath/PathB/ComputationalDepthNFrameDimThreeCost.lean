import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDim3Criterion

/-!
# N-Frame: the tearing-depth invariant — defined, tested, calibrated

Mountain-path staging (steps 2–5): before any SAT-side attack, the candidate obstruction measure must pass the
classification tests — it must *not* flag easy functions.  A raw count of odd squares fails immediately (`AND` has
exponentially many).  The honest measure is **robustness depth**: odd squares surviving *every* `k`-coordinate
restriction.

  `OddSquare f z i₁ i₂` — a 2×2 square with odd second difference (the tearing witness of the dimension theory).
  `Robust f k` — for every way of fixing at most `k` coordinates, an odd square survives on the free coordinates
        honouring the fixing — the graded tearing depth.
  `robust_one_hyperplaneSquares` / `boundaryDim_eq_three_of_robust` — **PROVED, the link**: depth-1 robustness is the
        dimension-3 criterion; every depth-1-robust function has boundary dimension exactly 3.

**The test battery (all PROVED — the step-5 gate):**
  `parityFn_no_oddSquare` / `parityFn_not_robust` — parity has **no odd squares at all** (affine): correctly classified
        easy — the invariant does not repeat sensitivity's mistake.
  `fullAnd_not_robust_one` — `AND` fails robustness already at depth 1 (`{x₀ = 0}` kills every square): correctly
        classified easy, despite its many raw odd squares.
  `majFn_robust` — majority is robust to depth `(n−3)/2` — **quantitative tearing depth ~n/2**, the graded
        strengthening of the dimension-3 criterion.

## Honest scope — the open cost interface, named

The tested invariant gives the *SAT-side* vocabulary (steps 3/6: clause-driven odd squares surviving restrictions).
The **cost side** (steps 2/4) — "volume `V` at dimension 3 ⇒ obstruction count ≤ `g(V)`" — is proved only at dimension
`≤ 2` (the `≤ length+1` affine classes of the normal form); the width-3 class decomposition, and any transfer of
robustness depth into a volume lower bound, are **open** — the genuine next structural targets, not claimed here.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### The tearing witness and the graded measure -/

/-- A 2×2 square with odd second difference — the tearing witness. -/
def OddSquare (f : (Fin n → Bool) → Bool) (z : Fin n → Bool) (i₁ i₂ : Fin n) : Prop :=
  i₁ ≠ i₂ ∧
  xor (xor (f z) (f (Function.update z i₁ true)))
    (xor (f (Function.update z i₂ true))
      (f (Function.update (Function.update z i₁ true) i₂ true))) = true

/-- **Robustness depth `k`**: for every fixing of at most `k` coordinates, an odd square survives on free coordinates
honouring the fixing. -/
def Robust (f : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ∀ (F : Finset (Fin n)) (ρ : Fin n → Bool), F.card ≤ k →
    ∃ (z : Fin n → Bool) (i₁ i₂ : Fin n),
      i₁ ∉ F ∧ i₂ ∉ F ∧ (∀ j ∈ F, z j = ρ j) ∧ OddSquare f z i₁ i₂

/-! ### The link to the dimension-3 criterion -/

/-- **Depth-1 robustness is the dimension-3 criterion (proved).** -/
theorem robust_one_hyperplaneSquares (f : (Fin n → Bool) → Bool) (h : Robust f 1) :
    HyperplaneSquares f := by
  intro w a
  obtain ⟨z, i₁, i₂, h1, h2, hagree, hne, hodd⟩ :=
    h {w} (fun _ => a) (by simp)
  exact ⟨z, i₁, i₂, hne, fun hc => h1 (hc ▸ Finset.mem_singleton_self w),
    fun hc => h2 (hc ▸ Finset.mem_singleton_self w),
    hagree w (Finset.mem_singleton_self w), hodd⟩

/-- **Depth-1-robust functions have boundary dimension exactly 3 (proved).** -/
theorem boundaryDim_eq_three_of_robust (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    (h : Robust f 1) : boundaryDim f = 3 :=
  boundaryDim_eq_three_of_hyperplaneSquares hn f (robust_one_hyperplaneSquares f h)

/-! ### Test 1: parity has no odd squares at all -/

/-- **Parity is never torn (proved)**: no odd square exists — the affine function is correctly classified easy. -/
theorem parityFn_no_oddSquare (hn : 0 < n) (z : Fin n → Bool) (i₁ i₂ : Fin n) :
    ¬ OddSquare (parityFn n) z i₁ i₂ := by
  rintro ⟨hne, hodd⟩
  by_cases h1 : z i₁ = true
  · -- the i₁-update is the identity: columns collapse
    have e := Function.update_eq_self i₁ z
    rw [h1] at e
    rw [e] at hodd
    generalize parityFn n z = p at hodd
    generalize parityFn n (Function.update z i₂ true) = q at hodd
    cases p <;> cases q <;> exact Bool.noConfusion hodd
  · by_cases h2 : z i₂ = true
    · -- the i₂-update is the identity
      have e := Function.update_eq_self i₂ z
      rw [h2] at e
      have hX : Function.update z i₁ true i₂ = true := by
        rw [Function.update_of_ne (fun hc => hne hc.symm)]
        exact h2
      have e2 := Function.update_eq_self i₂ (Function.update z i₁ true)
      rw [hX] at e2
      rw [e, e2] at hodd
      generalize parityFn n z = p at hodd
      generalize parityFn n (Function.update z i₁ true) = q at hodd
      cases p <;> cases q <;> exact Bool.noConfusion hodd
    · -- both fresh: two genuine flips cancel
      have hb1 : z i₁ = false := by
        cases hv : z i₁
        · rfl
        · exact absurd hv h1
      have hb2 : z i₂ = false := by
        cases hv : z i₂
        · rfl
        · exact absurd hv h2
      have e10 := parityFn_flip hn z i₁
      rw [hb1] at e10
      simp only [Bool.not_false] at e10
      have e01 := parityFn_flip hn z i₂
      rw [hb2] at e01
      simp only [Bool.not_false] at e01
      have hb2' : Function.update z i₁ true i₂ = false := by
        rw [Function.update_of_ne (fun hc => hne hc.symm)]
        exact hb2
      have e11 := parityFn_flip hn (Function.update z i₁ true) i₂
      rw [hb2'] at e11
      simp only [Bool.not_false] at e11
      rw [e10] at e11
      simp only [Bool.not_not] at e11
      rw [e10, e01, e11] at hodd
      generalize parityFn n z = p at hodd
      cases p <;> exact Bool.noConfusion hodd

/-- **Parity is not robust at any depth (proved)** — not even depth 0. -/
theorem parityFn_not_robust (hn : 0 < n) (k : ℕ) : ¬ Robust (parityFn n) k := by
  intro h
  obtain ⟨z, i₁, i₂, -, -, -, hodd⟩ := h ∅ (fun _ => false) (by simp)
  exact parityFn_no_oddSquare hn z i₁ i₂ hodd

/-! ### Test 2: AND fails robustness at depth 1 -/

theorem foldr_and_false (x : Fin n → Bool) (j : Fin n) (hj : x j = false) :
    ∀ l : List (Fin n), j ∈ l → l.foldr (fun i acc => x i && acc) true = false := by
  intro l
  induction l with
  | nil => intro hmem; exact absurd hmem List.not_mem_nil
  | cons a t ih =>
    intro hmem
    show (x a && _) = false
    rcases List.mem_cons.mp hmem with h | h
    · rw [h] at hj
      rw [hj]
      rfl
    · rw [ih h]
      simp

theorem fullAnd_false_of_coord (x : Fin n → Bool) (j : Fin n) (hj : x j = false) :
    fullAndFn n x = false :=
  foldr_and_false x j hj (List.finRange n) (List.mem_finRange j)

/-- **AND fails robustness at depth 1 (proved)**: fixing `x₀ = 0` kills every square — correctly classified easy,
despite its many raw odd squares. -/
theorem fullAnd_not_robust_one (hn : 0 < n) : ¬ Robust (fullAndFn n) 1 := by
  intro h
  obtain ⟨z, i₁, i₂, h1, h2, hagree, hne, hodd⟩ :=
    h {⟨0, hn⟩} (fun _ => false) (by simp)
  have hz0 : z ⟨0, hn⟩ = false := hagree _ (Finset.mem_singleton_self _)
  have hne1 : i₁ ≠ (⟨0, hn⟩ : Fin n) := fun hc => h1 (hc ▸ Finset.mem_singleton_self _)
  have hne2 : i₂ ≠ (⟨0, hn⟩ : Fin n) := fun hc => h2 (hc ▸ Finset.mem_singleton_self _)
  -- every corner keeps x₀ = 0, so AND is false on all four
  have c00 : fullAndFn n z = false := fullAnd_false_of_coord z _ hz0
  have c10 : fullAndFn n (Function.update z i₁ true) = false := by
    apply fullAnd_false_of_coord _ (⟨0, hn⟩ : Fin n)
    rw [Function.update_of_ne (fun hc => hne1 hc.symm)]
    exact hz0
  have c01 : fullAndFn n (Function.update z i₂ true) = false := by
    apply fullAnd_false_of_coord _ (⟨0, hn⟩ : Fin n)
    rw [Function.update_of_ne (fun hc => hne2 hc.symm)]
    exact hz0
  have c11 : fullAndFn n (Function.update (Function.update z i₁ true) i₂ true) = false := by
    apply fullAnd_false_of_coord _ (⟨0, hn⟩ : Fin n)
    rw [Function.update_of_ne (fun hc => hne2 hc.symm),
      Function.update_of_ne (fun hc => hne1 hc.symm)]
    exact hz0
  rw [c00, c10, c01, c11] at hodd
  exact Bool.noConfusion hodd

/-! ### Test 3: majority is robust to depth (n−3)/2 -/

/-- **Majority's quantitative tearing depth (proved)**: robust to depth `(n−3)/2` — odd squares survive every such
restriction.  The graded strengthening of the dimension-3 criterion. -/
theorem majFn_robust (hn : 5 ≤ n) (k : ℕ) (hk : k ≤ (n - 3) / 2) :
    Robust (majFn n) k := by
  intro F ρ hF
  -- two fresh coordinates
  have hsd : ((Finset.univ : Finset (Fin n)) \ F).card = n - F.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hfree : 1 < ((Finset.univ : Finset (Fin n)) \ F).card := by
    rw [hsd]
    omega
  obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := Finset.one_lt_card.mp hfree
  have h1F : i₁ ∉ F := (Finset.mem_sdiff.mp hi₁).2
  have h2F : i₂ ∉ F := (Finset.mem_sdiff.mp hi₂).2
  -- the padding pool
  set others := ((((Finset.univ : Finset (Fin n)) \ F).erase i₁).erase i₂) with hoth
  have hmem2 : i₂ ∈ ((Finset.univ : Finset (Fin n)) \ F).erase i₁ :=
    Finset.mem_erase.mpr ⟨fun hc => hne (hc ▸ rfl), hi₂⟩
  have hcard_others : others.card = n - F.card - 2 := by
    rw [hoth, Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hi₁, hsd]
    omega
  -- the forced ones and the padding
  set Fones := F.filter (fun j => ρ j = true) with hFones
  have hcF : Fones.card ≤ k := le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hF
  have hpad : (n + 1) / 2 - 2 - Fones.card ≤ others.card := by
    rw [hcard_others]
    omega
  obtain ⟨S, hS, hScard⟩ := Finset.le_card_iff_exists_subset_card.mp hpad
  -- membership facts
  have hS_not_F : ∀ j ∈ S, j ∉ F := by
    intro j hj
    have := hS hj
    rw [hoth, Finset.mem_erase, Finset.mem_erase, Finset.mem_sdiff] at this
    exact this.2.2.2
  have hS_not_1 : i₁ ∉ S := fun hc => by
    have := hS hc
    rw [hoth, Finset.mem_erase, Finset.mem_erase] at this
    exact this.2.1 rfl
  have hS_not_2 : i₂ ∉ S := fun hc => by
    have := hS hc
    rw [hoth, Finset.mem_erase] at this
    exact this.1 rfl
  have hdisj : Disjoint Fones S := by
    rw [Finset.disjoint_left]
    intro j hj hjS
    exact hS_not_F j hjS (Finset.mem_filter.mp hj).1
  set zSet := Fones ∪ S with hzSet
  refine ⟨fun i => decide (i ∈ zSet), i₁, i₂, h1F, h2F, ?_, hne, ?_⟩
  · -- honours the fixing
    intro j hj
    have hjS : j ∉ S := fun hc => hS_not_F j hc hj
    rw [hzSet]
    cases hρ : ρ j
    · have : j ∉ Fones := by
        rw [hFones, Finset.mem_filter]
        rintro ⟨-, hc⟩
        rw [hρ] at hc
        exact Bool.noConfusion hc
      simp [Finset.mem_union, this, hjS]
    · have : j ∈ Fones := by
        rw [hFones, Finset.mem_filter]
        exact ⟨hj, hρ⟩
      simp [Finset.mem_union, this]
  · -- the odd square: counts T−2, T−1, T−1, T
    have h1z : (fun i => decide (i ∈ zSet)) i₁ = false := by
      have : i₁ ∉ zSet := by
        rw [hzSet, Finset.mem_union]
        rintro (hc | hc)
        · exact h1F (Finset.mem_filter.mp hc).1
        · exact hS_not_1 hc
      simp [this]
    have h2z : (fun i => decide (i ∈ zSet)) i₂ = false := by
      have : i₂ ∉ zSet := by
        rw [hzSet, Finset.mem_union]
        rintro (hc | hc)
        · exact h2F (Finset.mem_filter.mp hc).1
        · exact hS_not_2 hc
      simp [this]
    have hcount : (onesOf (fun i => decide (i ∈ zSet))).card = (n + 1) / 2 - 2 := by
      have hones : onesOf (fun i => decide (i ∈ zSet)) = zSet := by
        ext i
        simp [onesOf]
      rw [hones, hzSet, Finset.card_union_of_disjoint hdisj, hScard]
      omega
    have c10 : (onesOf (Function.update (fun i => decide (i ∈ zSet)) i₁ true)).card
        = (n + 1) / 2 - 1 := by
      rw [card_onesOf_update_true _ i₁ h1z, hcount]
      omega
    have c11 : (onesOf (Function.update (Function.update (fun i => decide (i ∈ zSet)) i₁ true)
        i₂ true)).card = (n + 1) / 2 := by
      rw [card_onesOf_update_true _ i₂ (by
        rw [Function.update_of_ne (fun hc => hne hc.symm)]
        exact h2z), c10]
      omega
    have c01 : (onesOf (Function.update (fun i => decide (i ∈ zSet)) i₂ true)).card
        = (n + 1) / 2 - 1 := by
      rw [card_onesOf_update_true _ i₂ h2z, hcount]
      omega
    have m00 : majFn n (fun i => decide (i ∈ zSet)) = false := by
      rw [majFn_eq_decide, hcount]
      simp only [decide_eq_false_iff_not]
      omega
    have m10 : majFn n (Function.update (fun i => decide (i ∈ zSet)) i₁ true) = false := by
      rw [majFn_eq_decide, c10]
      simp only [decide_eq_false_iff_not]
      omega
    have m01 : majFn n (Function.update (fun i => decide (i ∈ zSet)) i₂ true) = false := by
      rw [majFn_eq_decide, c01]
      simp only [decide_eq_false_iff_not]
      omega
    have m11 : majFn n (Function.update (Function.update (fun i => decide (i ∈ zSet)) i₁ true)
        i₂ true) = true := by
      rw [majFn_eq_decide, c11]
      simp
    rw [m00, m10, m01, m11]
    rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.parityFn_not_robust
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.fullAnd_not_robust_one
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.majFn_robust
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.boundaryDim_eq_three_of_robust
