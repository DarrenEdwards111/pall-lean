import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA4b

/-!
# Shrinkage brick A5a: the count-tracking kit

The iteration re-normalizes after every restriction, so normalization must
provably never introduce variables:

* `cntC_subst1_self`/`cntC_subst1_le` — substitution kills its own variable
  and never grows any count;
* `cntC_mkAnd_le`/`cntC_mkOr_le`/`cntC_simpC_le` — simplification never
  grows counts;
* **`fix_bad'`/`normalize'` (proved)** — the A3 theorems re-run with the
  count-monotonicity conclusion;
* `restrictF1` — the one-variable function restriction, with
  `restricted_tree_computes` connecting it to the tree surgery;
* `dmsizeC_leC`/`dmsizeC_const` — measure facts for the telescope base.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Count monotonicity -/

theorem cntC_subst1_self {n : ℕ} (i : Fin n) (b : Bool) (t : DMTreeC n) :
    cntC i (subst1 i b t) = 0 := by
  induction t with
  | lit j v =>
    by_cases hj : j = i
    · show cntC i (if j = i then (DMTreeC.cst (b == v) : DMTreeC n)
        else .lit j v) = 0
      rw [if_pos hj]
      rfl
    · show cntC i (if j = i then (DMTreeC.cst (b == v) : DMTreeC n)
        else .lit j v) = 0
      rw [if_neg hj]
      show (if j = i then 1 else 0) = 0
      rw [if_neg hj]
  | cst v => rfl
  | and l r ihl ihr =>
    show cntC i (subst1 i b l) + cntC i (subst1 i b r) = 0
    omega
  | or l r ihl ihr =>
    show cntC i (subst1 i b l) + cntC i (subst1 i b r) = 0
    omega

theorem cntC_subst1_le {n : ℕ} (j i : Fin n) (b : Bool) (t : DMTreeC n) :
    cntC j (subst1 i b t) ≤ cntC j t := by
  induction t with
  | lit k v =>
    by_cases hk : k = i
    · show cntC j (if k = i then (DMTreeC.cst (b == v) : DMTreeC n)
        else .lit k v) ≤ cntC j (.lit k v : DMTreeC n)
      rw [if_pos hk]
      exact Nat.zero_le _
    · show cntC j (if k = i then (DMTreeC.cst (b == v) : DMTreeC n)
        else .lit k v) ≤ cntC j (.lit k v : DMTreeC n)
      rw [if_neg hk]
  | cst v => exact le_refl _
  | and l r ihl ihr =>
    show cntC j (subst1 i b l) + cntC j (subst1 i b r)
      ≤ cntC j l + cntC j r
    omega
  | or l r ihl ihr =>
    show cntC j (subst1 i b l) + cntC j (subst1 i b r)
      ≤ cntC j l + cntC j r
    omega

theorem cntC_mkAnd_le {n : ℕ} (j : Fin n) (l r : DMTreeC n) :
    cntC j (mkAnd l r) ≤ cntC j l + cntC j r := by
  cases l with
  | cst v =>
    cases v
    · exact Nat.zero_le _
    · show cntC j r ≤ 0 + cntC j r
      omega
  | lit i b =>
    cases r with
    | cst v =>
      cases v
      · exact Nat.zero_le _
      · show cntC j (.lit i b : DMTreeC n) ≤ cntC j (.lit i b : DMTreeC n) + 0
        omega
    | lit k v => exact le_refl _
    | and a b' => exact le_refl _
    | or a b' => exact le_refl _
  | and a b' =>
    cases r with
    | cst v =>
      cases v
      · exact Nat.zero_le _
      · show cntC j (.and a b' : DMTreeC n) ≤ cntC j (.and a b') + 0
        omega
    | lit k v => exact le_refl _
    | and c d => exact le_refl _
    | or c d => exact le_refl _
  | or a b' =>
    cases r with
    | cst v =>
      cases v
      · exact Nat.zero_le _
      · show cntC j (.or a b' : DMTreeC n) ≤ cntC j (.or a b') + 0
        omega
    | lit k v => exact le_refl _
    | and c d => exact le_refl _
    | or c d => exact le_refl _

theorem cntC_mkOr_le {n : ℕ} (j : Fin n) (l r : DMTreeC n) :
    cntC j (mkOr l r) ≤ cntC j l + cntC j r := by
  cases l with
  | cst v =>
    cases v
    · show cntC j r ≤ 0 + cntC j r
      omega
    · exact Nat.zero_le _
  | lit i b =>
    cases r with
    | cst v =>
      cases v
      · show cntC j (.lit i b : DMTreeC n) ≤ cntC j (.lit i b : DMTreeC n) + 0
        omega
      · exact Nat.zero_le _
    | lit k v => exact le_refl _
    | and a b' => exact le_refl _
    | or a b' => exact le_refl _
  | and a b' =>
    cases r with
    | cst v =>
      cases v
      · show cntC j (.and a b' : DMTreeC n) ≤ cntC j (.and a b') + 0
        omega
      · exact Nat.zero_le _
    | lit k v => exact le_refl _
    | and c d => exact le_refl _
    | or c d => exact le_refl _
  | or a b' =>
    cases r with
    | cst v =>
      cases v
      · show cntC j (.or a b' : DMTreeC n) ≤ cntC j (.or a b') + 0
        omega
      · exact Nat.zero_le _
    | lit k v => exact le_refl _
    | and c d => exact le_refl _
    | or c d => exact le_refl _

theorem cntC_simpC_le {n : ℕ} (j : Fin n) (t : DMTreeC n) :
    cntC j (simpC t) ≤ cntC j t := by
  induction t with
  | lit i b => exact le_refl _
  | cst v => exact le_refl _
  | and l r ihl ihr =>
    show cntC j (mkAnd (simpC l) (simpC r)) ≤ cntC j l + cntC j r
    have h := cntC_mkAnd_le j (simpC l) (simpC r)
    omega
  | or l r ihl ihr =>
    show cntC j (mkOr (simpC l) (simpC r)) ≤ cntC j l + cntC j r
    have h := cntC_mkOr_le j (simpC l) (simpC r)
    omega

/-! ### Count-tracking normalization -/

/-- **`fix_bad` with count monotonicity (proved).** -/
theorem fix_bad' {n : ℕ} (t : DMTreeC n) (hbad : ¬ NormalAt t) :
    ∃ t₁ : DMTreeC n, (∀ x, t₁.eval x = t.eval x)
      ∧ t₁.lsize0 < t.lsize0 ∧ ∀ j, cntC j t₁ ≤ cntC j t := by
  induction t with
  | lit i b => exact absurd trivial hbad
  | cst v => exact absurd trivial hbad
  | and l r ihl ihr =>
    by_cases hnl : NormalAt l
    · by_cases hnr : NormalAt r
      · by_cases h1 : ∀ i b, l = .lit i b → cntC i r = 0
        · have h2 : ¬ ∀ i b, r = .lit i b → cntC i l = 0 := by
            intro h
            exact hbad ⟨hnl, hnr, h1, h⟩
          push_neg at h2
          obtain ⟨i, b, hrl, hcnt⟩ := h2
          subst hrl
          refine ⟨.and (subst1 i b l) (.lit i b),
            and_lit_subst_eval' i b l, ?_, ?_⟩
          · show (subst1 i b l).lsize0 + 1 < l.lsize0 + 1
            have := subst1_lsize0 i b l
            omega
          · intro j
            show cntC j (subst1 i b l) + cntC j (.lit i b : DMTreeC n)
              ≤ cntC j l + cntC j (.lit i b : DMTreeC n)
            have := cntC_subst1_le j i b l
            omega
        · push_neg at h1
          obtain ⟨i, b, hll, hcnt⟩ := h1
          subst hll
          refine ⟨.and (.lit i b) (subst1 i b r),
            and_lit_subst_eval i b r, ?_, ?_⟩
          · show 1 + (subst1 i b r).lsize0 < 1 + r.lsize0
            have := subst1_lsize0 i b r
            omega
          · intro j
            show cntC j (.lit i b : DMTreeC n) + cntC j (subst1 i b r)
              ≤ cntC j (.lit i b : DMTreeC n) + cntC j r
            have := cntC_subst1_le j i b r
            omega
      · obtain ⟨r₁, hr₁e, hr₁s, hr₁c⟩ := ihr hnr
        refine ⟨.and l r₁, ?_, ?_, ?_⟩
        · intro x
          show (l.eval x && r₁.eval x) = (l.eval x && r.eval x)
          rw [hr₁e]
        · show l.lsize0 + r₁.lsize0 < l.lsize0 + r.lsize0
          omega
        · intro j
          show cntC j l + cntC j r₁ ≤ cntC j l + cntC j r
          have := hr₁c j
          omega
    · obtain ⟨l₁, hl₁e, hl₁s, hl₁c⟩ := ihl hnl
      refine ⟨.and l₁ r, ?_, ?_, ?_⟩
      · intro x
        show (l₁.eval x && r.eval x) = (l.eval x && r.eval x)
        rw [hl₁e]
      · show l₁.lsize0 + r.lsize0 < l.lsize0 + r.lsize0
        omega
      · intro j
        show cntC j l₁ + cntC j r ≤ cntC j l + cntC j r
        have := hl₁c j
        omega
  | or l r ihl ihr =>
    by_cases hnl : NormalAt l
    · by_cases hnr : NormalAt r
      · by_cases h1 : ∀ i b, l = .lit i b → cntC i r = 0
        · have h2 : ¬ ∀ i b, r = .lit i b → cntC i l = 0 := by
            intro h
            exact hbad ⟨hnl, hnr, h1, h⟩
          push_neg at h2
          obtain ⟨i, b, hrl, hcnt⟩ := h2
          subst hrl
          refine ⟨.or (subst1 i (!b) l) (.lit i b),
            or_lit_subst_eval' i b l, ?_, ?_⟩
          · show (subst1 i (!b) l).lsize0 + 1 < l.lsize0 + 1
            have := subst1_lsize0 i (!b) l
            omega
          · intro j
            show cntC j (subst1 i (!b) l) + cntC j (.lit i b : DMTreeC n)
              ≤ cntC j l + cntC j (.lit i b : DMTreeC n)
            have := cntC_subst1_le j i (!b) l
            omega
        · push_neg at h1
          obtain ⟨i, b, hll, hcnt⟩ := h1
          subst hll
          refine ⟨.or (.lit i b) (subst1 i (!b) r),
            or_lit_subst_eval i b r, ?_, ?_⟩
          · show 1 + (subst1 i (!b) r).lsize0 < 1 + r.lsize0
            have := subst1_lsize0 i (!b) r
            omega
          · intro j
            show cntC j (.lit i b : DMTreeC n) + cntC j (subst1 i (!b) r)
              ≤ cntC j (.lit i b : DMTreeC n) + cntC j r
            have := cntC_subst1_le j i (!b) r
            omega
      · obtain ⟨r₁, hr₁e, hr₁s, hr₁c⟩ := ihr hnr
        refine ⟨.or l r₁, ?_, ?_, ?_⟩
        · intro x
          show (l.eval x || r₁.eval x) = (l.eval x || r.eval x)
          rw [hr₁e]
        · show l.lsize0 + r₁.lsize0 < l.lsize0 + r.lsize0
          omega
        · intro j
          show cntC j l + cntC j r₁ ≤ cntC j l + cntC j r
          have := hr₁c j
          omega
    · obtain ⟨l₁, hl₁e, hl₁s, hl₁c⟩ := ihl hnl
      refine ⟨.or l₁ r, ?_, ?_, ?_⟩
      · intro x
        show (l₁.eval x || r.eval x) = (l.eval x || r.eval x)
        rw [hl₁e]
      · show l₁.lsize0 + r.lsize0 < l.lsize0 + r.lsize0
        omega
      · intro j
        show cntC j l₁ + cntC j r ≤ cntC j l + cntC j r
        have := hl₁c j
        omega

theorem normalize'_aux {n : ℕ} :
    ∀ (L : ℕ) (t : DMTreeC n), t.lsize0 ≤ L →
      ∃ t' : DMTreeC n, (∀ x, t'.eval x = t.eval x) ∧ t'.lsize0 ≤ t.lsize0
        ∧ ((∃ v, t' = .cst v) ∨ (CstFree t' ∧ NormalAt t'))
        ∧ ∀ j, cntC j t' ≤ cntC j t := by
  intro L
  induction L with
  | zero =>
    intro t hL
    rcases simpC_cstFree t with ⟨v, hv⟩ | hcf
    · exact ⟨simpC t, simpC_eval t, simpC_lsize0 t, Or.inl ⟨v, hv⟩,
        fun j => cntC_simpC_le j t⟩
    · exfalso
      have h1 := cstFree_lsize0_pos _ hcf
      have h2 := simpC_lsize0 t
      omega
  | succ L ih =>
    intro t hL
    classical
    rcases simpC_cstFree t with ⟨v, hv⟩ | hcf
    · exact ⟨simpC t, simpC_eval t, simpC_lsize0 t, Or.inl ⟨v, hv⟩,
        fun j => cntC_simpC_le j t⟩
    · by_cases hnorm : NormalAt (simpC t)
      · exact ⟨simpC t, simpC_eval t, simpC_lsize0 t, Or.inr ⟨hcf, hnorm⟩,
          fun j => cntC_simpC_le j t⟩
      · obtain ⟨t₁, ht₁e, ht₁s, ht₁c⟩ := fix_bad' (simpC t) hnorm
        have hsi := simpC_lsize0 t
        obtain ⟨t', h1, h2, h3, h4⟩ := ih t₁ (by omega)
        refine ⟨t', ?_, by omega, h3, ?_⟩
        · intro x
          rw [h1 x, ht₁e x, simpC_eval]
        · intro j
          have ha := h4 j
          have hb := ht₁c j
          have hc := cntC_simpC_le j t
          omega

/-- **Count-tracking normalization (proved).** -/
theorem normalize' {n : ℕ} (t : DMTreeC n) :
    ∃ t' : DMTreeC n, (∀ x, t'.eval x = t.eval x) ∧ t'.lsize0 ≤ t.lsize0
      ∧ ((∃ v, t' = .cst v) ∨ (CstFree t' ∧ NormalAt t'))
      ∧ ∀ j, cntC j t' ≤ cntC j t :=
  normalize'_aux t.lsize0 t (le_refl _)

/-! ### Function-level restriction -/

/-- The one-variable restriction of a function. -/
def restrictF1 {n : ℕ} (i : Fin n) (b : Bool)
    (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => f (Function.update x i b)

theorem restricted_tree_computes {n : ℕ} (i : Fin n) (b : Bool)
    (t : DMTreeC n) (f : (Fin n → Bool) → Bool)
    (ht : ∀ x, t.eval x = f x) :
    ∀ x, (simpC (subst1 i b t)).eval x = restrictF1 i b f x := by
  intro x
  rw [simpC_eval, subst1_eval, ht]
  rfl

theorem dmsizeC_leC {n : ℕ} (f : (Fin n → Bool) → Bool) (t : DMTreeC n)
    (ht : ∀ x, t.eval x = f x) : dmsizeC f ≤ t.lsize0 :=
  Nat.sInf_le ⟨t, ht, rfl⟩

theorem dmsizeC_const {n : ℕ} (c : Bool) :
    dmsizeC (fun _ : Fin n → Bool => c) = 0 :=
  Nat.le_zero.mp (Nat.sInf_le ⟨.cst c, fun _ => rfl, rfl⟩)

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.normalize'
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.restricted_tree_computes
