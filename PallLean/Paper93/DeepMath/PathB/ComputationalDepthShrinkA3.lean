import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA2

/-!
# Shrinkage brick A3: normalization

Every formula can be brought to the shape the one-step accounting needs —
constant-free (unless trivial) with every literal's sibling free of that
literal's variable:

* `CstFree` / `NormalAt` — the two target predicates;
* **`and_lit_subst_eval` (+ dual/commuted, proved)** — the Subbotovskaya
  substitution identity `x∧g ≡ x∧(g↾_{x usable})`;
* **`fix_bad` (proved)** — a non-normal formula admits a STRICTLY smaller
  equivalent (the substitution kills ≥ 1 leaf — so termination is plain
  strong induction on `lsize0`, no composite measure);
* **`normalize` (proved)** — every formula has an equivalent, no-larger,
  constant-or-(CstFree ∧ Normal) form.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### The target predicates -/

/-- No constant leaves anywhere. -/
def CstFree {n : ℕ} : DMTreeC n → Prop
  | .lit _ _ => True
  | .cst _ => False
  | .and l r => CstFree l ∧ CstFree r
  | .or l r => CstFree l ∧ CstFree r

/-- Every literal child's sibling is free of the literal's variable. -/
def NormalAt {n : ℕ} : DMTreeC n → Prop
  | .lit _ _ => True
  | .cst _ => True
  | .and l r => NormalAt l ∧ NormalAt r
      ∧ (∀ i b, l = .lit i b → cntC i r = 0)
      ∧ (∀ i b, r = .lit i b → cntC i l = 0)
  | .or l r => NormalAt l ∧ NormalAt r
      ∧ (∀ i b, l = .lit i b → cntC i r = 0)
      ∧ (∀ i b, r = .lit i b → cntC i l = 0)

/-- A constant-free formula has at least one var leaf. -/
theorem cstFree_lsize0_pos {n : ℕ} (t : DMTreeC n) (h : CstFree t) :
    0 < t.lsize0 := by
  induction t with
  | lit i b => exact Nat.zero_lt_one
  | cst v => exact h.elim
  | and l r ihl ihr =>
    have h1 := ihl h.1
    show 0 < l.lsize0 + r.lsize0
    omega
  | or l r ihl ihr =>
    have h1 := ihl h.1
    show 0 < l.lsize0 + r.lsize0
    omega

/-! ### Constant-freeness of the simplification pass -/

theorem mkAnd_cstFree {n : ℕ} {l r : DMTreeC n} (hl : CstFree l)
    (hr : CstFree r) : CstFree (mkAnd l r) := by
  cases l <;> cases r <;> first
    | exact hl.elim
    | exact hr.elim
    | exact ⟨hl, hr⟩

theorem mkOr_cstFree {n : ℕ} {l r : DMTreeC n} (hl : CstFree l)
    (hr : CstFree r) : CstFree (mkOr l r) := by
  cases l <;> cases r <;> first
    | exact hl.elim
    | exact hr.elim
    | exact ⟨hl, hr⟩

/-- The simplification output is a constant or constant-free. -/
theorem simpC_cstFree {n : ℕ} (t : DMTreeC n) :
    (∃ v, simpC t = .cst v) ∨ CstFree (simpC t) := by
  induction t with
  | lit i b => exact Or.inr trivial
  | cst v => exact Or.inl ⟨v, rfl⟩
  | and l r ihl ihr =>
    show (∃ v, mkAnd (simpC l) (simpC r) = .cst v)
      ∨ CstFree (mkAnd (simpC l) (simpC r))
    rcases ihl with ⟨vl, hvl⟩ | hl
    · rw [hvl]
      cases vl
      · exact Or.inl ⟨false, rfl⟩
      · rcases ihr with ⟨vr, hvr⟩ | hr
        · rw [hvr]
          exact Or.inl ⟨vr, rfl⟩
        · exact Or.inr hr
    · rcases ihr with ⟨vr, hvr⟩ | hr
      · rw [hvr]
        cases vr
        · cases hsl : simpC l with
          | cst v =>
            rw [hsl] at hl
            exact hl.elim
          | lit i b => exact Or.inl ⟨false, rfl⟩
          | and a b => exact Or.inl ⟨false, rfl⟩
          | or a b => exact Or.inl ⟨false, rfl⟩
        · cases hsl : simpC l with
          | cst v =>
            rw [hsl] at hl
            exact hl.elim
          | lit i b =>
            rw [hsl] at hl
            exact Or.inr hl
          | and a b =>
            rw [hsl] at hl
            exact Or.inr hl
          | or a b =>
            rw [hsl] at hl
            exact Or.inr hl
      · exact Or.inr (mkAnd_cstFree hl hr)
  | or l r ihl ihr =>
    show (∃ v, mkOr (simpC l) (simpC r) = .cst v)
      ∨ CstFree (mkOr (simpC l) (simpC r))
    rcases ihl with ⟨vl, hvl⟩ | hl
    · rw [hvl]
      cases vl
      · rcases ihr with ⟨vr, hvr⟩ | hr
        · rw [hvr]
          exact Or.inl ⟨vr, rfl⟩
        · exact Or.inr hr
      · exact Or.inl ⟨true, rfl⟩
    · rcases ihr with ⟨vr, hvr⟩ | hr
      · rw [hvr]
        cases vr
        · cases hsl : simpC l with
          | cst v =>
            rw [hsl] at hl
            exact hl.elim
          | lit i b =>
            rw [hsl] at hl
            exact Or.inr hl
          | and a b =>
            rw [hsl] at hl
            exact Or.inr hl
          | or a b =>
            rw [hsl] at hl
            exact Or.inr hl
        · cases hsl : simpC l with
          | cst v =>
            rw [hsl] at hl
            exact hl.elim
          | lit i b => exact Or.inl ⟨true, rfl⟩
          | and a b => exact Or.inl ⟨true, rfl⟩
          | or a b => exact Or.inl ⟨true, rfl⟩
      · exact Or.inr (mkOr_cstFree hl hr)

/-! ### The substitution identities -/

theorem and_lit_subst_eval {n : ℕ} (i : Fin n) (b : Bool) (r : DMTreeC n)
    (x : Fin n → Bool) :
    (DMTreeC.and (.lit i b) (subst1 i b r)).eval x
      = (DMTreeC.and (.lit i b) r).eval x := by
  show ((x i == b) && (subst1 i b r).eval x) = ((x i == b) && r.eval x)
  rw [subst1_eval]
  by_cases hx : x i = b
  · have hup : Function.update x i b = x := by
      rw [← hx]
      exact Function.update_eq_self i x
    rw [hup]
  · have hlit : (x i == b) = false := by
      cases hxb : x i <;> cases hbv : b <;> simp_all
    rw [hlit, Bool.false_and, Bool.false_and]

theorem and_lit_subst_eval' {n : ℕ} (i : Fin n) (b : Bool) (l : DMTreeC n)
    (x : Fin n → Bool) :
    (DMTreeC.and (subst1 i b l) (.lit i b)).eval x
      = (DMTreeC.and l (.lit i b)).eval x := by
  show ((subst1 i b l).eval x && (x i == b)) = (l.eval x && (x i == b))
  rw [subst1_eval]
  by_cases hx : x i = b
  · have hup : Function.update x i b = x := by
      rw [← hx]
      exact Function.update_eq_self i x
    rw [hup]
  · have hlit : (x i == b) = false := by
      cases hxb : x i <;> cases hbv : b <;> simp_all
    rw [hlit, Bool.and_false, Bool.and_false]

theorem or_lit_subst_eval {n : ℕ} (i : Fin n) (b : Bool) (r : DMTreeC n)
    (x : Fin n → Bool) :
    (DMTreeC.or (.lit i b) (subst1 i (!b) r)).eval x
      = (DMTreeC.or (.lit i b) r).eval x := by
  show ((x i == b) || (subst1 i (!b) r).eval x) = ((x i == b) || r.eval x)
  rw [subst1_eval]
  by_cases hx : x i = b
  · have hlit : (x i == b) = true := by
      rw [hx]
      exact beq_self_eq_true b
    rw [hlit, Bool.true_or, Bool.true_or]
  · have hup : Function.update x i (!b) = x := by
      have hxv : x i = !b := by
        cases hxb : x i <;> cases hbv : b <;> simp_all
      rw [← hxv]
      exact Function.update_eq_self i x
    rw [hup]

theorem or_lit_subst_eval' {n : ℕ} (i : Fin n) (b : Bool) (l : DMTreeC n)
    (x : Fin n → Bool) :
    (DMTreeC.or (subst1 i (!b) l) (.lit i b)).eval x
      = (DMTreeC.or l (.lit i b)).eval x := by
  show ((subst1 i (!b) l).eval x || (x i == b)) = (l.eval x || (x i == b))
  rw [subst1_eval]
  by_cases hx : x i = b
  · have hlit : (x i == b) = true := by
      rw [hx]
      exact beq_self_eq_true b
    rw [hlit, Bool.or_true, Bool.or_true]
  · have hup : Function.update x i (!b) = x := by
      have hxv : x i = !b := by
        cases hxb : x i <;> cases hbv : b <;> simp_all
      rw [← hxv]
      exact Function.update_eq_self i x
    rw [hup]

/-! ### The strict-decrease step -/

/-- **A non-normal formula shrinks strictly (proved).** -/
theorem fix_bad {n : ℕ} (t : DMTreeC n) (hbad : ¬ NormalAt t) :
    ∃ t₁ : DMTreeC n, (∀ x, t₁.eval x = t.eval x)
      ∧ t₁.lsize0 < t.lsize0 := by
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
            and_lit_subst_eval' i b l, ?_⟩
          show (subst1 i b l).lsize0 + 1 < l.lsize0 + 1
          have := subst1_lsize0 i b l
          omega
        · push_neg at h1
          obtain ⟨i, b, hll, hcnt⟩ := h1
          subst hll
          refine ⟨.and (.lit i b) (subst1 i b r),
            and_lit_subst_eval i b r, ?_⟩
          show 1 + (subst1 i b r).lsize0 < 1 + r.lsize0
          have := subst1_lsize0 i b r
          omega
      · obtain ⟨r₁, hr₁e, hr₁s⟩ := ihr hnr
        refine ⟨.and l r₁, ?_, ?_⟩
        · intro x
          show (l.eval x && r₁.eval x) = (l.eval x && r.eval x)
          rw [hr₁e]
        · show l.lsize0 + r₁.lsize0 < l.lsize0 + r.lsize0
          omega
    · obtain ⟨l₁, hl₁e, hl₁s⟩ := ihl hnl
      refine ⟨.and l₁ r, ?_, ?_⟩
      · intro x
        show (l₁.eval x && r.eval x) = (l.eval x && r.eval x)
        rw [hl₁e]
      · show l₁.lsize0 + r.lsize0 < l.lsize0 + r.lsize0
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
            or_lit_subst_eval' i b l, ?_⟩
          show (subst1 i (!b) l).lsize0 + 1 < l.lsize0 + 1
          have := subst1_lsize0 i (!b) l
          omega
        · push_neg at h1
          obtain ⟨i, b, hll, hcnt⟩ := h1
          subst hll
          refine ⟨.or (.lit i b) (subst1 i (!b) r),
            or_lit_subst_eval i b r, ?_⟩
          show 1 + (subst1 i (!b) r).lsize0 < 1 + r.lsize0
          have := subst1_lsize0 i (!b) r
          omega
      · obtain ⟨r₁, hr₁e, hr₁s⟩ := ihr hnr
        refine ⟨.or l r₁, ?_, ?_⟩
        · intro x
          show (l.eval x || r₁.eval x) = (l.eval x || r.eval x)
          rw [hr₁e]
        · show l.lsize0 + r₁.lsize0 < l.lsize0 + r.lsize0
          omega
    · obtain ⟨l₁, hl₁e, hl₁s⟩ := ihl hnl
      refine ⟨.or l₁ r, ?_, ?_⟩
      · intro x
        show (l₁.eval x || r.eval x) = (l.eval x || r.eval x)
        rw [hl₁e]
      · show l₁.lsize0 + r.lsize0 < l.lsize0 + r.lsize0
        omega

/-! ### Normalization -/

theorem normalize_aux {n : ℕ} :
    ∀ (L : ℕ) (t : DMTreeC n), t.lsize0 ≤ L →
      ∃ t' : DMTreeC n, (∀ x, t'.eval x = t.eval x) ∧ t'.lsize0 ≤ t.lsize0
        ∧ ((∃ v, t' = .cst v) ∨ (CstFree t' ∧ NormalAt t')) := by
  intro L
  induction L with
  | zero =>
    intro t hL
    rcases simpC_cstFree t with ⟨v, hv⟩ | hcf
    · exact ⟨simpC t, simpC_eval t, simpC_lsize0 t, Or.inl ⟨v, hv⟩⟩
    · exfalso
      have h1 := cstFree_lsize0_pos _ hcf
      have h2 := simpC_lsize0 t
      omega
  | succ L ih =>
    intro t hL
    classical
    rcases simpC_cstFree t with ⟨v, hv⟩ | hcf
    · exact ⟨simpC t, simpC_eval t, simpC_lsize0 t, Or.inl ⟨v, hv⟩⟩
    · by_cases hnorm : NormalAt (simpC t)
      · exact ⟨simpC t, simpC_eval t, simpC_lsize0 t, Or.inr ⟨hcf, hnorm⟩⟩
      · obtain ⟨t₁, ht₁e, ht₁s⟩ := fix_bad (simpC t) hnorm
        have hsi := simpC_lsize0 t
        obtain ⟨t', h1, h2, h3⟩ := ih t₁ (by omega)
        refine ⟨t', ?_, by omega, h3⟩
        intro x
        rw [h1 x, ht₁e x, simpC_eval]

/-- **NORMALIZATION (proved)**: every formula has an equivalent, no-larger,
constant-or-normal form. -/
theorem normalize {n : ℕ} (t : DMTreeC n) :
    ∃ t' : DMTreeC n, (∀ x, t'.eval x = t.eval x) ∧ t'.lsize0 ≤ t.lsize0
      ∧ ((∃ v, t' = .cst v) ∨ (CstFree t' ∧ NormalAt t')) :=
  normalize_aux t.lsize0 t (le_refl _)

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.fix_bad
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.normalize
