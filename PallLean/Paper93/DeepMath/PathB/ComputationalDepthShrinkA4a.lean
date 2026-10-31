import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA3

/-!
# Shrinkage brick A4a: the one-step kit

The identities and point computations the integer one-step accounting sums:

* `subst1_of_cnt_zero` / `simpC_of_cstFree` — absent substitution and
  simplification are the identity;
* `litInd` — the literal indicator carrying the `+1` slack;
* the `mkAnd`/`mkOr` constant-value laws (left constants reduce
  definitionally; right constants by shape case analysis);
* **`and_lit_point`/`and_lit_point'`/`or_lit_point`/`or_lit_point'`
  (proved)** — the EXACT budget at a literal child's own variable: the two
  restrictions of that variable spend the sibling's full size as slack;
* `sum_slack_one`/`sum_slack_two` — slack-extracting sum comparisons.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Identity laws -/

theorem subst1_of_cnt_zero {n : ℕ} (i : Fin n) (b : Bool) (t : DMTreeC n)
    (h : cntC i t = 0) : subst1 i b t = t := by
  induction t with
  | lit j v =>
    have hji : ¬ (j = i) := by
      intro hji
      have h' : (if j = i then 1 else 0) = 0 := h
      rw [if_pos hji] at h'
      exact Nat.one_ne_zero h'
    show (if j = i then (DMTreeC.cst (b == v) : DMTreeC n)
      else .lit j v) = .lit j v
    rw [if_neg hji]
  | cst v => rfl
  | and l r ihl ihr =>
    have h' : cntC i l + cntC i r = 0 := h
    show DMTreeC.and (subst1 i b l) (subst1 i b r) = .and l r
    rw [ihl (by omega), ihr (by omega)]
  | or l r ihl ihr =>
    have h' : cntC i l + cntC i r = 0 := h
    show DMTreeC.or (subst1 i b l) (subst1 i b r) = .or l r
    rw [ihl (by omega), ihr (by omega)]

theorem simpC_of_cstFree {n : ℕ} (t : DMTreeC n) (h : CstFree t) :
    simpC t = t := by
  induction t with
  | lit i b => rfl
  | cst v => exact h.elim
  | and l r ihl ihr =>
    show mkAnd (simpC l) (simpC r) = .and l r
    rw [ihl h.1, ihr h.2]
    cases l with
    | cst v => exact h.1.elim
    | lit i b =>
      cases r with
      | cst w => exact h.2.elim
      | lit j v => rfl
      | and a b' => rfl
      | or a b' => rfl
    | and a b' =>
      cases r with
      | cst w => exact h.2.elim
      | lit j v => rfl
      | and c d => rfl
      | or c d => rfl
    | or a b' =>
      cases r with
      | cst w => exact h.2.elim
      | lit j v => rfl
      | and c d => rfl
      | or c d => rfl
  | or l r ihl ihr =>
    show mkOr (simpC l) (simpC r) = .or l r
    rw [ihl h.1, ihr h.2]
    cases l with
    | cst v => exact h.1.elim
    | lit i b =>
      cases r with
      | cst w => exact h.2.elim
      | lit j v => rfl
      | and a b' => rfl
      | or a b' => rfl
    | and a b' =>
      cases r with
      | cst w => exact h.2.elim
      | lit j v => rfl
      | and c d => rfl
      | or c d => rfl
    | or a b' =>
      cases r with
      | cst w => exact h.2.elim
      | lit j v => rfl
      | and c d => rfl
      | or c d => rfl

/-! ### The literal indicator and small laws -/

/-- The `+1` slack indicator. -/
def litInd {n : ℕ} : DMTreeC n → ℕ
  | .lit _ _ => 1
  | _ => 0

theorem subst1_lit_self {n : ℕ} (j : Fin n) (v b : Bool) :
    subst1 j b (.lit j v : DMTreeC n) = .cst (b == v) := by
  show (if j = j then (DMTreeC.cst (b == v) : DMTreeC n)
    else .lit j v) = .cst (b == v)
  rw [if_pos rfl]

theorem cntC_lit_self {n : ℕ} (j : Fin n) (v : Bool) :
    cntC j (.lit j v : DMTreeC n) = 1 := by
  show (if j = j then 1 else 0) = 1
  rw [if_pos rfl]

theorem lsize0_mkAnd_cstfalse_right {n : ℕ} (A : DMTreeC n) :
    (mkAnd A (.cst false)).lsize0 = 0 := by
  cases A with
  | cst v => cases v <;> rfl
  | lit i b => rfl
  | and a b => rfl
  | or a b => rfl

theorem lsize0_mkAnd_csttrue_right {n : ℕ} (A : DMTreeC n) :
    (mkAnd A (.cst true)).lsize0 = A.lsize0 := by
  cases A with
  | cst v => cases v <;> rfl
  | lit i b => rfl
  | and a b => rfl
  | or a b => rfl

theorem lsize0_mkOr_csttrue_right {n : ℕ} (A : DMTreeC n) :
    (mkOr A (.cst true)).lsize0 = 0 := by
  cases A with
  | cst v => cases v <;> rfl
  | lit i b => rfl
  | and a b => rfl
  | or a b => rfl

theorem lsize0_mkOr_cstfalse_right {n : ℕ} (A : DMTreeC n) :
    (mkOr A (.cst false)).lsize0 = A.lsize0 := by
  cases A with
  | cst v => cases v <;> rfl
  | lit i b => rfl
  | and a b => rfl
  | or a b => rfl

/-! ### The literal-point budgets -/

/-- **The exact budget at a left literal's own variable (AND, proved)**:
the two restrictions spend the sibling's full size. -/
theorem and_lit_point {n : ℕ} (j : Fin n) (v : Bool) (r : DMTreeC n)
    (hcfr : CstFree r) (hcnt : cntC j r = 0) :
    (simpC (subst1 j false (.and (.lit j v) r))).lsize0
      + (simpC (subst1 j true (.and (.lit j v) r))).lsize0
      + r.lsize0
    = ((simpC (subst1 j false (.lit j v : DMTreeC n))).lsize0
      + (simpC (subst1 j true (.lit j v : DMTreeC n))).lsize0)
      + ((simpC (subst1 j false r)).lsize0
      + (simpC (subst1 j true r)).lsize0) := by
  have hs0 := subst1_of_cnt_zero j false r hcnt
  have hs1 := subst1_of_cnt_zero j true r hcnt
  have hsi := simpC_of_cstFree r hcfr
  have hc : ∀ b, simpC (subst1 j b (.and (.lit j v) r))
      = mkAnd (.cst (b == v)) r := by
    intro b
    show mkAnd (simpC (subst1 j b (.lit j v))) (simpC (subst1 j b r)) = _
    rw [subst1_lit_self]
    cases b
    · rw [hs0, hsi]
      rfl
    · rw [hs1, hsi]
      rfl
  have hA : ∀ b, (simpC (subst1 j b (.lit j v : DMTreeC n))).lsize0 = 0 := by
    intro b
    rw [subst1_lit_self]
    rfl
  have hB0 : (simpC (subst1 j false r)).lsize0 = r.lsize0 := by
    rw [hs0, hsi]
  have hB1 : (simpC (subst1 j true r)).lsize0 = r.lsize0 := by
    rw [hs1, hsi]
  rw [hc false, hc true, hA false, hA true, hB0, hB1]
  cases v
  · have e1 : (mkAnd (.cst (false == false)) r).lsize0 = r.lsize0 := rfl
    have e2 : (mkAnd (.cst (true == false)) r).lsize0 = 0 := rfl
    rw [e1, e2]
    omega
  · have e1 : (mkAnd (.cst (false == true)) r).lsize0 = 0 := rfl
    have e2 : (mkAnd (.cst (true == true)) r).lsize0 = r.lsize0 := rfl
    rw [e1, e2]
    omega

/-- **The exact budget at a right literal's own variable (AND, proved).** -/
theorem and_lit_point' {n : ℕ} (j : Fin n) (v : Bool) (l : DMTreeC n)
    (hcfl : CstFree l) (hcnt : cntC j l = 0) :
    (simpC (subst1 j false (.and l (.lit j v)))).lsize0
      + (simpC (subst1 j true (.and l (.lit j v)))).lsize0
      + l.lsize0
    = ((simpC (subst1 j false l)).lsize0
      + (simpC (subst1 j true l)).lsize0)
      + ((simpC (subst1 j false (.lit j v : DMTreeC n))).lsize0
      + (simpC (subst1 j true (.lit j v : DMTreeC n))).lsize0) := by
  have hs0 := subst1_of_cnt_zero j false l hcnt
  have hs1 := subst1_of_cnt_zero j true l hcnt
  have hsi := simpC_of_cstFree l hcfl
  have hc : ∀ b, simpC (subst1 j b (.and l (.lit j v)))
      = mkAnd l (.cst (b == v)) := by
    intro b
    show mkAnd (simpC (subst1 j b l)) (simpC (subst1 j b (.lit j v))) = _
    rw [subst1_lit_self]
    cases b
    · rw [hs0, hsi]
      rfl
    · rw [hs1, hsi]
      rfl
  have hA : ∀ b, (simpC (subst1 j b (.lit j v : DMTreeC n))).lsize0 = 0 := by
    intro b
    rw [subst1_lit_self]
    rfl
  have hB0 : (simpC (subst1 j false l)).lsize0 = l.lsize0 := by
    rw [hs0, hsi]
  have hB1 : (simpC (subst1 j true l)).lsize0 = l.lsize0 := by
    rw [hs1, hsi]
  rw [hc false, hc true, hA false, hA true, hB0, hB1]
  cases v
  · have e1 : (mkAnd l (.cst (false == false))).lsize0 = l.lsize0 :=
      lsize0_mkAnd_csttrue_right l
    have e2 : (mkAnd l (.cst (true == false))).lsize0 = 0 :=
      lsize0_mkAnd_cstfalse_right l
    rw [e1, e2]
    omega
  · have e1 : (mkAnd l (.cst (false == true))).lsize0 = 0 :=
      lsize0_mkAnd_cstfalse_right l
    have e2 : (mkAnd l (.cst (true == true))).lsize0 = l.lsize0 :=
      lsize0_mkAnd_csttrue_right l
    rw [e1, e2]
    omega

/-- **The exact budget at a left literal's own variable (OR, proved).** -/
theorem or_lit_point {n : ℕ} (j : Fin n) (v : Bool) (r : DMTreeC n)
    (hcfr : CstFree r) (hcnt : cntC j r = 0) :
    (simpC (subst1 j false (.or (.lit j v) r))).lsize0
      + (simpC (subst1 j true (.or (.lit j v) r))).lsize0
      + r.lsize0
    = ((simpC (subst1 j false (.lit j v : DMTreeC n))).lsize0
      + (simpC (subst1 j true (.lit j v : DMTreeC n))).lsize0)
      + ((simpC (subst1 j false r)).lsize0
      + (simpC (subst1 j true r)).lsize0) := by
  have hs0 := subst1_of_cnt_zero j false r hcnt
  have hs1 := subst1_of_cnt_zero j true r hcnt
  have hsi := simpC_of_cstFree r hcfr
  have hc : ∀ b, simpC (subst1 j b (.or (.lit j v) r))
      = mkOr (.cst (b == v)) r := by
    intro b
    show mkOr (simpC (subst1 j b (.lit j v))) (simpC (subst1 j b r)) = _
    rw [subst1_lit_self]
    cases b
    · rw [hs0, hsi]
      rfl
    · rw [hs1, hsi]
      rfl
  have hA : ∀ b, (simpC (subst1 j b (.lit j v : DMTreeC n))).lsize0 = 0 := by
    intro b
    rw [subst1_lit_self]
    rfl
  have hB0 : (simpC (subst1 j false r)).lsize0 = r.lsize0 := by
    rw [hs0, hsi]
  have hB1 : (simpC (subst1 j true r)).lsize0 = r.lsize0 := by
    rw [hs1, hsi]
  rw [hc false, hc true, hA false, hA true, hB0, hB1]
  cases v
  · have e1 : (mkOr (.cst (false == false)) r).lsize0 = 0 := rfl
    have e2 : (mkOr (.cst (true == false)) r).lsize0 = r.lsize0 := rfl
    rw [e1, e2]
    omega
  · have e1 : (mkOr (.cst (false == true)) r).lsize0 = r.lsize0 := rfl
    have e2 : (mkOr (.cst (true == true)) r).lsize0 = 0 := rfl
    rw [e1, e2]
    omega

/-- **The exact budget at a right literal's own variable (OR, proved).** -/
theorem or_lit_point' {n : ℕ} (j : Fin n) (v : Bool) (l : DMTreeC n)
    (hcfl : CstFree l) (hcnt : cntC j l = 0) :
    (simpC (subst1 j false (.or l (.lit j v)))).lsize0
      + (simpC (subst1 j true (.or l (.lit j v)))).lsize0
      + l.lsize0
    = ((simpC (subst1 j false l)).lsize0
      + (simpC (subst1 j true l)).lsize0)
      + ((simpC (subst1 j false (.lit j v : DMTreeC n))).lsize0
      + (simpC (subst1 j true (.lit j v : DMTreeC n))).lsize0) := by
  have hs0 := subst1_of_cnt_zero j false l hcnt
  have hs1 := subst1_of_cnt_zero j true l hcnt
  have hsi := simpC_of_cstFree l hcfl
  have hc : ∀ b, simpC (subst1 j b (.or l (.lit j v)))
      = mkOr l (.cst (b == v)) := by
    intro b
    show mkOr (simpC (subst1 j b l)) (simpC (subst1 j b (.lit j v))) = _
    rw [subst1_lit_self]
    cases b
    · rw [hs0, hsi]
      rfl
    · rw [hs1, hsi]
      rfl
  have hA : ∀ b, (simpC (subst1 j b (.lit j v : DMTreeC n))).lsize0 = 0 := by
    intro b
    rw [subst1_lit_self]
    rfl
  have hB0 : (simpC (subst1 j false l)).lsize0 = l.lsize0 := by
    rw [hs0, hsi]
  have hB1 : (simpC (subst1 j true l)).lsize0 = l.lsize0 := by
    rw [hs1, hsi]
  rw [hc false, hc true, hA false, hA true, hB0, hB1]
  cases v
  · have e1 : (mkOr l (.cst (false == false))).lsize0 = 0 :=
      lsize0_mkOr_csttrue_right l
    have e2 : (mkOr l (.cst (true == false))).lsize0 = l.lsize0 :=
      lsize0_mkOr_cstfalse_right l
    rw [e1, e2]
    omega
  · have e1 : (mkOr l (.cst (false == true))).lsize0 = l.lsize0 :=
      lsize0_mkOr_cstfalse_right l
    have e2 : (mkOr l (.cst (true == true))).lsize0 = 0 :=
      lsize0_mkOr_csttrue_right l
    rw [e1, e2]
    omega

/-! ### Slack-extracting sums -/

theorem sum_slack_one {α : Type*} [DecidableEq α] (I : Finset α)
    (f g : α → ℕ) (κ : ℕ) (hpt : ∀ p ∈ I, f p ≤ g p)
    (p₀ : α) (h₀ : p₀ ∈ I) (hs : f p₀ + κ ≤ g p₀) :
    (∑ p ∈ I, f p) + κ ≤ ∑ p ∈ I, g p := by
  rw [← Finset.add_sum_erase I f h₀, ← Finset.add_sum_erase I g h₀]
  have hrest : ∑ p ∈ I.erase p₀, f p ≤ ∑ p ∈ I.erase p₀, g p :=
    Finset.sum_le_sum (fun p hp => hpt p (Finset.mem_of_mem_erase hp))
  omega

theorem sum_slack_two {α : Type*} [DecidableEq α] (I : Finset α)
    (f g : α → ℕ) (κ₀ κ₁ : ℕ) (hpt : ∀ p ∈ I, f p ≤ g p)
    (p₀ p₁ : α) (hne : p₀ ≠ p₁) (h₀ : p₀ ∈ I) (h₁ : p₁ ∈ I)
    (hs₀ : f p₀ + κ₀ ≤ g p₀) (hs₁ : f p₁ + κ₁ ≤ g p₁) :
    (∑ p ∈ I, f p) + κ₀ + κ₁ ≤ ∑ p ∈ I, g p := by
  rw [← Finset.add_sum_erase I f h₀, ← Finset.add_sum_erase I g h₀]
  have h₁' : p₁ ∈ I.erase p₀ := Finset.mem_erase.mpr ⟨fun h => hne h.symm, h₁⟩
  have hrest := sum_slack_one (I.erase p₀) f g κ₁
    (fun p hp => hpt p (Finset.mem_of_mem_erase hp)) p₁ h₁' hs₁
  omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.and_lit_point
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.or_lit_point'
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.sum_slack_two
