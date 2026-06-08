import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CodeCount

/-!
# Block-DT model, foundation 54: branching holography, step 4l — the label cardinality (branch only)

The concrete `w`-dependent label bound, assembled into the switching count.  A code stream (`≤ F` blocks,
each code `≤ w` ternary slots) is encoded by its `getElem?` profile into the *finite* type
`Fin F → Option (Fin w → Option (Option Bool))` (card `(4^w + 1)^F`), and this encoding is injective on
valid streams — so the label space has cardinality `≤ (4^w + 1)^F`.

* `codeEnc` / `codeEnc_inj` — the `getElem?`-profile encoding and its injectivity on valid streams.
* `codesList_length_le` / `codesList_code_length_le` — code streams are valid (`≤ F` blocks, codes `≤ w`).
* `descent_switching_count` — `|Bad| ≤ |Short| · (4^w + 1)^F`: the bad restrictions, counted by a
  `w`-dependent label space.

This closes the *counting* side of the branching switching lemma (modulo the constant base `4` vs Håstad's
optimal): `|Bad| ≤ |Short| · (poly-in-`2^w`)^F`, with the label space `w`-dependent (not `n`-dependent).
The remaining gap is the **p-biased measure** turning `|Short| / |all|` into the probability factor.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Encode a code stream by its `getElem?` profile into a fixed finite function type. -/
def codeEnc (F w : ℕ) (L : List (List (Option Bool))) :
    Fin F → Option (Fin w → Option (Option Bool)) :=
  fun i => (getElem? L i.val).map (fun c => fun j : Fin w => getElem? c j.val)

/-- Two codes of length `≤ w` agreeing on all `Fin w` positions are equal. -/
theorem code_ext {w : ℕ} {c1 c2 : List (Option Bool)} (hl1 : c1.length ≤ w) (hl2 : c2.length ≤ w)
    (h : ∀ j : Fin w, getElem? c1 j.val = getElem? c2 j.val) : c1 = c2 := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < w
  · exact h ⟨j, hj⟩
  · rw [List.getElem?_eq_none_iff.mpr (le_trans hl1 (not_lt.mp hj)),
        List.getElem?_eq_none_iff.mpr (le_trans hl2 (not_lt.mp hj))]

/-- **The encoding is injective on valid code streams.** -/
theorem codeEnc_inj {F w : ℕ} {L1 L2 : List (List (Option Bool))}
    (h1 : L1.length ≤ F) (h2 : L2.length ≤ F)
    (hc1 : ∀ c ∈ L1, c.length ≤ w) (hc2 : ∀ c ∈ L2, c.length ≤ w)
    (heq : codeEnc F w L1 = codeEnc F w L2) : L1 = L2 := by
  apply List.ext_getElem?
  intro i
  by_cases hiF : i < F
  · have hcong := congrFun heq ⟨i, hiF⟩
    simp only [codeEnc] at hcong
    cases h1i : getElem? L1 i with
    | none =>
      cases h2i : getElem? L2 i with
      | none => rfl
      | some c2 => rw [h1i, h2i] at hcong; simp at hcong
    | some c1 =>
      cases h2i : getElem? L2 i with
      | none => rw [h1i, h2i] at hcong; simp at hcong
      | some c2 =>
        rw [h1i, h2i] at hcong
        simp only [Option.map_some] at hcong
        have hcong2 := Option.some.inj hcong
        have he : c1 = c2 :=
          code_ext (hc1 c1 (List.mem_of_getElem? h1i)) (hc2 c2 (List.mem_of_getElem? h2i))
            (fun j => congrFun hcong2 j)
        rw [he]
  · rw [List.getElem?_eq_none_iff.mpr (le_trans h1 (not_lt.mp hiF)),
        List.getElem?_eq_none_iff.mpr (le_trans h2 (not_lt.mp hiF))]

/-- Code streams have at most `F` blocks. -/
theorem codesList_length_le (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool), (codesList cs w F σ x).length ≤ F := by
  intro F
  induction F with
  | zero => intro σ x; simp [codesList]
  | succ F ih =>
    intro σ x
    rw [codesList]
    cases hany : anyTermSat cs σ with
    | true => simp
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp
      | some T =>
        simp only [Bool.false_eq_true, if_false, List.length_cons]
        have := ih (extendσ σ T x) x
        omega

/-- Each code has at most `w` slots (for width-`≤ w` clauses). -/
theorem codesList_code_length_le (cs : List (Clause n)) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      ∀ c ∈ codesList cs w F σ x, c.length ≤ w := by
  intro F
  induction F with
  | zero => intro σ x c hc; rw [codesList] at hc; simp at hc
  | succ F ih =>
    intro σ x c hc
    rw [codesList] at hc
    cases hany : anyTermSat cs σ with
    | true => rw [hany] at hc; simp at hc
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp only [hany, Bool.false_eq_true, if_false, hact] at hc; simp at hc
      | some T =>
        simp only [hany, Bool.false_eq_true, if_false, hact, List.mem_cons] at hc
        cases hc with
        | inl h => rw [h, maskOnTerm, List.length_map]; exact hw T (activeTerm_mem hact)
        | inr h => exact ih (extendσ σ T x) x c h

/-- **The branching switching count.**  The bad restrictions inject into `Short × Labels` with `Labels`
the code streams, whose cardinality is `≤ (4^w + 1)^F` — a `w`-dependent label space. -/
theorem descent_switching_count (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T) (w F : ℕ)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    {Bad Short : Finset (Fin n → Option Bool)} (xσ : (Fin n → Option Bool) → (Fin n → Bool))
    (hS : ∀ σ ∈ Bad, descentSat cs w F σ (xσ σ) ∈ Short) :
    Bad.card ≤ Short.card * (4 ^ w + 1) ^ F := by
  classical
  set Labels : Finset (List (List (Option Bool))) :=
    Bad.image (fun σ => codesList cs w F σ (xσ σ)) with hLabels
  have hL : ∀ σ ∈ Bad, codesList cs w F σ (xσ σ) ∈ Labels :=
    fun σ hσ => Finset.mem_image_of_mem _ hσ
  have hcount := descent_code_count cs hcons w F xσ hS hL
  have hLcard : Labels.card ≤ Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (codeEnc F w) (fun L _ => Finset.mem_univ _)
      (fun L1 hL1 L2 hL2 heq => ?_)
    simp only [hLabels, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hL1 hL2
    obtain ⟨σ1, _, rfl⟩ := hL1
    obtain ⟨σ2, _, rfl⟩ := hL2
    exact codeEnc_inj (codesList_length_le cs w F σ1 (xσ σ1)) (codesList_length_le cs w F σ2 (xσ σ2))
      (codesList_code_length_le cs w hw F σ1 (xσ σ1)) (codesList_code_length_le cs w hw F σ2 (xσ σ2)) heq
  have hcardeq : Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) = (4 ^ w + 1) ^ F := by
    rw [Fintype.card_pi_const, Fintype.card_option, Fintype.card_pi_const, Fintype.card_option,
      Fintype.card_option, Fintype.card_bool]
  rw [hcardeq] at hLcard
  calc Bad.card ≤ Short.card * Labels.card := hcount
    _ ≤ Short.card * (4 ^ w + 1) ^ F := Nat.mul_le_mul_left _ hLcard

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_count
