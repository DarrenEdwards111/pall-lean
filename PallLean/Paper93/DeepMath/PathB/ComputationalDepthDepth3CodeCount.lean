import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MaskCode

/-!
# Block-DT model, foundation 53: branching holography, step 4k — the code-labelled count (branch only)

The labels are now the **term-relative codes** (brick 52), not the masks: each code is a list of `≤ w`
ternary slots, so the label space is `(3^w)^F`-bounded (`w`-dependent), not the `n`-dependent mask space
of brick 47.  The codes are recovered into the masks on the fly during the peel (find the term, decode the
mask from the term + code, reset), so `σ ↦ (descentSat, codesList)` is still injective.

* `codesList` — the per-block code stream (`maskOnTerm` of each block mask).
* `codeMasks` — the code-driven peel: recover each block's mask from its code + the just-found term.
* `codeMasks_recovery` — `codeMasks (codesList …) (descentSat …) = descentSatMasks …`.
* `descent_code_injective` — `σ ↦ (descentSat, codesList)` is injective.
* `descent_code_count` — `|Bad| ≤ |Short| · |Labels|` with `Labels` the code streams.

This reduces the switching count to `|{code streams}| ≤ (3^w)^F` (codes are `≤ w` ternary slots, `≤ F`
blocks) — the concrete cardinality (pad to `Fin w` / `Fin F`) and the p-biased measure remain.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The per-block code stream: the term-relative code of each block mask. -/
def codesList (cs : List (Clause n)) (w : ℕ) :
    ℕ → (Fin n → Option Bool) → (Fin n → Bool) → List (List (Option Bool))
  | 0, _, _ => []
  | F + 1, σ, x =>
    if anyTermSat cs σ then []
    else match activeTerm cs σ with
      | none => []
      | some T =>
        maskOnTerm T (fun v => if v ∈ freeVarsOf σ T then some (x v) else none)
          :: codesList cs w F (extendσ σ T x) x

/-- The code-driven peel: find the first satisfied term, decode its mask from the term + code, reset,
recurse. -/
def codeMasks (cs : List (Clause n)) :
    List (List (Option Bool)) → (Fin n → Option Bool) → List (Fin n → Option Bool)
  | [], _ => []
  | code :: codes, σ' =>
    match cs.find? (termSat σ') with
    | none => []
    | some T => maskFromTerm T code :: codeMasks cs codes (resetX (maskFromTerm T code) σ')

/-- **Code recovery.**  Decoding the code stream against the satisfying boundary recovers the descent
masks. -/
theorem codeMasks_recovery (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      codeMasks cs (codesList cs w F σ x) (descentSat cs w F σ x) = descentSatMasks cs w F σ x := by
  intro F
  induction F with
  | zero => intro σ x; rw [codesList, codeMasks, descentSatMasks]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true =>
      rw [show codesList cs w (F + 1) σ x = [] by rw [codesList]; simp [hany],
          show descentSatMasks cs w (F + 1) σ x = [] by rw [descentSatMasks]; simp [hany], codeMasks]
    | false =>
      cases hact : activeTerm cs σ with
      | none =>
        rw [show codesList cs w (F + 1) σ x = [] by rw [codesList]; simp [hany, hact],
            show descentSatMasks cs w (F + 1) σ x = [] by rw [descentSatMasks]; simp [hany, hact],
            codeMasks]
      | some T =>
        have hTcons : Consistent T := hcons T (activeTerm_mem hact)
        have hcodes : codesList cs w (F + 1) σ x
            = maskOnTerm T (fun v => if v ∈ freeVarsOf σ T then some (x v) else none)
              :: codesList cs w F (extendσ σ T x) x := by
          rw [codesList]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hmask : descentSatMasks cs w (F + 1) σ x
            = (fun v => if v ∈ freeVarsOf σ T then some (x v) else none)
              :: descentSatMasks cs w F (extendσ σ T x) x := by
          rw [descentSatMasks]; simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [hcodes, hmask, codeMasks]
        simp only [descentSat_firstSat x hTcons hany hact, descentMask_recover,
          descentSat_step x hany hact, ih (extendσ σ T x) x]

/-- **The code injection.**  `σ ↦ (descentSat, codesList)` is injective: the masks (hence `σ`) are
recovered from the boundary and codes. -/
theorem descent_code_injective (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T) (w F : ℕ)
    {σ₁ σ₂ : Fin n → Option Bool} {x₁ x₂ : Fin n → Bool}
    (henc : descentSat cs w F σ₁ x₁ = descentSat cs w F σ₂ x₂)
    (hcodes : codesList cs w F σ₁ x₁ = codesList cs w F σ₂ x₂) : σ₁ = σ₂ := by
  have hm : descentSatMasks cs w F σ₁ x₁ = descentSatMasks cs w F σ₂ x₂ := by
    rw [← codeMasks_recovery cs hcons w F σ₁ x₁, ← codeMasks_recovery cs hcons w F σ₂ x₂, henc, hcodes]
  exact descentSat_injective cs w F henc hm

/-- **The code-labelled count.**  The bad set injects into `Short × Labels` with `Labels` the code streams,
so `|Bad| ≤ |Short| · |Labels|`. -/
theorem descent_code_count (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T) (w F : ℕ)
    {Bad Short : Finset (Fin n → Option Bool)} {Labels : Finset (List (List (Option Bool)))}
    (xσ : (Fin n → Option Bool) → (Fin n → Bool))
    (hS : ∀ σ ∈ Bad, descentSat cs w F σ (xσ σ) ∈ Short)
    (hL : ∀ σ ∈ Bad, codesList cs w F σ (xσ σ) ∈ Labels) :
    Bad.card ≤ Short.card * Labels.card := by
  classical
  have hcard : Bad.card ≤ (Short ×ˢ Labels).card := by
    refine Finset.card_le_card_of_injOn
      (fun σ => (descentSat cs w F σ (xσ σ), codesList cs w F σ (xσ σ)))
      (fun σ hσ => Finset.mem_product.mpr ⟨hS σ hσ, hL σ hσ⟩)
      (fun σ₁ _ σ₂ _ heq =>
        descent_code_injective cs hcons w F (congrArg Prod.fst heq) (congrArg Prod.snd heq))
  rwa [Finset.card_product] at hcard

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_code_count
