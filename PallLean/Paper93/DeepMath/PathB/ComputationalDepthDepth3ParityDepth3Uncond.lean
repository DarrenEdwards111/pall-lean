import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowAllUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightCollapseOr
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightIterated

/-!
# Tight switching, step 35: unconditional depth-3 parity lower bound (branch `razborov-recoverRho-wip`)

`collapse_to_dnf_layer_tight` (step 20) and `parity_not_depth3_tight` (step 21) with the empty-skip
hypotheses dropped: the dual collapse round now uses `exists_shallow_all_tight_uncond` (step 33), so the
depth-3 `OR`-of-`CNF` parity lower bound holds with **no `hnf`/`hleaf`/`hpos`** — only width (`hw`),
clause-count (`hm`) bounds and the terminal survivor budget `hterm` (itself dischargeable unconditionally by
`exists_survivor_shallow_extends`'s unconditional analogue).

* `collapse_to_dnf_layer_tight_uncond` — the unconditional dual `EquivOn` round (`OR`-of-`CNF` → `DNF`).
* `parity_not_depth3_tight_uncond` — the unconditional depth-3 parity lower bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered Classical

variable {n : ℕ}

/-- **The unconditional dual `EquivOn` round (`OR`-of-`CNF` → `DNF`).**  As `collapse_to_dnf_layer_tight`,
but the underlying collapse-existence is unconditional — no `hnf`/`hleaf`/`hpos`, only width/clause-count. -/
theorem collapse_to_dnf_layer_tight_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F) (G : Finset (List (Clause n)))
    (hw : ∀ g ∈ G.image negDNF, ∀ T ∈ g, T.lits.length ≤ w)
    (hm : ∀ g ∈ G.image negDNF, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall : ((G.image negDNF).card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))) < 1) :
    ∃ ρ : Fin n → Option Bool,
      (∀ g ∈ G, (canonicalDT (negDNF g) F ρ).depth < s)
        ∧ EquivOn ρ (gOr (G.toList.map cnf))
          (dnf (G.toList.flatMap (fun g =>
            dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ))))))
        ∧ (∀ T ∈ G.toList.flatMap (fun g =>
              dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ)))),
            T.lits.length < s) := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_shallow_all_tight_uncond hp0 hp3 (G.image negDNF) hw hm hr1 hsmall
  have hstars : SwitchingCounting.stars ρ ≤ F :=
    le_trans (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  have hshallow : ∀ g ∈ G, (canonicalDT (negDNF g) F ρ).depth < s :=
    fun g hg => hρ (negDNF g) (Finset.mem_image_of_mem _ hg)
  refine ⟨ρ, hshallow, ?_, ?_⟩
  · intro x hx
    rw [eval_gOr_cnf, eval_dnf]
    exact ((collapse_core_or_tight F s G hstars hshallow).1 x hx).symm
  · exact (collapse_core_or_tight F s G hstars hshallow).2

/-- **The unconditional depth-3 parity lower bound.**  An `OR` of `CNF` gates does not compute parity, with
no empty-skip (`hnf`/`hleaf`/`hpos`) hypotheses — only width/clause-count bounds and the terminal survivor
budget `hterm`. -/
theorem parity_not_depth3_tight_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s₁ s₂ m : ℕ} [NeZero w] [NeZero m] (hF : n ≤ F) (G : Finset (List (Clause n)))
    (hw : ∀ g ∈ G.image negDNF, ∀ T ∈ g, T.lits.length ≤ w)
    (hm : ∀ g ∈ G.image negDNF, g.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1)
    (hsmall₁ : ((G.image negDNF).card : ℚ)
        * (((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s₁
            / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)))) < 1)
    (hterm : ∀ ρ₁ : Restriction n,
        (∀ g ∈ G, (canonicalDT (negDNF g) F ρ₁).depth < s₁) →
        ∃ ρ₂ : Restriction n, Extends ρ₁ ρ₂ ∧ s₂ ≤ SwitchingCounting.stars ρ₂ ∧
          SwitchingCounting.stars ρ₂ ≤ F ∧
          (canonicalDT (G.toList.flatMap (fun g =>
            dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ₁))))) F ρ₂).depth < s₂) :
    ∃ x : Fin n → Bool, eval (gOr (G.toList.map cnf)) x ≠ DTree.parity x := by
  classical
  obtain ⟨ρ₁, hsh₁, heq₁, _hwid₁⟩ :=
    collapse_to_dnf_layer_tight_uncond hp0 hp3 hF G hw hm hr1 hsmall₁
  set D₁ : List (Clause n) :=
    G.toList.flatMap (fun g =>
      dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF g) F ρ₁)))) with hD₁
  obtain ⟨ρ₂, hext₂, hge₂, hle₂, hshD₁⟩ := hterm ρ₁ hsh₁
  have hshallow : (canonicalDT D₁ F ρ₂).depth < SwitchingCounting.stars ρ₂ :=
    lt_of_lt_of_le hshD₁ hge₂
  let C : ℕ → Layered n := fun i => match i with | 0 => gOr (G.toList.map cnf) | _ + 1 => dnf D₁
  let ρ : ℕ → Restriction n := fun i => match i with | 0 => ρ₁ | _ + 1 => ρ₂
  have hext : ∀ i, Extends (ρ i) ρ₂ := by
    intro i; cases i with
    | zero => exact hext₂
    | succ j => exact fun v b hb => hb
  have heq : ∀ i, EquivOn (ρ i) (C i) (C (i + 1)) := by
    intro i; cases i with
    | zero => exact heq₁
    | succ j => exact fun x _ => rfl
  have hfinal := iterated_not_parity_tight C ρ ρ₂ 1 D₁ F hext heq rfl hle₂ hshallow
  push_neg at hfinal
  obtain ⟨x, _, hx⟩ := hfinal
  exact ⟨x, hx⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_depth3_tight_uncond
