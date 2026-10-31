import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockPeel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockPathLabel

/-!
# Block-DT model, foundation 10b: compact label compatibility (branch only)

The conceptual bridge for the tight `(2^w)^s` count: the **in-clause positions** of the free literals
reconstruct exactly the global block mask.

* `freePosOf` — per block, the `Fin w` positions whose literal is free at `σ`.
* `posMaskOf` — the global mask reconstructed from a position set + the active term.
* `posMaskOf_freePosOf` — **compatibility**: `posMaskOf T (freePosOf T σ) = (the block mask of T at σ)`,
  for a width-`≤ w` term.

Clean, no `sorry`.  AC⁰/depth-3.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The block mask of `T` at `σ` (the global predicate used by `blockMasks`). -/
@[reducible] def blockMaskPred (σ : Restriction n) (T : Clause n) : Fin n → Bool :=
  fun v => decide (σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits))

/-- Per block: the `Fin w` positions whose literal in `T` is free at `σ`. -/
def freePosOf (w : ℕ) (σ : Restriction n) (T : Clause n) : Finset (Fin w) :=
  Finset.univ.filter (fun p => (T.lits[p.val]?).any (fun ℓ => decide (σ (litVar ℓ) = none)))

/-- The global mask reconstructed from a position set and the active term. -/
def posMaskOf (w : ℕ) (T : Clause n) (cl : Finset (Fin w)) : Fin n → Bool :=
  fun v => decide (∃ p ∈ cl, (T.lits[p.val]?).any (fun ℓ => decide (litVar ℓ = v)))

/-- **Compatibility.**  For a width-`≤ w` term, the in-clause positions of the free literals
reconstruct exactly the global block mask. -/
theorem posMaskOf_freePosOf (w : ℕ) (σ : Restriction n) (T : Clause n)
    (hw : T.lits.length ≤ w) :
    posMaskOf w T (freePosOf w σ T) = blockMaskPred σ T := by
  funext v
  simp only [posMaskOf, blockMaskPred, freePosOf, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_decide]
  constructor
  · rintro ⟨p, hpfree, hpv⟩
    rw [Option.any_eq_true] at hpfree hpv
    obtain ⟨ℓ, hℓ, hfree⟩ := hpfree
    obtain ⟨ℓ', hℓ', hvv⟩ := hpv
    rw [hℓ] at hℓ'; injection hℓ' with hℓeq; subst hℓeq
    have hfree' : σ (litVar ℓ) = none := of_decide_eq_true hfree
    have hveq : litVar ℓ = v := of_decide_eq_true hvv
    have hmem' : ℓ ∈ T.lits := List.mem_of_getElem? hℓ
    cases ℓ with
    | pos i => simp only [litVar] at hveq hfree'; subst hveq; exact ⟨hfree', Or.inl hmem'⟩
    | neg i => simp only [litVar] at hveq hfree'; subst hveq; exact ⟨hfree', Or.inr hmem'⟩
  · rintro ⟨hvnone, hmem⟩
    have hlit : ∃ ℓ ∈ T.lits, litVar ℓ = v := by
      rcases hmem with hp | hn
      · exact ⟨Rung4Literal.pos v, hp, rfl⟩
      · exact ⟨Rung4Literal.neg v, hn, rfl⟩
    obtain ⟨ℓ, hℓmem, hℓv⟩ := hlit
    obtain ⟨k, hklt, hk⟩ := List.getElem_of_mem hℓmem
    have hkw : k < w := lt_of_lt_of_le hklt hw
    have hget : T.lits[(⟨k, hkw⟩ : Fin w).val]? = some ℓ := by
      rw [List.getElem?_eq_getElem hklt, hk]
    refine ⟨⟨k, hkw⟩, ?_, ?_⟩
    · rw [Option.any_eq_true]; exact ⟨ℓ, hget, by rw [hℓv]; exact decide_eq_true_eq.mpr hvnone⟩
    · rw [Option.any_eq_true]; exact ⟨ℓ, hget, decide_eq_true_eq.mpr hℓv⟩

end PallLean.Paper93.DeepMath.PathB.Depth3
