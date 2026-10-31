import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PBiased

/-!
# AC⁰ reduction, foundation 22: conditioning the p-biased measure on a base restriction (branch only)

The enabling fact for *subcube-relative* switching — the primitive the multi-round coordinate budget needs.
The full-domain p-biased measure (brick 55) is run unconditionally; to track survivors across rounds we
must condition on already-fixed coordinates.  Conditioning on "extends `τ`" **factors**: each coordinate
`τ` fixes contributes the constant `(1-p)/2`, each coordinate `τ` leaves free normalises to `1`, so the
total weight of the extension box is exactly `((1-p)/2)^(n - stars τ)`.

* `extBox τ` — the restrictions extending `τ` (free on `τ`'s free coordinates, equal to `τ` elsewhere).
* `mem_extBox` — `σ ∈ extBox τ ↔ Extends τ σ`.
* `pweight_sum_extends` — `∑_{σ extends τ} pweight p σ = ((1-p)/2)^(n - stars τ)`.

Dividing through by this constant turns the unconditional switching bound (`descent_switching_le`, brick 60)
into a *conditional* one on `τ`'s subcube — the step toward iterating switching over nested free sets.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The extension box of `τ`: restrictions free on `τ`'s free coordinates, equal to `τ` on the rest. -/
def extBox (τ : Fin n → Option Bool) : Finset (Fin n → Option Bool) :=
  Fintype.piFinset (fun v => if τ v = none then (Finset.univ : Finset (Option Bool)) else {τ v})

/-- Membership in the extension box is exactly extending `τ`. -/
theorem mem_extBox {τ σ : Fin n → Option Bool} : σ ∈ extBox τ ↔ Extends τ σ := by
  rw [extBox, Fintype.mem_piFinset]
  constructor
  · intro h v b hb
    have hv := h v
    rw [if_neg (by rw [hb]; exact Option.some_ne_none b)] at hv
    rw [Finset.mem_singleton] at hv
    rw [hv]; exact hb
  · intro h v
    by_cases hv : τ v = none
    · rw [if_pos hv]; exact Finset.mem_univ _
    · rw [if_neg hv, Finset.mem_singleton]
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hv
      rw [hb]; exact h v b hb

/-- **Conditioning factors the p-biased measure.**  The total weight of all restrictions extending `τ` is
`((1-p)/2)^(n - stars τ)`: each of `τ`'s fixed coordinates contributes `(1-p)/2`, each free coordinate
normalises to `1`. -/
theorem pweight_sum_extends (p : ℚ) (τ : Fin n → Option Bool) :
    ∑ σ ∈ extBox τ, pweight p σ = ((1 - p) / 2) ^ (n - stars τ) := by
  simp only [pweight, extBox]
  rw [← Finset.prod_univ_sum (fun v => if τ v = none then (Finset.univ : Finset (Option Bool)) else {τ v})
    (fun (_ : Fin n) (b : Option Bool) => if b = none then p else (1 - p) / 2)]
  have hfac : ∀ v ∈ (Finset.univ : Finset (Fin n)),
      (∑ b ∈ (if τ v = none then (Finset.univ : Finset (Option Bool)) else {τ v}),
        (if b = none then p else (1 - p) / 2))
        = (if τ v = none then (1 : ℚ) else (1 - p) / 2) := by
    intro v _
    by_cases hv : τ v = none
    · rw [if_pos hv, if_pos hv, Fintype.sum_option, Fintype.sum_bool, if_pos rfl,
        if_neg (by simp), if_neg (by simp)]
      ring
    · rw [if_neg hv, if_neg hv, Finset.sum_singleton, if_neg hv]
  rw [Finset.prod_congr rfl hfac, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const]
  congr 1
  rw [stars, freeVars]
  have h : (Finset.univ.filter (fun v : Fin n => τ v = none)).card
      + (Finset.univ.filter (fun v : Fin n => ¬ τ v = none)).card = n := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_fin]
  omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pweight_sum_extends
