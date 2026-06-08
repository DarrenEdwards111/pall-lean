import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalComplete

/-!
# Block-DT model, foundation 29: the parity connection (increment 3, step 4) (branch only)

The parity-bridge connection of the adaptive canonical tree.  Combining full eval-correctness
(`canonicalDTree_eval`) with the relativized parity lower bound (`parity_needs_full_depth_rel`): a DNF
that computes parity on a `σ`-subcube forces its canonical decision tree to have depth `≥ stars σ` — it
must read every surviving variable.

* `canonicalDTree_depth_ge_of_parity` — parity on the subcube ⇒ canonical depth `≥ stars σ`.
* `shallow_canonical_not_parity` — if the canonical tree is shallow (`depth < stars σ`) it does **not**
  compute parity on the subcube (the switching-lemma contradiction, modulo "shallow").
* `dnf_parity_stars_le` — combined with the fuel depth bound: parity on the subcube ⇒ `stars σ ≤ F · w`.

## Honest scope

This is the parity connection as a **depth lower bound** (`≥ stars σ`).  The switching-lemma punchline —
that a *good restriction* makes the canonical tree shallow (`blockStream.length · w < stars σ`), so a
small DNF cannot compute parity on the subcube — needs the tighter upper bound (`≤ blockStream.length·w`,
increment 3 step 3); `shallow_canonical_not_parity` is exactly the statement that consumes it.  No `sorry`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Parity forces full survivor-depth.**  If the DNF computes parity on the `σ`-subcube, its canonical
decision tree (with sufficient fuel) has depth `≥ stars σ`. -/
theorem canonicalDTree_depth_ge_of_parity (cs : List (Clause n)) (w F : ℕ)
    (σ : Fin n → Option Bool) (hsf : stars σ < F)
    (hpar : ∀ x, DTree.agreeRestriction σ x → DTree.dnfValue cs x = DTree.parity x) :
    stars σ ≤ (canonicalDTree cs w F σ).depth := by
  by_contra hlt
  push_neg at hlt
  exact DTree.parity_needs_full_depth_rel (canonicalDTree cs w F σ) σ
    (fun x hx => by rw [canonicalDTree_eval cs w F σ x hsf hx]; exact hpar x hx)
    hlt

/-- **A shallow canonical tree cannot compute parity on the subcube.**  If `depth < stars σ`, some
`σ`-consistent input witnesses `dnfValue ≠ parity`. -/
theorem shallow_canonical_not_parity (cs : List (Clause n)) (w F : ℕ)
    (σ : Fin n → Option Bool) (hsf : stars σ < F)
    (hshallow : (canonicalDTree cs w F σ).depth < stars σ) :
    ∃ x, DTree.agreeRestriction σ x ∧ DTree.dnfValue cs x ≠ DTree.parity x := by
  by_contra hall
  push_neg at hall
  exact absurd (canonicalDTree_depth_ge_of_parity cs w F σ hsf hall) (by omega)

/-- **Parity ⇒ `stars σ ≤ F · w`.**  Combining the parity depth lower bound with the fuel depth upper
bound for a width-`≤ w` DNF. -/
theorem dnf_parity_stars_le (cs : List (Clause n)) (w F : ℕ) (σ : Fin n → Option Bool)
    (hsf : stars σ < F) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hpar : ∀ x, DTree.agreeRestriction σ x → DTree.dnfValue cs x = DTree.parity x) :
    stars σ ≤ F * w :=
  le_trans (canonicalDTree_depth_ge_of_parity cs w F σ hsf hpar)
    (canonicalDTree_depth_le cs w hw F σ)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDTree_depth_ge_of_parity
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.shallow_canonical_not_parity
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dnf_parity_stars_le
