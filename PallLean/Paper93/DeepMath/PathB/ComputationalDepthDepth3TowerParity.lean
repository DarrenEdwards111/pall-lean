import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reduces
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalParity

/-!
# AC⁰ reduction, foundation 21: the parity capstone (branch only)

The contradiction that closes the pipeline.  The multi-round reduction spine (brick 20) carries a depth-`d`
tower down to a depth-2 bottom `DNF` on a common subcube; the relativized parity bound (brick: parity
connection) says a `DNF` whose canonical tree is shallow *relative to the survivors* cannot compute parity
there.  Wiring the two gives: **a tower that reduces to such a shallow depth-2 `DNF` on a subcube does not
compute parity on it.**

* `tower_not_parity` — if `C` reduces (at every `σ`-subcube point) to a bottom `DNF d` whose canonical tree
  is shallow relative to `stars σ`, then `C` does not compute parity on the `σ`-subcube.

## Honest scope — what this is and what it is not

This is the *capstone glue*: it composes `Reduces.eval_eq` (brick 20) with `shallow_canonical_not_parity`
(the relativized parity lower bound).  Two hypotheses are the per-instance interface, **stated openly, not
hidden**:

* `hred` — the `d`-round reduction holds on the `σ`-subcube.  For a concrete depth-`d` circuit this is
  assembled from the well-formed layer collapses (bricks 17/19) via `Reduces.head`/`trans` (the hypotheses
  they require are preserved round-to-round by bricks 14/15/18/19).
* `hshallow` — the endpoint `DNF`'s canonical tree is shallow relative to the survivor count.  This is the
  switching-lemma output (`exists_shallow_all`, brick 6) — available once the shallow bound `s` is below
  `stars σ`.

The single genuinely-open analytic input behind both is the **coordinate budget**: that after `d` rounds
the common subcube still has `stars σ` survivors exceeding the shallow bound.  That needs *subcube-relative*
switching (each round applied to the previous round's free coordinates), which `exists_shallow_all` (a
full-domain restriction) does not yet provide.  We do **not** paper over it: `tower_not_parity` is exactly
the honest statement of what the built machinery delivers *given* that budget.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

/-- **The parity capstone.**  If a tower `C` reduces, at every point of the `σ`-subcube, to a bottom
`DNF d` whose canonical tree is shallow relative to the survivors (`depth < stars σ`), then `C` does not
compute parity on the `σ`-subcube. -/
theorem tower_not_parity (C : Layered n) (d : List (Clause n)) (w F : ℕ)
    (σ : Fin n → Option Bool) (hsf : stars σ < F)
    (hshallow : (canonicalDTree d w F σ).depth < stars σ)
    (hred : ∀ x, DTree.agreeRestriction σ x → Reduces x C (dnf d)) :
    ¬ (∀ x, DTree.agreeRestriction σ x → eval C x = DTree.parity x) := by
  intro hpar
  -- the depth-2 endpoint computes parity on the subcube
  have hdnf : ∀ x, DTree.agreeRestriction σ x → DTree.dnfValue d x = DTree.parity x := by
    intro x hx
    have he := (hred x hx).eval_eq
    rw [eval_dnf] at he
    rw [← he]
    exact hpar x hx
  -- but a shallow canonical tree cannot compute parity on the subcube
  obtain ⟨x, hx, hne⟩ := shallow_canonical_not_parity d w F σ hsf hshallow
  exact hne (hdnf x hx)

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.tower_not_parity
