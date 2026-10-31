import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightParity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3IteratedReduction

/-!
# Tight switching, step 17: the reduction spine over the tight tree (branch `razborov-recoverRho-wip`)

The capstone glue, now entirely over the single-literal canonical tree.  `tower_not_parity` /
`iterated_not_parity` (foundations 21/37) compose the `d`-fold reduction chain with the parity lower bound —
but their parity input is `shallow_canonical_not_parity`, stated over the **block** tree `canonicalDTree`.
We re-derive both over `canonicalDT`, using `shallow_canonicalDT_not_parity` (step 14).

Nothing else changes: `reduces_iterate` (foundation 37) is *generic* over `EquivOn` rounds, so it carries the
tight `EquivOn` rounds (`collapse_or_layer_tight`, step 16) verbatim.  The only tree-specific input is the
final-endpoint parity refutation, which step 14 supplies over `canonicalDT`.  So the entire spine —
switching count → collapse → `EquivOn` round → `d`-fold reduction → parity contradiction — now runs over the
tight tree, with an `F`-independent shallow bound.

* `tower_not_parity_tight` — a tower reducing (on the `σ`-subcube) to a bottom `DNF` `D` whose *single-
  literal* canonical tree is shallow relative to the survivors does not compute parity there.
* `iterated_not_parity_tight` — the `d`-fold version: `d` nested tight `EquivOn` rounds ending in such a
  shallow bottom `DNF` ⟹ the original tower does not compute parity on the subcube.

## Honest scope

The two per-instance interfaces are stated openly (as in the crude versions): `hred`/`heq` (the rounds,
supplied by `collapse_or_layer_tight`) and `hshallow` (the endpoint shallowness, supplied by the tight
switching count).  The genuinely-open analytic input remains the **subcube-relative survivor budget** — that
after `d` rounds the common subcube still has `stars σ` survivors exceeding the shallow bound `s`.  That is
the conditional star concentration (step 15's third bad event applied per-round on the previous round's free
coordinates); it is not discharged here.  We flag it, not paper over it.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The parity capstone over the tight tree.**  If `C` reduces (at every `σ`-subcube point) to a bottom
`DNF` `D` whose *single-literal* canonical tree is shallow relative to `stars σ`, then `C` does not compute
parity on the `σ`-subcube. -/
theorem tower_not_parity_tight (C : Layered n) (D : List (Clause n)) (F : ℕ)
    (σ : Fin n → Option Bool) (hsf : SwitchingCounting.stars σ ≤ F)
    (hshallow : (canonicalDT D F σ).depth < SwitchingCounting.stars σ)
    (hred : ∀ x, DTree.agreeRestriction σ x → Reduces x C (dnf D)) :
    ¬ (∀ x, DTree.agreeRestriction σ x → eval C x = DTree.parity x) := by
  intro hpar
  have hdnf : ∀ x, DTree.agreeRestriction σ x → DTree.dnfValue D x = DTree.parity x := by
    intro x hx
    have he := (hred x hx).eval_eq
    rw [eval_dnf] at he
    rw [← he]
    exact hpar x hx
  obtain ⟨x, hx, hne⟩ := shallow_canonicalDT_not_parity D F σ hsf hshallow
  exact hne (hdnf x hx)

/-- **The `d`-fold chaining capstone over the tight tree.**  If `d` nested tight `EquivOn` rounds reduce
`C 0` to a bottom `DNF` `D` whose single-literal canonical tree is shallow relative to the survivors of `σ`,
then `C 0` does not compute parity on the `σ`-subcube. -/
theorem iterated_not_parity_tight (C : ℕ → Layered n) (ρ : ℕ → Fin n → Option Bool)
    (σ : Fin n → Option Bool) (d : ℕ) (D : List (Clause n)) (F : ℕ)
    (hext : ∀ i, Extends (ρ i) σ)
    (heq : ∀ i, EquivOn (ρ i) (C i) (C (i + 1)))
    (hCd : C d = dnf D) (hsf : SwitchingCounting.stars σ ≤ F)
    (hshallow : (canonicalDT D F σ).depth < SwitchingCounting.stars σ) :
    ¬ (∀ x, DTree.agreeRestriction σ x → eval (C 0) x = DTree.parity x) :=
  tower_not_parity_tight (C 0) D F σ hsf hshallow (fun x hx => by
    have h := Layered.reduces_iterate x σ C ρ hext hx heq d
    rw [hCd] at h
    exact h)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.tower_not_parity_tight
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.iterated_not_parity_tight
