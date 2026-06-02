import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonLabel

/-!
# Bridge: the canonical `(2w)^s` switching count → the depth-3 collapse pipeline

**STATUS: REAL.  THE FIRST LINK — COUNT ⟹ A GOOD RESTRICTION EXISTS.**

The depth-3 collapse gate (`Depth3CollapseModel.collapse`) needs: a restriction under which the
refuting circuit collapses to a short list-derivation refutation.  The canonical switching count
`canonMarkLabel_switching_count` is the *quantitative* ingredient — it bounds the **bad**
restrictions (those that fail to collapse a bottom gate) by `|Short| · (2w)^s`.

This file builds the first honest link of the count → collapse chain: a **pigeonhole** turning
the count into the *existence* of a good (non-bad) restriction, *provided* the count is strictly
below the total number of restrictions (`|Short| · (2w)^s < 3^n`).  That strict inequality is
the **parameter-algebra** obligation (random-restriction / binomial-ratio estimate) — stated
here as a hypothesis, to be discharged by the choice of restriction parameters.

What this file does **not** do (the remaining open links, genuinely new machinery):
* the *union bound* over all bottom gates (one good restriction for *all* gates at once);
* the *assembly*: a good restriction collapses the circuit to a short `LDeriv` refutation.

So this is the honest interface seam: the canonical count is consumed to produce a good
restriction; the collapse-assembly remains the open gate.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Pigeonhole: a good restriction exists.**  If the bad set is bounded by `|Short| · (2w)^s`
and that is strictly less than the total number of restrictions, some restriction is not bad. -/
theorem exists_good_restriction {w s : ℕ} {Bad Short : Finset (Restriction n)}
    (hcount : Bad.card ≤ Short.card * (2 * w) ^ s)
    (hlt : Short.card * (2 * w) ^ s < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ρ ∉ Bad := by
  have hBad : Bad.card < (Finset.univ : Finset (Restriction n)).card := lt_of_le_of_lt hcount hlt
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Restriction n)) ⊆ Bad := fun ρ _ => h ρ
  exact absurd (Finset.card_le_card hsub) (not_le.mpr hBad)

/-- **Count ⟹ good restriction, via the canonical switching count.**  Discharges the bad-set
bound from `canonMarkLabel_switching_count` and applies the pigeonhole: under the parameter
condition `|Short| · (2w)^s < 3^n` (the total restriction count), a non-bad restriction exists.
This is the first link consuming the canonical `(2w)^s` count in the collapse pipeline. -/
theorem exists_good_restriction_canon {w s : ℕ} [NeZero w] {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hne : ∀ ρ ∈ Bad, ∀ b ∈ canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))), b ≠ [])
    (hlen : ∀ ρ ∈ Bad, (ungroupBlocks (canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))))).length = s)
    (hmem : ∀ ρ ∈ Bad, complete ρ (encLits ρ cs) ∈ Short)
    (hlt : Short.card * (2 * w) ^ s < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ρ ∉ Bad :=
  exists_good_restriction (canonMarkLabel_switching_count hcs hwidth hne hlen hmem) hlt

/-- The total number of restrictions is `3^n` (each coordinate is unset / 0 / 1).  Pins the
right-hand side of the parameter-algebra inequality `|Short| · (2w)^s < 3^n`. -/
theorem card_restriction (n : ℕ) :
    (Finset.univ : Finset (Restriction n)).card = 3 ^ n := by
  rw [Finset.card_univ]
  simp [Restriction, Fintype.card_fun, Fintype.card_option, Fintype.card_bool]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.exists_good_restriction_canon
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_restriction
