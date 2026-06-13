import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCReuseSwitchingTarget

/-!
# The correlation / Williams frontier — opening the next mechanism for ACC⁰

The rank‑counting / restriction family is exhausted (`…ACCReuseSwitchingTarget`).  The next mechanism is
**correlation / Williams** — non‑natural, avoiding the rank route's limits.  This file opens it: it proves the
*correlation bridge core* and the *Williams cash‑out shape*, and names the hard correlation theorem as the open
target.

The correlation idea: a low‑resource predictor (e.g. one constant on the classes of a low‑rank holonomy
projection) cannot agree much with a function balanced across those classes.  The Williams idea: if ACC⁰ circuits
were small enough, a fast SAT algorithm + the hierarchy would collapse — contradiction.

## What is proved (clean axioms, no `sorry`)

* `class_agreement_le_majority` — **the correlation bridge core**: a predictor with a *fixed* value `b` on a class
  `S` agrees with `f` on at most the per‑class **majority** of `f` (`max(#{f=true}, #{f=false})` on `S`).  Summed
  over a low‑rank predictor's few classes, a target *balanced* on each class is predicted only `≈ ½` of the time —
  a correlation upper bound from the predictor's coarseness, *not* from counting functions.
* `acc0_williams_cashout` — **the Williams cash‑out shape**: `smallACC0 → fastSat`, `fastSat → collapse`,
  `¬ collapse ⇒ ¬ smallACC0`.  The classical algorithmic‑method skeleton, with the hard `smallACC0 → fastSat`
  step (Williams' fast ACC⁰‑SAT algorithm) a *named hypothesis*.

## The named targets (the open mechanism)

* `ACC0CorrelationAgainstTseitin` — ACC⁰ predictors agree with the Tseitin/Goldreich‑Majority family on only
  `≈ ½` of inputs (the family is balanced across every ACC⁰ class).  This is the `NP ⊄ ACC⁰`‑strength correlation
  theorem the bridge needs.

## The holonomy connection (stated)

High holonomy rank (`…HolonomyHardEffectiveRank`: the expander family realizes `2^m` classes) means a low‑rank
predictor's partition is *coarser* than the family's: within each predictor class the family still takes both
values (balance), so by `class_agreement_le_majority` the predictor's agreement is `≈ ½` — low correlation.  The
proved piece is the per‑class majority bound; the open piece is that ACC⁰ predictors *are* low‑rank / that the
family is balanced in their classes — exactly `ACC0CorrelationAgainstTseitin`.

## Honest scope

This *opens* the correlation/Williams route: the elementary correlation tool and the cash‑out skeleton are proved;
the load‑bearing steps — ACC⁰‑vs‑Tseitin correlation, and Williams' fast ACC⁰‑SAT algorithm — are named
hypotheses, both `NP ⊄ ACC⁰`‑strength (the SAT‑algorithm step is non‑natural, evading the Razborov–Rudich barrier
that caps the rank route — its one genuine advantage).  Restricted‑fragment correlation theorems (log‑gate,
read‑once) are the next concrete rungs.  This is a frontier opened, not crossed.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCWilliamsCorrelationTarget

variable {ι : Type*}

/-- **The correlation bridge core (proved): a class‑constant predictor agrees with `f` on ≤ the per‑class
majority.**  Whatever fixed value `b` the predictor outputs on the class `S`, it matches `f` only on the `f = b`
part of `S`, which is at most `max(#{f=true}, #{f=false})` on `S`. -/
theorem class_agreement_le_majority (S : Finset ι) (f : ι → Bool) (b : Bool) :
    (S.filter (fun x => b = f x)).card
      ≤ max (S.filter (fun x => f x = true)).card (S.filter (fun x => f x = false)).card := by
  have hrw : S.filter (fun x => b = f x) = S.filter (fun x => f x = b) :=
    Finset.filter_congr (fun x _ => eq_comm)
  rw [hrw]
  cases b
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- **(Named open target):** ACC⁰ predictors agree with the hard (Tseitin / Goldreich‑Majority) family on only
`≈ ½` of inputs — the family is balanced across every ACC⁰ class.  `NP ⊄ ACC⁰`‑strength correlation theorem. -/
def ACC0CorrelationAgainstTseitin (acc0Agreement : ℕ → ℕ) (halfInputs : ℕ → ℕ) : Prop :=
  ∀ n, acc0Agreement n ≤ halfInputs n

/-- **The Williams cash‑out shape (proved).**  If small ACC⁰ circuits would yield a fast SAT algorithm
(`smallACC0 → fastSat`, Williams' algorithmic method) and a fast SAT algorithm would collapse the hierarchy
(`fastSat → collapse`), then no collapse implies no small ACC⁰ circuits — the `NP ⊄ ACC⁰` shape.  The hard
`smallACC0 → fastSat` step is a named hypothesis; it is *non‑natural*, evading the Razborov–Rudich barrier that
caps the rank route. -/
theorem acc0_williams_cashout (smallACC0 fastSat collapse : Prop)
    (algo : smallACC0 → fastSat) (cashout : fastSat → collapse) (noCollapse : ¬ collapse) :
    ¬ smallACC0 :=
  fun h => noCollapse (cashout (algo h))

end PallLean.Paper93.DeepMath.PathB.ACCWilliamsCorrelationTarget

#print axioms PallLean.Paper93.DeepMath.PathB.ACCWilliamsCorrelationTarget.class_agreement_le_majority
#print axioms PallLean.Paper93.DeepMath.PathB.ACCWilliamsCorrelationTarget.acc0_williams_cashout
