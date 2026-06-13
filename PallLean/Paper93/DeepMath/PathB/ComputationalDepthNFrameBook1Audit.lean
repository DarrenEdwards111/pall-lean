import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTimeBoundaryPrinciple

/-!
# Audit: does Book 1 (the N-Frame CEW/SPDP route) supply the missing explicit-time theorem?

**Short answer (this file makes it precise): no — Book 1 supplies the *shape* of the missing thing, not the
missing theorem.**  The active obstruction is exactly one of its axioms, and that axiom in its load-bearing
(semantic) form is `P ≠ NP`-strength, while in its naive (time-only) form it is *already refuted* by results
proved elsewhere in this corpus.

## What Book 1 already is, in Lean

The Book-1 contextual-entanglement-width / SPDP route is fully formalized in
`ComputationalDepthBook1CEWRoute.lean` as the obligation structure `Book1CEWSPDPEpistemicBoundaryPort enc`, whose
four fields are exactly Book 1's four pillars:

* **(A1) `boundedCEWForP`** — every SAT-deciding P observer has polylogarithmic CEW.
* **(A2) `cewToPolynomialSPDP`** — polylog CEW ⇒ polynomial SPDP rank.
* **(A3) `hardNPLowerBound`** — the hard NP family has super-polynomial SPDP rank (`n^{log₂ n / 4}`).
* **(A4) `transportCertificate`** — a SAT decider transports the hard rank into its own P-side rank.

These assemble — *unconditionally, modulo the four fields* — into the separation:
`no_DTMDecidesSATWithEncoding_of_book1CEWSPDP` and `standardPvsNP_of_book1CEWSPDP`.  So **A1–A4 ⇒ P ≠ NP is a
theorem**; the content is entirely in discharging the fields.

Of the four, A2 is a genuine counting lemma (`cewToPolynomialSPDP_of_countingCertificate`, proved), A3 is the
calibrated Ramanujan/Tseitin lower bound (sound on the permanent side), A4 is a transport/no-loss certificate.
**A1 is the live wall.**  In `ComputationalDepthBook1CEWRoute.lean`, A1 is discharged only by a *syntactic*
log-window surrogate (`book1LogSyntacticPCEW := fun _ n => Nat.log 2 n`, `boundedCEWForP_of_logSyntacticPCEW`),
which — the file says so explicitly — is "only a window budget, not a claim that an arbitrary SAT decider has low
semantic complexity."  The semantic A1 — *every* poly-time SAT decider's *actual* contextual interface is
polylog — is the unproved step, and is equivalent in strength to the separation.

## What this file proves: the naive (time-only) form of A1 is FALSE

A1 would be cheap if running time bounded the contextual interface — "poly-time ⇒ cheap observer."  This corpus
already proved that is false at the boundary/action level.  We package the verdict here against the Book-1
interface:

* `naive_time_cew_bound_false` — **no function of the time bound alone can serve as A1.**  For any candidate
  budget `f : ℕ → ℕ` (purporting `CEW/action ≤ f(T)`) and any `T ≥ 1`, there is a trajectory whose action exceeds
  `f T`.  A direct corollary of `action_unbounded_by_time`: a single step's action `2^{B τ}` is unbounded, so
  time indexes nothing about the boundary.
* `space_bound_does_supply_A1` — by contrast, a *space* bound **does** give subcriticality
  (`subcritical_of_lowspace`): `Tb · 2^s < K ⇒ action < K`.  This is the exact contrast — the working A1 surrogate
  is a *space/contextual* invariant, never a time-only one.
* `correct_decider_escapes_boundary_A1` — worse, a *correct* (zero-debt) SAT-style decider of **full** boundary
  `n` exists (`hard_instance_has_correct_high_boundary_decider`, the brute-force / Gaussian-elimination escape).
  So "every decider has low boundary" is false even semantically; CEW, to be true, must be a strictly finer
  invariant than boundary or action.

## Verdict

Book 1 is *aligned*: it names the right target and the geometry is faithful (this matches the audited corpus
finding that the SPDP/CEW bridge is the right object but is **assumed, not derived**).  But the usable route
reduces `P ≠ NP` to **semantic A1** — bounded contextual width for *all* P — which is the one irreducible step,
`P ≠ NP`-strength, and provably not obtainable from a time bound.  To go further one must replace A1 with a new
*time-sensitive contextual invariant* (finer than boundary/action and not refuted by the brute-force escape), or
prove bounded CEW for all P directly.  Neither is supplied by Book 1.  This audit file does not weaken or fake
that conclusion; it pins it to proved theorems.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBook1Audit

open PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple
open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

/-- **The naive (time-only) form of Book-1 axiom A1 is false (proved).**  No budget `f` that is a function of the
running-time bound `T` alone can bound the observer action: for every `f` and every `T ≥ 1`, some boundary
sequence has `action B T > f T`.  Hence "poly-time ⇒ polylog CEW/action" cannot hold by any time-indexed bound —
A1 must come from a space/contextual invariant, not from time.  Direct from `action_unbounded_by_time`. -/
theorem naive_time_cew_bound_false (f : ℕ → ℕ) (T : ℕ) (hT : 1 ≤ T) :
    ∃ B : ℕ → ℕ, f T < action B T :=
  action_unbounded_by_time T (f T) hT

/-- **A space bound DOES supply A1 (proved, by contrast).**  If the space-time budget `Tb · 2^s` is below the
fooling-set size `K`, the action is subcritical.  This is the working A1 surrogate — a *space/contextual* bound,
the regime where Book-1's "cheap observer" claim is a theorem rather than the wall. -/
theorem space_bound_does_supply_A1 (B : ℕ → ℕ) (T Tb s K : ℕ) (hT : T ≤ Tb)
    (hsp : ∀ τ, B τ ≤ s) (hbudget : Tb * 2 ^ s < K) :
    action B T < K :=
  subcritical_of_lowspace B T Tb s K hT hsp hbudget

/-- **A correct decider can have full boundary — semantic A1 fails at the boundary level (proved).**  The hard
hypercube instance has a *correct*, zero-debt decider of full boundary `n` (the brute-force / Gaussian-elimination
escape).  So "every SAT decider has low contextual boundary" is false even before time bounds enter; any true CEW
notion must be strictly finer than boundary/action.  Re-export of `hard_instance_has_correct_high_boundary_decider`. -/
theorem correct_decider_escapes_boundary_A1 (n : ℕ) :
    ∃ view0 : (Fin n → Bool) → Fin (2 ^ n), debtCount (hypercubeFool n) view0 = 0 :=
  hard_instance_has_correct_high_boundary_decider n

end PallLean.Paper93.DeepMath.PathB.NFrameBook1Audit

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBook1Audit.naive_time_cew_bound_false
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBook1Audit.space_bound_does_supply_A1
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBook1Audit.correct_decider_escapes_boundary_A1
