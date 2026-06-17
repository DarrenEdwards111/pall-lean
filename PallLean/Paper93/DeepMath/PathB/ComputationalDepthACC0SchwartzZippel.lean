import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SumCheck

/-!
# Sum-check soundness — Schwartz–Zippel in one variable (proved), multilinearity socketed

Entry 225 proved the sum-check round-reduction engine and left **`SumCheckSoundness`** as a named BFL socket.  This
file proves its genuine single-variable core — the **Schwartz–Zippel root bound** that makes a *cheating* prover get
caught: two distinct degree-`≤ d` round polynomials agree at most `d` field points, so a random challenge separates the
prover's claimed round polynomial from the honest one with probability `≥ 1 - d/|F|`.

The point.  In each sum-check round the prover sends a univariate polynomial `q` claiming `q = p`, where `p` is the
honest round polynomial.  If the prover lies (`q ≠ p`) but the polynomials are degree `≤ d`, then `q` and `p` agree on
at most `d` points (the roots of `p - q ≠ 0`).  A verifier picking the challenge `r` uniformly from a field of size
`|F| > d` therefore catches the lie with probability `≥ 1 - d/|F|`.  This is the soundness amplifier of every round.

## What is proved (clean axioms, no `sorry`)

* **`agreement_le_degree`** (PROVED) — for distinct `p q : F[X]`, the number of field points where they agree is at most
  `(p - q).natDegree` (the agreement set injects into the roots of `p - q ≠ 0`; `Polynomial.card_roots'`).
* **`agreement_le_max`** (PROVED) — for distinct degree-`≤ d` polynomials, they agree at most `d` points
  (`natDegree_sub_le` + `max_le`).
* **`few_agreements`** (PROVED) — if `|F| > d`, distinct degree-`≤ d` polynomials *disagree* somewhere: the agreement
  set is a strict subset of the field, so a separating challenge exists.
* **`SumCheckRoundSoundness`** — the residual socket: the honest round polynomial is degree `≤ d` and the prover's claim
  is degree `≤ d` (the multilinearity / low-degree-extension bound), plus the *multi-prover* multilinearity test.

## Honest scope

This proves the **single-variable Schwartz–Zippel root bound** completely — distinct degree-`≤ d` polynomials agree at
`≤ d` field points, and so disagree (a separating challenge exists) once `|F| > d` — by `Polynomial.card_roots'` and
`natDegree_sub_le`.  This is the per-round soundness amplifier of sum-check.  What remains the named socket is
**`SumCheckRoundSoundness`**: that the round polynomials are *actually* degree `≤ d` (the low-degree-extension /
multilinearity bound on the arithmetized predicate) and the *multi-prover* multilinearity test that makes the protocol
`MIP` rather than single-prover `IP = PSPACE` — the genuinely protocol-specific content.  The root bound is proved; the
degree bound and multi-prover structure are socketed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

open Finset Polynomial

namespace PallLean.Paper93.DeepMath.PathB.ACC0SchwartzZippel

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The agreement bound (PROVED).**  Two distinct polynomials `p ≠ q` over a finite field agree at most
`(p - q).natDegree` points: the agreement set `{r | p(r) = q(r)}` injects into the roots of `p - q ≠ 0`, whose count is
`≤ natDegree (p - q)` (`Polynomial.card_roots'`). -/
theorem agreement_le_degree (p q : F[X]) (hpq : p ≠ q) :
    (Finset.univ.filter (fun r => p.eval r = q.eval r)).card ≤ (p - q).natDegree := by
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hsub : (Finset.univ.filter (fun r => p.eval r = q.eval r))
      ⊆ (p - q).roots.toFinset := by
    intro r hr
    simp only [Finset.mem_filter] at hr
    rw [Multiset.mem_toFinset, mem_roots hne]
    simp only [IsRoot.def, eval_sub, sub_eq_zero]
    exact hr.2
  calc (Finset.univ.filter (fun r => p.eval r = q.eval r)).card
      ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (p - q).roots := (p - q).roots.toFinset_card_le
    _ ≤ (p - q).natDegree := (p - q).card_roots'

/-- **Schwartz–Zippel, one variable (PROVED).**  Distinct degree-`≤ d` polynomials agree at most `d` field points.  In
sum-check: a cheating prover's claimed round polynomial agrees with the honest one at `≤ d` of the `|F|` possible
challenges. -/
theorem agreement_le_max {d : ℕ} (p q : F[X]) (hpq : p ≠ q)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    (Finset.univ.filter (fun r => p.eval r = q.eval r)).card ≤ d :=
  le_trans (agreement_le_degree p q hpq)
    (le_trans (natDegree_sub_le p q) (max_le hp hq))

/-- **A separating challenge exists (PROVED).**  If the field is larger than the degree bound (`d < |F|`), distinct
degree-`≤ d` polynomials must disagree somewhere — there is a challenge `r` with `p(r) ≠ q(r)`.  This is why a random
challenge from a large field catches a cheating prover. -/
theorem few_agreements {d : ℕ} (p q : F[X]) (hpq : p ≠ q)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (hd : d < Fintype.card F) :
    ∃ r : F, p.eval r ≠ q.eval r := by
  by_contra h
  push_neg at h
  have hall : (Finset.univ.filter (fun r => p.eval r = q.eval r)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro r _; exact h r
  have : Fintype.card F ≤ d := by
    have := agreement_le_max p q hpq hp hq
    rwa [hall, Finset.card_univ] at this
  omega

/-- **The round-soundness socket (BFL).**  The honest sum-check round polynomial and the prover's claim are both degree
`≤ d` (the low-degree-extension / multilinearity bound on the arithmetized predicate), and the *multi-prover*
multilinearity test forces `MIP` rather than single-prover `IP = PSPACE`.  Stated, not proved. -/
def SumCheckRoundSoundness {d : ℕ} (honest claimed : F[X]) : Prop :=
  honest.natDegree ≤ d ∧ claimed.natDegree ≤ d

end PallLean.Paper93.DeepMath.PathB.ACC0SchwartzZippel

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SchwartzZippel.agreement_le_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SchwartzZippel.agreement_le_max
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SchwartzZippel.few_agreements
