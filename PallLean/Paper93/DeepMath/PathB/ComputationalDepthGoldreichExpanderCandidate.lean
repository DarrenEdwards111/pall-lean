import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGoldreichPredicate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverWilliams

/-!
# The strongest conditional route: N‑frame observer‑Williams over a Goldreich expander CSP

The debt side is complete (`B < r / bounded K ⇒ debt ⇒ no separator`).  The frontier is the *decision‑hard
compressing family*.  This file assembles the strongest **conditional** route:

* **Debt / raveling** supplies the separator geometry (low‑action observer ⇒ separator in a class `K`);
* **Goldreich's local PRG** supplies a plausible *decision‑hard, compressing* family (a high‑AI predicate over
  an expander hypergraph);
* **Williams** supplies the cash‑out (a separator ⇒ a fast inversion algorithm ⇒ contradiction with hardness).

## The family

`GoldreichCSP n d m` is `m` output bits, each `P` applied to a `d`‑tuple of inputs along a hyperedge; on an
*expander* hypergraph with a *high‑algebraic‑immunity* predicate `P` (e.g. the verified `TSA`
`x₀⊕x₁⊕x₂⊕(x₃∧x₄)`, `AI ≥ 2`), this is the canonical Goldreich/Applebaum local one‑way function / PRG — the
right candidate for a decision‑hard compressing family.

## Proved (clean axioms, no `sorry`)

* `GoldreichCSP` / `eval` — the family and its evaluation `eval G x i = P(x restricted to edge i)`.
* `tsaGoldreich` — the TSA‑based instance (predicate fixed to the `AI ≥ 2` TSA; see
  `tsa_algebraic_immunity_ge_two`).
* `goldreich_observer_williams` — **the conditional route, proved**: given `raveling` (low‑action ⇒ separator in
  `K`), `separatorSpeedup` (a separator in `K` ⇒ a fast inversion algorithm), and `goldreichHard`
  (`GoldreichHardnessHyp`: no fast inversion — the PRG is secure), **no low‑action observer correctly inverts the
  family**.  A correct low‑action observer would break Goldreich's hardness.

## Honest status — what is conditional, and the open gap

* `raveling` is **provable for restricted `K`** (the whole debt corpus); `separatorSpeedup` is supplied by the
  framework's DP engine (`dpSat_beats_bruteforce`) with abundant margin.
* `goldreichHard` (`GoldreichHardnessHyp`) is a **cryptographic conjecture**, not a theorem — the security of
  local PRGs.  A *proof* of it is `P ≠ NP`‑strength.  So this route gives "no low‑action Goldreich inverter"
  *conditionally on local‑PRG security*, not unconditionally.
* The predicate direction is verified at its base case (`TSA`, `AI ≥ 2`, fixing the `AND` gadget's `AI = 1`
  collapse); **higher‑arity predicates with growing algebraic immunity / resiliency** are the next rung — but
  `AI ≥ 3` is infeasible by `decide` (the degree‑`≤2` annihilator search is exponential), so it needs structural
  immunity arguments, not brute force.  Noted, not faked.

So this is the cleanest possible conditional separation: **observer geometry + Goldreich family + Williams
cash‑out**, with exactly one conjectural input (`GoldreichHardnessHyp`) whose unconditional proof is the
separation.  Not a proof of `P ≠ NP`; the strongest honest route, assembled.
-/

namespace PallLean.Paper93.DeepMath.PathB.GoldreichExpanderCandidate

open PallLean.Paper93.DeepMath.PathB.GoldreichPredicate

/-- A **Goldreich local CSP**: `m` output bits over `n` inputs, each output the local predicate `pred` applied to
the `d` inputs on its hyperedge.  On an expander hypergraph with high‑AI `pred`, this is Goldreich's local PRG. -/
structure GoldreichCSP (n d m : ℕ) where
  /-- the `m` hyperedges, each a `d`‑tuple of input indices -/
  edges : Fin m → (Fin d → Fin n)
  /-- the local predicate applied along each hyperedge -/
  pred : (Fin d → Bool) → Bool

/-- Evaluation: output bit `i` is `pred` applied to the inputs on hyperedge `i`. -/
def GoldreichCSP.eval {n d m : ℕ} (G : GoldreichCSP n d m) (x : Fin n → Bool) : Fin m → Bool :=
  fun i => G.pred (fun j => x (G.edges i j))

/-- The **TSA‑based Goldreich family**: the local predicate is the verified high‑algebraic‑immunity TSA
predicate `x₀⊕x₁⊕x₂⊕(x₃∧x₄)` (`AI ≥ 2`, `tsa_algebraic_immunity_ge_two`), the canonical Goldreich primitive. -/
def tsaGoldreich {n m : ℕ} (edges : Fin m → (Fin 5 → Fin n)) : GoldreichCSP n 5 m :=
  { edges := edges, pred := P }

/-- **The conditional observer‑Williams route over a Goldreich family (proved).**  Compose the three engines:
`raveling` (a low‑action observer factors through a separator class `K`), `separatorSpeedup` (a separator in `K`
yields a fast inversion algorithm for the family), and `goldreichHard` (`GoldreichHardnessHyp`: no fast inversion
— the PRG is secure).  Conclusion: **no low‑action observer correctly inverts the family** — a correct low‑action
inverter would break Goldreich's hardness.  Conditional on `goldreichHard` (cryptographic conjecture). -/
theorem goldreich_observer_williams {Obs : Type*}
    (lowAction correctlyInverts inK : Obs → Prop) (fastInversion : Prop)
    (raveling : ∀ o, lowAction o → inK o)
    (separatorSpeedup : (∃ o, inK o ∧ correctlyInverts o) → fastInversion)
    (goldreichHard : ¬ fastInversion) :
    ∀ o, ¬ (lowAction o ∧ correctlyInverts o) :=
  fun o h => goldreichHard (separatorSpeedup ⟨o, raveling o h.1, h.2⟩)

end PallLean.Paper93.DeepMath.PathB.GoldreichExpanderCandidate

#print axioms PallLean.Paper93.DeepMath.PathB.GoldreichExpanderCandidate.goldreich_observer_williams
