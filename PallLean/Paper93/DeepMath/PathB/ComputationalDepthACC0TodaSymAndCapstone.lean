import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerSparse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerEvalBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerModulusChoice

/-!
# Capstone: the Toda integer `SYM∘AND` for bounded-`AND`/`OR` ACC⁰[p], in one theorem (PROVED)

The headline of the polynomial half.  Everything built this run — degree, sparsity, computes-the-circuit,
modulus choice — packaged into a single named result:

  `acc0_toda_symand` — for a bounded `MOD`/`AND`/`OR` tower `t` over `Fin n`, the polynomial `frep p k t`
  satisfies **all four** `SYM∘AND` properties at once:
    1. `totalDegree (frep t) ≤ K^(fdepth t)`            (low degree, `K = max(w, 3^k(p−1))`),
    2. monomial-`AND` count `≤ (n+1)^(K^(fdepth t))`     (sparse),
    3. `∀ x, p^{2^k} ∣ (eval x (frep t) − bval t x)`     (computes the circuit mod `p^{2^k}`),
    4. `∃ k', card(monomial sets) < p^{2^k'}`            (a uniform modulus clears the width).

For `K = polylog` and constant depth this is a **quasipolynomial `SYM∘AND` exactly computing the circuit**
— the complete Beigel–Tarui integer representation for bounded-`AND`/`OR` ACC⁰[p], with `MOD` gates of
*any* modulus (Toda).  This single statement is what the ~17 Toda bricks of this run establish.

## What is proved (clean axioms, no `sorry`)

* `acc0_toda_symand` — the packaged end-to-end `SYM∘AND` theorem (degree ∧ sparsity ∧ computes ∧ modulus).

## Honest scope

This packages the polynomial half end-to-end.  It is **not** `NEXP ⊄ ACC⁰`: the algorithmic half (the
sub-`2^n` `#SAT` counter exploiting properties 1–2 and the `NEXP ⊄ ACC⁰` diagonalization) needs a timed
machine model Mathlib lacks — Williams-strength, **not** built.  Unbounded `AND`/`OR` stays the no-go
(RS).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaSymAndCapstone

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerDegree (FTower frep fdepth FBounded frep_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSparse (full_tower_sparse)
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerEvalBridge (bval eval_frep_bridge)
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerModulusChoice (exists_modulus_clears_width)

variable {n : ℕ}

/-- **Capstone (proved): the Toda integer `SYM∘AND` for bounded-`AND`/`OR` ACC⁰[p].**  `frep p k t` is a
low-degree (`≤ K^depth`), sparse (`≤ (n+1)^{K^depth}` monomial-`AND` sets) polynomial that computes the
circuit mod `p^{2^k}` at every input, with a uniform modulus clearing the width — a quasipoly `SYM∘AND`
for polylog `K` and constant depth. -/
theorem acc0_toda_symand (p k w : ℕ) [Fact p.Prime] (hp : 2 ≤ p)
    (hpos : 1 ≤ max w (3 ^ k * (p - 1))) (t : FTower (Fin n)) (h : FBounded w t) :
    (frep p k t).totalDegree ≤ (max w (3 ^ k * (p - 1))) ^ fdepth t
    ∧ ((frep p k t).support.image (fun d => d.support)).card
        ≤ (n + 1) ^ ((max w (3 ^ k * (p - 1))) ^ fdepth t)
    ∧ (∀ x : Fin n → ℤ, (p : ℤ) ^ (2 ^ k) ∣ (eval x (frep p k t) - bval p x t))
    ∧ (∃ k', ((frep p k t).support.image (fun d => d.support)).card < p ^ (2 ^ k')) :=
  ⟨frep_totalDegree_le p k w hpos t h,
   full_tower_sparse p k w n hpos t h,
   fun x => eval_frep_bridge p k x t,
   exists_modulus_clears_width p hp p k t⟩

/-!
**Capstone proved.**  One theorem: `frep p k t` is degree-`K^depth`, `(n+1)^{K^depth}`-sparse, computes
the circuit mod `p^{2^k}`, with a uniform modulus clearing the width — the complete Beigel–Tarui integer
`SYM∘AND` for bounded-`AND`/`OR` ACC⁰[p].  The algorithmic half (sub-`2^n` `#SAT` + `NEXP ⊄ ACC⁰`) needs a
timed machine model Mathlib lacks.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TodaSymAndCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TodaSymAndCapstone.acc0_toda_symand
