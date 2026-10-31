import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSymLayer

/-!
# Bounding `deg P` for the composite-MOD outer gate

C12 left the composite-MOD cost as the factor `deg P` (the arithmetised outer symmetric/`MOD` gate degree) in the bound
`NFrameComplexity (boolFn P(∑∏Q)) ≤ deg P · m · t`.  This file bounds it.

A composite-`MOD` gate is a **symmetric** Boolean function — a function `g` of the *sum* of the `s` products it reads,
so `g : {0,…,s} → F`.  Over a field where the `s+1` evaluation points `0,…,s` are distinct (`char 0` or `char > s`),
Lagrange interpolation gives an arithmetisation of degree `≤ s`:

  `natDegree_symGateArith_le` — `deg (symGateArith g) ≤ N` for any gate `g : Fin (N+1) → F` (`N+1` points distinct).
  `eval_symGateArith` — the arithmetisation agrees with the gate on `{0,…,N}`.
  `natDegree_modmGate_arith_le` — the concrete composite-`MOD_m` gate: `deg ≤ N` (the fan-in).

Feeding `deg P ≤ s` into C12's `symSumProd_degree_lb_of_modq`:

  `modq_BTsize_lb` — if `MOD_q = P(∑∏Q)` on the cube with `P` a symmetric gate of fan-in `≤ s`, then `s · m · t ≥ ⌈n/2⌉`.

So a Beigel–Tarui representation of `MOD_q` — `s` products of `m` degree-`t` factors under a symmetric outer gate — has
`s · m · t ≥ ⌈n/2⌉`: a size lower bound in the raw circuit parameters, with `deg P` now bounded by the top fan-in `s`.

## The composite-MOD subtlety, honestly

The `deg P ≤ s` bound needs the `s+1` points `0,…,s` **distinct** — `char 0` or `char > s`.  Over `F_p` with `p ≤ s`
they wrap around, and instead *every* function `F_p → F_p` is degree `≤ p−1`; but a genuine composite `MOD_m` (`m`
coprime to / different from `p`) is then **not** a function of `∑ mod p` at all, so no low-degree `P(∑∏)` over `F_p`
represents it — that missing arithmetisation is the composite-MOD barrier itself.  This file bounds `deg P` exactly in
the regime where the gate *is* a low-degree symmetric polynomial (`char > s`); pushing it into the small-characteristic
composite case is the standing barrier, not crossed here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open MvPolynomial Polynomial
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- Arithmetisation of a symmetric gate `g : {0,…,N} → F` by Lagrange interpolation on the nodes `0,…,N`. -/
noncomputable def symGateArith {N : ℕ} (g : Fin (N + 1) → F) : Polynomial F :=
  Lagrange.interpolate Finset.univ (fun i : Fin (N + 1) => (i : F)) g

/-- **The degree bound (proved)**: a symmetric gate reading `N` inputs arithmetises to degree `≤ N`
(over a field where the `N+1` nodes are distinct). -/
theorem natDegree_symGateArith_le {N : ℕ} (g : Fin (N + 1) → F)
    (hinj : Set.InjOn (fun i : Fin (N + 1) => (i : F)) ↑(Finset.univ : Finset (Fin (N + 1)))) :
    (symGateArith g).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_degree_le]
  refine le_trans (Lagrange.degree_interpolate_le g hinj) ?_
  rw [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]

/-- The arithmetisation agrees with the gate on `{0,…,N}`. -/
theorem eval_symGateArith {N : ℕ} (g : Fin (N + 1) → F)
    (hinj : Set.InjOn (fun i : Fin (N + 1) => (i : F)) ↑(Finset.univ : Finset (Fin (N + 1))))
    (k : Fin (N + 1)) : eval ((k : F)) (symGateArith g) = g k :=
  Lagrange.eval_interpolate_at_node g hinj (Finset.mem_univ k)

/-- The composite-`MOD_m` gate as a symmetric function of the sum `k ∈ {0,…,N}`. -/
noncomputable def modmGate (m N : ℕ) : Fin (N + 1) → F := fun k => if (k : ℕ) % m = 0 then 1 else 0

/-- **The composite-MOD gate arithmetises to degree `≤` its fan-in (proved).** -/
theorem natDegree_modmGate_arith_le (m N : ℕ)
    (hinj : Set.InjOn (fun i : Fin (N + 1) => (i : F)) ↑(Finset.univ : Finset (Fin (N + 1)))) :
    (symGateArith (modmGate m N : Fin (N + 1) → F)).natDegree ≤ N :=
  natDegree_symGateArith_le _ hinj

/-- **The Beigel–Tarui size lower bound for `MOD_q` (proved)**: if `MOD_q = P(∑∏Q)` on the cube with `P` a symmetric
outer gate of fan-in `≤ s` (so `deg P ≤ s`), then `s · m · t ≥ ⌈n/2⌉`.  The composite-MOD `deg P` factor is now bounded
by the top fan-in `s`, giving a size bound in the raw circuit parameters. -/
theorem modq_BTsize_lb [Fintype F] [DecidableEq F] {s m t q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (P : Polynomial F)
    (Q : Fin s → Fin m → MvPolynomial (Fin n) F) (ht : ∀ i j, (Q i j).totalDegree ≤ t)
    (hPdeg : P.natDegree ≤ s)
    (heq : omegaFn ω (Finset.univ : Finset (Fin n)) = boolFn (Polynomial.aeval (∑ i, ∏ j, Q i j) P)) :
    n - n / 2 ≤ s * (m * t) :=
  le_trans (symSumProd_degree_lb_of_modq ω hω hq2 P Q ht heq)
    (Nat.mul_le_mul hPdeg (le_refl _))

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.natDegree_symGateArith_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.natDegree_modmGate_arith_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.modq_BTsize_lb
