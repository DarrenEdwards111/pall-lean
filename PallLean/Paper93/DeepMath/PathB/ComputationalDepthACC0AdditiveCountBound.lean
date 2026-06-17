import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeBTCapstone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTExactCompose

/-!
# The additive count bound — degree-governed count is quasipoly; the exact gate-count blows up

Entry 169 located the Beigel–Tarui wall precisely: in the *exact* `SYM∘AND` form the fan-in is `≤ 1`, so the bottleneck
is the **count** of AND gates, which the exact construction tracks as `symAndSize` — *multiplicative* `s₁+(s₁+1)·s₂` at
every `AND`/`OR`.  This file makes the two count regimes explicit and contrasts them:

* **Degree-governed count is quasipolynomial (proved).**  The polynomial-method representation
  (`…ACC0CompositeBTCapstone.compositeBT_representation`) has monomial-support count `≤ (n+1)^{δ^{depth+1}}`.  For a
  polylog gate-degree `δ ≤ L` and *constant* depth `depth ≤ D`, this is `≤ (n+1)^{L^{D+1}}` — quasipolynomial
  (`n^{polylog}`).  The count is governed *additively*, through the degree recurrence `δ^{depth+1}`, not through the
  number of gates.

* **The exact gate-count blows up (proved).**  The multiplicative recurrence makes `symAndSize` grow at least
  exponentially: a balanced `AND`-tree of depth `d` has `symAndSize ≥ 2^d`.  So the *exact* `SYM∘AND` form is not
  quasipolynomial-size, which is exactly why Beigel–Tarui replaces it with the degree-governed (polynomial-method)
  count.

## What is proved (clean axioms, no `sorry`)

* **`count_quasipoly_of_degree_bound`** — `cnt ≤ (n+1)^{δ^e}`, `δ ≤ L`, `e ≤ E` ⇒ `cnt ≤ (n+1)^{L^E}` (the
  degree-governed count is quasipoly for polylog `L` and constant `E`).
* **`compositeBT_count_quasipoly`** — applied to `compositeBT_representation`: the circuit-polynomial monomial count is
  `≤ (n+1)^{L^{D+1}}` when `δ ≤ L` and `depth c ≤ D`.
* **`symAndSize_andTree_ge`** — the exact gate-count of a balanced depth-`d` `AND`-tree is `≥ 2^d` (multiplicative
  blow-up; not quasipoly).

## Honest scope

The degree-governed count bound is quasipolynomial and is proved (built on the already-proved
`compositeBT_representation`); the exact gate-count is shown to blow up.  This sharpens *why* the additive (degree)
route is the right one — but `compositeBT_representation` is a generic packaging over a `CommRing`, and instantiating it
for an actual `ACC⁰` circuit needs the gate polynomials, which over a field exist only for prime-power `MOD` (the
documented composite-`MOD` obstruction).  So the quasipoly *count* is established; the remaining gap is the gate-poly
instantiation for composite `MOD` — and the Beigel–Tarui theorem and `NEXP ⊄ ACC⁰` (Williams 2011) are proven classical
results, so this is formalisation, not an open problem.  Nothing here is a new separation or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AdditiveCountBound

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose (symAndSize)

/-- **The degree-governed count is quasipolynomial (proved).**  A count bounded by `(n+1)^{δ^e}` is bounded by
`(n+1)^{L^E}` whenever `δ ≤ L` and `e ≤ E` — for polylog `L` and *constant* `E` this is `n^{polylog}`, quasipolynomial.
The count is controlled by the degree exponent `δ^e`, not by the number of gates. -/
theorem count_quasipoly_of_degree_bound (n cnt δ e L E : ℕ) (hL : 1 ≤ L) (hδ : δ ≤ L) (he : e ≤ E)
    (hcnt : cnt ≤ (n + 1) ^ (δ ^ e)) : cnt ≤ (n + 1) ^ (L ^ E) := by
  refine le_trans hcnt (Nat.pow_le_pow_right (by omega) ?_)
  exact le_trans (Nat.pow_le_pow_left hδ e) (Nat.pow_le_pow_right hL he)

/-- **The composite-BT circuit-polynomial count is quasipolynomial (proved).**  Applying
`count_quasipoly_of_degree_bound` to the `(n+1)^{δ^{depth+1}}` monomial-support bound of
`compositeBT_representation`: for polylog gate-degree `δ ≤ L` and constant depth `depth c ≤ D`, the monomial count is
`≤ (n+1)^{L^{D+1}}`. -/
theorem compositeBT_count_quasipoly {n : ℕ} {R : Type*} [CommRing R]
    (Q : ACC0CircuitSubstitution.Circ n → MvPolynomial (Fin n) R)
    (gu : (Bool → Bool) → MvPolynomial (Fin 1) R) (gb : (Bool → Bool → Bool) → MvPolynomial (Fin 2) R)
    (δ : ℕ) (hδ1 : 1 ≤ δ)
    (hinp : ∀ i, (Q (.inp i)).totalDegree ≤ δ) (hcst : ∀ b, (Q (.cst b)).totalDegree ≤ δ)
    (hgu : ∀ f, (gu f).totalDegree ≤ δ) (hgb : ∀ g, (gb g).totalDegree ≤ δ)
    (huna_eq : ∀ f c, Q (.una f c) = MvPolynomial.aeval ![Q c] (gu f))
    (hbin_eq : ∀ g a b, Q (.bin g a b) = MvPolynomial.aeval ![Q a, Q b] (gb g))
    (c : ACC0CircuitSubstitution.Circ n) (L D : ℕ) (hL : 1 ≤ L) (hδL : δ ≤ L)
    (hdepth : ACC0LowDegreeSubstitution.depth c ≤ D) :
    ((Q c).support.image (fun d => d.support)).card ≤ (n + 1) ^ (L ^ (D + 1)) := by
  have hcount := (ACC0CompositeBTCapstone.compositeBT_representation
    Q gu gb δ hδ1 hinp hcst hgu hgb huna_eq hbin_eq c).2.1
  exact count_quasipoly_of_degree_bound n _ δ (ACC0LowDegreeSubstitution.depth c + 1) L (D + 1)
    hL hδL (by omega) hcount

/-- A balanced `AND`-tree of depth `d` over a fixed variable `i`. -/
def andTree {n : ℕ} (i : Fin n) : ℕ → ACC0Circuit n
  | 0 => .var i
  | (d + 1) => .and (andTree i d) (andTree i d)

/-- **The exact gate-count blows up (proved): a depth-`d` balanced `AND`-tree has `symAndSize ≥ 2^d`.**  The
multiplicative recurrence `symAndSize (AND a b) = sₐ + (sₐ+1)·s_b` makes the exact `SYM∘AND` count grow at least
exponentially — so the exact form is *not* quasipolynomial-size, and Beigel–Tarui must use the degree-governed count
(`count_quasipoly_of_degree_bound`) instead. -/
theorem symAndSize_andTree_ge {n : ℕ} (i : Fin n) :
    ∀ d, 2 ^ d ≤ symAndSize (andTree i d)
  | 0 => by simp [andTree, symAndSize]
  | (d + 1) => by
    have ih := symAndSize_andTree_ge i d
    have hrec : symAndSize (andTree i (d + 1))
        = symAndSize (andTree i d) + (symAndSize (andTree i d) + 1) * symAndSize (andTree i d) := by
      simp [andTree, symAndSize]
    rw [hrec, pow_succ]
    nlinarith [ih]

end PallLean.Paper93.DeepMath.PathB.ACC0AdditiveCountBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AdditiveCountBound.count_quasipoly_of_degree_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AdditiveCountBound.compositeBT_count_quasipoly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AdditiveCountBound.symAndSize_andTree_ge
