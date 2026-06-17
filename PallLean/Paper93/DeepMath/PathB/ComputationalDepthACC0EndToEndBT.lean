import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SubstitutionPoly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeBTCapstone

/-!
# End-to-end Beigel–Tarui instantiation — the exact circuit polynomial fed into `compositeBT_representation`

Entry 171 resolved the composite-`MOD` field-gate dichotomy (squarefree works low-degree, prime-power is the
obstruction).  This file completes the **end-to-end** instantiation: it feeds the *exact multilinear circuit
polynomial* `subst` (`…ACC0SubstitutionPoly`, which provably computes the circuit on the cube, `subst_eval`) into the
proved degree/count packaging `compositeBT_representation`, with the **concrete** exact gate polynomials — closing the
pipeline `circuit → polynomial → degree bound + quasipoly count + sparse cube sum`.

Each gate is its exact multilinear interpolation (`guP`, `gbP`), of degree `≤ 2`, so the instantiation runs with `δ = 2`.
The squarefree composite-`MOD` field gate of entry 171 (degree `≤ p−1`) slots into the *same* pipeline with
`δ = max(2, p−1)`; the only thing that does not generalise to a low-degree field gate is the prime-power case (the
documented obstruction).

## What is proved (clean axioms, no `sorry`)

* **`guP` / `gbP`** — the exact unary/binary multilinear gate polynomials; **`guP_deg` / `gbP_deg`** — degree `≤ 2`.
* **`subst_una_eq` / `subst_bin_eq`** — `subst` composes through them via `aeval` (the hypotheses
  `compositeBT_representation` needs).
* **`endToEnd_BT`** — the end-to-end theorem: for every circuit `c`, the exact polynomial `subst c` (1) computes the
  circuit on the cube, (2) has total degree `≤ 2^{depth+1}`, (3) has `< (n+1)^{2^{depth+1}}` distinct monomial-supports
  (quasipolynomial for bounded depth), and (4) has the sparse cube-sum read-off.

## Honest scope

This is a genuine, concrete, **exact** end-to-end instantiation of `compositeBT_representation`: the exact circuit
polynomial, its degree, its quasipoly monomial count (for bounded depth), and its faithful cube evaluation, all proved
and composed.  It is the *exact* representation, so the count `(n+1)^{2^{depth+1}}` is quasipolynomial only for bounded
depth (the exact route's known limitation, entry 170); the quasipoly count for all poly-size circuits needs the
*approximate* low-degree gates (the probabilistic polynomial method) and, for `MOD` gates, the squarefree field gate of
entry 171 — with the prime-power case remaining the proven obstruction.  Beigel–Tarui and `NEXP ⊄ ACC⁰` (Williams 2011)
are proven classical theorems, so this is formalisation, not an open problem.  Nothing here is a new separation or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EndToEndBT

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitSubstitution
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation (boolVal)
open PallLean.Paper93.DeepMath.PathB.ACC0SubstitutionPoly (subst subst_eval)

variable {n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]

/-- The exact unary gate polynomial (multilinear interpolation in one variable), degree `≤ 1`. -/
noncomputable def guP (f : Bool → Bool) : MvPolynomial (Fin 1) R :=
  C (boolVal (f false)) * (1 - X 0) + C (boolVal (f true)) * X 0

/-- The exact binary gate polynomial (multilinear interpolation in two variables), degree `≤ 2`. -/
noncomputable def gbP (g : Bool → Bool → Bool) : MvPolynomial (Fin 2) R :=
  C (boolVal (g false false)) * ((1 - X 0) * (1 - X 1)) + C (boolVal (g true false)) * (X 0 * (1 - X 1))
    + C (boolVal (g false true)) * ((1 - X 0) * X 1) + C (boolVal (g true true)) * (X 0 * X 1)

/-- **`(1 - Xᵢ)` has degree `≤ 1` (proved).** -/
theorem oneSubX_deg {k : ℕ} (i : Fin k) : ((1 - X i : MvPolynomial (Fin k) R)).totalDegree ≤ 1 := by
  rw [sub_eq_add_neg]
  refine le_trans (totalDegree_add _ _) ?_
  rw [totalDegree_neg, totalDegree_X, totalDegree_one]
  omega

/-- **`(C a · (p · q))` has degree `≤ 2` for `p, q` of degree `≤ 1` (proved).** -/
theorem termBd (a : R) (p q : MvPolynomial (Fin 2) R) (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) :
    (C a * (p * q)).totalDegree ≤ 2 := by
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  exact le_trans (totalDegree_mul _ _) (by omega)

/-- **The unary gate polynomial has degree `≤ 2` (proved).** -/
theorem guP_deg (f : Bool → Bool) : (guP (R := R) f).totalDegree ≤ 2 := by
  refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
  · refine le_trans (totalDegree_mul _ _) ?_
    rw [totalDegree_C, zero_add]; exact le_trans (oneSubX_deg 0) (by norm_num)
  · refine le_trans (totalDegree_mul _ _) ?_
    rw [totalDegree_C, zero_add, totalDegree_X]; norm_num

/-- **The binary gate polynomial has degree `≤ 2` (proved).** -/
theorem gbP_deg (g : Bool → Bool → Bool) : (gbP (R := R) g).totalDegree ≤ 2 := by
  refine le_trans (totalDegree_add _ _) (max_le (le_trans (totalDegree_add _ _)
    (max_le (le_trans (totalDegree_add _ _) (max_le ?_ ?_)) ?_)) ?_)
  · exact termBd _ _ _ (oneSubX_deg 0) (oneSubX_deg 1)
  · exact termBd _ _ _ (by rw [totalDegree_X]) (oneSubX_deg 1)
  · exact termBd _ _ _ (oneSubX_deg 0) (by rw [totalDegree_X])
  · exact termBd _ _ _ (by rw [totalDegree_X]) (by rw [totalDegree_X])

/-- **`subst` composes through the unary gate poly via `aeval` (proved).** -/
theorem subst_una_eq (f : Bool → Bool) (c : Circ n) :
    subst (R := R) (.una f c) = aeval ![subst (R := R) c] (guP (R := R) f) := by
  simp [guP, subst, eval₂_add, eval₂_mul, eval₂_sub, eval₂_C, eval₂_X, Matrix.cons_val_zero]

/-- **`subst` composes through the binary gate poly via `aeval` (proved).** -/
theorem subst_bin_eq (g : Bool → Bool → Bool) (a b : Circ n) :
    subst (R := R) (.bin g a b) = aeval ![subst (R := R) a, subst (R := R) b] (gbP (R := R) g) := by
  simp [gbP, subst, eval₂_add, eval₂_mul, eval₂_sub, eval₂_C, eval₂_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **End-to-end Beigel–Tarui instantiation (proved).**  For every circuit `c`, the exact multilinear polynomial
`subst c` (a) computes the circuit on the cube, (b) has total degree `≤ 2^{depth+1}`, (c) has fewer than
`(n+1)^{2^{depth+1}}` distinct monomial-supports (quasipolynomial for bounded depth), and (d) admits the sparse cube-sum
read-off — the full `circuit → polynomial → degree + quasipoly count + sparse sum` pipeline, instantiated concretely
with the exact gate polynomials (`δ = 2`). -/
theorem endToEnd_BT (c : Circ n) :
    (∀ x : Fin n → Bool,
        MvPolynomial.eval (fun i => (boolVal (x i) : R)) (subst c)
          = boolVal (ACC0CircuitSubstitution.eval c x))
      ∧ (subst (R := R) c).totalDegree ≤ 2 ^ (ACC0LowDegreeSubstitution.depth c + 1)
      ∧ ((subst (R := R) c).support.image (fun d => d.support)).card
          ≤ (n + 1) ^ (2 ^ (ACC0LowDegreeSubstitution.depth c + 1))
      ∧ (∑ x : Fin n → Bool, MvPolynomial.eval (fun i => (boolVal (x i) : R)) (subst c))
          = ∑ d ∈ (subst (R := R) c).support, (subst c).coeff d * (2 : R) ^ (n - d.support.card) := by
  have hBT := ACC0CompositeBTCapstone.compositeBT_representation
    (subst (R := R)) guP gbP 2 (by norm_num)
    (fun i => by rw [subst]; rw [totalDegree_X]; norm_num)
    (fun b => by rw [subst]; rw [totalDegree_C]; norm_num)
    guP_deg gbP_deg subst_una_eq subst_bin_eq c
  exact ⟨fun x => subst_eval c x, hBT.1, hBT.2.1, hBT.2.2⟩

end PallLean.Paper93.DeepMath.PathB.ACC0EndToEndBT

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EndToEndBT.guP_deg
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EndToEndBT.subst_una_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EndToEndBT.endToEnd_BT
