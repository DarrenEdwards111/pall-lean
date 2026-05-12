import PallLean.Paper93.Paper283.BridgeACookLevinLocalQvCandidate
import PallLean.ProductDeriv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Block product rule for `cookLevinLocalBlockQ`

The polynomial `cookLevinLocalBlockQ M n hn htb hns b` is defined in
`BridgeACookLevinLocalQvCandidate.lean` as the `List.prod` of the
factors `(1 - c.poly)` ranging over the filtered Cook-Levin constraints
touching the locality block `b`.

This file packages the standard partial derivative product rule
(Leibniz rule) for `MvPolynomial.pderiv` applied to such a list product.
For an arbitrary list of polynomial factors `fs = [f_0, f_1, ..., f_{n-1}]`
and a variable `X_v`, the product rule states that
$$
   \partial_v\!\left(\prod_{k < n} f_k\right)
   = \sum_{k < n}\, (\partial_v f_k)\,
     \prod_{j \ne k}\, f_j .
$$
We express this at list level by induction on the list, encoding the
right-hand side as the recursively-defined sum `pderivListProdSum`.

We then specialize this rule to the `cookLevinLocalBlockQ` factors, which
have shape `1 - c.poly` for `c` ranging over the filtered constraints
`cookLevinConstraintsTouchingBlock T b`.  Because `pderiv` is `R`-linear and
`pderiv (1) = 0`, each derivative factor simplifies to `- pderiv X_v c.poly`
in the signed expansion `pderivListProdSumNeg`.

The proof of the generic list Leibniz rule reuses one core fact already in
Mathlib:

* `MvPolynomial.pderiv_mul`           -- two-factor Leibniz rule.

No new axioms are introduced.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open PaperFaithfulSeparation
open MultilinearSPDP

attribute [local instance] Classical.dec

namespace BridgeABlockProductRule

/-! ## Generic Leibniz product rule for a list of polynomial factors -/

/--
The polynomial Leibniz sum corresponding to the product rule on a list:
for a cons `x :: xs`, the contribution is `pderiv i x * xs.prod` plus
`x` times the recursive Leibniz sum on `xs`.  Unfolding the recursion,
this equals
$$
   \sum_k \Big(\textstyle\prod_{j<k} f_j\Big)\,(\partial_i f_k)\,
            \Big(\textstyle\prod_{j>k} f_j\Big),
$$
which is the explicit form of the partial-derivative product rule. -/
noncomputable def pderivListProdSum
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (i : σ) : List (MvPolynomial σ R) → MvPolynomial σ R
  | [] => 0
  | x :: xs => pderiv i x * xs.prod + x * pderivListProdSum i xs

@[simp] theorem pderivListProdSum_nil
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R] (i : σ) :
    pderivListProdSum (R := R) i ([] : List (MvPolynomial σ R)) = 0 := rfl

@[simp] theorem pderivListProdSum_cons
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (i : σ) (x : MvPolynomial σ R) (xs : List (MvPolynomial σ R)) :
    pderivListProdSum i (x :: xs) =
      pderiv i x * xs.prod + x * pderivListProdSum i xs := rfl

/-- The list-version of the partial-derivative product rule (Leibniz):
for any list `fs` of polynomial factors and any variable `i`,
$$
  \partial_i\!\left(\textstyle\prod fs\right)
  \;=\; \sum_k (\partial_i f_k) \cdot \prod_{j \neq k} f_j ,
$$
where the right-hand side is encoded recursively as `pderivListProdSum`.

The proof is a straightforward induction on `fs`, using
`MvPolynomial.pderiv_mul` at each step. -/
theorem pderiv_list_prod
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (i : σ) (fs : List (MvPolynomial σ R)) :
    pderiv i fs.prod = pderivListProdSum i fs := by
  induction fs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.prod_cons, pderiv_mul, pderivListProdSum_cons, ih]

/-! ## Signed version for `(1 - g c)` factors -/

/--
The signed Leibniz sum for factors of the form `(1 - g c)`: each
derivative factor is `-pderiv i (g c)`.  This is the explicit
sign-extracted form of the product rule on a list of `(1 - g c)`
factors, and is the form that arises when differentiating
`cookLevinLocalBlockQ` (where `g c = c.poly`).
-/
noncomputable def pderivListProdSumNeg
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (i : σ) {ι : Type*} :
    List ι → (ι → MvPolynomial σ R) → MvPolynomial σ R
  | [], _ => 0
  | c :: cs, g =>
      (- pderiv i (g c)) *
        (cs.map (fun c => (1 : MvPolynomial σ R) - g c)).prod
      + ((1 : MvPolynomial σ R) - g c) * pderivListProdSumNeg i cs g

@[simp] theorem pderivListProdSumNeg_nil
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R] (i : σ)
    {ι : Type*} (g : ι → MvPolynomial σ R) :
    pderivListProdSumNeg (R := R) i ([] : List ι) g = 0 := rfl

@[simp] theorem pderivListProdSumNeg_cons
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R] (i : σ)
    {ι : Type*} (c : ι) (cs : List ι) (g : ι → MvPolynomial σ R) :
    pderivListProdSumNeg i (c :: cs) g =
      (- pderiv i (g c)) *
        (cs.map (fun c => (1 : MvPolynomial σ R) - g c)).prod
      + ((1 : MvPolynomial σ R) - g c) *
        pderivListProdSumNeg i cs g := rfl

/-- The per-factor derivative of `1 - c.poly` is `- pderiv v c.poly`. -/
theorem pderiv_one_sub_poly
    {N : Nat} (v : Fin N) (c : LocalConstraint N) :
    pderiv v ((1 : MvPolynomial (Fin N) Rat) - c.poly) =
      - pderiv v c.poly := by
  rw [map_sub, pderiv_one]
  ring

/--
A list-Leibniz rewrite specialised to factors of the form `(1 - g c)`
indexed by elements of an underlying list `cs`.  The Leibniz sum then
becomes the signed recursive sum `pderivListProdSumNeg`, where each
derivative factor is explicitly negated.

This is the precise form of the partial derivative product rule
applied to a list of `(1 - g c)` factors.
-/
theorem pderivListProdSum_one_sub_map
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (i : σ) {ι : Type*} (cs : List ι) (g : ι → MvPolynomial σ R) :
    pderivListProdSum i (cs.map (fun c => (1 : MvPolynomial σ R) - g c)) =
      pderivListProdSumNeg i cs g := by
  induction cs with
  | nil =>
      simp [pderivListProdSum_nil, pderivListProdSumNeg_nil]
  | cons c cs ih =>
      rw [List.map_cons, pderivListProdSum_cons, pderivListProdSumNeg_cons, ih]
      have hone_sub :
          pderiv i ((1 : MvPolynomial σ R) - g c) = - pderiv i (g c) := by
        rw [map_sub, pderiv_one]; ring
      rw [hone_sub]

/-! ## Specialisation to `cookLevinLocalBlockQ` -/

/-- Generic-form Leibniz expansion of `pderiv v (cookLevinLocalBlockQ ...)`.

The right-hand side is the recursive Leibniz sum on the list of factors
`(1 - c.poly)` ranging over the filtered constraints touching block `b`. -/
theorem pderiv_cookLevinLocalBlockQ
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (v : Fin (cook_levin_compilation M n hn htb hns).numVars) :
    pderiv v (cookLevinLocalBlockQ M n hn htb hns b) =
      pderivListProdSum v
        (((cookLevinConstraintsTouchingBlock
            (cook_levin_compilation M n hn htb hns) b)).map
          (fun c =>
            (1 : MvPolynomial
              (Fin (cook_levin_compilation M n hn htb hns).numVars) Rat) -
                c.poly)) := by
  unfold cookLevinLocalBlockQ
  exact pderiv_list_prod (R := Rat) v _

/--
Sign-extracted form of the Leibniz product rule for the
`cookLevinLocalBlockQ` factors.

For each filtered constraint `c`, the factor `(1 - c.poly)` differentiates
to `- pderiv v c.poly`.  The list-Leibniz expansion of `pderiv v Q_b` is
therefore the signed recursive sum `pderivListProdSumNeg`, which encodes
$$
   \partial_v Q_b
   \;=\;
   \sum_{c \in cs}\,
     (-\partial_v c.\mathrm{poly})\,
     \prod_{c' \in cs,\; c' \neq c} (1 - c'.\mathrm{poly}) ,
$$
with `cs := cookLevinConstraintsTouchingBlock T b`.
-/
theorem pderiv_cookLevinLocalBlockQ_signed
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (v : Fin (cook_levin_compilation M n hn htb hns).numVars) :
    pderiv v (cookLevinLocalBlockQ M n hn htb hns b) =
      pderivListProdSumNeg v
        (cookLevinConstraintsTouchingBlock
          (cook_levin_compilation M n hn htb hns) b)
        (fun c => c.poly) := by
  rw [pderiv_cookLevinLocalBlockQ]
  exact pderivListProdSum_one_sub_map (R := Rat) v _ _

/-! ## Axiom audit anchors -/

#print axioms pderiv_list_prod
#print axioms pderiv_one_sub_poly
#print axioms pderivListProdSum_one_sub_map
#print axioms pderiv_cookLevinLocalBlockQ
#print axioms pderiv_cookLevinLocalBlockQ_signed

end BridgeABlockProductRule

end PallLean.Paper93.Paper283
