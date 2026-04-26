import PallLean.Paper93.Paper283.BridgeABlockProductRule
import PallLean.Paper93.Paper283.BridgeAKappaTwoTouchedListExplicit

/-!
# Two-fold Leibniz expansion for κ=2 Bridge A

Given Step 1 (`BridgeAKappaTwoTouchedListExplicit.lean`) which produces a
literal explicit form for the touched-list at an interior block, this
file builds the two-fold Leibniz expansion of
`pderiv w (pderiv v (cookLevinLocalBlockQ M n hn htb hns ⟨k, _⟩))` over
that list.

## Strategy

We do **not** explicitly enumerate the (i, j) factor pairs as a finite
sum: the list is `O(numStates)` long, so a finite sum over indices
would still leave the per-state arithmetic to do.  Instead, we re-iterate
the existing `pderiv_list_prod` from
`BridgeABlockProductRule.pderiv_list_prod` *twice*, yielding a clean
recursive expression `pderivListProdSum_twice v w fs` that encodes

  `pderiv w (pderiv v fs.prod) = pderivListProdSum_twice v w fs`

as a recursive term.  The recursive form is amenable to per-target
analysis (e.g. coefficient extraction by case-splitting on the head
factor), and it is the form used by Step 3.

Two expansion shapes are exposed:

* `pderivListProdSum_twice` — generic two-fold list Leibniz.
* `pderiv_two_cookLevinLocalBlockQ` — instance specialised to the
  literal touched-list of Step 1 (uses
  `cookLevinConstraintsTouchingBlock_at_interior_block`).

No new axioms.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open PaperFaithfulSeparation
open MultilinearSPDP
open BridgeABlockProductRule

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoTwoFoldLeibnizExpansion

/-! ## Section A: generic two-fold list Leibniz expansion -/

/-- The two-fold Leibniz expansion sum, defined as the partial
derivative of `pderivListProdSum` (i.e. iterating the list-Leibniz once
on the result of the first list-Leibniz).

This is the *recursive* form; explicit (i, j) pair enumeration is
recovered by unfolding through the structure of the list. -/
noncomputable def pderivListProdSumTwice
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w : σ) (fs : List (MvPolynomial σ R)) : MvPolynomial σ R :=
  pderiv w (pderivListProdSum v fs)

@[simp] theorem pderivListProdSumTwice_nil
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R] (v w : σ) :
    pderivListProdSumTwice (R := R) v w ([] : List (MvPolynomial σ R)) = 0 := by
  unfold pderivListProdSumTwice
  rw [pderivListProdSum_nil]
  exact map_zero _

theorem pderivListProdSumTwice_cons
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R] (v w : σ)
    (x : MvPolynomial σ R) (xs : List (MvPolynomial σ R)) :
    pderivListProdSumTwice v w (x :: xs) =
      pderiv w (pderiv v x) * xs.prod
      + pderiv v x * pderiv w xs.prod
      + pderiv w x * pderivListProdSum v xs
      + x * pderivListProdSumTwice v w xs := by
  unfold pderivListProdSumTwice
  rw [pderivListProdSum_cons]
  rw [map_add]
  rw [pderiv_mul, pderiv_mul]
  ring

/-- The two-fold Leibniz product rule for a list of polynomial factors:
$$
  \partial_w \partial_v \!\left(\prod_k f_k\right)
  = \mathrm{pderivListProdSumTwice}\ v\ w\ \mathrm{fs}.
$$

The right-hand side is the recursive expansion produced by iterating
the list-Leibniz once; per Step 3, it can be unfolded into the explicit
sum over (i, j) factor pairs. -/
theorem pderiv_pderiv_list_prod
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (v w : σ) (fs : List (MvPolynomial σ R)) :
    pderiv w (pderiv v fs.prod) = pderivListProdSumTwice v w fs := by
  rw [pderiv_list_prod]
  rfl

/-! ## Section B: specialisation to `cookLevinLocalBlockQ` -/

/-- Two-fold Leibniz expansion of `pderiv w pderiv v Q_b`:

  `pderiv w (pderiv v Q_b)
   = pderivListProdSumTwice v w (touchedFactors as polynomial list)`.

This is the precise form needed by Step 3 (per-pair bilinear coefficient
calculation), since each summand is a single product of two factor
derivatives times a residual product. -/
theorem pderiv_pderiv_cookLevinLocalBlockQ
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (v w : Fin (cook_levin_compilation M n hn htb hns).numVars) :
    pderiv w (pderiv v (cookLevinLocalBlockQ M n hn htb hns b)) =
      pderivListProdSumTwice v w
        (((cookLevinConstraintsTouchingBlock
            (cook_levin_compilation M n hn htb hns) b)).map
          (fun c =>
            (1 : MvPolynomial
              (Fin (cook_levin_compilation M n hn htb hns).numVars) Rat) -
                c.poly)) := by
  unfold cookLevinLocalBlockQ
  exact pderiv_pderiv_list_prod (R := Rat) v w _

/-! ## Section C: at an interior block via Step 1's explicit touched-list -/

/-- The two-fold Leibniz expansion at an interior block, using Step 1's
literal touched-list.  This is the expansion form fed into Step 3 for
the per-pair bilinear coefficient calculation. -/
theorem pderiv_pderiv_cookLevinLocalBlockQ_at_interior_block
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (v w : Fin (cook_levin_compilation M n hn htb hns).numVars) :
    pderiv w (pderiv v (cookLevinLocalBlockQ M n hn htb hns
        ⟨k, by rw [cook_levin_numBlocks]; omega⟩)) =
      pderivListProdSumTwice v w
        ((kappaTwoTouchedList_explicit M n k hk1 hk2).map
          (fun c => (1 : MvPolynomial (Fin n) Rat) - c.poly)) := by
  rw [pderiv_pderiv_cookLevinLocalBlockQ]
  rw [cookLevinConstraintsTouchingBlock_at_interior_block
        M n hn htb hns k hk1 hk2]
  rfl

/-! ## Axiom audit anchors -/

#print axioms pderivListProdSumTwice_cons
#print axioms pderiv_pderiv_list_prod
#print axioms pderiv_pderiv_cookLevinLocalBlockQ
#print axioms pderiv_pderiv_cookLevinLocalBlockQ_at_interior_block

end BridgeAKappaTwoTwoFoldLeibnizExpansion

end PallLean.Paper93.Paper283
