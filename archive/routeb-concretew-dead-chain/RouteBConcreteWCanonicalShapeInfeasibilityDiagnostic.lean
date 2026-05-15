import PallLean.Paper93.DeepMath.PathB.ConcreteWFactorMembership

/-!
# Diagnostic — `CookLevinCanonicalConcreteWShapeWitnesses` is infeasible at `n ≥ 2`

This file is a pressure-test diagnostic, in the same spirit as
`routeBFiberPartitionWitnessSkeletonLemma31Obligation_fullProduct_mem_booleanity`
and Codex's `routeBPaperFaithfulTPhi_strictSourceWitnessedLeibnizNFOfWordEventAtomQDim_rowWitness_unshiftedProduct_mem_atomSpan`.

It records a positive theorem proving that the canonical-shape route
through `concreteW (Fin.castLEEmb hn4)` cannot fire at the compilation
scale: `CookLevinCanonicalConcreteWShapeWitnesses` claims every Cook–Levin
booleanity factor equals the fixed polynomial `1 - X(0) + X(0)²`, but the
actual booleanity factor at index `1` (which exists for `n ≥ 2`) uses the
variable `X(1)`. The two polynomials separate under evaluation, so the
canonical-shape Prop cannot hold globally.

**Consequence:** `CookLevinFactorMemPerType_concreteW_of_canonicalShapeWitnesses`
is well-typed but rests on an unsatisfiable hypothesis at any compilation
with `n ≥ 2`. Future attempts to inhabit the Lemma 31 Property 1 chain
through `concreteW (Fin.castLEEmb hn4)` should instead use the
`directBranchShapes + canonicalRowTransport` route, or pivot to
`interfaceSpace_compiledBasis`, which is parameterised over coordinate
embeddings.

This is the kind of "name the wrong shape, prove it wrong" pressure
test introduced earlier in the chain. CLAUDE.md "DO NOT SIMPLIFY proofs"
applies: nothing is simplified or hidden behind `sorry`; the
infeasibility is fully proved.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93
open PaperFaithfulSeparation

/-! ## Auxiliary polynomial-separation fact -/

/-- The two polynomials `1 - X(0) + X(0)²` and `1 - X(1) + X(1)²` are
distinct in `MvPolynomial (Fin n) ℚ` for `n ≥ 2`. Separated by
evaluation at `X(0) := 2, X(j) := 0` for `j ≠ 0`. -/
theorem booleanityFactor_at_zero_ne_at_one
    (n : ℕ) (hn : n ≥ 2) :
    (1 - MvPolynomial.X (⟨0, by omega⟩ : Fin n)
        + (MvPolynomial.X (⟨0, by omega⟩ : Fin n)) ^ 2
      : MvPolynomial (Fin n) ℚ) ≠
    (1 - MvPolynomial.X (⟨1, by omega⟩ : Fin n)
        + (MvPolynomial.X (⟨1, by omega⟩ : Fin n)) ^ 2
      : MvPolynomial (Fin n) ℚ) := by
  intro hEq
  -- Apply `MvPolynomial.eval` at `f j := if j = ⟨0, _⟩ then 2 else 0`.
  let f : Fin n → ℚ := fun j => if j = ⟨0, by omega⟩ then 2 else 0
  have hEvalEq :
      MvPolynomial.eval f
          (1 - MvPolynomial.X (⟨0, by omega⟩ : Fin n)
            + (MvPolynomial.X (⟨0, by omega⟩ : Fin n)) ^ 2) =
        MvPolynomial.eval f
          (1 - MvPolynomial.X (⟨1, by omega⟩ : Fin n)
            + (MvPolynomial.X (⟨1, by omega⟩ : Fin n)) ^ 2) := by
    rw [hEq]
  -- Compute both sides explicitly.
  have hzero_ne_one : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) := by
    intro h
    have : (0 : ℕ) = 1 := by simpa using congrArg Fin.val h
    omega
  have hLHS :
      MvPolynomial.eval f
          (1 - MvPolynomial.X (⟨0, by omega⟩ : Fin n)
            + (MvPolynomial.X (⟨0, by omega⟩ : Fin n)) ^ 2) = (3 : ℚ) := by
    simp [f, MvPolynomial.eval_X]
    norm_num
  have hRHS :
      MvPolynomial.eval f
          (1 - MvPolynomial.X (⟨1, by omega⟩ : Fin n)
            + (MvPolynomial.X (⟨1, by omega⟩ : Fin n)) ^ 2) = (1 : ℚ) := by
    have h1 : f (⟨1, by omega⟩ : Fin n) = 0 := by
      simp [f, hzero_ne_one.symm]
    simp [f, MvPolynomial.eval_X]
  -- From hEvalEq, hLHS, hRHS we get `(3 : ℚ) = 1`, contradiction.
  rw [hLHS, hRHS] at hEvalEq
  norm_num at hEvalEq

/-! ## Cook–Levin factor at index 1 has the variable-1 form -/

/-- The Cook–Levin compiled factor list, at any index `i` with `i.val < n`,
is the booleanity factor `1 - X(i) + X(i)²`. This unpacks the prefix-of-`++`
indexing for booleanity factors. -/
theorem cookLevinFactorList_get_booleanity_explicit
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hi : i.val < n) :
    (cookLevinFactorList M n hn htb hns).get i =
      (1 - MvPolynomial.X (⟨i.val, by omega⟩ : Fin n)
          + (MvPolynomial.X (⟨i.val, by omega⟩ : Fin n)) ^ 2
        : MvPolynomial (Fin n) ℚ) := by
  classical
  -- Convert to getElem and use getElem_map / getElem_append_left.
  have hbool : (boolConstraintList n).length = n := boolConstraintList_length n
  rw [List.get_eq_getElem]
  -- Step 1: unfold cookLevinFactorList = (boolList ++ adjList ++ transList).map (1 - ·.poly).
  unfold cookLevinFactorList cook_levin_compilation
  -- The booleanity prefix `boolConstraintList n` has length n ≥ i.val.
  have hi_bool : i.val < (boolConstraintList n).length := by rw [hbool]; exact hi
  -- The full constraint list is `boolConstraintList n ++ adjConstraintList n ++ transSkelConstraintList M n`.
  have h_in_bool_prefix :
      i.val < (boolConstraintList n ++ adjConstraintList n).length := by
    rw [List.length_append, hbool]; omega
  -- Compute via getElem on map and append.
  simp only [List.getElem_map, List.getElem_append_left h_in_bool_prefix,
    List.getElem_append_left hi_bool]
  -- Reduce boolConstraintList: it's `(List.finRange n).map (boolLC n)`.
  show (1 : MvPolynomial (Fin n) ℚ) - ((boolConstraintList n)[i.val]'hi_bool).poly =
    1 - MvPolynomial.X (⟨i.val, by omega⟩ : Fin n)
      + (MvPolynomial.X (⟨i.val, by omega⟩ : Fin n)) ^ 2
  have h_bool_idx :
      ((boolConstraintList n)[i.val]'hi_bool) = boolLC n ⟨i.val, hi⟩ := by
    unfold boolConstraintList
    rw [List.getElem_map]
    congr 1
    simp [List.getElem_finRange]
  rw [h_bool_idx]
  -- Unfold boolLC.poly = boolPoly' = X · (1 - X), then ring.
  unfold boolLC boolPoly'
  ring

/-! ## Main diagnostic -/

/-- **Infeasibility diagnostic.** For any compilation with `n ≥ 2`, the
canonical-shape Prop `CookLevinCanonicalConcreteWShapeWitnesses` is
false.

The argument: at index `1 < n`, the constraint type is `booleanity`
(by `cookLevinConstraintType_eq_booleanity`), so the canonical-shape
hypothesis would force `(cookLevinFactorList _).get ⟨1, _⟩ = 1 - X(0) + X(0)²`.
But the actual factor at index `1` equals `1 - X(1) + X(1)²`
(`cookLevinFactorList_get_booleanity_explicit`). The two polynomials
separate under evaluation (`booleanityFactor_at_zero_ne_at_one`),
contradiction. -/
theorem cookLevinCanonicalConcreteWShapeWitnesses_infeasible
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ CookLevinCanonicalConcreteWShapeWitnesses M n hn htb hns hn4 := by
  intro hShape
  -- Index 1 is valid: `(cookLevinFactorList _).length ≥ n ≥ 2`.
  have hLenGe : (cookLevinFactorList M n hn htb hns).length ≥ n := by
    -- The factor list has length equal to the constraint list length,
    -- which is at least n (the booleanity count).
    unfold cookLevinFactorList cook_levin_compilation
    simp only [List.length_map, List.length_append]
    have hbool : (boolConstraintList n).length = n := boolConstraintList_length n
    omega
  have h1lt : (1 : ℕ) < (cookLevinFactorList M n hn htb hns).length := by omega
  let i₁ : Fin (cookLevinFactorList M n hn htb hns).length := ⟨1, h1lt⟩
  -- The constraint type at i₁ is booleanity (since i₁.val = 1 < n).
  have hType : cookLevinConstraintType M n hn htb hns i₁ = ConstraintType.booleanity :=
    cookLevinConstraintType_eq_booleanity M n hn htb hns i₁ (by show (1 : ℕ) < n; omega)
  -- Extract the canonical-shape claim at i₁.
  have hi := hShape i₁
  rw [hType] at hi
  -- The match resolves to the booleanity branch.
  -- After rw, `hi` says `(cookLevinFactorList _).get i₁ = 1 - X(castLEEmb 0) + X(castLEEmb 0)^2`.
  -- Compute the actual factor at i₁.
  have hFactor :
      (cookLevinFactorList M n hn htb hns).get i₁ =
        (1 - MvPolynomial.X (⟨1, by omega⟩ : Fin n)
            + (MvPolynomial.X (⟨1, by omega⟩ : Fin n)) ^ 2
          : MvPolynomial (Fin n) ℚ) :=
    cookLevinFactorList_get_booleanity_explicit M n hn htb hns i₁ (by show (1 : ℕ) < n; omega)
  -- Substitute to get the polynomial equality that must hold.
  rw [hFactor] at hi
  -- Note: `Fin.castLEEmb hn4 (0 : Fin 4)` evaluates to `⟨0, _⟩ : Fin n`.
  have hcast0 :
      ((Fin.castLEEmb hn4) (0 : Fin 4) : Fin n) = ⟨0, by omega⟩ := by
    rfl
  rw [hcast0] at hi
  -- Now `hi : 1 - X(⟨1, _⟩) + X(⟨1, _⟩)^2 = 1 - X(⟨0, _⟩) + X(⟨0, _⟩)^2`.
  -- This contradicts `booleanityFactor_at_zero_ne_at_one`.
  exact booleanityFactor_at_zero_ne_at_one n hn hi.symm

/-! ### Axiom audit -/

#print axioms booleanityFactor_at_zero_ne_at_one
#print axioms cookLevinFactorList_get_booleanity_explicit
#print axioms cookLevinCanonicalConcreteWShapeWitnesses_infeasible

end PallLean.Paper93.DeepMath.PathB
