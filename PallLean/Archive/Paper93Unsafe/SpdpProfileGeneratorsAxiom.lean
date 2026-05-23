/-
  Archive/Paper93Unsafe/SpdpProfileGeneratorsAxiom.lean

  UNSAFE — NOT part of the consistent default build target.

  This module holds the false `spdp_profile_generators` axiom and the
  declarations that depend on it directly (`product_leibniz_profile_cover`,
  `leibniz_symmetric_power_descent_bound`). The axiom asserts the SPDP
  subspace of the compiled polynomial is covered by polynomially-many,
  polynomially-bounded profile generators — i.e. SPDP rank ≤ (log n + 1)^12.

  This is PROVABLY FALSE: it contradicts the NP-side identity-minor lower
  bound on the same compiled object (see the obstruction theorems
  `godMove_transport_upper_bound_impossible_at_paperScale` and
  `theorem207_strict_target_incompatibility`). Retained for the record only.

  Anything that transitively uses these declarations is unsound and must
  live in this Unsafe archive, never in the default `PallLean` target.
-/
import PallLean.SymmetricPower

namespace SymmetricPower

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation
open LeibnizProduct

/-- **FALSE AXIOM (archived).** Profile-generator cover of the compiled SPDP
subspace. Refuted by the NP-side identity minor. -/
axiom spdp_profile_generators_ARCHIVED_DELETED
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∃ (numP bound : ℕ)
      (generators : Fin numP → Fin bound →
        MvPolynomial (Fin (cook_levin_compilation M n hn htb hns).numVars) ℚ),
      numP ≤ (Nat.log 2 n + 1) ^ 4 ∧
      bound ≤ (Nat.log 2 n + 1) ^ 8 ∧
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤
      Submodule.span ℚ (Set.range (fun (ij : Fin numP × Fin bound) =>
        generators ij.1 ij.2))

/-- Product Leibniz profile cover (archived; uses the false axiom). -/
theorem product_leibniz_profile_cover
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∃ (numP : ℕ) (spaces : Fin numP → Submodule ℚ
        (MvPolynomial (Fin (cook_levin_compilation M n hn htb hns).numVars) ℚ)),
      numP ≤ (Nat.log 2 n + 1) ^ 4 ∧
      (∀ i, Module.Finite ℚ (spaces i)) ∧
      (∀ i, Module.finrank ℚ (spaces i) ≤ (Nat.log 2 n + 1) ^ 8) ∧
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤ ⨆ i, spaces i := by
  obtain ⟨numP, bound, generators, hnumP, hbound, hcover⟩ :=
    spdp_profile_generators_ARCHIVED_DELETED M n hn htb hns
  let spaces : Fin numP → Submodule ℚ
      (MvPolynomial (Fin (cook_levin_compilation M n hn htb hns).numVars) ℚ) :=
    fun i => Submodule.span ℚ (Set.range (fun j : Fin bound => generators i j))
  refine ⟨numP, spaces, hnumP, ?_, ?_, ?_⟩
  · intro i
    apply Module.Finite.span_of_finite
    exact Set.finite_range _
  · intro i
    calc Module.finrank ℚ ↥(spaces i)
        = Module.finrank ℚ ↥(Submodule.span ℚ (Set.range (fun j : Fin bound => generators i j))) := rfl
      _ ≤ (Set.range (fun j : Fin bound => generators i j)).toFinset.card :=
          finrank_span_le_card _
      _ ≤ Fintype.card (Fin bound) := by
          rw [Set.toFinset_range]
          exact Finset.card_image_le
      _ = bound := Fintype.card_fin bound
      _ ≤ (Nat.log 2 n + 1) ^ 8 := hbound
  · calc mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (compiledPoly (cook_levin_compilation M n hn htb hns))
        ≤ Submodule.span ℚ (Set.range (fun ij : Fin numP × Fin bound =>
            generators ij.1 ij.2)) := hcover
      _ = Submodule.span ℚ (⋃ i : Fin numP,
            Set.range (fun j : Fin bound => generators i j)) := by
          congr 1
          ext x
          simp only [Set.mem_range, Set.mem_iUnion, Prod.exists]
      _ = ⨆ i : Fin numP, Submodule.span ℚ
            (Set.range (fun j : Fin bound => generators i j)) :=
          Submodule.span_iUnion _
      _ = ⨆ i, spaces i := rfl

private theorem finrank_iSup_le (m : ℕ)
    {n : ℕ}
    (U : Fin m → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    [∀ i, Module.Finite ℚ ↥(U i)] :
    Module.finrank ℚ ↥(⨆ i : Fin m, U i) ≤ ∑ i : Fin m, Module.finrank ℚ ↥(U i) :=
  finrank_iSup_fin_le m U

/-- SPDP rank ≤ (κ+1)^12 (archived; FALSE — uses the false axiom). -/
theorem leibniz_symmetric_power_descent_bound
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Module.finrank ℚ ↥(mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)))
    ≤ combinedProfileBound (Nat.log 2 n) := by
  obtain ⟨numP, spaces, hnumP, hfin, hbound, hcover⟩ :=
    product_leibniz_profile_cover M n hn htb hns
  set κ := Nat.log 2 n
  have hcomb : combinedProfileBound κ = (κ + 1) ^ 12 :=
    combinedProfileBound_eq κ
  rw [hcomb]
  have h1 : Module.finrank ℚ ↥(mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn htb hns).partition κ κ
      (compiledPoly (cook_levin_compilation M n hn htb hns))) ≤
    Module.finrank ℚ ↥(⨆ i : Fin numP, spaces i) :=
    Submodule.finrank_mono hcover
  have h2 : Module.finrank ℚ ↥(⨆ i : Fin numP, spaces i) ≤
    ∑ i : Fin numP, Module.finrank ℚ (spaces i) := by
    haveI : ∀ i, Module.Finite ℚ (spaces i) := hfin
    exact finrank_iSup_fin_le numP spaces
  have h3 : ∑ i : Fin numP, Module.finrank ℚ (spaces i) ≤ numP * (κ + 1) ^ 8 := by
    calc ∑ i : Fin numP, Module.finrank ℚ (spaces i)
        ≤ ∑ _i : Fin numP, (κ + 1) ^ 8 :=
          Finset.sum_le_sum (fun i _ => hbound i)
      _ = numP * (κ + 1) ^ 8 := by simp [Finset.sum_const, Finset.card_fin]
  have h4 : numP * (κ + 1) ^ 8 ≤ (κ + 1) ^ 12 := by
    calc numP * (κ + 1) ^ 8
        ≤ (κ + 1) ^ 4 * (κ + 1) ^ 8 :=
          Nat.mul_le_mul_right _ hnumP
      _ = (κ + 1) ^ 12 := by ring
  linarith

end SymmetricPower
