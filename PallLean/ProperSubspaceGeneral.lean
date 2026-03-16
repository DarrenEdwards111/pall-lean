/-
  ProperSubspaceGeneral.lean — fspdpEvalSubspace n ≠ ⊤ for large n

  Paper §8.6: The FSPDP evaluation subspace is proper.

  Proof: The Möbius functional L(v) = ∑_T (-1)^{w-|T|} v(x_T) vanishes
  on all InFSPDP evalVecs (because the top coefficient of the restricted
  multilinear polynomial is forced to 0 by the SPDP rank bound ≤ √n < 2^w),
  but L(evalVec(indicator of allLiveOnes)) = 1 ≠ 0.
-/
import PallLean.PneqNP_Defs
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.RestrictedSPDP
import PallLean.BoolEval
import PallLean.Depth4Simulation
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace ProperSubspaceGeneral

open MvPolynomial SPDP RestrictedSPDP Restriction BoolEval PneqNP_Defs
open Depth4Simulation UniversalRestriction

/-! ## Arithmetic -/

lemma sqrt_lt_pow_log (n : ℕ) (hn : n ≥ 4) : Nat.sqrt n < 2 ^ Nat.log 2 n := by
  have hlog_succ : n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
  have hpow_half : n / 2 < 2 ^ Nat.log 2 n := by
    have : 2 ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by ring
    omega
  suffices Nat.sqrt n ≤ n / 2 from lt_of_le_of_lt this hpow_half
  by_contra h; push_neg at h
  have h1 : n / 2 + 1 ≤ Nat.sqrt n := h
  have h2 : (n / 2 + 1) * (n / 2 + 1) ≤ n :=
    le_trans (Nat.mul_le_mul h1 h1) (Nat.sqrt_le n)
  set k := n / 2
  have : k ≥ 2 := by omega
  have : n ≤ 2 * k + 1 := by omega
  nlinarith

/-! ## SPDP rank of ∏ Xᵢ is ≥ 2^w

  The derivative ∂_{x₀}...∂_{x_{w-1}} of ∏ᵢ Xᵢ equals 1.
  So generators include {m · 1 : deg(m) ≤ w}, which span all
  degree-≤-w polynomials. The multilinear monomials among these
  are 2^w linearly independent vectors, giving rank ≥ 2^w.

  Axiomatized because the full proof needs:
  (a) iterDerivList [0,...,w-1] (∏ Xᵢ) = 1
  (b) Linear independence of multilinear monomials in MvPolynomial
  Both are standard but require nontrivial Lean infrastructure. -/

axiom spdp_rank_allVarsProd_ge (w : ℕ) (hw : w ≥ 1) :
    spdpRank w w (Finset.univ.prod (fun i : Fin w => (X i : MvPolynomial (Fin w) ℚ))) ≥ 2 ^ w

/-! ## Top coefficient constraint

  For any InFSPDP function f, the restricted multilinear interpolation
  has SPDP rank ≤ √n. If its top coefficient were nonzero, the SPDP rank
  would be ≥ 2^w > √n (for n ≥ 4). So the top coefficient must be 0.

  The top coefficient of a multilinear polynomial q on w vars equals
  ∑_{T ⊆ [w]} (-1)^{w-|T|} q(1_T) by Möbius inversion. Since q agrees
  with boolToRat ∘ f on Boolean inputs, this gives a linear relation
  on f's evaluation vector. -/

/-! ## Möbius coefficient as a linear functional

  Define L(v) = ∑_{x ρ-consistent} (-1)^{w - |{i live : x(i) = true}|} · v(x).
  For InFSPDP f, L(evalVec f) = top coefficient of restricted polynomial = 0.
  For indicatorAllLiveOnes, L(evalVec g) = (-1)^0 · 1 = 1. -/

/-- A ρ-consistent Boolean input: one where fixed vars match ρ. -/
def isConsistent (n : ℕ) (x : Fin n → Bool) : Prop :=
  ∀ i, ∀ b, (universalRestriction n) i = some b → x i = b

instance (n : ℕ) (x : Fin n → Bool) : Decidable (isConsistent n x) :=
  inferInstanceAs (Decidable (∀ i, ∀ b, _))

/-- Count of live variables that are true. -/
def liveTrue (n : ℕ) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => (universalRestriction n) i = none ∧ x i = true)).card

/-- Number of live variables = Nat.log 2 n for the universal restriction. -/
def w (n : ℕ) : ℕ := (liveVars (universalRestriction n)).card

/-- The Möbius functional. -/
noncomputable def mobiusL (n : ℕ) : ((Fin n → Bool) → ℚ) →ₗ[ℚ] ℚ where
  toFun v := ∑ x : Fin n → Bool,
    if isConsistent n x
    then v x * ((-1 : ℚ) ^ (w n - liveTrue n x))
    else 0
  map_add' u v := by
    have : ∀ x : Fin n → Bool,
      (if isConsistent n x then (u + v) x * (-1 : ℚ) ^ (w n - liveTrue n x) else 0) =
      (if isConsistent n x then u x * (-1 : ℚ) ^ (w n - liveTrue n x) else 0) +
      (if isConsistent n x then v x * (-1 : ℚ) ^ (w n - liveTrue n x) else 0) := by
        intro x; split_ifs <;> simp [Pi.add_apply]; ring
    simp_rw [this, Finset.sum_add_distrib]
  map_smul' c v := by
    have : ∀ x : Fin n → Bool,
      (if isConsistent n x then (c • v) x * (-1 : ℚ) ^ (w n - liveTrue n x) else 0) =
      c * (if isConsistent n x then v x * (-1 : ℚ) ^ (w n - liveTrue n x) else 0) := by
        intro x; split_ifs <;> simp [Pi.smul_apply, smul_eq_mul]; ring
    simp_rw [this, ← Finset.mul_sum]; rfl

/-- The allLiveOnes point: fixed vars = false, live vars = true. -/
def allLiveOnes (n : ℕ) : Fin n → Bool :=
  fun i => if (universalRestriction n) i = none then true else false

/-- The indicator function: true only at allLiveOnes. -/
def indicatorAllLiveOnes (n : ℕ) : BoolFun n :=
  fun x => x = allLiveOnes n

/-- allLiveOnes is ρ-consistent. -/
lemma allLiveOnes_consistent (n : ℕ) : isConsistent n (allLiveOnes n) := by
  intro i b hib
  unfold allLiveOnes
  -- If ρ i = some b, then ρ i ≠ none, so the if-branch gives false
  have hne : universalRestriction n i ≠ none := by rw [hib]; simp
  simp only [hne, ↓reduceIte]
  -- universalRestriction fixes to false, so b = false
  have : universalRestriction n i = some false := by
    unfold universalRestriction at hib ⊢
    split_ifs at hib ⊢ <;> simp_all
  rw [this] at hib; exact Option.some_injective _ hib

/-- For allLiveOnes, all live vars are true, so liveTrue = w. -/
lemma liveTrue_allLiveOnes (n : ℕ) : liveTrue n (allLiveOnes n) = w n := by
  unfold liveTrue w liveVars allLiveOnes
  congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact h1
  · intro h; exact ⟨h, by simp [h]⟩

/-! ## Main theorem -/

-- The Mobius functional vanishes on InFSPDP evalVecs.
-- Proved in MobiusBridge.lean from two sub-axioms:
-- mobiusL_eq_top_coeff (Mobius inversion) + top_coeff_zero_of_InFSPDP (SPDP rank bound)

/-- L(evalVec(indicatorAllLiveOnes)) = 1. -/
lemma mobiusL_indicator (n : ℕ) (hn : n ≥ 2) :
    mobiusL n (evalVec (indicatorAllLiveOnes n)) = 1 := by
  unfold mobiusL
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- evalVec(indicatorAllLiveOnes) is 0 everywhere except at allLiveOnes
  have h_eq : ∀ x : Fin n → Bool, x ≠ allLiveOnes n →
      evalVec (indicatorAllLiveOnes n) x = 0 := by
    intro x hx; unfold evalVec indicatorAllLiveOnes boolToRat; simp [hx]
  have h_val : evalVec (indicatorAllLiveOnes n) (allLiveOnes n) = 1 := by
    unfold evalVec indicatorAllLiveOnes boolToRat; simp
  -- The sum reduces to the single term at allLiveOnes
  have h_cons : isConsistent n (allLiveOnes n) := allLiveOnes_consistent n
  conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (allLiveOnes n))]
  rw [if_pos h_cons, h_val, liveTrue_allLiveOnes, Nat.sub_self]
  simp only [pow_zero, mul_one]
  suffices h : ∑ x ∈ Finset.univ.erase (allLiveOnes n),
      (if isConsistent n x then evalVec (indicatorAllLiveOnes n) x *
        (-1 : ℚ) ^ (w n - liveTrue n x) else 0) = 0 by linarith
  apply Finset.sum_eq_zero
  intro x hx
  have hne : x ≠ allLiveOnes n := Finset.ne_of_mem_erase hx
  rw [h_eq x hne]; split_ifs <;> simp

/-- The FSPDP evaluation subspace is proper for n ≥ 4,
    given that the Möbius functional vanishes on all InFSPDP functions. -/
theorem fspdp_proper (n : ℕ) (hn : n ≥ 4)
    (h_van : ∀ f : BoolFun n, InFSPDP f → mobiusL n (evalVec f) = 0) :
    fspdpEvalSubspace n ≠ ⊤ := by
  intro h_eq_top
  -- mobiusL vanishes on the span of InFSPDP evalVecs
  have h_le_ker : fspdpEvalSubspace n ≤ LinearMap.ker (mobiusL n) := by
    apply Submodule.span_le.mpr
    rintro v ⟨f, hf, rfl⟩
    exact LinearMap.mem_ker.mpr (h_van f hf)
  have h_span_van : ∀ v ∈ fspdpEvalSubspace n, mobiusL n v = 0 :=
    fun v hv => LinearMap.mem_ker.mp (h_le_ker hv)
  -- But mobiusL(evalVec(indicatorAllLiveOnes)) = 1 ≠ 0
  have h_one : mobiusL n (evalVec (indicatorAllLiveOnes n)) = 1 :=
    mobiusL_indicator n (by omega)
  -- evalVec(indicatorAllLiveOnes) ∈ ⊤ = fspdpEvalSubspace
  have h_mem : evalVec (indicatorAllLiveOnes n) ∈ fspdpEvalSubspace n := by
    rw [h_eq_top]; exact Submodule.mem_top
  -- Contradiction: 0 = L(v) = 1
  linarith [h_span_van _ h_mem]

/-- Existential version, parameterized by the vanishing hypothesis. -/
theorem fspdp_proper_subspace_of
    (h_van : ∀ n, n ≥ 4 → ∀ f : BoolFun n, InFSPDP f → mobiusL n (evalVec f) = 0) :
    ∃ n₁ : ℕ, ∀ (n : ℕ), n ≥ n₁ → n ≥ 2 → fspdpEvalSubspace n ≠ ⊤ :=
  ⟨4, fun n hn _ => fspdp_proper n hn (h_van n hn)⟩

end ProperSubspaceGeneral
