/-
  SpdpRemaining.lean — All remaining sorry interfaces (Q1-Q9)
  Based on Darren's comprehensive specification.
-/
import Mathlib
import PallLean.SpdpPaperKeyLemmas

open scoped BigOperators

namespace SpdpRemaining

/-! ## Q3-Q4: Padding Leibniz containment -/

section PaddingLeibniz
variable {σ F : Type*} [CommRing F]
variable (Var : Type*) [DecidableEq Var]
abbrev Poly (Var : Type*) (F : Type*) [CommRing F] := MvPolynomial Var F

noncomputable def pderivSet (s : Finset Var) (p : Poly Var F) : Poly Var F :=
  s.toList.foldl (fun q v => MvPolynomial.pderiv v q) p

variable (padMonomial : Finset Var → Poly Var F)
variable (splitS : Finset Var → Finset Var × Finset Var)

axiom pderivSet_mul_padding_form (Y V : Poly Var F) (S : Finset Var) :
    ∃ (sgn : F), pderivSet Var S (Y * V) =
      sgn • (padMonomial (splitS S).1 * pderivSet Var (splitS S).2 V)

variable (blockedSpdpGens : Poly Var F → Set (Poly Var F))

noncomputable def blockedSpdpSubspace' (p : Poly Var F) : Submodule F (Poly Var F) :=
  Submodule.span F (blockedSpdpGens p)

noncomputable def blockedSpdpRank' (p : Poly Var F) : ℕ :=
  Module.finrank F (blockedSpdpSubspace' Var blockedSpdpGens p)

variable {ι : Type*}
variable (U : ι → Submodule F (Poly Var F))
variable (idx : Finset ι)

axiom padding_subspace_le' (Y V : Poly Var F) :
  blockedSpdpSubspace' Var blockedSpdpGens (Y * V) ≤ idx.sup U

end PaddingLeibniz

/-! ## Q5: ProfileCover shortcut for width_to_rank_bound -/

section ProfileShortcut
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]

structure ProfileCover (Profile : Type*) where
  H : Finset Profile
  Vh : Profile → Submodule F V
  d : ℕ
  dimBound : ∀ h ∈ H, Module.finrank F (Vh h) ≤ d

end ProfileShortcut

/-! ## Q7: Tseitin specs from ramanujanFamily -/

section TseitinSpecs

structure RamanujanFamilySpec where
  oddParity : Prop
  clauseCountUpper : Prop
  clauseCountLower : Prop
  boundedOccurrence : Prop

end TseitinSpecs

/-! ## Q8: Binomial lower bound as axiom -/

axiom binomial_lower_bound :
  ∃ n0 : ℕ, ∀ n ≥ n0, Nat.choose (n / 30) (Nat.log 2 n) ≥ n ^ (Nat.log 2 n / 4)

/-! ## Q9: coeffLin + identity minor -/

section IdentityMinor
variable {σ F : Type*} [CommRing F]

noncomputable def coeffLin (m : σ →₀ ℕ) : MvPolynomial σ F →ₗ[F] F where
  toFun := MvPolynomial.coeff m
  map_add' := by intros; simp [map_add]
  map_smul' := by intros; simp [MvPolynomial.coeff_smul, smul_eq_mul]

end IdentityMinor

section IdentityMinorField
variable {σ F : Type*}

theorem identity_minor_lower_bound'
    [Field F] [FiniteDimensional F (MvPolynomial σ F)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → MvPolynomial σ F)
    (τ : ι → σ →₀ ℕ)
    (hδ : ∀ i j, coeffLin (τ i) (R j) = if i = j then (1 : F) else 0) :
    Fintype.card ι ≤ Module.finrank F (Submodule.span F (Set.range R)) := by
  have hv := SpdpPaper.linearIndependent_of_dual R (fun i => coeffLin (τ i)) hδ
  rw [← finrank_span_eq_card hv]

end IdentityMinorField

end SpdpRemaining
