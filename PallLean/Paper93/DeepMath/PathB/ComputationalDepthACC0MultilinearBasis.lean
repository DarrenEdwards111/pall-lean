import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NonNativeDegree

/-!
# The multilinear monomial basis over `F` — discharging `LowDegreeDimensionIdentity`

Entry 264 reduced the open `PatternRichCrossFieldLowerBound` to two sockets: the analytic `PolynomialMethodApproximation`
(the genuine open Razborov–Smolensky core) and the *secondary* `LowDegreeDimensionIdentity` (`finrank W = lowDegreeDim
n D` for the non-native degree-`≤ D` function space).  This file **discharges the secondary socket** by building the
multilinear monomial basis over a general field `F` — the `F`-analogue of the in-arc `anf_involutive` (which did this
over `F₂`).

**The basis.**  For `S : Finset (Fin n)`, the multilinear monomial `χ_S(x) := ∏_{i∈S} (xᵢ : F)` (over the Boolean cube
`x : Fin n → Bool`, with `true ↦ 1`, `false ↦ 0`).  The key fact is the **triangular evaluation**: at the point
`e_T(i) := [i ∈ T]`, `χ_S(e_T) = [S ⊆ T]` — the subset (zeta) matrix, which is unitriangular, hence the `χ_S` are
linearly independent.  This is proved by Möbius/strong induction (`∑_{S ⊆ T} c_S = 0 ∀T ⇒ c_T = 0`).

## What is proved (clean axioms, no `sorry`)

* **`mlMon S x := ∏_{i∈S} (if xᵢ then 1 else 0)`** — the multilinear monomial of degree `|S|`.
* **`mlMon_eval`** (PROVED) — `χ_S(e_T) = [S ⊆ T]`: the triangular evaluation.
* **`mlMon_linearIndependent`** (PROVED) — the `2ⁿ` multilinear monomials are linearly independent over `F` (Möbius
  inversion on the subset lattice).  *A genuine general-field generalisation of `anf_involutive`.*
* **`card_subtype_card_le`** (PROVED) — `#{S : S.card ≤ D} = lowDegreeDim n D = ∑_{i≤D} C(n,i)` (partition the
  subsets by cardinality; `Finset.card_powersetCard`).
* **`lowDegreeSubmodule_finrank`** (PROVED) — the degree-`≤ D` submodule `span {χ_S : |S| ≤ D}` has dimension exactly
  `lowDegreeDim n D` (`finrank_span_eq_card` on the independent sub-family).
* **`lowDegreeDimensionIdentity_discharged`** (PROVED) — therefore `LowDegreeDimensionIdentity (lowDegreeSubmodule n D)
  n D` holds: **the secondary socket of entry 264 is discharged**.
* **`patternRichCrossFieldLowerBound_no_dimSocket`** (PROVED) — consequently, for Boolean gate families the reduction of
  entry 264 holds with the dimension socket *eliminated*: `PatternRichCrossFieldLowerBound` follows from the **single**
  remaining socket `PolynomialMethodApproximation`.

## Honest scope

This builds the multilinear basis over an arbitrary field and computes the degree-`≤ D` dimension exactly, discharging
the secondary `LowDegreeDimensionIdentity` socket completely.  After this, the open target
`PatternRichCrossFieldLowerBound` rests on the **single** socket `PolynomialMethodApproximation` — the probabilistic
polynomial method (the genuine open Razborov–Smolensky core, entry-238 `CarryRefinementCrossing`).  This does **not**
prove that socket, and is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis

open PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree (lowDegreeDim LowDegreeDimensionIdentity)

variable {F : Type} [Field F]

/-- **The multilinear monomial** `χ_S(x) = ∏_{i∈S} xᵢ` over the Boolean cube (`true ↦ 1`, `false ↦ 0`), of degree
`|S|`. -/
def mlMon {n : ℕ} (S : Finset (Fin n)) : (Fin n → Bool) → F :=
  fun x => ∏ i ∈ S, (if x i then (1 : F) else 0)

/-- **The evaluation point** `e_T(i) = [i ∈ T]`. -/
def pt {n : ℕ} (T : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ T)

/-- **The triangular evaluation (PROVED).**  `χ_S(e_T) = [S ⊆ T]`: if `S ⊆ T` every factor is `1` (product `1`); else
some `i ∈ S` has `i ∉ T`, a factor is `0`.  This is the unitriangular subset (zeta) matrix. -/
theorem mlMon_eval {n : ℕ} (S T : Finset (Fin n)) :
    mlMon (F := F) S (pt T) = if S ⊆ T then 1 else 0 := by
  simp only [mlMon, pt]
  by_cases h : S ⊆ T
  · simp only [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h hi]
  · simp only [if_neg h]
    obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp h
    refine Finset.prod_eq_zero hiS ?_
    simp [hiT]

/-- **The multilinear monomials are linearly independent over `F` (PROVED).**  A general-field generalisation of the
in-arc `anf_involutive` (`F₂`).  Proof: a dependence `∑_S c_S χ_S = 0`, evaluated at `e_T`, gives `∑_{S ⊆ T} c_S = 0`
for all `T` (triangular evaluation); Möbius/strong induction on the subset lattice then forces every `c_T = 0`. -/
theorem mlMon_linearIndependent {n : ℕ} :
    LinearIndependent F (fun S : Finset (Fin n) => mlMon (F := F) S) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : ∀ T : Finset (Fin n), ∑ S ∈ T.powerset, g S = 0 := by
    intro T
    have hgT := congrFun hg (pt T)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mlMon_eval, mul_ite, mul_one,
      mul_zero, Pi.zero_apply] at hgT
    have key : ∑ S ∈ T.powerset, g S = ∑ S, (if S ⊆ T then g S else 0) := by
      have h1 : ∑ S ∈ T.powerset, g S = ∑ S ∈ T.powerset, (if S ⊆ T then g S else 0) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.mem_powerset] at hS
        rw [if_pos hS]
      rw [h1]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      rw [Finset.mem_powerset] at hS
      rw [if_neg hS]
    rw [key]; exact hgT
  intro T0
  refine Finset.strongInductionOn T0 ?_
  intro T IH
  have hsT := hsum T
  rw [← Finset.add_sum_erase _ g (Finset.mem_powerset.mpr (Finset.Subset.refl T))] at hsT
  have herase : (∑ S ∈ (T.powerset).erase T, g S) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_erase, Finset.mem_powerset] at hS
    exact IH S (Finset.ssubset_iff_subset_ne.mpr ⟨hS.2, hS.1⟩)
  rw [herase, add_zero] at hsT
  exact hsT

/-- **The number of subsets of size `≤ D` is `lowDegreeDim n D` (PROVED).**  Partition the subsets by cardinality:
`{S : S.card ≤ D} = ⋃_{i≤D} {S : S.card = i}`, and `#{S : S.card = i} = C(n,i)` (`Finset.card_powersetCard`). -/
theorem card_subtype_card_le {n D : ℕ} :
    Fintype.card {S : Finset (Fin n) // S.card ≤ D} = lowDegreeDim n D := by
  rw [Fintype.card_subtype]
  have hpart : Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ D)
      = (Finset.range (D + 1)).biUnion (fun i => (Finset.univ : Finset (Fin n)).powersetCard i) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · intro h; exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨i, hi, hSi⟩; omega
  rw [hpart, Finset.card_biUnion]
  · simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rfl
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro S hSi hSj
    rw [Finset.mem_powersetCard] at hSi hSj
    exact hij (hSi.2.symm.trans hSj.2)

/-- **The non-native degree-`≤ D` submodule** `span {χ_S : |S| ≤ D}` of the function space on the `n`-bit cube. -/
def lowDegreeSubmodule (n D : ℕ) : Submodule F ((Fin n → Bool) → F) :=
  Submodule.span F (Set.range
    ((fun S : Finset (Fin n) => mlMon (F := F) S) ∘ (Subtype.val : {S : Finset (Fin n) // S.card ≤ D} → _)))

/-- **The degree-`≤ D` submodule has dimension `lowDegreeDim n D` (PROVED).**  Its spanning family — the multilinear
monomials of degree `≤ D` — is linearly independent (sub-family of `mlMon_linearIndependent`), so
`finrank = #{S : S.card ≤ D} = lowDegreeDim n D` (`finrank_span_eq_card` + `card_subtype_card_le`). -/
theorem lowDegreeSubmodule_finrank {n D : ℕ} :
    Module.finrank F (lowDegreeSubmodule (F := F) n D) = lowDegreeDim n D := by
  rw [lowDegreeSubmodule,
    finrank_span_eq_card (mlMon_linearIndependent.comp Subtype.val Subtype.val_injective)]
  exact card_subtype_card_le

/-- **The secondary socket of entry 264 is DISCHARGED (PROVED).**  `LowDegreeDimensionIdentity (lowDegreeSubmodule n D)
n D` holds — the non-native degree-`≤ D` function space has dimension `lowDegreeDim n D`, no longer assumed. -/
theorem lowDegreeDimensionIdentity_discharged {n D : ℕ} :
    LowDegreeDimensionIdentity (lowDegreeSubmodule (F := F) n D) n D :=
  lowDegreeSubmodule_finrank

/-- **`PatternRichCrossFieldLowerBound` with the dimension socket eliminated (PROVED).**  For a Boolean gate family
(`X = Fin n → Bool`), instantiating entry-264's reduction at `W := lowDegreeSubmodule n D` discharges the
`LowDegreeDimensionIdentity` hypothesis via `lowDegreeSubmodule_finrank`.  The open target therefore rests on the
**single** remaining socket `PolynomialMethodApproximation` (the probabilistic polynomial method, the genuine open
Razborov–Smolensky core). -/
theorem patternRichCrossFieldLowerBound_no_dimSocket {n s : ℕ}
    (gates : Fin s → ((Fin n → Bool) → Bool)) (D : ℕ) (hlt : lowDegreeDim n D < s)
    (ComputesCount : Prop)
    (hPoly : ACC0NonNativeDegree.PolynomialMethodApproximation gates
      (lowDegreeSubmodule (F := F) n D) ComputesCount) :
    ACC0VaryingAffinePatterns.PatternRichCrossFieldLowerBound gates (¬ ComputesCount) F :=
  ACC0NonNativeDegree.patternRichCrossFieldLowerBound_via_nonNativeDegree
    gates (lowDegreeSubmodule (F := F) n D) n D lowDegreeSubmodule_finrank hlt ComputesCount hPoly

/-!
**The wall after this entry.**  The Smolensky counting engine (entry 264) and now the multilinear-basis dimension
identity are both *proved*: `lowDegreeSubmodule_finrank` discharges `LowDegreeDimensionIdentity` completely.  The open
target `PatternRichCrossFieldLowerBound` rests on the **single** remaining socket `PolynomialMethodApproximation` — the
probabilistic polynomial method (`AC⁰[p] ⇒` low-degree approximation), the genuine open Razborov–Smolensky core
(entry-238 `CarryRefinementCrossing`), whose concrete instances are the in-arc `Layer3`/`Layer4` lower bounds.  Not
faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis.mlMon_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis.mlMon_linearIndependent
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis.card_subtype_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis.lowDegreeSubmodule_finrank
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis.lowDegreeDimensionIdentity_discharged
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis.patternRichCrossFieldLowerBound_no_dimSocket
