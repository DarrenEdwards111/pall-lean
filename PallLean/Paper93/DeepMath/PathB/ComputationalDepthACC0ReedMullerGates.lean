import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0VaryingAffinePatterns

/-!
# Reed–Muller / low-degree polynomial gates — a THIRD proved `AlgExpander` + `PatternRich` family

The third hard-family candidate the program asked for, and the one closest to Razborov–Smolensky: **low-degree
polynomial gates**.  Gate `i` is a degree-`≤ d` polynomial `Pᵢ` over `ZMod p`; it fires on `x` iff `Pᵢ(x) = bᵢ`.  The
Reed–Muller code `RM(d, n)` is exactly the span of such polynomials, so these are the Reed–Muller gates.

**The key reduction (the real content).**  Write `Pᵢ = ∑_m coeffᵢ,m · m` in the monomial basis, and let
`φ(x)_m := m(x)` be the **monomial feature map** (`feat`), with `m` ranging over the degree-`≤ d` monomials `M`.  Then

> `Pᵢ(x) = ⟨coeffᵢ, φ(x)⟩`,

so **a low-degree polynomial gate is an affine gate in the monomial feature space** (`rmGate = varGate ∘ φ`).  Hence
the entire entry-262 varying-affine analysis lifts: under the **feature-general-position** hypothesis that the
polynomial-evaluation map `rmEval feat coeff : x ↦ (Pᵢ(x))ᵢ` is *surjective* (every value-vector is attained — for
Reed–Muller this is non-degeneracy / large distance of the code), the family is `AlgExpander` + `PatternRich` +
`CoFiringRich`.  The varying-affine family of entry 262 is the **degree-1** special case (`feat m x = x_m`).

## What is proved (clean axioms, no `sorry`)

* **`rmGate_degree_one_eq_varGate`** (PROVED) — the degree-1 Reed–Muller family (`feat m x = x_m`) *is* the entry-262
  varying-affine family: `rmGate (fun m x => x m) a b = varGate a b`.  The reduction is exact.
* **`rmGate_patternImage_eq_univ`** (PROVED) — under feature general position every subset is realized as a
  fire-pattern (solve `rmEval feat coeff x = (i ↦ if i∈T then bᵢ else bᵢ+1)`).
* **`rmGate_patternRich`** (PROVED) — hence `PatternRich (rmGate feat coeff b) (2^s)`.
* **`rmGate_coFiringRich`** (PROVED) — solving `rmEval feat coeff x = b` makes all `s` gates fire on one input:
  `CoFiringRich (rmGate feat coeff b) s`.
* **`rmGate_algExpander`** (PROVED) — feature general position gives a private witness per gate, so the indicators are
  linearly independent over any field `F`: `AlgExpander`.

## The lower-bound target + the RS attack invariant (reused named sockets)

The target socket `PatternRichCrossFieldLowerBound` and the Razborov–Smolensky attack invariant
`NonNativeDegreeLowerBound` from entry 262 apply verbatim to `rmGate`.

* **`rmGate_ACC0_chain`** (PROVED) — *given* the lower-bound socket and the entry-261 bridge
  `crossFieldHard_to_ACC0Component`, the Reed–Muller family yields the `ACC⁰[composite]` component **with `AlgExpander`
  and `PatternRich` discharged here**.

## Honest scope

A third proved family (low-degree / Reed–Muller polynomial gates), reduced cleanly to affine gates in monomial feature
space, satisfying `AlgExpander` + `PatternRich` + `CoFiringRich` under feature general position, with the degree-1 case
shown to coincide with entry 262.  The chain to `ACC⁰[composite]` is assembled with all family-specific hypotheses
discharged; the only remaining open inputs are the named `PatternRichCrossFieldLowerBound`/`NonNativeDegreeLowerBound`
socket (Smolensky-strength, entry-238 `CarryRefinementCrossing`) and the named `crossFieldHard_to_ACC0Component` bridge.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0ReedMullerGates

open PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion (AlgExpander)
open PallLean.Paper93.DeepMath.PathB.ACC0CoFiring (firePattern CoFiringRich)
open PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplanes (private_witness_indep)
open PallLean.Paper93.DeepMath.PathB.ACC0FirePatternRichness (PatternRich crossFieldHard_to_ACC0Component)
open PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns
  (dotEval varGate PatternRichCrossFieldLowerBound)

/-- **The polynomial-evaluation map.**  `rmEval feat coeff x i = ∑_m coeffᵢ,m · feat m x = Pᵢ(x)`: the value of the
degree-`≤ d` polynomial gate `i` at `x`, expressed in the monomial feature basis `feat`. -/
def rmEval {p : ℕ} {X M : Type} [Fintype M] {s : ℕ}
    (feat : M → X → ZMod p) (coeff : Fin s → M → ZMod p) (x : X) : Fin s → ZMod p :=
  fun i => ∑ m, coeff i m * feat m x

/-- **The Reed–Muller / low-degree polynomial gate family.**  Gate `i` fires on `x` iff `Pᵢ(x) = bᵢ`, i.e.
`⟨coeffᵢ, φ(x)⟩ = bᵢ` — an affine gate in the monomial feature space `φ = feat`. -/
def rmGate {p : ℕ} {X M : Type} [Fintype M] {s : ℕ}
    (feat : M → X → ZMod p) (coeff : Fin s → M → ZMod p) (b : Fin s → ZMod p)
    (i : Fin s) (x : X) : Bool :=
  decide (rmEval feat coeff x i = b i)

/-- **Degree-1 Reed–Muller is exactly the varying-affine family (PROVED).**  Taking the degree-1 features
`feat m x = x_m` (`M = Fin n`) makes `rmEval` the inner product `dotEval` and `rmGate` the entry-262 `varGate`.  So the
varying-affine family is the degree-1 special case of this Reed–Muller family. -/
theorem rmGate_degree_one_eq_varGate {p n s : ℕ} (a : Fin s → Fin n → ZMod p) (b : Fin s → ZMod p) :
    rmGate (fun (m : Fin n) (x : Fin n → ZMod p) => x m) a b = varGate a b := by
  funext i x
  simp only [rmGate, varGate, rmEval, dotEval]

/-- **Feature general position realizes every fire-pattern (PROVED).**  If `rmEval feat coeff` is surjective, then for
any subset `T` the input solving `rmEval feat coeff x = (i ↦ if i∈T then bᵢ else bᵢ+1)` fires gate `i` iff `i ∈ T`.  So
the pattern image is all of `Finset (Fin s)`. -/
theorem rmGate_patternImage_eq_univ {p : ℕ} [Fact p.Prime] {X M : Type} [Fintype M] [Fintype X] {s : ℕ}
    (feat : M → X → ZMod p) (coeff : Fin s → M → ZMod p) (b : Fin s → ZMod p)
    (hsurj : Function.Surjective (rmEval feat coeff)) :
    Finset.image (firePattern (rmGate feat coeff b)) Finset.univ = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro T
  rw [Finset.mem_image]
  obtain ⟨x, hx⟩ := hsurj (fun i => if i ∈ T then b i else b i + 1)
  refine ⟨x, Finset.mem_univ _, ?_⟩
  ext i
  simp only [firePattern, rmGate, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq]
  have hv : rmEval feat coeff x i = (if i ∈ T then b i else b i + 1) := congrFun hx i
  rw [hv]
  by_cases h : i ∈ T
  · simp [h]
  · rw [if_neg h]
    constructor
    · intro hcontra
      have h10 : (1 : ZMod p) = 0 := add_left_cancel (a := b i) (by rw [add_zero]; exact hcontra)
      exact absurd h10 one_ne_zero
    · intro hT; exact absurd hT h

/-- **Reed–Muller / low-degree polynomial gates are exponentially pattern-rich (PROVED).**  Every subset is realized, so
`PatternRich (rmGate feat coeff b) (2^s)`. -/
theorem rmGate_patternRich {p : ℕ} [Fact p.Prime] {X M : Type} [Fintype M] [Fintype X] {s : ℕ}
    (feat : M → X → ZMod p) (coeff : Fin s → M → ZMod p) (b : Fin s → ZMod p)
    (hsurj : Function.Surjective (rmEval feat coeff)) :
    PatternRich (rmGate feat coeff b) (2 ^ s) := by
  unfold PatternRich
  rw [rmGate_patternImage_eq_univ feat coeff b hsurj, Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin]

/-- **Reed–Muller / low-degree polynomial gates co-fire fully (PROVED).**  Solving `rmEval feat coeff x = b` makes
*every* gate fire on a single input `x`, so `CoFiringRich (rmGate feat coeff b) s`. -/
theorem rmGate_coFiringRich {p : ℕ} [Fact p.Prime] {X M : Type} [Fintype M] {s : ℕ}
    (feat : M → X → ZMod p) (coeff : Fin s → M → ZMod p) (b : Fin s → ZMod p)
    (hsurj : Function.Surjective (rmEval feat coeff)) :
    CoFiringRich (rmGate feat coeff b) s := by
  obtain ⟨x, hx⟩ := hsurj b
  refine ⟨x, ?_⟩
  have hpat : firePattern (rmGate feat coeff b) x = Finset.univ := by
    ext i
    simp only [firePattern, rmGate, Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq, iff_true]
    exact congrFun hx i
  rw [hpat, Finset.card_univ, Fintype.card_fin]

/-- **Reed–Muller / low-degree polynomial gates are `AlgExpander` (PROVED).**  Feature general position gives a private
witness per gate: solve `rmEval feat coeff (wit i) = (j ↦ if j=i then bⱼ else bⱼ+1)`, so gate `i` fires on `wit i` and
no other gate does.  Private witnesses force linear independence of the indicators over any field `F`. -/
theorem rmGate_algExpander {p : ℕ} [Fact p.Prime] {X M : Type} [Fintype M] {s : ℕ} {F : Type} [Field F]
    (feat : M → X → ZMod p) (coeff : Fin s → M → ZMod p) (b : Fin s → ZMod p)
    (hsurj : Function.Surjective (rmEval feat coeff)) :
    AlgExpander (F := F) (rmGate feat coeff b) := by
  choose wit hwit using fun (i : Fin s) =>
    hsurj (fun j => if j = i then b j else b j + 1)
  apply private_witness_indep _ wit
  · intro i
    simp only [rmGate, decide_eq_true_eq]
    have hv := congrFun (hwit i) i
    rw [hv, if_pos rfl]
  · intro i j hji
    simp only [rmGate, decide_eq_false_iff_not]
    have hv := congrFun (hwit i) j
    rw [hv, if_neg hji]
    intro hcontra
    have h10 : (1 : ZMod p) = 0 := add_left_cancel (a := b j) (by rw [add_zero]; exact hcontra)
    exact absurd h10 one_ne_zero

/-- **Wiring Reed–Muller into Williams (PROVED, modulo the two named sockets).**  *Given* the lower-bound socket
`PatternRichCrossFieldLowerBound` (entry 262) and the entry-261 bridge `crossFieldHard_to_ACC0Component`, the
Reed–Muller / low-degree polynomial family yields the `ACC⁰[composite]` component — with `AlgExpander` and `PatternRich`
**discharged here** (proved under feature general position).  The only remaining open inputs are the two named sockets. -/
theorem rmGate_ACC0_chain {p : ℕ} [Fact p.Prime] {X M : Type} [Fintype M] [Fintype X] {s : ℕ}
    {F : Type} [Field F]
    (feat : M → X → ZMod p) (coeff : Fin s → M → ZMod p) (b : Fin s → ZMod p)
    (hsurj : Function.Surjective (rmEval feat coeff))
    (CrossFieldCountHard ACC0CompositeComponent : Prop)
    (hLB : PatternRichCrossFieldLowerBound (rmGate feat coeff b) CrossFieldCountHard F)
    (hBridge : crossFieldHard_to_ACC0Component CrossFieldCountHard ACC0CompositeComponent) :
    ACC0CompositeComponent := by
  apply hBridge
  apply hLB
  · exact rmGate_algExpander feat coeff b hsurj
  · exact rmGate_patternRich feat coeff b hsurj

/-!
**The state of the program.**  Three proved families now satisfy the count-hardness antecedent `AlgExpander ∧
PatternRich`: dictator/`MOD_q` (260–261, count-hard in-arc via `Layer4.mod_q_indicators_false`), varying-direction
affine (262, under general position), and **Reed–Muller / low-degree polynomial gates** (here, under feature general
position) — with the affine family being the degree-1 special case (`rmGate_degree_one_eq_varGate`).  The single missing
theorem is `PatternRichCrossFieldLowerBound`, whose recommended attack is `NonNativeDegreeLowerBound` (non-native degree
over `F_q` = Reed–Muller distance, the Razborov–Smolensky measure); both are Smolensky-strength (entry-238
`CarryRefinementCrossing`), not proved.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ReedMullerGates

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ReedMullerGates.rmGate_degree_one_eq_varGate
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ReedMullerGates.rmGate_patternImage_eq_univ
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ReedMullerGates.rmGate_patternRich
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ReedMullerGates.rmGate_coFiringRich
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ReedMullerGates.rmGate_algExpander
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ReedMullerGates.rmGate_ACC0_chain
