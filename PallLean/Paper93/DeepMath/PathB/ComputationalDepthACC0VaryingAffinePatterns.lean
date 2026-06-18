import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FirePatternRichness

/-!
# Varying-direction affine hyperplanes — a SECOND proved `AlgExpander` + `PatternRich` family, beyond dictator/MOD_q

The invariant stack is fixed (entries 256–261): `AlgExpander` (non-redundant) + `PatternRich` (many distinct,
*large* co-firing patterns) is the count-hardness hypothesis, with the open lower bound socketed as
`PatternRichCrossFieldLowerBound`.  Only the dictator/`MOD_q` family had been shown to satisfy *both*.  This file
delivers a genuinely different proved family — **varying-direction affine hyperplanes** — and isolates the real
lower-bound target and its Razborov–Smolensky attack invariant (non-native degree).

**The family.**  Directions `a : Fin s → (Fin n → ZMod p)` and offsets `b : Fin s → ZMod p`.  Gate `i` fires on
`x : Fin n → ZMod p` iff `⟨a i, x⟩ = b i`, i.e. `∑ⱼ (a i j)·xⱼ = b i` (`varGate`).  Each gate is the affine
hyperplane `{x : ⟨a i, x⟩ = b i}` with its *own* direction `a i` — unlike the *parallel* family (one fixed
all-ones direction, varying offset), whose hyperplanes are disjoint and never co-fire.

**General position.**  The geometric general-position hypothesis is that the evaluation map
`dotEval a : x ↦ (⟨a i, x⟩)ᵢ` is **surjective** — every value-vector is attained (for `n = s` this is exactly that the
direction matrix is invertible).  Surjectivity is precisely what lets us *solve* for an input realizing any prescribed
firing pattern, which is what both `AlgExpander` and `PatternRich` need.

## What is proved (clean axioms, no `sorry`)

* **`varyingAffine_patternImage_eq_univ`** (PROVED) — under general position, *every* subset `T ⊆ Fin s` is realized
  as a fire-pattern: solve `dotEval a x = (i ↦ if i∈T then bᵢ else bᵢ+1)`; then gate `i` fires iff `i ∈ T`.  So the
  pattern image is all of `Finset (Fin s)`.
* **`varyingAffine_patternRich`** (PROVED) — hence `PatternRich (varGate a b) (2^s)`: exponentially many distinct
  fire-patterns (every subset).
* **`varyingAffine_coFiringRich`** (PROVED) — the *full* pattern is realized (`T = univ`): a single input fires **all
  `s` gates simultaneously**, so `CoFiringRich (varGate a b) s`.  This is the genuinely-new content *beyond* the
  parallel family, which can never co-fire `≥ 2` gates.
* **`varyingAffine_algExpander`** (PROVED) — general position gives private witnesses (solve for the singleton pattern
  `{i}`), so the indicators are linearly independent over any field `F`: `AlgExpander`.
* **`parallel_pattern_image_ne_univ`** (PROVED, `s ≥ 2`) — the **degenerate easy subcase**: for the parallel family
  (fixed all-ones direction), the all-fire pattern `univ` is *never* realized (no input co-fires `≥ 2` gates, entry 259),
  so its pattern image `≠ univ` — general position *fails*.  This is exactly the rank-deficient (`a i` all equal)
  degeneracy that makes the parallel fire-count easy.

## The real lower-bound target + the RS attack invariant (named sockets)

* **`PatternRichCrossFieldLowerBound`** — *the single named missing theorem*:
  `AlgExpander gates → PatternRich gates (2^s) → CrossFieldCountHard`.
* **`NonNativeDegreeLowerBound`** — the Razborov–Smolensky **attack invariant**: factor the target through *non-native
  polynomial degree over `F_q`* (`q ≠ p`).  `(AlgExpander ∧ PatternRich ⇒ HighNonNativeDegree) ∧ (HighNonNativeDegree ⇒
  CrossFieldCountHard)`.  This is the route closest to RS (degree of the `F_q`-representation of the mod-`q` count).
* **`patternRich_lb_of_nonNativeDegree`** (PROVED) — the attack invariant *implies* the target (composition).
* **`varyingAffine_ACC0_chain`** (PROVED) — the payoff: *given* the lower-bound socket and the entry-261 bridge
  `crossFieldHard_to_ACC0Component`, the varying-affine family yields the `ACC⁰[composite]` component **with
  `AlgExpander` and `PatternRich` discharged** (proved here for this family).  Only the two named sockets remain open.

## Honest scope

A second genuinely-different family (varying-direction affine, not dictator/`MOD_q`) is proved `AlgExpander` +
`PatternRich` + `CoFiringRich` under general position, with the parallel family shown to be the degenerate easy
subcase.  The chain to `ACC⁰[composite]` is assembled with all the *family-specific* hypotheses discharged; the only
remaining inputs are the named `PatternRichCrossFieldLowerBound`/`NonNativeDegreeLowerBound` socket (Smolensky-strength,
entry-238 `CarryRefinementCrossing`) and the named `crossFieldHard_to_ACC0Component` bridge.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns

open PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion (AlgExpander)
open PallLean.Paper93.DeepMath.PathB.ACC0CoFiring (firePattern CoFiringRich)
open PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplanes (private_witness_indep)
open PallLean.Paper93.DeepMath.PathB.ACC0FirePatternRichness
  (PatternRich parallel_no_large_patterns crossFieldHard_to_ACC0Component)

/-- **The evaluation map** `x ↦ (⟨a i, x⟩)ᵢ`: row `i` is the inner product of direction `a i` with `x`. -/
def dotEval {p n s : ℕ} (a : Fin s → Fin n → ZMod p) (x : Fin n → ZMod p) : Fin s → ZMod p :=
  fun i => ∑ j, a i j * x j

/-- **The varying-direction affine gate family.**  Gate `i` fires on `x` iff `⟨a i, x⟩ = b i` — the affine hyperplane
`{x : ⟨a i, x⟩ = b i}` with its own direction `a i`. -/
def varGate {p n s : ℕ} (a : Fin s → Fin n → ZMod p) (b : Fin s → ZMod p)
    (i : Fin s) (x : Fin n → ZMod p) : Bool :=
  decide (dotEval a x i = b i)

/-- **General position realizes every fire-pattern (PROVED).**  If `dotEval a` is surjective, then for any subset
`T ⊆ Fin s` the input solving `dotEval a x = (i ↦ if i∈T then bᵢ else bᵢ+1)` fires gate `i` iff `i ∈ T` (using
`bᵢ+1 ≠ bᵢ`).  So the image of `firePattern (varGate a b)` is all of `Finset (Fin s)`. -/
theorem varyingAffine_patternImage_eq_univ {p n s : ℕ} [Fact p.Prime] [NeZero p]
    (a : Fin s → Fin n → ZMod p) (b : Fin s → ZMod p)
    (hsurj : Function.Surjective (dotEval a)) :
    Finset.image (firePattern (varGate a b)) Finset.univ = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro T
  rw [Finset.mem_image]
  obtain ⟨x, hx⟩ := hsurj (fun i => if i ∈ T then b i else b i + 1)
  refine ⟨x, Finset.mem_univ _, ?_⟩
  ext i
  simp only [firePattern, varGate, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq]
  have hv : dotEval a x i = (if i ∈ T then b i else b i + 1) := congrFun hx i
  rw [hv]
  by_cases h : i ∈ T
  · simp [h]
  · rw [if_neg h]
    constructor
    · intro hcontra
      have h10 : (1 : ZMod p) = 0 := add_left_cancel (a := b i) (by rw [add_zero]; exact hcontra)
      exact absurd h10 one_ne_zero
    · intro hT; exact absurd hT h

/-- **Varying-direction affine hyperplanes are exponentially pattern-rich (PROVED).**  Every subset is realized, so
`PatternRich (varGate a b) (2^s)`: `2^s` distinct fire-patterns. -/
theorem varyingAffine_patternRich {p n s : ℕ} [Fact p.Prime] [NeZero p]
    (a : Fin s → Fin n → ZMod p) (b : Fin s → ZMod p)
    (hsurj : Function.Surjective (dotEval a)) :
    PatternRich (varGate a b) (2 ^ s) := by
  unfold PatternRich
  rw [varyingAffine_patternImage_eq_univ a b hsurj, Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin]

/-- **Varying-direction affine hyperplanes co-fire fully (PROVED).**  Solving `dotEval a x = b` makes *every* gate fire
on a single input `x`, so `CoFiringRich (varGate a b) s`.  This is the content the parallel family lacks: parallel
hyperplanes are disjoint and never co-fire `≥ 2` gates (entry 259). -/
theorem varyingAffine_coFiringRich {p n s : ℕ} [Fact p.Prime]
    (a : Fin s → Fin n → ZMod p) (b : Fin s → ZMod p)
    (hsurj : Function.Surjective (dotEval a)) :
    CoFiringRich (varGate a b) s := by
  obtain ⟨x, hx⟩ := hsurj b
  refine ⟨x, ?_⟩
  have hpat : firePattern (varGate a b) x = Finset.univ := by
    ext i
    simp only [firePattern, varGate, Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq, iff_true]
    exact congrFun hx i
  rw [hpat, Finset.card_univ, Fintype.card_fin]

/-- **Varying-direction affine hyperplanes are `AlgExpander` (PROVED).**  General position gives a private witness for
each gate: solve `dotEval a (wit i) = (j ↦ if j=i then bⱼ else bⱼ+1)`, so gate `i` fires on `wit i` and no other gate
does.  Private witnesses force linear independence of the indicators over any field `F`. -/
theorem varyingAffine_algExpander {p n s : ℕ} [Fact p.Prime] {F : Type} [Field F]
    (a : Fin s → Fin n → ZMod p) (b : Fin s → ZMod p)
    (hsurj : Function.Surjective (dotEval a)) :
    AlgExpander (F := F) (varGate a b) := by
  choose wit hwit using fun (i : Fin s) =>
    hsurj (fun j => if j = i then b j else b j + 1)
  apply private_witness_indep _ wit
  · intro i
    simp only [varGate, decide_eq_true_eq]
    have hv := congrFun (hwit i) i
    rw [hv, if_pos rfl]
  · intro i j hji
    simp only [varGate, decide_eq_false_iff_not]
    have hv := congrFun (hwit i) j
    rw [hv, if_neg hji]
    intro hcontra
    have h10 : (1 : ZMod p) = 0 := add_left_cancel (a := b j) (by rw [add_zero]; exact hcontra)
    exact absurd h10 one_ne_zero

/-- **The parallel family is the degenerate easy subcase (PROVED, `s ≥ 2`).**  For the parallel hyperplanes (one fixed
all-ones direction, distinct offsets), the all-fire pattern `univ` is *never* realized — no input co-fires `≥ 2` gates
(entry 259) — so the pattern image `≠ univ`: general position *fails*.  This is the rank-deficient (`a i` all equal)
degeneracy, exactly where the parallel fire-count becomes easy. -/
theorem parallel_pattern_image_ne_univ {p n s : ℕ} [NeZero p] (hs : 2 ≤ s) (targets : Fin s → ZMod p)
    (hinj : Function.Injective targets) :
    Finset.image
        (firePattern (fun (i : Fin s) (x : Fin (n + 1) → ZMod p) => decide ((∑ j, x j) = targets i)))
        Finset.univ
      ≠ Finset.univ := by
  intro hcontra
  have hmem : (Finset.univ : Finset (Fin s)) ∈
      Finset.image
        (firePattern (fun (i : Fin s) (x : Fin (n + 1) → ZMod p) => decide ((∑ j, x j) = targets i)))
        Finset.univ := by
    rw [hcontra]; exact Finset.mem_univ _
  rw [Finset.mem_image] at hmem
  obtain ⟨x, _, hx⟩ := hmem
  have hcard : 2 ≤ (firePattern
      (fun (i : Fin s) (x : Fin (n + 1) → ZMod p) => decide ((∑ j, x j) = targets i)) x).card := by
    rw [hx, Finset.card_univ, Fintype.card_fin]; exact hs
  exact parallel_no_large_patterns targets hinj x hcard

/-- **The single named missing theorem (Smolensky-strength, NOT proved).**  The count lower bound under the corrected
invariant: a non-redundant (`AlgExpander`) and exponentially pattern-rich (`PatternRich (2^s)`) gate family has a hard
mod-`q` fire-count. -/
def PatternRichCrossFieldLowerBound {X : Type} [Fintype X] {s : ℕ} (gates : Fin s → (X → Bool))
    (CrossFieldCountHard : Prop) (F : Type) [Field F] : Prop :=
  AlgExpander (F := F) gates → PatternRich gates (2 ^ s) → CrossFieldCountHard

/-- **The Razborov–Smolensky attack invariant (NOT proved).**  Factor the lower bound through *non-native polynomial
degree over `F_q`* (`q ≠ p`) — the RS measure: (1) algebraic expansion + pattern richness force a *high* non-native
degree for the mod-`q` count's `F_q`-representation; (2) high non-native degree gives count-hardness.  This is the
route closest to Razborov–Smolensky. -/
def NonNativeDegreeLowerBound {X : Type} [Fintype X] {s : ℕ} (gates : Fin s → (X → Bool))
    (HighNonNativeDegree CrossFieldCountHard : Prop) (F : Type) [Field F] : Prop :=
  (AlgExpander (F := F) gates → PatternRich gates (2 ^ s) → HighNonNativeDegree)
    ∧ (HighNonNativeDegree → CrossFieldCountHard)

/-- **The attack invariant implies the target (PROVED, composition).**  If the non-native degree route holds, then the
single missing theorem `PatternRichCrossFieldLowerBound` holds — so attacking non-native degree (RS) is a sound route to
the target. -/
theorem patternRich_lb_of_nonNativeDegree {X : Type} [Fintype X] {s : ℕ} (gates : Fin s → (X → Bool))
    (HighNonNativeDegree CrossFieldCountHard : Prop) (F : Type) [Field F]
    (h : NonNativeDegreeLowerBound gates HighNonNativeDegree CrossFieldCountHard F) :
    PatternRichCrossFieldLowerBound gates CrossFieldCountHard F := by
  intro hae hpr
  exact h.2 (h.1 hae hpr)

/-- **Wiring varying-affine into Williams (PROVED, modulo the two named sockets).**  *Given* the lower-bound socket
`PatternRichCrossFieldLowerBound` and the entry-261 bridge `crossFieldHard_to_ACC0Component`, the varying-direction
affine family yields the `ACC⁰[composite]` component — with `AlgExpander` and `PatternRich` **discharged here** (proved
for this family under general position).  The only remaining open inputs are the two named sockets. -/
theorem varyingAffine_ACC0_chain {p n s : ℕ} [Fact p.Prime] [NeZero p] {F : Type} [Field F]
    (a : Fin s → Fin n → ZMod p) (b : Fin s → ZMod p)
    (hsurj : Function.Surjective (dotEval a))
    (CrossFieldCountHard ACC0CompositeComponent : Prop)
    (hLB : PatternRichCrossFieldLowerBound (varGate a b) CrossFieldCountHard F)
    (hBridge : crossFieldHard_to_ACC0Component CrossFieldCountHard ACC0CompositeComponent) :
    ACC0CompositeComponent := by
  apply hBridge
  apply hLB
  · exact varyingAffine_algExpander a b hsurj
  · exact varyingAffine_patternRich a b hsurj

/-!
**The state of the program.**  Chain: `AlgExpander ∧ PatternRich → [PatternRichCrossFieldLowerBound] →
CrossFieldCountHard → [crossFieldHard_to_ACC0Component] → ACC0CompositeComponent → (Williams) → NEXP ⊄ ACC⁰`.  Two
proved families now satisfy the antecedent: dictator/`MOD_q` (entries 260–261, count-hard in-arc via
`Layer4.mod_q_indicators_false`) and **varying-direction affine** (here, under general position).  The parallel family
is the degenerate easy subcase (general position fails; `parallel_pattern_image_ne_univ`).  The single missing theorem
is `PatternRichCrossFieldLowerBound`; its recommended attack is `NonNativeDegreeLowerBound` (non-native degree over
`F_q`, closest to Razborov–Smolensky), which `patternRich_lb_of_nonNativeDegree` shows suffices.  Both are
Smolensky-strength (entry-238 `CarryRefinementCrossing`); not proved.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns.varyingAffine_patternImage_eq_univ
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns.varyingAffine_patternRich
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns.varyingAffine_coFiringRich
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns.varyingAffine_algExpander
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns.parallel_pattern_image_ne_univ
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns.patternRich_lb_of_nonNativeDegree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns.varyingAffine_ACC0_chain
