import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CrossFieldCountCore
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ReedMullerGates

/-!
# Attacking `PatternRichCrossFieldLowerBound` via the non-native degree route — the Smolensky counting engine, PROVED

This is the direct attack on the single open target `PatternRichCrossFieldLowerBound` (entry 262) along its recommended
Razborov–Smolensky route (`NonNativeDegreeLowerBound`): factor the lower bound through *non-native polynomial degree
over the field `F`* (the `F_q` of the cross-field count, `q ≠ p`).  The route has two halves:

* **(B) richness forces high non-native degree** — the *counting* half (Smolensky's dimension argument);
* **(A) small resources force low non-native degree** — the *polynomial-method* half (the probabilistic
  low-degree approximation of `AC⁰[p]` circuits).

**What this file does honestly.**  It **proves the entire (B) engine** — the dimension counting and the rank
pigeonhole that are the actual mechanism of Smolensky's lower bound — and reduces the target to the **single** named
analytic socket (A) (the polynomial method), closing the implication through entry-262's
`patternRich_lb_of_nonNativeDegree`.  Half (A) is the genuine open analytic core (its concrete instances are the in-arc
`Layer3.parity_function_lower_bound` and `Layer4.mod_q_indicators_false`); it is **not** faked.

## What is proved (clean axioms, no `sorry`)

* **`lowDegreeDim n D := ∑_{i≤D} C(n,i)`** — the dimension of the non-native degree-`≤ D` function space (number of
  multilinear monomials of degree `≤ D`).
* **`lowDegreeDim_lt_two_pow`** (PROVED) — `D < n ⇒ lowDegreeDim n D < 2^n`: the low-degree space is *strictly smaller*
  than the full function space (`Nat.sum_range_choose` + `Finset.sum_lt_sum_of_subset`).  This is the heart of why
  low-degree polynomials cannot compute rich functions.
* **`exists_notMem_of_finrank_lt`** (PROVED) — the rank kernel: if a family `f` spans a space of dimension exceeding
  `finrank W`, then some `f i ∉ W` (`Submodule.span_le` + `Submodule.finrank_mono`).
* **`algExpander_forces_high_degree`** (PROVED) — the Smolensky **pigeonhole**: an `AlgExpander` family of `s` gates
  (rank `s`, via `finrank_span_eq_card`) with `lowDegreeDim n D < s` must contain a gate of non-native degree `> D`
  (a gate outside the degree-`≤ D` submodule `W`).  Too many independent gates cannot all be low-degree.
* **`crossFieldCount_eq_firePattern_card_mod`** (PROVED) — the cross-field count *is* `|firing pattern| mod q` = `MOD_q`
  evaluated on the firing-pattern indicator; this is the function whose `AC⁰[p]` hardness is the in-arc
  `Layer4.mod_q_indicators_false`.

## The reduction (PROVED, modulo the two named sockets)

* **`PolynomialMethodApproximation`** — the (A) socket: a small-resource observer computing the count forces every
  gate-indicator into the degree-`≤ D` submodule `W` (gates approximated by low-degree polynomials).  The genuine open
  analytic core.
* **`LowDegreeDimensionIdentity`** — the (secondary) socket: `finrank W = lowDegreeDim n D` (the multilinear-basis
  count; provable via the `F`-Möbius/ANF basis, cf. the in-arc `anf_involutive` over `F₂`).
* **`nonNativeDegreeLowerBound_via_counting`** (PROVED) — assembles a concrete `NonNativeDegreeLowerBound` instance:
  the (B) half is *proved* by the counting engine; the (A) half is the polynomial-method socket.
* **`patternRichCrossFieldLowerBound_via_nonNativeDegree`** (PROVED) — feeds that through entry-262's
  `patternRich_lb_of_nonNativeDegree` to obtain `PatternRichCrossFieldLowerBound`, modulo the polynomial-method socket.

## Honest scope

The Smolensky *counting + rank* mechanism — the part that makes the non-native degree route work — is **proved here**
as reusable kernels, and the target lower bound is reduced to the *single* analytic socket `PolynomialMethodApproximation`
(plus the dimension identity).  That socket is the probabilistic polynomial method (`AC⁰[p] ⇒` low-degree
approximation), the genuine open analytic core, whose concrete instances are the in-arc `Layer3`/`Layer4` results.  This
does **not** prove the general lower bound, and is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree

open PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion (AlgExpander gateInd)
open PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns
  (NonNativeDegreeLowerBound PatternRichCrossFieldLowerBound patternRich_lb_of_nonNativeDegree)

/-! ## Part A — the Smolensky counting engine (PROVED) -/

/-- **The dimension of the non-native degree-`≤ D` function space.**  The number of multilinear monomials of degree
`≤ D` over `n` variables: `∑_{i≤D} C(n,i)`.  Functions of non-native degree `≤ D` form a subspace of this dimension. -/
def lowDegreeDim (n D : ℕ) : ℕ := ∑ i ∈ Finset.range (D + 1), n.choose i

/-- **The low-degree space is strictly smaller than the full function space (PROVED).**  For `D < n`,
`lowDegreeDim n D < 2^n`.  Since `∑_{i≤n} C(n,i) = 2^n` and the top term `C(n,n) = 1` (and others) are dropped, the
degree-`≤ D` sum is strictly less.  This is the engine of Smolensky's bound: a `2^n`-rich behaviour cannot be packed
into the `< 2^n`-dimensional low-degree space. -/
theorem lowDegreeDim_lt_two_pow {n D : ℕ} (h : D < n) : lowDegreeDim n D < 2 ^ n := by
  have hbase : (∑ i ∈ Finset.range (n + 1), n.choose i) = 2 ^ n := Nat.sum_range_choose n
  have hn : n ∉ Finset.range (D + 1) := by simp only [Finset.mem_range]; omega
  have key : lowDegreeDim n D + n.choose n ≤ ∑ i ∈ Finset.range (n + 1), n.choose i := by
    rw [lowDegreeDim]
    calc (∑ i ∈ Finset.range (D + 1), n.choose i) + n.choose n
        = ∑ i ∈ insert n (Finset.range (D + 1)), n.choose i := by
          rw [Finset.sum_insert hn]; ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), n.choose i := by
          apply Finset.sum_le_sum_of_subset
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_range] at hk ⊢
          omega
  rw [hbase, Nat.choose_self] at key
  omega

/-! ## Part B — the rank kernel and the Smolensky pigeonhole (PROVED) -/

/-- **The rank kernel (PROVED).**  If the family `f` spans a space whose dimension exceeds `finrank W`, then some `f i`
escapes `W`.  (If all `f i ∈ W` then `span (range f) ≤ W`, so `finrank (span) ≤ finrank W` — contradicting the strict
inequality.) -/
theorem exists_notMem_of_finrank_lt {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {ι : Type} (f : ι → V) (W : Submodule F V)
    (hlt : Module.finrank F W < Module.finrank F (Submodule.span F (Set.range f))) :
    ∃ i, f i ∉ W := by
  by_contra hcon
  push_neg at hcon
  have hsub : Submodule.span F (Set.range f) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hcon i
  have hmono := Submodule.finrank_mono hsub
  omega

/-- **The Smolensky pigeonhole (PROVED).**  An `AlgExpander` family of `s` gates (so the gate indicators are linearly
independent, spanning a space of dimension `s`) with `lowDegreeDim n D < s` must contain a gate whose indicator lies
*outside* the non-native degree-`≤ D` submodule `W` — i.e. a gate of non-native degree `> D`.  *Too many independent
gates cannot all be low-degree.*  This is the concrete (B)-half engine. -/
theorem algExpander_forces_high_degree {X F : Type} [Fintype X] [Field F] {s : ℕ}
    (gates : Fin s → (X → Bool)) (hAE : AlgExpander (F := F) gates)
    (W : Submodule F (X → F)) (n D : ℕ)
    (hW : Module.finrank F W = lowDegreeDim n D) (hlt : lowDegreeDim n D < s) :
    ∃ i, gateInd gates i ∉ W := by
  apply exists_notMem_of_finrank_lt (gateInd gates (F := F)) W
  rw [hW, finrank_span_eq_card hAE, Fintype.card_fin]
  exact hlt

/-! ## The cross-field count is `MOD_q` of the firing pattern (PROVED) -/

/-- **The cross-field count is `|firing pattern| mod q` (PROVED).**  Definitionally, `crossFieldCount q gates x` is the
cardinality of the firing pattern, reduced mod `q` — i.e. `MOD_q` evaluated on the firing-pattern indicator.  This is the
function whose `AC⁰[p]` hardness (`q ∤ p`) is the in-arc Razborov–Smolensky theorem `Layer4.mod_q_indicators_false`. -/
theorem crossFieldCount_eq_firePattern_card_mod {X : Type} {s : ℕ} (q : ℕ)
    (gates : Fin s → (X → Bool)) (x : X) :
    PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCountCore.crossFieldCount q gates x
      = (PallLean.Paper93.DeepMath.PathB.ACC0CoFiring.firePattern gates x).card % q := rfl

/-! ## The reduction — two named sockets, the (B) half proved by the engine above -/

/-- **The polynomial-method socket — the (A) half, the genuine open analytic core (NOT proved).**  A small-resource
observer computing the cross-field count forces every gate-indicator into the non-native degree-`≤ D` submodule `W`
(the `AC⁰[p]` gates are approximated by low-degree `F`-polynomials).  This is the probabilistic polynomial method; its
concrete instances are the in-arc `Layer3.parity_function_lower_bound` and `Layer4.mod_q_indicators_false`. -/
def PolynomialMethodApproximation {X F : Type} [Fintype X] [Field F] {s : ℕ}
    (gates : Fin s → (X → Bool)) (W : Submodule F (X → F)) (ComputesCount : Prop) : Prop :=
  ComputesCount → ∀ i, gateInd gates i ∈ W

/-- **The dimension-identity socket (secondary, NOT proved here).**  The non-native degree-`≤ D` function submodule `W`
has dimension `lowDegreeDim n D`.  Provable via the multilinear (`F`-Möbius/ANF) monomial basis — cf. the in-arc
`anf_involutive` over `F₂`; socketed here. -/
def LowDegreeDimensionIdentity {X F : Type} [Fintype X] [Field F]
    (W : Submodule F (X → F)) (n D : ℕ) : Prop :=
  Module.finrank F W = lowDegreeDim n D

/-- **The non-native degree route, assembled (PROVED, modulo the polynomial-method socket).**  Builds a concrete
`NonNativeDegreeLowerBound` instance with `HighNonNativeDegree := (∃ gate outside W)` and `CrossFieldCountHard :=
(¬ ComputesCount)`:

* the **(B) half** — `AlgExpander → PatternRich → HighNonNativeDegree` — is *proved* by `algExpander_forces_high_degree`
  (the counting engine);
* the **(A) half** — `HighNonNativeDegree → CrossFieldCountHard` — is the contrapositive of the polynomial-method socket
  (`hPoly`). -/
theorem nonNativeDegreeLowerBound_via_counting {X F : Type} [Fintype X] [Field F] {s : ℕ}
    (gates : Fin s → (X → Bool)) (W : Submodule F (X → F)) (n D : ℕ)
    (hW : Module.finrank F W = lowDegreeDim n D) (hlt : lowDegreeDim n D < s)
    (ComputesCount : Prop) (hPoly : PolynomialMethodApproximation gates W ComputesCount) :
    NonNativeDegreeLowerBound gates (∃ i, gateInd gates i ∉ W) (¬ ComputesCount) F := by
  constructor
  · intro hAE _hPR
    exact algExpander_forces_high_degree gates hAE W n D hW hlt
  · rintro ⟨i, hi⟩ hc
    exact hi (hPoly hc i)

/-- **`PatternRichCrossFieldLowerBound` via the non-native degree route (PROVED, modulo the polynomial-method socket).**
Feeds the assembled `NonNativeDegreeLowerBound` through entry-262's `patternRich_lb_of_nonNativeDegree` to obtain the
single open target — for any gate family that is `AlgExpander` and has more independent gates than the low-degree
dimension (`lowDegreeDim n D < s`), the cross-field count is hard, *provided* the polynomial-method socket holds.  This
is the direct, honest reduction of the wall to its one genuine analytic ingredient. -/
theorem patternRichCrossFieldLowerBound_via_nonNativeDegree {X F : Type} [Fintype X] [Field F] {s : ℕ}
    (gates : Fin s → (X → Bool)) (W : Submodule F (X → F)) (n D : ℕ)
    (hW : Module.finrank F W = lowDegreeDim n D) (hlt : lowDegreeDim n D < s)
    (ComputesCount : Prop) (hPoly : PolynomialMethodApproximation gates W ComputesCount) :
    PatternRichCrossFieldLowerBound gates (¬ ComputesCount) F :=
  patternRich_lb_of_nonNativeDegree gates _ _ F
    (nonNativeDegreeLowerBound_via_counting gates W n D hW hlt ComputesCount hPoly)

/-!
**The state of the wall.**  The non-native degree route is now *machine-assembled* with its Smolensky engine proved:
the dimension counting (`lowDegreeDim_lt_two_pow`) and the rank pigeonhole (`exists_notMem_of_finrank_lt`,
`algExpander_forces_high_degree`) — the actual mechanism by which richness forces high non-native degree — are PROVED,
and discharge the (B) half of `NonNativeDegreeLowerBound`.  The cross-field count is identified with `MOD_q` of the
firing pattern (`crossFieldCount_eq_firePattern_card_mod`).  `PatternRichCrossFieldLowerBound` is reduced to the single
analytic socket `PolynomialMethodApproximation` (the probabilistic polynomial method, `AC⁰[p] ⇒` low-degree
approximation) plus the dimension identity — the genuine open Razborov–Smolensky core (entry-238
`CarryRefinementCrossing`), whose concrete instances are the in-arc `Layer3`/`Layer4` lower bounds.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree.lowDegreeDim_lt_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree.exists_notMem_of_finrank_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree.algExpander_forces_high_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree.crossFieldCount_eq_firePattern_card_mod
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree.nonNativeDegreeLowerBound_via_counting
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree.patternRichCrossFieldLowerBound_via_nonNativeDegree
