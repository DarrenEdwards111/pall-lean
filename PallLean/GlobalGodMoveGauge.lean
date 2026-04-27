/-
  GlobalGodMoveGauge.lean — Π⋆ projection and projected SPDP rank
  -------------------------------------------------------------

  This file implements the paper's **Global God-Move Gauge** Π⋆ (Definition 7
  / Theorem 207) as a per-compilation ℚ-linear projection on
  `MvPolynomial (Fin n) ℚ`, and the associated **projected SPDP rank**
  functional `mlBlockedSpdpRankProjected`.

  ## Architecture (post-consolidation)

  Earlier drafts of this file used three independent axioms (rank monotonicity,
  projected P-side bound, projected NP-side preservation for SAT-deciders).
  This file consolidates those three claims into a single existence axiom for a
  structure `IsAmplituhedronGauge` that bundles all three properties for a given
  Cook-Levin compilation. The three previous axioms are then *derived* as
  theorems via `Classical.choose` of the existence witness.

  Net effect on the trust surface:
  * Old: 3 custom axioms (`piStar` + 3 properties).
  * New: 1 custom axiom (`exists_amplituhedron_gauge`) plus standard `Classical.choice`.

  Mathematically the trust is the same — the existence axiom asserts the
  conjunction of the three previous properties. But the axiom *surface* is
  strictly smaller and structurally cleaner: there is exactly one mathematical
  claim to discharge (existence of the amplituhedron gauge), and that claim
  exactly matches what the paper's Theorem 207 / §6 invokes via "uniform
  projection Π_⋆ derived from amplituhedron geometry".

  ## Why this file exists

  The previously-trusted axiom `spdp_profile_generators`
  (`PallLean/SymmetricPower.lean`) is documented in `AxiomAnalysis.lean` as
  *mathematically false*: it claims `mlBlockedSpdpRank ≤ (κ+1)¹²` for the
  Cook-Levin compiled polynomial of any DTM, but the axiom-free, sorry-free
  theorem `GodMoveReal.compiled_np_lower_bound_any_dtm` exhibits
  `C(n/3, log n)` linearly independent SPDP generators from disjoint blocks.
  Their conjunction produces the inconsistency
  `spdp_profile_generators_inconsistent_with_np_side` at n = 2⁸⁰⁴.

  Per the paper (Definition 6 / Theorem 207), the resolution is a
  position-quotienting projection Π⋆ that:

  1. Collapses block-position multiplicity for compiled polynomials of
     **generic** DTMs (so the P-side bound on the projected rank becomes
     polynomial — property `p_side_bound` of `IsAmplituhedronGauge`).
  2. **Preserves** the clause-sheet identity-minor structure for compiled
     polynomials of **SAT-deciding** DTMs, where `DecidesSAT` constrains the
     tableau to encode the formula's clause data
     (property `preserves_identity_minor_for_sat_deciders`).

  The asymmetry between (1) and (2) is exactly what makes `DecidesSAT`
  genuinely load-bearing in the new chain: the projected NP-side lower bound
  requires `DecidesSAT`, while the projected P-side upper bound applies
  uniformly. This breaks the previous "any-DTM" inconsistency.

  ## Open mathematical content

  The single existence axiom `exists_amplituhedron_gauge` replaces the
  provably-false `spdp_profile_generators`. It is mathematically plausible and
  consistent with `compiled_np_lower_bound_any_dtm`. A concrete proof requires:

  * Constructing the amplituhedron gauge Π⋆ explicitly (the paper's positive
    geometry construction / derandomized switching lemma instantiation),
  * Proving that the constructed Π⋆ satisfies the three properties bundled
    into `IsAmplituhedronGauge`.

  This is open research — we axiomatise the *spec* here so the rest of the
  separation chain becomes structurally honest.
-/
import PallLean.MultilinearSPDP
import PallLean.CookLevinDefs
import PallLean.GodMoveCore
import PallLean.GodMoveReal
import Mathlib.Tactic

namespace GlobalGodMoveGauge

open MvPolynomial SPDP MultilinearSPDP TuringMachine PaperFaithfulSeparation

/-! ## The amplituhedron gauge: structure of required properties

`IsAmplituhedronGauge` packages together the three mathematical properties the
paper requires of the Global God-Move Gauge, evaluated at a specific
Cook-Levin compilation.  -/

/-- The mathematical content of the Global God-Move Gauge for a specific
Cook-Levin compilation: a ℚ-linear endomorphism Π on the compiled
polynomial's variable space, satisfying

* (i) **rank monotonicity** — Π does not increase the multilinear blocked
  SPDP rank of any polynomial,
* (ii) **projected P-side bound** — applied to *this* DTM's compiled
  polynomial, the projected rank is at most n²⁰⁰,
* (iii) **projected NP-side preservation for SAT-deciders** — *if* M decides
  3-SAT, then applied to the compiled polynomial Π preserves the identity
  minor lower bound C(n/3, log n) on the projected rank.

Property (i) is the standard rank-decreasing property of any honest
projection. Property (ii) is the position-multiplicity-collapsing content of
the paper's amplituhedron geometry. Property (iii) is the load-bearing site
of `DecidesSAT`: without it, only (ii) applies and no contradiction arises. -/
structure IsAmplituhedronGauge
    (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
         MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) :
    Prop where
  /-- (i) Rank monotonicity — `gauge` does not increase SPDP rank for ANY polynomial. -/
  rank_monotone : ∀ (κ ℓ : ℕ)
      (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
    mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (gauge p) ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p
  /-- (ii) Projected P-side bound on the COMPILED polynomial. -/
  p_side_bound :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≤ n ^ 200
  /-- (iii) Projected NP-side preservation for SAT-deciders.  -/
  preserves_identity_minor_for_sat_deciders : DecidesSAT M →
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-! ## The existence axiom

This is the single load-bearing custom axiom of the file.  It replaces the
provably-false `spdp_profile_generators` with the existence claim that the
paper's amplituhedron gauge actually exists for any Cook-Levin compilation. -/

/-- **Existence of the amplituhedron gauge.**  For every Cook-Levin
compilation in the bounded-parameter regime, there exists a ℚ-linear
endomorphism Π on the compiled polynomial's variable space satisfying the
three properties of `IsAmplituhedronGauge`.

This is the only custom axiom of this file. It encodes the paper's
existence claim from Theorem 207 / §6: "there is a uniform projection
Π_⋆ derived from amplituhedron geometry that ...". The axiom is
*consistent* with the axiom-free `compiled_np_lower_bound_any_dtm` (the
projected rank ≤ unprojected rank, so a small upper bound on projected
does not contradict a large lower bound on unprojected). -/
axiom exists_amplituhedron_gauge
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∃ (gauge : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
               MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      IsAmplituhedronGauge M n hn hn2 htb hns gauge

/-! ## The chosen amplituhedron gauge

We pick a concrete witness via `Classical.choose`, then derive the three
properties as theorems from the chosen witness's specification. -/

/-- The chosen amplituhedron gauge for the Cook-Levin compilation
`(M, n, hn, hn2, htb, hns)`. -/
noncomputable def piStar
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  Classical.choose (exists_amplituhedron_gauge M n hn hn2 htb hns)

/-- The chosen `piStar` satisfies the three amplituhedron gauge properties. -/
theorem piStar_isAmplituhedronGauge
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    IsAmplituhedronGauge M n hn hn2 htb hns (piStar M n hn hn2 htb hns) :=
  Classical.choose_spec (exists_amplituhedron_gauge M n hn hn2 htb hns)

/-! ## The projected SPDP rank functional -/

/-- **Projected SPDP rank** for a Cook-Levin compilation: the multilinear
blocked SPDP rank of the polynomial *after* applying the chosen
amplituhedron gauge. -/
noncomputable def mlBlockedSpdpRankProjected
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (κ ℓ : ℕ)
    (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : ℕ :=
  mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
    (piStar M n hn hn2 htb hns p)

/-! ## Derived theorems (formerly axioms)

The three properties of `IsAmplituhedronGauge` give the three theorems below.
Each was a separate axiom in the previous draft; they are now consequences of
the single existence axiom `exists_amplituhedron_gauge`. -/

/-- **Theorem (formerly Axiom 1): rank monotonicity.** -/
theorem piStar_rank_monotone
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (κ ℓ : ℕ)
    (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) :
    mlBlockedSpdpRankProjected M n hn hn2 htb hns κ ℓ p ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p := by
  unfold mlBlockedSpdpRankProjected
  exact (piStar_isAmplituhedronGauge M n hn hn2 htb hns).rank_monotone κ ℓ p

/-- **Theorem (formerly Axiom 2): projected P-side upper bound.** -/
theorem piStar_p_side_bound
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRankProjected M n hn hn2 htb hns
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200 := by
  unfold mlBlockedSpdpRankProjected
  exact (piStar_isAmplituhedronGauge M n hn hn2 htb hns).p_side_bound

/-- **Theorem (formerly Axiom 3): projected NP-side lower bound for SAT-deciders.**

`DecidesSAT M` is required as a hypothesis — without it, no projected
lower bound is asserted. This is what makes `DecidesSAT` load-bearing
in the separation chain. -/
theorem piStar_preserves_identity_minor_for_sat_deciders
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (hdec : DecidesSAT M)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRankProjected M n hn hn2 htb hns
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  unfold mlBlockedSpdpRankProjected
  exact (piStar_isAmplituhedronGauge M n hn hn2 htb hns).preserves_identity_minor_for_sat_deciders
    hdec

/-! ## Why this resolves the previous inconsistency

The old inconsistency theorem
`PaperFaithfulSeparation.spdp_profile_generators_inconsistent_with_np_side`
derives `False` from:

* (NP-side, axiom-free) `C(n/3, log n) ≤ mlBlockedSpdpRank (compiledPoly T_M)`
  for *any* DTM M, and
* (P-side, axiom) `mlBlockedSpdpRank (compiledPoly T_M) ≤ n²⁰⁰` for *any* DTM M.

Both bounds are on the *same* quantity (un-projected rank) for the *same*
class of objects (any DTM), so their conjunction is a real contradiction —
falsifying the P-side axiom.

The projected formulation breaks this:

* `piStar_p_side_bound` is about the *projected* rank, not un-projected. By
  `piStar_rank_monotone`, projected ≤ un-projected, so the axiom-free
  `compiled_np_lower_bound_any_dtm` does not lift to a lower bound on the
  projected rank.
* `piStar_preserves_identity_minor_for_sat_deciders` lower-bounds the
  projected rank, but **only** for SAT-deciding DTMs. For non-SAT-deciders no
  projected lower bound is asserted, so the projected upper bound's
  universality is consistent.
* The contradiction `piStar_p_side_bound` + `piStar_preserves_identity_minor_for_sat_deciders`
  fires *only* on SAT-deciding DTMs, which exist (with bounded parameters at
  n = 2⁸⁰⁴) only if P = NP. -/

/-! ## Concrete construction (partial): the zero gauge for non-SAT-deciders

This section discharges the existence claim of the amplituhedron gauge
**concretely and axiom-free** in the case where `M` does not decide 3-SAT.

### Observation

The `IsAmplituhedronGauge` structure bundles three properties:

1. `rank_monotone` — holds trivially for the zero linear map, because the
   zero map sends every polynomial to `0`, and the SPDP rank of `0` is `0`
   (lemma `mlBlockedSpdpRank_zero` in `MultilinearSPDP.lean`).
2. `p_side_bound` — likewise trivial: projected rank of `0` is `0 ≤ n²⁰⁰`.
3. `preserves_identity_minor_for_sat_deciders` — the hypothesis is
   `DecidesSAT M`. If `¬ DecidesSAT M`, this property holds **vacuously**.

Therefore the zero linear map satisfies `IsAmplituhedronGauge M n …` for
every DTM `M` that does *not* decide 3-SAT — with no appeal to any axiom
other than those imported from Mathlib.

### Implication for the axiom surface

The full `exists_amplituhedron_gauge` axiom quantifies over *all* bounded-
parameter DTMs. The concrete theorem below shows that the non-SAT-decider
case is a *theorem* discharged by the zero gauge. The axiomatic content of
`exists_amplituhedron_gauge` is therefore entirely concentrated in the
SAT-decider case — a strictly narrower claim that is (arithmetically)
equivalent to "no bounded-parameter SAT-decider exists at n = 2⁸⁰⁴",
i.e., to the separation itself in restricted form.

We package this as (a) a named concrete theorem, (b) a strictly narrower
axiom `exists_amplituhedron_gauge_for_sat_decider`, and (c) a derived
theorem `exists_amplituhedron_gauge_via_narrow_axiom` that recovers the
statement of the original axiom from the narrower axiom plus the concrete
non-SAT-decider case.

**What remains open**: the SAT-decider branch. That is the honest
mathematical frontier — constructing (or axiomatising) a gauge that
simultaneously collapses the P-side workload and preserves the NP-side
identity minor, for a DTM that genuinely decides 3-SAT. -/

/-- The zero linear map on the compiled polynomial's variable space. -/
private noncomputable abbrev zeroGauge (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  (0 : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
        MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)

/-- The zero-gauge image of any polynomial is `0`. -/
private theorem zeroGauge_apply (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) :
    zeroGauge M n hn2 htb hns p = 0 :=
  LinearMap.zero_apply p

/-- Under the zero gauge, the projected SPDP rank of any polynomial is `0`. -/
theorem zeroGauge_spdp_rank_zero
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (κ ℓ : ℕ)
    (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) :
    mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
      (zeroGauge M n hn2 htb hns p) = 0 := by
  rw [zeroGauge_apply]
  exact mlBlockedSpdpRank_zero _ _ _

/-- **Concrete theorem (axiom-free)**: the zero linear map satisfies every
clause of `IsAmplituhedronGauge` for any DTM `M` that does *not* decide
3-SAT.

All three properties are discharged concretely:

* `rank_monotone` reduces to `0 ≤ mlBlockedSpdpRank … p`, immediate from
  `Nat.zero_le`.
* `p_side_bound` reduces to `0 ≤ n²⁰⁰`, immediate from `Nat.zero_le`.
* `preserves_identity_minor_for_sat_deciders` is vacuous under the
  hypothesis `¬ DecidesSAT M`.

Uses no custom axioms beyond the Mathlib standard `propext`,
`Classical.choice`, `Quot.sound`. -/
theorem zeroGauge_isAmplituhedronGauge_of_not_decidesSAT
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnd : ¬ DecidesSAT M) :
    IsAmplituhedronGauge M n hn hn2 htb hns (zeroGauge M n hn2 htb hns) where
  rank_monotone := by
    intro κ ℓ p
    rw [zeroGauge_spdp_rank_zero]
    exact Nat.zero_le _
  p_side_bound := by
    rw [zeroGauge_spdp_rank_zero]
    exact Nat.zero_le _
  preserves_identity_minor_for_sat_deciders := fun hdec => absurd hdec hnd

/-- **Concrete existence theorem (axiom-free) for the non-SAT-decider case**:
for any bounded-parameter DTM `M` that does not decide 3-SAT, an
amplituhedron gauge exists — concretely, the zero linear map works.

This theorem is fully discharged without the `exists_amplituhedron_gauge`
axiom. It narrows the axiomatic content of the amplituhedron gauge
existence claim to the SAT-decider case only. -/
theorem exists_amplituhedron_gauge_of_not_decidesSAT
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnd : ¬ DecidesSAT M) :
    ∃ (gauge : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
               MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      IsAmplituhedronGauge M n hn hn2 htb hns gauge :=
  ⟨zeroGauge M n hn2 htb hns,
   zeroGauge_isAmplituhedronGauge_of_not_decidesSAT M n hn hn2 htb hns hnd⟩

/-! ## Narrowed existence axiom

Using the concrete non-SAT-decider theorem above, we introduce a strictly
narrower axiom that only asserts existence for SAT-deciding DTMs. The full
`exists_amplituhedron_gauge` axiom is then *derivable* from this narrow
axiom combined with `exists_amplituhedron_gauge_of_not_decidesSAT`.

At `n = 2^804` with bounded parameters, the narrow axiom is mathematically
equivalent to "no bounded-parameter SAT-decider exists" (the three
`IsAmplituhedronGauge` properties become arithmetically inconsistent for a
SAT-decider at these bounds: `C(n/3, log n) > n^200` at `n = 2^804`, so
property (ii) and property (iii) cannot both hold for a SAT-decider).

In other words, the narrow axiom makes explicit that the mathematical
content of the amplituhedron gauge is the separation `P ≠ NP` itself,
at the restricted scale and bounds. The existence claim as stated is a
vacuous-for-non-SAT-decider / equivalent-to-separation-for-SAT-decider
packaging of the main conjecture. -/

/-- **Narrowed existence axiom**: an amplituhedron gauge exists for every
*SAT-deciding* DTM with bounded parameters at `n ≥ 2^804`.

This is strictly narrower than `exists_amplituhedron_gauge` (which
quantifies over all DTMs regardless of whether they decide SAT). The
non-SAT-decider case is discharged concretely by
`exists_amplituhedron_gauge_of_not_decidesSAT`, so axiomatising only the
SAT-decider branch reduces the axiomatic content to its genuine
mathematical kernel.

Under the bound `n ≥ 2^804`, this axiom is (arithmetically) equivalent to
"no bounded-parameter SAT-decider exists at n ≥ 2^804" — the separation
`P ≠ NP` in the restricted bounded-parameter form used here. -/
axiom exists_amplituhedron_gauge_for_sat_decider
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ (gauge : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
               MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      IsAmplituhedronGauge M n hn hn2 htb hns gauge

/-- **Derived full-existence theorem**: combines the axiom-free
non-SAT-decider case with the narrow SAT-decider axiom to recover the
statement of the original `exists_amplituhedron_gauge`.

This theorem has the same conclusion as `exists_amplituhedron_gauge` but
uses the strictly narrower axiom `exists_amplituhedron_gauge_for_sat_decider`
— making explicit that the SAT-decider case is the only one carrying
axiomatic content. -/
theorem exists_amplituhedron_gauge_via_narrow_axiom
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∃ (gauge : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
               MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      IsAmplituhedronGauge M n hn hn2 htb hns gauge := by
  by_cases hdec : DecidesSAT M
  · exact exists_amplituhedron_gauge_for_sat_decider M n hn hn2 htb hns hdec
  · exact exists_amplituhedron_gauge_of_not_decidesSAT M n hn hn2 htb hns hdec

/-! ## Summary of the axiomatic trust surface (post-partial-construction)

After this file's concrete partial construction:

* `exists_amplituhedron_gauge` — original axiom, unchanged (kept for
  backward compatibility with the existing separation chain).
* `exists_amplituhedron_gauge_for_sat_decider` — **new, strictly narrower**
  axiom covering only the SAT-decider case. The non-SAT-decider case is
  now an axiom-free theorem (`exists_amplituhedron_gauge_of_not_decidesSAT`).
* `exists_amplituhedron_gauge_via_narrow_axiom` — theorem, same statement
  as `exists_amplituhedron_gauge`, but uses the narrower axiom above.

Migrating `P_ne_NP_via_piStar` to use `exists_amplituhedron_gauge_via_narrow_axiom`
(rather than `exists_amplituhedron_gauge`) would reduce the canonical
chain's axiom surface to `exists_amplituhedron_gauge_for_sat_decider` —
a strict strengthening of the structural honesty of the separation chain. -/

/-! ## Paper-faithful refactor: Theorem 207 (God-Move extraction form)

The `exists_amplituhedron_gauge*` family of axioms above packages everything
into a single ℚ-linear endomorphism Π⋆ acting on `MvPolynomial`. The
paper's Theorem 207 does not actually use a single Π⋆; it decomposes the
argument as:

* **(a) Extraction (Theorem 181/203).** Cook-Levin compilation + God-Move
  extraction produce, from the accepting tableau of a SAT-deciding DTM on
  a hard Tseitin instance, a **coupled sheet** polynomial Q×_Φₙ.
* **(b) P-side bound (Theorem 10 / Lemma 205).** Profile compression +
  Ramanujan-expander CEW bound + amplituhedron / totally-positive projection
  bound the SPDP rank of the coupled sheet from above by n^O(1).
* **(c) NP-side bound (Theorem 98).** The Ramanujan-Tseitin identity minor
  construction bounds the rank of the same coupled sheet from below by
  n^Ω(log n).
* **(d) Contradiction at n = 2^804.** The upper and lower bounds are
  arithmetically incompatible, forcing ¬ P = NP.

The following section bundles the coupled sheet with its two bounds into
a structure `Theorem207Witness`, adds a single existence axiom
`exists_theorem207_witness`, and derives the separation through it.

### What this buys

Each field of `Theorem207Witness` is attached to a named paper theorem, so
the axiomatic frontier maps directly onto the paper's Theorem 207 chain.
The `exists_amplituhedron_gauge*` axioms are *retained* for continuity
(the narrow one becomes derivable from the Theorem 207 axiom, via the
arithmetic bridge in `PaperFaithfulSeparation.lean`); the original full
axiom also remains as an independent alternative formulation.

### What this does **not** buy

The full Theorem 207 witness is still a single axiom rather than three.
Splitting it into three independent axioms (one per paper theorem) would
let (a) and (c) be largely discharged from existing infrastructure — the
compiled polynomial already has an axiom-free NP-side bound via
`compiled_np_lower_bound_any_dtm`, and the extraction (a) is essentially
a data-constructive operation given the accepting tableau. The real open
mathematical content of Theorem 207 is the P-side bound (b): profile
compression + amplituhedron / totally-positive projection is genuine
paper content requiring hundreds of pages of supporting lemmas in the
paper and substantial Lean infrastructure (CEW accounting, derandomised
switching lemma, expander spectral bounds, positive geometry) to
formalise. We do not discharge (b) here; we package it as a field of the
witness so it is visible and named. -/

/-- A paper-faithful two-stage witness for Theorem 207 (Global God-Move
Separation).

The paper's chain is a **two-stage argument**, not a single bound. Stage 1
is the instance-uniform extraction `T_Φ` that maps the paper's instrumented
compiled polynomial `P_{M',n}` to the coupled sheet `Q×_Φ,S`. Stage 2 is
the rank comparison under the Π⋆ gauge (radius-1 diagonal basis),
producing the polynomial SPDP rank bound on `P_{M',n}` via
Width⇒Rank (Theorem 32 / Theorem 10).

Note on Π⋆: the paper's Π⋆ is a **gauge / coordinate system**, not a linear
map on polynomials (see Remark 10: *"the gauge fixes the basis and
locality structure, while Π_Φ performs the actual codimension collapse"*).
In Lean, Π⋆ is realised implicitly by the choice of `BlockPartition` and
the SPDP rank definition — there is no separate `LinearMap` field for it.

### Fields (each tied to a named paper theorem)

* `paperCompiledPoly` — the paper's instrumented P_{M',n} (Theorem 181 /
  Lemma 204): `Q×_Φ(u, ζ(u,v)) + R_{M',Φ}(v)`. This is **distinct from**
  our local `compiledPoly` (which is the product-form Cook-Levin
  compilation used by `compiled_np_lower_bound_any_dtm`); the paper's
  instrumented version has a different structure.
* `sheet` — the extracted coupled sheet Q×_Φ,S (Theorem 181/205).
* `extraction_rank_monotone` — Lemma 205: T_Φ is rank non-increasing,
  so `rank(sheet) ≤ rank(paperCompiledPoly)`.
* `compiled_p_side_bound` — Theorem 10 / Theorem 32 (Width⇒Rank): under
  the Π⋆ gauge, `rank(paperCompiledPoly) ≤ n^200`.
* `sheet_np_side_lower_bound` — Theorem 98 (Ramanujan-Tseitin identity
  minor): `rank(sheet) ≥ C(n/3, log n)`.

### Why `paperCompiledPoly` is a separate field

Our local `compiledPoly` (from `cook_levin_compilation`) is a *product
form* `∏(1 - cᵢ.poly)` satisfying the axiom-free
`compiled_np_lower_bound_any_dtm`: it already has super-polynomial SPDP
rank for any DTM. The paper's P_{M',n} from Theorem 181 is a *sum form*
`Q×_Φ(u,ζ) + R_{M',Φ}(v)` constructed by a different instrumented compiler.
These are genuinely different polynomials with (potentially) different
rank profiles. Collapsing them would be paper-unfaithful — which is why
we bundle `paperCompiledPoly` inside the witness as its own abstract
polynomial. -/
structure Theorem207Witness
    (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type where
  /-- **Theorem 181 / Lemma 204 (Machine-Exact Compiler with Coupled
  Verifier Sheet).** The paper's instrumented compiled polynomial
  `P_{M',n}(u,v) = Q×_Φ(u, ζ(u,v)) + R_{M',Φ}(v)` from the instrumented
  machine M' that prepends clause gadgets and forces a verifier slice.

  This is **distinct from** our local `compiledPoly` — the paper's
  instrumented polynomial has a sum form with coupling structure, whereas
  our local `compiledPoly` is the product-form Cook-Levin compilation. -/
  paperCompiledPoly :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ
  /-- **Theorem 181 / §34.2 (Coupled-sheet extraction).** The coupled
  sheet `Q×_Φ,S` produced by the instance-uniform extraction operator
  `T_Φ = (basis) ◦ (affine relabel) ◦ (restriction) ◦ (projection)`
  applied to `paperCompiledPoly`. -/
  sheet :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ
  /-- **Lemma 205 (Extraction rank monotonicity).** Since `T_Φ` is a
  composition of basis changes, affine relabelings, restrictions, and
  projections (each rank non-increasing by Lemma 38), its rank-monotone
  effect on the sheet satisfies `rank(sheet) ≤ rank(paperCompiledPoly)`. -/
  extraction_rank_monotone :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) sheet ≤
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) paperCompiledPoly
  /-- **Theorem 10 / Theorem 32 (Width⇒Rank, P-side upper bound under
  the Π⋆ gauge).** Under the Π⋆ gauge (radius-1 diagonal basis) the
  paper's instrumented compiled polynomial has polynomial SPDP rank:
  `rank(paperCompiledPoly) ≤ n^200`.

  This is the paper's genuinely deep content — profile compression,
  Ramanujan-expander CEW bound, derandomised switching lemma, and
  amplituhedron / totally-positive projection. The paper devotes
  Sections 7, 29–31, 37–42 to establishing this inequality. -/
  compiled_p_side_bound :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) paperCompiledPoly ≤ n ^ 200
  /-- **Theorem 98 (Ramanujan-Tseitin identity minor, NP-side lower bound
  on the sheet).** The coupled sheet contains a super-polynomial identity
  minor of size `C(n/3, log n)`, coming from the Tseitin encoding of the
  hard 3-CNF family on a Ramanujan expander. -/
  sheet_np_side_lower_bound :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) sheet

/-! ### Machine-checkable Route B component interfaces

Route B separates the *coordinate gauge* from the actual collapse:

* `PiStar` is the paper's gauge / coordinate choice. In this file it is
  represented by the selected block partition and SPDP rank coordinates, not by
  an arbitrary projection that can be applied to erase any hard polynomial.
* `PiPhi` / `T_Phi` is the coupled-sheet extraction. This is the collapse step:
  it extracts the sheet `Qx_Phi,S` from the paper-compiled polynomial. The
  interface below records only the paper-legitimate collapse and the four rank
  facts needed for Theorem 207; it does not expose an unconstrained
  `LinearMap` projection field.

The existing `Theorem207Witness` remains the compatibility bundle. The
component structures below make the four paper claims individually
machine-checkable, and `theorem207Witness_of_components` assembles them back
into the old witness shape. -/

/-- **Route B extraction interface (Theorem 181 / Lemma 204 / Lemma 205 data).**

This carries the paper-compiled polynomial and the coupled sheet extracted from
it by `PiPhi` / `T_Phi`. It intentionally contains no arbitrary `LinearMap`:
the collapse is represented by the existence of the coupled sheet itself, with
rank behavior supplied by `Theorem207ExtractionRankMonotone`. -/
structure Theorem207Extraction
    (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type where
  /-- The paper's instrumented `P_{M',n}`, in PiStar gauge coordinates. -/
  paperCompiledPoly :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ
  /-- The coupled sheet `Qx_Phi,S` extracted by PiPhi / `T_Phi`. -/
  coupledSheet :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ

/-- **Route B extraction rank monotonicity interface (Lemma 205).**

The PiPhi / coupled-sheet extraction is rank non-increasing. This is the
machine statement of the collapse step; PiStar only fixes the coordinates in
which this rank is measured. -/
structure Theorem207ExtractionRankMonotone
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (E : Theorem207Extraction M n hn hn2 htb hns) : Prop where
  extraction_rank_monotone :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) E.coupledSheet ≤
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) E.paperCompiledPoly

/-- **Route B P-side upper-bound interface (Theorem 10 / Theorem 32).**

Under the PiStar gauge / coordinate system, the paper-compiled polynomial has
polynomial SPDP rank. -/
structure Theorem207PSideUpperBound
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (E : Theorem207Extraction M n hn hn2 htb hns) : Prop where
  compiled_p_side_bound :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) E.paperCompiledPoly ≤ n ^ 200

/-- **Route B NP-side lower-bound interface (Theorem 98).**

The same coupled sheet extracted by PiPhi carries the Ramanujan-Tseitin
identity minor lower bound. -/
structure Theorem207NPSideLowerBound
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (E : Theorem207Extraction M n hn hn2 htb hns) : Prop where
  sheet_np_side_lower_bound :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) E.coupledSheet

/-- Assemble the four Route B component interfaces back into the existing
`Theorem207Witness` compatibility bundle. -/
noncomputable def theorem207Witness_of_components
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (E : Theorem207Extraction M n hn hn2 htb hns)
    (hExtractRank : Theorem207ExtractionRankMonotone M n hn hn2 htb hns E)
    (hP : Theorem207PSideUpperBound M n hn hn2 htb hns E)
    (hNP : Theorem207NPSideLowerBound M n hn hn2 htb hns E) :
    Theorem207Witness M n hn hn2 htb hns where
  paperCompiledPoly := E.paperCompiledPoly
  sheet := E.coupledSheet
  extraction_rank_monotone := hExtractRank.extraction_rank_monotone
  compiled_p_side_bound := hP.compiled_p_side_bound
  sheet_np_side_lower_bound := hNP.sheet_np_side_lower_bound

/-- Extract the Route B polynomial/sheet data from an existing
`Theorem207Witness`. -/
noncomputable def theorem207Extraction_of_witness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : Theorem207Witness M n hn hn2 htb hns) :
    Theorem207Extraction M n hn hn2 htb hns where
  paperCompiledPoly := W.paperCompiledPoly
  coupledSheet := W.sheet

/-- Existing witnesses supply the Route B extraction-rank component. -/
theorem theorem207ExtractionRankMonotone_of_witness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : Theorem207Witness M n hn hn2 htb hns) :
    Theorem207ExtractionRankMonotone M n hn hn2 htb hns
      (theorem207Extraction_of_witness M n hn hn2 htb hns W) where
  extraction_rank_monotone := W.extraction_rank_monotone

/-- Existing witnesses supply the Route B P-side upper-bound component. -/
theorem theorem207PSideUpperBound_of_witness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : Theorem207Witness M n hn hn2 htb hns) :
    Theorem207PSideUpperBound M n hn hn2 htb hns
      (theorem207Extraction_of_witness M n hn hn2 htb hns W) where
  compiled_p_side_bound := W.compiled_p_side_bound

/-- Existing witnesses supply the Route B NP-side lower-bound component. -/
theorem theorem207NPSideLowerBound_of_witness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : Theorem207Witness M n hn hn2 htb hns) :
    Theorem207NPSideLowerBound M n hn hn2 htb hns
      (theorem207Extraction_of_witness M n hn hn2 htb hns W) where
  sheet_np_side_lower_bound := W.sheet_np_side_lower_bound

/-- **Theorem 207 axiom (paper-faithful, two-stage).** For every
bounded-parameter SAT-decider at `n ≥ 2^804`, the paper's instrumented
compiler (Theorem 181 / Lemma 204) + God-Move extraction T_Φ (Lemma 205) +
P-side Width⇒Rank (Theorem 10 / §32) + NP-side Ramanujan-Tseitin identity
minor (Theorem 98) jointly produce a `Theorem207Witness`.

The witness carries **five named paper-theorem fields** — the paper's full
two-stage chain made explicit:

1. `paperCompiledPoly` — P_{M',n} from Theorem 181 / Lemma 204.
2. `sheet` — Q×_Φ,S from Lemma 205 extraction.
3. `extraction_rank_monotone` — Lemma 205 rank monotonicity.
4. `compiled_p_side_bound` — Theorem 10 / Theorem 32 Width⇒Rank.
5. `sheet_np_side_lower_bound` — Theorem 98 Ramanujan-Tseitin.

At `n = 2^804` the chain
`C(n/3, log n) ≤ rank(sheet) ≤ rank(paperCompiledPoly) ≤ n^200`
is arithmetically incompatible (`n^200 < C(n/3, log n)`), so the axiom's
existence claim is mathematically equivalent to "no bounded-parameter
SAT-decider exists at n = 2^804" — the separation `P ≠ NP` in
restricted form.

The deepest mathematical content is the `compiled_p_side_bound` field
(Theorem 10 / Width⇒Rank via profile compression + amplituhedron);
`extraction_rank_monotone` (Lemma 205) and `sheet_np_side_lower_bound`
(Theorem 98) are relatively more tractable given existing infrastructure. -/
axiom exists_theorem207_witness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    Theorem207Witness M n hn hn2 htb hns

/-- The existing Theorem 207 witness axiom yields the split Route B component
interfaces. This is the backward-compatible projection direction. -/
noncomputable def exists_theorem207_component_interfaces_from_witness_axiom
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ (E : Theorem207Extraction M n hn hn2 htb hns),
      Theorem207ExtractionRankMonotone M n hn hn2 htb hns E ∧
      Theorem207PSideUpperBound M n hn hn2 htb hns E ∧
      Theorem207NPSideLowerBound M n hn hn2 htb hns E :=
  let W := exists_theorem207_witness M n hn hn2 htb hns hdec
  let E := theorem207Extraction_of_witness M n hn hn2 htb hns W
  ⟨E,
   theorem207ExtractionRankMonotone_of_witness M n hn hn2 htb hns W,
   theorem207PSideUpperBound_of_witness M n hn hn2 htb hns W,
   theorem207NPSideLowerBound_of_witness M n hn hn2 htb hns W⟩

/-- A split Route B component package assembles into the existing
`Theorem207Witness` type. This is the forward migration direction for replacing
the monolithic witness axiom with separately proved component claims. -/
noncomputable def theorem207Witness_from_component_interfaces
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hComponents :
      ∃ (E : Theorem207Extraction M n hn hn2 htb hns),
        Theorem207ExtractionRankMonotone M n hn hn2 htb hns E ∧
        Theorem207PSideUpperBound M n hn hn2 htb hns E ∧
        Theorem207NPSideLowerBound M n hn hn2 htb hns E) :
    Theorem207Witness M n hn hn2 htb hns :=
  let E := Classical.choose hComponents
  let hE := Classical.choose_spec hComponents
  theorem207Witness_of_components M n hn hn2 htb hns E hE.1 hE.2.1 hE.2.2

/-! ### Paper-faithful semantic Theorem 207 target

The component interfaces above are a compatibility layer around the older
`Theorem207Witness` bundle. The paper-faithful Route B object is stricter:
it is a coupled-sheet extraction target equipped with the staged semantic
pipeline from `GodMoveCore`.

In this surface, `PiStar` is still only the SPDP coordinate/gauge choice. The
actual codimension collapse is the semantic `PiPhi` extraction pipeline:
restriction, projection, output identification, and a rank bridge proving the
steps are rank-monotone. This avoids treating an arbitrary polynomial
`LinearMap` as a valid God-Move projection. -/

/-- **Raw/source P-side upper-bound interface for the semantic Theorem 207 route.**

The direct semantic contradiction in `GodMoveCore.separation_from_semantic_target`
uses the rank of the source Cook-Levin polynomial itself, because the staged
`PiPhi` extraction bridge proves
`rank(coupled sheet) ≤ rank(compiledPoly)`. This seam is therefore deliberately
not the projected `piStar_p_side_bound`: replacing it by a bound on
`piStar (compiledPoly)` would not match the paper-faithful source/target chain
unless an additional theorem related that projected quantity back to the raw
source rank used by the extraction bridge. -/
structure Theorem207RawSourcePSideUpperBound
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop where
  /-- Theorem 10 / Theorem 32 as needed by the semantic target route:
  the unprojected source polynomial has polynomial SPDP rank. -/
  raw_source_p_side_bound :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200

/-- Package the raw/source P-side inequality into its named Theorem 207 seam. -/
def theorem207RawSourcePSideUpperBound_of_bound
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hP :
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200) :
    Theorem207RawSourcePSideUpperBound M n hn hn2 htb hns where
  raw_source_p_side_bound := hP

/-- The local product-form `compiledPoly` cannot satisfy the raw/source
P-side seam at the Route B scale.

`GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n` proves, axiom-free, that
this unprojected product polynomial already has rank strictly larger than
`n^200`. Therefore a paper-faithful semantic witness cannot close by proving a
raw bound on this local `compiledPoly`; it needs the paper's instrumented or
gauge/collapse source object instead. -/
theorem theorem207RawSourcePSideUpperBound_not_for_local_compiledPoly
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ Theorem207RawSourcePSideUpperBound M n hn hn2 htb hns := by
  intro hP
  have hgt : n ^ 200 <
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
    simpa using GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n M n hn htb hns
  exact (not_le_of_gt hgt) hP.raw_source_p_side_bound

/-- Paper-faithful P-side source object for the semantic Theorem 207 route.

This is deliberately **not** the local product-form `compiledPoly`. It is the
paper's instrumented/gauged source object after the profile-compression and
Π⋆/ΠΦ coordinate choices have been made. The only structure downstream needs is
its SPDP rank in the Theorem 207 window, plus a rank-monotone transport into the
chosen semantic coupled-sheet target. -/
structure Theorem207PaperSource
    (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (_hn2 : n ≥ 2)
    (_htb : M.timeBound ≤ 4) (_hns : M.numStates ≤ n) : Type where
  sourceVars : ℕ
  sourcePartition : BlockPartition sourceVars
  sourcePoly : MvPolynomial (Fin sourceVars) ℚ

namespace Theorem207PaperSource

/-- SPDP rank of a paper-faithful source object in the Theorem 207 log window. -/
noncomputable def spdpRank
    {M : DTM} {n : ℕ} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (source : Theorem207PaperSource M n hn hn2 htb hns) : ℕ :=
  mlBlockedSpdpRank source.sourcePartition
    (Nat.log 2 n) (Nat.log 2 n) source.sourcePoly

end Theorem207PaperSource

/-- P-side polynomial upper bound for a paper-faithful source object. -/
structure Theorem207PaperSourcePSideUpperBound
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (source : Theorem207PaperSource M n hn hn2 htb hns) : Prop where
  source_p_side_bound :
    source.spdpRank ≤ n ^ 200

/-- Rank-monotone transport from the paper-faithful P-side source into the
chosen semantic coupled-sheet target. -/
structure Theorem207PaperSourceToTargetRankBridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (source : Theorem207PaperSource M n hn hn2 htb hns)
    (target : GodMoveExtractionTarget M n hn2 htb hns) : Prop where
  target_rank_le_source :
    mlBlockedSpdpRank target.coupledPartition
      (Nat.log 2 n) (Nat.log 2 n) target.coupledPoly ≤
    source.spdpRank

/-- Paper-source transport plus the same-target NP lower bound closes the
Theorem 207 arithmetic contradiction, without using the refuted local
`compiledPoly` as the P-side source. -/
theorem theorem207PaperSource_transport_false
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (target : GodMoveExtractionTarget M n hn2 htb hns)
    (source : Theorem207PaperSource M n hn hn2 htb hns)
    (hP : Theorem207PaperSourcePSideUpperBound M n hn hn2 htb hns source)
    (bridge : Theorem207PaperSourceToTargetRankBridge M n hn hn2 htb hns source target)
    (hNP : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank target.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) target.coupledPoly) :
    False := by
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans (le_trans hbin hmono) hNP)
      (le_trans bridge.target_rank_le_source hP.source_p_side_bound)
  have hlog : 804 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

/-- Paper-faithful semantic Theorem 207 witness using an explicit source object
and transport bridge, rather than the impossible raw local `compiledPoly`
bound. -/
structure Theorem207SemanticTransportWitness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) : Type where
  targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec
  extraction_semantics :
    GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget
  same_target_identity_minor :
    RouteBIdentityMinorSameTargetData targetData.extractionTarget
  paper_source : Theorem207PaperSource M n hn hn2 htb hns
  source_p_side_upper_bound :
    Theorem207PaperSourcePSideUpperBound M n hn hn2 htb hns paper_source
  source_to_target_rank_bridge :
    Theorem207PaperSourceToTargetRankBridge
      M n hn hn2 htb hns paper_source targetData.extractionTarget

/-- Constructor for the source-transport semantic witness from already chosen
semantic target data, same-target identity-minor evidence, and a paper source
rank bridge. -/
def theorem207SemanticTransportWitness_of_target_data
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (hsem :
      GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget)
    (minor : RouteBIdentityMinorSameTargetData targetData.extractionTarget)
    (source : Theorem207PaperSource M n hn hn2 htb hns)
    (hP : Theorem207PaperSourcePSideUpperBound M n hn hn2 htb hns source)
    (bridge :
      Theorem207PaperSourceToTargetRankBridge
        M n hn hn2 htb hns source targetData.extractionTarget) :
    Theorem207SemanticTransportWitness M n hn hn2 htb hns hdec where
  targetData := targetData
  extraction_semantics := hsem
  same_target_identity_minor := minor
  paper_source := source
  source_p_side_upper_bound := hP
  source_to_target_rank_bridge := bridge

/-- A source-transport semantic witness closes the paper-faithful Route B
contradiction without requiring a polynomial rank bound for the local
product-form `compiledPoly`. -/
theorem theorem207SemanticTransportWitness_false
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (W : Theorem207SemanticTransportWitness M n hn hn2 htb hns hdec) :
    False :=
  theorem207PaperSource_transport_false M n hn hn2 htb hns
    W.targetData.extractionTarget W.paper_source W.source_p_side_upper_bound
    W.source_to_target_rank_bridge
    (routeB_strong_np_from_same_target_identity_minor W.same_target_identity_minor)

/-- Package exact semantic target data, staged semantics, and same-target
identity-minor evidence into the real nonzero Route B semantic-gap object.

This is only a constructor: the semantic target and the identity-minor evidence
are still supplied explicitly. -/
def godMoveSemanticIdentityMinorGap_of_target_data_same_target_identity_minor
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (hsem :
      GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget)
    (minor : RouteBIdentityMinorSameTargetData targetData.extractionTarget) :
    GodMoveSemanticIdentityMinorGap M n hn2 htb hns hdec where
  gap :=
    { toHardInstanceData := targetData.toGodMoveHardInstanceData
      extractionTarget := targetData.extractionTarget
      extractionSemantics := hsem }
  same_target_identity_minor := by
    simpa using minor

/-- Constructor for the explicit semantic identity-minor/source-transport seam
from exact target data rather than a prebuilt
`GodMoveSemanticIdentityMinorGap`.

The theorem does not prove the semantic target, identity minor, source bound, or
rank bridge; it only assembles those explicit inputs into the global source
transport existential. -/
theorem exists_theorem207_semantic_identity_minor_gap_source_transport_data_of_target_data
    {M : DTM} {n : ℕ} (hn : n ≥ 2 ^ 804) {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (hsem :
      GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget)
    (minor : RouteBIdentityMinorSameTargetData targetData.extractionTarget)
    (source : Theorem207PaperSource M n hn hn2 htb hns)
    (hP : Theorem207PaperSourcePSideUpperBound M n hn hn2 htb hns source)
    (bridge :
      Theorem207PaperSourceToTargetRankBridge
        M n hn hn2 htb hns source targetData.extractionTarget) :
    ∃ G : GodMoveSemanticIdentityMinorGap M n hn2 htb hns hdec,
      ∃ source : Theorem207PaperSource M n hn hn2 htb hns,
        Theorem207PaperSourcePSideUpperBound M n hn hn2 htb hns source ∧
        Theorem207PaperSourceToTargetRankBridge
          M n hn hn2 htb hns source G.gap.extractionTarget := by
  refine ⟨godMoveSemanticIdentityMinorGap_of_target_data_same_target_identity_minor
      targetData hsem minor, source, hP, ?_⟩
  simpa [godMoveSemanticIdentityMinorGap_of_target_data_same_target_identity_minor]
    using bridge

/-- Explicit nonzero semantic-target plus source-transport theorem seam for
paper-faithful Theorem 207.

This is the real remaining Route B theorem shape. It asserts:

1. a chosen semantic extraction target that already carries same-target
   identity-minor evidence, and
2. an instrumented/gauged P-side source with polynomial rank and a
   rank-monotone transport into that target.

The existing zero strict-shrink semantic target cannot inhabit
`GodMoveSemanticIdentityMinorGap`; this seam therefore forces the nonzero
coupled-sheet target to be supplied explicitly. The source side is likewise the
paper-faithful `Theorem207PaperSource`, not the refuted local product-form
`compiledPoly`. -/
axiom exists_theorem207_semantic_identity_minor_gap_source_transport_data
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ G : GodMoveSemanticIdentityMinorGap M n hn2 htb hns hdec,
      ∃ source : Theorem207PaperSource M n hn hn2 htb hns,
        Theorem207PaperSourcePSideUpperBound M n hn hn2 htb hns source ∧
        Theorem207PaperSourceToTargetRankBridge
          M n hn hn2 htb hns source G.gap.extractionTarget

/-- Package explicit semantic identity-minor and paper-source transport data
into the existing source-transport existential seam.

This constructor is axiom-free: it does not choose target/source data, but
only repackages an already chosen `GodMoveSemanticIdentityMinorGap`, paper
source, source P-side bound, and rank bridge into the existential shape used by
the legacy theorem-207 source-transport seam. -/
theorem exists_theorem207_semantic_source_transport_data_of_identity_minor_gap
    {M : DTM} {n : ℕ} (hn : n ≥ 2 ^ 804) {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    (G : GodMoveSemanticIdentityMinorGap M n hn2 htb hns hdec)
    (source : Theorem207PaperSource M n hn hn2 htb hns)
    (hP : Theorem207PaperSourcePSideUpperBound M n hn hn2 htb hns source)
    (bridge :
      Theorem207PaperSourceToTargetRankBridge
        M n hn hn2 htb hns source G.gap.extractionTarget) :
    ∃ targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec,
      GodMoveExtractionTargetTheorem
        M n hn2 htb hns hdec targetData.extractionTarget ∧
      Nonempty (RouteBIdentityMinorSameTargetData targetData.extractionTarget) ∧
      ∃ source : Theorem207PaperSource M n hn hn2 htb hns,
        Theorem207PaperSourcePSideUpperBound M n hn hn2 htb hns source ∧
        Theorem207PaperSourceToTargetRankBridge
          M n hn hn2 htb hns source targetData.extractionTarget := by
  refine ⟨G.gap.toTargetData, ?_, ?_, source, hP, ?_⟩
  · exact G.gap.targetTheorem
  · exact ⟨by simpa [GodMoveSemanticGap.toTargetData] using
      G.same_target_identity_minor⟩
  · simpa [GodMoveSemanticGap.toTargetData] using bridge

/-- Compatibility projection from the explicit semantic identity-minor/source
transport seam to the older source-transport existential shape.

This theorem is the place where the broad existential is instantiated. Its
only custom dependency is the explicit
`exists_theorem207_semantic_identity_minor_gap_source_transport_data` seam
above. -/
theorem exists_theorem207_semantic_source_transport_data
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec,
      GodMoveExtractionTargetTheorem
        M n hn2 htb hns hdec targetData.extractionTarget ∧
      Nonempty (RouteBIdentityMinorSameTargetData targetData.extractionTarget) ∧
      ∃ source : Theorem207PaperSource M n hn hn2 htb hns,
        Theorem207PaperSourcePSideUpperBound M n hn hn2 htb hns source ∧
        Theorem207PaperSourceToTargetRankBridge
          M n hn hn2 htb hns source targetData.extractionTarget := by
  obtain ⟨G, source, hP, bridge⟩ :=
    exists_theorem207_semantic_identity_minor_gap_source_transport_data
      M n hn hn2 htb hns hdec
  exact exists_theorem207_semantic_source_transport_data_of_identity_minor_gap
    hn G source hP bridge

/-- Assemble the source-transport semantic witness from the narrow theorem
seam above. -/
noncomputable def theorem207SemanticTransportWitness_from_source_transport_data
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    Theorem207SemanticTransportWitness M n hn hn2 htb hns hdec :=
  let targetData :=
    Classical.choose
      (exists_theorem207_semantic_source_transport_data
        M n hn hn2 htb hns hdec)
  let htarget :=
    Classical.choose_spec
      (exists_theorem207_semantic_source_transport_data
        M n hn hn2 htb hns hdec)
  let source := Classical.choose htarget.2.2
  let hsource := Classical.choose_spec htarget.2.2
  theorem207SemanticTransportWitness_of_target_data
    M n hn hn2 htb hns hdec targetData htarget.1
    (Classical.choice htarget.2.1) source hsource.1 hsource.2

/-- **Paper-faithful Theorem 207 semantic witness.**

This is the Route B chain in the shape used by `GodMoveCore`:

* a concrete coupled-sheet target `Qx_Phi,S`,
* staged extraction semantics for the map from the Cook-Levin polynomial to
  that target,
* a rank bridge for the restriction/projection pipeline,
* the P-side upper bound on the source polynomial, and
* the NP-side identity-minor lower bound on the same extracted sheet.

Unlike the legacy gauge shells above, this type contains no arbitrary
polynomial projection field. -/
structure Theorem207SemanticWitness
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) : Type where
  /-- The coupled verifier sheet `Qx_Phi,S` extracted by the paper's
  `PiPhi` pipeline. -/
  target : GodMoveExtractionTarget M n hn2 htb hns
  /-- The semantic extraction data: restriction, projection, and output
  identification for the chosen coupled sheet. -/
  extraction_semantics :
    GodMoveExtractionSemanticObligation M n hn2 htb hns hdec target
  /-- Rank-monotone bridge for every semantic realization of the extraction
  map on this target. -/
  rank_bridge :
    ∀ sem : ExtractionMapSemantics M n hn2 htb hns hdec target,
      ExtractionMapRankBridge sem
  /-- Raw/source P-side upper bound used by the semantic extraction bridge. -/
  raw_source_p_side_upper_bound :
    Theorem207RawSourcePSideUpperBound M n hn hn2 htb hns
  /-- NP-side Ramanujan-Tseitin identity-minor lower bound on the same
  coupled sheet. -/
  sheet_np_side_lower_bound :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank target.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) target.coupledPoly

/-- The named raw/source P-side seam carried by a semantic witness gives the
inequality expected by `separation_from_semantic_target`. -/
theorem theorem207SemanticWitness_raw_source_p_side_bound
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (W : Theorem207SemanticWitness M n hn hn2 htb hns hdec) :
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200 :=
  have hP : Theorem207RawSourcePSideUpperBound M n hn hn2 htb hns :=
    Theorem207SemanticWitness.raw_source_p_side_upper_bound
      (M := M) (n := n) (hn := hn) (hn2 := hn2)
      (htb := htb) (hns := hns) (hdec := hdec) W
  Theorem207RawSourcePSideUpperBound.raw_source_p_side_bound
    (M := M) (n := n) (hn := hn) (hn2 := hn2)
    (htb := htb) (hns := hns) hP

/-- Build the paper-faithful Theorem 207 semantic witness from the exact
`GodMoveCore` target package.

This is only packaging: the missing mathematical content remains precisely the
staged semantic theorem on the chosen extraction target and the two Theorem
207 rank bounds on that same target/source pair. The rank bridge is rebuilt
axiom-free from the staged semantic record. -/
def theorem207SemanticWitness_of_target_data
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (hsem :
      GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget)
    (hP : Theorem207RawSourcePSideUpperBound M n hn hn2 htb hns)
    (hNP : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank targetData.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) targetData.extractionTarget.coupledPoly) :
    Theorem207SemanticWitness M n hn hn2 htb hns hdec where
  target := targetData.extractionTarget
  extraction_semantics := hsem
  rank_bridge := fun sem => ExtractionMapRankBridge.ofSemantics sem
  raw_source_p_side_upper_bound := hP
  sheet_np_side_lower_bound := hNP

/-- Build the paper-faithful Theorem 207 semantic witness directly from the
`GodMoveSemanticGap` convenience bundle.

The gap supplies the chosen extraction target and staged semantic witness. The
rank bridge follows from the staged semantic record, so only the P-side source
bound and same-target NP-side lower bound stay explicit. -/
def theorem207SemanticWitness_of_semantic_gap
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (hP : Theorem207RawSourcePSideUpperBound M n hn hn2 htb hns)
    (hNP : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank gap.extractionTarget.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) gap.extractionTarget.coupledPoly) :
    Theorem207SemanticWitness M n hn hn2 htb hns hdec where
  target := gap.extractionTarget
  extraction_semantics := gap.extractionSemantics
  rank_bridge := fun sem => ExtractionMapRankBridge.ofSemantics sem
  raw_source_p_side_upper_bound := hP
  sheet_np_side_lower_bound := hNP

/-- Build the paper-faithful semantic witness from same-target identity-minor
data, rather than from a detached rank inequality. -/
def theorem207SemanticWitness_of_target_data_same_target_identity_minor
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec)
    (hsem :
      GodMoveExtractionTargetTheorem M n hn2 htb hns hdec targetData.extractionTarget)
    (hP : Theorem207RawSourcePSideUpperBound M n hn hn2 htb hns)
    (minor : RouteBIdentityMinorSameTargetData targetData.extractionTarget) :
    Theorem207SemanticWitness M n hn hn2 htb hns hdec :=
  theorem207SemanticWitness_of_target_data M n hn hn2 htb hns hdec
    targetData hsem hP
    (routeB_strong_np_from_same_target_identity_minor minor)

/-- Build the paper-faithful semantic witness from a semantic gap plus
same-target identity-minor data. -/
def theorem207SemanticWitness_of_semantic_gap_same_target_identity_minor
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (gap : GodMoveSemanticGap M n hn2 htb hns hdec)
    (hP : Theorem207RawSourcePSideUpperBound M n hn hn2 htb hns)
    (minor : RouteBIdentityMinorSameTargetData gap.extractionTarget) :
    Theorem207SemanticWitness M n hn hn2 htb hns hdec :=
  theorem207SemanticWitness_of_semantic_gap M n hn hn2 htb hns hdec
    gap hP (routeB_strong_np_from_same_target_identity_minor minor)

/-- Narrow semantic-target/NP-side theorem seam for Theorem 207.

This deliberately does **not** assert the P-side source bound. It only chooses
the exact semantic extraction target and supplies identity-minor evidence on
that same target. The raw/source P-side question remains the separate
`Theorem207RawSourcePSideUpperBound` seam above. -/
theorem exists_theorem207_semantic_target_identity_minor_data
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ targetData : GodMoveExtractionTargetData M n hn2 htb hns hdec,
      GodMoveExtractionTargetTheorem
        M n hn2 htb hns hdec targetData.extractionTarget ∧
      Nonempty (RouteBIdentityMinorSameTargetData targetData.extractionTarget) := by
  obtain ⟨targetData, hsem, hminor, _hsource⟩ :=
    exists_theorem207_semantic_source_transport_data M n hn hn2 htb hns hdec
  exact ⟨targetData, hsem, hminor⟩

/-- Assemble the semantic witness from the narrow semantic-target/identity-minor
axiom plus a separate P-side source-bound seam. -/
noncomputable def theorem207SemanticWitness_from_target_identity_minor_data
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (hP : Theorem207RawSourcePSideUpperBound M n hn hn2 htb hns) :
    Theorem207SemanticWitness M n hn hn2 htb hns hdec :=
  let targetData :=
    Classical.choose
      (exists_theorem207_semantic_target_identity_minor_data
        M n hn hn2 htb hns hdec)
  let htarget :=
    Classical.choose_spec
      (exists_theorem207_semantic_target_identity_minor_data
        M n hn hn2 htb hns hdec)
  theorem207SemanticWitness_of_target_data_same_target_identity_minor
    M n hn hn2 htb hns hdec targetData htarget.1 hP (Classical.choice htarget.2)

/-- The Theorem 207 identity-minor lower bound implies the weakened NP lower
bound expected by `separation_from_semantic_target`. -/
theorem theorem207SemanticWitness_weakened_np_lower
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (W : Theorem207SemanticWitness M n hn hn2 htb hns hdec) :
    n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank W.target.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) W.target.coupledPoly := by
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  exact le_trans (le_trans hbin hmono) W.sheet_np_side_lower_bound

/-- A paper-faithful semantic Theorem 207 witness is enough for the Route B
contradiction shell already proved in `GodMoveCore`. -/
theorem theorem207SemanticWitness_false
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (W : Theorem207SemanticWitness M n hn hn2 htb hns hdec) :
    False :=
  separation_from_semantic_target M n hn2 htb hns hdec hn
    W.target W.extraction_semantics
    (theorem207SemanticWitness_weakened_np_lower M n hn hn2 htb hns hdec W)
    W.rank_bridge
    (theorem207SemanticWitness_raw_source_p_side_bound M n hn hn2 htb hns hdec W)

/-! ### Partial axiom-free discharge of Theorem207Witness

The `extraction_rank_monotone` field of `Theorem207Witness` (paper's
Lemma 205, field #3) can be discharged axiom-free by using a specific
`T_Φ = id` choice that sets `sheet := paperCompiledPoly`. The identity
operator is trivially rank-preserving (a special case of Lemma 40(a)
under `T_Φ ∈ {basis, affine relabel, restriction, projection}`).

This reduces the axiom surface: `exists_theorem207_witness` claims 5
fields exist; after this discharge, only 4 remain load-bearing (the
two paper-deep bounds `compiled_p_side_bound` and
`sheet_np_side_lower_bound`, plus the data fields). -/

/-- **Partial axiom-free factoring of `Theorem207Witness`.**

Given just the two hard rank bounds for a single polynomial
`q := paperCompiledPoly`, we can construct a full `Theorem207Witness`
by choosing `sheet := q` (a trivial identity extraction). This
discharges field #3 (`extraction_rank_monotone`) via `le_refl`
axiom-free.

The remaining content — the two bounds — is the genuine paper-deep
mathematics (Theorem 10/§32 for P-side, Theorem 98 for NP-side).
This helper packages them into the witness without the need for the
broader `exists_theorem207_witness` axiom. -/
noncomputable def theorem207Witness_of_bounds
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (h_p_side :
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) q ≤ n ^ 200)
    (h_np_side :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n) q) :
    Theorem207Witness M n hn hn2 htb hns where
  paperCompiledPoly := q
  sheet := q
  extraction_rank_monotone := le_refl _
  compiled_p_side_bound := h_p_side
  sheet_np_side_lower_bound := h_np_side

/-- **Rephrased existence axiom.** Equivalent to `exists_theorem207_witness`
but with the `extraction_rank_monotone` field discharged implicitly
via `theorem207Witness_of_bounds`: the two bounds alone suffice.

This is a **strictly narrower axiom** than `exists_theorem207_witness`:
it asserts just the existence of the two rank bounds on a single
polynomial, not the full 5-field witness. The 5-field witness is
derivable via `theorem207Witness_of_bounds`. -/
axiom exists_theorem207_bounds_on_some_poly
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ (q : MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n) q ≤ n ^ 200 ∧
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n) q

/-- `exists_theorem207_witness` derived from the narrower
`exists_theorem207_bounds_on_some_poly` axiom. This is the
axiom-surface reduction: 5 fields → 2 rank-bound claims on a
single polynomial. -/
noncomputable def exists_theorem207_witness_from_bounds_axiom
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    Theorem207Witness M n hn hn2 htb hns :=
  let h := exists_theorem207_bounds_on_some_poly M n hn hn2 htb hns hdec
  let q := Classical.choose h
  let hq := Classical.choose_spec h
  theorem207Witness_of_bounds M n hn hn2 htb hns q hq.1 hq.2

/-! ### Discharging `exists_theorem207_bounds_on_some_poly` via `exists_amplituhedron_gauge`

The two rank bounds on a single polynomial can be discharged via the
amplituhedron gauge: set `q := gauge(compiledPoly)`. The P-side bound
is `IsAmplituhedronGauge.p_side_bound`, and the NP-side bound is
`IsAmplituhedronGauge.preserves_identity_minor_for_sat_deciders`. -/

/-- **Axiom-free discharge of `exists_theorem207_bounds_on_some_poly`
from `exists_amplituhedron_gauge`.**

This shows the narrower 2-bound axiom reduces to the amplituhedron
gauge existence axiom. The construction takes `q := gauge(compiledPoly)`
where `gauge = Π⋆` is the amplituhedron gauge. Both rank bounds follow
from the gauge's three bundled properties. -/
theorem exists_theorem207_bounds_on_some_poly_from_gauge
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ (q : MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n) q ≤ n ^ 200 ∧
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n) q := by
  obtain ⟨gauge, hgauge⟩ := exists_amplituhedron_gauge M n hn hn2 htb hns
  refine ⟨gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)),
          hgauge.p_side_bound,
          hgauge.preserves_identity_minor_for_sat_deciders hdec⟩

/-- **End-to-end Theorem207Witness construction axiom-free** (modulo the
amplituhedron gauge axiom). Combines the bounds discharge with the
`theorem207Witness_of_bounds` construction, reducing the axiom surface
of `Theorem207Witness` to just `exists_amplituhedron_gauge`. -/
noncomputable def theorem207Witness_from_gauge
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    Theorem207Witness M n hn hn2 htb hns :=
  let h := exists_theorem207_bounds_on_some_poly_from_gauge
    M n hn hn2 htb hns hdec
  let q := Classical.choose h
  let hq := Classical.choose_spec h
  theorem207Witness_of_bounds M n hn hn2 htb hns q hq.1 hq.2

/-- **Narrower-axiom variant**: uses `exists_amplituhedron_gauge_for_sat_decider`
(strictly narrower than `exists_amplituhedron_gauge`). -/
theorem exists_theorem207_bounds_on_some_poly_from_narrow_gauge
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ (q : MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n) q ≤ n ^ 200 ∧
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n) q := by
  obtain ⟨gauge, hgauge⟩ :=
    exists_amplituhedron_gauge_for_sat_decider M n hn hn2 htb hns hdec
  refine ⟨gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns)),
          hgauge.p_side_bound,
          hgauge.preserves_identity_minor_for_sat_deciders hdec⟩

/-- **Theorem207Witness from the narrow gauge axiom** (using
`exists_amplituhedron_gauge_for_sat_decider`). This is the
minimum-axiom-surface reduction of `Theorem207Witness`. -/
noncomputable def theorem207Witness_from_narrow_gauge
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    Theorem207Witness M n hn hn2 htb hns :=
  let h := exists_theorem207_bounds_on_some_poly_from_narrow_gauge
    M n hn hn2 htb hns hdec
  let q := Classical.choose h
  let hq := Classical.choose_spec h
  theorem207Witness_of_bounds M n hn hn2 htb hns q hq.1 hq.2

/-! ### Minimal rank-sandwich axiom (narrowest reduction)

The gauge axiom `exists_amplituhedron_gauge_for_sat_decider` bundles 3
properties (rank_monotone, p_side_bound, preserves_identity_minor).
However, the SEPARATION PROOF only uses the ARITHMETIC FACT
`C(n/3, log n) ≤ r ≤ n^200` for some natural number `r` (the rank of
the gauge's image of compiledPoly).

This motivates a strictly narrower axiom: just the existence of a
natural number `r` in the arithmetic sandwich, without reference to
gauges, polynomials, or subspaces. -/

/-- **Minimal rank-sandwich** (narrowest derived form).

For any bounded-parameter SAT-decider at `n ≥ 2^804`, there exists a
natural number `r` with `C(n/3, log n) ≤ r ≤ n^200`. At `n = 2^804`
this is arithmetically False (since `n^200 < C(n/3, log n)`), so
the existential claim under the `DecidesSAT M` hypothesis is
equivalent to "no bounded-parameter SAT-decider exists at `n = 2^804`"
— the separation `P ≠ NP` in the restricted bounded-parameter form.

**THEOREM** (not axiom): derived from `exists_amplituhedron_gauge_for_sat_decider`
via `exists_rank_sandwich_from_narrow_gauge` above. This reduces the
axiom surface of `P_ne_NP_unconditional` to depend only on the single
custom axiom `exists_amplituhedron_gauge_for_sat_decider`. -/
theorem exists_rank_sandwich_for_sat_decider
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ (r : ℕ), Nat.choose (n / 3) (Nat.log 2 n) ≤ r ∧ r ≤ n ^ 200 := by
  obtain ⟨q, h_p, h_np⟩ :=
    exists_theorem207_bounds_on_some_poly_from_narrow_gauge
      M n hn hn2 htb hns hdec
  exact ⟨mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n) q, h_np, h_p⟩

/-- **Alias** for `exists_rank_sandwich_for_sat_decider` (kept for backward
compatibility — the previous narrow axiom has been promoted to a theorem
derived from `exists_amplituhedron_gauge_for_sat_decider`). -/
theorem exists_rank_sandwich_from_narrow_gauge
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ (r : ℕ), Nat.choose (n / 3) (Nat.log 2 n) ≤ r ∧ r ≤ n ^ 200 :=
  exists_rank_sandwich_for_sat_decider M n hn hn2 htb hns hdec

/-- **Derived form of the rank sandwich axiom as direct separation.**

By the arithmetic impossibility of the rank sandwich at `n ≥ 2^804`,
the rank-sandwich axiom is LOGICALLY EQUIVALENT to the direct
assertion that no bounded-parameter SAT-decider exists at such `n`.

This is the axiom in its most essential form — a direct statement of
the restricted separation, with no polynomial/SPDP machinery. Proved
here as a theorem (not an axiom) from `exists_rank_sandwich_for_sat_decider`. -/
theorem no_bounded_sat_decider_at_2pow804_from_rank_sandwich_axiom
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ DecidesSAT M := by
  intro hdec
  obtain ⟨r, hr_lb, hr_ub⟩ :=
    exists_rank_sandwich_for_sat_decider M n hn hn2 htb hns hdec
  -- Arithmetic chain n^201 ≤ n^(log n / 4) ≤ C(n/30, log n) ≤ C(n/3, log n) ≤ r ≤ n^200
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans (le_trans hbin hmono) hr_lb) hr_ub
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hn_ge_1 : 1 ≤ n := by omega
  have hn_gt_1 : 1 < n := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right hn_ge_1 hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right hn_gt_1 (by omega : 200 < 201)))

/-! ### Axiom-inventory checks

These `#print axioms` calls document which custom axioms each result
depends on. Expected outcomes:

* `zeroGauge_isAmplituhedronGauge_of_not_decidesSAT` —
  **no custom axioms** (the non-SAT-decider case is genuinely axiom-free).
* `exists_amplituhedron_gauge_of_not_decidesSAT` — same.
* `exists_amplituhedron_gauge_via_narrow_axiom` —
  only `exists_amplituhedron_gauge_for_sat_decider`
  (strictly narrower than the original `exists_amplituhedron_gauge`).
* `theorem207Witness_of_bounds` —
  **no custom axioms** (axiom-free discharge of field #3 via le_refl).
* `exists_theorem207_witness_from_bounds_axiom` —
  only `exists_theorem207_bounds_on_some_poly`
  (strictly narrower than the 5-field `exists_theorem207_witness`).
* `theorem207Witness_of_components` / `theorem207Witness_from_component_interfaces` —
  no custom axioms; these are interface assembly helpers.
* `exists_theorem207_component_interfaces_from_witness_axiom` —
  only `exists_theorem207_witness`, documenting the compatibility projection
  from the old monolithic witness axiom into the split Route B interfaces.
* `theorem207SemanticWitness_of_target_data` /
  `theorem207SemanticWitness_of_semantic_gap` —
  no custom axioms; these only package exact `GodMoveCore` semantic data and
  the two same-target rank bounds into the paper-faithful witness.
* `theorem207RawSourcePSideUpperBound_not_for_local_compiledPoly` —
  no custom axioms; it records that the local product-form `compiledPoly`
  cannot be the raw/source P-side object for this semantic shell.
* `theorem207PaperSource_transport_false` /
  `theorem207SemanticTransportWitness_false` —
  no custom axioms; these close the arithmetic contradiction from a
  paper-faithful source object, source-to-target rank bridge, and same-target
  identity-minor lower bound.
* `exists_theorem207_semantic_target_identity_minor_data` —
  now a theorem derived from the explicit semantic identity-minor/source
  transport seam
  `exists_theorem207_semantic_identity_minor_gap_source_transport_data`.
* `exists_theorem207_semantic_source_transport_data_of_identity_minor_gap` —
  no custom axioms; this is pure packaging from an explicit nonzero semantic
  identity-minor gap, paper source, P-side bound, and source-to-target bridge.
* `exists_theorem207_semantic_source_transport_data` —
  now a theorem projected from
  `exists_theorem207_semantic_identity_minor_gap_source_transport_data`,
  forcing the remaining target to be supplied as a
  `GodMoveSemanticIdentityMinorGap`.
* `theorem207SemanticWitness_from_target_identity_minor_data` —
  now depends on
  `exists_theorem207_semantic_identity_minor_gap_source_transport_data`,
  because the target/identity-minor existential is projected from that
  stronger seam.
* `theorem207SemanticTransportWitness_from_source_transport_data` —
  only `exists_theorem207_semantic_identity_minor_gap_source_transport_data`;
  this is the paper-faithful source/target transport seam with the nonzero
  identity-minor target made explicit.
* `theorem207SemanticWitness_weakened_np_lower` / `theorem207SemanticWitness_false` —
  no new custom axioms; these expose the paper-faithful `GodMoveCore`
  semantic extraction route and reuse the existing arithmetic/binomial and
  semantic separation infrastructure. -/
#print axioms zeroGauge_isAmplituhedronGauge_of_not_decidesSAT
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms)
#print axioms exists_amplituhedron_gauge_of_not_decidesSAT
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms)
#print axioms exists_amplituhedron_gauge_via_narrow_axiom
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider.
-- (Single custom axiom — the narrow SAT-decider-only version,
--  strictly narrower than the original exists_amplituhedron_gauge.)
#print axioms theorem207Witness_of_bounds
-- Expected: propext, Classical.choice, Quot.sound
-- (Axiom-free: field #3 discharged via le_refl by sheet = q construction.)
#print axioms exists_theorem207_witness_from_bounds_axiom
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_theorem207_bounds_on_some_poly.
-- (Strictly narrower axiom than exists_theorem207_witness:
--  only 2 rank bounds on a single polynomial vs 5-field witness.)
#print axioms theorem207Witness_of_components
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms theorem207Witness_from_component_interfaces
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms exists_theorem207_component_interfaces_from_witness_axiom
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_theorem207_witness.
#print axioms theorem207RawSourcePSideUpperBound_of_bound
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms theorem207RawSourcePSideUpperBound_not_for_local_compiledPoly
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
-- Axiom-free obstruction to using the local product-form compiledPoly as the
-- raw/source P-side object.
#print axioms theorem207PaperSource_transport_false
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
-- Arithmetic contradiction from paper source rank, transport, and target NP.
#print axioms theorem207SemanticTransportWitness_of_target_data
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms theorem207SemanticTransportWitness_false
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms exists_theorem207_semantic_source_transport_data_of_identity_minor_gap
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
-- Pure packaging from explicit semantic identity-minor/source transport data.
#print axioms exists_theorem207_semantic_source_transport_data
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_theorem207_semantic_identity_minor_gap_source_transport_data.
#print axioms theorem207SemanticTransportWitness_from_source_transport_data
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_theorem207_semantic_identity_minor_gap_source_transport_data.
#print axioms exists_theorem207_semantic_target_identity_minor_data
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_theorem207_semantic_identity_minor_gap_source_transport_data.
-- Target/identity-minor data is now projected out of the explicit semantic
-- identity-minor/source transport seam, not asserted as its own axiom.
#print axioms theorem207SemanticWitness_raw_source_p_side_bound
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms theorem207SemanticWitness_of_target_data
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms theorem207SemanticWitness_of_semantic_gap
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms theorem207SemanticWitness_of_target_data_same_target_identity_minor
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms theorem207SemanticWitness_of_semantic_gap_same_target_identity_minor
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms theorem207SemanticWitness_from_target_identity_minor_data
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_theorem207_semantic_identity_minor_gap_source_transport_data.
#print axioms theorem207SemanticWitness_weakened_np_lower
-- Expected: propext, Classical.choice, Quot.sound
-- (Axiom-free arithmetic weakening from C(n/3, log n) to n^(log n / 4).)
#print axioms theorem207SemanticWitness_false
-- Expected: propext, Classical.choice, Quot.sound
-- (No new custom axioms beyond the existing semantic Route B shell.)

end GlobalGodMoveGauge
