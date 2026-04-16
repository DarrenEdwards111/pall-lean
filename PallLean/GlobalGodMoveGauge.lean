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

/-! ### Axiom-inventory checks

These `#print axioms` calls document which custom axioms each result
depends on. Expected outcomes:

* `zeroGauge_isAmplituhedronGauge_of_not_decidesSAT` —
  **no custom axioms** (the non-SAT-decider case is genuinely axiom-free).
* `exists_amplituhedron_gauge_of_not_decidesSAT` — same.
* `exists_amplituhedron_gauge_via_narrow_axiom` —
  only `exists_amplituhedron_gauge_for_sat_decider`
  (strictly narrower than the original `exists_amplituhedron_gauge`). -/
#print axioms zeroGauge_isAmplituhedronGauge_of_not_decidesSAT
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms)
#print axioms exists_amplituhedron_gauge_of_not_decidesSAT
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms)
#print axioms exists_amplituhedron_gauge_via_narrow_axiom
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider.
-- (Single custom axiom — the narrow SAT-decider-only version,
--  strictly narrower than the original exists_amplituhedron_gauge.)

end GlobalGodMoveGauge
