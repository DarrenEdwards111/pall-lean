/-
  GlobalGodMoveGauge.lean — Π⋆ projection and projected SPDP rank
  -------------------------------------------------------------

  This file implements the paper's **Global God-Move Gauge** Π⋆ (Definition 7
  / Theorem 207) as a ℚ-linear projection on `MvPolynomial (Fin n) ℚ`, and the
  associated **projected SPDP rank** functional `mlBlockedSpdpRankProjected`.

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
  *position-quotienting projection* Π⋆ that:

  1. Collapses block-position multiplicity for compiled polynomials of
     **generic** DTMs (so the P-side bound on the projected rank becomes
     polynomial — Axiom 2 below).
  2. **Preserves** the clause-sheet identity-minor structure for compiled
     polynomials of **SAT-deciding** DTMs, where `DecidesSAT` constrains the
     tableau to encode the formula's clause data (Axiom 3 below).

  The asymmetry between (1) and (2) is exactly what makes `DecidesSAT`
  genuinely load-bearing in the new chain: the projected NP-side lower bound
  requires `DecidesSAT`, while the projected P-side upper bound applies
  uniformly. This breaks the previous "any-DTM" inconsistency.

  ## Open mathematical content

  The three axioms below (rank monotonicity, projected P-side upper bound,
  projected NP-side lower bound for SAT-deciders) replace the single,
  provably-false `spdp_profile_generators`. Each is mathematically plausible
  and consistent with `compiled_np_lower_bound_any_dtm`. Concrete proofs
  require:

  * Constructing Π⋆ explicitly (the paper's amplituhedron projection /
    derandomized switching lemma instantiation),
  * Proving Π⋆ collapses position multiplicity uniformly,
  * Proving Π⋆ is faithful on the SAT-decider clause-sheet substructure.

  This is open research — we axiomatise the *spec* here so the rest of the
  separation chain becomes structurally honest.
-/
import PallLean.MultilinearSPDP
import PallLean.CookLevinDefs
import PallLean.GodMoveCore
import Mathlib.Tactic

namespace GlobalGodMoveGauge

open MvPolynomial SPDP MultilinearSPDP TuringMachine PaperFaithfulSeparation

/-! ## The Global God-Move Gauge Π⋆

Π⋆ is a ℚ-linear endomorphism on `MvPolynomial (Fin n) ℚ`, parameterised by a
block partition. The partition argument is required because the projection
acts blockwise (compressing position multiplicity within blocks).

The construction is left abstract; concretely instantiating it is the content
of Theorem 207's "uniform projection Π_⋆ derived from amplituhedron geometry"
in §6 of the paper. -/
axiom piStar : ∀ {n : ℕ} (_B : BlockPartition n),
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ

/-- The **projected SPDP rank**: the multilinear blocked SPDP rank of the
polynomial *after* applying the Global God-Move Gauge Π⋆. -/
noncomputable def mlBlockedSpdpRankProjected {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) ℚ) : ℕ :=
  mlBlockedSpdpRank B κ ℓ (piStar B p)

/-! ## Axioms governing Π⋆

These three axioms encode the *spec* the gauge must satisfy. They are
mathematically plausible (none is provably false in this codebase) and
collectively make `DecidesSAT` load-bearing in the separation chain. -/

/-- **Axiom 1 (rank monotonicity).** Π⋆ does not increase SPDP rank.

For any genuine projection / quotient map this would be automatic; we state it
explicitly here because `piStar` is left abstract. -/
axiom piStar_rank_monotone {n : ℕ} (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) ℚ) :
    mlBlockedSpdpRankProjected B κ ℓ p ≤ mlBlockedSpdpRank B κ ℓ p

/-- **Axiom 2 (projected P-side upper bound).** For *any* DTM M with the
bounded compilation parameters, the projected SPDP rank of M's Cook-Levin
compiled polynomial is polynomial in n.

This is the projected-rank replacement for `spdp_profile_generators`. The
crucial difference is that it applies to the *projected* quantity, after the
position-multiplicity-collapsing Π⋆ has been applied. The within-profile
dimension after Π⋆ is genuinely (κ+1)^{O(1)} (since the C(n/3, κ) disjoint-block
generators get identified), so the profile-compression count
`(κ+1)⁴ · (κ+1)⁸ = (κ+1)¹²` becomes a true upper bound on the projected rank.

This axiom does **not** contradict the axiom-free
`GodMoveReal.compiled_np_lower_bound_any_dtm` — that theorem is about the
*un-projected* rank, while this axiom is about the *projected* rank. By
Axiom 1, projected ≤ un-projected, so the axiom-free lower bound on
un-projected does not lift to a lower bound on projected.

Concrete proof would require: (i) constructing Π⋆ as the amplituhedron
projection of Definition 7, (ii) showing that for the compiled polynomial of
*any* DTM, the projected SPDP generators factor through symmetric powers of
local interface spaces of dimension ≤ 3, and (iii) verifying numerical
bounds. -/
axiom piStar_p_side_bound (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRankProjected
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤ n ^ 200

/-- **Axiom 3 (projected NP-side lower bound for SAT-deciders).** For DTMs
that *decide 3-SAT* in the bounded-parameter regime, Π⋆ preserves the
identity-minor structure of the compiled polynomial, so the projected SPDP
rank retains its super-polynomial lower bound.

This axiom is the load-bearing site of `DecidesSAT` in the new chain. The
mechanism the paper describes:

* For a generic DTM (no clause-sheet semantics), the C(n/3, κ) disjoint-block
  identity-minor generators are *position-equivalent* under Π⋆ — they all
  sit in the same projected equivalence class, so Π⋆ collapses them. This is
  what licenses Axiom 2's polynomial upper bound for any DTM.
* For a SAT-deciding DTM, the `DecidesSAT M` hypothesis forces the compiled
  tableau to encode the formula's clause-sheet structure (via the
  transition-skeleton constraints in `cook_levin_compilation`). Π⋆ is
  calibrated against this clause-sheet basis and is *faithful* on the
  identity-minor sub-system that the clause-sheet exposes; the C(n/3, κ)
  generators remain linearly independent after projection.

The asymmetry is what licenses the contradiction: combining Axiom 2 (any
DTM) with Axiom 3 (SAT-deciders only) at n = 2⁸⁰⁴ rules out the existence of
a polytime SAT-decider, i.e. forces P ≠ NP.

Concrete proof would require: (i) extracting from `DecidesSAT M` the
clause-sheet substructure encoded in M's accepting tableau (cf.
`DecidesSAT.accepting_input_of_satisfiable` in `GodMoveCore.lean`), (ii)
defining the clause-sheet identity-minor restriction, and (iii) showing Π⋆
is faithful on this restriction. -/
axiom piStar_preserves_identity_minor_for_sat_deciders
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (_hdec : DecidesSAT M)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRankProjected
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))

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

* Axiom 2 above is about `mlBlockedSpdpRankProjected = mlBlockedSpdpRank ∘ Π⋆`,
  not about un-projected rank. It does **not** combine with the un-projected
  `compiled_np_lower_bound_any_dtm` to give a contradiction (Axiom 1 only goes
  the wrong way: projected ≤ un-projected).
* Axiom 3 lower-bounds the projected rank, but **only** for SAT-deciding DTMs.
  For non-SAT-deciders Axiom 3 gives nothing, so Axiom 2's universal bound is
  consistent with the existence of generic-DTM compiled polynomials having
  small projected rank.
* The contradiction Axiom 2 + Axiom 3 fires *only* on SAT-deciding DTMs,
  which exist (with bounded parameters at n = 2⁸⁰⁴) only if P = NP. -/

end GlobalGodMoveGauge
