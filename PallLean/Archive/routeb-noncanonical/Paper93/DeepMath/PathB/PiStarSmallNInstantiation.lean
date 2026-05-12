import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier
import PallLean.Paper93.DeepMath.PathB.Positroid.NonIdentityGaugeN5

/-!
# Small-`n` stress-test of the Codex Π⋆ surface at `n = 5`

This file is a structural sanity-check of the Π⋆ target
`CookLevinRichProjectionTarget` (defined in
`SATDeciderGaugeFinalTarget`) at the toy size `n = 5`. The point is
*not* to discharge the contradiction — that would amount to proving
P ≠ NP at the toy scale, which is false at `n = 5` by trivial counting
alone (the projected `n^200 < choose (n/3) (log₂ n)` gap simply does
not hold there). The point is to confirm:

1. **Type-level well-formedness at `n = 5`.** The Codex gauge surface
   `SATDeciderGaugeMap M 5 …`, the three subgoal predicates
   `SATDeciderGaugeRankMonotonicity`, `SATDeciderGaugePSideBound`,
   `SATDeciderGaugeNPIdentityMinorPreservation`, and the bundled target
   `CookLevinRichProjectionTarget` are all well-typed and elaborate
   without any `n ≥ 2 ^ 804` simplification. This rules out a
   silently-vacuous Π⋆ scaffold.

2. **Structural inhabitation of the gauge type at `n = 5`.** The
   identity gauge `identitySATDeciderGauge` already supplies a term of
   `SATDeciderGaugeMap M 5 …` for any DTM `M` with `M.timeBound ≤ 4`
   and `M.numStates ≤ 5`. This shows the *carrier* of Π⋆ is non-empty
   at small `n`.

3. **Partial subgoal discharge at `n = 5`.** The rank-monotonicity
   subgoal `SATDeciderGaugeRankMonotonicity` does *not* need
   `n ≥ 2 ^ 804` — it is satisfied by the identity gauge at any `n`
   (with `n ≥ 2`). We discharge it explicitly at `n = 5` here.

4. **Vacuous discharge of the bundled target.** The bundled
   `CookLevinRichProjectionTarget M 5 hn …` has the unused hypothesis
   `_hn : 5 ≥ 2 ^ 804`, which is propositionally `False`. Hence the
   target is provable at `n = 5` *vacuously* from any consumer of `hn`,
   and we record this explicitly. This is the precise technical reason
   the Π⋆ scaffold cannot derive a contradiction at small `n`: the
   contradiction-strength bite lives in the conjunction with
   `n ≥ 2 ^ 804`, not in the subgoals taken individually.

Connection to the §28.3 closed-form determinant stack: the
`compiledGadget α 5` Lean object lives in
`Matrix (Fin 5) (Fin 5) ℝ` (real-valued matrix), whereas the Codex
`SATDeciderGaugeMap` lives in
`MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) Rat`
(a rational multivariate polynomial linear endomorphism). These
inhabit *distinct* Lean types: there is no way to "plug in" the
round-70 matrix witness directly. The §28.3 stack's role at the Π⋆
surface is therefore mediated by the identity-minor gauge bridge
(`compiledGadget_isAmplituhedronGauge_satFamily_iff` and the
amplituhedron-gauge reducer), not by definitional equality. We record
this type-incompatibility here as a remark.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are
introduced. No `sorry`, no custom `axiom`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-!
## (1) Type-level well-formedness anchors at `n = 5`

The following abbreviations exist purely to force Lean to elaborate
each Π⋆ surface predicate at the concrete toy size `n = 5`. If any of
these failed to elaborate (e.g.\ because of an implicit
`n ≥ 2 ^ 804`-driven typeclass instance), the file would not compile.
-/

/-- The SAT-decider gauge space type at `n = 5`. Does not require
`n ≥ 2 ^ 804`. -/
abbrev SATDeciderGaugeSpaceN5
    (M : DTM) (hn2 : (5 : Nat) ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 5) : Type :=
  SATDeciderGaugeSpace M 5 hn2 htb hns

/-- The SAT-decider gauge map type at `n = 5`. Does not require
`n ≥ 2 ^ 804`. -/
abbrev SATDeciderGaugeMapN5
    (M : DTM) (hn2 : (5 : Nat) ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 5) : Type :=
  SATDeciderGaugeMap M 5 hn2 htb hns

/-- The rank-monotonicity subgoal predicate at `n = 5`. Does not
require `n ≥ 2 ^ 804`. -/
abbrev SATDeciderGaugeRankMonotonicityN5
    (M : DTM) (hn2 : (5 : Nat) ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 5)
    (gauge : SATDeciderGaugeMapN5 M hn2 htb hns) : Prop :=
  SATDeciderGaugeRankMonotonicity M 5 hn2 htb hns gauge

/-- The projected P-side bound subgoal predicate at `n = 5`. Does not
require `n ≥ 2 ^ 804` to be merely well-typed (although the predicate
is generally false at small `n`, since `n^200` may exceed
`choose (n/3) (log₂ n)`). -/
abbrev SATDeciderGaugePSideBoundN5
    (M : DTM) (hn2 : (5 : Nat) ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 5)
    (gauge : SATDeciderGaugeMapN5 M hn2 htb hns) : Prop :=
  SATDeciderGaugePSideBound M 5 hn2 htb hns gauge

/-- The NP identity-minor preservation subgoal predicate at `n = 5`.
Does not require `n ≥ 2 ^ 804`. -/
abbrev SATDeciderGaugeNPIdentityMinorPreservationN5
    (M : DTM) (hn2 : (5 : Nat) ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 5)
    (gauge : SATDeciderGaugeMapN5 M hn2 htb hns) : Prop :=
  SATDeciderGaugeNPIdentityMinorPreservation M 5 hn2 htb hns gauge

/-!
## (2) Structural inhabitation of the gauge type at `n = 5`

The identity gauge supplies a closed term of the gauge type at any
admissible `n`, including `n = 5`.
-/

/-- The identity gauge instantiated at the toy size `n = 5` is a
well-formed `SATDeciderGaugeMap M 5 …`. This shows the carrier of the
Π⋆ surface is non-empty at small `n`. -/
noncomputable def identitySATDeciderGaugeN5
    (M : DTM) (hn2 : (5 : Nat) ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 5) :
    SATDeciderGaugeMapN5 M hn2 htb hns :=
  identitySATDeciderGauge M 5 hn2 htb hns

/-!
## (3) Partial subgoal discharge at `n = 5`

The rank-monotonicity subgoal does not require any large-`n`
hypothesis. We can discharge it explicitly at `n = 5` for the identity
gauge.
-/

/-- The identity gauge satisfies the rank-monotonicity subgoal at
`n = 5`. This shows that *part* of the Π⋆ subgoal package is
genuinely satisfiable at small `n` (it is the conjunction with the
P-side / NP-side fields, plus the `n ≥ 2 ^ 804` hypothesis, that
forbids small-`n` discharge of the full target). -/
theorem identitySATDeciderGaugeN5_rankMonotonicity
    (M : DTM) (hn2 : (5 : Nat) ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 5) :
    SATDeciderGaugeRankMonotonicityN5 M hn2 htb hns
      (identitySATDeciderGaugeN5 M hn2 htb hns) :=
  identitySATDeciderGauge_rankMonotonicity M 5 hn2 htb hns

/-!
## (4) Vacuous structural inhabitation of `CookLevinRichProjectionTarget`
at `n = 5`

The bundled Π⋆ target `CookLevinRichProjectionTarget M 5 hn …` has
hypothesis `hn : (5 : Nat) ≥ 2 ^ 804`, which is propositionally
`False`. Any consumer of such an `hn` can therefore exhibit the
existential vacuously. This is the precise technical reason the small-`n`
instantiation is *uninformative* for contradiction purposes: the
Π⋆ scaffold's contradiction-strength bite lives in the interaction of
the three subgoals with `n ≥ 2 ^ 804`, not in the subgoals taken
individually at small `n`.

We record this fact as `cookLevinRichProjectionTarget_n5_of_false_hyp`,
which constructs the bundled target at `n = 5` from an arbitrary
inhabitant of `(5 : Nat) ≥ 2 ^ 804` (or any `False`-equivalent). The
construction does *not* assert P ≠ NP at `n = 5`: it is exactly the
ex-falso branch.
-/

set_option exponentiation.threshold 1024 in
/-- The hypothesis `(5 : Nat) ≥ 2 ^ 804` is propositionally `False`. -/
theorem not_five_ge_two_pow_804 : ¬ ((5 : Nat) ≥ 2 ^ 804) := by
  intro h
  have h2 : (2 : Nat) ^ 804 ≤ 5 := h
  -- `2 ^ 804` is astronomically larger than `5`. We argue via
  -- `2 ^ 11 = 2048 > 5` and monotonicity of `2 ^ ·`.
  have hmono : (2 : Nat) ^ 11 ≤ 2 ^ 804 :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by decide : 11 ≤ 804)
  have h3 : (2 : Nat) ^ 11 ≤ 5 := le_trans hmono h2
  have h4 : (2 : Nat) ^ 11 = 2048 := by decide
  omega

/-- **Ex-falso instantiation of `CookLevinRichProjectionTarget` at
`n = 5`.**

Given a hypothetical `hn : (5 : Nat) ≥ 2 ^ 804`, the Π⋆ target at
`n = 5` is provable vacuously. This is *not* a discharge of the Π⋆
contradiction-strength content; it is the formal record that the
Π⋆ surface at `n = 5` is sealed off from contradiction by its
unsatisfiable hypothesis hypothesis (cf.\
`not_five_ge_two_pow_804`). -/
theorem cookLevinRichProjectionTarget_n5_of_false_hyp
    (M : DTM) (hn : (5 : Nat) ≥ 2 ^ 804) (hn2 : (5 : Nat) ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 5) :
    CookLevinRichProjectionTarget M 5 hn hn2 htb hns :=
  absurd hn not_five_ge_two_pow_804

/-!
## (5) Remark on the §28.3 / round-70 closed-form determinant stack

The §28.3 round-70 closed-form determinant package
(`compiledGadget_5x5_det`, `compiledGadget_5x5_det_pos`,
`exists_alpha_n5_det_one`, `nonIdentity_gauge_n5`) yields a
`Matrix (Fin 5) (Fin 5) ℝ`-valued non-identity amplituhedron-gauge
witness for `satFamily 5`. This witness lives in a *different* Lean
type from the Codex SAT-decider gauge `SATDeciderGaugeMap M 5 …`,
which is `MvPolynomial (Fin (cook_levin_compilation M 5 hn2 htb hns).numVars) Rat
→ₗ[Rat] MvPolynomial …`. There is no definitional or canonical
coercion between the two types.

In particular, the round-70 matrix witness *cannot* be plugged in as
the `gauge` field of `CookLevinRichProjectionTarget M 5 …`, even
ignoring the `n ≥ 2 ^ 804` hypothesis. The §28.3 stack's role at the
Π⋆ surface is therefore mediated by the identity-minor /
amplituhedron-gauge reducers
(`compiledGadget_isAmplituhedronGauge_satFamily_iff`), not by direct
substitution.

The following anchor records the existence of *both* witness layers at
`n = 5`: the matrix-side amplituhedron gauge (from the §28.3 stack)
and the polynomial-side identity gauge (from the SAT-decider real
frontier). They are independent objects.
-/

/-- Joint existence at `n = 5`: a non-identity `Matrix (Fin 5) (Fin 5) ℝ`
amplituhedron gauge witness for `satFamily 5` (from the §28.3
round-70 stack) and a polynomial-side identity gauge in
`SATDeciderGaugeMap M 5 …` (from the real frontier). The two witnesses
inhabit different types and document the type-incompatibility between
the §28.3 matrix stack and the Codex polynomial gauge surface. -/
theorem n5_witnesses_two_layers
    (M : DTM) (hn2 : (5 : Nat) ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 5) :
    (∃ A : Matrix (Fin 5) (Fin 5) ℝ,
        IsAmplituhedronGauge A (satFamily 5) ∧
          A ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ)) ∧
      (∃ gauge : SATDeciderGaugeMapN5 M hn2 htb hns,
        SATDeciderGaugeRankMonotonicityN5 M hn2 htb hns gauge) :=
  ⟨Positroid.nonIdentity_gauge_n5,
   ⟨identitySATDeciderGaugeN5 M hn2 htb hns,
    identitySATDeciderGaugeN5_rankMonotonicity M hn2 htb hns⟩⟩

/-! ## Axiom audit anchors -/

#print axioms identitySATDeciderGaugeN5_rankMonotonicity
#print axioms not_five_ge_two_pow_804
#print axioms cookLevinRichProjectionTarget_n5_of_false_hyp
#print axioms n5_witnesses_two_layers

end PallLean.Paper93.DeepMath.PathB
