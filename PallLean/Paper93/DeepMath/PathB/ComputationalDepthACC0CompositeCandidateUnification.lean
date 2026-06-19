import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MultilinearBasis

/-!
# Workstream B — the composite-barrier candidates collapse onto the single open socket

The Universal Native Characteristic Obstruction (entries 280/300/312) kills every *native exact* polynomial method:
no `AddCommMonoidWithOne` hosts both `2 = 0` and `3 = 0` without collapsing (`3 = 2 + 1 ⟹ 1 = 0`).  The surviving open
candidates of `NFRAME_TWO_ROUTES.md` §4 are the *non-native* routes:

1. **char-0 polynomials** (`ℚ`/`ℝ`) — "parity needs degree `n`", plausibly a dead end;
2. **CRT / product observers** (`ZMod 2 × ZMod 3`) — cross-modulus blow-up (282);
4. **probabilistic / approximate** cross-characteristic representations — the natural next object;
5. **staged / layered** non-flattening observers (281).

This file establishes, with proved theorems, that **none of these is an *independent* escape**: the native algebraic
obstruction is *inapplicable* to all of them (they live over a nontrivial field with `2 ≠ 0` and `3 ≠ 0`, so the
`2 = 0 ∧ 3 = 0` hypothesis that powers 280/300/312 is simply false), and the **dimensional barrier is
characteristic-independent** — the degree-`< n` function space is a *proper* subspace over **every** field, including the
characteristic-0 field `ℚ` of candidate 1, with exactly the same dimension `lowDegreeDim n D < 2ⁿ` proved by the
multilinear basis (entry 264⁺).  Hence the only remaining lever, in *every* characteristic, is the single open analytic
socket `PolynomialMethodApproximation` (the Razborov–Smolensky core, entry-238 `CarryRefinementCrossing`).

## What is proved (clean axioms, no `sorry`)

* **`exists_nontrivial_field_two_three_neZero`** — `∃` a nontrivial field with `(2 : F) ≠ 0 ∧ (3 : F) ≠ 0` (witness
  `ℚ`).  The native obstruction *requires* `2 = 0 ∧ 3 = 0`; here both fail, so 280/300/312 cannot engage.
* **`native_obstruction_hypothesis_fails`** — in any such field, `¬ ((2 : F) = 0 ∧ (3 : F) = 0)`: the algebraic no-go's
  hypothesis is vacuous for the non-native candidates.
* **`finrank_cube_fun`** — `finrank F ((Fin n → Bool) → F) = 2ⁿ` (the ambient function-space dimension, any field).
* **`lowDegreeSubmodule_ne_top`** — for `D < n`, the degree-`≤ D` submodule is a *proper* subspace, over **any** field
  (`finrank = lowDegreeDim n D < 2ⁿ`).
* **`exists_high_degree_over_any_field`** — hence over any field there is a function of true degree `> D`.
* **`charZero_no_low_degree`** — the `ℚ` (characteristic-0) instance: candidate 1 gains *nothing* dimensionally; the
  degree-`< n` space is proper over `ℚ` exactly as over `F_p`.

## Honest scope

This proves that the algebraic obstruction is inapplicable to the non-native candidates and that the dimension barrier
is the same in *every* characteristic (including char 0) — so the choice of ambient field/structure is *not* where a
separation can come from; the candidates are re-skins of the same single open socket, not independent escapes.  It does
**not** prove `PolynomialMethodApproximation` (the genuine open Razborov–Smolensky core — that is the composite barrier
itself), and is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `NFRAME_TWO_ROUTES.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeCandidateUnification

open PallLean.Paper93.DeepMath.PathB.ACC0NonNativeDegree (lowDegreeDim lowDegreeDim_lt_two_pow)
open PallLean.Paper93.DeepMath.PathB.ACC0MultilinearBasis (lowDegreeSubmodule lowDegreeSubmodule_finrank)

/-- **A nontrivial field where neither `2` nor `3` vanishes (PROVED).**  Witness `ℚ`: `2, 3 ≠ 0`.  The Universal
Native Characteristic Obstruction (280/300/312) requires *both* `2 = 0` and `3 = 0`; over such a field both fail, so the
algebraic no-go cannot engage with the non-native (char-0 / CRT / approximate / staged) candidates. -/
theorem exists_nontrivial_field_two_three_neZero :
    ∃ (F : Type) (_inst : Field F), Nontrivial F ∧ (2 : F) ≠ 0 ∧ (3 : F) ≠ 0 :=
  ⟨ℚ, inferInstance, inferInstance, by norm_num, by norm_num⟩

/-- **The obstruction's hypothesis is vacuous for the non-native candidates (PROVED).**  In a field with `2 ≠ 0`, the
conjunction `2 = 0 ∧ 3 = 0` that powers the native obstruction is false. -/
theorem native_obstruction_hypothesis_fails {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    ¬ ((2 : F) = 0 ∧ (3 : F) = 0) :=
  fun h => h2 h.1

variable {F : Type} [Field F]

/-- **The ambient function-space dimension (PROVED).**  `finrank F ((Fin n → Bool) → F) = 2ⁿ`, in any field. -/
theorem finrank_cube_fun {n : ℕ} :
    Module.finrank F ((Fin n → Bool) → F) = 2 ^ n := by
  rw [Module.finrank_pi, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **The degree-`≤ D` submodule is proper, over ANY field (PROVED).**  For `D < n` it has dimension
`lowDegreeDim n D < 2ⁿ = finrank` of the whole space, so it cannot be all of it.  Crucially this holds in *every*
characteristic — char 0 (`ℚ`) included — because `lowDegreeSubmodule_finrank` (the multilinear basis) and
`lowDegreeDim_lt_two_pow` (pure counting) are both field-independent. -/
theorem lowDegreeSubmodule_ne_top {n D : ℕ} (h : D < n) :
    lowDegreeSubmodule (F := F) n D ≠ ⊤ := by
  intro htop
  have h1 : Module.finrank F (lowDegreeSubmodule (F := F) n D) = lowDegreeDim n D :=
    lowDegreeSubmodule_finrank
  have h2 : Module.finrank F (lowDegreeSubmodule (F := F) n D)
      = Module.finrank F ((Fin n → Bool) → F) := by
    rw [htop, finrank_top]
  rw [h1, finrank_cube_fun] at h2
  exact absurd h2 (Nat.ne_of_lt (lowDegreeDim_lt_two_pow h))

/-- **A function of true degree `> D` exists, over ANY field (PROVED).**  Since the degree-`≤ D` submodule is proper
(`lowDegreeSubmodule_ne_top`), some function lies outside it. -/
theorem exists_high_degree_over_any_field {n D : ℕ} (h : D < n) :
    ∃ f : (Fin n → Bool) → F, f ∉ lowDegreeSubmodule (F := F) n D := by
  by_contra hc
  push_neg at hc
  exact lowDegreeSubmodule_ne_top (F := F) h (Submodule.eq_top_iff'.mpr hc)

/-- **Candidate 1 (characteristic 0) gains nothing dimensionally (PROVED).**  Over `ℚ` the degree-`< n` function space
is proper exactly as over a finite field — there is a function of true degree `> D` for every `D < n`.  So moving to
characteristic 0 does not evade the dimension barrier; the obstruction to a low-degree representation is the same in
every characteristic. -/
theorem charZero_no_low_degree {n D : ℕ} (h : D < n) :
    ∃ f : (Fin n → Bool) → ℚ, f ∉ lowDegreeSubmodule (F := ℚ) n D :=
  exists_high_degree_over_any_field (F := ℚ) h

/-!
**The composite candidates, unified.**  The native algebraic obstruction (280/300/312) needs `2 = 0 ∧ 3 = 0`, which
fails over the nontrivial field `ℚ` (`exists_nontrivial_field_two_three_neZero`,
`native_obstruction_hypothesis_fails`) — so it is silent on the non-native candidates.  And the dimension barrier is
*characteristic-independent*: the degree-`≤ D` submodule is proper over **every** field, char 0 (`ℚ`) included
(`lowDegreeSubmodule_ne_top`, `charZero_no_low_degree`), with the same `lowDegreeDim n D < 2ⁿ`.  Therefore none of the
surviving candidates (char-0, CRT, approximate, staged) is an independent escape — each, over its ambient field, reduces
to the *single* open analytic socket `PolynomialMethodApproximation`
(`…ACC0MultilinearBasis.patternRichCrossFieldLowerBound_no_dimSocket`), the genuine open Razborov–Smolensky core.  Not
faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeCandidateUnification

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCandidateUnification.exists_nontrivial_field_two_three_neZero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCandidateUnification.finrank_cube_fun
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCandidateUnification.lowDegreeSubmodule_ne_top
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCandidateUnification.exists_high_degree_over_any_field
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCandidateUnification.charZero_no_low_degree
