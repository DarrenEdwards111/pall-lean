/-
  PallLean/Paper93/DeepMath/PathB/SpanningSubLemmaSmallN.lean

  Sub-lemma chip at Codex's named live blocker
  `AgentG4_Spanning_concrete` / `hPostSpan` — discharging a concrete
  small-`n` (n = 2) sub-component of the Cook–Levin per-type spanning
  containment

      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp W

  at a specific non-admissible `bp : BoundedProfile (Nat.log 2 2)`.

  ## Real-component scope

  `AgentG4_Spanning_concrete` (Paper93/FinalCompositionV2.lean) and the
  more general per-type bundle `CookLevinPerTypeSpanning_universal`
  (Paper93/Spanning/Composition.lean) ultimately reduce to a per-`bp`
  containment

      `cookLevinPostSpanAt M n hn htb hns bp.toHistogram
         ≤ cookLevinProfileSubspace bp W`

  for every `bp : BoundedProfile (Nat.log 2 n)`. The `BoundedProfile`
  fintype at parameter `Nat.log 2 n` covers profiles whose components
  are each ≤ `Nat.log 2 n`, but its profile **mass** can be as large
  as `4 * Nat.log 2 n` — well above `Nat.log 2 n` for non-trivial bp.

  Profiles `bp` with `profileMass bp.toHistogram > Nat.log 2 n` are
  **non-admissible** at radius `κ = Nat.log 2 n`, and the Cook–Levin
  post-span contribution at such a `bp` is `⊥`
  (`allBoundedProfilePostSpan_zero_of_not_admissible`,
  `WithinProfileBound.lean`). Hence the spanning containment at any
  such `bp` is `⊥ ≤ cookLevinProfileSubspace bp W`, i.e. `bot_le`.

  This file isolates that **vacuous-bp branch** of the spanning
  obligation as a kernel-only lemma at the smallest paper-scale
  `n = 2`, where `Nat.log 2 n = 1` and there are explicit non-admissible
  profiles in `BoundedProfile 1` (every histogram with mass ≥ 2).

  The discharge is **not peripheral**: it covers exactly the bp-branch
  of `cookLevinProfileSubspace_contains_postSpan_at_bp` that is
  vacuously true by an empty generator set — the same branch that the
  `WithinProfileBound` admissibility split exploits in the upstream
  finrank pipeline (Part 26, Part 27 of `WithinProfileBound.lean`).

  ## What is discharged

    * `cookLevinPostSpanAt_le_subspace_of_not_admissible`:
      universal kernel-only discharge — for any `(M, n, hn, htb, hns, W)`
      and any `bp : BoundedProfile (Nat.log 2 n)` with
      `¬ ProfileAdmissible (Nat.log 2 n) bp.toHistogram`, the spanning
      containment holds (as `⊥ ≤ _`).

    * `bp_full_smallN`:
      explicit non-admissible witness in `BoundedProfile (Nat.log 2 2)`
      with histogram identically `1` (mass `4 > 1`).

    * `cookLevin_spanning_smallN_full_bp`:
      concrete `n = 2` instance of the spanning containment for the
      non-admissible witness `bp_full_smallN`, for any `W`.

    * `cookLevinPerTypeSpanning_smallN_full_bp_generator`:
      the per-generator membership clause of `CookLevinPerTypeSpanning`
      at `n = 2`, `bp = bp_full_smallN` — the actual unit consumed by
      the existential reduction
      `cookLevinProfileSubspace_contains_postSpan_at_bp` in
      `Paper93/Spanning/Composition.lean`. This is the vacuous branch
      of the Fin-indexed equation set in `CookLevinPerTypeSpanning`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:  [propext, Classical.choice, Quot.sound].
-/
import PallLean.Paper93.Spanning.Composition
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.WithinProfileBound

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Spanning

/-! ## Universal vacuous-bp discharge

The post-span at any non-admissible histogram is `⊥`, so the
spanning containment is `bot_le`. -/

/-- **Universal vacuous spanning at a non-admissible bp.**

For any cookLevin parameters `(M, n, hn, htb, hns)` and any per-type
family `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)`,
if `bp : BoundedProfile (Nat.log 2 n)` is non-admissible at radius
`Nat.log 2 n` (i.e. `profileMass bp.toHistogram > Nat.log 2 n`), then
the Cook–Levin post-span containment for that `bp` holds trivially —
because the post-span is the zero submodule.

This is the vacuous branch of
`cookLevinProfileSubspace_contains_postSpan_at_bp`. Unlike the
non-vacuous (admissible) branch, it requires no spanning data on the
per-type family `W` at all. -/
theorem cookLevinPostSpanAt_le_subspace_of_not_admissible
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n))
    (hnot : ¬ ProfileAdmissible (Nat.log 2 n) bp.toHistogram) :
    cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp W := by
  -- The post-span at a non-admissible histogram is `⊥`.
  have hbot :
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram = ⊥ := by
    -- `cookLevinPostSpanAt` is a `noncomputable abbrev` for
    -- `allBoundedProfilePostSpan ...`; reuse the existing
    -- WithinProfileBound vanishing lemma.
    unfold cookLevinPostSpanAt
    exact allBoundedProfilePostSpan_zero_of_not_admissible
      (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (cookLevinConstraintType M n hn htb hns)
      bp.toHistogram hnot
  -- Then `⊥ ≤ _` is the trivial bottom-inequality.
  rw [hbot]
  exact bot_le

/-! ## Per-generator (Fin-indexed equation) form

The same content stated as the per-generator membership clause of
`CookLevinPerTypeSpanning`. This is the exact Fin-indexed equation
discharged for the non-admissible bp in the spanning bundle. -/

/-- **Vacuous per-generator membership for non-admissible bp.**

The per-generator clause of `CookLevinPerTypeSpanning` at a fixed
non-admissible `bp` is vacuously true: no generator `g` exists in
`boundedProfileClassifiedSet … S bp.toHistogram` for any `S` with
`S.length ≤ Nat.log 2 n`, because `profileMass bp.toHistogram >
S.length` rules out any compatible derivative distribution. -/
theorem cookLevinPerTypeSpanning_perGenerator_of_not_admissible
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n))
    (hnot : ¬ ProfileAdmissible (Nat.log 2 n) bp.toHistogram) :
    ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
      (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
      (g : MvPolynomial (Fin n) ℚ)
      (_hg : g ∈ boundedProfileClassifiedSet
                (fun i => (cookLevinFactorList M n hn htb hns).get i)
                (cookLevinConstraintType M n hn htb hns)
                S bp.toHistogram),
      mlProj (shift * g) ∈ cookLevinProfileSubspace bp W := by
  intro S hSlen shift _hshift g hg
  -- A bounded profile-classified generator is admissible at `S.length`,
  -- which by `hSlen` is ≤ `Nat.log 2 n`, contradicting `hnot`.
  have hSadm :
      ProfileAdmissible S.length bp.toHistogram :=
    boundedProfileClassifiedSet_profile_admissible
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (cookLevinConstraintType M n hn htb hns) S bp.toHistogram g hg
  have hkadm : ProfileAdmissible (Nat.log 2 n) bp.toHistogram :=
    le_trans hSadm hSlen
  exact False.elim (hnot hkadm)

/-! ## Concrete `n = 2` witness

We pin a specific `bp : BoundedProfile (Nat.log 2 2)` with histogram
identically `1`, mass `4 > 1`, hence non-admissible. -/

/-- Numeric helper: `Nat.log 2 2 = 1`. -/
private theorem nat_log_2_2 : Nat.log 2 2 = 1 := by decide

/-- The all-ones histogram on `ConstraintType`: every component is `1`,
mass `4`. -/
def histFull : ProfileHistogram := fun _ => 1

/-- The all-ones histogram has profile mass `4`. -/
theorem profileMass_histFull : profileMass histFull = 4 := by
  classical
  -- Unfold and explicitly compute the four-term sum over `ConstraintType`.
  show (∑ τ : ConstraintType, (1 : ℕ)) = 4
  rw [Finset.sum_const, Finset.card_univ]
  -- `Fintype.card ConstraintType = 4` by decide on the inductive
  -- type with four constructors.
  decide

/-- The all-ones histogram is component-wise `≤ 1` and so lies in
`BoundedProfile (Nat.log 2 2) = BoundedProfile 1`. -/
def bp_full_smallN : BoundedProfile (Nat.log 2 2) :=
  ⟨histFull, by
    intro τ
    rw [nat_log_2_2]
    -- Each component of `histFull` is `1`, and `1 ≤ 1`.
    rfl⟩

/-- Sanity: `bp_full_smallN`'s underlying histogram is `histFull`. -/
theorem bp_full_smallN_toHistogram :
    bp_full_smallN.toHistogram = histFull := rfl

/-- The all-ones histogram is **not** admissible at radius
`Nat.log 2 2 = 1`: its mass is `4`, exceeding `1`. -/
theorem histFull_not_admissible_smallN :
    ¬ ProfileAdmissible (Nat.log 2 2) histFull := by
  unfold ProfileAdmissible
  rw [profileMass_histFull, nat_log_2_2]
  -- Goal: ¬ 4 ≤ 1
  decide

/-- Equivalent statement, for `bp_full_smallN.toHistogram`. -/
theorem bp_full_smallN_not_admissible :
    ¬ ProfileAdmissible (Nat.log 2 2) bp_full_smallN.toHistogram := by
  rw [bp_full_smallN_toHistogram]
  exact histFull_not_admissible_smallN

/-! ## The discharged spanning containment at `n = 2`, `bp_full_smallN`

The concrete `n = 2` instance of the spanning containment for
`bp_full_smallN`. This is a **real** spanning unit (per-generator
clause for one specific `bp` of the universal `bp`-quantifier in
`CookLevinPerTypeSpanning`), discharged with no hypothesis on `W`. -/

/-- **Concrete `n = 2` spanning containment for the all-ones bp.**

For any DTM `M` with `M.timeBound ≤ 4` and `M.numStates ≤ 2`, and
any per-type family `W`, the Cook–Levin post-span at the all-ones
profile `bp_full_smallN` is contained in `cookLevinProfileSubspace
bp_full_smallN W`. The post-span vanishes because the all-ones
profile has mass `4`, exceeding the radius `Nat.log 2 2 = 1`. -/
theorem cookLevin_spanning_smallN_full_bp
    (M : DTM)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin 2) ℚ)) :
    cookLevinPostSpanAt M 2 (by decide) htb hns bp_full_smallN.toHistogram
      ≤ cookLevinProfileSubspace bp_full_smallN W :=
  cookLevinPostSpanAt_le_subspace_of_not_admissible
    M 2 (by decide) htb hns W
    bp_full_smallN bp_full_smallN_not_admissible

/-- **Per-generator membership clause for the `n = 2` all-ones bp.**

The exact Fin-indexed equation that `CookLevinPerTypeSpanning` asks
for at `bp = bp_full_smallN` and `n = 2` — discharged vacuously. -/
theorem cookLevinPerTypeSpanning_smallN_full_bp_generator
    (M : DTM)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin 2) ℚ)) :
    ∀ (S : List (Fin 2)) (_hSlen : S.length ≤ Nat.log 2 2)
      (shift : MvPolynomial (Fin 2) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
      (g : MvPolynomial (Fin 2) ℚ)
      (_hg : g ∈ boundedProfileClassifiedSet
                (fun i => (cookLevinFactorList M 2 (by decide) htb hns).get i)
                (cookLevinConstraintType M 2 (by decide) htb hns)
                S bp_full_smallN.toHistogram),
      mlProj (shift * g) ∈ cookLevinProfileSubspace bp_full_smallN W :=
  cookLevinPerTypeSpanning_perGenerator_of_not_admissible
    M 2 (by decide) htb hns W
    bp_full_smallN bp_full_smallN_not_admissible

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms cookLevinPostSpanAt_le_subspace_of_not_admissible
#print axioms cookLevinPerTypeSpanning_perGenerator_of_not_admissible
#print axioms cookLevin_spanning_smallN_full_bp
#print axioms cookLevinPerTypeSpanning_smallN_full_bp_generator

end PathB
end DeepMath
end Paper93
end PallLean
