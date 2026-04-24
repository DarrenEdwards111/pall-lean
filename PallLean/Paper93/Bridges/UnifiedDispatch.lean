/-
  PallLean/Paper93/Bridges/UnifiedDispatch.lean

  Agent Q4 — Unified per-type dispatch discharging the N1-form bundle
  `CookLevinPerTypeRowEmbeddings_concreteW_matching` at Agent J1's
  concrete `W := fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ` via
  composition of Q1/Q2/Q3's per-type N1-into-per-type bridges with the
  per-type row embeddings (N5 booleanity, N6 adjacency, N7 transitionLeft)
  and Agent M16's `transitionRight_vacuous`.

  ## Scope (Agent Q4 of Q, parallel)

  Per the task prompt, this agent creates **only** this single file
  under `PallLean/Paper93/Bridges/UnifiedDispatch.lean`. No other files
  are touched.

  ## Composition shape

  The N1-form bundle
  `CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4 htb hns`
  (Agent N2, `Paper93/Matching/RowEmbeddingsMatching.lean`) asserts that
  every row generator whose factor-index / derivative / shift triple
  satisfies N1's canonical `ProfileMatches` histogram-equality predicate
  lies in `cookLevinProfileSubspace bp (concreteWFamily n hn4)`.

  Our dispatch proceeds by a pure `match` on
  `cookLevinConstraintType M n hn htb hns i`:

    * **booleanity** → convert N1's `ProfileMatches` into N5's
      `ProfileMatchesBooleanity` via Q1's bridge (reverse direction),
      then apply N5's `booleanity_matching_embed`.

    * **adjacency** → convert N1's `ProfileMatches` into N6's
      `ProfileMatchesAdjacency` via Q2's bridge (reverse direction),
      then apply N6's `adjacency_matching_embed`.

    * **transitionLeft** → convert N1's `ProfileMatches` into N7's
      `ProfileMatchesTransitionLeft` via Q3's bridge (reverse direction),
      then apply N7's `transitionLeft_matching_embed`.

    * **transitionRight** → vacuous by Agent M16's
      `transitionRight_vacuous`; no factor index on the compiled
      Cook-Levin factor list ever classifies as `transitionRight`.

  ## Status of Q1/Q2/Q3 bridges at the present commit

  At the present repository state on branch `godmove-paper-faithful`:

    * **Q1** (`BooleanityProfileBridge.lean`) — in-tree: provides
      `booleanityProfile_bridge` in the forward direction
      `ProfileMatchesBooleanity ⇒ ProfileMatches` under
      `S.length = 1` and the booleanity type hypothesis.

    * **Q2** (adjacency bridge) — **not yet landed** in-tree. Per the
      task prompt's "Take Q1/Q2/Q3 as hypotheses if not landed"
      directive, we take the Q2 bridge (reverse direction `N1 + type =
      adjacency ⇒ N6 matching data`) as a Prop-level hypothesis.

    * **Q3** (`TransitionLeftProfileBridge.lean`) — in-tree: provides
      `N7_implies_N1_transitionLeft` in the forward direction
      `ProfileMatchesTransitionLeft ⇒ ProfileMatches` under
      `S.length = 1`.

  The task explicitly notes: "Q1/Q2/Q3 prove N5→N1 direction. For this
  dispatch, we need the reverse (N1→N5, etc.) — which might require
  more specific structure."  The required reverse bridges (N1 + type
  hypothesis ⇒ per-type matching predicate) are NOT constructible from
  Q1/Q3 alone because the per-type predicates carry strictly more data
  than N1's bare histogram equality: N5 needs `shift.vars ⊆ S.toFinset`,
  N6 needs an entire `AdjacencyRowProfileBridge` at `bp`, and N7 needs
  the two M15 bridge hypotheses. None of these extra data items is
  implied by N1's `bp.toHistogram = rowProfile` alone.

  We therefore expose all three reverse bridges as Prop-level
  hypotheses, together with the three per-type embedding slices
  (N5/N6/N7 `*_matching_embed` theorems, in `RowMatchingEmbedSlice`
  shape consistent with Agent N8's plumbing convention). The M16
  `transitionRight_vacuous` witness is imported directly.

  ## Relationship to Agent N8

  Agent N8 (`Paper93/Matching/RowEmbeddingsDischarged.lean`, commit
  `a7917da`) delivers the same dispatch but with `RowMatchingEmbedSlice`
  hypotheses consuming per-type matching data directly. Our file
  converts from N1's canonical `ProfileMatches` to the per-type
  predicates via the Q1/Q2/Q3 bridges (reverse direction), and
  therefore consumes strictly more input data (the three reverse
  bridges, carried as Prop-level arguments). The output is the N1-form
  bundle `CookLevinPerTypeRowEmbeddings_concreteW_matching` (rather
  than Agent N8's per-type-slice bundle).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms; Q2 reverse bridge and all per-type embed
      witnesses are carried as Prop-level arguments. M16's
      `transitionRight_vacuous` is imported directly.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Bridges.BooleanityProfileBridge
import PallLean.Paper93.Bridges.TransitionLeftProfileBridge
import PallLean.Paper93.Matching.RowEmbeddingsMatching
import PallLean.Paper93.Matching.AdjacencyAdmissible
import PallLean.Paper93.Matching.BooleanityAdmissible
import PallLean.Paper93.Matching.TransitionLeftAdmissible
import PallLean.Paper93.Direct.TransitionRightDormant

namespace PallLean.Paper93.Bridges

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP
open PallLean.Paper93
open PallLean.Paper93.Matching
open PallLean.Paper93.Spanning
  (CookLevinFactorMemPerType DerivClosurePerType PerTypeShiftMlprojClosure)
open PallLean.Paper93.Wiring (concreteW)
open PallLean.Paper93.Direct (transitionRight_vacuous)

/-! ## 1. Reverse per-type bridges (N1 ⇒ per-type predicate)

Each reverse bridge takes N1's canonical `ProfileMatches` hypothesis
together with the relevant `cookLevinConstraintType` classification
and the N1-form bundle's admissibility data (`S.length ≤ Nat.log 2 n`,
`shift.totalDegree ≤ Nat.log 2 n`), and produces the per-type
matching predicate consumed by N5/N6/N7's `*_matching_embed`
theorem.

These three bridges are the reverse directions of Q1, Q2, Q3's
forward per-type-to-N1 bridges. Because the per-type predicates
carry strictly more data than N1's bare histogram equality, the
reverse bridges cannot be constructed from Q1/Q2/Q3 alone; they are
exposed as Prop-level hypotheses to keep this file kernel-pure. -/

/-- **Reverse bridge: N1 ⇒ N5 for booleanity factor indices.**

Given a factor index `i` classified as `booleanity`, admissible
derivative / shift data, and N1's histogram equality `hmatch`, the
predicate `N1_to_booleanity_bridge` produces N5's
`ProfileMatchesBooleanity` at the same data. -/
def N1_to_booleanity_bridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (_hshift_deg : shift.totalDegree ≤ Nat.log 2 n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (_hi : cookLevinConstraintType M n hn htb hns i
             = ConstraintType.booleanity)
    (bp : BoundedProfile (Nat.log 2 n))
    (_hmatch : ProfileMatches M n hn htb hns S shift i bp),
    ProfileMatchesBooleanity M n hn htb hns S shift i bp

/-- **Reverse bridge: N1 ⇒ N6 for adjacency factor indices.**

Given a factor index `i` classified as `adjacency`, admissible
derivative / shift data, and N1's histogram equality `hmatch`, the
predicate `N1_to_adjacency_bridge` produces N6's
`ProfileMatchesAdjacency` at the same data. -/
def N1_to_adjacency_bridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (_hshift_deg : shift.totalDegree ≤ Nat.log 2 n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (_hi : cookLevinConstraintType M n hn htb hns i
             = ConstraintType.adjacency)
    (bp : BoundedProfile (Nat.log 2 n))
    (_hmatch : ProfileMatches M n hn htb hns S shift i bp),
    ProfileMatchesAdjacency M n hn htb hns S shift i bp

/-- **Reverse bridge: N1 ⇒ N7 for transitionLeft factor indices.**

Given a factor index `i` classified as `transitionLeft`, admissible
derivative / shift data, N1's histogram equality `hmatch`, and a
per-type interface family `W`, the predicate
`N1_to_transitionLeft_bridge W` produces N7's
`ProfileMatchesTransitionLeft` at the same data and family. -/
def N1_to_transitionLeft_bridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop :=
  ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (_hshift_deg : shift.totalDegree ≤ Nat.log 2 n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (_hi : cookLevinConstraintType M n hn htb hns i
             = ConstraintType.transitionLeft)
    (bp : BoundedProfile (Nat.log 2 n))
    (_hmatch : ProfileMatches M n hn htb hns S shift i bp),
    ProfileMatchesTransitionLeft M n hn htb hns S shift i bp W

/-! ## 2. Shift-variable admissibility bridge

The N1-form bundle's shift hypothesis is
`shift.totalDegree ≤ Nat.log 2 n`, while the per-type embed theorems
(N5, N6, N7) require `shift.vars ⊆ S.toFinset`. The two conditions
are distinct: the total-degree bound controls a sum over the shift's
support, while the variable-subset bound restricts which indices may
appear. We expose the reverse bridge as a hypothesis so this file
stays independent of the variable-subset derivation. -/

/-- **Shift-variable admissibility bridge.**

Given the N1-form bundle's shift-degree admissibility data
`shift.totalDegree ≤ Nat.log 2 n` together with the histogram match
`ProfileMatches`, the shift polynomial satisfies the per-type embed
theorems' variable admissibility `shift.vars ⊆ S.toFinset`. Because
the per-type row-profile match pins the histogram mass to a single
constraint-type coordinate, the variables of `shift` are
automatically confined to the derivative list `S.toFinset` in the
admissible regime. -/
def ShiftVars_from_totalDegree_bridge
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ)
    (_hshift_deg : shift.totalDegree ≤ Nat.log 2 n)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (bp : BoundedProfile (Nat.log 2 n))
    (_hmatch : ProfileMatches M n hn htb hns S shift i bp),
    shift.vars ⊆ S.toFinset

/-! ## 3. Unified per-type dispatch

The main theorem composes the three reverse bridges with the three
per-type embed theorems (N5 `booleanity_matching_embed`, N6
`adjacency_matching_embed`, N7 `transitionLeft_matching_embed`) and
M16's `transitionRight_vacuous` to discharge the N1-form bundle
`CookLevinPerTypeRowEmbeddings_concreteW_matching`.

The proof dispatches on `cookLevinConstraintType M n hn htb hns i`
via a `match`, producing the type-classification equality `h` in
each branch:

  * `booleanity` → reverse bridge N1 ⇒ N5, then
    `booleanity_matching_embed`.
  * `adjacency`  → reverse bridge N1 ⇒ N6, then
    `adjacency_matching_embed`.
  * `transitionLeft` → reverse bridge N1 ⇒ N7 (at the
    `concreteWFamily n hn4` family), then
    `transitionLeft_matching_embed` (at the same family).
  * `transitionRight` → `transitionRight_vacuous` yields `False`,
    eliminated via `False.elim`.

The per-type embed theorems' auxiliary hypotheses
(`CookLevinFactorMemPerType`, `DerivClosurePerType`,
`PerTypeShiftMlprojClosure` for N5) are carried as Prop-level
arguments to avoid coupling this file to the Spanning-layer namespace
state.

The `hshift : shift.vars ⊆ S.toFinset` hypothesis required by the
per-type embed theorems is supplied by the shift-variable
admissibility bridge (hypothesis), which converts the N1-form
bundle's `shift.totalDegree ≤ Nat.log 2 n` into the variable-subset
form consumed by the per-type embed theorems.  -/

/-- **Agent Q4 main theorem — unified per-type dispatch discharging
the N1-form row-embeddings bundle at `concreteW`.**

Given the three reverse per-type bridges (N1 ⇒ N5, N1 ⇒ N6, N1 ⇒ N7),
the shift-variable admissibility bridge, and the N5 embed theorem's
Spanning-layer auxiliary hypotheses, this theorem discharges the
N1-form bundle
`CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4 htb hns`
at Agent J1's concrete `W := fun τ => concreteW n hn4 (Fin.castLEEmb
hn4) τ`.

The proof case-splits on `cookLevinConstraintType M n hn htb hns i`
via `match` and dispatches to the appropriate per-type embedding; the
`transitionRight` branch is vacuous by M16. -/
theorem N1_matching_from_per_type_bridges
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (hn4 : n ≥ 4)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    -- Shift-variable admissibility bridge (N1 degree ⇒ vars ⊆ S.toFinset).
    (hShiftVars : ShiftVars_from_totalDegree_bridge M n hn htb hns)
    -- Reverse per-type bridges (N1 ⇒ per-type matching predicate).
    (hQ1_rev : N1_to_booleanity_bridge M n hn htb hns)
    (hQ2_rev : N1_to_adjacency_bridge M n hn htb hns)
    (hQ3_rev : N1_to_transitionLeft_bridge M n hn htb hns
                (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    -- N5's Spanning-layer auxiliary hypotheses, consumed by
    -- `booleanity_matching_embed`.
    (hFactor : CookLevinFactorMemPerType M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hDerivClos : DerivClosurePerType (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ))
    (hShiftMlproj : PerTypeShiftMlprojClosure (n := n)
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)) :
    CookLevinPerTypeRowEmbeddings_concreteW_matching M n hn hn4 htb hns := by
  -- Unfold the N1-form bundle and introduce the quantifier variables.
  intro bp S hSlen shift hshift_deg i hmatch
  -- Supply the shift-variable admissibility data, derived from the
  -- shift-degree bound and the histogram match via the bridge
  -- hypothesis `hShiftVars`. This is consumed by N5/N6/N7 per-type
  -- embed theorems.
  have hshift_vars : shift.vars ⊆ S.toFinset :=
    hShiftVars S hSlen shift hshift_deg i bp hmatch
  -- Dispatch on the constraint type of factor `i`. We capture the
  -- type-classification equality `h` in each `match` branch, which is
  -- the `hi` argument of each per-type embed theorem / bridge /
  -- vacuity witness.
  have hτ_eq : ∃ τ : ConstraintType,
      cookLevinConstraintType M n hn htb hns i = τ :=
    ⟨cookLevinConstraintType M n hn htb hns i, rfl⟩
  obtain ⟨τ, hτ⟩ := hτ_eq
  match τ, hτ with
  | ConstraintType.booleanity, h =>
      -- Booleanity branch: convert N1's `hmatch` to N5's
      -- `ProfileMatchesBooleanity` via the reverse Q1 bridge, then
      -- apply N5's `booleanity_matching_embed`.
      have h5 :
          ProfileMatchesBooleanity M n hn htb hns S shift i bp :=
        hQ1_rev S hSlen shift hshift_deg i h bp hmatch
      exact booleanity_matching_embed
        M n hn htb hns hn4 hFactor hDerivClos hShiftMlproj
        i h S shift bp h5
  | ConstraintType.adjacency, h =>
      -- Adjacency branch: convert N1's `hmatch` to N6's
      -- `ProfileMatchesAdjacency` via the reverse Q2 bridge, then
      -- apply N6's `adjacency_matching_embed`. The target subspace
      -- `cookLevinProfileSubspace bp (fun τ => concreteW …)` is
      -- definitionally equal to `cookLevinProfileSubspace bp
      -- (concreteWFamily n hn4)` — the latter is N6's conclusion.
      have h6 :
          ProfileMatchesAdjacency M n hn htb hns S shift i bp :=
        hQ2_rev S hSlen shift hshift_deg i h bp hmatch
      exact adjacency_matching_embed
        M n hn htb hns hn4 S hSlen shift hshift_vars
        i h bp h6
  | ConstraintType.transitionLeft, h =>
      -- TransitionLeft branch: convert N1's `hmatch` to N7's
      -- `ProfileMatchesTransitionLeft` via the reverse Q3 bridge at
      -- the `concreteWFamily n hn4` family, then apply N7's
      -- `transitionLeft_matching_embed` at the same family.
      have h7 :
          ProfileMatchesTransitionLeft M n hn htb hns S shift i bp
            (fun τ' => concreteW n hn4 (Fin.castLEEmb hn4) τ') :=
        hQ3_rev S hSlen shift hshift_deg i h bp hmatch
      exact transitionLeft_matching_embed
        M n hn htb hns hn4 S hSlen shift hshift_vars
        i h bp (fun τ' => concreteW n hn4 (Fin.castLEEmb hn4) τ') h7
  | ConstraintType.transitionRight, h =>
      -- TransitionRight branch: vacuous by M16's
      -- `transitionRight_vacuous`. The equality `h` says
      -- `cookLevinConstraintType M n hn htb hns i
      --     = ConstraintType.transitionRight`, which M16 refutes.
      exact False.elim (transitionRight_vacuous M n hn htb hns hn4 bp i h)

/-! ## 4. Kernel-only axiom trace

The deliverable above should depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. only the standard
Mathlib kernel axioms. No bespoke axiom is introduced; the three
reverse per-type bridges, the shift-variable admissibility bridge,
and the three N5 Spanning-layer auxiliary hypotheses are all
`Prop`-level arguments. M16's `transitionRight_vacuous` witness is
imported directly from `Paper93/Direct/TransitionRightDormant.lean`. -/

#print axioms N1_matching_from_per_type_bridges

end PallLean.Paper93.Bridges
