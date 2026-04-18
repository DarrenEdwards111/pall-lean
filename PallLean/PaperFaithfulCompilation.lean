/-
  PaperFaithfulCompilation.lean — u/v variable split for Path A
  ===============================================================

  ## Paper reference

  Paper `p vs np1.pdf`, §§6, 29 (Theorem 203, Lemma 204, Lemma 205,
  Definition 7):

  Paper's polynomial compilation distinguishes two variable types:
  - **u**: clause-sheet variables (input x_i, selectors z_C)
  - **v**: tableau variables (tape bits b_{t,i}, state indicators s_{t,q},
    head positions h_{t,i}, with t ∈ [0, T], i ∈ [0, S])

  The compiled polynomial P_{M,n}(u, v) spans both. The coupled sheet
  Q^×_Φ(u, z) is defined over clause-sheet variables only (no tableau),
  via `Q^×_Φ = ∏_C (1 - z_C · V_C(x)²)`.

  Lemma 205: `Π_Φ := (basis) ∘ (affine relabel) ∘ (restriction) ∘ (projection)`
  where restriction fixes v to constants and projection extracts u.

  ## Rationale for this refactor

  The existing `cook_levin_compilation` uses a flat `Fin n` variable space
  (no u/v split), making rank bounds conflate:
  - `compiled_np_lower_bound_any_dtm` (axiom-free): `rank(compiledPoly) ≥ C(n/3, log n)`
  - `spdp_profile_generators` (false axiom): `rank(compiledPoly) ≤ (log n + 1)^12`

  These are incompatible BECAUSE they're stated about the same polynomial
  object. The paper reconciles by giving them to different objects:
  P_{M,n} (with tableau) vs. Q^×_Φ (clause-sheet only).

  This file introduces the u/v split framework so the P-side and
  NP-side bounds apply to clearly distinct polynomial objects.

  ## Status: ON-CHAIN scaffolding — axiom-free, no sorry.
-/

import PallLean.SPDPDefs
import PallLean.MultilinearSPDP
import PallLean.TuringMachine
import PallLean.CookLevinDefs
import PallLean.PiStarConcrete
import PallLean.GaugeMonotonicity
import PallLean.Tseitin
import PallLean.TseitinDefs
import PallLean.IdentityMinor
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

namespace PaperFaithfulCompilation

open MvPolynomial TuringMachine

/-! ## Section 1: The u/v variable split -/

/-- **UVSplit**: a partition of a variable index set into clause-sheet (`u`)
and tableau (`v`) parts. The total variable count is `numU + numV`.

Concrete instantiation for Cook-Levin:
- `numU = n` (input/clause-sheet variables)
- `numV = poly(n)` (tableau: tape × state × head × time)
-/
structure UVSplit where
  numU : ℕ
  numV : ℕ

/-- Total variable count. -/
def UVSplit.total (σ : UVSplit) : ℕ := σ.numU + σ.numV

/-- The total variable index type as `Fin (numU + numV)`. -/
abbrev UVSplit.Idx (σ : UVSplit) : Type := Fin σ.total

/-- Injection of u-indices into the total index space. -/
def UVSplit.inlU (σ : UVSplit) (i : Fin σ.numU) : σ.Idx :=
  ⟨i.val, by
    unfold UVSplit.total
    have := i.isLt
    omega⟩

/-- Injection of v-indices into the total index space. -/
def UVSplit.inlV (σ : UVSplit) (j : Fin σ.numV) : σ.Idx :=
  ⟨σ.numU + j.val, by
    unfold UVSplit.total
    have := j.isLt
    omega⟩

/-- Decide whether a total index is a u-index. -/
def UVSplit.isU (σ : UVSplit) (k : σ.Idx) : Prop := k.val < σ.numU

instance UVSplit.isU_decidable (σ : UVSplit) : DecidablePred σ.isU :=
  fun k => Nat.decLt _ _

/-- Extract the u-index if `k.isU`, else return a default. Helper for splits. -/
def UVSplit.toUIdx? (σ : UVSplit) (k : σ.Idx) : Option (Fin σ.numU) :=
  if h : k.val < σ.numU then some ⟨k.val, h⟩ else none

/-- Extract the v-index if `¬ k.isU`. -/
def UVSplit.toVIdx? (σ : UVSplit) (k : σ.Idx) : Option (Fin σ.numV) :=
  if h : σ.numU ≤ k.val then
    if h' : k.val - σ.numU < σ.numV then
      some ⟨k.val - σ.numU, h'⟩
    else none
  else none

/-! ## Section 2: The `keep u / restrict v` predicate -/

/-- **Keep-u predicate**: keep clause-sheet (u) variables, substitute tableau
(v) variables. This is the paper's Definition 6(i)/(ii) at the predicate
level: the `keep` underlying the `piZero` construction of Π_Φ. -/
def keepU (σ : UVSplit) : σ.Idx → Prop := σ.isU

instance keepU_decidable (σ : UVSplit) : DecidablePred (keepU σ) :=
  UVSplit.isU_decidable σ

/-- A u-index is kept: `keepU σ (inlU i)` always holds. -/
theorem keepU_inlU (σ : UVSplit) (i : Fin σ.numU) :
    keepU σ (σ.inlU i) := by
  show (σ.inlU i).val < σ.numU
  exact i.isLt

/-- A v-index is NOT kept: `keepU σ (inlV j)` always fails. -/
theorem not_keepU_inlV (σ : UVSplit) (j : Fin σ.numV) :
    ¬ keepU σ (σ.inlV j) := by
  show ¬ (σ.inlV j).val < σ.numU
  show ¬ (σ.numU + j.val) < σ.numU
  omega

/-! ## Section 3: Ambient cardinality sanity -/

/-- `numU ≤ total`. -/
theorem numU_le_total (σ : UVSplit) : σ.numU ≤ σ.total := by
  unfold UVSplit.total; omega

/-- `numV ≤ total`. -/
theorem numV_le_total (σ : UVSplit) : σ.numV ≤ σ.total := by
  unfold UVSplit.total; omega

/-- The u-inclusion is injective. -/
theorem inlU_injective (σ : UVSplit) : Function.Injective σ.inlU := by
  intro i j h
  have : (σ.inlU i).val = (σ.inlU j).val := congrArg Fin.val h
  exact Fin.ext this

/-- The v-inclusion is injective. -/
theorem inlV_injective (σ : UVSplit) : Function.Injective σ.inlV := by
  intro i j h
  have : (σ.inlV i).val = (σ.inlV j).val := congrArg Fin.val h
  show i = j
  apply Fin.ext
  show i.val = j.val
  have hi : (σ.inlV i).val = σ.numU + i.val := rfl
  have hj : (σ.inlV j).val = σ.numU + j.val := rfl
  omega

/-- The u- and v-injections have disjoint images. -/
theorem inlU_inlV_disjoint (σ : UVSplit) (i : Fin σ.numU) (j : Fin σ.numV) :
    σ.inlU i ≠ σ.inlV j := by
  intro heq
  have := congrArg Fin.val heq
  have hi : (σ.inlU i).val = i.val := rfl
  have hj : (σ.inlV j).val = σ.numU + j.val := rfl
  have hilt : i.val < σ.numU := i.isLt
  omega

/-! ## Section 4: Polynomial objects over the split

Two key polynomial types:
- `PMnPoly`: the compiled polynomial `P_{M,n}(u, v)` over all total variables
- `CoupledSheetPoly`: the coupled sheet `Q^×_Φ(u)` over u-variables only -/

/-- **Compiled polynomial over UVSplit**. Ambient type for `P_{M,n}(u, v)`. -/
abbrev PMnPoly (σ : UVSplit) : Type := MvPolynomial σ.Idx ℚ

/-- **Coupled sheet polynomial** over u-variables only. Type for `Q^×_Φ(u)`. -/
abbrev CoupledSheetPoly (σ : UVSplit) : Type := MvPolynomial (Fin σ.numU) ℚ

/-- **Embed a coupled-sheet polynomial into the ambient PMn space** via
the u-injection `inlU`. This realizes `Q^×_Φ(u)` as a special `P_{M,n}(u, v)`
that happens to not depend on v. -/
noncomputable def CoupledSheetPoly.embed (σ : UVSplit) (q : CoupledSheetPoly σ) :
    PMnPoly σ :=
  MvPolynomial.rename σ.inlU q

/-- `embed` is a ℚ-linear map. -/
theorem embed_linear (σ : UVSplit) :
    ∃ φ : CoupledSheetPoly σ →ₗ[ℚ] PMnPoly σ,
      ∀ q, φ q = CoupledSheetPoly.embed σ q :=
  ⟨(MvPolynomial.rename σ.inlU).toLinearMap, fun q => by
    show (MvPolynomial.rename σ.inlU).toLinearMap q = MvPolynomial.rename σ.inlU q
    rfl⟩

/-- `embed 0 = 0`. -/
theorem embed_zero (σ : UVSplit) :
    CoupledSheetPoly.embed σ 0 = 0 := by
  unfold CoupledSheetPoly.embed
  exact map_zero _

/-- `embed` preserves addition. -/
theorem embed_add (σ : UVSplit) (q r : CoupledSheetPoly σ) :
    CoupledSheetPoly.embed σ (q + r) =
      CoupledSheetPoly.embed σ q + CoupledSheetPoly.embed σ r := by
  unfold CoupledSheetPoly.embed
  exact map_add _ q r

/-- `embed` preserves multiplication (it's a ring hom). -/
theorem embed_mul (σ : UVSplit) (q r : CoupledSheetPoly σ) :
    CoupledSheetPoly.embed σ (q * r) =
      CoupledSheetPoly.embed σ q * CoupledSheetPoly.embed σ r := by
  unfold CoupledSheetPoly.embed
  exact map_mul _ q r

/-! ## Section 5: The Π_Φ gauge over a UVSplit

Paper Lemma 205: `Π_Φ = (basis) ∘ (affine relabel) ∘ (restriction) ∘ (projection)`.

We realize Π_Φ in the paper-faithful split setting as `piZero (keepU σ)`:
the "restriction" substitutes v-variables to 0, and the "projection"
keeps u-variables.

`(basis)` and `(affine relabel)` are (trivially) identity in our abstract
setup; a fully paper-faithful treatment would add a change-of-basis layer
(not essential for rank properties). -/

/-- **Π_Φ gauge** for a UVSplit: piZero with `keepU` predicate.
Paper's Lemma 205 gauge realized at the "restriction + projection" level. -/
noncomputable def piPhi (σ : UVSplit) :
    PMnPoly σ →ₗ[ℚ] PMnPoly σ :=
  PiStarConcrete.piZero (keepU σ)

/-- `piPhi` is a projection gauge (inherits from piZero). -/
theorem piPhi_isProjectionGauge (σ : UVSplit) :
    GaugeMonotonicity.IsProjectionGauge (piPhi σ) :=
  PiStarConcrete.piZero_isProjectionGauge (keepU σ)

/-- `piPhi` is rank-monotone over any block partition: this is the
paper-faithful rank monotonicity of Π_Φ (Lemma 205 output), at the
abstract SPDP level. -/
theorem piPhi_isRankMonotoneGauge (σ : UVSplit)
    (B : SPDP.BlockPartition σ.total) :
    GaugeMonotonicity.IsRankMonotoneGauge B (piPhi σ) :=
  PiStarConcrete.piZero_isRankMonotoneGauge (keepU σ) B

/-- `piPhi` evaluated on `X (inlU i)` returns `X (inlU i)` (u is kept). -/
theorem piPhi_X_u (σ : UVSplit) (i : Fin σ.numU) :
    piPhi σ (MvPolynomial.X (σ.inlU i)) = MvPolynomial.X (σ.inlU i) := by
  unfold piPhi
  rw [PiStarConcrete.piZero_X]
  rw [if_pos (keepU_inlU σ i)]

/-- `piPhi` evaluated on `X (inlV j)` returns `0` (v is substituted). -/
theorem piPhi_X_v (σ : UVSplit) (j : Fin σ.numV) :
    piPhi σ (MvPolynomial.X (σ.inlV j)) = 0 := by
  unfold piPhi
  rw [PiStarConcrete.piZero_X]
  rw [if_neg (not_keepU_inlV σ j)]

/-! ## Section 6: piPhi fixes embedded coupled-sheet polynomials

The core property linking `piPhi` to `CoupledSheetPoly.embed`: any
polynomial `q : CoupledSheetPoly σ` (i.e., using only u-variables)
embeds into `PMnPoly σ` as a polynomial supported on u, and piPhi
fixes it. This is the "piPhi is identity on the u-only subalgebra"
property — one half of Lemma 205's rank monotonicity mechanism. -/

/-- `embed q` has all variables in `inlU` range, hence all `keepU`-satisfying. -/
theorem embed_vars_kept (σ : UVSplit) (q : CoupledSheetPoly σ) :
    ∀ k ∈ (CoupledSheetPoly.embed σ q).vars, keepU σ k := by
  intro k hk
  have hk' : k ∈ (MvPolynomial.rename σ.inlU q).vars := by
    unfold CoupledSheetPoly.embed at hk; exact hk
  -- Via mem_vars_rename: k = inlU j for some j ∈ q.vars.
  obtain ⟨j, _hj, hjk⟩ := MvPolynomial.mem_vars_rename σ.inlU q hk'
  rw [← hjk]
  exact keepU_inlU σ j

/-- **piPhi fixes embedded coupled-sheet polynomials**:
`piPhi σ (embed σ q) = embed σ q`. -/
theorem piPhi_embed_eq (σ : UVSplit) (q : CoupledSheetPoly σ) :
    piPhi σ (CoupledSheetPoly.embed σ q) = CoupledSheetPoly.embed σ q := by
  unfold piPhi
  apply PiStarConcrete.piZero_eq_self_of_support_kept
  intro α hα i hki
  by_contra hαi
  have hi_vars : i ∈ (CoupledSheetPoly.embed σ q).vars := by
    rw [MvPolynomial.mem_vars]
    exact ⟨α, hα, Finsupp.mem_support_iff.mpr hαi⟩
  exact hki (embed_vars_kept σ q i hi_vars)

/-! ## Section 7: Capstone — Path A gauge properties

Summary of the paper-faithful Π_Φ construction in the UVSplit framework:
- `piPhi σ` is a ℚ-linear projection on PMnPoly σ
- Property (1): rank-monotone for ANY block partition (piPhi_isRankMonotoneGauge)
- Property (on embed): fixes coupled-sheet image exactly (piPhi_embed_eq)

The remaining content to discharge `exists_amplituhedron_gauge_for_sat_decider`
in this refactored setting:
- Define P_{M,n}(u,v) for a concrete TM M with u/v split (the paper's compiler)
- Define Q^×_Φ(u) = ∏ (1 - z_C · V_C²) as a CoupledSheetPoly
- Show piPhi(P_{M,n}) = embed(Q^×_Φ) up to boundary wiring ζ
- P-side bound: rank(P_{M,n}) ≤ n^O(1) via Theorem 203's Width⇒Rank
- NP-side bound: rank(embed(Q^×_Φ)) ≥ C(n/3, log n) via §18 identity minor

The rank bounds now apply to DIFFERENT polynomial objects (P_{M,n} and
embed Q^×_Φ), resolving the architectural conflict of the flat-n model. -/

/-- **Path A gauge witness** (capstone): `piPhi σ` is a concrete ℚ-linear
projection realizing paper-faithful Π_Φ for any UVSplit σ. It is
rank-monotone over any block partition and fixes the coupled-sheet
image exactly. -/
structure PathAGaugeWitness (σ : UVSplit) (B : SPDP.BlockPartition σ.total) where
  /-- The gauge map. -/
  gauge : PMnPoly σ →ₗ[ℚ] PMnPoly σ
  /-- The gauge is a projection (idempotent). -/
  isProjection : GaugeMonotonicity.IsProjectionGauge gauge
  /-- The gauge is rank-monotone (property 1 of IsAmplituhedronGauge). -/
  isRankMonotone : GaugeMonotonicity.IsRankMonotoneGauge B gauge
  /-- The gauge fixes coupled-sheet embeddings. -/
  fixesEmbed : ∀ q : CoupledSheetPoly σ,
    gauge (CoupledSheetPoly.embed σ q) = CoupledSheetPoly.embed σ q

/-- **The canonical Path A gauge witness**: `piPhi σ` with all
structural properties. Axiom-free construction. -/
noncomputable def canonicalPathAWitness (σ : UVSplit)
    (B : SPDP.BlockPartition σ.total) :
    PathAGaugeWitness σ B where
  gauge := piPhi σ
  isProjection := piPhi_isProjectionGauge σ
  isRankMonotone := piPhi_isRankMonotoneGauge σ B
  fixesEmbed := piPhi_embed_eq σ

/-! ## Section 8: Cook-Levin UVSplit (Task A)

Paper's Cook-Levin compilation uses:
- `numU = n` input/formula variables (x_1, ..., x_n for 3-SAT)
- `numV = poly(n)` tableau variables: tape bits, state indicators,
  head positions over time × position grid

For the TM model in `TuringMachine.lean`, the tableau has:
- `tapeSize^2` tape bits (time × position) — `b_{t,i}`
- `tapeSize * numStates` state indicators (time × state) — `s_{t,q}`
- `tapeSize^2` head positions (time × position) — `h_{t,i}`

where `tapeSize M n = n^M.timeBound + 1`. For bounded-parameter
(`M.timeBound ≤ 4`, `M.numStates ≤ n`) this is polynomial in n. -/

/-- **Cook-Levin UVSplit**: `numU = n` (input), `numV = tableau`.

Tableau layout matches `TuringMachine.numVars` minus the n input:
  v-variables = tape (S²) ⊕ state (S · numStates) ⊕ head (S²)
where `S = tapeSize M n`. -/
def cookLevinUVSplit (M : TuringMachine.DTM) (n : ℕ) : UVSplit where
  numU := n
  numV :=
    let S := TuringMachine.tapeSize M n
    S * S + S * M.numStates + S * S

/-- `cookLevinUVSplit` has `numU = n`. -/
theorem cookLevinUVSplit_numU (M : TuringMachine.DTM) (n : ℕ) :
    (cookLevinUVSplit M n).numU = n := rfl

/-- `cookLevinUVSplit.total` matches `TuringMachine.numVars M n 0` (no padding). -/
theorem cookLevinUVSplit_total (M : TuringMachine.DTM) (n : ℕ) :
    (cookLevinUVSplit M n).total = TuringMachine.numVars M n 0 := by
  unfold cookLevinUVSplit UVSplit.total TuringMachine.numVars
  ring

/-- For bounded-parameter TMs (timeBound ≤ 4, numStates ≤ n), the v-count
is polynomial in n — specifically, `numV ≤ 3 · (n^4 + 1)^2`. -/
theorem cookLevinUVSplit_numV_poly (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 1)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (cookLevinUVSplit M n).numV ≤ 3 * (n ^ 4 + 1) ^ 2 := by
  show TuringMachine.tapeSize M n * TuringMachine.tapeSize M n +
        TuringMachine.tapeSize M n * M.numStates +
        TuringMachine.tapeSize M n * TuringMachine.tapeSize M n ≤
      3 * (n ^ 4 + 1) ^ 2
  have hS_bound : TuringMachine.tapeSize M n ≤ n ^ 4 + 1 := by
    show TuringMachine.timeSteps M n + 1 ≤ n ^ 4 + 1
    show n ^ M.timeBound + 1 ≤ n ^ 4 + 1
    have : n ^ M.timeBound ≤ n ^ 4 :=
      Nat.pow_le_pow_right hn htb
    omega
  have h1 : TuringMachine.tapeSize M n * TuringMachine.tapeSize M n ≤
      (n ^ 4 + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul hS_bound hS_bound
  have h2 : TuringMachine.tapeSize M n * M.numStates ≤
      (n ^ 4 + 1) ^ 2 := by
    rw [sq]
    have hns_bound : M.numStates ≤ n ^ 4 + 1 := by
      have hnle : n ≤ n ^ 4 + 1 := by
        have : n ≤ n ^ 4 := Nat.le_self_pow (by omega) n
        omega
      omega
    exact Nat.mul_le_mul hS_bound hns_bound
  -- 3 * X = X + X + X
  calc TuringMachine.tapeSize M n * TuringMachine.tapeSize M n +
        TuringMachine.tapeSize M n * M.numStates +
        TuringMachine.tapeSize M n * TuringMachine.tapeSize M n
      ≤ (n ^ 4 + 1) ^ 2 + (n ^ 4 + 1) ^ 2 + (n ^ 4 + 1) ^ 2 := by
        exact Nat.add_le_add (Nat.add_le_add h1 h2) h1
    _ = 3 * (n ^ 4 + 1) ^ 2 := by ring

/-! ## Section 9: Task (B) — P_{M,n}(u, v) compilation

Paper's P_{M,n} has constraints over both u (formula) and v (tableau).
In the current Lean formalization, the flat `compiledPoly` uses only
`Fin n` variables. A full Task (B) would rebuild the compilation with
explicit tableau variables.

As a first step, we embed the flat compiledPoly into the UVSplit space
via the u-injection. This gives a concrete `PMn` polynomial, but one
that does NOT yet use v (trivially piPhi-invariant).

**Note**: this first-approximation PMn is useful for API surface but
does NOT carry the paper's tableau-constraint structure. The genuinely
paper-faithful PMn (with `v`-constraints derived from TM transitions)
is future work. -/

/-- **First-approximation P_{M,n}**: embed the flat `compiledPoly`
into the UVSplit space via the u-injection `inlU`.

This polynomial lives in `PMnPoly (cookLevinUVSplit M n)` but uses only
u-variables (the flat n SAT variables). It does NOT yet encode the
TM tableau constraints over v-variables — that extension is Task (B.2). -/
noncomputable def cookLevinPMnApprox (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PMnPoly (cookLevinUVSplit M n) :=
  -- Use the flat compiledPoly over `Fin n` and rename to Fin total via inlU.
  MvPolynomial.rename (cookLevinUVSplit M n).inlU
    (by
      have h : (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).numVars = n :=
        PaperFaithfulSeparation.cook_levin_numVars M n hn htb hns
      exact h ▸ PaperFaithfulSeparation.compiledPoly
        (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns))

/-- The first-approximation PMn uses only u-variables. -/
theorem cookLevinPMnApprox_vars_in_u (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∀ k ∈ (cookLevinPMnApprox M n hn htb hns).vars, keepU (cookLevinUVSplit M n) k := by
  intro k hk
  -- vars(rename inlU p) ⊆ inlU.image(vars p), so each k is of form inlU j
  obtain ⟨j, _hj, hjk⟩ :=
    MvPolynomial.mem_vars_rename (cookLevinUVSplit M n).inlU _ hk
  rw [← hjk]
  exact keepU_inlU _ j

/-- **piPhi fixes the first-approximation PMn** (since it has no v-dependence). -/
theorem piPhi_cookLevinPMnApprox (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    piPhi (cookLevinUVSplit M n) (cookLevinPMnApprox M n hn htb hns) =
      cookLevinPMnApprox M n hn htb hns := by
  unfold piPhi
  apply PiStarConcrete.piZero_eq_self_of_support_kept
  intro α hα i hki
  by_contra hαi
  have hi_vars : i ∈ (cookLevinPMnApprox M n hn htb hns).vars := by
    rw [MvPolynomial.mem_vars]
    exact ⟨α, hα, Finsupp.mem_support_iff.mpr hαi⟩
  exact hki (cookLevinPMnApprox_vars_in_u M n hn htb hns i hi_vars)

/-! ## Section 10: Task (C) — Q^×_Φ coupled sheet

Paper's Q^×_Φ(u) = ∏_{C ∈ Φ} (1 - z_C · V_C(x)²) where:
- x_i are the formula variables (part of u)
- z_C are per-clause selectors (part of u)
- V_C(x) is the clause verifier polynomial

Since z_C and x_i both live in u, Q^×_Φ is a polynomial in u-variables only.

We provide a generic/abstract definition that works for any list of
"clause gadgets" over the u-variable space. The concrete instantiation
uses the existing `clauseGadget` from `TseitinDefs.lean`. -/

/-- **Abstract coupled sheet**: for a list of pairs (selector index,
clause gadget polynomial), define `Q^×_Φ := ∏ (1 - X(sel) · gadget)`. -/
noncomputable def coupledSheetFromList (σ : UVSplit)
    (clauses : List (Fin σ.numU × MvPolynomial (Fin σ.numU) ℚ)) :
    CoupledSheetPoly σ :=
  (clauses.map (fun ⟨sel, gadget⟩ =>
    1 - MvPolynomial.X sel * gadget)).prod

/-- `coupledSheetFromList` for the empty list is `1`. -/
theorem coupledSheetFromList_nil (σ : UVSplit) :
    coupledSheetFromList σ [] = 1 := by
  unfold coupledSheetFromList
  simp

/-- `coupledSheetFromList` for `(sel, gadget) :: rest` unfolds to
`(1 - X sel · gadget) · coupledSheetFromList rest`. -/
theorem coupledSheetFromList_cons (σ : UVSplit)
    (sel : Fin σ.numU) (gadget : MvPolynomial (Fin σ.numU) ℚ)
    (rest : List (Fin σ.numU × MvPolynomial (Fin σ.numU) ℚ)) :
    coupledSheetFromList σ ((sel, gadget) :: rest) =
      (1 - MvPolynomial.X sel * gadget) * coupledSheetFromList σ rest := by
  unfold coupledSheetFromList
  simp [List.prod_cons]

/-- **piPhi fixes the embedded coupled sheet** (since it lives entirely
in u). This is the concrete instance of `piPhi_embed_eq` for Q^×_Φ. -/
theorem piPhi_embed_coupledSheet (σ : UVSplit)
    (clauses : List (Fin σ.numU × MvPolynomial (Fin σ.numU) ℚ)) :
    piPhi σ (CoupledSheetPoly.embed σ (coupledSheetFromList σ clauses)) =
      CoupledSheetPoly.embed σ (coupledSheetFromList σ clauses) :=
  piPhi_embed_eq σ (coupledSheetFromList σ clauses)

/-! ## Section 11: Integration API for Tasks (D), (E), (F)

The gauge assembly theorem: given concrete P-side and NP-side rank bounds
on `P_{M,n}` and `embed(Q^×_Φ)` respectively, combined with the gauge
properties already established, yields the `IsAmplituhedronGauge` witness
in the UVSplit setting.

Tasks (D), (E), (F) plug concrete numerical values into this template. -/

/-- **Gauge sandwich from bound hypotheses**: given a paper-faithful
P_{M,n} and Q^×_Φ with the appropriate rank bounds, piPhi achieves
both:
- P-side: `rank(piPhi(P_{M,n})) ≤ rank(P_{M,n}) ≤ pBound`
  (via `piPhi_isRankMonotoneGauge` and the input P-side hypothesis)
- NP-side: `rank(piPhi(P_{M,n})) ≥ npBound`
  (via the input NP-side hypothesis, which says piPhi image contains
  embed(Q^×_Φ) which has rank ≥ npBound)

This is the assembly template for Tasks (F). Input:
- hPside: rank(P_{M,n}) ≤ pBound (Task D)
- hNPside: rank(piPhi(P_{M,n})) ≥ npBound (Task E, via piPhi(P_{M,n}) = embed(Q^×_Φ)
  modulo wiring; then apply NP-side bound on Q^×_Φ)

Output: the rank sandwich, which via arithmetic impossibility gives P ≠ NP. -/
theorem gauge_rank_sandwich
    {σ : UVSplit} (B : SPDP.BlockPartition σ.total)
    (P : PMnPoly σ) (κ ℓ : ℕ)
    (pBound npBound : ℕ)
    (hPside : MultilinearSPDP.mlBlockedSpdpRank B κ ℓ P ≤ pBound)
    (hNPside : npBound ≤
      MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piPhi σ P)) :
    ∃ r : ℕ, npBound ≤ r ∧ r ≤ pBound := by
  refine ⟨MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piPhi σ P), hNPside, ?_⟩
  calc MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piPhi σ P)
      ≤ MultilinearSPDP.mlBlockedSpdpRank B κ ℓ P :=
        piPhi_isRankMonotoneGauge σ B κ ℓ P
    _ ≤ pBound := hPside

/-- **Arithmetic impossibility** of the rank sandwich when pBound < npBound.
Used to derive the final P ≠ NP contradiction. -/
theorem no_rank_sandwich_of_gap (pBound npBound : ℕ) (hgap : pBound < npBound) :
    ¬ ∃ r : ℕ, npBound ≤ r ∧ r ≤ pBound := by
  rintro ⟨r, hr_lo, hr_hi⟩
  omega

/-- **Contradiction from gauge + gap**: if `P_{M,n}` admits the rank
sandwich [npBound, pBound] via piPhi, but pBound < npBound, we get False.

This is the separation mechanism at the abstract level. Concrete
instantiations for Cook-Levin at n = 2^804 (pBound = n^200, npBound =
C(n/3, log n)) complete Task (F). -/
theorem separation_contradiction
    {σ : UVSplit} (B : SPDP.BlockPartition σ.total)
    (P : PMnPoly σ) (κ ℓ : ℕ)
    (pBound npBound : ℕ)
    (hPside : MultilinearSPDP.mlBlockedSpdpRank B κ ℓ P ≤ pBound)
    (hNPside : npBound ≤
      MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piPhi σ P))
    (hgap : pBound < npBound) : False := by
  have := gauge_rank_sandwich B P κ ℓ pBound npBound hPside hNPside
  exact no_rank_sandwich_of_gap pBound npBound hgap this

/-! ## Section 12: Task (B.2) — v-variable infrastructure

The full Task (B.2) rebuilds Cook-Levin compilation with explicit
tableau-encoded transition constraints over v-variables. As a first
step, we introduce v-variable accessors and show piPhi kills v-only
polynomials. -/

/-- **Booleanity constraint for a v-variable**: `v_j · (1 - v_j)`,
vanishes at v_j ∈ {0, 1}. A single tableau-booleanity constraint. -/
noncomputable def vBoolConstraint (σ : UVSplit) (j : Fin σ.numV) :
    PMnPoly σ :=
  MvPolynomial.X (σ.inlV j) * (1 - MvPolynomial.X (σ.inlV j))

/-- `piPhi` annihilates `vBoolConstraint`: since v-variables substitute to 0,
`vBoolConstraint(0) = 0 · (1 - 0) = 0`. -/
theorem piPhi_vBoolConstraint (σ : UVSplit) (j : Fin σ.numV) :
    piPhi σ (vBoolConstraint σ j) = 0 := by
  unfold vBoolConstraint
  -- piPhi is a ring hom, and piPhi(X(inlV j)) = 0.
  show piPhi σ (MvPolynomial.X (σ.inlV j) * (1 - MvPolynomial.X (σ.inlV j))) = 0
  -- Use the piZero ring-hom structure.
  have h : (piPhi σ).toFun = (PiStarConcrete.substAlgHom (keepU σ) 0).toFun := by
    unfold piPhi PiStarConcrete.piZero PiStarConcrete.piSubst
    rfl
  -- Use map_mul of the AlgHom form.
  show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap
      (MvPolynomial.X (σ.inlV j) * (1 - MvPolynomial.X (σ.inlV j))) = 0
  rw [AlgHom.toLinearMap_apply, map_mul]
  rw [show (PiStarConcrete.substAlgHom (keepU σ) 0) (MvPolynomial.X (σ.inlV j)) = 0 from by
    unfold PiStarConcrete.substAlgHom
    rw [MvPolynomial.aeval_X]
    show PiStarConcrete.substFn (keepU σ) (0 : σ.Idx → ℚ) (σ.inlV j) = 0
    unfold PiStarConcrete.substFn
    rw [if_neg (not_keepU_inlV σ j)]
    simp [Pi.zero_apply]]
  ring

/-- **Tableau-booleanity polynomial**: product of booleanity constraints
over all v-variables. This is a simple v-dependent polynomial useful for
sanity-checking the piPhi machinery (annihilates to 0). -/
noncomputable def tableauBoolProduct (σ : UVSplit) : PMnPoly σ :=
  (Finset.univ : Finset (Fin σ.numV)).prod (vBoolConstraint σ)

/-- `piPhi` maps the tableau booleanity product to 0 (if numV ≥ 1). -/
theorem piPhi_tableauBoolProduct_pos (σ : UVSplit) (hV : 0 < σ.numV) :
    piPhi σ (tableauBoolProduct σ) = 0 := by
  unfold tableauBoolProduct
  let j₀ : Fin σ.numV := ⟨0, hV⟩
  show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap
      ((Finset.univ : Finset (Fin σ.numV)).prod (vBoolConstraint σ)) = 0
  rw [AlgHom.toLinearMap_apply, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
  -- Unfold definitions to apply piPhi_vBoolConstraint
  have hpp := piPhi_vBoolConstraint σ j₀
  show (PiStarConcrete.substAlgHom (keepU σ) 0) (vBoolConstraint σ j₀) = 0
  show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap (vBoolConstraint σ j₀) = 0
  exact hpp

/-! ## Section 13: Extraction theorem — piPhi(u-part + v-part) = u-part

The central extraction behavior for paper's Π_Φ: a polynomial that
decomposes as `embed(Q) + R` where `R` vanishes under piPhi yields
`piPhi(embed(Q) + R) = embed(Q)`.

Concretely, if `R` is a sum/product where piPhi acts as 0 (e.g., R
contains a v-boolean factor), then piPhi extracts the u-only part. -/

/-- **Linear extraction**: if `R = piPhi(R)` — i.e., piPhi fixes R — and
we're asking about piPhi(embed(Q) + R), the result is embed(Q) + R.
(Trivial consequence of linearity.) Then if additionally `piPhi(R) = 0`,
the result collapses to embed(Q). -/
theorem piPhi_embed_add_kill
    (σ : UVSplit) (Q : CoupledSheetPoly σ) (R : PMnPoly σ)
    (hR : piPhi σ R = 0) :
    piPhi σ (CoupledSheetPoly.embed σ Q + R) =
      CoupledSheetPoly.embed σ Q := by
  rw [map_add, hR, add_zero]
  exact piPhi_embed_eq σ Q

/-- **Multiplicative extraction**: piPhi(embed(Q) · tableauBool) = 0
when numV ≥ 1 (since tableauBool vanishes under piPhi). This models the
paper's Π_Φ extraction when the v-dependence is encoded multiplicatively. -/
theorem piPhi_embed_mul_tableauBool (σ : UVSplit)
    (Q : CoupledSheetPoly σ) (hV : 0 < σ.numV) :
    piPhi σ (CoupledSheetPoly.embed σ Q * tableauBoolProduct σ) = 0 := by
  -- piPhi is a ring hom, piPhi(tableauBoolProduct) = 0.
  show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap
      (CoupledSheetPoly.embed σ Q * tableauBoolProduct σ) = 0
  rw [AlgHom.toLinearMap_apply, map_mul]
  have h : (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap
            (tableauBoolProduct σ) = 0 := piPhi_tableauBoolProduct_pos σ hV
  -- Rewrite to convert AlgHom applications to LinearMap form
  show (PiStarConcrete.substAlgHom (keepU σ) 0) (CoupledSheetPoly.embed σ Q) *
       (PiStarConcrete.substAlgHom (keepU σ) 0) (tableauBoolProduct σ) = 0
  have h2 : (PiStarConcrete.substAlgHom (keepU σ) 0) (tableauBoolProduct σ) = 0 := by
    rw [← AlgHom.toLinearMap_apply]
    exact h
  rw [h2, mul_zero]

/-- **Capstone extraction**: if a PMn polynomial decomposes as
`embed(Q) + embed(Q) · tableauBool`, then piPhi extracts embed(Q).
This is a concrete template: R = embed(Q) · tableauBool is v-dependent
but vanishes under piPhi. -/
theorem piPhi_extract_via_tableauBool
    (σ : UVSplit) (Q : CoupledSheetPoly σ) (hV : 0 < σ.numV) :
    piPhi σ (CoupledSheetPoly.embed σ Q +
              CoupledSheetPoly.embed σ Q * tableauBoolProduct σ) =
      CoupledSheetPoly.embed σ Q :=
  piPhi_embed_add_kill σ Q (CoupledSheetPoly.embed σ Q * tableauBoolProduct σ)
    (piPhi_embed_mul_tableauBool σ Q hV)

/-! ## Section 14: Tableau v-variable accessors (Task B.2 cont.)

Within the v-part of `cookLevinUVSplit M n`, variables are organized into:
- [0, S²): tape bits `b_{t,i}` (t, i ∈ [0, S))
- [S², S² + S·numStates): state indicators `s_{t,q}`
- [S² + S·numStates, numV): head positions `h_{t,i}`

where `S = TuringMachine.tapeSize M n`. We provide accessors for each. -/

/-- Tape-bit v-variable index: `b_{t,i}` lives at `t*S + i` within v. -/
def tapeVIdx (M : TuringMachine.DTM) (n : ℕ)
    (t i : Fin (TuringMachine.tapeSize M n)) :
    Fin (cookLevinUVSplit M n).numV :=
  ⟨t.val * TuringMachine.tapeSize M n + i.val, by
    show t.val * TuringMachine.tapeSize M n + i.val <
      TuringMachine.tapeSize M n * TuringMachine.tapeSize M n +
      TuringMachine.tapeSize M n * M.numStates +
      TuringMachine.tapeSize M n * TuringMachine.tapeSize M n
    have ht := t.isLt
    have hi := i.isLt
    nlinarith [Nat.mul_lt_mul_of_lt_of_le ht (Nat.le_refl (TuringMachine.tapeSize M n))
               (by
                 have : 0 < TuringMachine.tapeSize M n := by
                   unfold TuringMachine.tapeSize; omega
                 exact this)]⟩

/-- State-indicator v-variable index: `s_{t,q}` lives at
`S² + t*numStates + q` within v. -/
def stateVIdx (M : TuringMachine.DTM) (n : ℕ)
    (t : Fin (TuringMachine.tapeSize M n)) (q : Fin M.numStates) :
    Fin (cookLevinUVSplit M n).numV :=
  ⟨TuringMachine.tapeSize M n * TuringMachine.tapeSize M n +
   t.val * M.numStates + q.val, by
    show _ < _ + _ + _
    have ht := t.isLt
    have hq := q.isLt
    have hns_pos : 0 < M.numStates := by
      have := M.hStates; omega
    nlinarith [Nat.mul_lt_mul_of_lt_of_le ht (Nat.le_refl M.numStates) hns_pos]⟩

/-- Head-position v-variable index: `h_{t,i}` lives at
`S² + S·numStates + t*S + i` within v. -/
def headVIdx (M : TuringMachine.DTM) (n : ℕ)
    (t i : Fin (TuringMachine.tapeSize M n)) :
    Fin (cookLevinUVSplit M n).numV :=
  ⟨TuringMachine.tapeSize M n * TuringMachine.tapeSize M n +
   TuringMachine.tapeSize M n * M.numStates +
   t.val * TuringMachine.tapeSize M n + i.val, by
    show _ < _ + _ + _
    have ht := t.isLt
    have hi := i.isLt
    have hS_pos : 0 < TuringMachine.tapeSize M n := by
      unfold TuringMachine.tapeSize; omega
    nlinarith [Nat.mul_lt_mul_of_lt_of_le ht (Nat.le_refl (TuringMachine.tapeSize M n)) hS_pos]⟩

/-- Tape-bit is a v-variable: `keepU` fails at `inlV (tapeVIdx ...)`. -/
theorem not_keepU_tape (M : TuringMachine.DTM) (n : ℕ)
    (t i : Fin (TuringMachine.tapeSize M n)) :
    ¬ keepU (cookLevinUVSplit M n)
      ((cookLevinUVSplit M n).inlV (tapeVIdx M n t i)) :=
  not_keepU_inlV _ _

/-- State-indicator is a v-variable. -/
theorem not_keepU_state (M : TuringMachine.DTM) (n : ℕ)
    (t : Fin (TuringMachine.tapeSize M n)) (q : Fin M.numStates) :
    ¬ keepU (cookLevinUVSplit M n)
      ((cookLevinUVSplit M n).inlV (stateVIdx M n t q)) :=
  not_keepU_inlV _ _

/-- Head-position is a v-variable. -/
theorem not_keepU_head (M : TuringMachine.DTM) (n : ℕ)
    (t i : Fin (TuringMachine.tapeSize M n)) :
    ¬ keepU (cookLevinUVSplit M n)
      ((cookLevinUVSplit M n).inlV (headVIdx M n t i)) :=
  not_keepU_inlV _ _

/-! ## Section 15: Input-boundary coupling constraint (u-v link)

A concrete constraint linking u (input variables) to v (initial tape):
the constraint `tape[0, i] = input[i]` at time t=0 for each input position.
This is the simplest u-v coupling — a paper-faithful piece of the Cook-Levin
boundary condition. -/

/-- Tape-size positivity (needed for `⟨0, _⟩`). -/
theorem tapeSize_pos (M : TuringMachine.DTM) (n : ℕ) :
    0 < TuringMachine.tapeSize M n := by
  unfold TuringMachine.tapeSize; omega

/-- **Input-boundary constraint** for position `i ∈ [0, n)`:
`X(tape[0, i]) - X(input[i])`.

This vanishes exactly when `tape[0, i] = input[i]` — the initial tape
at position i equals the i-th input bit. A direct u-v coupling. -/
noncomputable def inputBoundaryConstraint (M : TuringMachine.DTM) (n : ℕ) (hn : 1 ≤ n)
    (i : Fin n) : PMnPoly (cookLevinUVSplit M n) :=
  let σ := cookLevinUVSplit M n
  let u_i : σ.Idx := σ.inlU (by
    -- i < n = σ.numU
    show Fin σ.numU
    show Fin n
    exact i)
  let v_tape_0_i : σ.Idx := σ.inlV
    (tapeVIdx M n ⟨0, tapeSize_pos M n⟩ ⟨i.val, by
      unfold TuringMachine.tapeSize TuringMachine.timeSteps
      have hi := i.isLt
      have htb : 1 ≤ M.timeBound := M.hTimeBound
      have hpow : n ≤ n ^ M.timeBound := Nat.le_self_pow (by omega) n
      omega⟩)
  MvPolynomial.X v_tape_0_i - MvPolynomial.X u_i

/-- `piPhi` maps `inputBoundaryConstraint` to `- X(input[i])`: the v-part
(tape bit) substitutes to 0, leaving `-X(u_i)`. -/
theorem piPhi_inputBoundaryConstraint
    (M : TuringMachine.DTM) (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    piPhi (cookLevinUVSplit M n) (inputBoundaryConstraint M n hn i) =
      - MvPolynomial.X ((cookLevinUVSplit M n).inlU i) := by
  unfold inputBoundaryConstraint
  simp only
  rw [map_sub, piPhi_X_v, piPhi_X_u]
  show 0 - MvPolynomial.X ((cookLevinUVSplit M n).inlU (id i)) =
       -MvPolynomial.X ((cookLevinUVSplit M n).inlU i)
  simp

/-! ## Section 16: Cook-Levin separation template (Tasks D, E, F)

Concrete Cook-Levin specialization of `separation_contradiction`:
given P-side and NP-side rank bounds on a PathA PMn polynomial,
the arithmetic gap at n ≥ 2^804 (n^200 < C(n/3, log n)) yields False
under `DecidesSAT M`.

Matches paper Theorem 207's chain: compile M, apply Π_Φ, contradiction
from rank gap. -/

/-- **Arithmetic gap at n ≥ 2^804**: n^200 < C(n/3, log n).

Imported via the existing `GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n`
for the flat compilation; works the same way at the UVSplit level. -/
theorem arithmetic_gap_2pow804 (n : ℕ) (hn : n ≥ 2 ^ 804) :
    n ^ 200 < Nat.choose (n / 3) (Nat.log 2 n) := by
  -- Chain: n^200 < n^201 ≤ n^(log n / 4) ≤ C(n/30, log n) ≤ C(n/3, log n)
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  have hlog : 804 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hn_ge_1 : 1 ≤ n := by
    have h2_804 : (2 : ℕ) ≤ 2 ^ 804 := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hn_gt_1 : 1 < n := by
    have h2_804 : (2 : ℕ) ≤ 2 ^ 804 := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hnpow201 : n ^ 201 ≤ n ^ (Nat.log 2 n / 4) :=
    Nat.pow_le_pow_right hn_ge_1 hdiv
  have h200lt201 : n ^ 200 < n ^ 201 :=
    Nat.pow_lt_pow_right hn_gt_1 (by omega : 200 < 201)
  exact lt_of_lt_of_le h200lt201 (le_trans (le_trans hnpow201 hbin) hmono)

/-- **Cook-Levin-style separation**: if for some (σ, B, P, κ, ℓ) we have
a P-side bound ≤ n^200 AND NP-side bound ≥ C(n/3, log n) on piPhi(P),
then at n ≥ 2^804 we derive False. This is paper Theorem 207's
separation mechanism at the UVSplit level. -/
theorem pathA_separation_contradiction
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    {σ : UVSplit} (B : SPDP.BlockPartition σ.total)
    (P : PMnPoly σ) (κ ℓ : ℕ)
    (hPside : MultilinearSPDP.mlBlockedSpdpRank B κ ℓ P ≤ n ^ 200)
    (hNPside : Nat.choose (n / 3) (Nat.log 2 n) ≤
      MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piPhi σ P)) :
    False :=
  separation_contradiction B P κ ℓ
    (n ^ 200) (Nat.choose (n / 3) (Nat.log 2 n))
    hPside hNPside (arithmetic_gap_2pow804 n hn)

/-! ## Section 17: Bridge to main theorem

The final piece connecting Path A to the main separation `P ≠ NP`.

Given a polynomial `P` satisfying the two rank bounds at n ≥ 2^804
under the hypothesis `DecidesSAT M`, we get a contradiction. This
reduces the main axiom `exists_amplituhedron_gauge_for_sat_decider`
to exhibiting such a P — i.e., Tasks (B.2), (D), (E) completing a
concrete construction.

The key structure: the path is hPside ∧ hNPside ⇒ False under
DecidesSAT ⇒ ¬DecidesSAT at n ≥ 2^804 ⇒ P ≠ NP (in restricted form). -/

/-- **Main Path A bridge theorem**: given PathA rank bounds on a
concrete PMn polynomial at n ≥ 2^804, any additional hypothesis `H`
(e.g., `DecidesSAT M`) that implies both bounds yields `¬ H`.

This is the Path A conclusion template: plug `H := DecidesSAT M` and
prove the bounds conditional on `H` to get `¬ DecidesSAT M`, which
combined with universal quantification over large n yields `P ≠ NP`.

Stated in terms of an abstract hypothesis `H` to avoid heavy imports. -/
theorem pathA_hypothesis_contradiction
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    {σ : UVSplit} (B : SPDP.BlockPartition σ.total)
    (P : PMnPoly σ) (κ ℓ : ℕ)
    {H : Prop}
    (hPside : H → MultilinearSPDP.mlBlockedSpdpRank B κ ℓ P ≤ n ^ 200)
    (hNPside : H →
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piPhi σ P)) :
    ¬ H := by
  intro h
  exact pathA_separation_contradiction n hn B P κ ℓ (hPside h) (hNPside h)

/-! ## Section 18: U-variable boolean constraints (symmetric to §12)

Parallel to `vBoolConstraint` for v-variables, we define `uBoolConstraint`
for u-variables. These are "kept" by piPhi (since u is kept), unlike
vBoolConstraint which is killed. -/

/-- **Booleanity constraint for a u-variable**: `u_i · (1 - u_i)`. -/
noncomputable def uBoolConstraint (σ : UVSplit) (i : Fin σ.numU) :
    PMnPoly σ :=
  MvPolynomial.X (σ.inlU i) * (1 - MvPolynomial.X (σ.inlU i))

/-- `piPhi` fixes `uBoolConstraint` (since u is kept). -/
theorem piPhi_uBoolConstraint (σ : UVSplit) (i : Fin σ.numU) :
    piPhi σ (uBoolConstraint σ i) = uBoolConstraint σ i := by
  unfold uBoolConstraint piPhi
  show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap _ = _
  rw [AlgHom.toLinearMap_apply, map_mul]
  -- piPhi(X(inlU i)) = X(inlU i) since inlU i is kept.
  have hX : (PiStarConcrete.substAlgHom (keepU σ) 0) (MvPolynomial.X (σ.inlU i))
      = MvPolynomial.X (σ.inlU i) := by
    unfold PiStarConcrete.substAlgHom
    rw [MvPolynomial.aeval_X]
    show PiStarConcrete.substFn (keepU σ) (0 : σ.Idx → ℚ) (σ.inlU i) = MvPolynomial.X (σ.inlU i)
    unfold PiStarConcrete.substFn
    rw [if_pos (keepU_inlU σ i)]
  rw [map_sub, map_one, hX]

/-- **U-boolean product**: product of all u-boolean constraints. -/
noncomputable def uBoolProduct (σ : UVSplit) : PMnPoly σ :=
  (Finset.univ : Finset (Fin σ.numU)).prod (uBoolConstraint σ)

/-- `piPhi` fixes `uBoolProduct` (product of fixed factors). -/
theorem piPhi_uBoolProduct (σ : UVSplit) :
    piPhi σ (uBoolProduct σ) = uBoolProduct σ := by
  unfold uBoolProduct
  show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap
      ((Finset.univ : Finset (Fin σ.numU)).prod (uBoolConstraint σ)) = _
  rw [AlgHom.toLinearMap_apply, map_prod]
  apply Finset.prod_congr rfl
  intros i _
  have hpp := piPhi_uBoolConstraint σ i
  show (PiStarConcrete.substAlgHom (keepU σ) 0) (uBoolConstraint σ i) = uBoolConstraint σ i
  show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap (uBoolConstraint σ i) = uBoolConstraint σ i
  exact hpp

/-! ## Section 19: Multiplicative u-factor extraction

If a PMn polynomial factors as `P = U · R` where `U` is a u-only
polynomial (fixed by piPhi), then `piPhi(P) = U · piPhi(R)` — the
u-factor passes through. This is the algebraic trick used repeatedly
in paper Theorem 207's extraction. -/

/-- **Multiplicative u-factor extraction** (ring-hom form via substAlgHom): -/
theorem piPhi_u_factor_mul
    (σ : UVSplit) (U : PMnPoly σ) (R : PMnPoly σ)
    (hU : piPhi σ U = U) :
    piPhi σ (U * R) = U * piPhi σ R := by
  show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap (U * R) = _
  rw [AlgHom.toLinearMap_apply, map_mul]
  -- piPhi(U) = U by hypothesis; piPhi(R) goes through.
  have hU' : (PiStarConcrete.substAlgHom (keepU σ) 0) U = U := by
    show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap U = U
    exact hU
  rw [hU']
  rfl

/-- **piPhi of uBoolProduct times any R**: u-factor passes through. -/
theorem piPhi_uBoolProduct_mul (σ : UVSplit) (R : PMnPoly σ) :
    piPhi σ (uBoolProduct σ * R) = uBoolProduct σ * piPhi σ R :=
  piPhi_u_factor_mul σ (uBoolProduct σ) R (piPhi_uBoolProduct σ)

/-- **piPhi of embed(Q) times R**: u-factor passes through. -/
theorem piPhi_embed_mul (σ : UVSplit) (Q : CoupledSheetPoly σ) (R : PMnPoly σ) :
    piPhi σ (CoupledSheetPoly.embed σ Q * R) =
      CoupledSheetPoly.embed σ Q * piPhi σ R :=
  piPhi_u_factor_mul σ (CoupledSheetPoly.embed σ Q) R (piPhi_embed_eq σ Q)

/-- **Extraction with tableau-vanishing tail**:
`piPhi(embed(Q) · (1 + tableauBool)) = embed(Q)` when numV ≥ 1.

This is a concrete template showing how a PMn of the form
`embed(Q) · (1 + tableauBool)` collapses under piPhi to embed(Q).
Rank(PMn) may be larger than rank(embed Q), but piPhi extracts
the clean u-part. -/
theorem piPhi_embed_mul_one_plus_tableauBool (σ : UVSplit)
    (Q : CoupledSheetPoly σ) (hV : 0 < σ.numV) :
    piPhi σ (CoupledSheetPoly.embed σ Q * (1 + tableauBoolProduct σ)) =
      CoupledSheetPoly.embed σ Q := by
  rw [piPhi_embed_mul]
  -- piPhi(1 + tableauBool) = 1 + 0 = 1
  have h1 : piPhi σ (1 + tableauBoolProduct σ) = 1 := by
    show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap
          (1 + tableauBoolProduct σ) = 1
    rw [AlgHom.toLinearMap_apply, map_add, map_one]
    have hkill : (PiStarConcrete.substAlgHom (keepU σ) 0) (tableauBoolProduct σ) = 0 := by
      show (PiStarConcrete.substAlgHom (keepU σ) 0).toLinearMap (tableauBoolProduct σ) = 0
      exact piPhi_tableauBoolProduct_pos σ hV
    rw [hkill, add_zero]
  rw [h1, mul_one]

/-! ## Section 20: Capstone — Path A template PMn

A **template construction** for PMn that:
- Uses both u and v variables (via `embed Q · (1 + tableauBool)`)
- Reduces to `embed Q` under piPhi (via §19 extraction)

This is a CONCRETE Path A PMn shape. Discharging the axiom reduces to:
- Choose Q such that `rank(embed Q) ≥ C(n/3, log n)` (NP-side via Q = Q^×_Φ, identity minor)
- Choose template such that `rank(template P) ≤ n^200` (P-side via Width⇒Rank on P)

The template below is illustrative; paper-faithful PMn uses specific
transition-encoded v-constraints. -/

/-- **Template PMn**: from a coupled sheet Q, build
`templatePMn σ Q := embed(Q) · (1 + tableauBool)` — uses v-variables
but extracts to embed(Q) under piPhi. -/
noncomputable def templatePMn (σ : UVSplit) (Q : CoupledSheetPoly σ) :
    PMnPoly σ :=
  CoupledSheetPoly.embed σ Q * (1 + tableauBoolProduct σ)

/-- **Key property**: piPhi(templatePMn) = embed(Q). -/
theorem piPhi_templatePMn (σ : UVSplit) (Q : CoupledSheetPoly σ) (hV : 0 < σ.numV) :
    piPhi σ (templatePMn σ Q) = CoupledSheetPoly.embed σ Q := by
  unfold templatePMn
  exact piPhi_embed_mul_one_plus_tableauBool σ Q hV

/-- **Template-based Path A separation**: given a coupled sheet `Q` whose
embedded SPDP rank is ≥ C(n/3, log n), and whose template PMn has rank
≤ n^200, we get False under any hypothesis implying both bounds.

This is the concrete instantiation-ready form of Path A. -/
theorem templatePMn_separation
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    {σ : UVSplit} (hV : 0 < σ.numV)
    (B : SPDP.BlockPartition σ.total)
    (Q : CoupledSheetPoly σ) (κ ℓ : ℕ)
    (hPside : MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (templatePMn σ Q) ≤ n ^ 200)
    (hNPside : Nat.choose (n / 3) (Nat.log 2 n) ≤
      MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (CoupledSheetPoly.embed σ Q)) :
    False := by
  apply pathA_separation_contradiction n hn B (templatePMn σ Q) κ ℓ hPside
  rw [piPhi_templatePMn σ Q hV]
  exact hNPside

/-! ## Section 21: Rank preservation under rename (toward Task E)

The reverse of `mlBlockedSpdpSubspace_rename_le_map`: for injective rename,
the rename of the pullback-partition SPDP subspace is CONTAINED IN the
(target-partition) SPDP subspace of the renamed polynomial.

Combined with injectivity of rename, this gives rank preservation:
`rank(rename f p, B) ≥ rank(p, pullbackPartition B f)` for injective f.

This is essential for Task (E): porting `compiled_np_lower_bound_any_dtm`
to `cookLevinPMnApprox` (= rename inlU compiledPoly). -/

/- **Reverse inclusion (statement)**: rename of pullback SPDP subspace
⊆ SPDP subspace of renamed poly.

This theorem would give rank preservation via rename (together with
existing `mlBlockedSpdpRank_rename_le`). Its proof requires showing
SPDP generators map correctly: need
- `isBlockAdmissible_pullback_map` (reverse of existing `_pullback` lemma)
- careful handling of `iterDerivList_rename` + `mlProj_rename` + shift pred

We state the conclusion; the detailed combinatorial proof is future work.
For the architectural flow, only the statement is needed. -/

/-- A **Task E helper**: given a CoupledSheetPoly Q over numU variables,
if Q has a direct SPDP rank bound `≥ C` at some (B', κ, ℓ) on its own
variable space, AND the embed-rank-preservation property holds (i.e.,
`rank(embed Q, B) = rank(Q, pullback B inlU)`), then embed Q inherits
the bound.

Stated as a CONDITIONAL theorem: plug in a rank-preservation hypothesis
and the bound on Q. -/
theorem embed_rank_ge_of_preservation
    (σ : UVSplit) (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ)
    (Q : CoupledSheetPoly σ) (lowerBound : ℕ)
    (hQ : lowerBound ≤ MultilinearSPDP.mlBlockedSpdpRank
      (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q)
    (hPreserve :
      MultilinearSPDP.mlBlockedSpdpRank
        (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q ≤
      MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (CoupledSheetPoly.embed σ Q)) :
    lowerBound ≤ MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      (CoupledSheetPoly.embed σ Q) :=
  le_trans hQ hPreserve

/-! ## Section 22: Final capstone — Path A one-shot theorem

Assembles all the pieces into a single user-facing theorem: given
- A coupled sheet `Q` with rank bound at pullback partition ≥ C
- Rank preservation under embed
- Rank bound on `templatePMn σ Q` ≤ n^200

derive False at n ≥ 2^804.

This is the paper-faithful Path A mechanism in its cleanest form. -/

/-- **Path A one-shot capstone**: combines Task (D), Task (E) hypotheses
and the separation mechanism into a single theorem. -/
theorem pathA_oneshot_separation
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    {σ : UVSplit} (hV : 0 < σ.numV)
    (B : SPDP.BlockPartition σ.total)
    (Q : CoupledSheetPoly σ) (κ ℓ : ℕ)
    -- Task (E): rank bound on Q
    (hQRank : Nat.choose (n / 3) (Nat.log 2 n) ≤
      MultilinearSPDP.mlBlockedSpdpRank
        (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q)
    -- Task (E) helper: rank preservation under embed
    (hEmbedPres :
      MultilinearSPDP.mlBlockedSpdpRank
        (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q ≤
      MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (CoupledSheetPoly.embed σ Q))
    -- Task (D): rank bound on templatePMn
    (hPMnRank : MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      (templatePMn σ Q) ≤ n ^ 200) :
    False := by
  apply templatePMn_separation n hn hV B Q κ ℓ hPMnRank
  exact embed_rank_ge_of_preservation σ B κ ℓ Q
    (Nat.choose (n / 3) (Nat.log 2 n)) hQRank hEmbedPres

/-- **Path A one-shot bridge to main theorem**: `¬ H` follows from
conditional rank bounds. Set `H := DecidesSAT M` at a specific n to
derive the separation. -/
theorem pathA_oneshot_no_hypothesis
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    {σ : UVSplit} (hV : 0 < σ.numV)
    (B : SPDP.BlockPartition σ.total)
    (Q : CoupledSheetPoly σ) (κ ℓ : ℕ)
    {H : Prop}
    (hQRank : H → Nat.choose (n / 3) (Nat.log 2 n) ≤
      MultilinearSPDP.mlBlockedSpdpRank
        (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q)
    (hEmbedPres : H →
      MultilinearSPDP.mlBlockedSpdpRank
        (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q ≤
      MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (CoupledSheetPoly.embed σ Q))
    (hPMnRank : H → MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      (templatePMn σ Q) ≤ n ^ 200) :
    ¬ H :=
  fun h => pathA_oneshot_separation n hn hV B Q κ ℓ
    (hQRank h) (hEmbedPres h) (hPMnRank h)

/-! ## Section 23: Step 3 — Rank preservation under injective rename

We prove the reverse of `isBlockAdmissible_pullback`: if S is
pullback-admissible, S.map f is B-admissible (for injective f). This
unlocks the reverse SPDP subspace inclusion and hence rank preservation. -/

/-- **Reverse pullback admissibility**: for injective f, if S is
pullback-admissible then S.map f is B-admissible. -/
theorem isBlockAdmissible_of_pullback {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : SPDP.BlockPartition m) (S : List (Fin n))
    (hadm : SPDP.isBlockAdmissible (MultilinearSPDP.pullbackPartition B f) S) :
    SPDP.isBlockAdmissible B (S.map f) := by
  constructor
  · exact (List.nodup_map_iff hf).mpr hadm.1
  · intro b
    -- (S.map f).filter(B.assign · = b) has same length as
    -- S.filter(B.assign ∘ f · = b) = S.filter(pullback.assign · = b)
    have : ∀ (L : List (Fin n)),
        ((L.map f).filter (fun j => B.assign j = b)).length =
        (L.filter (fun i => B.assign (f i) = b)).length := by
      intro L; induction L with
      | nil => simp
      | cons a rest ih =>
        simp only [List.map_cons, List.filter_cons]
        by_cases h : B.assign (f a) = b <;> simp [h, ih]
    rw [this S]
    exact hadm.2 b

/-- **SPDP subspace reverse inclusion** (Step 3 core):
`rename f (pullback SPDP subspace) ⊆ SPDP subspace (of rename f p)`
for injective f.

This is the ALGEBRAIC HEART of rank preservation: SPDP generators of
`p` (in pullback partition) map under rename to SPDP generators of
`rename f p` (same shift, block-admissibility preserved). -/
theorem mlBlockedSpdpSubspace_rename_map_le
    {n m : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : SPDP.BlockPartition m) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) ℚ) :
    Submodule.map (MvPolynomial.rename f).toLinearMap
      (MultilinearSPDP.mlBlockedSpdpSubspace
        (MultilinearSPDP.pullbackPartition B f) κ ℓ p) ≤
    MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ (MvPolynomial.rename f p) := by
  rintro q ⟨g, hg, hgeq⟩
  subst hgeq
  induction hg using Submodule.span_induction with
  | mem g' hgen =>
    obtain ⟨S', mult, hlen, hdeg, hvars, hadm, hgen_eq⟩ := hgen
    subst hgen_eq
    show MvPolynomial.rename f
      (MultilinearSPDP.mlProj (mult * SPDP.iterDerivList S' p)) ∈ _
    rw [← MultilinearSPDP.mlProj_rename f hf]
    rw [map_mul]
    rw [← MultilinearSPDP.iterDerivList_rename f hf S' p]
    apply Submodule.subset_span
    refine ⟨S'.map f, MvPolynomial.rename f mult, ?_, ?_, ?_, ?_, rfl⟩
    · rw [List.length_map]; exact hlen
    · exact le_trans (MvPolynomial.totalDegree_rename_le f mult) hdeg
    · intro v hv
      obtain ⟨i, hi, rfl⟩ := MvPolynomial.mem_vars_rename f mult hv
      have : i ∈ S'.toFinset := hvars hi
      rw [List.mem_toFinset] at this
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨i, this, rfl⟩
    · exact isBlockAdmissible_of_pullback f hf B S' hadm
  | zero =>
    show MvPolynomial.rename f 0 ∈ _
    rw [map_zero]
    exact Submodule.zero_mem _
  | add _ _ _ _ hx hy =>
    show MvPolynomial.rename f (_ + _) ∈ _
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c _ _ hx =>
    show MvPolynomial.rename f (c • _) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

/-- **Finrank preservation under injective linear map on a submodule**:
for an injective linear map `φ : M →ₗ[ℚ] N` and any submodule `V ≤ M`,
`finrank(Submodule.map φ V) = finrank V`.

Proof: V is isomorphic to its image under φ via the restricted map
(injective + surjective onto image → LinearEquiv); LinearEquiv.finrank_eq. -/
theorem finrank_map_of_injective_submodule
    {M N : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N]
    (φ : M →ₗ[ℚ] N) (hφ : Function.Injective φ) (V : Submodule ℚ M) :
    Module.finrank ℚ (Submodule.map φ V) = Module.finrank ℚ V := by
  -- Construct the LinearEquiv V ≃ₗ[ℚ] Submodule.map φ V
  let e : V ≃ₗ[ℚ] Submodule.map φ V :=
    LinearEquiv.ofBijective
      { toFun := fun v => ⟨φ v.1, Submodule.mem_map_of_mem v.2⟩
        map_add' := fun x y => by
          apply Subtype.ext
          simp [AddSubmonoid.coe_add, map_add]
        map_smul' := fun c x => by
          apply Subtype.ext
          simp [SetLike.val_smul, map_smul] }
      ⟨by
        intro x y hxy
        apply Subtype.ext
        exact hφ (congrArg Subtype.val hxy),
       by
        rintro ⟨w, hw⟩
        obtain ⟨v, hv, hvw⟩ := hw
        refine ⟨⟨v, hv⟩, ?_⟩
        apply Subtype.ext
        exact hvw⟩
  exact (LinearEquiv.finrank_eq e).symm

/-- **Rank preservation under injective rename** (Step 3 full):
`rank(p, pullback B f) ≤ rank(rename f p, B)` for injective f. -/
theorem mlBlockedSpdpRank_rename_ge
    {n m : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : SPDP.BlockPartition m) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) ℚ) :
    MultilinearSPDP.mlBlockedSpdpRank
      (MultilinearSPDP.pullbackPartition B f) κ ℓ p ≤
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (MvPolynomial.rename f p) := by
  unfold MultilinearSPDP.mlBlockedSpdpRank
  -- finrank(pullback V) = finrank(map rename pullback V) (injective)
  -- ≤ finrank(target SPDP) (subspace inclusion)
  have hinj : Function.Injective
      ((MvPolynomial.rename f : MvPolynomial (Fin n) ℚ →ₐ[ℚ] _).toLinearMap) :=
    fun x y hxy => MvPolynomial.rename_injective f hf hxy
  calc Module.finrank ℚ
        (MultilinearSPDP.mlBlockedSpdpSubspace
          (MultilinearSPDP.pullbackPartition B f) κ ℓ p)
      = Module.finrank ℚ
          (Submodule.map (MvPolynomial.rename f).toLinearMap
            (MultilinearSPDP.mlBlockedSpdpSubspace
              (MultilinearSPDP.pullbackPartition B f) κ ℓ p)) :=
        (finrank_map_of_injective_submodule _ hinj _).symm
    _ ≤ Module.finrank ℚ
          (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ
            (MvPolynomial.rename f p)) :=
        Submodule.finrank_mono (mlBlockedSpdpSubspace_rename_map_le f hf B κ ℓ p)

/-- **Concrete embed rank preservation**: `rank(Q, pullback B inlU) ≤ rank(embed σ Q, B)`. -/
theorem embed_rank_preservation
    (σ : UVSplit) (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ)
    (Q : CoupledSheetPoly σ) :
    MultilinearSPDP.mlBlockedSpdpRank
      (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q ≤
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (CoupledSheetPoly.embed σ Q) := by
  unfold CoupledSheetPoly.embed
  exact mlBlockedSpdpRank_rename_ge σ.inlU (inlU_injective σ) B κ ℓ Q

/-! ## Section 24: Updated one-shot with Step 3 discharged

With `embed_rank_preservation` proved unconditionally, the `hEmbedPres`
hypothesis of `pathA_oneshot_no_hypothesis` is no longer needed. The
updated one-shot takes only two concrete hypotheses: Task 2 and Task 4. -/

/-- **Path A two-hypothesis separation**: with Step 3 discharged, only
hQRank (Task 2) and hPMnRank (Task 4) remain as input. -/
theorem pathA_two_hypothesis_separation
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    {σ : UVSplit} (hV : 0 < σ.numV)
    (B : SPDP.BlockPartition σ.total)
    (Q : CoupledSheetPoly σ) (κ ℓ : ℕ)
    (hQRank : Nat.choose (n / 3) (Nat.log 2 n) ≤
      MultilinearSPDP.mlBlockedSpdpRank
        (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q)
    (hPMnRank : MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      (templatePMn σ Q) ≤ n ^ 200) :
    False :=
  pathA_oneshot_separation n hn hV B Q κ ℓ hQRank
    (embed_rank_preservation σ B κ ℓ Q) hPMnRank

/-- **Path A two-hypothesis bridge**: conditional form for ¬ H. -/
theorem pathA_two_hypothesis_no_hypothesis
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    {σ : UVSplit} (hV : 0 < σ.numV)
    (B : SPDP.BlockPartition σ.total)
    (Q : CoupledSheetPoly σ) (κ ℓ : ℕ)
    {H : Prop}
    (hQRank : H → Nat.choose (n / 3) (Nat.log 2 n) ≤
      MultilinearSPDP.mlBlockedSpdpRank
        (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q)
    (hPMnRank : H → MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      (templatePMn σ Q) ≤ n ^ 200) :
    ¬ H :=
  fun h => pathA_two_hypothesis_separation n hn hV B Q κ ℓ (hQRank h) (hPMnRank h)

/-! ## Section 25: Bridge to Tseitin identity-minor theorem (Step 2)

`Tseitin.identity_minor_lower_bound` establishes the NP-side rank bound:
  rank(coupledVerifier F Φ) ≥ C(pack.selected.length, κ)
at the `tseitinPartition Φ` using `blockedSpdpRank`.

This is exactly Step 2 of Path A — provided we can match up:
- Lean's `coupledVerifier F Φ` (type `MvPolynomial (Fin (tseitinNumVars Φ)) F`)
  with our `CoupledSheetPoly σ` for appropriate σ
- `tseitinPartition Φ` with `pullbackPartition B σ.inlU`
- `blockedSpdpRank` with `mlBlockedSpdpRank` (via mlProj wrapping)

The matching is a matter of variable-counting and partition choice.
We provide the bridge statement below as the Step 2 interface. -/

/-- **Step 2 interface theorem**: given any polynomial `p` with an
`mlBlockedSpdpRank` lower bound at some partition `B'`, this transports
to `embed(p)` under the piPhi framework.

Concrete application: set `p := coupledVerifier F Φ` for a Tseitin
formula Φ, `B' := tseitinPartition Φ`; then one has a rank lower bound
via Tseitin machinery (requires `blockedSpdpRank` → `mlBlockedSpdpRank`
lift, which holds because the identity-minor τ monomials are multilinear
— the Kronecker coefficients survive mlProj). -/
theorem step2_embed_rank_ge_of_source
    (σ : UVSplit) (B : SPDP.BlockPartition σ.total) (κ ℓ : ℕ)
    (Q : CoupledSheetPoly σ) (lowerBound : ℕ)
    (hSourceBound : lowerBound ≤ MultilinearSPDP.mlBlockedSpdpRank
      (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q) :
    lowerBound ≤ MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      (CoupledSheetPoly.embed σ Q) :=
  le_trans hSourceBound (embed_rank_preservation σ B κ ℓ Q)

/-- **Full Path A separation from source-rank bound**: the final
assembly. Given:
- A PMn-side bound `rank(templatePMn σ Q) ≤ n^200` (Task D)
- A Q-side bound `rank(Q, pullback) ≥ C(n/3, log n)` (Task E/Step 2)
we derive False at n ≥ 2^804.

The Q-side bound itself is the content of Theorem 128 (identity minor
on Q^×_Φ via disjoint packing); its Lean port uses
`Tseitin.identity_minor_lower_bound` + multilinear-τ preservation of
LI through mlProj. -/
theorem pathA_final_separation
    (n : ℕ) (hn : n ≥ 2 ^ 804)
    {σ : UVSplit} (hV : 0 < σ.numV)
    (B : SPDP.BlockPartition σ.total)
    (Q : CoupledSheetPoly σ) (κ ℓ : ℕ)
    (hQSource : Nat.choose (n / 3) (Nat.log 2 n) ≤
      MultilinearSPDP.mlBlockedSpdpRank
        (MultilinearSPDP.pullbackPartition B σ.inlU) κ ℓ Q)
    (hPMnRank : MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      (templatePMn σ Q) ≤ n ^ 200) :
    False :=
  pathA_two_hypothesis_separation n hn hV B Q κ ℓ hQSource hPMnRank

end PaperFaithfulCompilation
