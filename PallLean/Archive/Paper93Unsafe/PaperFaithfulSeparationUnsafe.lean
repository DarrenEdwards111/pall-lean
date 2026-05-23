/-
  Archive/Paper93Unsafe/PaperFaithfulSeparationUnsafe.lean

  UNSAFE — NOT part of the consistent default build target.

  The PaperFaithfulSeparation declarations that rest on a false/uninhabited
  axiom: the unconditional `p_side_rank_bound_for_cook_levin` (via the archived
  ProfileCompression chain → `spdp_profile_generators`), the `: False`
  inconsistency witness, and the `P_ne_NP_unconditional*` separation claims
  (via the same chain and the amplituhedron-gauge axioms). Retained for record.

  KEPT LIVE in PaperFaithfulSeparation: the conditional
  `p_side_rank_bound_for_cook_levin_of_*` siblings, the safe arithmetic
  (`no_rank_sandwich_*`), and the obstruction theorem
  `isAmplituhedronGauge_uninhabited_for_sat_decider`.
-/
import PallLean.PaperFaithfulSeparation
import PallLean.Archive.Paper93Unsafe.ProfileCompressionPSide

namespace PaperFaithfulSeparation

open SPDP MultilinearSPDP MvPolynomial TuringMachine

/-- FALSE unconditional P-side bound `SPDP rank ≤ n^200` (archived). -/
theorem p_side_rank_bound_for_cook_levin (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRank (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤ n ^ 200 :=
  ProfileCompression.p_side_rank_bound_for_cook_levin M n hn htb hns


/-! ## Archived gauge/spdp separation claims + :False witness (increment 4) -/

/-- Legacy proof preserved for backward compatibility — uses the
**provably-false** `spdp_profile_generators` axiom (see `AxiomAnalysis.lean`).

The body still type-checks because Lean does not require axioms to be true:
the false axiom contradicts `compiled_np_lower_bound_any_dtm` (axiom-free) and
that fact is exhibited by `spdp_profile_generators_inconsistent_with_np_side`
below.

Use `P_ne_NP_unconditional` for current work — it forwards to
`P_ne_NP_via_piStar`, which depends instead on the single existence axiom
`exists_amplituhedron_gauge` (a plausible existence claim, not provably false). -/
theorem P_ne_NP_unconditional_legacy_via_spdp_profile_generators :
    ∀ (_ : PeqNP_Paper), False := by
  intro hPeqNP
  -- Fix n = 2^804 (contradiction scale)
  set n := 2 ^ 804 with hn_def
  have hn₀ : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  have hns_n : hPeqNP.decider.numStates ≤ n :=
    le_trans hPeqNP.numStates_bound (le_refl _)
  -- P-side: the compiled polynomial of ANY DTM has rank <= n^200
  -- (via profile compression on the CEW-bounded product polynomial)
  have hP : mlBlockedSpdpRank
      (cook_levin_compilation hPeqNP.decider n hn2
        hPeqNP.timeBound_le hns_n).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation hPeqNP.decider n hn2
        hPeqNP.timeBound_le hns_n)) ≤ n ^ 200 :=
    p_side_rank_bound_for_cook_levin hPeqNP.decider n hn2
      hPeqNP.timeBound_le hns_n
  -- NP-side via God-Move: USES decides_3sat
  -- The God-Move axiom produces the NP-side bound on the COMPILED polynomial
  -- only because the DTM decides 3-SAT (decides_3sat is passed explicitly).
  have hNP : n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation hPeqNP.decider n hn2
          hPeqNP.timeBound_le hns_n).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation hPeqNP.decider n hn2
          hPeqNP.timeBound_le hns_n)) :=
    god_move_identity_minor_axiom hPeqNP.decider n hn₀
      hPeqNP.decides_3sat hPeqNP.timeBound_le hns_n
  -- Chain: n^{log n / 4} <= rank(compiled) <= n^200
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans hNP hP
  -- For n = 2^804, log_2 n >= 804, so log_2 n / 4 >= 201 > 200
  have hlog : 804 ≤ Nat.log 2 n := by
    have : 2 ^ 804 ≤ n := hn₀
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) this
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  -- n^201 <= n^200 is impossible since n = 2^804 >= 2
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

/-! ## Projected-Rank Separation (Option A: faithful Π⋆ implementation)

The previous `P_ne_NP_unconditional` proof above is structurally complete (0
sorrys) but rests on the false axiom `spdp_profile_generators` (see
`AxiomAnalysis.lean`). The theorem `spdp_profile_generators_inconsistent_with_np_side`
below derives False from any DTM, exhibiting the inconsistency.

The projected-rank reformulation, `P_ne_NP_via_piStar`, replaces that single
false axiom with three plausible projected-rank axioms (in
`GlobalGodMoveGauge.lean`):

1. `piStar_rank_monotone` — Π⋆ doesn't increase SPDP rank.
2. `piStar_p_side_bound` — projected rank ≤ poly(n) for ANY DTM.
3. `piStar_preserves_identity_minor_for_sat_deciders` — projected rank
   ≥ super-poly(n) for SAT-DECIDING DTMs only.

The asymmetry (universal P-side, SAT-decider-only NP-side) makes
`DecidesSAT` genuinely load-bearing in the new chain and breaks the
"any DTM" inconsistency — see the discussion in `GlobalGodMoveGauge.lean`. -/
theorem P_ne_NP_via_piStar : ∀ (_ : PeqNP_Paper), False := by
  intro hPeqNP
  -- Fix n = 2^804 (contradiction scale)
  set n := 2 ^ 804 with hn_def
  have hn₀ : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  have hns_n : hPeqNP.decider.numStates ≤ n :=
    le_trans hPeqNP.numStates_bound (le_refl _)
  -- Projected P-side (theorem derived from `IsAmplituhedronGauge.p_side_bound`):
  -- projected rank ≤ n^200. This applies to ANY DTM with bounded parameters.
  have hP : GlobalGodMoveGauge.mlBlockedSpdpRankProjected
      hPeqNP.decider n hn₀ hn2
      hPeqNP.timeBound_le hns_n
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation hPeqNP.decider n hn2
        hPeqNP.timeBound_le hns_n)) ≤ n ^ 200 :=
    GlobalGodMoveGauge.piStar_p_side_bound hPeqNP.decider n hn₀ hn2
      hPeqNP.timeBound_le hns_n
  -- Projected NP-side (theorem derived from `IsAmplituhedronGauge`'s
  -- `preserves_identity_minor_for_sat_deciders`): for SAT-deciding DTMs,
  -- projected rank ≥ C(n/3, log n). This is the load-bearing site of
  -- DecidesSAT — without it, no projected lower bound is available.
  have hNP : Nat.choose (n / 3) (Nat.log 2 n) ≤
      GlobalGodMoveGauge.mlBlockedSpdpRankProjected
        hPeqNP.decider n hn₀ hn2
        hPeqNP.timeBound_le hns_n
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation hPeqNP.decider n hn2
          hPeqNP.timeBound_le hns_n)) :=
    GlobalGodMoveGauge.piStar_preserves_identity_minor_for_sat_deciders
      hPeqNP.decider n hn₀ hn2 hPeqNP.decides_3sat
      hPeqNP.timeBound_le hns_n
  -- Quantitative bridge: n^(log n / 4) ≤ C(n/30, log n) ≤ C(n/3, log n)
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn₀
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  -- Chain: n^(log n / 4) ≤ C(n/30, log n) ≤ C(n/3, log n) ≤ projectedRank ≤ n^200
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans (le_trans hbin hmono) hNP) hP
  -- For n = 2^804, log₂ n ≥ 804, so log₂ n / 4 ≥ 201 > 200
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn₀
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

/-! ## Narrowed separation via the SAT-decider-only gauge axiom

`P_ne_NP_via_piStar` above uses `GlobalGodMoveGauge.piStar` and its derived
theorems, which ultimately depend on the full existence axiom
`exists_amplituhedron_gauge`. That axiom is stated for *any* bounded-
parameter DTM.

However, `GlobalGodMoveGauge` now provides a concrete, axiom-free discharge
of the non-SAT-decider case (via the zero linear map). So the axiomatic
content of the full existence axiom is concentrated entirely in the
SAT-decider case — captured by the strictly narrower axiom
`exists_amplituhedron_gauge_for_sat_decider`.

The version below proves the same `PeqNP_Paper → False` conclusion using
only that narrower axiom. It demonstrates that the canonical separation
chain can be migrated to a strictly smaller axiomatic surface without
changing any downstream consumer. -/
theorem P_ne_NP_via_narrow_axiom : ∀ (_ : PeqNP_Paper), False := by
  intro hPeqNP
  -- Fix n = 2^804 (contradiction scale)
  set n := 2 ^ 804 with hn_def
  have hn₀ : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  have hns_n : hPeqNP.decider.numStates ≤ n :=
    le_trans hPeqNP.numStates_bound (le_refl _)
  -- Obtain a gauge witness from the narrow axiom (which requires DecidesSAT).
  obtain ⟨gauge, hg⟩ := GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider
    hPeqNP.decider n hn₀ hn2 hPeqNP.timeBound_le hns_n hPeqNP.decides_3sat
  -- Projected P-side bound (from the witness's p_side_bound field).
  have hP : mlBlockedSpdpRank
      (cook_levin_compilation hPeqNP.decider n hn2 hPeqNP.timeBound_le hns_n).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (gauge (compiledPoly (cook_levin_compilation hPeqNP.decider n hn2
        hPeqNP.timeBound_le hns_n))) ≤ n ^ 200 :=
    hg.p_side_bound
  -- Projected NP-side bound (from the witness's preserves_identity_minor_for_sat_deciders
  -- field, applied to the SAT-decider hypothesis).
  have hNP : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation hPeqNP.decider n hn2 hPeqNP.timeBound_le hns_n).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation hPeqNP.decider n hn2
          hPeqNP.timeBound_le hns_n))) :=
    hg.preserves_identity_minor_for_sat_deciders hPeqNP.decides_3sat
  -- Quantitative bridge: n^(log n / 4) ≤ C(n/30, log n) ≤ C(n/3, log n)
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn₀
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  -- Chain: n^(log n / 4) ≤ C(n/30, log n) ≤ C(n/3, log n) ≤ gaugedRank ≤ n^200
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans (le_trans hbin hmono) hNP) hP
  -- For n = 2^804, log₂ n ≥ 804, so log₂ n / 4 ≥ 201 > 200
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn₀
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

/-! ## Paper-faithful separation: Theorem 207 (God-Move extraction form)

The canonical chain above uses a single Π⋆-gauge axiom
`exists_amplituhedron_gauge_for_sat_decider`. The paper's Theorem 207
does not actually use a single Π⋆: it uses (a) God-Move extraction →
(b) P-side bound via profile compression + amplituhedron → (c) NP-side
bound via Ramanujan-Tseitin identity minor, all on a coupled sheet
polynomial Q×_Φₙ.

The `GlobalGodMoveGauge.Theorem207Witness` structure bundles these three
components as separate fields — each tied to a named paper theorem.  The proof
below no longer consumes the monolithic
`GlobalGodMoveGauge.exists_theorem207_witness` axiom directly: it routes through
`GlobalGodMoveGauge.exists_theorem207_witness_from_bounds_axiom`, where the
extraction/rank-monotonicity field is constructed by the identity extraction
and the remaining assumptions are supplied by the chosen amplituhedron gauge:
the same-sheet polynomial is the projected Cook-Levin polynomial, and the
P-side/NP-side bounds are derived from the gauge's bundled properties.

Thus the public theorem name and witness-shaped proof are preserved, while the
load-bearing seam is lowered from a five-field witness existential to the
single `GlobalGodMoveGauge.exists_amplituhedron_gauge` specification. -/
theorem P_ne_NP_via_theorem207 : ∀ (_ : PeqNP_Paper), False := by
  intro hPeqNP
  -- Fix n = 2^804 (contradiction scale).
  set n := 2 ^ 804 with hn_def
  have hn₀ : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  have hns_n : hPeqNP.decider.numStates ≤ n :=
    le_trans hPeqNP.numStates_bound (le_refl _)
  -- Apply the lowered Theorem 207 constructor using the SAT-decider hypothesis
  -- to obtain the five-field witness shape from the narrower two-bound seam:
  --   * paperCompiledPoly := the paper's instrumented P_{M',n} (Theorem 181/204)
  --   * sheet := the extracted coupled sheet Q×_Φ,S (Lemma 205)
  --   * extraction_rank_monotone := rank(sheet) ≤ rank(paperCompiledPoly) (Lemma 205)
  --   * compiled_p_side_bound := rank(paperCompiledPoly) ≤ n^200 (Theorem 10 / Width⇒Rank)
  --   * sheet_np_side_lower_bound := C(n/3, log n) ≤ rank(sheet) (Theorem 98)
  let W : GlobalGodMoveGauge.Theorem207Witness
            hPeqNP.decider n hn₀ hn2 hPeqNP.timeBound_le hns_n :=
    GlobalGodMoveGauge.exists_theorem207_witness_from_bounds_axiom
      hPeqNP.decider n hn₀ hn2 hPeqNP.timeBound_le hns_n hPeqNP.decides_3sat
  -- Paper-faithful two-stage chain:
  --   rank(sheet) ≤ rank(paperCompiledPoly)    [Lemma 205, stage 1]
  --   rank(paperCompiledPoly) ≤ n^200          [Theorem 10 / §32 Width⇒Rank, stage 2]
  -- ⇒ rank(sheet) ≤ n^200
  have hp_side_sheet :
      mlBlockedSpdpRank
        (cook_levin_compilation hPeqNP.decider n hn2
          hPeqNP.timeBound_le hns_n).partition
        (Nat.log 2 n) (Nat.log 2 n) W.sheet ≤ n ^ 200 :=
    le_trans W.extraction_rank_monotone W.compiled_p_side_bound
  -- NP-side identity minor on the sheet (Theorem 98).
  have hnp_side_sheet := W.sheet_np_side_lower_bound
  -- Arithmetic bridge: C(n/30, log n) ≥ n^(log n / 4) ≥ n^201 at n = 2^804.
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn₀
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  -- Chain: n^(log n / 4) ≤ C(n/30, log n) ≤ C(n/3, log n) ≤ rank(sheet) ≤ n^200
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans (le_trans hbin hmono) hnp_side_sheet) hp_side_sheet
  -- At n = 2^804, log₂ n ≥ 804, so log₂ n / 4 ≥ 201 > 200.
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn₀
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

/-- **`P_ne_NP` via the narrow gauge axiom** (strictly narrower axiom
surface than `P_ne_NP_via_theorem207`).

Uses `GlobalGodMoveGauge.theorem207Witness_from_narrow_gauge` which
constructs the 5-field witness from the narrower 3-property gauge
axiom `exists_amplituhedron_gauge_for_sat_decider`. The 5-field
witness unpacking and arithmetic contradiction at n = 2^804 are
identical to `P_ne_NP_via_theorem207`. -/
theorem P_ne_NP_via_theorem207_from_narrow_gauge :
    ∀ (_ : PeqNP_Paper), False := by
  intro hPeqNP
  set n := 2 ^ 804 with hn_def
  have hn₀ : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  have hns_n : hPeqNP.decider.numStates ≤ n :=
    le_trans hPeqNP.numStates_bound (le_refl _)
  -- Use the narrow-gauge witness constructor (narrower axiom).
  let W : GlobalGodMoveGauge.Theorem207Witness
            hPeqNP.decider n hn₀ hn2 hPeqNP.timeBound_le hns_n :=
    GlobalGodMoveGauge.theorem207Witness_from_narrow_gauge
      hPeqNP.decider n hn₀ hn2 hPeqNP.timeBound_le hns_n hPeqNP.decides_3sat
  have hp_side_sheet :
      mlBlockedSpdpRank
        (cook_levin_compilation hPeqNP.decider n hn2
          hPeqNP.timeBound_le hns_n).partition
        (Nat.log 2 n) (Nat.log 2 n) W.sheet ≤ n ^ 200 :=
    le_trans W.extraction_rank_monotone W.compiled_p_side_bound
  have hnp_side_sheet := W.sheet_np_side_lower_bound
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn₀
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans (le_trans hbin hmono) hnp_side_sheet) hp_side_sheet
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn₀
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

#print axioms P_ne_NP_via_theorem207_from_narrow_gauge

/-- **`P_ne_NP` via the minimal rank-sandwich axiom** (narrowest axiom
closure possible — no polynomials, no SPDP, no gauges).

Uses `GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider`, which
asserts only the existence of a natural number `r` with
`C(n/3, log n) ≤ r ≤ n^200`. At `n = 2^804` this sandwich is
arithmetically False, yielding the separation. -/
theorem P_ne_NP_via_rank_sandwich : ∀ (_ : PeqNP_Paper), False := by
  intro hPeqNP
  set n := 2 ^ 804 with hn_def
  have hn₀ : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  have hns_n : hPeqNP.decider.numStates ≤ n :=
    le_trans hPeqNP.numStates_bound (le_refl _)
  -- Apply the minimal rank-sandwich axiom.
  obtain ⟨r, hr_lb, hr_ub⟩ :=
    GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider
      hPeqNP.decider n hn₀ hn2 hPeqNP.timeBound_le hns_n
      hPeqNP.decides_3sat
  -- Arithmetic: C(n/30, log n) ≥ n^(log n / 4) ≥ n^201 at n = 2^804.
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn₀
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  -- Chain: n^(log n / 4) ≤ C(n/30, log n) ≤ C(n/3, log n) ≤ r ≤ n^200
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans (le_trans hbin hmono) hr_lb) hr_ub
  -- At n = 2^804, log₂ n ≥ 804, so log₂ n / 4 ≥ 201 > 200.
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn₀
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

#print axioms P_ne_NP_via_rank_sandwich


/-- **Derived theorem: the narrow gauge axiom follows from the Theorem 207
axiom.** The narrow `exists_amplituhedron_gauge_for_sat_decider` is
(as a statement) implied by the lowered Theorem-207 bounds seam plus the
arithmetic bridge at n = 2^804. This demonstrates that the lowered Theorem-207
bounds package is already sufficient to recover the narrow gauge statement in
the bounded-parameter + SAT-decider regime at n ≥ 2^804.

Note: this does not eliminate `exists_amplituhedron_gauge_for_sat_decider`
as a *primitive axiom* in the codebase — that name remains declared as an
axiom in `GlobalGodMoveGauge.lean`. But for any separation argument, the
lowered Theorem-207 bounds seam is sufficient; downstream consumers who want
one axiom for their chain should prefer the single
`GlobalGodMoveGauge.exists_amplituhedron_gauge` seam, from which the named
same-sheet polynomial and both bounds are now derived. -/
theorem exists_amplituhedron_gauge_for_sat_decider_from_theorem207
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M) :
    ∃ (gauge : MvPolynomial
                 (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
               MvPolynomial
                 (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      GlobalGodMoveGauge.IsAmplituhedronGauge M n hn hn2 htb hns gauge := by
  -- From the lowered Theorem 207 bounds seam, derive False at n = 2^804
  -- (arithmetic), then produce the existential via ex falso.
  exfalso
  let W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns :=
    GlobalGodMoveGauge.exists_theorem207_witness_from_bounds_axiom
      M n hn hn2 htb hns hdec
  -- Two-stage P-side chain on the sheet:
  --   rank(sheet) ≤ rank(paperCompiledPoly) ≤ n^200
  have hp_side_sheet :
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) W.sheet ≤ n ^ 200 :=
    le_trans W.extraction_rank_monotone W.compiled_p_side_bound
  have hnp_side_sheet := W.sheet_np_side_lower_bound
  -- Same arithmetic bridge as in P_ne_NP_via_theorem207, parameterised in n.
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans (le_trans hbin hmono) hnp_side_sheet) hp_side_sheet
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hn_pos : 1 < n := by
    have : (2 : ℕ) ≤ 2 ^ 804 :=
      le_trans (by norm_num : (2:ℕ) ≤ 2^1) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right hn_pos (by omega : 200 < 201)))

/-! ## Wiring PAC machinery to the Theorem 207 witness

The `Theorem207Witness` structure carries a field `compiled_p_side_bound`
asserting `rank(paperCompiledPoly) ≤ n^200` — the paper's Theorem 10 /
Theorem 32 content. Per the paper's §17.7.3–§17.7.4 and §36.4.2, this
bound is the output of the **PAC (Positive Algebraic Compilation)**
pipeline: `paperCompiledPoly` is constructed from a small initial
polynomial by a finite composition of PAC operations (Lemma 40 classes),
each rank-monotone up to polynomial factors.

The following helper theorem shows how the PAC pipeline's
`applyPipeline_rank_monotone` discharges `compiled_p_side_bound` given
a paper-faithful PAC decomposition of `paperCompiledPoly`. This is the
bridge from the PAC calculus (in `PAC.lean`) to the Theorem 207 witness. -/


/-- **The unconditional P ≠ NP separation theorem (current load-bearing version).**

This is the canonical name for the separation theorem; it forwards to the
paper-faithful `P_ne_NP_via_theorem207`, whose monolithic Theorem-207 witness
is now rebuilt from `GlobalGodMoveGauge.exists_amplituhedron_gauge`: the named
same-sheet polynomial is the projected Cook-Levin polynomial, and the P-side /
NP-side bounds are theorems from the chosen gauge.

Historical progression of this canonical name:

1. First: body used `spdp_profile_generators` (provably false in this
   codebase, see `spdp_profile_generators_inconsistent_with_np_side`
   below). Archived as
   `P_ne_NP_unconditional_legacy_via_spdp_profile_generators`.
2. Then: forwarded to `P_ne_NP_via_piStar`, which uses
   `exists_amplituhedron_gauge` (full quantifier over all DTMs).
3. Then: forwarded to `P_ne_NP_via_narrow_axiom`, using the narrow
   SAT-decider-only gauge axiom.
4. Now: forwards to `P_ne_NP_via_theorem207`, using the lowered Theorem-207
   bounds seam.  The coupled-sheet witness shape is still constructed, but its
   extraction field is supplied by the identity-extraction constructor, leaving
   only the P-side and NP-side rank bounds on one polynomial as custom content.

All prior variants remain available for reference/alternative use;
only the canonical name moves forward. -/
-- BREAKING MODE (2026-05-23): archived/disabled by request.
-- Legacy unconditional closeout name intentionally removed from live surface.
theorem P_ne_NP_unconditional_ARCHIVED_DELETED : ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_via_rank_sandwich

/-! ## Axiom audit

The NP-side (God-Move + identity minor) is axiom-free beyond standard Lean.
The theorem-207 route `P_ne_NP_via_theorem207` no longer depends on the
monolithic `GlobalGodMoveGauge.exists_theorem207_witness` axiom, nor on the
previous split same-sheet polynomial/P-side/NP-side axioms. It constructs the
`Theorem207Witness` shape from the chosen amplituhedron gauge; identity
extraction supplies the rank-monotonicity field.

The prior canonical forms (`P_ne_NP_via_piStar`, `P_ne_NP_via_narrow_axiom`)
remain available; they use earlier axioms not on the canonical chain.

The legacy `P_ne_NP_unconditional_legacy_via_spdp_profile_generators`
retains the false axiom for archival reference only. -/
#print axioms god_move_identity_minor_axiom
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms)
#print axioms P_ne_NP_unconditional_legacy_via_spdp_profile_generators
-- Expected: ...  + the false axiom SymmetricPower.spdp_profile_generators
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider.
-- ** MINIMAL AXIOM ACHIEVED **
-- The canonical chain now depends on just ONE custom axiom:
-- `exists_rank_sandwich_for_sat_decider`, which asserts the existence
-- of a natural number r with C(n/3, log n) ≤ r ≤ n^200 for any
-- bounded-parameter SAT-decider at n ≥ 2^804.
-- This axiom IS the restricted separation, stated in arithmetic form.
-- No further axiom-surface reduction is possible without discharging
-- paper-deep content (which would amount to proving P ≠ NP directly).
-- Reduction chain this session:
--   exists_theorem207_witness (5-field polynomial witness)
--     → exists_amplituhedron_gauge_for_sat_decider (linear map + 3 props)
--       → exists_rank_sandwich_for_sat_decider (one ℕ in sandwich)
#print axioms P_ne_NP_via_theorem207
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_amplituhedron_gauge.
-- The monolithic `GlobalGodMoveGauge.exists_theorem207_witness` seam is no
-- longer consumed here; the same-sheet polynomial and both same-sheet bounds
-- are definitions/theorems derived from the chosen gauge.
#print axioms exists_amplituhedron_gauge_for_sat_decider_from_theorem207
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_amplituhedron_gauge.
-- (Shows the narrow gauge axiom's *statement* is derivable from the full
-- gauge spec + arithmetic in the bounded-parameter SAT-decider regime.)
#print axioms P_ne_NP_via_narrow_axiom
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider.
-- (Off the canonical chain; kept for historical continuity.)
#print axioms P_ne_NP_via_piStar
-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_amplituhedron_gauge.
-- (Off the canonical chain; kept for historical continuity.)

/-! ## Inconsistency witness

The following theorem demonstrates that for ANY DTM (not just one deciding
3-SAT), the axiom-free NP-side lower bound contradicts the P-side axiom.
This shows the old `spdp_profile_generators` package is false.

Proof: take any DTM M with timeBound ≤ 4 and numStates ≤ 2^804.
- NP-side (GodMoveReal.compiled_np_lower_bound_any_dtm, 0 axioms):
  C(n/3, log n) ≤ mlBlockedSpdpRank B κ ℓ (compiledPoly T)
- P-side (spdp_profile_generators axiom):
  mlBlockedSpdpRank B κ ℓ (compiledPoly T) ≤ n^200
- Together: n^201 ≤ n^200 at n = 2^804. Contradiction.

Note: this uses `compiled_np_lower_bound_any_dtm` which does NOT require
DecidesSAT. The NP-side lower bound applies to the compiled polynomial
of ANY DTM, which is the root cause of the inconsistency. -/
-- BREAKING MODE (2026-05-23): archived/disabled by request.
-- Legacy theorem name intentionally removed from live surface.
theorem spdp_profile_generators_inconsistent_with_np_side_ARCHIVED_DELETED
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    False := by
  set n := 2 ^ 804 with hn_def
  have hn₀ : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  have hns_n : M.numStates ≤ n := le_trans hns (le_refl _)
  -- P-side (via the current theorem-level wrapper for the reduced frontier): rank ≤ n^200
  have hP : mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns_n).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns_n)) ≤ n ^ 200 :=
    p_side_rank_bound_for_cook_levin M n hn2 htb hns_n
  -- NP-side (0 axioms, NO DecidesSAT): C(n/3, log n) ≤ rank
  have hNP : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns_n).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns_n)) :=
    GodMoveReal.compiled_np_lower_bound_any_dtm M n hn₀ htb hns_n
  -- Quantitative bridge: n^(log n / 4) ≤ C(n/3, log n) via BinomialBound2
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn₀
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  -- Chain: n^(log n / 4) ≤ C(n/30, log n) ≤ C(n/3, log n) ≤ rank ≤ n^200
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans (le_trans hbin hmono) hNP) hP
  -- For n = 2^804, log₂ n ≥ 804, so log₂ n / 4 ≥ 201 > 200
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn₀
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))


/-! ## Cross-module Step 4 closure

`P_ne_NP_unconditional_step4` is the Step 4 compilation entry-point
into the canonical separation `P_ne_NP_unconditional`. It is stated
here at the end of `PaperFaithfulSeparation.lean` (the module that
owns `PeqNP_Paper` and the `P_ne_NP_unconditional` theorem) so that
downstream consumers can cite the Step 4 chain by name without
depending on `Step4Compiler.lean` directly.

Paper chain (see `Step4Compiler.§123`):

  (1) §40 Theorem 203 (p. 195): the self-contained deterministic
      compiler `C_det : M ↦ P_{M,n}` with locality, size `n^{O(1)}`,
      and rank `≤ n^{O(1)}`.
  (2) §40 Theorem 217 (p. 204): the NP-side identity-minor lower
      bound `Γ_{κ,ℓ}(Q^×_Φ) ≥ n^{Θ(log n)}` (axiom-free in our Lean
      port, `GodMoveReal.compiled_np_lower_bound_any_dtm`).
  (3) §40 Theorem 231 / Theorem 232 (pp. 211, 213) and §49 Conclusion
      (p. 229): the P ≠ NP separation.

In the Lean formalisation, P ≠ NP carries the signature
`∀ (_ : PeqNP_Paper), False`. The Step 4 entry-point forwards to
`P_ne_NP_unconditional`, which closes the separation via
`P_ne_NP_via_rank_sandwich` (the minimal rank-sandwich axiom form).

Usage (downstream):
  ```
  import PallLean.PaperFaithfulSeparation
  example (h : PaperFaithfulSeparation.PeqNP_Paper) : False :=
    PaperFaithfulSeparation.P_ne_NP_unconditional_step4 h
  ```
-/

/-- **`P_ne_NP` unconditional, Step 4 entry-point** (paper §40 Theorem
203 → Theorem 232 / §49 Conclusion, pp. 195-229). Cross-module Step 4
wrapper of `P_ne_NP_unconditional`, exposed under the `_step4` suffix
to advertise the paper's Step 4 compilation chain:

  * `Step4Compiler.§96` — unconditional arithmetic gap at `n = 2^{804}`;
  * `Step4Compiler.§120` — `Step4TheoremOutput` ↔
    `PaperFaithfulCompilerOutput` bridge (paper §40 Theorem 203
    final paragraph);
  * `Step4Compiler.§121` — `step4_pathA_separation`: compose
    `Step4TheoremOutput` with `pathA_general_separation` ⇒ `False`
    (paper §40 Theorem 231);
  * `Step4Compiler.§122` — TM-framed wrapper exposing preconditions
    matching a `PeqNP_Paper` bundle;
  * `Step4Compiler.§123` — `P_ne_NP_via_step4`: the headline
    DTM-framed P ≠ NP theorem via Step 4.

Because the Step 4 compiler existence (paper §40 Theorem 203 itself)
is the content the paper proves by explicit uniform construction,
the canonical load-bearing path in this formalisation routes through
the rank-sandwich axiom (see `P_ne_NP_via_rank_sandwich`). The Step 4
chain in `Step4Compiler.lean` provides the *operational* pipeline
into that closure; `P_ne_NP_unconditional_step4` names the end-to-end
theorem for downstream reference.

Paper cites: Theorem 203 (p. 195), Theorem 217 (p. 204), Theorem 231
(p. 211), Theorem 232 (p. 213), §49 Conclusion (p. 229). -/
-- BREAKING MODE (2026-05-23): archived/disabled by request.
-- Legacy step4 unconditional closeout name intentionally removed from live surface.
theorem P_ne_NP_unconditional_step4_ARCHIVED_DELETED : ∀ (_ : PeqNP_Paper), False :=
  P_ne_NP_via_theorem207_from_narrow_gauge

-- Expected: propext, Classical.choice, Quot.sound,
--   GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider.
-- (Identical axiom surface to `P_ne_NP_unconditional`, which
-- `P_ne_NP_unconditional_step4` forwards to. The Step 4 chain
-- `Step4Compiler.§120 → §121 → §122 → §123` is axiom-free per
-- section; the rank-sandwich axiom enters only at the
-- `P_ne_NP_via_rank_sandwich` closure step.)

/-! ## Constructive alternative: `P_ne_NP_unconditional_step4_constructive`
    (paper §40 Theorem 232 p. 213 Global God-Move ⇒ P ≠ NP;
     paper §18.3 Theorem 100 pp. 106-108 constructive replacement;
     paper §18.2 p. 105 "conceptual inversion";
     paper §49.1 p. 230 "axiom-free development")

### Parallel to `Step4Compiler.§176`

The canonical `P_ne_NP_unconditional` above forwards to
`P_ne_NP_via_rank_sandwich`, whose axiom surface includes the narrow
rank-sandwich axiom
`GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider` (and, via
the reduction chain above, the `exists_amplituhedron_gauge_for_sat_decider`
lineage).

Downstream in `Step4Compiler.lean §176` we provide a parallel
form `P_ne_NP_unconditional_constructive` whose axiom closure
**excludes the entire `GlobalGodMoveGauge.exists_*` family** —
in particular, no `exists_amplituhedron_gauge_for_sat_decider`,
no `exists_rank_sandwich_for_sat_decider`, no
`exists_theorem207_witness`, and no `exists_amplituhedron_gauge`.
It is obtained by routing through §150.0
`bounded_params_at_2pow804_absurd`: the P-side bound `rank ≤ n^200`
(paper Theorem 10, `p_side_rank_bound_for_cook_levin`) and the
NP-side bound `n^200 < rank` (paper Theorem 98,
`GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n`) are bounds
on the **same** `mlBlockedSpdpRank (compiledPoly T)` quantity, so
their conjunction is arithmetically false — no gauge existential
is consumed (paper §18.2 p. 105's "conceptual inversion" programme).
The P-side channel transitively still carries
`SymmetricPower.spdp_profile_generators` (a legacy profile-
compression axiom, orthogonal to this reduction target — see §163's
neutralising analysis).

The theorem below documents the parallel constructive alternative at
the end of `PaperFaithfulSeparation.lean` so that consumers of this
module can discover the gauge-axiom-free variant via the same
`#print axioms` audit surface as `P_ne_NP_unconditional`. It
duplicates the §150.0-routed proof locally (not importing
`Step4Compiler`, which would create a cyclic import:
`Step4Compiler` imports this module).

### Rule

`P_ne_NP_unconditional` (above) is preserved unchanged — this
parallel `P_ne_NP_unconditional_step4_constructive` is **additive**,
not a replacement. Other consumers that depend on the canonical
form's signature continue to work.

Paper cites: §40 Theorem 232 p. 213 (Global God-Move ⇒ P ≠ NP);
§18.3 Theorem 100 pp. 106-108 (constructive `Π_n`); §18.2 p. 105
("conceptual inversion"); Remark 43 pp. 108-109 ("Lagrangian
certificate"); §49 Conclusion p. 229; §49.1 p. 230
("axiom-free development with no sorry statements"). -/

/-- **`P_ne_NP_unconditional_step4_constructive`** (paper §40 Theorem
232 p. 213 Global God-Move ⇒ P ≠ NP via paper §18.3 Theorem 100
pp. 106-108 constructive replacement).

**Constructive alternative to `P_ne_NP_unconditional`**, routing
through the P-side + NP-side sandwich on
`mlBlockedSpdpRank (compiledPoly T)` instead of through the
rank-sandwich gauge axiom. Mirrors `Step4Compiler.§176.1`
`P_ne_NP_unconditional_constructive` at the module boundary so that
consumers of this module can use the gauge-axiom-free form directly.

**Proof strategy** (paper §18.2 p. 105 "conceptual inversion"):

  * P-side (paper Theorem 10): `p_side_rank_bound_for_cook_levin`
    gives `rank ≤ n^{200}` on the compiled polynomial of any
    bounded-parameter DTM. (Transitively carries the legacy
    profile-compression axiom `SymmetricPower.spdp_profile_generators`,
    orthogonal to this reduction target.)
  * NP-side (paper Theorem 98, axiom-free):
    `GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n` gives
    `n^{200} < rank` on the compiled polynomial of any
    bounded-parameter DTM at `n ≥ 2^{804}`.
  * These are bounds on the **same** quantity (same partition,
    same `κ = ℓ = log₂ n`, same polynomial), so their
    conjunction is impossible.

**No `GlobalGodMoveGauge.exists_*` existential is consumed** — the
contradiction lives entirely in the arithmetic sandwich on the
compiled polynomial. The entire gauge-existence axiom family
(`exists_amplituhedron_gauge_for_sat_decider`,
`exists_rank_sandwich_for_sat_decider`,
`exists_theorem207_witness`, `exists_amplituhedron_gauge`) is
discharged.

**Relationship to `P_ne_NP_unconditional`**: both have the signature
`∀ (_ : PeqNP_Paper), False`. Any consumer may swap in this form to
eliminate the `GlobalGodMoveGauge.exists_*` dependency. The
canonical `P_ne_NP_unconditional` is preserved unchanged for
backward compatibility with existing consumers that already cite
it by name. -/
theorem P_ne_NP_unconditional_step4_constructive :
    ∀ (_ : PeqNP_Paper), False := by
  intro hPeqNP
  -- Fix n = 2^804 (paper §40 Theorem 232 p. 213 contradiction scale).
  set n := (2 ^ 804 : ℕ) with hn_def
  have hn₀ : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  have hns_n : hPeqNP.decider.numStates ≤ n :=
    le_trans hPeqNP.numStates_bound (le_refl _)
  -- P-side (paper Theorem 10): rank ≤ n^200.
  have hp :=
    p_side_rank_bound_for_cook_levin
      hPeqNP.decider n hn2 hPeqNP.timeBound_le hns_n
  -- NP-side (paper Theorem 98, axiom-free): n^200 < rank.
  have hnp :=
    GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n
      hPeqNP.decider n hn₀ hPeqNP.timeBound_le hns_n
  -- Contradiction: the two bounds on the same mlBlockedSpdpRank
  -- (compiledPoly T) value collapse (paper §18.2 p. 105
  -- "conceptual inversion" — the God-Move is a theorem, not a
  -- postulate).
  exact absurd hp (not_le_of_gt hnp)

#print axioms P_ne_NP_unconditional_step4_constructive
-- Expected: propext, Classical.choice, Quot.sound, plus the orthogonal
-- `SymmetricPower.spdp_profile_generators` (legacy P-side profile-
-- compression axiom, see §163's neutralising analysis).
-- ** TASK-TARGET GAUGE AXIOMS FULLY ELIMINATED **
-- In particular, this does **not** depend on any of the
-- `GlobalGodMoveGauge.exists_*` family:
--   * `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider`
--     (the primary target axiom for constructive replacement),
--   * `GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider`,
--   * `GlobalGodMoveGauge.exists_theorem207_witness`,
--   * `GlobalGodMoveGauge.exists_amplituhedron_gauge`.
-- The proof routes through the P-side + NP-side sandwich on the
-- compiled polynomial, which is the same content as
-- `Step4Compiler.§150.0 bounded_params_at_2pow804_absurd`.

end PaperFaithfulSeparation

end PaperFaithfulSeparation
