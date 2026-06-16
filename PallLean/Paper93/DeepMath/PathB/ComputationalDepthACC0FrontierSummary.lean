import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0QuantError
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModPExact
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTExactCompose
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsFastSat
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsRealizationSplit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BoundedDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NFrameLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CollapseLift
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankWhp
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LowRankFragment
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BoundedOverlapRank
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountSwitching
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ChainCellCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ClusteredRank
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LaminarCellCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BlockProductCellCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RandomRestrictionCellCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0VCCellCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DirectCellConcentration
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountHardRegime
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SunflowerCellCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountCharacterization
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RefinedObserverModel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MODNoGo
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MODResidualObserver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PivotToPolynomialMethod
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsCashoutFromPolynomial
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BoundaryObserverControl
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ControlShrinkage
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SparseCounting
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymLayerReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LevelCounts
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ElementarySymmetric
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BinomialInversion

/-!
# ACC⁰ frontier summary — the dependency graph as Lean theorems

A single readable file that re-states the converged `ACC⁰` boundary map as Lean theorems, so the corpus's claim is
checkable at a glance.  Each "pillar" below is *re-exported from its proved source*; the Williams route is assembled
into one conditional theorem whose only open inputs are the two genuine walls.

```
 AC⁰ polynomial method (quantitative)         PROVED   ac0_approximation_quantitative      (…ACC0QuantError)
 MOD_p exact low-degree over F_p              PROVED   modp_exact_low_degree               (…ACC0ModPExact)
 exact SYM∘AND decoding (every ACC0Circuit)   PROVED   exact_symAnd_decoding               (…ACC0YBTExactCompose)
 Williams fastSat count-search (quantitative) PROVED   fastSat_quantitative                (…ACC0WilliamsFastSat)
 realization socket split + self-audit        PROVED   timeHierarchy_is_the_separation     (…ACC0WilliamsRealizationSplit)
 ── size wall CROSSED on three restricted fragments (each + speedup, all PROVED) ──────────────────────────
 fragment 1: O(log n) leaves                  PROVED   restricted_exact_by_leaves          (…ACC0RestrictedYBT)
 fragment 2: support footprint < n            PROVED   restricted_exact_by_footprint       (…ACC0BoundedOverlapMOD)
 fragment 3: bounded (binary) depth           PROVED   restricted_exact_by_depth           (…ACC0BoundedDepth)
 restricted Williams speedup (super-poly)     PROVED   restricted_speedup_by_footprint/_depth (…ACC0RestrictedWilliamsSpeedup)
 ───────────────────────────────────────────────────────────────────────────────────────────────────────
 Williams route to NEXP ⊄ ACC⁰                CONDITIONAL on the two remaining walls:
   williams_route_reduces_to_two_sockets :
     (exact + quasipolynomial SYM∘AND for all ACC⁰)  ∧  (NTIME-hierarchy / Williams' method)  ⇒  NEXP ⊄ ACC⁰
 ── N-Frame route: ONE socket (bridge proved), discharged on bounded fragments ───────────────────────────
 bridge (collapse ⇒ low correlation)          PROVED   nframe_bridge                       (…ACC0CellCollapseRoute)
 composition (collapse lifts under budget)    PROVED   nframe_collapse_composes            (…ACC0CollapseLift)
 fragment (disjoint supports, unconditional)  PROVED   nframe_unconditional_disjoint       (…ACC0DisjointCollapse)
 N-Frame lower bound (ONE socket)             CONDITIONAL on cell collapse:
   nframe_lower_bound : (cell collapse for the predictor class)  ⇒  (holonomy lower bound)
 ── rank route: the sharpened N-Frame route (rank, not survivor count) ────────────────────────────────────
 rank sharp bridge (2^rank<|L| ⇒ low corr)    PROVED   rank_bridge                         (…ACC0RankBridge)
 rank subsumes survivors (cellRank≤survivors) PROVED   rank_subsumes_survivor              (…ACC0RankBridge)
 rank fragment (equal supports, any k)        PROVED   rank_fragment_equal_supports        (…ACC0LowRankFragment)
 probabilistic low-rank restriction           PROVED   rank_random_restriction             (…ACC0RandomRestrictionRank)
 rank whp (two-event, weaker feasibility)     PROVED   rank_whp                            (…ACC0RankWhp)
 rank composition (subadditive through layer) PROVED   rank_append_subadditive             (…ACC0RankComposition)
 ── cell-count route: the sharpest observer invariant (cells, not rank) — the OFFICIAL FINAL TARGET ───────
 cell-count bridge (cells < |L| ⇒ low corr)   PROVED   cellcount_bridge                    (…ACC0CellCountRoute)
 cells subsume rank (2^cellRank < |L| ⇒ …)     PROVED   cellcount_subsumes_rank             (…ACC0CellCountRoute)
 chain/nested fragment (full rank, ≤k+1 cells) PROVED   cellcount_chain_fragment            (…ACC0ChainCellCount)
 clustered fragment (cellRank ≤ d+r)           PROVED   cellcount_clustered_fragment        (…ACC0ClusteredRank)
 low-VC fragment (Sauer–Shelah ∑C(k,i), no rk) PROVED   cellcount_lowVC_le                  (…ACC0VCCellCount)
 sunflower fragment (wide overlap, ≤k+2)       PROVED   cellcount_sunflower                 (…ACC0SunflowerCellCount)
 laminar fragment (nested-or-disjoint, ≤k+1)   PROVED   cellcount_laminar_fragment          (…ACC0LaminarCellCount)
 block-product fragment (cells multiply, ∏)    PROVED   cellcount_block_product             (…ACC0BlockProductCellCount)
 cell-count composition (submult. ×, append)   PROVED   cellcount_append_submultiplicative  (…ACC0CellCountComposition)
 cell-count socket is the weakest socket       PROVED   cellcount_socket_is_weakest         (…ACC0CellCountSwitching)
 direct tail (Pr[≥a] ≤ Pr[|L|≥a], no 2^surv)   PROVED   cellcount_direct_tail               (…ACC0DirectCellConcentration)
 direct first moment (Exp ≤ globalCellCount)   PROVED   cellcount_expected_le_global        (…ACC0DirectCellConcentration)
 few gates ⇒ collapse (2^k<n, deterministic)   PROVED   cellcount_few_gates_forces          (…ACC0DirectCellConcentration)
 cell-count Markov tail (Pr[≥a] ≤ Exp/a)       PROVED   cellcount_markov                    (…ACC0RandomRestrictionCellCount)
 cell-count whp (needs a≤b, no 2^a≤b)          PROVED   cellcount_whp                       (…ACC0RandomRestrictionCellCount)
 cell-count whp subsumes rank/survivor whp     PROVED   cellcount_whp_subsumes_rank         (…ACC0RandomRestrictionCellCount)
 first-moment restriction (Exp≤B<a ⇒ ∃L)       PROVED   cellcount_random_restriction        (…ACC0RandomRestrictionCellCount)
 cell-count lower bound (ONE socket)           CONDITIONAL on FullACC0ForcesLowCellCount:
   cellcount_lower_bound : NFrameLowCellCount sys → ACC0HolonomyLowerBound sys tops
 hard-regime reduction (open lives here only)  PROVED   cellcount_full_of_hardRegime_resolved (…ACC0CellCountHardRegime)
 EXACT characterization (socket ⟺ global<n)    PROVED   cellcount_socket_iff_global_lt      (…ACC0CellCountCharacterization)
 socket is FALSE in the hard regime            PROVED   cellcount_socket_false_in_hardRegime (…ACC0CellCountCharacterization)
 ── CEILING (proved): ACC0ForcesLowCellCount ⟺ globalCellCount < n ⟺ membership map non-injective. ───────
 ──   Membership restriction CANNOT merge (a separating gate always survives); FALSE in the hard regime. ─
 ── RICHER variable-fixing model — restriction CAN merge ──────────────────────────────────────────────────
 refined model strictly beats membership      PROVED   refined_observer_strictly_beats_membership (…ACC0RefinedObserverModel)
 refined merging (inactive separators merge)   PROVED   refined_observer_merge              (…ACC0RefinedObserverModel)
 refined correlation bridge (collapse⇒no corr) PROVED   refined_observer_collapse_implies_low_correlation (…ACC0RefinedObserverModel)
 ── MOD NO-GO (proved): the variable-fixing merging is INERT for symmetric gates ─────────────────────────
 MOD-refined = membership on free coords       PROVED   mod_refined_eq_membership_on_free   (…ACC0MODNoGo)
 MOD gives no merging gain (⟺ SameCell)        PROVED   mod_refined_no_merging_gain         (…ACC0MODNoGo)
 parity constant ⟺ support fully fixed         PROVED   mod_parity_constant_iff_fully_fixed (…ACC0MODResidualObserver)
 residual observer reduces to membership       PROVED   mod_residual_reduces_to_membership  (…ACC0MODResidualObserver)
 ── THE WALL (pinned with gate semantics): MOD has NO absorbing value (parity constant iff support ──────
 ──   fully fixed; AND constant from one fixed-false input). A coordinate's affine contribution to a ────
 ──   linear gate IS its membership ⇒ the residual/refined observer = membership observer on free ───────
 ──   coords ⇒ inherits the hard-regime ceiling. The ENTIRE observer/merging programme is membership- ───
 ──   bounded for MOD ⇒ ACC⁰ needs the POLYNOMIAL METHOD (low-degree/rank), not observer cells. ─────────
 ── PIVOT to the polynomial method — effective dimension bites where the observer cannot ─────────────────
 poly degree < n ⇒ ≠ holonomy parity (exact)   PROVED   polynomial_method_separates_holonomy_parity (…ACC0PivotToPolynomialMethod)
 RS size bound 2^Ω(n^{1/2d}) on fParity univ   PROVED   nframe_parity_target_size_lower_bound (…Layer3NFrameParityRS)
 ── Williams cash-out (CONDITIONAL): polynomial method discharges the representation half ────────────────
 RS representation half (SYM∘AND) discharged   PROVED   rsMonoANDRepresentation_proved      (…ACC0WilliamsCashoutFromPolynomial)
 cash-out chain (impl., NOT the separation)    PROVED   williams_cashout_from_polynomial_method (…ACC0WilliamsCashoutFromPolynomial)
 sparse-counting kernel (cube-sum=Σc_S·2^{n-|S|}) PROVED  sparse_symand_cube_sum              (…ACC0SparseCounting)
 SYM-layer reduction (SAT ⟺ over k+1 levels)   PROVED   symand_sat_decided_by_levels        (…ACC0SymLayerReduction)
 binomial moments ↔ level counts (N_t bridge)  PROVED   level_counts_from_binomial_moments  (…ACC0LevelCounts)
 e_d-sparsity (moment = sparse d-subset sum)   PROVED   moment_integrand_is_sparse          (…ACC0ElementarySymmetric)
 binomial inversion (N_t = alt-sum of moments) PROVED   level_count_eq_alternating_moments  (…ACC0BinomialInversion)
 ── OPEN input: counting socket (rep ⇒ sub-2ⁿ ACC⁰-SAT). PROVED: rep half, sparse cube-sum kernel, ──────
 ──   SYM-layer reduction (SAT ⟺ k+1 levels), moments↔levels bridge, e_d-sparsity, binomial inversion. ──
 ──   The N_t are now an explicit alternating sum of kernel-computable sparse moments. SOLE remaining ───
 ──   input: Beigel-Tarui quasipoly #monomials bound for ACC⁰; then williams collapse + time hierarchy. ─
 ── Dynamic N-frame: the BOUNDARY selects the observer (unification of all routes) ───────────────────────
 boundary selects observer (absorbing⟺AND/OR)  PROVED   boundary_selects_absorbing_iff_andOr (…ACC0BoundaryObserverControl)
 ──   AND/OR→absorbing (refined collapses); MOD→linearResidual (=membership, bounded)→polynomialSpan ─────
 ──   (RS separates)→countingState (Williams cash-out). Concrete countingState instance: ────────────────
 ──   …ACC0OracleControl.oracle_control_over_mod_searchable (few-MOD fragment SAT-searchable < 2ⁿ); ──────
 ──   open rung random_restriction_makes_control_shallow = the state-shrinkage the process needs. ───────
 leaf-restriction shrinkage (state ≤ 2^|free|) PROVED   control_restriction_shallow/_searchable (…ACC0ControlShrinkage)
 ──   BARRIER (honest): searches the RESTRICTED composite; x-realizing leaf shrinkage over wide MOD is ──
 ──   blocked — a MOD leaf is x-constant only when its whole support is fixed (no absorbing value). ─────
 ── (implied by ACC0ForcesLowCellRank ⊇ the survivor socket; subsumes chain/laminar the rank route misses)─
```

## What is proved (clean axioms, no `sorry`)

* `ac0_approximation_quantitative` — re-export of `approximable_full`: every `MOD`-free circuit has an `F₂`
  approximant of degree `≤ t^depth` and error `≤ size·2^{-t}`.
* `modp_exact_low_degree` — re-export of `modp_exact_eval`: `MOD_p` is *exactly* the degree-`(p−1)` `F_p` polynomial.
* `exact_symAnd_decoding` — re-export of `acc0circuit_hasSymAndForm`: every `ACC0Circuit` has an *exact* `SYM∘AND`
  form (size `symAndSize C`).
* `fastSat_quantitative` — re-export of `symAnd_williams_fastSat`: a low-degree `SYM∘AND` decides SAT by a count-cell
  search with quantitative Williams savings.
* `timeHierarchy_is_the_separation` — re-export of the self-audit: the deep realization sub-socket is `⟺ NEXP ⊄ ACC⁰`.
* `restricted_exact_by_leaves` / `_footprint` / `_depth` — the three controllable fragments where the *size* wall is
  crossed (exact `SYM∘AND` below `2^n`), all from the one multiplicative `psize = ∏ leaf-bases` identity.
* `restricted_speedup_by_footprint` / `_depth` — the restricted Williams speedup: those fragments get a count-cell
  `ACC⁰`-SAT algorithm with *super-polynomial* savings `2^k`.
* **`williams_route_reduces_to_two_sockets`** — the headline: the whole route is one conditional theorem; its only
  non-routine inputs are (A) the exact-quasipolynomial `SYM∘AND` socket and (B) the time-hierarchy socket.
* The **N-Frame route**: `nframe_bridge` (collapse ⇒ low correlation, *proved*), `nframe_collapse_composes`
  (collapse lifts through a layer under a survivor budget), `nframe_unconditional_disjoint` (the socket discharged on
  disjoint supports — *unconditional*), and **`nframe_lower_bound`** — the holonomy lower bound from *one* socket
  (cell collapse), the N-Frame analogue of the Williams two-socket reduction, sharper because the bridge is proved.
* The **rank route** (the sharpened N-Frame route): `rank_bridge` (`2^{cellRank} < |L| ⇒` low correlation — cell
  count by `F₂`-rank, not survivor count), `rank_subsumes_survivor` (`cellRank ≤ survivingCount`),
  `rank_fragment_equal_supports` (equal supports, any gate count — *unconditional*, where survivors are powerless),
  `rank_random_restriction` (a `p`-biased low-rank live set), `rank_whp` (the two-event intersection on the rank
  tail — strictly weaker feasibility than the survivor whp route, which it subsumes), and `rank_append_subadditive`
  / `rank_collapse_lifts_budget` (depth composition as *rank-budget* accounting: `cellRank` is subadditive under
  `append`, so a layer adding only `r₂` observer rank keeps the composite collapse within `r₁+r₂`).

## Honest scope — the two remaining walls, named and isolated

The route is **conditional**, not a proof.  Open input (A) = an exact `SYM∘AND` of *quasipolynomial* size for all
`ACC⁰` (the size wall — exactness is proved, `…ACC0YBTExactCompose`; quasipoly size is open and stops at prime-power
`MOD`, the composite-`MOD` barrier).  Open input (B) = the nondeterministic time hierarchy / Williams' algorithmic
method (`timeHierarchy_is_the_separation` proves it *is* the separation).  Everything between them — encoding, cost
arithmetic, depth induction, decoding — is proved or routine.  The size wall (A) is *crossed* on three restricted
fragments (`restricted_exact_by_leaves`/`_footprint`/`_depth`), which feed the restricted Williams speedup — but
*full* `ACC⁰` needs all three controls to fail at once (poly leaves, footprint `≫ n`, super-constant depth), so the
fragments do not touch the full wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox
open PallLean.Paper93.DeepMath.PathB.ACC0OrStep
open PallLean.Paper93.DeepMath.PathB.ACC0QuantDegree
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat
open PallLean.Paper93.DeepMath.PathB.ACC0QuantError
open PallLean.Paper93.DeepMath.PathB.ACC0ModPExact
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRealizationSplit
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket
open PallLean.Paper93.DeepMath.PathB.ACC0RestrictedYBT
open PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapMOD
open PallLean.Paper93.DeepMath.PathB.ACC0RestrictedWilliamsSpeedup
open PallLean.Paper93.DeepMath.PathB.ACC0BoundedDepth
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0DisjointCollapse
open PallLean.Paper93.DeepMath.PathB.ACC0CollapseLift
open PallLean.Paper93.DeepMath.PathB.ACC0NFrameLowerBound
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionRank
open PallLean.Paper93.DeepMath.PathB.ACC0LowRankFragment
open PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapRank
open PallLean.Paper93.DeepMath.PathB.ACC0RankWhp
open PallLean.Paper93.DeepMath.PathB.ACC0RankComposition
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountSwitching
open PallLean.Paper93.DeepMath.PathB.ACC0ChainCellCount
open PallLean.Paper93.DeepMath.PathB.ACC0ClusteredRank
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountComposition
open PallLean.Paper93.DeepMath.PathB.ACC0LaminarCellCount
open PallLean.Paper93.DeepMath.PathB.ACC0BlockProductCellCount
open PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionCellCount
open PallLean.Paper93.DeepMath.PathB.ACC0VCCellCount
open PallLean.Paper93.DeepMath.PathB.ACC0DirectCellConcentration
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountHardRegime
open PallLean.Paper93.DeepMath.PathB.ACC0SunflowerCellCount
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountCharacterization
open PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel
open PallLean.Paper93.DeepMath.PathB.ACC0MODNoGo
open PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PivotToPolynomialMethod
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashoutFromPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0BoundaryObserverControl
open PallLean.Paper93.DeepMath.PathB.ACC0ControlShrinkage
open PallLean.Paper93.DeepMath.PathB.ACC0SparseCounting
open PallLean.Paper93.DeepMath.PathB.ACC0SymLayerReduction
open PallLean.Paper93.DeepMath.PathB.ACC0LevelCounts
open PallLean.Paper93.DeepMath.PathB.ACC0ElementarySymmetric
open PallLean.Paper93.DeepMath.PathB.ACC0BinomialInversion

/-! ## The proved pillars (re-exported) -/

/-- **Pillar 1 (proved): the AC⁰ polynomial method, quantitative.**  Every `MOD`-free circuit `C` has an `F₂`
approximant of degree `≤ t^(depth C)` and error `≤ size·2^{-t}` (here in the `2^t·error ≤ size·2^n` form). -/
theorem ac0_approximation_quantitative {n t : ℕ} (ht : 1 ≤ t) (C : Circ n) :
    ∃ Q : MvPolynomial (Fin n) (ZMod 2),
      Q.totalDegree ≤ t ^ cdepth C
        ∧ 2 ^ t * (perr Q (fun x => Circ.eval x C)).card ≤ Circ.size C * Fintype.card (Fin n → Bool) :=
  approximable_full ht C

/-- **Pillar 2 (proved): `MOD_p` is exactly the degree-`(p−1)` polynomial over `F_p` (Fermat).** -/
theorem modp_exact_low_degree {n p : ℕ} [Fact p.Prime] (x : Fin n → Bool) (S : Finset (Fin n)) :
    eval (fun i => boolToZMod p (x i)) (modpPoly p S) = boolToZMod p (modpBool p S x) :=
  modp_exact_eval x S

/-- **Pillar 3 (proved): every `ACC0Circuit` has an *exact* `SYM∘AND` form** (of size `symAndSize C`).  The decoding /
composition half of YBT — proved in full; only quasipolynomial *size* remains open. -/
theorem exact_symAnd_decoding {n : ℕ} (C : ACC0Circuit n) :
    HasSymAndForm (fun x => eval C x) (symAndSize C) :=
  acc0circuit_hasSymAndForm C

/-- **Pillar 4 (proved): the Williams `fastSat` count-search is quantitative.**  A degree-`≤D` injective `SYM∘AND`
decides SAT by the count-cell image and delivers Williams savings `≥ 2^k` when the gate count fits `2^{n−k}`. -/
theorem fastSat_quantitative {n m D : ℕ} (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool)
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ D) {k : ℕ} (hkn : k ≤ n)
    (hfit : (∑ i ∈ Finset.range (D + 1), n.choose i) + 1 ≤ 2 ^ (n - k)) :
    2 ^ k * (Finset.univ.image
        (ACC0SymmetricObserver.gateCount (fun j x => ACC0PolyToSymAnd.monoAND (mono j) x))).card
      ≤ 2 ^ n :=
  (symAnd_williams_fastSat mono h hinj hdeg hkn hfit).2.2

/-! ## The restricted fragments — where the size wall is crossed (re-exported) -/

/-- **Fragment 1 (proved): logarithmic leaf count ⇒ exact quasipolynomial `SYM∘AND`.**  `leafCount C ≤ ℓ`,
`maxBase C ≤ B`, `B^ℓ < 2^n ⇒ HasExactSymAndForm C`.  For `ℓ = O(log n)`, `B = poly`, `B^ℓ = 2^{O(log²n)} < 2^n`. -/
theorem restricted_exact_by_leaves {n : ℕ} (C : ACC0Circuit n) {ℓ B : ℕ}
    (hlc : leafCount C ≤ ℓ) (hb : maxBase C ≤ B) (hfit : B ^ ℓ < 2 ^ n) :
    HasExactSymAndForm C :=
  restricted_acc0_quasipoly C hlc hb hfit

/-- **Fragment 2 (proved): small support footprint ⇒ exact `SYM∘AND` (bounded-overlap / disjoint `MOD`).**
`baseSum C < n ⇒ HasExactSymAndForm C`, sharp since `baseSum = log₂ psize`. -/
theorem restricted_exact_by_footprint {n : ℕ} (C : ACC0Circuit n) (h : baseSum C < n) :
    HasExactSymAndForm C :=
  acc0_exact_of_baseSum_lt C h

/-- **Fragment 3 (proved): bounded (binary) depth + poly base ⇒ exact `SYM∘AND`.**  `depth C ≤ d`, `maxBase C ≤ B`,
`B^{2^d} < 2^n ⇒ HasExactSymAndForm C`.  Polynomial size for constant `d`. -/
theorem restricted_exact_by_depth {n : ℕ} (C : ACC0Circuit n) {d B : ℕ}
    (hd : depth C ≤ d) (hb : maxBase C ≤ B) (hfit : B ^ (2 ^ d) < 2 ^ n) :
    HasExactSymAndForm C :=
  bounded_depth_exact C hd hb hfit

/-- **Restricted Williams speedup by footprint (proved): footprint `≤ n−k` ⇒ SAT in `≤ 2^{n−k}` cells, savings
`≥ 2^k`.**  For footprint `= polylog`, the savings is `2^{n−polylog}` — super-polynomial. -/
theorem restricted_speedup_by_footprint {n : ℕ} (C : ACC0Circuit n) {k : ℕ}
    (hk : k ≤ n) (hfoot : baseSum C + k ≤ n) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval C) ↔ ∃ c ∈ cells, dec c = true)
      ∧ cells.card ≤ 2 ^ (n - k) ∧ 2 ^ k * cells.card ≤ 2 ^ n :=
  restricted_williams_speedup C hk hfoot

/-- **Restricted Williams speedup by depth (proved): bounded depth + poly base ⇒ super-polynomial savings.** -/
theorem restricted_speedup_by_depth {n : ℕ} (C : ACC0Circuit n) {d B k : ℕ}
    (hd : depth C ≤ d) (hb : maxBase C ≤ B) (hk : k ≤ n) (hfit : B ^ (2 ^ d) ≤ 2 ^ (n - k)) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval C) ↔ ∃ c ∈ cells, dec c = true)
      ∧ cells.card ≤ 2 ^ (n - k) ∧ 2 ^ k * cells.card ≤ 2 ^ n :=
  bounded_depth_williams_speedup C hd hb hk hfit

/-! ## The Williams route, reduced to two sockets -/

/-- **Self-audit (proved, re-exported): the deep realization sub-socket *is* the separation.**  Once a uniform
`ACC⁰`-SAT speedup is established, the time-hierarchy sub-socket is logically equivalent to `NEXP ⊄ ACC⁰`. -/
theorem timeHierarchy_is_the_separation {Uniform NEXPnotACC0 : Prop} (hu : Uniform) :
    TimeHierarchySocket Uniform NEXPnotACC0 ↔ NEXPnotACC0 :=
  timeHierarchy_socket_iff_separation Uniform NEXPnotACC0 hu

/-- **The headline (proved): the entire Williams route is one conditional theorem on two deep sockets.**

Given
* **(A)** the exact-quasipolynomial `SYM∘AND` socket for all `ACC⁰` — here the `MixedACCDepthReductionSocket`
  (depth-2 residue normal form), the *size* content of YBT; and
* **(B)** the time-hierarchy / Williams' algorithmic-method socket `TimeHierarchySocket`,

together with the *routine* realization sub-sockets (`EncodingSocket`, `CostBridgeSocket`, `UniformitySocket`),
the separation `NEXP ⊄ ACC⁰` follows.  All content is in (A) and (B); the rest is proved or routine. -/
theorem williams_route_reduces_to_two_sockets
    {EncodedAlg TimeBounded Uniform NEXPnotACC0 : Prop}
    -- (A) the exact-quasipolynomial SYM∘AND / depth-reduction socket:
    (hExact : ∀ (n : ℕ) (C : ACC0Circuit n),
      ACC0ResidueDepthReduction.MixedACCDepthReductionSocket C)
    -- routine realization bookkeeping:
    (s1 : EncodingSocket EncodedAlg)
    (s2 : CostBridgeSocket EncodedAlg TimeBounded)
    (s3 : UniformitySocket TimeBounded Uniform)
    -- (B) the deep time-hierarchy socket:
    (hTimeHierarchy : TimeHierarchySocket Uniform NEXPnotACC0) :
    NEXPnotACC0 :=
  residue_cashout_bundled hExact
    (routine_reduce_to_timeHierarchy EncodedAlg TimeBounded Uniform NEXPnotACC0 s1 s2 s3 hTimeHierarchy)

/-! ## The N-Frame route — survival ⇒ low holonomy correlation (one socket, bridge proved) -/

/-- **N-Frame bridge (proved): cell collapse ⇒ low holonomy correlation.**  Re-export of the proved half of the
N-Frame route. -/
theorem nframe_bridge {k n : ℕ} (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (L : Finset (Fin n)) (h : CellCollapse supports L) : LowHolonomyCorrelation supports g :=
  cell_collapse_implies_low_holonomy_correlation supports g L h

/-- **N-Frame route, one socket (proved): the cell-collapse socket cashes out to low correlation.** -/
theorem nframe_route_one_socket {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (hcollapse : FullACC0ForcesCellCollapse supports) :
    LowHolonomyCorrelation supports g :=
  nframe_route supports g hcollapse

/-- **N-Frame composition (proved): collapse lifts through a layer under a survivor budget.**  Survivor counts add
across an appended layer, so `2^{s₁+s₂} < |L| ⇒` the composite collapses. -/
theorem nframe_collapse_composes {k₁ k₂ n : ℕ} (supp₁ : Fin k₁ → Finset (Fin n))
    (supp₂ : Fin k₂ → Finset (Fin n)) (L : Finset (Fin n))
    (hbudget : 2 ^ (survivingCount supp₁ L + survivingCount supp₂ L) < L.card) :
    CellCollapse (Fin.append supp₁ supp₂) L :=
  collapse_lifts_through_layer supp₁ supp₂ L hbudget

/-- **N-Frame fragment, unconditional (proved): disjoint supports with a size-`≥3` support give the lower bound.** -/
theorem nframe_unconditional_disjoint {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (hd : ∀ i j, i ≠ j → Disjoint (supports i) (supports j))
    (j₀ : Fin k) (hsize : 3 ≤ (supports j₀).card) : LowHolonomyCorrelation supports g :=
  disjoint_supports_low_holonomy_correlation supports g hd j₀ hsize

/-- **The N-Frame lower bound, one socket (proved), beside `williams_route_reduces_to_two_sockets`.**  For a class of
holonomy-predictors, the cell-collapse socket implies the holonomy lower bound — *one* socket, since the bridge is
proved. -/
theorem nframe_lower_bound {ι : Type} {n : ℕ} (sys : PredictorClass ι n)
    (tops : ∀ i, (Fin (sys i).1 → ℕ) → Bool) (h : NFrameCellCollapse sys) :
    ACC0HolonomyLowerBound sys tops :=
  nframe_acc_lower_bound sys tops h

/-! ## The rank route — the sharpened N-Frame route (rank, not survivor count) -/

/-- **Rank sharp bridge (proved): `2^{cellRank} < |L| ⇒ low holonomy correlation`.**  The cell count is governed by
the `F₂`-rank of the support incidence, not the survivor count. -/
theorem rank_bridge {k n : ℕ} (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (L : Finset (Fin n)) (h : 2 ^ cellRank supports L < L.card) :
    LowHolonomyCorrelation supports g :=
  rank_collapse_low_correlation supports g L h

/-- **Rank subsumes survivors (proved): `cellRank ≤ survivingCount`, so survivor collapse ⇒ rank collapse.** -/
theorem rank_subsumes_survivor {k n : ℕ} (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : 2 ^ survivingCount supports L < L.card) : 2 ^ cellRank supports L < L.card :=
  survivor_collapse_implies_rank_collapse supports L h

/-- **Rank fragment, unconditional (proved): equal supports — any gate count — fail to correlate.**  The survivor
route is powerless here (`survivingCount = k`), yet `cellRank ≤ 1`. -/
theorem rank_fragment_equal_supports {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (S : Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (hS : ∀ j, supports j = S) (hn : 3 ≤ n) :
    LowHolonomyCorrelation supports g :=
  equal_supports_low_correlation supports S g hS hn

/-- **Probabilistic low-rank restriction (proved): expected survivors `≤ B < a` ⇒ a live set with `cellRank < a`.** -/
theorem rank_random_restriction {k n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (B a : ℝ) (ha : 0 < a)
    (hE : Exp p (fun L => (survivingCount supports L : ℝ)) ≤ B) (hBa : B < a) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset, (cellRank supports L : ℝ) < a :=
  randomRestriction_forces_low_cellRank p hp0 hp1 supports B a ha hE hBa

/-- **The rank whp route (proved): the two-event intersection on the rank tail.**  `2^a ≤ b` and
`Pr[cellRank ≥ a] + Pr[|L| ≤ b] < 1` ⇒ low holonomy correlation — strictly weaker feasibility than the survivor
version, which it subsumes. -/
theorem rank_whp {k n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (a b : ℕ) (hab : 2 ^ a ≤ b)
    (hfeas : Pr p (fun L => a ≤ cellRank supports L)
        + Pr p (fun L : Finset (Fin n) => L.card ≤ b) < 1) :
    LowHolonomyCorrelation supports g :=
  rank_predictor_fails_whp p hp0 hp1 supports g a b hab hfeas

/-- **Rank growth through a layer (proved): `cellRank` is subadditive under `append`.** -/
theorem rank_append_subadditive {k₁ k₂ n : ℕ} (supp₁ : Fin k₁ → Finset (Fin n))
    (supp₂ : Fin k₂ → Finset (Fin n)) (L : Finset (Fin n)) :
    cellRank (Fin.append supp₁ supp₂) L ≤ cellRank supp₁ L + cellRank supp₂ L :=
  cellRank_append_le supp₁ supp₂ L

/-- **Rank-budget collapse lift (proved): a layer adding `≤ r₂` observer rank keeps the composite within budget.**
`2^{r₁+r₂} < |L|`, `cellRank supp₁ L ≤ r₁`, `cellRank supp₂ L ≤ r₂` ⇒ `2^{cellRank (append …)} < |L|`. -/
theorem rank_collapse_lifts_budget {k₁ k₂ n : ℕ} (supp₁ : Fin k₁ → Finset (Fin n))
    (supp₂ : Fin k₂ → Finset (Fin n)) (L : Finset (Fin n)) (r₁ r₂ : ℕ)
    (hbudget : 2 ^ (r₁ + r₂) < L.card) (h₁ : cellRank supp₁ L ≤ r₁) (h₂ : cellRank supp₂ L ≤ r₂) :
    2 ^ cellRank (Fin.append supp₁ supp₂) L < L.card :=
  rank_collapse_lifts_of_rank_budget supp₁ supp₂ L r₁ r₂ hbudget h₁ h₂

/-! ## The cell-count route — the sharpest observer invariant (cells, not rank); the official final target

The official open target is `FullACC0ForcesLowCellCount` (`∃ L, cellPatternCount supports L < |L|`), the *sharpest*
(weakest, most achievable) form of the N-Frame restriction lemma.  Since `cellPatternCount ≤ 2^{cellRank} ≤
2^{survivingCount}`, this socket is implied by the survivor and rank sockets, and it is strictly more general (chain /
nested supports have full rank but `≤ k+1` cells, missed by the rank route).  This section consolidates the **entire**
cell-count route; every piece below is proved (clean axioms), and the only open content is the hard regime.

**Core bridge & subsumption** — `cellcount_bridge` (`cellPatternCount < |L| ⇒` low correlation), `cellcount_subsumes_rank`
(`2^{cellRank} < |L| ⇒` collapse: cells subsume rank, hence survivors).

**Composition** — `cellcount_append_submultiplicative` (cell count is *submultiplicative* under `append`, vs additive
survivors / subadditive rank), `cellcount_collapse_lifts_budget` (`c₁·c₂ < |L| ⇒` collapse lifts through a layer).

**Structured fragments** (each unconditional on its hypothesis, no rank needed):
`cellcount_chain_fragment` (`≤ k+1`), `cellcount_laminar_fragment` (nested-or-disjoint, `≤ k+1`),
`cellcount_clustered_fragment` (`cellRank ≤ d+r`), `cellcount_sunflower` (common-core wide overlap, `≤ k+2`, outside
laminar), `cellcount_lowVC_le` / `cellcount_lowVC_low_correlation` (Sauer–Shelah `∑_{i≤d} C(k,i)`, the common
generalization — few patterns *without* low rank), `cellcount_block_product` (cells multiply over independent blocks).

**Probabilistic / first-moment** — `cellcount_markov` (`Pr[≥a] ≤ Exp/a`), `cellcount_whp` (two-event balance, needs only
`a ≤ b`), `cellcount_whp_subsumes_rank` (broadest whp: survivor ⊂ rank ⊂ cell-count), `cellcount_random_restriction`
(`Exp ≤ B < a ⇒ ∃ L` low-cell), and the deterministic-bound discharges `cellcount_bounded_distinct_expectation`
(`≤ 2^d`) [laminar/block discharges in their files].

**Direct concentration** (no `2^{survivors}`; cell count is `L`-monotone, bounded by the restriction-independent
`globalCellCount`) — `cellcount_direct_tail` (`Pr[≥a] ≤ Pr[|L|≥a]`), `cellcount_expected_le_global`
(`Exp ≤ globalCellCount`), `cellcount_few_gates_forces` (`2^k < n ⇒` collapse, deterministic).

**Socket, reduction & exact ceiling** — `cellcount_route_one_socket` / `cellcount_lower_bound` (the socket ⇒ holonomy
lower bound), `cellcount_socket_is_weakest` (survivor socket ⇒ this one), `cellcount_full_of_hardRegime_resolved` (the
socket reduces to the hard regime alone).  The socket is then *settled exactly*: `cellcount_socket_iff_global_lt`
(`FullACC0ForcesLowCellCount ⟺ globalCellCount < n ⟺` the membership map is non-injective) and
`cellcount_socket_false_in_hardRegime` (the hard regime forces `globalCellCount = n`, so the socket is **false** there).
A restriction *cannot merge* patterns in this membership-only model — a separating gate always survives — so the route
collapses exactly when two coordinates already share a global pattern (which the fragments force, but the hard regime
forbids).  Realizing restriction-induced merging requires a *richer* observer model (fixing variables ⇒ gates become
constant), strictly beyond this invariant. -/

/-- **Cell-count bridge (proved): `cellPatternCount supports L < |L| ⇒ low holonomy correlation`.**  The cell count —
not its rank — is the governing quantity; this is the sharpest collapse. -/
theorem cellcount_bridge {k n : ℕ} (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (L : Finset (Fin n)) (h : CellCountCollapse supports L) :
    LowHolonomyCorrelation supports g :=
  cellCountCollapse_implies_low_correlation supports g L h

/-- **Cell count subsumes rank (proved): `2^{cellRank} < |L| ⇒ CellCountCollapse`.**  A rank collapse is a special
case of a cell-count collapse, so the cell-count route subsumes the rank (hence survivor) route. -/
theorem cellcount_subsumes_rank {k n : ℕ} (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : 2 ^ cellRank supports L < L.card) : CellCountCollapse supports L :=
  rank_collapse_implies_cellCount_collapse supports L h

/-- **Cell-count fragment, unconditional (proved): chain / nested supports.**  `S₁ ⊆ … ⊆ S_k` can have full rank yet
`≤ k+1` cells; `k+1 < |L|` ⇒ low correlation — the class the rank route is too crude for. -/
theorem cellcount_chain_fragment {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (hch : ChainSupports supports) (L : Finset (Fin n))
    (hkL : k + 1 < L.card) : LowHolonomyCorrelation supports g :=
  chain_low_correlation supports g hch L hkL

/-- **Cell-count fragment, unconditional (proved): clustered supports.**  `d` cluster centers `+` `r`-dim variation
⇒ `cellRank ≤ d + r`; `2^{d+r} < n` ⇒ low correlation. -/
theorem cellcount_clustered_fragment {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (d r : ℕ) (h : ClusteredSupports supports d r) (hn : 2 ^ (d + r) < n) :
    LowHolonomyCorrelation supports g :=
  clustered_low_correlation supports g d r h hn

/-- **Cell-count composition (proved): submultiplicative under `append`.**  Depth composition *multiplies* cell counts
(vs additive survivors, subadditive rank). -/
theorem cellcount_append_submultiplicative {k₁ k₂ n : ℕ} (A : Fin k₁ → Finset (Fin n))
    (B : Fin k₂ → Finset (Fin n)) (L : Finset (Fin n)) :
    cellPatternCount (Fin.append A B) L ≤ cellPatternCount A L * cellPatternCount B L :=
  cellPatternCount_append_le A B L

/-- **Cell-count-budget collapse lift (proved): a layer adding `≤ c₂` cells keeps the composite within `c₁·c₂`.** -/
theorem cellcount_collapse_lifts_budget {k₁ k₂ n : ℕ} (A : Fin k₁ → Finset (Fin n))
    (B : Fin k₂ → Finset (Fin n)) (L : Finset (Fin n)) (c₁ c₂ : ℕ)
    (h₁ : cellPatternCount A L ≤ c₁) (h₂ : cellPatternCount B L ≤ c₂) (hbudget : c₁ * c₂ < L.card) :
    CellCountCollapse (Fin.append A B) L :=
  cellCount_collapse_of_budget A B L c₁ c₂ h₁ h₂ hbudget

/-- **The cell-count route, one socket (proved): the sharpest socket cashes out to low correlation.** -/
theorem cellcount_route_one_socket {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (h : FullACC0ForcesLowCellCount supports) :
    LowHolonomyCorrelation supports g :=
  nframe_cellcount_route supports g h

/-- **The cell-count socket is the weakest (proved): the survivor socket implies it.**  Hence every disjoint/bounded
discharge of the survivor socket discharges the official final target too. -/
theorem cellcount_socket_is_weakest {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (h : FullACC0ForcesCellCollapse supports) : FullACC0ForcesLowCellCount supports :=
  cellCollapse_implies_lowCellCount supports h

/-- **Cell-count fragment, unconditional (proved): laminar (nested-or-disjoint) supports.**  Generalizes chains: full
rank yet `≤ k+1` cells; `k+1 < |L|` ⇒ low correlation. -/
theorem cellcount_laminar_fragment {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (hlam : LaminarSupports supports) (L : Finset (Fin n))
    (hkL : k + 1 < L.card) : LowHolonomyCorrelation supports g :=
  laminar_low_correlation supports g hlam L hkL

/-- **Cell-count composition, block product (proved): cell count multiplies over independent blocks.**  `m` blocks of
`b` gates; `cellPatternCount (flatten) ≤ ∏ block cells`; `∏ < |L|` ⇒ low correlation. -/
theorem cellcount_block_product {m b n : ℕ} (supports : Fin m → Fin b → Finset (Fin n))
    (g : (Fin (m * b) → ℕ) → Bool) (L : Finset (Fin n))
    (h : (∏ i, cellPatternCount (supports i) L) < L.card) :
    LowHolonomyCorrelation (flatSupports supports) g :=
  block_product_low_correlation supports g L h

/-- **Cell-count Markov tail (proved): `Pr[cellPatternCount ≥ a] ≤ Exp[cellPatternCount] / a`.** -/
theorem cellcount_markov {k n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (a : ℝ) (ha : 0 < a) :
    Pr p (fun L => a ≤ (cellPatternCount supports L : ℝ))
      ≤ Exp p (fun L => (cellPatternCount supports L : ℝ)) / a :=
  Pr_cellPatternCount_ge_le_markov p hp0 hp1 supports a ha

/-- **Cell-count whp route (proved): the two-event balance needs only `a ≤ b`** — sharper than the rank whp's
`2^a ≤ b`, since the cell count compares to `|L|` directly. -/
theorem cellcount_whp {k n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (a b : ℕ) (hab : a ≤ b)
    (hfeas : Pr p (fun L => a ≤ cellPatternCount supports L)
        + Pr p (fun L : Finset (Fin n) => L.card ≤ b) < 1) :
    LowHolonomyCorrelation supports g :=
  cellCount_predictor_fails_whp p hp0 hp1 supports g a b hab hfeas

/-- **The cell-count whp subsumes the rank (hence survivor) whp (proved).**  Rank feasibility (`2^a ≤ b`) ⇒ the
cell-count route fires — the broadest of the three whp routes. -/
theorem cellcount_whp_subsumes_rank {k n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (a b : ℕ) (hab : 2 ^ a ≤ b)
    (hfeas : Pr p (fun L => a ≤ cellRank supports L)
        + Pr p (fun L : Finset (Fin n) => L.card ≤ b) < 1) :
    LowHolonomyCorrelation supports g :=
  cellCount_whp_subsumes_rank p hp0 hp1 supports g a b hab hfeas

/-- **Cell-count first-moment restriction (proved): `Exp[cellPatternCount] ≤ B < a ⇒ ∃ L, cellPatternCount < a`.**  The
open balance is bounding `Exp[cellPatternCount]` below `2^{survivingCount}` for wide overlapping `MOD` supports. -/
theorem cellcount_random_restriction {k n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (B a : ℝ) (ha : 0 < a)
    (hE : Exp p (fun L => (cellPatternCount supports L : ℝ)) ≤ B) (hBa : B < a) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset, (cellPatternCount supports L : ℝ) < a :=
  randomRestriction_forces_low_cellCount p hp0 hp1 supports B a ha hE hBa

/-- **Bounded-distinct first-moment discharge (proved): `≤ d` distinct supports ⇒ `Exp[cellPatternCount] ≤ 2ᵈ`.**  A
deterministic bound (independent of the gate count), so the first-moment route closes with no concentration. -/
theorem cellcount_bounded_distinct_expectation {k n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (d : ℕ) (hd : (Finset.univ.image supports).card ≤ d) :
    Exp p (fun L => (cellPatternCount supports L : ℝ)) ≤ ((2 ^ d : ℕ) : ℝ) :=
  bounded_distinct_expected_cellPatternCount_le p hp0 hp1 supports d hd

/-- **Low-VC fragment (proved): Sauer–Shelah cell bound.**  If the gate-membership family `{suppSet v : v ∈ L}` has VC
dimension `≤ d`, the cell count is `≤ ∑_{i ≤ d} C(k, i)` — few observer patterns *without* low rank, the common
generalization of bounded-distinct/clustered/laminar. -/
theorem cellcount_lowVC_le {k n : ℕ} (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) (d : ℕ)
    (hvc : cellVCdim supports L ≤ d) :
    cellPatternCount supports L ≤ ∑ i ∈ Finset.Iic d, k.choose i :=
  lowVC_cellPatternCount_le supports L d hvc

/-- **Low-VC ⇒ low correlation (proved): `∑_{i ≤ d} C(k, i) < |L|`.** -/
theorem cellcount_lowVC_low_correlation {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (L : Finset (Fin n)) (d : ℕ) (hvc : cellVCdim supports L ≤ d)
    (hlt : (∑ i ∈ Finset.Iic d, k.choose i) < L.card) :
    LowHolonomyCorrelation supports g :=
  lowVC_low_correlation supports g L d hvc hlt

/-- **Direct cell-count tail (proved): `Pr[cellPatternCount ≥ a] ≤ Pr[|L| ≥ a]`** — no `2^{survivors}`, since the cell
count is bounded by the live-set size directly. -/
theorem cellcount_direct_tail {k n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (a : ℕ) :
    Pr p (fun L => a ≤ cellPatternCount supports L)
      ≤ Pr p (fun L : Finset (Fin n) => a ≤ L.card) :=
  Pr_cellPatternCount_ge_le_size_tail p hp0 hp1 supports a

/-- **Direct first moment (proved): `Exp[cellPatternCount] ≤ globalCellCount`** — the restriction-independent ceiling,
not the exponential `Exp[2^{survivingCount}]`. -/
theorem cellcount_expected_le_global {k n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) :
    Exp p (fun L => (cellPatternCount supports L : ℝ)) ≤ ((globalCellCount supports : ℕ) : ℝ) :=
  expected_cellPatternCount_le_global p hp0 hp1 supports

/-- **Deterministic collapse, few gates (proved): `2^k < n ⇒ FullACC0ForcesLowCellCount`** — the low-resolution regime,
no probability at all. -/
theorem cellcount_few_gates_forces {k n : ℕ} (supports : Fin k → Finset (Fin n)) (h : 2 ^ k < n) :
    FullACC0ForcesLowCellCount supports :=
  few_gates_forces_lowCellCount supports h

/-- **Sunflower (common-core) overlapping fragment (proved): wide overlap ⇒ `≤ k+2` cells.**  `supports j = core ∪
petal j` with disjoint petals — every pair overlaps in the core, not laminar — yet `k+2 < |L| ⇒` low correlation. -/
theorem cellcount_sunflower {k n : ℕ} (supports : Fin k → Finset (Fin n)) (core : Finset (Fin n))
    (petal : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (hsf : SunflowerSupports supports core petal) (L : Finset (Fin n)) (hkL : k + 2 < L.card) :
    LowHolonomyCorrelation supports g :=
  sunflower_low_correlation supports core petal g hsf L hkL

/-- **The hard-regime reduction (proved): the open lemma reduces to the hard regime alone.**  If the open socket holds
whenever `supports` is hard on the cube, it holds outright — outside the hard regime the collapse is already proved. -/
theorem cellcount_full_of_hardRegime_resolved {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (h : HardRegime supports Finset.univ → FullACC0ForcesLowCellCount supports) :
    FullACC0ForcesLowCellCount supports :=
  full_of_hardRegime_resolved supports h

/-- **Exact characterization (proved): the socket holds iff the global pattern count drops below `n`** — equivalently,
iff the membership map is not injective.  A restriction cannot merge patterns (a separating gate always survives), so
the collapse is a purely global pattern-collision condition. -/
theorem cellcount_socket_iff_global_lt {k n : ℕ} (supports : Fin k → Finset (Fin n)) :
    FullACC0ForcesLowCellCount supports ↔ globalCellCount supports < n :=
  forcesLowCellCount_iff_global_lt supports

/-- **The socket is FALSE in the hard regime (proved).**  The hard regime forces `globalCellCount = n` (injective
patterns), so no per-`L` collapse exists — the membership-only invariant cannot reach the hard regime, and a
`StructuredOverlappingMOD ⇒ collapse` theorem would be proving a falsehood there. -/
theorem cellcount_socket_false_in_hardRegime {k n : ℕ} (supports : Fin k → Finset (Fin n))
    (h : HardRegime supports Finset.univ) : ¬ FullACC0ForcesLowCellCount supports :=
  not_forcesLowCellCount_of_hardRegime supports h

/-- **The richer variable-fixing observer model can merge where membership cannot (proved).**  A restriction making a
*separating* gate inactive (an `AND` gate with a fixed-`false` input) merges two refined cells — the strict gain that
breaks the membership ceiling.  Witness: `¬ CellCountCollapse` (membership) yet `RefinedCellCollapse` (refined). -/
theorem refined_observer_strictly_beats_membership :
    ∃ (n k : ℕ) (supports : Fin k → Finset (Fin n)) (ρ : Restriction n) (L : Finset (Fin n)),
      ¬ CellCountCollapse supports L ∧ RefinedCellCollapse ρ supports L :=
  refined_strictly_beats_membership

/-- **The refined merging power (proved): inactive separators merge.**  If `ρ` deactivates every gate separating `v, w`,
their refined patterns coincide — impossible in the membership model. -/
theorem refined_observer_merge {k n : ℕ} (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (v w : Fin n) (h : ∀ j, (v ∈ supports j ↔ w ∈ supports j) ∨ ¬ GateActive ρ supports j) :
    refinedCellPatternVec ρ supports v = refinedCellPatternVec ρ supports w :=
  refined_merge_of_inactive_separators ρ supports v w h

/-- **The refined correlation bridge (proved): refined collapse ⇒ no correlation.**  The variable-fixing analogue of the
membership bridge, firing on cells that *merge* under restriction (via swap-invariance over active gates) — beyond the
reach of the membership model. -/
theorem refined_observer_collapse_implies_low_correlation {k n : ℕ} (ρ : Restriction n)
    (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (L : Finset (Fin n))
    (h : RefinedCellCollapse ρ supports L) : RefinedLowCorrelation ρ supports g :=
  refinedCellCollapse_implies_refinedLowCorrelation ρ supports g L h

/-- **The MOD no-go (proved): the variable-fixing model gives no merging for symmetric gates.**  A `MOD` gate has no
absorbing value (active iff it reads a free input), so the `MOD`-refined pattern of a free coordinate equals its
membership pattern — the richer model collapses to the membership model on free coordinates. -/
theorem mod_refined_eq_membership_on_free {k n : ℕ} (ρ : Restriction n)
    (supports : Fin k → Finset (Fin n)) (v : Fin n) (hv : ρ v = none) :
    modRefinedCellPatternVec ρ supports v = cellPatternVec supports v :=
  modRefined_eq_membership_of_free ρ supports v hv

/-- **The MOD no-go, merging form (proved): two free coordinates merge under `MOD`-refinement iff they already share a
membership cell** — no gain over the membership ceiling, localizing the `ACC⁰` barrier to `MOD`. -/
theorem mod_refined_no_merging_gain {k n : ℕ} (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (v w : Fin n) (hv : ρ v = none) (hw : ρ w = none) :
    modRefinedCellPatternVec ρ supports v = modRefinedCellPatternVec ρ supports w
      ↔ PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation.SameCell supports v w :=
  mod_refined_merge_iff_sameCell ρ supports v w hv hw

/-- **MOD gate semantics (proved): a parity gate is constant under `ρ` iff its support is entirely fixed.**  The
forward direction is the no-absorbing-value statement; `MOD` has no absorbing value, unlike `AND`/`OR` — the exact
reason `AC⁰` switches under restriction and `ACC⁰` does not. -/
theorem mod_parity_constant_iff_fully_fixed {n : ℕ} (ρ : Restriction n) (S : Finset (Fin n)) :
    ParityConstant ρ S ↔ ∀ i ∈ S, ρ i ≠ none :=
  parity_constant_iff_support_fully_fixed ρ S

/-- **The residual observer reduces to membership (proved): no escape for `MOD`.**  A coordinate's affine contribution
to a linear gate is its membership, so over the free coordinates the residual observer is the membership observer —
inheriting the proved hard-regime ceiling.  The whole observer/coordinate-merging programme is membership-bounded for
`MOD`; `ACC⁰` needs the polynomial method. -/
theorem mod_residual_reduces_to_membership {k n : ℕ} (ρ : Restriction n)
    (supports : Fin k → Finset (Fin n)) (v : Fin n) (hv : ρ v = none) :
    residualSignature ρ supports v = cellPatternVec supports v :=
  residual_eq_membership_of_free ρ supports v hv

/-- **The pivot to the polynomial method (proved): exact effective-dimension separation.**  A polynomial of total
degree `< n` cannot equal the holonomy parity `x ↦ ∏ᵢ pmOne(xᵢ)` on the cube — its evaluation lands in the low-degree
span `V_D` which the holonomy parity escapes (effective dimension `≥ n`).  This is the dimension lever that bites on
`MOD` where the observer route cannot; the quantitative `AC⁰[p]` size bound is
`…Layer3NFrameParityRS.nframe_parity_target_size_lower_bound`. -/
theorem polynomial_method_separates_holonomy_parity {n : ℕ} (p : ℕ) [Fact p.Prime]
    (hp2 : (2 : ZMod p) ≠ 0) {D : ℕ} (hD : D < n) (h : MvPolynomial (Fin n) (ZMod p))
    (hdeg : h.totalDegree ≤ D) :
    (fun x : Fin n → Bool => MvPolynomial.eval (fun i => Layer3.boolToZMod p (x i)) h)
      ≠ (fun x : Fin n → Bool => ∏ i, Layer3.pmOne p (x i)) :=
  lowDegree_poly_ne_holonomy_parity p hp2 hD h hdeg

/-- **The Williams cash-out from the polynomial method (proved logic).**  The polynomial method discharges the
*representation* half of Williams' `ACC⁰`-SAT algorithm; the remaining inputs are the **counting** socket
(representation ⇒ sub-`2ⁿ` SAT — the open algorithmic heart), the **Williams** collapse, and the **time hierarchy**.
This proves the *implication*, not `NEXP ⊄ ACC⁰`. -/
theorem williams_cashout_from_polynomial_method
    (ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (counting : RSMonoANDRepresentation → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  williams_cashout_from_polynomial ACC0SatSpeedup NEXPHasACC0Circuits Collapse counting williams hierarchy

/-- **The boundary selects the observer (proved): the dynamic N-frame unification.**  The absorbing observer is
selected exactly by `AND`/`OR`; `MOD`/symmetric gates route to the residual ⤳ polynomial regime.  Each route is
grounded in a proved gate-semantics fact (`…ACC0BoundaryObserverControl`). -/
theorem boundary_selects_absorbing_iff_andOr (gk : GateKind) :
    boundarySelect gk = BoundaryContext.absorbing ↔ gk = GateKind.andOr :=
  boundarySelect_andOr_iff_absorbing gk

/-- **The sparse-counting kernel (proved): a sparse `SYM∘AND` polynomial's cube-sum is a closed form over its
coefficients.**  `∑_x Σ_{S∈𝒮} c_S·[∏_{i∈S} x_i] = Σ_{S∈𝒮} c_S·2^{n−|S|}` — the algorithmic heart of Williams' fast
counting, computable in `|𝒮|` operations with no `2ⁿ`-enumeration (sub-`2ⁿ` when `#monomials < 2ⁿ`). -/
theorem sparse_symand_cube_sum {n : ℕ} {R : Type*} [CommRing R] (𝒮 : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → R) :
    (∑ x : Fin n → Bool, ∑ S ∈ 𝒮, c S *
        (if PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd.monoAND S x = true then (1 : R) else 0))
      = ∑ S ∈ 𝒮, c S * (2 : R) ^ (n - S.card) :=
  sparse_cube_sum 𝒮 c

/-- **The SYM-layer reduction (proved): `SYM∘AND` SAT is decided by the `k+1` AND-layer level-counts.**  `∃x` accepting
`⟺ ∃ t ≤ k, sym t ∧ N_t ≠ 0` — the symmetric layer collapses the search from the `2ⁿ` cube to `k+1` levels. -/
theorem symand_sat_decided_by_levels {n k : ℕ} (sym : ℕ → Bool) (gates : Fin k → Finset (Fin n)) :
    (∃ x, ACC0SymLayerReduction.symAndEval sym gates x = true)
      ↔ ∃ t ∈ Finset.range (k + 1), sym t = true ∧ ACC0SymLayerReduction.levelCount gates t ≠ 0 :=
  symAnd_sat_iff sym gates

/-- **The binomial-moment ↔ level-count bridge (proved): `∑_x C(andCount x, d) = ∑_{t≤k} N_t · C(t,d)`.**  Connects the
`SYM∘AND` level-counts `N_t` to the kernel-computable binomial moments via a unit-triangular system — so the moments
determine the `N_t` by inclusion–exclusion. -/
theorem level_counts_from_binomial_moments {n k : ℕ} (gates : Fin k → Finset (Fin n)) (d : ℕ) :
    (∑ x : Fin n → Bool, (ACC0SymLayerReduction.andCount gates x).choose d)
      = ∑ t ∈ Finset.range (k + 1), ACC0SymLayerReduction.levelCount gates t * t.choose d :=
  binomial_moment_eq_sum_levels gates d

/-- **The `e_d`-sparsity identity (proved): each moment integrand is a sparse `d`-subset sum.**
`C(∑_j b_j, d) = Σ_{|T|=d} ∏_{j∈T} b_j` for `0/1` values — making each binomial moment a kernel-computable sparse sum. -/
theorem moment_integrand_is_sparse {k : ℕ} (b : Fin k → ℕ) (hb : ∀ j, b j ≤ 1) (d : ℕ) :
    (∑ j, b j).choose d = ∑ T ∈ Finset.powersetCard d Finset.univ, ∏ j ∈ T, b j :=
  boolean_esymm b hb d

/-- **Binomial inversion (proved): the level-counts are an alternating sum of the binomial moments.**
`(N_s : ℤ) = Σ_d (-1)^{d-s} C(d,s) · (∑_x C(andCount x, d))` — recovers each `N_t` explicitly from the
kernel-computable moments. -/
theorem level_count_eq_alternating_moments {n k : ℕ} (gates : Fin k → Finset (Fin n)) (s : ℕ)
    (hsk : s ≤ k) :
    (ACC0SymLayerReduction.levelCount gates s : ℤ)
      = ∑ d ∈ Finset.range (k + 1), ((-1 : ℤ)) ^ (d - s) * (d.choose s : ℤ)
          * (∑ x : Fin n → Bool, ((ACC0SymLayerReduction.andCount gates x).choose d : ℤ)) :=
  levelCount_eq_inversion gates s hsk

/-- **The cell-count lower bound, one socket (proved), beside `nframe_lower_bound`.**  For a class of holonomy-predictors,
the *sharpest* cell-count socket implies the holonomy lower bound. -/
theorem cellcount_lower_bound {ι : Type} {n : ℕ} (sys : PredictorClass ι n)
    (tops : ∀ i, (Fin (sys i).1 → ℕ) → Bool) (h : NFrameLowCellCount sys) :
    ACC0HolonomyLowerBound sys tops :=
  nframe_cellcount_lower_bound sys tops h

end PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.ac0_approximation_quantitative
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.exact_symAnd_decoding
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.restricted_exact_by_leaves
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.restricted_exact_by_depth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.restricted_speedup_by_footprint
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.williams_route_reduces_to_two_sockets
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.nframe_bridge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.nframe_unconditional_disjoint
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.nframe_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.rank_bridge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.rank_subsumes_survivor
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.rank_fragment_equal_supports
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.rank_whp
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.rank_append_subadditive
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.rank_collapse_lifts_budget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_bridge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_subsumes_rank
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_chain_fragment
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_clustered_fragment
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_append_submultiplicative
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_route_one_socket
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_socket_is_weakest
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_laminar_fragment
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_block_product
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_markov
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_whp
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_whp_subsumes_rank
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_random_restriction
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_bounded_distinct_expectation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_lowVC_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_lowVC_low_correlation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_direct_tail
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_expected_le_global
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_few_gates_forces
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_sunflower
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_full_of_hardRegime_resolved
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_socket_iff_global_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.cellcount_socket_false_in_hardRegime
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.refined_observer_strictly_beats_membership
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.refined_observer_merge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.refined_observer_collapse_implies_low_correlation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.mod_refined_eq_membership_on_free
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.mod_refined_no_merging_gain
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.mod_parity_constant_iff_fully_fixed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.mod_residual_reduces_to_membership
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.polynomial_method_separates_holonomy_parity
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.williams_cashout_from_polynomial_method
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.boundary_selects_absorbing_iff_andOr
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.sparse_symand_cube_sum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.symand_sat_decided_by_levels
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.level_counts_from_binomial_moments
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.moment_integrand_is_sparse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FrontierSummary.level_count_eq_alternating_moments
