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
 laminar fragment (nested-or-disjoint, ≤k+1)   PROVED   cellcount_laminar_fragment          (…ACC0LaminarCellCount)
 block-product fragment (cells multiply, ∏)    PROVED   cellcount_block_product             (…ACC0BlockProductCellCount)
 cell-count composition (submult. ×, append)   PROVED   cellcount_append_submultiplicative  (…ACC0CellCountComposition)
 cell-count socket is the weakest socket       PROVED   cellcount_socket_is_weakest         (…ACC0CellCountSwitching)
 cell-count Markov tail (Pr[≥a] ≤ Exp/a)       PROVED   cellcount_markov                    (…ACC0RandomRestrictionCellCount)
 cell-count whp (needs a≤b, no 2^a≤b)          PROVED   cellcount_whp                       (…ACC0RandomRestrictionCellCount)
 cell-count whp subsumes rank/survivor whp     PROVED   cellcount_whp_subsumes_rank         (…ACC0RandomRestrictionCellCount)
 first-moment restriction (Exp≤B<a ⇒ ∃L)       PROVED   cellcount_random_restriction        (…ACC0RandomRestrictionCellCount)
 cell-count lower bound (ONE socket)           CONDITIONAL on FullACC0ForcesLowCellCount:
   cellcount_lower_bound : NFrameLowCellCount sys → ACC0HolonomyLowerBound sys tops
 ── open: ACC0ForcesLowCellCount (∃ L, cellPatternCount < |L|) = the SHARPEST (weakest) switching lemma ────
 ── open balance (cell-count language): bound Exp[cellPatternCount] below Exp[2^survivingCount] for wide ──
 ──   overlapping MOD — first moment closes only for deterministic-bound structures (laminar/block/dist.) ─
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

The official open target is now `FullACC0ForcesLowCellCount` (`∃ L, cellPatternCount supports L < |L|`), the *sharpest*
(weakest, most achievable) form of the N-Frame restriction lemma.  Since `cellPatternCount ≤ 2^{cellRank} ≤
2^{survivingCount}`, this socket is implied by the survivor and rank sockets — and it is strictly more general (chain /
nested supports have full rank but `≤ k+1` cells, handled here, missed by the rank route).  Everything else on the
route is proved. -/

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
