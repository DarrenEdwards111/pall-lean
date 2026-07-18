import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNonSizeDominated

/-!
# The polynomial ceiling: additive multi-row measures are capped at time

The single-configuration cap (`NonSizeDominated`) showed a non-size-dominated measure gets no
per-configuration freedom.  This file pushes to the multi-row question and answers it for the
whole *additive* class: any measure bounded by a **polynomial** in `traceSize` — which includes
every row-subadditive measure — has exactly `traceSize`'s (= time's) separating power.

* `PolySizeDominated μ` — `μ tr ≤ c·(traceSize tr + 1)^k` for some `c, k`.  Strictly extends
  `SizeDominated` (the `c = k = 1` linear case).
* `traceInv_le_poly_traceSize` — the bound lifts through the per-length `Finset.sup`:
  `traceInv μ M n ≤ c·(traceInv traceSize M n + 1)^k`.
* `polySizeDominated_hard_imp_traceSize_hard`, `polySizeDominated_ceiling`,
  `polySizeDominated_hard_iff_sep` — the ceiling for the whole polynomial class: a hard
  polynomially-size-dominated measure exists iff `traceSize` is hard iff `¬ PolyCollapse`.

**The multi-row payoff** (`rowSubadditive_hard_imp_traceSize_hard`).  A measure is *row-
subadditive* if `μ tr ≤ Σ_{row ∈ tr} μ [row]`.  A generically-sound row-subadditive measure is
polynomially size-dominated — its per-configuration values are polynomially capped
(`NonSizeDominated`), and summing `≤ #rows` of them over a trace stays polynomial in
`traceSize`.  So **every additive multi-row measure is capped at time**.  Content beyond time
therefore requires a genuinely *super-additive* measure: the superpolynomial value on SAT
traces must come from **cross-row correlation**, not from any sum of per-configuration
contributions.  That is the sharpest structural constraint the schema yields.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PolyCeiling

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo
open PallLean.Paper93.DeepMath.PathB.NonSizeDominated
open PallLean.Paper93.DeepMath.PathB.TraceSchemaComplete (traceSize_hard_iff_sep)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- A measure bounded by a polynomial in the trace size. -/
def PolySizeDominated (μ : List (List Bool) → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ tr, μ tr ≤ c * (traceSize tr + 1) ^ k

/-- Linear size-domination is the `c = k = 1` case. -/
theorem polySizeDominated_of_sizeDominated (μ : List (List Bool) → ℕ) (hμ : SizeDominated μ) :
    PolySizeDominated μ :=
  ⟨1, 1, fun tr => by have := hμ tr; simp only [pow_one, one_mul]; omega⟩

/-- **The polynomial ceiling, pointwise.**  A polynomial bound in `traceSize` lifts through the
per-length worst case. -/
theorem traceInv_le_poly_traceSize (μ : List (List Bool) → ℕ) (c k : ℕ)
    (hμ : ∀ tr, μ tr ≤ c * (traceSize tr + 1) ^ k) (M : Machine) (n : ℕ) :
    traceInv μ M n ≤ c * (traceInv traceSize M n + 1) ^ k := by
  unfold traceInv
  apply Finset.sup_le
  intro v _
  refine le_trans (hμ _) (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right ?_ 1) k))
  exact Finset.le_sup (f := fun v => traceSize (traceObj M (minHalt M n) (List.ofFn v)))
    (Finset.mem_univ v)

/-- `c·(g + 1)^k` is polynomially bounded when `g` is. -/
theorem polyBounded_polyComp {g : ℕ → ℕ} (c k : ℕ) (hg : PolyBounded g) :
    PolyBounded (fun n => c * (g n + 1) ^ k) :=
  polyBounded_of_le
    (fun n => Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) k))
    (polyBounded_time_comp c k hg)

/-- **`traceSize` is the top of the polynomial class.**  A polynomially-size-dominated
measure's hardness implies `traceSize`'s. -/
theorem polySizeDominated_hard_imp_traceSize_hard (SATV : NPObs) (μ : List (List Bool) → ℕ)
    (hμ : PolySizeDominated μ) (hH : InvHard SATV (traceInv μ)) :
    InvHard SATV (traceInv traceSize) := by
  obtain ⟨c, k, hb⟩ := hμ
  intro M T hD hPB
  exact hH M T hD
    (polyBounded_of_le (traceInv_le_poly_traceSize μ c k hb M) (polyBounded_polyComp c k hPB))

/-- **THE POLYNOMIAL CEILING.**  A hard polynomially-size-dominated measure exists iff
`traceSize` is hard. -/
theorem polySizeDominated_ceiling (SATV : NPObs) :
    (∃ μ, PolySizeDominated μ ∧ InvHard SATV (traceInv μ))
      ↔ InvHard SATV (traceInv traceSize) := by
  constructor
  · rintro ⟨μ, hμ, hH⟩
    exact polySizeDominated_hard_imp_traceSize_hard SATV μ hμ hH
  · intro hH
    exact ⟨traceSize, ⟨1, 1, fun tr => by simp⟩, hH⟩

/-- The polynomial ceiling in separation terms: the class separates exactly to the extent
time does. -/
theorem polySizeDominated_hard_iff_sep (SATV : NPObs) :
    (∃ μ, PolySizeDominated μ ∧ InvHard SATV (traceInv μ)) ↔ ¬ PolyCollapse SATV :=
  (polySizeDominated_ceiling SATV).trans (traceSize_hard_iff_sep SATV)

/-! ## The multi-row payoff: additive measures are capped -/

/-- Row-subadditivity: the measure of a trace is at most the sum of its rows' singleton
measures. -/
def RowSubadditive (μ : List (List Bool) → ℕ) : Prop :=
  ∀ tr, μ tr ≤ (tr.map fun row => μ [row]).sum

/-- Generic soundness gives a per-configuration polynomial bound. -/
theorem perConfig_poly_of_genSound (μ : List (List Bool) → ℕ)
    (hG : InvGenSound (traceInv μ)) :
    ∃ c k, ∀ w : List Bool, μ [w] ≤ c * (w.length + 1) ^ k := by
  obtain ⟨c, k, hb⟩ := genSound_singleRow_poly μ hG
  refine ⟨c, k, fun w => ?_⟩
  have hv : List.ofFn (fun i : Fin w.length => w.getD (↑i) false) = w := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
        Option.getD_some]
  have hle : μ [w] ≤ singleRowProfile μ w.length := by
    unfold singleRowProfile
    calc μ [w] = μ [List.ofFn fun i : Fin w.length => w.getD (↑i) false] := by rw [hv]
      _ ≤ _ := Finset.le_sup
          (f := fun v : Fin w.length → Bool => μ [List.ofFn v])
          (Finset.mem_univ (fun i : Fin w.length => w.getD (↑i) false))
  exact le_trans hle (hb w.length)

/-- Each row's length is at most the whole trace size. -/
theorem row_length_le_traceSize {tr : List (List Bool)} {row : List Bool} (h : row ∈ tr) :
    row.length ≤ traceSize tr := by
  unfold traceSize
  have hmem : row.length ∈ tr.map List.length := List.mem_map.mpr ⟨row, h, rfl⟩
  have hle := List.single_le_sum (fun (x : ℕ) _ => Nat.zero_le x) _ hmem
  omega

/-- **A generically-sound row-subadditive measure is polynomially size-dominated.**  Its per-
configuration values are polynomially capped, and a trace sums at most `#rows ≤ traceSize` of
them. -/
theorem rowSubadditive_polySizeDominated (μ : List (List Bool) → ℕ)
    (hsub : RowSubadditive μ) (hG : InvGenSound (traceInv μ)) :
    PolySizeDominated μ := by
  obtain ⟨c, k, hpc⟩ := perConfig_poly_of_genSound μ hG
  refine ⟨c, k + 1, fun tr => ?_⟩
  have hrow : ∀ y ∈ tr.map fun row => μ [row], y ≤ c * (traceSize tr + 1) ^ k := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨row, hrow_mem, rfl⟩ := hy
    refine le_trans (hpc row) (Nat.mul_le_mul_left c (Nat.pow_le_pow_left ?_ k))
    have := row_length_le_traceSize hrow_mem
    omega
  calc μ tr ≤ (tr.map fun row => μ [row]).sum := hsub tr
    _ ≤ (tr.map fun row => μ [row]).length • (c * (traceSize tr + 1) ^ k) :=
        List.sum_le_card_nsmul _ _ hrow
    _ = tr.length * (c * (traceSize tr + 1) ^ k) := by rw [List.length_map]; rw [smul_eq_mul]
    _ ≤ (traceSize tr + 1) * (c * (traceSize tr + 1) ^ k) := by
        refine Nat.mul_le_mul_right _ ?_
        have : tr.length ≤ traceSize tr := by unfold traceSize; omega
        omega
    _ = c * (traceSize tr + 1) ^ (k + 1) := by ring

/-- **The multi-row cap.**  Every generically-sound row-subadditive (additive) measure is capped
at time: its hardness implies `traceSize`'s.  Content beyond time needs a *super-additive*
measure — cross-row correlation, not a sum of per-configuration contributions. -/
theorem rowSubadditive_hard_imp_traceSize_hard (SATV : NPObs) (μ : List (List Bool) → ℕ)
    (hsub : RowSubadditive μ) (hG : InvGenSound (traceInv μ))
    (hH : InvHard SATV (traceInv μ)) : InvHard SATV (traceInv traceSize) :=
  polySizeDominated_hard_imp_traceSize_hard SATV μ (rowSubadditive_polySizeDominated μ hsub hG) hH

end PallLean.Paper93.DeepMath.PathB.PolyCeiling
