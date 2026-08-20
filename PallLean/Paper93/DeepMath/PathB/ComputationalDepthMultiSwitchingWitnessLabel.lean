import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingCommonTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingDnfCount

/-!
# Finite labels for common multi-switching witnesses

A common bad path pays once for its shared branch transcript.  The remaining bookkeeping records,
for each gate, its number of contiguous active runs and, for each of its terms, its multiplicity on
the common path.  All counts lie between zero and the shared depth.  This file gives the exact finite
label space and connects it to the generic injective counting theorem; constructing the canonical
bad-path packing is the next combinatorial obligation.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- A fresh shared query together with the first raw canonical gate segment that contains it.
`none` is retained in the total definition until origin existence is proved. -/
abbrev FreshQueryAnnotation (n G : ℕ) := Fin n × Option (Fin G)

/-- First gate, in the canonical padded order, whose raw execution path queries `v`. -/
def firstGateOrigin? {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) (v : Fin n) : Option (Fin G) :=
  (List.finRange G).find? fun g => v ∈
    CommonTree.queryVars (CommonTree.ofBool (trees g)) x

/-- Annotate every genuinely fresh read-once query with its first raw gate of origin. -/
def annotatedFreshQueries {n G : ℕ} (σ : Restriction n)
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool) :
    List (FreshQueryAnnotation n G) :=
  (CommonTree.queryVars
    (CommonTree.readOnce σ (CommonTree.commonRefineFin trees)) x).map
      fun v => (v, firstGateOrigin? trees x v)

/-- Origin annotation does not alter, reorder, duplicate, or discard the fresh query path. -/
theorem annotatedFreshQueries_map_fst {n G : ℕ} (σ : Restriction n)
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool) :
    (annotatedFreshQueries σ trees x).map Prod.fst =
      CommonTree.queryVars
        (CommonTree.readOnce σ (CommonTree.commonRefineFin trees)) x := by
  simp [annotatedFreshQueries, List.map_map, Function.comp_def]

/-- The annotated fresh-variable stream remains duplicate-free. -/
theorem annotatedFreshQueries_vars_nodup {n G : ℕ} (σ : Restriction n)
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    ((annotatedFreshQueries σ trees x).map Prod.fst).Nodup := by
  rw [annotatedFreshQueries_map_fst]
  exact CommonTree.queryVars_readOnce_nodup σ _ x hext

/-- Every retained fresh query has a genuine raw gate segment of origin. -/
theorem firstGateOrigin_isSome_of_mem_readOnce {n G : ℕ} (σ : Restriction n)
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) {v : Fin n}
    (hv : v ∈ CommonTree.queryVars
      (CommonTree.readOnce σ (CommonTree.commonRefineFin trees)) x) :
    (firstGateOrigin? trees x v).isSome = true := by
  have hraw := CommonTree.mem_queryVars_of_mem_readOnce σ
    (CommonTree.commonRefineFin trees) x hext hv
  rw [CommonTree.queryVars_commonRefineFin] at hraw
  obtain ⟨segment, hsegment, hvsegment⟩ := List.mem_flatten.mp hraw
  obtain ⟨tree, htree, rfl⟩ := List.mem_map.mp hsegment
  obtain ⟨g, hg⟩ := List.mem_ofFn.mp htree
  subst tree
  apply List.find?_isSome.mpr
  refine ⟨g, List.mem_finRange g, ?_⟩
  simpa using hvsegment

/-- Shared boundary bookkeeping: one run count per gate and one term multiplicity per gate/term. -/
abbrev CommonBoundaryLabel (d G m : ℕ) :=
  (Fin G → Fin (d + 1)) × (Fin G → Fin m → Fin (d + 1))

/-- The full finite common witness label: one shared transcript plus polynomial boundary data. -/
abbrev CommonBadPathLabel (d G m : ℕ) :=
  CommonTree.FinitePathLabel d × CommonBoundaryLabel d G m

/-- Exact cardinality of the shared gate/term boundary bookkeeping. -/
theorem card_commonBoundaryLabel (d G m : ℕ) :
    Fintype.card (CommonBoundaryLabel d G m) =
      (d + 1) ^ G * ((d + 1) ^ m) ^ G := by
  simp [CommonBoundaryLabel, Fintype.card_prod]

/-- Exact common-witness label count.  The exponential transcript factor occurs once; all
gate/term identity information is in the displayed fixed-parameter polynomial factors. -/
theorem card_commonBadPathLabel (d G m : ℕ) :
    Fintype.card (CommonBadPathLabel d G m) =
      ((d + 1) * 2 ^ d) * ((d + 1) ^ G * ((d + 1) ^ m) ^ G) := by
  rw [Fintype.card_prod, CommonTree.card_finitePathLabel, card_commonBoundaryLabel]

/-- Assemble the shared transcript and boundary tables without duplicating path bits per gate. -/
def commonBadPathPack {d G m : ℕ}
    (path : CommonTree.PathLabel d)
    (gateRuns : Fin G → Fin (d + 1))
    (termCounts : Fin G → Fin m → Fin (d + 1)) : CommonBadPathLabel d G m :=
  (path.toFinite, (gateRuns, termCounts))

/-- The common packing is injective once its three mathematical components agree. -/
theorem commonBadPathPack_eq_iff {d G m : ℕ}
    {p q : CommonTree.PathLabel d}
    {gr₁ gr₂ : Fin G → Fin (d + 1)}
    {tc₁ tc₂ : Fin G → Fin m → Fin (d + 1)} :
    commonBadPathPack p gr₁ tc₁ = commonBadPathPack q gr₂ tc₂ ↔
      p = q ∧ gr₁ = gr₂ ∧ tc₁ = tc₂ := by
  constructor
  · intro h
    exact ⟨CommonTree.PathLabel.toFinite_injective (congrArg Prod.fst h),
      congrArg (fun z => z.2.1) h, congrArg (fun z => z.2.2) h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Every real gate segment fits inside the total common-path depth. -/
theorem gateTrace_length_le_commonDepth {n G : ℕ}
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool) (g : Fin G) :
    (CommonTree.trace (CommonTree.ofBool (trees g)) x).length ≤
      CommonTree.depth (CommonTree.commonRefineFin trees) := by
  calc
    (CommonTree.trace (CommonTree.ofBool (trees g)) x).length
        ≤ ((List.ofFn trees).map fun t =>
            (CommonTree.trace (CommonTree.ofBool t) x).length).sum := by
          apply List.le_sum_of_mem
          simp
    _ = (CommonTree.trace (CommonTree.commonRefineFin trees) x).length :=
      (CommonTree.trace_commonRefineFin_length trees x).symm
    _ ≤ CommonTree.depth (CommonTree.commonRefineFin trees) :=
      CommonTree.trace_length_le_depth _ _

/-- The actual ordered common-refinement execution supplies the gate-run component of the label:
the `g`th entry is precisely the length of the `g`th canonical tree segment. -/
def commonGateRunCounts {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) :
    Fin G → Fin (CommonTree.depth (CommonTree.commonRefineFin trees) + 1) :=
  fun g => ⟨(CommonTree.trace (CommonTree.ofBool (trees g)) x).length,
    Nat.lt_succ_of_le (gateTrace_length_le_commonDepth trees x g)⟩

@[simp] theorem commonGateRunCounts_val {n G : ℕ}
    (trees : Fin G → BoolDecisionTree n) (x : Fin n → Bool) (g : Fin G) :
    (commonGateRunCounts trees x g).1 =
      (CommonTree.trace (CommonTree.ofBool (trees g)) x).length := rfl

variable {n : ℕ}

/-- The finite-label count consumed by a genuine common bad-path encoder.  The sole remaining
semantic premise is injectivity of `(endpoint, shared witness label)` on the chosen bad set. -/
theorem commonBadPath_count {d G m : ℕ}
    (endpoint : Restriction n → Restriction n)
    (label : Restriction n → CommonBadPathLabel d G m)
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, endpoint ρ ∈ Short)
    (hrec : ∀ ρ ∈ Bad, ∀ σ ∈ Bad,
      endpoint ρ = endpoint σ → label ρ = label σ → ρ = σ) :
    Bad.card ≤ Short.card *
      (((d + 1) * 2 ^ d) * ((d + 1) ^ G * ((d + 1) ^ m) ^ G)) := by
  apply card_bad_le_label_card endpoint label
  · exact le_of_eq (card_commonBadPathLabel d G m)
  · exact hmem
  · exact hrec

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.card_commonBadPathLabel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.annotatedFreshQueries_map_fst
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.annotatedFreshQueries_vars_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.firstGateOrigin_isSome_of_mem_readOnce
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonBadPathPack_eq_iff
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.gateTrace_length_le_commonDepth
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonGateRunCounts_val
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonBadPath_count
