import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BottomGates
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeSize

/-!
# Tight switching, step 55: the leaf-switch produces a size-bounded bottom gate (branch `razborov-recoverRho-wip`)

The switch half of the width-aware reduction.  `leafCollapse F ρ` turns each bottom gate into the switched
gate of a canonical decision tree (`dnf cs ↦ cnf (dtreeToCNF (toDTree (canonicalDT cs F ρ)))`, and dually for
`cnf`).  Composing `toDTree_depth` / `negTree_depth` (depth-preserving conversions) with the width bounds
(foundations 1/2) and the clause-count bounds (step 53), the switched bottom gate has width and clause-count
controlled by the tree depth `(canonicalDT … F ρ).depth` — *exactly the quantity a survivor `ρ` drives below
`s`*.  So after a survivor round every new bottom gate is `BottomBounded` at `(s, 2^s)`.

* `leafCollapse_dnf_BottomBounded` / `leafCollapse_cnf_BottomBounded` — the per-gate switched-size bound at
  the canonical-tree depth.
* `BottomBounded_mono` — monotonicity in the width/count budgets (so `depth < s` upgrades to the `(s, 2^s)`
  budget).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- `BottomBounded` is monotone in both budgets: widening `w` or `M` weakens the predicate. -/
theorem BottomBounded_mono {w w' M M' : ℕ} (hw : w ≤ w') (hM : M ≤ M') {C : Layered n}
    (h : BottomBounded w M C) : BottomBounded w' M' C := by
  intro cs hcs
  obtain ⟨hcw, hcm⟩ := h cs hcs
  exact ⟨fun T hT => le_trans (hcw T hT) hw, le_trans hcm hM⟩

/-- **The switched `DNF` bottom gate is size-bounded by the canonical-tree depth.**  `leafCollapse F ρ (dnf cs)`
is a `CNF` of width `≤ d` and clause-count `≤ 2^d`, where `d = (canonicalDT cs F ρ).depth`. -/
theorem leafCollapse_dnf_BottomBounded (F : ℕ) (ρ : Fin n → Option Bool) (cs : List (Clause n)) :
    BottomBounded ((canonicalDT cs F ρ).depth) (2 ^ (canonicalDT cs F ρ).depth)
      (leafCollapse F ρ (dnf cs)) := by
  intro cs' hcs'
  rw [show leafCollapse F ρ (dnf cs) = cnf (dtreeToCNF (toDTree (canonicalDT cs F ρ))) from rfl,
    bottomGates, List.mem_singleton] at hcs'
  subst hcs'
  refine ⟨fun T hT => ?_, ?_⟩
  · have h := dtreeToCNF_width (toDTree (canonicalDT cs F ρ)) T hT
    rwa [toDTree_depth] at h
  · have h := dtreeToCNF_length (toDTree (canonicalDT cs F ρ))
    rwa [toDTree_depth] at h

/-- **The switched `CNF` bottom gate is size-bounded by the canonical-tree depth (dual).**  `leafCollapse F ρ
(cnf cs)` is a `DNF` of width `≤ d` and clause-count `≤ 2^d`, where `d = (canonicalDT (negDNF cs) F ρ).depth`. -/
theorem leafCollapse_cnf_BottomBounded (F : ℕ) (ρ : Fin n → Option Bool) (cs : List (Clause n)) :
    BottomBounded ((canonicalDT (negDNF cs) F ρ).depth) (2 ^ (canonicalDT (negDNF cs) F ρ).depth)
      (leafCollapse F ρ (cnf cs)) := by
  intro cs' hcs'
  rw [show leafCollapse F ρ (cnf cs)
        = dnf (dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF cs) F ρ)))) from rfl,
    bottomGates, List.mem_singleton] at hcs'
  subst hcs'
  refine ⟨fun T hT => ?_, ?_⟩
  · have h := dtreeToDNF_width (DTree.negTree (toDTree (canonicalDT (negDNF cs) F ρ))) T hT
    rwa [DTree.negTree_depth, toDTree_depth] at h
  · have h := dtreeToDNF_length (DTree.negTree (toDTree (canonicalDT (negDNF cs) F ρ)))
    rwa [DTree.negTree_depth, toDTree_depth] at h

/-- **Survivor upgrade (`DNF`).**  If `ρ` shallows `cs` below `s`, the switched bottom gate is `BottomBounded`
at the uniform budget `(s, 2^s)`. -/
theorem leafCollapse_dnf_BottomBounded_survivor (F : ℕ) (ρ : Fin n → Option Bool)
    (cs : List (Clause n)) {s : ℕ} (hsh : (canonicalDT cs F ρ).depth < s) :
    BottomBounded s (2 ^ s) (leafCollapse F ρ (dnf cs)) :=
  BottomBounded_mono (le_of_lt hsh) (Nat.pow_le_pow_right (by norm_num) (le_of_lt hsh))
    (leafCollapse_dnf_BottomBounded F ρ cs)

/-- **Survivor upgrade (`CNF`, dual).** -/
theorem leafCollapse_cnf_BottomBounded_survivor (F : ℕ) (ρ : Fin n → Option Bool)
    (cs : List (Clause n)) {s : ℕ} (hsh : (canonicalDT (negDNF cs) F ρ).depth < s) :
    BottomBounded s (2 ^ s) (leafCollapse F ρ (cnf cs)) :=
  BottomBounded_mono (le_of_lt hsh) (Nat.pow_le_pow_right (by norm_num) (le_of_lt hsh))
    (leafCollapse_cnf_BottomBounded F ρ cs)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.leafCollapse_dnf_BottomBounded
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.leafCollapse_cnf_BottomBounded_survivor
