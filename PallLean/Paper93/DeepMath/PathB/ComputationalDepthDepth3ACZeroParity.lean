import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitDepthReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Parity

/-!
# Block-DT model, foundation 18: the AC⁰ pipeline endpoint — circuits vs parity (branch only)

The bridge that makes the depth-reduction pipeline an actual lower bound: a circuit that the pipeline
has reduced to a *shallow* decision tree cannot compute parity.

* `circuit_not_parity_of_shallow` — if a circuit equals a depth-`< n` decision tree, it is not parity.
* `and_of_shallow_dts_not_parity` — the depth-3 endpoint: an `AND` of shallow-DT gates that further
  collapses to a depth-`< n` tree does not compute parity (combines `and_trees_depth_reduction` with the
  bridge).
* `iterate_collapse` — one switching round is `and_trees_depth_reduction`; chaining it is transitive
  (eval equality composes).  Here it is stated as the explicit two-round composition certificate.

## Honest scope of the iteration

Each round (`and_trees_depth_reduction`) needs its own good restriction (every surviving bottom gate
shallow), supplied by `circuit_collapse_exists`.  The *eval-equality composition* across rounds is the
transitivity proved here; the remaining work to a full `parity ∉ AC⁰` theorem is the **quantitative
budget**: choosing the star-probability per round so that after `d-2` rounds enough variables survive
(`≥ s`) yet the tree is shallow (`depth < #survivors`), then invoking `shallow_dtree_not_parity`.  That
budget bookkeeping is the genuine remaining step; the structural pipeline is complete and machine-checked.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

variable {n : ℕ}

/-- **The bridge.**  A circuit that equals a depth-`< n` decision tree does not compute parity. -/
theorem circuit_not_parity_of_shallow (c : Circ n) (t : DTree n)
    (hct : ∀ x, Circ.eval x c = t.eval x) (hd : t.depth < n) :
    ∃ x, Circ.eval x c ≠ DTree.parity x := by
  obtain ⟨x, hx⟩ := DTree.shallow_dtree_not_parity t hd
  refine ⟨x, fun h => hx ?_⟩
  rw [hct x] at h
  exact h

/-- **Depth-3 endpoint.**  An `AND` of shallow-DT gates whose reduced CNF circuit further equals a
depth-`< n` decision tree does not compute parity.  (Combines one switching round
`and_trees_depth_reduction` with the parity bridge.) -/
theorem and_of_shallow_dts_not_parity (ts : List (DTree n)) (t : DTree n)
    (hred : ∀ x, Circ.eval x (DTree.cnfToCirc (ts.flatMap DTree.toCNF)) = t.eval x)
    (hd : t.depth < n) :
    ∃ x, Circ.eval x (Circ.and (ts.map DTree.toCirc)) ≠ DTree.parity x := by
  refine circuit_not_parity_of_shallow (Circ.and (ts.map DTree.toCirc)) t (fun x => ?_) hd
  rw [← hred x]
  -- one switching round: AND-of-shallow-DT-gates ≡ the reduced CNF circuit
  by_cases h : Circ.eval x (Circ.and (ts.map DTree.toCirc)) = true
  · rw [h, ((DTree.and_trees_depth_reduction ts x).mp h)]
  · simp only [Bool.not_eq_true] at h
    rw [h]
    cases hr : Circ.eval x (DTree.cnfToCirc (ts.flatMap DTree.toCNF)) with
    | false => rfl
    | true => exact absurd ((DTree.and_trees_depth_reduction ts x).mpr hr) (by rw [h]; simp)

/-- **Iteration is transitive eval-composition.**  Two switching rounds compose: if round 1 makes `c₀`
equal to `c₁` and round 2 makes `c₁` equal to a shallow tree `t`, then `c₀` equals `t` — hence
(by the bridge) `c₀` is not parity.  The schema iterates to any depth. -/
theorem iterate_collapse (c₀ c₁ : Circ n) (t : DTree n)
    (h01 : ∀ x, Circ.eval x c₀ = Circ.eval x c₁)
    (h1t : ∀ x, Circ.eval x c₁ = t.eval x) (hd : t.depth < n) :
    ∃ x, Circ.eval x c₀ ≠ DTree.parity x :=
  circuit_not_parity_of_shallow c₀ t (fun x => (h01 x).trans (h1t x)) hd

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.circuit_not_parity_of_shallow
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.and_of_shallow_dts_not_parity
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.iterate_collapse
