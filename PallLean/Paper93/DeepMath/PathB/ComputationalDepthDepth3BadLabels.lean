import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3EncodeInjective

/-!
# Block-DT model, foundation 44: branching holography, step 4b — bad restrictions have long, narrow labels (branch only)

The quantitative packaging that feeds the counting/measure layer.  Combining the deepest input (brick 39)
with the label bridges (brick 42): every restriction whose canonical tree is deep (`depth ≥ s`) has a
descent whose labels carry `≥ s` variable-slots, partitioned into blocks of width `≤ w`.

* `exists_bad_labels` — for distinct-variable, width-`≤ w` clauses, if `s ≤ depth` then there is a descent
  input `x` with `s ≤ (descentLabels …).flatten.length` and every label of length `≤ w`.

With `descent_encode_injective` (brick 43) this is the complete structural content of the switching count:
the bad restrictions inject into `(label-list, final-restriction)` pairs whose label-lists are long
(`≥ s` slots) and narrow (blocks `≤ w`).  Bounding the cardinality of *that* codomain — the `(c·w)^s`
arithmetic over the p-biased measure — is the remaining analytic sub-project.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Bad restrictions have long, narrow labels.**  If the canonical tree has depth `≥ s`, some descent
realises a label list carrying `≥ s` variable-slots in blocks of width `≤ w`. -/
theorem exists_bad_labels (cs : List (Clause n)) (w : ℕ)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (F : ℕ) (σ : Fin n → Option Bool) (s : ℕ) (hs : s ≤ (canonicalDTree cs w F σ).depth) :
    ∃ x, s ≤ (descentLabels cs w F σ x).flatten.length
      ∧ ∀ L ∈ descentLabels cs w F σ x, L.length ≤ w := by
  obtain ⟨x, hx⟩ := exists_deep_input cs w hnd F σ
  refine ⟨x, ?_, descentLabels_label_le_w cs w hw F σ x⟩
  rw [descentLabels_flatten_length]
  exact le_trans hs hx

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_bad_labels
