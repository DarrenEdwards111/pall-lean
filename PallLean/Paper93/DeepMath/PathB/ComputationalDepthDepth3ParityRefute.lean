import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowExists
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalParity

/-!
# Block-DT model, foundation 62: branching holography, step 4t — switching refutes parity (branch only)

The payoff: the branching switching bound (brick 60) versus the parity decision-tree lower bound
(`canonicalDTree_depth_ge_of_parity` — a DNF computing parity on a `σ`-subcube must read every surviving
variable, so its canonical tree has depth `≥ stars σ`).

If a width-`≤ w` DNF computed parity on *every* `σ`-subcube with `s ≤ stars σ < F`, then every such `σ`
would have a depth-`≥ s` canonical tree (be "bad"); but the switching bound caps the total p-biased weight
of bad restrictions at `(2p/(1-p))^s · (4^w+1)^F`.  So once that cap is below the weight of the high-star
restrictions, the DNF must *fail* parity on some high-star subcube.

* `parity_refuted_by_switching` — if `(2p/(1-p))^s · (4^w+1)^F < ∑_{s ≤ stars σ < F} pweight σ`, then some
  high-star subcube witnesses `dnfValue cs ≠ parity`.

The hypothesis is where a concentration bound (`∑_{s ≤ stars < F} pweight ≈ 1` for `s < pn < F`) would
enter; we state it directly, as it is a separate standard fact.  This is the switching step of
`parity ∉ AC⁰`, with the cruder `4^w` base (vs Håstad's optimal `poly(w)`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Switching refutes parity.**  If the switching bound is below the p-biased weight of the high-star
restrictions, a width-`≤ w` DNF cannot compute parity on all of them: some `σ` with `s ≤ stars σ < F` has
a `σ`-consistent input where `dnfValue cs ≠ parity`. -/
theorem parity_refuted_by_switching {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (F s : ℕ)
    (hbig : (2 * p / (1 - p)) ^ s
          * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)
        < ∑ σ ∈ Finset.univ.filter (fun σ : Fin n → Option Bool => s ≤ stars σ ∧ stars σ < F),
            pweight p σ) :
    ∃ σ : Fin n → Option Bool, s ≤ stars σ ∧ stars σ < F
      ∧ ∃ x, DTree.agreeRestriction σ x ∧ DTree.dnfValue cs x ≠ DTree.parity x := by
  by_contra hcon
  push_neg at hcon
  have hBad : ∀ σ ∈ Finset.univ.filter (fun σ : Fin n → Option Bool => s ≤ stars σ ∧ stars σ < F),
      s ≤ (canonicalDTree cs w F σ).depth := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    obtain ⟨_, hs, hF⟩ := hσ
    have hpar : ∀ x, DTree.agreeRestriction σ x → DTree.dnfValue cs x = DTree.parity x :=
      fun x hx => hcon σ hs hF x hx
    exact le_trans hs (canonicalDTree_depth_ge_of_parity cs w F σ hF hpar)
  have h := descent_switching_le hp0 hp3 cs hcons hnd w hw F s hBad
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_refuted_by_switching
