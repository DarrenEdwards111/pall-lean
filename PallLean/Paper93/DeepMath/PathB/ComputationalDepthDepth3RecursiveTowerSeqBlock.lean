import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TowerParity

/-!
# Block-DT model, route-2 step [166]: the BLOCK-level recursive-tower engine (option (b) B1)

The general-`d` engine `recursive_tower_not_parity_surv_seq` bakes its terminal switching into the
**bit-level** tree `canonicalDT` (via `tower_not_parity_tight`).  Here we give the **block-level**
twin: identical sequence construction (the tree-agnostic `recursive_tower_chain_surv_seq` is reused
verbatim), but the terminal hypothesis and the parity capstone are over `canonicalDTree`
(`tower_not_parity`), so the m-free route-2 terminal [165] can discharge it.

`TightParity` guarantees this is sound with no depth bridge: the relativized parity bound is generic
over decision trees, so `(canonicalDTree D w F σ').depth < stars σ'` forces `D ≠ parity` on the
subcube exactly as the bit-level version does.

* `recursive_tower_not_parity_surv_seq_block` — the block-tree analog of
  `recursive_tower_not_parity_surv_seq`; same oracle, terminal over `canonicalDTree`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The block-level recursive-tower parity engine.**  Identical to
`recursive_tower_not_parity_surv_seq`, but the terminal `hterm` produces a shallow **block** tree
`(canonicalDTree D w F σ').depth < stars σ'` and the parity contradiction is closed by the block
capstone `tower_not_parity`.  The hard sequence construction `recursive_tower_chain_surv_seq` is
reused unchanged (it is tree-agnostic). -/
theorem recursive_tower_not_parity_surv_seq_block (Valid : ℕ → Layered n → Prop) (s : ℕ → ℕ)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : Valid 0 C₀)
    (hτ₀ : s 0 ≤ SwitchingCounting.stars τ₀)
    (oracle : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), Valid i C →
      s i ≤ SwitchingCounting.stars τ →
      ∃ (C' : Layered n) (ρ : Fin n → Option Bool),
        Extends τ ρ ∧ s (i + 1) ≤ SwitchingCounting.stars ρ ∧ EquivOn ρ C C' ∧ Valid (i + 1) C')
    (d w F : ℕ)
    (hterm : ∀ (Cd : Layered n) (σ : Fin n → Option Bool), Valid d Cd → Extends τ₀ σ →
      s d ≤ SwitchingCounting.stars σ →
      ∃ (σ' : Fin n → Option Bool) (D : List (Clause n)),
        Extends σ σ' ∧ Cd = dnf D ∧ SwitchingCounting.stars σ' < F ∧
        (canonicalDTree D w F σ').depth < SwitchingCounting.stars σ') :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  obtain ⟨Cd, σ, hVd, hextd, hsurv, hredd⟩ :=
    recursive_tower_chain_surv_seq Valid s C₀ τ₀ hC₀ hτ₀ oracle d
  obtain ⟨σ', D, hextσ', hCdD, hltF, hsh⟩ := hterm Cd σ hVd hextd hsurv
  have hred : ∀ x, DTree.agreeRestriction σ' x → Reduces x C₀ (dnf D) :=
    fun x hx => hCdD ▸ hredd x (agreeRestriction_of_extends hextσ' hx)
  have hnp := tower_not_parity C₀ D w F σ' hltF hsh hred
  push_neg at hnp
  obtain ⟨x, _, hx⟩ := hnp
  exact ⟨x, hx⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recursive_tower_not_parity_surv_seq_block
