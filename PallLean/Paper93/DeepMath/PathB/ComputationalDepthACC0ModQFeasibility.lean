import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityConstraintRealization

/-!
# General `MOD_q` realization: realizable ⟺ a 0/1-feasibility system is solvable

For parity (MOD₂) the realization condition was *linear consistency* (`parity_realizable_iff_consistent`) and the
reachable image was an F₂-subspace of size `2^rank`.  For general `MOD_q` (`q ≥ 3`) the story is genuinely harder:
forcing a `MOD_q` gate is a **count-residue (dis)equality** `∑_{i∈Sⱼ} xᵢ = tⱼ (mod q)` (forced true) or `≠ tⱼ` (forced
false), and the variables are Boolean `{0,1}` — so realizability is a **0/1-integer-feasibility** problem, *not* free
linear algebra over `ZMod q`.

`modq_realizable_iff_feasible` characterizes realizability as solvability of that equality/disequality count system —
the general-`q` analogue of the parity consistency theorem.  And `modq_residue_image_not_subspace` *proves the
obstruction*: already for a single `MOD₃` gate the reachable residue set `{0,1} ⊆ ZMod 3` is **not** closed under
addition (`1+1 = 2` is unreachable), so the `2^rank` subspace structure is genuinely MOD₂-specific.

The `x`-level speedup itself is `q`-independent: a control reads the `k` Boolean gate outputs, so the reachable image
has `≤ 2^k` cells (`oracle_control_over_mod_searchable`, already general for arbitrary moduli).  What `MOD_q` changes is
*which* of the `2^k` patterns are reachable — the 0/1-feasibility region characterized here.

## What is proved (clean axioms, no `sorry`)

* `modGate_eval_true_iff` / `modGate_eval_false_iff` — forcing a `MOD_q` gate is a count `=`/`≠` target constraint.
* `modq_realizable_iff_feasible` — realizable ⟺ the equality/disequality 0/1-count system has a Boolean solution.
* `modQStatOn_singleton`, `modq_residue_image_not_subspace` — the MOD₃ obstruction: the reachable residue set is not
  closed under `+`, so there is no `2^rank` structure for `q > 2`.

## Honest scope

This characterizes general-`MOD_q` realizability as 0/1-feasibility and proves the linear-rank refinement is
MOD₂-only.  It does **not** give a closed-form cardinality for the reachable region (`q ≥ 3`); that is a genuine
integer-feasibility / lattice question with no subspace shortcut — the honest barrier beyond parity.  Still the
cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModQFeasibility

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0OracleRestrictionRealization
open PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization

variable {n k : ℕ}

/-- **Forcing a `MOD_q` gate true is the count-residue equation (proved).** -/
theorem modGate_eval_true_iff (G : ModGate n) (x : Fin n → Bool) :
    G.eval x = true ↔ modQStatOn G.support G.modulus x = G.target := by
  simp only [ModGate.eval, decide_eq_true_eq]

/-- **Forcing a `MOD_q` gate false is the count-residue disequation (proved).** -/
theorem modGate_eval_false_iff (G : ModGate n) (x : Fin n → Bool) :
    G.eval x = false ↔ modQStatOn G.support G.modulus x ≠ G.target := by
  simp only [ModGate.eval, decide_eq_false_iff_not, ne_eq]

/-- **General `MOD_q` realizability ⟺ a 0/1-feasibility system (proved).**  A forced family of `MOD_q` gates is
realizable iff there is a Boolean assignment meeting every gate's count constraint: `= tⱼ` where the gate is forced
true, `≠ tⱼ` where forced false. -/
theorem modq_realizable_iff_feasible (ρ : Fin k → Option Bool) (gate : Fin k → ModGate n) :
    RealizableByInputRestriction ρ gate ↔
      ∃ x : Fin n → Bool, ∀ j,
        (ρ j = some true →
          modQStatOn (gate j).support (gate j).modulus x = (gate j).target) ∧
        (ρ j = some false →
          modQStatOn (gate j).support (gate j).modulus x ≠ (gate j).target) := by
  rw [realizable_iff_achievable]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun j => ⟨fun h => (modGate_eval_true_iff (gate j) x).mp (hx j true h),
                        fun h => (modGate_eval_false_iff (gate j) x).mp (hx j false h)⟩⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, fun j b hjb => ?_⟩
    cases b with
    | true => exact (modGate_eval_true_iff (gate j) x).mpr ((hx j).1 hjb)
    | false => exact (modGate_eval_false_iff (gate j) x).mpr ((hx j).2 hjb)

/-! ## The MOD₃ obstruction: no subspace structure for `q > 2` -/

/-- A `MOD_q` count over a singleton support is the per-bit `ZMod q` value. -/
theorem modQStatOn_singleton (i : Fin n) (q : ℕ) (x : Fin n → Bool) :
    modQStatOn ({i} : Finset (Fin n)) q x = (if x i then (1 : ZMod q) else 0) := by
  unfold modQStatOn weightOn
  rw [Finset.sum_singleton]
  by_cases h : x i <;> simp [h]

/-- **The reachable residue set is not closed under `+` for `q = 3` (proved): the `2^rank` subspace structure is
MOD₂-specific.**  For a single `MOD₃` gate on a singleton support the reachable residues are `{0,1}`, and `1` is
reachable while `1 + 1 = 2` is not — so no F₃-subspace / rank cardinality applies. -/
theorem modq_residue_image_not_subspace :
    (1 : ZMod 3) ∈ Set.range (fun x : Fin 1 → Bool => modQStatOn ({0} : Finset (Fin 1)) 3 x) ∧
      (1 + 1 : ZMod 3) ∉ Set.range (fun x : Fin 1 → Bool => modQStatOn ({0} : Finset (Fin 1)) 3 x) := by
  refine ⟨⟨fun _ => true, ?_⟩, ?_⟩
  · simp [modQStatOn_singleton]
  · rintro ⟨x, hx⟩
    simp only [modQStatOn_singleton] at hx
    cases hb : x 0 <;> rw [hb] at hx <;> exact absurd hx (by decide)

end PallLean.Paper93.DeepMath.PathB.ACC0ModQFeasibility

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModQFeasibility.modq_realizable_iff_feasible
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModQFeasibility.modq_residue_image_not_subspace
