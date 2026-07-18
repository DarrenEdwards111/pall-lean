import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNonSizeDominated

/-!
# The schema evades relativization: `traceInv` is machine-dependent

The ceiling tower (`PolyCeiling`) showed that any content beyond time must come from a
super-additive measure — cross-row correlation.  A prior obstruction one might fear is
**relativization**: a proof technique relativizes if it holds relative to any oracle, and a
complexity measure is *language-invariant* (relativizing) if it is determined by the decided
language alone.  Language-invariant measures cannot separate P from NP by the classical
relativization barrier.

This file shows the trace measures are **not** language-invariant, so the schema is not blocked
by relativization a priori.  Two machines that decide the *same* language have *different*
`traceInv`:

* `haltMachine` halts at step `0`; its trace on `x` is `[x]`.
* `delay1Machine` takes one no-op step then halts; its trace on `x` is `[x, x]`.

Both decide the constant-false language (`haltMachine_decides`, `delay1Machine_decides`), yet
`traceInv_haltMachine_one = 2 ≠ 4 = traceInv_delay1Machine_one` (`traceInv_machine_dependent`).
So `traceInv` reads the machine's *actual computation*, not just its language behavior — exactly
the non-relativizing property.  A separation via a trace measure (super-additive or otherwise)
is therefore not excluded by relativization.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceRelativization

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.NonSizeDominated

/-- The machine that takes one no-op step (move-stay, no write), then halts. -/
def delay1Machine : Machine where
  State := Fin 2
  fin := inferInstance
  dec := inferInstance
  start := 0
  halt := fun s => decide (s = 1)
  δ := fun _ _ => (1, none, 2)
  accept := fun _ => false

theorem delay1_step (x : List Bool) :
    run delay1Machine 1 (init delay1Machine x) = (⟨(1 : Fin 2), 0, x⟩ : Cfg delay1Machine) := by
  show step delay1Machine (init delay1Machine x) = _
  rfl

theorem delay1_haltsBy (x : List Bool) (t : ℕ) (ht : 1 ≤ t) : HaltsBy delay1Machine x t := by
  have hh : delay1Machine.halt (run delay1Machine 1 (init delay1Machine x)).st = true := by
    rw [delay1_step]; rfl
  show delay1Machine.halt (run delay1Machine t (init delay1Machine x)).st = true
  rw [run_stable delay1Machine x ht hh, delay1_step]; rfl

theorem delay1_not_halted_0 (x : List Bool) :
    delay1Machine.halt (run delay1Machine 0 (init delay1Machine x)).st = false := by
  rw [run_zero]; rfl

/-! ## Both decide the constant-false language -/

theorem haltMachine_decides : Decides haltMachine (fun _ => false) (fun _ => 0) := by
  intro x
  refine ⟨haltMachine_haltsBy x 0, ?_⟩
  show haltMachine.accept (run haltMachine 0 (init haltMachine x)).st = false
  rw [run_zero]; rfl

theorem delay1Machine_decides : Decides delay1Machine (fun _ => false) (fun _ => 1) := by
  intro x
  refine ⟨delay1_haltsBy x 1 (le_refl 1), ?_⟩
  show delay1Machine.accept (run delay1Machine 1 (init delay1Machine x)).st = false
  rw [delay1_step]; rfl

/-! ## The traces differ -/

theorem minHalt_delay1 (n : ℕ) : minHalt delay1Machine n = 1 := by
  have hex : ∃ t, HaltsAllAt delay1Machine n t :=
    ⟨1, fun x _ => delay1_haltsBy x 1 (le_refl 1)⟩
  show (if h : ∃ t, HaltsAllAt delay1Machine n t then Nat.find h else 0) = 1
  rw [dif_pos hex]
  rw [Nat.find_eq_iff]
  refine ⟨fun x _ => delay1_haltsBy x 1 (le_refl 1), ?_⟩
  intro m hm hall
  interval_cases m
  have := hall (List.replicate n false) (by simp)
  rw [show HaltsBy delay1Machine (List.replicate n false) 0
      = (delay1Machine.halt (run delay1Machine 0 (init delay1Machine _)).st = true) from rfl,
    delay1_not_halted_0] at this
  simp at this

theorem traceObj_delay1 (x : List Bool) : traceObj delay1Machine 1 x = [x, x] := by
  show (List.range 2).map (fun i => (run delay1Machine i (init delay1Machine x)).tp) = [x, x]
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [run_zero, delay1_step]
  rfl

theorem traceInv_haltMachine_one : traceInv traceSize haltMachine 1 = 2 := by
  rw [traceInv_haltMachine]
  unfold singleRowProfile
  have heq : (fun v : Fin 1 → Bool => traceSize [List.ofFn v]) = fun _ => 2 := by
    funext v
    simp [traceSize]
  rw [heq, Finset.sup_const Finset.univ_nonempty]

theorem traceInv_delay1Machine_one : traceInv traceSize delay1Machine 1 = 4 := by
  unfold traceInv
  rw [minHalt_delay1]
  have heq : (fun v : Fin 1 → Bool =>
      traceSize (traceObj delay1Machine 1 (List.ofFn v))) = fun _ => 4 := by
    funext v
    rw [traceObj_delay1]
    simp [traceSize]
  rw [heq, Finset.sup_const Finset.univ_nonempty]

/-! ## Machine-dependence -/

/-- **`traceInv` is machine-dependent.**  Two machines deciding the same (constant-false)
language have different `traceInv traceSize` — so the trace measure is not a function of the
decided language.  A relativizing (language-invariant) measure could not distinguish them;
`traceInv` does, by reading the actual computation.  The schema is not blocked by
relativization. -/
theorem traceInv_machine_dependent :
    ∃ (M₁ M₂ : Machine) (L : List Bool → Bool) (T₁ T₂ : ℕ → ℕ),
      Decides M₁ L T₁ ∧ Decides M₂ L T₂
        ∧ traceInv traceSize M₁ 1 ≠ traceInv traceSize M₂ 1 :=
  ⟨haltMachine, delay1Machine, fun _ => false, fun _ => 0, fun _ => 1,
    haltMachine_decides, delay1Machine_decides, by
      rw [traceInv_haltMachine_one, traceInv_delay1Machine_one]; decide⟩

end PallLean.Paper93.DeepMath.PathB.TraceRelativization
