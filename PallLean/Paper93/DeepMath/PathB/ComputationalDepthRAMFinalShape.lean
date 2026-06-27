import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMDiagonal
import Mathlib.Tactic

/-!
# The final theorem shape: `NEXP ⊄ ACC⁰` from named classical sockets (PROVED, conditional) — step 6

This file assembles the whole RAM lazy-diagonal arc into the target shape — `¬ NEXP ⊆ ACC⁰` — *proved from an
explicit, named bundle of the classical assumptions*.  It is the honest culmination: every RAM-engineering and
diagonalisation piece is unconditional and `sorry`-free; the only inputs are the two separation-strength
classical bridges, gathered into one `WilliamsBridge` hypothesis so they cannot hide.

The classes `ACC0`, `NEXP` are abstract predicates on decision functions `ℕ → ℕ` (Boolean outputs).  The decider
is `ramDiag sim`, the diagonal of the clocked simulator (brick 4 / the integrated `simDecider`).  The bundle:

* `faithful` — **Socket 1**: the clocked simulator reproduces the class value on every self-application.  Holds
  exactly when the budget dominates each machine's runtime, i.e. `ACC⁰` membership — the Beigel–Tarui `SYM∘AND`
  quasipoly normal form plus the Williams fast-`SAT` speed-up.  *Classical, not proved here.*
* `decider_in_nexp` — **Socket 2**: the decider lies in `NEXP` — again the Williams fast-`SAT` content.
  *Classical, not proved here.*
* `acc0_enumerated` — the structural fact that the clocked family `C` enumerates `ACC⁰` (every `ACC⁰` function
  is some `C e`); this is how the abstract diagonal class is identified with `ACC⁰`.
* `boolean` — the class is Boolean on its diagonal.

The theorem then derives the separation by pure diagonalisation (`diagonal_separation_skeleton`, proved).

**This is not a proof of `NEXP ⊄ ACC⁰`.**  Discharging `WilliamsBridge` *is* that theorem; this file proves the
implication `WilliamsBridge → NEXP ⊄ ACC⁰`, exhibiting the diagonal skeleton onto which the classical bridges
plug, with the separation-strength content fully isolated in named fields.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- The named bundle of classical assumptions linking the clocked simulator/class to `ACC⁰` and `NEXP`.  Each
field is a separation-strength classical bridge or a structural identification; none is proved here. -/
structure WilliamsBridge (ACC0 NEXP : (ℕ → ℕ) → Prop) (sim C : ℕ → ℕ → ℕ) : Prop where
  /-- Socket 1: faithful clocked simulation on the diagonal (budget domination = `ACC⁰` membership). -/
  faithful : FaithfulOnDiagonal C sim
  /-- The class is Boolean on its own diagonal. -/
  boolean : ∀ e, C e e ≤ 1
  /-- Socket 2: the diagonal decider lies in `NEXP` (Williams fast-`SAT`). -/
  decider_in_nexp : NEXP (ramDiag sim)
  /-- The clocked family `C` enumerates `ACC⁰`: every `ACC⁰` function is some row `C e`. -/
  acc0_enumerated : ∀ f : ℕ → ℕ, ACC0 f → ∃ e, ∀ x, C e x = f x

/-- **`NEXP ⊄ ACC⁰`, from the named classical bridge.**  Under `WilliamsBridge`, the diagonal decider
`ramDiag sim` is in `NEXP` (Socket 2) but is not in `ACC⁰` (pure diagonalisation against the enumerated class),
so `NEXP` is not contained in `ACC⁰`.  The whole proof below the sockets is unconditional. -/
theorem NEXP_not_subset_ACC0
    (ACC0 NEXP : (ℕ → ℕ) → Prop) (sim C : ℕ → ℕ → ℕ)
    (H : WilliamsBridge ACC0 NEXP sim C) :
    ¬ (∀ f : ℕ → ℕ, NEXP f → ACC0 f) := by
  intro hsub
  -- the decider is in NEXP (Socket 2), hence — if NEXP ⊆ ACC⁰ — in ACC⁰
  have hacc0 : ACC0 (ramDiag sim) := hsub _ H.decider_in_nexp
  -- ACC⁰ functions are enumerated by the clocked family C
  obtain ⟨e, he⟩ := H.acc0_enumerated _ hacc0
  -- but the diagonal escapes the class: no e has C e = ramDiag sim
  exact diagonal_separation_skeleton C sim H.faithful H.boolean ⟨e, he⟩

/-- The same conclusion phrased as set non-inclusion of the function classes. -/
theorem NEXP_not_subset_ACC0'
    (ACC0 NEXP : (ℕ → ℕ) → Prop) (sim C : ℕ → ℕ → ℕ)
    (H : WilliamsBridge ACC0 NEXP sim C) :
    ¬ {f | NEXP f} ⊆ {f | ACC0 f} := by
  intro hsub
  exact NEXP_not_subset_ACC0 ACC0 NEXP sim C H (fun f hf => hsub hf)

/-- **The decider witnesses the separation**: it is in `NEXP` and not in `ACC⁰`.  This is the explicit
separating function (the diagonal of the clocked simulator), with both memberships sourced from the bundle. -/
theorem ramDiag_separates
    (ACC0 NEXP : (ℕ → ℕ) → Prop) (sim C : ℕ → ℕ → ℕ)
    (H : WilliamsBridge ACC0 NEXP sim C) :
    NEXP (ramDiag sim) ∧ ¬ ACC0 (ramDiag sim) := by
  refine ⟨H.decider_in_nexp, ?_⟩
  intro hacc0
  obtain ⟨e, he⟩ := H.acc0_enumerated _ hacc0
  exact diagonal_separation_skeleton C sim H.faithful H.boolean ⟨e, he⟩

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.NEXP_not_subset_ACC0
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.NEXP_not_subset_ACC0'
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.ramDiag_separates
