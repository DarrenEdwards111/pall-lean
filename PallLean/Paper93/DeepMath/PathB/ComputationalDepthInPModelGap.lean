import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedHolographicMachine

/-!
# The `InP` model gap: `ChargedMachine.InP` is advice-contaminated; the equivalence bridge is FALSE

The natural next step after `reductionClosure` (proved for `ComposableMachine.InP`) would be a poly-time
*equivalence bridge* `ChargedMachine.InP L ↔ ComposableMachine.InP L`, transporting the closure to the
observer-class fence (whose `PLang` is `ChargedMachine.InP`).  **This file proves that bridge does not exist**,
and pins exactly why — an honest negative result, not a manufactured closure.

## The mechanism

`ChargedMachine.clock : Nat → Nat` is a *free structure field*, constrained only by `PolyBounded`.  The decision
is `decide M x = accept (run M (clock |x|) x).state` — it reads the accept bit **at whatever timestep the clock
names**.  A trivial two-state control (step `0` sits in a reject state, step `≥ 1` sits in an accept state) with
`clock n := if h n then 1 else 0` therefore decides the tally language `L(x) = h(|x|)` for **any**
`h : Nat → Bool` (`tally_in_charged_InP`).  Since `h` is arbitrary — including non-computable — the clock carries
one bit of per-length advice, and `ChargedMachine.InP` contains all tally languages: it is strictly larger than
uniform `P` and is not even contained in the computable languages.

## The contrast

`ComposableMachine.Decides M L T` requires `HaltsBy` and reads the accept bit at a **halt** state; by `run_stable`
the answer is independent of the clock past the halting time, so a fixed `ComposableMachine` decides **exactly one**
language (`composable_decides_unique`).  The clock is a *halting certificate*, not advice.  Hence
`ComposableMachine.InP` is genuine (computable, machine-determined) `P`.

## Conclusion (honest)

The two `InP` notions are **not** equivalent: `ChargedMachine.InP ⊋ ComposableMachine.InP`, the gap being exactly
the tally / advice languages the free clock admits.  So:

* the requested bridge is **false** and cannot be built;
* `reductionClosure` genuinely holds for `ComposableMachine.InP` (the faithful `P`), but does **not** transfer to
  the `ChargedMachine`-based observer-class fence;
* more consequentially, the corpus's `ChargedMachine.InP` is **not a faithful definition of `P`** — its free
  `clock` field is a non-uniform advice channel.

Both contrasting facts below are machine-checked.  The only non-formalized step is "there exist non-computable
`h`" (a standard truth needing a computability model not built here); the advice-contamination itself — a single
finite control deciding uncountably many languages by changing only the clock — is fully formal.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InPModelGap

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## `ChargedMachine.InP` contains every tally language (advice via the free clock) -/

/-- A trivial two-state charged machine: it sits in state `0` (reject) at time `0`, and in state `1` (accept) at
every later time.  All of the decision is delegated to the free `clock` field. -/
def tallyM (h : Nat → Bool) : ChargedHolographicMachine.ChargedMachine where
  Q := 2
  start := 0
  delta := fun _ _ => (1, false, 2)
  accept := fun i => decide (i = 1)
  clock := fun n => if h n then 1 else 0

/-- The trivial machine decides the tally language `x ↦ h |x|` — the clock does all the work. -/
theorem tallyM_decides (h : Nat → Bool) (x : List Bool) :
    ChargedHolographicMachine.decide (tallyM h) x = h x.length := by
  unfold ChargedHolographicMachine.decide
  by_cases hh : h x.length = true
  · have hc : (tallyM h).clock x.length = 1 := by simp [tallyM, hh]
    rw [hc]
    have hrun : ChargedHolographicMachine.run (tallyM h) 1 (ChargedHolographicMachine.init (tallyM h) x)
        = ChargedHolographicMachine.step (tallyM h) (ChargedHolographicMachine.init (tallyM h) x) := rfl
    rw [hrun]
    simp [ChargedHolographicMachine.step, ChargedHolographicMachine.init, tallyM, hh]
  · have hf : h x.length = false := by simpa using hh
    have hc : (tallyM h).clock x.length = 0 := by simp [tallyM, hf]
    rw [hc]
    simp [ChargedHolographicMachine.run, ChargedHolographicMachine.init, tallyM, hf]

/-- **Every tally language is in `ChargedMachine.InP`.**  For arbitrary `h : Nat → Bool` — including
non-computable `h` — the language `x ↦ h |x|` is decided by a fixed two-state charged machine whose only
`h`-dependence is the poly-bounded (`≤ 1`) clock.  So `ChargedMachine.InP` is strictly larger than uniform `P`;
the free clock is a per-length advice channel. -/
theorem tally_in_charged_InP (h : Nat → Bool) :
    ChargedHolographicMachine.InP (fun x => h x.length) := by
  refine ⟨tallyM h, ?_, ?_⟩
  · refine ⟨1, 0, fun n => ?_⟩
    simp only [tallyM]
    split <;> simp
  · intro x
    exact tallyM_decides h x

/-! ## `ComposableMachine.InP` has no such leak: a machine determines its language -/

open PallLean.Paper93.DeepMath.PathB.ComposableMachine (Machine Decides decideOut HaltsBy run init run_stable)

/-- **The clock carries no advice in the composable model.**  If a single `ComposableMachine` decides `L₁` within
clock `T₁` and `L₂` within clock `T₂`, then `L₁ = L₂`.  The answer is read at a genuine halt state, so by
`run_stable` it does not depend on the clock beyond the halting time — a fixed machine decides exactly one
language.  This is precisely the property `ChargedMachine.InP` lacks (`tally_in_charged_InP`: one control, many
languages). -/
theorem composable_decides_unique {M : Machine} {L₁ L₂ : List Bool → Bool} {T₁ T₂ : ℕ → ℕ}
    (h₁ : Decides M L₁ T₁) (h₂ : Decides M L₂ T₂) : L₁ = L₂ := by
  funext x
  obtain ⟨hh₁, hd₁⟩ := h₁ x
  obtain ⟨hh₂, hd₂⟩ := h₂ x
  rw [← hd₁, ← hd₂]
  unfold decideOut
  rcases le_total (T₁ x.length) (T₂ x.length) with hle | hle
  · rw [run_stable M x hle hh₁]
  · rw [run_stable M x hle hh₂]

end PallLean.Paper93.DeepMath.PathB.InPModelGap
