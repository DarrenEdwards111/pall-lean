import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedInfoCap

/-!
# Step (5): the horizon laws DERIVED, not assumed

The old black-hole model failed because it *attached* an expensive horizon and asserted the computation must pay
for it.  In the charged model the true laws are **derivable from the trace semantics**, and they say something
different — and honest:

* `forward_determinism` — **the derived no-shortcut core**: if two inputs agree on every variable read from time
  `t` onward and reach the same time-`t` state, the program's outputs agree.  The state must carry every
  distinction the computation still needs — and this is the *only* thing it must carry.

* `residual_decodes_from_state` — **the honest `regulatedDivergence`**: the output is always reconstructible from
  the time-`t` state, and the decoder is *the program's own suffix* — reconstruction cost is bounded by the
  remaining charge (`decoder_cost`: `cost − t`).  No externally-attached reconstruction cost exists to diverge:
  the only decoder the computation ever needs is the one it already contains.

* `collision_safe` — **why attaching a horizon cannot force payment**: in a correct program, state collisions
  (information loss — "crossing the horizon") happen only between inputs the residual function no longer
  distinguishes.  Forgetting is allowed exactly when the output does not require the reconstruction — the old
  model's `NoHorizonShortcut` premise, derived, with its quantifier corrected.

* `no_input_reconstruction` — beyond a collision, *input* reconstruction is impossible (not expensive —
  impossible).  Correct easy programs do this constantly: `qfProg A` and `parityProg` run on 3 wires, colliding
  states maximally, and stay correct because the accumulator is all the residual function needs — the
  machine-checked instance of "easy traces avoid the horizon or decode cheaply".

These are consistency laws (possibility/upper-bound shaped), derived rather than assumed.  The hardness content —
forcing a program to carry *many* distinctions — is not here and cannot be: by `collision_safe` it is a property
of the function's residual structure under the program's *own* read schedule (re-reading dissolves it, as
`qfProg A` shows), and forcing it for SAT against all schedules is the step-(6) target, at-least-separation-hard.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DerivedHorizon

open PallLean.Paper93.DeepMath.PathB.ChargedGate
open PallLean.Paper93.DeepMath.PathB.ChargedCircuit

variable {n w : ℕ}

/-- The variables read from time `t` onward. -/
def fwdReads (gs : List (Gate n w)) (t : ℕ) : Finset (Fin n) :=
  ((gs.drop t).filterMap Gate.readsInput).toFinset

/-- The time-`t` state of the run on input `x`. -/
def stateAt (P : Prog n w) (x : Fin n → Bool) (t : ℕ) : Fin w → Bool :=
  runGates x (P.gates.take t) (fun _ => false)

/-- **The derived no-shortcut core (forward determinism).**  Inputs agreeing on all forward reads and colliding
at time `t` produce equal outputs: the state carries every distinction the computation still needs — and only
those. -/
theorem forward_determinism (P : Prog n w) (t : ℕ) (x x' : Fin n → Bool)
    (hagree : ∀ i ∈ fwdReads P.gates t, x i = x' i)
    (hstate : stateAt P x t = stateAt P x' t) :
    P.run x = P.run x' := by
  unfold Prog.run
  rw [← List.take_append_drop t P.gates, runGates_append', runGates_append']
  rw [show runGates x (P.gates.take t) (fun _ => false)
      = runGates x' (P.gates.take t) (fun _ => false) from hstate]
  rw [runGates_congr x x' (P.gates.drop t) _ (fun i hi =>
    hagree i (List.mem_toFinset.mpr (List.mem_filterMap.mpr hi)))]

/-- **The honest `regulatedDivergence`: the decoder is the suffix.**  For any forward setting `α`, the output on
every `α`-forward-agreeing input is reconstructible from the time-`t` state — by running the program's own
remaining gates.  Reconstruction never needs more than the remaining charge. -/
theorem residual_decodes_from_state (P : Prog n w) (f : (Fin n → Bool) → Bool)
    (hP : ∀ x, P.run x = f x) (t : ℕ) (α : Fin n → Bool) :
    ∃ F : (Fin w → Bool) → Bool,
      ∀ x : Fin n → Bool, (∀ i ∈ fwdReads P.gates t, x i = α i) →
        f x = F (stateAt P x t) := by
  refine ⟨fun s => runGates α (P.gates.drop t) s P.out, fun x hx => ?_⟩
  rw [← hP x]
  unfold Prog.run
  conv_lhs => rw [← List.take_append_drop t P.gates, runGates_append']
  rw [runGates_congr x α (P.gates.drop t)
    (runGates x (P.gates.take t) (fun _ => false)) (fun i hi =>
      hx i (List.mem_toFinset.mpr (List.mem_filterMap.mpr hi)))]
  rfl

/-- The decoder's charge is the remaining charge. -/
theorem decoder_cost (P : Prog n w) (t : ℕ) : (P.gates.drop t).length = P.cost - t :=
  List.length_drop ..

/-- **Collision safety**: a correct program loses only information its residual function no longer needs.  This
is why attaching an expensive horizon cannot force payment — the computation pays only for `f`-needed
distinctions. -/
theorem collision_safe (P : Prog n w) (f : (Fin n → Bool) → Bool) (hP : ∀ x, P.run x = f x)
    (t : ℕ) (x x' : Fin n → Bool)
    (hagree : ∀ i ∈ fwdReads P.gates t, x i = x' i)
    (hstate : stateAt P x t = stateAt P x' t) :
    f x = f x' := by
  rw [← hP x, ← hP x']
  exact forward_determinism P t x x' hagree hstate

/-- **Beyond a collision, input reconstruction is impossible** — not expensive, impossible.  (Correct programs do
this freely on `f`-irrelevant distinctions: `qfProg A` runs on 3 wires.) -/
theorem no_input_reconstruction (P : Prog n w) (t : ℕ) (x x' : Fin n → Bool) (hne : x ≠ x')
    (hstate : stateAt P x t = stateAt P x' t) :
    ¬ ∃ D : (Fin w → Bool) → (Fin n → Bool), D (stateAt P x t) = x ∧ D (stateAt P x' t) = x' := by
  rintro ⟨D, h1, h2⟩
  exact hne (by rw [← h1, ← h2, hstate])

end PallLean.Paper93.DeepMath.PathB.DerivedHorizon

#print axioms PallLean.Paper93.DeepMath.PathB.DerivedHorizon.forward_determinism
#print axioms PallLean.Paper93.DeepMath.PathB.DerivedHorizon.residual_decodes_from_state
#print axioms PallLean.Paper93.DeepMath.PathB.DerivedHorizon.collision_safe
#print axioms PallLean.Paper93.DeepMath.PathB.DerivedHorizon.no_input_reconstruction
