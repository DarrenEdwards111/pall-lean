import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineBridge

/-!
# Universal machine, brick 2b: first-match recovery

Brick 2 proved faithful containment (`rule_mem`) and the lookup infrastructure.  This brick closes
the recovery: `lookupRule (serialRules data) i.val b` returns EXACTLY `data`'s transition on
`(state i, symbol b)`.  The serialized transition table is not just contained but faithfully and
unambiguously readable — the property the universal machine's step loop (brick 3) will consume.

## What is proved

* **`lookupRule_flatMap`** — the ordering induction: over any `Nodup` list `L` of states containing
  `i₀`, looking up `(i₀.val, b₀)` in the flattened rule table returns `data`'s transition.  The
  earlier rules are skipped because their state key `j.val ≠ i₀.val` (distinct states, by
  `Fin.val_injective`) or their symbol key differs.
* **`lookupRule_recovers`** — the payoff at `L = finRange k`: `lookupRule (serialRules data) i.val b
  = some ((δ i b).1.val, (δ i b).2.1, (δ i b).2.2.val)`.  Serialize a machine, look up any
  transition, get exactly the original back.

## Honest scope

The transition table now round-trips through the flat serialization AND is unambiguously readable by
a `(state, symbol)` lookup — bricks 2 + 2b together make `serialOf` a faithful, decodable machine
description.  What remains for the universal machine (unchanged): the step-simulation loop that uses
this lookup to advance a stored configuration (brick 3), the clocked run (brick 4), the lazy-delay
diagonal (brick 5), and — flagged in brick 2 — a `halt`-field extension for full `HaltsBy`
faithfulness.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineRecovery

open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal
open PallLean.Paper93.DeepMath.PathB.UniversalMachineBridge

variable {k : ℕ}

/-- **The ordering induction (proved).**  Over a `Nodup` list of states containing `i₀`, the lookup
of `(i₀.val, b₀)` in the flattened rule table returns `data`'s transition: earlier rules are skipped
because their `(state, symbol)` key differs. -/
theorem lookupRule_flatMap (data : FinMachineData k) :
    ∀ (L : List (Fin k)), L.Nodup → ∀ (i₀ : Fin k), i₀ ∈ L → ∀ (b₀ : Bool),
      lookupRule (L.flatMap (fun i => [mkRule data i false, mkRule data i true])) i₀.val b₀
        = some ((data.2.2.1 i₀ b₀).1.val, (data.2.2.1 i₀ b₀).2.1, (data.2.2.1 i₀ b₀).2.2.val) := by
  intro L
  induction L with
  | nil => intro _ i₀ hmem _; simp at hmem
  | cons j js ih =>
    intro hnodup i₀ hmem b₀
    have hjs : js.Nodup := (List.nodup_cons.mp hnodup).2
    show lookupRule (mkRule data j false :: mkRule data j true ::
      js.flatMap (fun i => [mkRule data i false, mkRule data i true])) i₀.val b₀ = _
    by_cases hj : j = i₀
    · subst hj
      cases b₀ with
      | false => exact lookupRule_cons_match _ _ _ _ ⟨rfl, rfl⟩
      | true =>
        rw [lookupRule, if_neg (by rintro ⟨_, h2⟩; exact Bool.noConfusion h2)]
        exact lookupRule_cons_match _ _ _ _ ⟨rfl, rfl⟩
    · have hij : i₀ ∈ js := (List.mem_cons.mp hmem).resolve_left (fun h => hj h.symm)
      have h1 : ¬ ((mkRule data j false).1 = i₀.val ∧ (mkRule data j false).2.1 = b₀) :=
        fun h => hj (Fin.val_injective h.1)
      have h2 : ¬ ((mkRule data j true).1 = i₀.val ∧ (mkRule data j true).2.1 = b₀) :=
        fun h => hj (Fin.val_injective h.1)
      rw [lookupRule, if_neg h1, lookupRule, if_neg h2]
      exact ih hjs i₀ hij b₀

/-- **First-match recovery (proved).**  Serialize a machine and look up any `(state i, symbol b)`:
you get back exactly `data`'s transition.  The serialized transition table is faithfully and
unambiguously readable. -/
theorem lookupRule_recovers (data : FinMachineData k) (i : Fin k) (b : Bool) :
    lookupRule (serialRules data) i.val b
      = some ((data.2.2.1 i b).1.val, (data.2.2.1 i b).2.1, (data.2.2.1 i b).2.2.val) :=
  lookupRule_flatMap data (List.finRange k) (List.nodup_finRange k) i (List.mem_finRange i) b

end PallLean.Paper93.DeepMath.PathB.UniversalMachineRecovery

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineRecovery.lookupRule_flatMap
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineRecovery.lookupRule_recovers
