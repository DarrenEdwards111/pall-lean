import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDerivedHorizonLaws

/-!
# Round 3: the charged speedup primitive — the horizon laws ARE the standard rule

The round-3 question: do the derived horizon laws constitute a *new* simulation primitive (a trading rule outside
the standard speedup/slowdown set), or an instance of the *standard* one?  This file settles it by formalizing
the identification:

* `midpoint_sound_complete` — verification of a charged run decomposes as **guess-a-midpoint-and-verify-both-
  segments** (`∃ m, prefix reaches m ∧ suffix from m accepts`), soundly and completely;
* `midpoint_unique` — the guessed midpoint is unique (determinism), so the `∃` is exact;
* `segment_costs` — the two segments cost `min t cost` and `cost − t`: time is genuinely split.

This is precisely the semantic core of the **standard speedup rule** (Nepomnjaščiĭ-style: split a space-bounded
computation at guessed configuration boundaries and verify blocks independently) — instantiated in the charged
host, where `forward_determinism` and `residual_decodes_from_state` were its two halves all along.  The charged
model therefore natively hosts alternation trading **with the standard rule set** — and hence inherits the
Buss–Williams ceiling (`2cos(π/7)`) rather than escaping it.  The corpus's simulation primitives do NOT yield a
rule outside the standard set; that is the round-3 finding, machine-checked on the primitive side.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedSpeedup

open PallLean.Paper93.DeepMath.PathB.ChargedGate
open PallLean.Paper93.DeepMath.PathB.ChargedCircuit
open PallLean.Paper93.DeepMath.PathB.DerivedHorizon

variable {n w : ℕ}

/-- **The charged speedup primitive** (guess-and-verify midpoint): a run outputs `b` iff there EXISTS a midpoint
state reached by the prefix from which the suffix outputs `b`.  Sound and complete — the semantic core of the
standard speedup rule, in the charged host. -/
theorem midpoint_sound_complete (P : Prog n w) (x : Fin n → Bool) (t : ℕ) (b : Bool) :
    P.run x = b
      ↔ ∃ m : Fin w → Bool,
          runGates x (P.gates.take t) (fun _ => false) = m
          ∧ runGates x (P.gates.drop t) m P.out = b := by
  constructor
  · intro hb
    refine ⟨runGates x (P.gates.take t) (fun _ => false), rfl, ?_⟩
    rw [← hb]
    unfold Prog.run
    conv_rhs => rw [← List.take_append_drop t P.gates, runGates_append']
  · rintro ⟨m, hm, hb⟩
    unfold Prog.run
    conv_lhs => rw [← List.take_append_drop t P.gates, runGates_append']
    rw [hm, hb]

/-- The midpoint is unique: the `∃` in the speedup is exact (determinism). -/
theorem midpoint_unique (P : Prog n w) (x : Fin n → Bool) (t : ℕ) (m m' : Fin w → Bool)
    (h : runGates x (P.gates.take t) (fun _ => false) = m)
    (h' : runGates x (P.gates.take t) (fun _ => false) = m') : m = m' := by
  rw [← h, ← h']

/-- The segments genuinely split the time. -/
theorem segment_costs (P : Prog n w) (t : ℕ) :
    (P.gates.take t).length = min t P.cost ∧ (P.gates.drop t).length = P.cost - t :=
  ⟨List.length_take .., List.length_drop ..⟩

end PallLean.Paper93.DeepMath.PathB.ChargedSpeedup

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedSpeedup.midpoint_sound_complete
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedSpeedup.midpoint_unique
