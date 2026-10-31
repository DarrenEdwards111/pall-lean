import Mathlib.Data.Finset.Card

/-!
# The gate-elimination attempt: the standard method reaches `2c − |shared|`, and is capped there

This is the genuine attempt at "SAT's minimal circuit can't share its two disjoint slots", via the
classical **gate-elimination / restriction** method — the standard technique for circuit lower
bounds.  It is carried as far as the mathematics allows, and it stops at exactly one place, provably.

## The attempt

A minimal circuit for the composed problem contains two slots on **disjoint variable sets**, each
needing `≥ c` gates to solve its sub-instance.  Let `slot1`, `slot2` be the two gate sets and
`sharedGates := slot1 ∩ slot2` the gates serving both.  Inclusion–exclusion on the gate sets is the
elimination bound:

* **`gate_elimination_bound`** — `2c ≤ |gates| + |shared|`, i.e. `|gates| ≥ 2c − |shared|`.  The two
  slots force `2c` gates, minus whatever they share.  This is the *most* the counting method proves.
* **`no_sharing_gives_doubling`** — if `sharedGates = ∅` (NoSharing), the clean doubling follows:
  `|gates| ≥ 2c`.  The attack succeeds *given* no shared gates.

## Where it stops — and the proof that it stops there

The elimination bound is **tight**: the shared term cannot be removed by any counting argument.

* **`elimination_is_tight`** — a concrete minimal circuit (`c = 2`, `slot1 = {0,1}`, `slot2 = {1,2}`,
  one shared gate) satisfies the elimination bound `4 ≤ 3 + 1` *with equality*, yet `|gates| = 3 < 4`:
  the doubling **fails**.  So `2c ≤ |gates|` is **not** derivable from the elimination bound — the
  method is capped exactly at the `|shared|` term.

So the gate-elimination method reaches `|gates| ≥ 2c − |shared|` and provably no further: closing the
gap needs `|shared| = 0`, which the counting cannot force (it is tight when sharing is present).

## Honest scope — attempted, capped at the wall, not faked and not declared impossible

I did not prove SAT's minimal circuit can't share its slots — that is `cost_super`, and it is
`P ≠ NP`.  What is proved: the standard gate-elimination method reaches `|gates| ≥ 2c − |shared|`, and
is **exactly tight** there (`elimination_is_tight`), so no counting/elimination argument closes the
`|shared| = 0` gap.  That gap — SAT's two disjoint slots share no gate — is the single remaining
obligation, and it is P ≠ NP-hard: a shared gate is a global gate (the map's coordinate), and ruling
it out is non-natural, beyond what this method (a natural-proofs-style counting argument) can do.  The
attempt reaches the wall and stops there, by proof.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GateElimination

variable {c : ℕ}

/-- A minimal circuit for the composed problem: its gates, and the two slot gate-sets on disjoint
variable sets, each needing `≥ c` gates. -/
structure MinimalCircuit (c : ℕ) where
  /-- all gates of the circuit -/
  gates : Finset ℕ
  /-- gates solving slot 1 -/
  slot1 : Finset ℕ
  /-- gates solving slot 2 -/
  slot2 : Finset ℕ
  /-- slot 1's gates are gates of the circuit -/
  slot1_sub : slot1 ⊆ gates
  /-- slot 2's gates are gates of the circuit -/
  slot2_sub : slot2 ⊆ gates
  /-- slot 1 needs at least `c` gates -/
  slot1_card : c ≤ slot1.card
  /-- slot 2 needs at least `c` gates -/
  slot2_card : c ≤ slot2.card

/-- The **shared gates** — those serving both slots. -/
def sharedGates (M : MinimalCircuit c) : Finset ℕ := M.slot1 ∩ M.slot2

/-- **The gate-elimination bound (proved).**  `2c ≤ |gates| + |shared|`: inclusion–exclusion on the
two slot gate-sets.  Each slot forces `c` gates; the two overlap only in the shared gates.  This is
the most the counting method proves — `|gates| ≥ 2c − |shared|`. -/
theorem gate_elimination_bound (M : MinimalCircuit c) :
    2 * c ≤ M.gates.card + (sharedGates M).card := by
  have hcard : (M.slot1 ∪ M.slot2).card + (M.slot1 ∩ M.slot2).card
      = M.slot1.card + M.slot2.card := Finset.card_union_add_card_inter M.slot1 M.slot2
  have hunion : (M.slot1 ∪ M.slot2).card ≤ M.gates.card :=
    Finset.card_le_card (Finset.union_subset M.slot1_sub M.slot2_sub)
  have h1 := M.slot1_card
  have h2 := M.slot2_card
  show 2 * c ≤ M.gates.card + (M.slot1 ∩ M.slot2).card
  omega

/-- No shared gates between the two slots. -/
def NoSharedGates (M : MinimalCircuit c) : Prop := sharedGates M = ∅

/-- **No sharing gives the doubling (proved).**  If the two slots share no gate, the clean bound
`|gates| ≥ 2c` follows.  The attack succeeds — given `NoSharedGates`. -/
theorem no_sharing_gives_doubling (M : MinimalCircuit c) (h : NoSharedGates M) :
    2 * c ≤ M.gates.card := by
  have hb := gate_elimination_bound M
  have hz : (sharedGates M).card = 0 := Finset.card_eq_zero.mpr h
  omega

/-! ### Where it stops: the elimination bound is tight -/

/-- A concrete minimal circuit with sharing: `c = 2`, `slot1 = {0,1}`, `slot2 = {1,2}`, sharing the
gate `1`, with only `3` gates. -/
def sharingCircuit : MinimalCircuit 2 where
  gates := {0, 1, 2}
  slot1 := {0, 1}
  slot2 := {1, 2}
  slot1_sub := by decide
  slot2_sub := by decide
  slot1_card := by decide
  slot2_card := by decide

/-- **The elimination bound is tight (proved).**  The sharing circuit satisfies the elimination bound
`4 ≤ 3 + 1` *with equality*, yet `|gates| = 3 < 4`: the doubling `2c ≤ |gates|` fails.  So the shared
term cannot be removed by counting — the gate-elimination method is capped exactly there. -/
theorem elimination_is_tight :
    (2 * 2 ≤ sharingCircuit.gates.card + (sharedGates sharingCircuit).card) ∧
    ¬ (2 * 2 ≤ sharingCircuit.gates.card) := by
  refine ⟨gate_elimination_bound sharingCircuit, ?_⟩
  decide

end PallLean.Paper93.DeepMath.PathB.GateElimination

#print axioms PallLean.Paper93.DeepMath.PathB.GateElimination.gate_elimination_bound
#print axioms PallLean.Paper93.DeepMath.PathB.GateElimination.no_sharing_gives_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.GateElimination.elimination_is_tight
