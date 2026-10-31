import Mathlib.Data.Nat.Basic

/-!
# The ∀ trick: you don't need the value on SAT — but you need the universal to be TRUE

Darren's move: we never need the *actual value* of the invariant on SAT.  A lower bound is a
**universal** — "∀ circuits `C` computing SAT, the bound holds" — not a value.  Quantify, don't
evaluate.  That is exactly right, and it is how every lower bound in the subject actually works: the
value is a red herring.  This file makes the move precise and then shows, honestly, what it costs.

**What the ∀ trick genuinely removes — the value.**  `forall_trick_value_free`: given the universal
`∀ C, StrongBound C`, you read the bound off at any circuit with no value ever evaluated.  There is
no `v = value(SAT)` anywhere in the argument.  Darren is right.

**What it does not remove — the universal's TRUTH.**  A universal is only as true as its weakest
instance (`counterexample_refutes`: one bad circuit refutes the whole `∀`).  Quantifying is free; the
*truth of the quantified predicate over every circuit in the domain* is the entire problem — the ∀
relocates the difficulty, it does not dissolve it.

**Uhlig is exactly the bad instance.**  Mass production builds a circuit (`uhligSharer`) that
computes the block demand by *sharing* — gate count driven below the demand, the overlap absorbing
the rest.  It satisfies the always-true weak bound (`uhlig_keeps_weak`) and violates the separating
strong bound (`uhlig_breaks_strong`) *simultaneously* (`weak_true_strong_false_same_circuit`).  So
the strong universal over **all** circuits is false (`uhlig_refutes_unrestricted`): the value-free ∀
trick **cannot run on the unrestricted domain**.

**So the ∀ must restrict its domain — and the restriction is the reading.**  The only way to keep the
universal true is to quantify over *SAT-computing* circuits and assert they obey the bound
(`restricted_forall_trick`).  And `forall_trick_relocates_not_removes` (`Iff.rfl`) shows that this
restricted universal's truth is *definitionally* the **reading** — SAT-circuits forbid the Uhlig
sharer.  The value on SAT is dissolved into the truth of a universal over SAT-circuits; supplying
that truth is `cost_super`.

## Honest scope — the value goes, the wall stays

The ∀ trick is real and correct: no value is needed.  But "∀ C computing SAT, `|C|` large" *is*
`P ≠ NP`; quantifying does not make it free — it relocates all the difficulty into the predicate's
truth over the domain, and Uhlig proves the predicate is false unless the domain is restricted to
SAT-circuits.  That restriction — SAT-circuits obey the overlap-free bound, i.e. computing SAT
forbids the mass-production collapse — is the reading, and it is `cost_super`.  The value is a red
herring; the truth of the universal is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForallTrick

/-- A tower circuit seen through the two numbers the counting argument cares about: its `gates` count
and its witness `overlap` (double-counted witness mass — the Uhlig residue). -/
structure TowerCircuit where
  /-- number of gates -/
  gates : ℕ
  /-- witness overlap: double-counted witness mass (the Uhlig residue) -/
  overlap : ℕ

/-- The **weak universal** — always true (this is `the_reason_with_overlap`): the block demand `k·b`
is at most `gates + overlap`.  True for *every* circuit, hypothesis-free — but too weak to separate,
because `overlap` can be as large as the demand. -/
def WeakBound (k b : ℕ) (C : TowerCircuit) : Prop := k * b ≤ C.gates + C.overlap

/-- The **strong universal** — the overlap-free bound that would separate: `k·b ≤ gates`.  This is
what a lower bound needs; whether it holds over the domain is the whole question. -/
def StrongBound (k b : ℕ) (C : TowerCircuit) : Prop := k * b ≤ C.gates

/-- **The ∀ trick is value-free (proved).**  A universally-quantified bound yields the lower bound at
any circuit *without ever evaluating the invariant's value on SAT* — you read it off the universal.
Darren's point: the value is not needed. -/
theorem forall_trick_value_free (k b : ℕ) (H : ∀ C, StrongBound k b C) (C : TowerCircuit) :
    k * b ≤ C.gates := H C

/-- **A universal is only as true as its weakest instance (proved).**  A single circuit that violates
the bound refutes the whole `∀`.  Quantifying is free; the universal's *truth* is not. -/
theorem counterexample_refutes (k b : ℕ) (C₀ : TowerCircuit) (h : ¬ StrongBound k b C₀) :
    ¬ ∀ C, StrongBound k b C :=
  fun H => h (H C₀)

/-- The **Uhlig mass-production circuit**: `k = 2` blocks of `b = 3` (demand `6`), realised with only
`3` gates by sharing — the `overlap = 3` absorbs the rest.  The concrete `overlap_collapses`: heavy
sharing drives the gate count below the demand. -/
def uhligSharer : TowerCircuit := ⟨3, 3⟩

/-- **Uhlig keeps the weak bound (proved).**  `6 ≤ 3 + 3`: the always-true universal survives. -/
theorem uhlig_keeps_weak : WeakBound 2 3 uhligSharer := by
  show (2 * 3 : ℕ) ≤ 3 + 3
  omega

/-- **Uhlig breaks the strong bound (proved).**  `¬ (6 ≤ 3)`: the separating universal fails on this
one circuit — sharing has driven the gate count below the demand. -/
theorem uhlig_breaks_strong : ¬ StrongBound 2 3 uhligSharer := by
  intro h
  have h6 : (2 * 3 : ℕ) ≤ 3 := h
  omega

/-- **Uhlig refutes the unrestricted ∀ trick (proved).**  Because the sharer breaks the strong bound,
the strong universal over *all* circuits is false — the value-free ∀ trick cannot run on the
unrestricted domain.  Mass production is exactly the counterexample. -/
theorem uhlig_refutes_unrestricted : ¬ ∀ C, StrongBound 2 3 C :=
  counterexample_refutes 2 3 uhligSharer uhlig_breaks_strong

/-- **The gap the ∀ trick leaves (proved).**  The Uhlig sharer satisfies the weak universal and
violates the strong one *simultaneously*: the always-true bound is too weak to separate, and the
separating bound is not always true.  Closing the gap = forbidding this circuit for SAT = the
reading. -/
theorem weak_true_strong_false_same_circuit :
    WeakBound 2 3 uhligSharer ∧ ¬ StrongBound 2 3 uhligSharer :=
  ⟨uhlig_keeps_weak, uhlig_breaks_strong⟩

/-- The **reading**: the invariant is high on SAT — every circuit that *computes SAT* obeys the strong
bound.  A property of SAT's circuits, supplied separately; not a value. -/
def Reading (k b : ℕ) (ComputesSAT : TowerCircuit → Prop) : Prop :=
  ∀ C, ComputesSAT C → StrongBound k b C

/-- **Given the reading, the restricted ∀ trick runs — value-free (proved).**  Over the SAT-circuit
domain the bound holds at every circuit, no value evaluated.  The ∀ trick works — *once the reading
restricts the domain* (excludes the Uhlig sharer). -/
theorem restricted_forall_trick (k b : ℕ) (ComputesSAT : TowerCircuit → Prop)
    (R : Reading k b ComputesSAT) (C : TowerCircuit) (hC : ComputesSAT C) :
    k * b ≤ C.gates :=
  R C hC

/-- **The ∀ trick relocates the value, it does not remove it (proved, `Iff.rfl`).**  "No value
needed" is genuine — but the trick's success is *definitionally* the truth of the universal over the
SAT-circuit domain, and that is the **reading**.  The value on SAT is dissolved into the truth of a
universal; that truth — SAT-circuits forbid the Uhlig sharer — is `cost_super`.  Quantifying is free;
the universal's truth is the wall. -/
theorem forall_trick_relocates_not_removes (k b : ℕ) (ComputesSAT : TowerCircuit → Prop) :
    Reading k b ComputesSAT ↔ (∀ C, ComputesSAT C → k * b ≤ C.gates) :=
  Iff.rfl

end PallLean.Paper93.DeepMath.PathB.ForallTrick

#print axioms PallLean.Paper93.DeepMath.PathB.ForallTrick.forall_trick_value_free
#print axioms PallLean.Paper93.DeepMath.PathB.ForallTrick.uhlig_refutes_unrestricted
#print axioms PallLean.Paper93.DeepMath.PathB.ForallTrick.forall_trick_relocates_not_removes
