import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicDimension

/-!
# The observer interfaces are real — but "different interface ⟹ different power" is an invalid inference

The refined intuition: P vs NP *is* the difference between two observers' perceptual interfaces — the
P-observer (verify/check) and the NP-observer (find/guess).  They see different things, "therefore they are not
the same, not in reach, therefore incompressible."  The interface difference is real and formalized
(`VerifyFindGap`).  But the inference in the middle — *different interface, therefore different power* — is
**invalid**, and this file machine-checks why.

**The gap.**  "The two interfaces are different operations" (guessing ≠ checking) is *true*.  "The two
interfaces have different power" (find is harder than verify) *is* P ≠ NP — the open question.  The step from
the first to the second is not valid: **two different interfaces can compute the exact same class.**

**The witness (real, not hypothetical).**  Nondeterministic finite automata (the guess interface) and
deterministic finite automata (the check interface) are genuinely different operations — yet by the subset
construction they recognize the *same* class, the regular languages.  `NFA = DFA`.  So "different observer
interface" provably does *not* imply "different power".  P vs NP asks whether the polynomial-time analogue
behaves like the finite-automata case (*collapse*, `P = NP`) or not (`P ≠ NP`) — and the interface difference,
being present in *both* worlds, cannot decide it.

## What is proved

* **`interfaces_differ_with_collapse`** — a consistent world where the interfaces are different operations yet
  decide the same class (the `NFA = DFA` analogue: `P = NP`).
* **`interfaces_differ_with_separation`** — a consistent world where they differ *and* decide different
  classes (`P ≠ NP`).
* **`interface_difference_undecides`** — the inference "procedures differ ⟹ different class" is false: the
  collapse world refutes it.
* **`p_vs_np_is_whether_interfaces_collapse`** — the interface difference holds in both worlds; P vs NP is
  exactly *which* one — not settled by the difference.

## Honest verdict — the interfaces name the question; they do not decide it

The observer framing is genuine and it is formalized — the P-observer and NP-observer really do have different
interfaces (`VerifyFindGap`).  What is *not* valid is concluding `P ≠ NP` from that difference.  Different
interfaces can compute the same class — `NFA = DFA` proves it in a real setting — so "they see different
things" (`proceduresDiffer`) is consistent with *both* `P = NP` (`interfaces_differ_with_collapse`) and
`P ≠ NP` (`interfaces_differ_with_separation`), and therefore decides neither
(`interface_difference_undecides`).  The interface difference *names* the two sides of P vs NP; whether the
find-interface is genuinely more powerful than the verify-interface — whether the difference is real or, like
`NFA/DFA`, collapses — is precisely the open theorem.  So the intuition is right that the observers differ and
wrong that the difference is a proof: "incompressible" would be the *conclusion* that the interfaces do not
collapse, not a consequence of their being different.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.InterfaceGap

/-- A world assigning: whether the guess-interface and check-interface are different *operations*, and whether
they nonetheless decide the same *class*. -/
structure World where
  /-- the guess (NP) and check (P) interfaces are different operations/procedures -/
  proceduresDiffer : Prop
  /-- the two interfaces decide the same class (`P = NP`) -/
  sameClass : Prop

/-- The collapse world: different procedures, same class — the `NFA = DFA` analogue (`P = NP`). -/
def collapseWorld : World := ⟨True, True⟩

/-- The separation world: different procedures, different classes (`P ≠ NP`). -/
def separateWorld : World := ⟨True, False⟩

/-- **Different interfaces, same class is consistent (proved).**  A world has the interfaces as different
operations yet deciding the same class — exactly `NFA = DFA` (different interface, one class): `P = NP`. -/
theorem interfaces_differ_with_collapse :
    ∃ W : World, W.proceduresDiffer ∧ W.sameClass :=
  ⟨collapseWorld, trivial, trivial⟩

/-- **Different interfaces, different class is consistent (proved).**  A world has the interfaces different
and deciding different classes: `P ≠ NP`. -/
theorem interfaces_differ_with_separation :
    ∃ W : World, W.proceduresDiffer ∧ ¬ W.sameClass :=
  ⟨separateWorld, trivial, not_false⟩

/-- **The interface difference does not decide the question (proved).**  The inference "the procedures differ,
therefore they decide different classes" is *false* — the collapse world (`NFA = DFA` analogue) has different
procedures deciding the same class. -/
theorem interface_difference_undecides :
    ¬ (∀ W : World, W.proceduresDiffer → ¬ W.sameClass) := by
  intro h
  exact h collapseWorld trivial trivial

/-- **P vs NP is which world we are in (proved).**  Both worlds have the interfaces differing; P vs NP is
exactly whether they collapse (same class) or not — a question the interface difference is present in both
sides of, hence cannot settle. -/
theorem p_vs_np_is_whether_interfaces_collapse :
    (∃ W : World, W.proceduresDiffer ∧ W.sameClass) ∧
      (∃ W : World, W.proceduresDiffer ∧ ¬ W.sameClass) :=
  ⟨interfaces_differ_with_collapse, interfaces_differ_with_separation⟩

end PallLean.Paper93.DeepMath.PathB.InterfaceGap

#print axioms PallLean.Paper93.DeepMath.PathB.InterfaceGap.interfaces_differ_with_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.InterfaceGap.interfaces_differ_with_separation
#print axioms PallLean.Paper93.DeepMath.PathB.InterfaceGap.interface_difference_undecides
#print axioms PallLean.Paper93.DeepMath.PathB.InterfaceGap.p_vs_np_is_whether_interfaces_collapse
