import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TreewidthCount

/-!
# Expander count obstruction — the conjectural bridge: DP-restricted bound proved, the general bound socketed

Entries 251–253 mapped the *tractable* side: disjoint, block-diagonal, and bounded-treewidth incidence ⇒ the
cross-field count factors by a separator DP.  The remaining wall is the *negative* side — **expander / unbounded-
treewidth incidence**.  This file formalizes the conjectural bridge and **sockets the exact lower-bound theorem
clearly**, with the honest split the user flagged: the general lower bound is Smolensky-strength.

The honest decomposition of "expander incidence ⇒ no cheap observer":

* **DP-restricted lower bound (PROVED, trivial by definition).**  A *separator-based* observer's boundary *is* a
  separator of the incidence; on an expander (no small separator) it must therefore be large
  (`dp_observer_needs_large_boundary`).  This is the easy direction — it bounds only observers that work by separator
  DP.
* **General lower bound (SOCKET, Smolensky-strength).**  *Any* observer computing the mod-`q` fire-count — including
  *algebraic / polynomial* ones that do **not** decompose along a separator — needs superpolynomial resources on an
  expander.  The gap between this and the DP-restricted bound is exactly **ruling out the clever algebraic
  shortcuts** — the real content, equivalent in strength to the composite-`ACC⁰` lower bound.

⚠️ **This socket is Smolensky-strength.**  `ExpanderCountObstruction` is a *named conjecture* (a `def`, not a proved
theorem).  Proving it generally would be at the `ACC⁰[composite]` wall.  I prove only the DP-restricted (separator)
bound and state the general one as the socket, honestly.

## What is proved (clean axioms, no `sorry`)

* **`IsSeparator supp S`** — `S` separates the gate–variable incidence: the gates split into two nonempty parts whose
  supports meet only within `S`.
* **`ExpanderIncidence supp k`** — no small separator: every separator has size `≥ k`.
* **`dp_observer_needs_large_boundary`** (PROVED) — a separator-DP observer whose boundary is a separator needs
  boundary `≥ k` on an expander (`hexp boundary hsep`).  The DP-restricted lower bound.

## The conjectural bridge (positive proved elsewhere; negative socketed here)

* **Positive (tractable side, PROVED in 251–253):** bounded separator / treewidth ⇒ the count factors by the DP
  recurrence (`ACC0TreewidthCount.separator_factor`).  Re-exported here as `boundedSeparator_factorizes`.
* **Negative (the wall, SOCKET):** **`ExpanderCountObstruction`** — `ExpanderIncidence supp k → ComputesCrossFieldCount
  obs → k ≤ ObserverBoundarySize obs`, for *arbitrary* observers (the `ComputesCrossFieldCount` predicate is abstract,
  covering algebraic ones).  Not proved; this is the open Smolensky-strength theorem.

## Honest scope

The proved content is the DP-restricted lower bound (separator observers need large boundary on expanders — trivial by
the definition of expander) and the positive tractable side (re-export of 251–253).  The general lower bound — *any*
observer, ruling out algebraic shortcuts — is the named socket `ExpanderCountObstruction`, Smolensky-strength and open.
The honest finding: the DP lower bound is free; the hard part is precisely ruling out non-DP observers.  Next step:
attack special expander families (instantiate `ExpanderIncidence` for concrete graphs).  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExpanderCountObstruction

variable {V Gate : Type} [Fintype Gate] [DecidableEq Gate] [DecidableEq V]

/-- **A separator of the gate–variable incidence.**  `S` separates if the gates split into two nonempty parts `A`, `B`
whose variable supports meet only within `S` (`supp ga ∩ supp gb ⊆ S` across the parts). -/
def IsSeparator (supp : Gate → Finset V) (S : Finset V) : Prop :=
  ∃ A B : Finset Gate, A ∪ B = Finset.univ ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
    ∀ ga ∈ A, ∀ gb ∈ B, supp ga ∩ supp gb ⊆ S

/-- **Expander incidence: no small separator.**  Every separator of the incidence has size `≥ k` (high expansion / no
small cut). -/
def ExpanderIncidence (supp : Gate → Finset V) (k : ℕ) : Prop :=
  ∀ S : Finset V, IsSeparator supp S → k ≤ S.card

/-- The boundary size of an observer = the size of the separator set of variables it conditions on. -/
def ObserverBoundarySize (boundary : Finset V) : ℕ := boundary.card

/-- **The DP-restricted lower bound (PROVED).**  A separator-based observer whose boundary is a separator of the
incidence must, on an expander, have boundary `≥ k` — trivially, since expander means *every* separator has size `≥ k`.
This bounds only separator-DP observers; ruling out non-DP (algebraic) observers is the Smolensky-strength socket
below. -/
theorem dp_observer_needs_large_boundary (supp : Gate → Finset V) (k : ℕ) (boundary : Finset V)
    (hexp : ExpanderIncidence supp k) (hsep : IsSeparator supp boundary) :
    k ≤ ObserverBoundarySize boundary :=
  hexp boundary hsep

/-- **The general lower bound (SOCKET — Smolensky-strength, NOT proved).**  For *any* observer computing the mod-`q`
fire-count (`ComputesCrossFieldCount`, abstract — covering algebraic / polynomial observers that need *not* decompose
along a separator), expander incidence forces boundary `≥ k`.  This is the exact open lower bound: the gap from the
DP-restricted bound is ruling out the clever algebraic shortcuts.  Stated as a named conjecture; proving it generally is
the `ACC⁰[composite]` wall. -/
def ExpanderCountObstruction (supp : Gate → Finset V) (k : ℕ)
    (ComputesCrossFieldCount : Finset V → Prop) : Prop :=
  ExpanderIncidence supp k →
    ∀ boundary : Finset V, ComputesCrossFieldCount boundary → k ≤ ObserverBoundarySize boundary

/-- **The positive (tractable) side of the bridge, re-exported (PROVED in 251–253).**  When the incidence has a small
separator, the cross-field count factors by the separator-conditioning DP recurrence
(`ACC0TreewidthCount.separator_factor`): `#{x : Pₐ ∧ P_b} = ∑ s, #{a : Pₐ(s,a)} · #{b : P_b(s,b)}`.  Bounded
separator/treewidth ⇒ tractable. -/
theorem boundedSeparator_factorizes (S A B : Type) [Fintype S] [Fintype A] [Fintype B]
    (PA : S → A → Bool) (PB : S → B → Bool) :
    (Finset.univ.filter (fun x : S × A × B => PA x.1 x.2.1 ∧ PB x.1 x.2.2)).card
      = ∑ s : S, (Finset.univ.filter (fun a => PA s a)).card
                  * (Finset.univ.filter (fun b => PB s b)).card :=
  ACC0TreewidthCount.separator_factor S A B PA PB

/-!
**The conjectural dichotomy.**  Bounded separator / treewidth ⇒ the count factors (tractable, `boundedSeparator_
factorizes`, entries 251–253).  Expander incidence (no small separator) ⇒ no cheap observer: the DP-restricted version
is `dp_observer_needs_large_boundary` (proved, trivial); the *general* version `ExpanderCountObstruction` (any observer,
including algebraic) is the open Smolensky-strength socket.  Next: instantiate `ExpanderIncidence` for special expander
families and attempt the general bound there.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ExpanderCountObstruction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExpanderCountObstruction.dp_observer_needs_large_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExpanderCountObstruction.boundedSeparator_factorizes
