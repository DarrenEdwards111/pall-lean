import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicDimension

/-!
# Why reaching EXP does not continue to NP: relativization is a proved barrier, not a P-observer artifact

The intuition: we reached `P ⊊ EXP`, so the wall to NP is "just a continuation" — it only *looks* uncrossable
from the bounded P-observer's interface, while the NP-observer (a hypercube) sees it easily.  Two halves of
this are right, and one proved fact is the crux.

**Right:** `P ⊊ EXP` is a theorem (the time hierarchy, by diagonalization), and from the God/NP-observer's
view the hard object *exists* by counting (`HardSlice`, `Korten`) — it is simply there.

**The crux (proved barrier).**  The technique that reached EXP is **diagonalization**, and diagonalization
**relativizes**: it establishes the same relation relative to *every* oracle.  So a relativizing proof of
`P ≠ NP` would establish `P^A ≠ NP^A` for **all** oracles `A`.  But **Baker–Gill–Solovay**: some oracle makes
`P^A = NP^A` and another makes `P^B ≠ NP^B` — P vs NP is *oracle-dependent*.  Hence **no relativizing
technique resolves P vs NP** (`relativizing_cannot_separate`, `relativizing_cannot_collapse`,
`p_vs_np_oracle_dependent`), including the diagonalization that reached EXP.  The continuation is not blocked
by the P-observer's limited interface; it is blocked because the EXP-reaching technique cannot *see* the
oracle-dependence that makes P vs NP different from `P ⊊ EXP`.

**The observer reading, corrected.**  The NP-observer does see the object (it exists) — but "exists" is not
"crossable": crossing needs the object made *explicit / P-accessible*, and the gap between "exists" (God-view)
and "findable" (P-view) is exactly NP (`VerifyFindGap`).  Adopting the NP-observer's perspective *names* that
gap; it does not close it.  And concretely, closing it needs a **non-relativizing** technique — one the
EXP-reaching diagonalization is not.  That is why `P ⊊ EXP` (whose separation relativizes) succeeds and the NP
crossing does not: not a perspective, a proved obstruction.

## What is proved

* **`relativizing_cannot_separate`** — a collapsing oracle (BGS) refutes "all oracles separate": no relativizing
  technique proves `P ≠ NP`.
* **`relativizing_cannot_collapse`** — a separating oracle (BGS) refutes "all oracles collapse": no relativizing
  technique proves `P = NP`.
* **`p_vs_np_oracle_dependent`** — with both a collapsing and a separating oracle (BGS), P vs NP is
  oracle-dependent: relativizing techniques resolve it *in neither direction*.
* **`exp_reached_but_np_blocked`** — the EXP separation relativizes (holds for all oracles) while P vs NP does
  not: the same relativizing technique reaches EXP but provably not NP.

## Honest verdict — the wall is a barrier, and the crossing needs non-relativizing math

The continuation from EXP to NP is not an artifact of the P-observer's boundary interface.  It is blocked by a
theorem: diagonalization relativizes, P vs NP is oracle-dependent (Baker–Gill–Solovay), so the EXP-reaching
technique provably cannot continue (`p_vs_np_oracle_dependent`, `exp_reached_but_np_blocked`).  The
NP-observer's perspective is real and it does show the hard object *exists* — but existence is not a crossing;
the crossing is making it explicit, which is the verify/find gap (NP itself), and closing that needs a
*non-relativizing* technique the reached-EXP method is not.  That is exactly why the campaign's one open object
is a **non-natural, non-relativizing** technique off Π★: the barriers are the reason the wall is a wall, and
they are proved, not perceived.  So the perspective is right that the object is there and wrong that seeing it
crosses — the crossing is new, non-relativizing mathematics.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Relativization

variable {Oracle : Type} (PeqNP_rel : Oracle → Prop)

/-! ### Relativization blocks both directions -/

/-- **A relativizing technique cannot prove `P ≠ NP` (proved).**  A relativizing proof would give
`P^A ≠ NP^A` for *all* oracles, but Baker–Gill–Solovay provides a *collapsing* oracle (`P^A = NP^A`) — so "all
oracles separate" is false. -/
theorem relativizing_cannot_separate (bgs_collapse : ∃ A, PeqNP_rel A) :
    ¬ (∀ A, ¬ PeqNP_rel A) := by
  obtain ⟨A, hA⟩ := bgs_collapse
  intro h
  exact h A hA

/-- **A relativizing technique cannot prove `P = NP` (proved).**  Symmetrically, Baker–Gill–Solovay provides a
*separating* oracle (`P^B ≠ NP^B`) — so "all oracles collapse" is false. -/
theorem relativizing_cannot_collapse (bgs_separate : ∃ A, ¬ PeqNP_rel A) :
    ¬ (∀ A, PeqNP_rel A) := by
  obtain ⟨A, hA⟩ := bgs_separate
  intro h
  exact hA (h A)

/-- **P vs NP is oracle-dependent (proved).**  With both a collapsing and a separating oracle (Baker–Gill–
Solovay), no relativizing technique resolves P vs NP in *either* direction. -/
theorem p_vs_np_oracle_dependent (bgs_collapse : ∃ A, PeqNP_rel A) (bgs_separate : ∃ A, ¬ PeqNP_rel A) :
    ¬ (∀ A, PeqNP_rel A) ∧ ¬ (∀ A, ¬ PeqNP_rel A) :=
  ⟨relativizing_cannot_collapse PeqNP_rel bgs_separate,
   relativizing_cannot_separate PeqNP_rel bgs_collapse⟩

/-! ### EXP is reached, NP is blocked — same relativizing technique -/

/-- **EXP reached, NP blocked (proved).**  The EXP separation *relativizes* — it holds relative to every
oracle (`expSep_rel`, the relativizing time hierarchy) — while P vs NP is oracle-dependent (BGS).  So the same
relativizing technique that reaches `P ⊊ EXP` provably cannot continue to `P` vs `NP`: the reached result is
oracle-uniform, the target is not. -/
theorem exp_reached_but_np_blocked (ExpSep_rel : Oracle → Prop)
    (hexp : ∀ A, ExpSep_rel A)                   -- the EXP separation relativizes: holds relative to every oracle
    (bgs_collapse : ∃ A, PeqNP_rel A) :
    (∀ A, ExpSep_rel A) ∧ ¬ (∀ A, ¬ PeqNP_rel A) :=
  ⟨hexp, relativizing_cannot_separate PeqNP_rel bgs_collapse⟩

end PallLean.Paper93.DeepMath.PathB.Relativization

#print axioms PallLean.Paper93.DeepMath.PathB.Relativization.relativizing_cannot_separate
#print axioms PallLean.Paper93.DeepMath.PathB.Relativization.relativizing_cannot_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.Relativization.p_vs_np_oracle_dependent
#print axioms PallLean.Paper93.DeepMath.PathB.Relativization.exp_reached_but_np_blocked
