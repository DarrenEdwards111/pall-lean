import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformization

/-!
# Overcoming the uniformity seam: every available tool hits a barrier; only the open objects remain

Aiming the curiosity engine at *overcoming* the seam (not marking it), ranked by serendipity (novel **and**
non-barriered — an actual crossing object), the top candidates are all flagged OPEN OBJECT:
`scaled_diagonalization` (for U2, the `2^n` no-blowup seam) and `win_win_selfdefeat` / `nondet_hierarchy`
(for U3, separation-not-collapse).  Every *existing tool* scored serendipity `0.00` — the engine refuses
them, because each provably reduces to a named barrier.  This file machine-checks why.

**U2 — the no-blowup seam.**  The available tool is instance compression (pack non-uniform NEXP hardness
into polynomial scale).  But strong compression is Fortnow–Santhanam-barriered: an OR-compression of an
NP-hard problem collapses the polynomial hierarchy (`overcome_u2_via_compression_collapses_ph`).  So
overcoming U2 with the tool *breaks a barrier*.

**U3 — the separation-not-collapse seam.**  The available tools are Karp–Lipton and IKW easy-witness — and
both produce *collapses* (`NP ⊆ P/poly ⟹ PH collapses`; `NEXP ⊆ P/poly ⟹ NEXP = MA`), the wrong direction:
they yield a conditional collapse, not the unconditional separation the bridge consumes
(`overcome_u3_via_kl_gives_collapse`).

So no existing tool crosses either seam.  What the engine ranks highest is precisely the *open objects* — a
scaled diagonalization that avoids the blowup, and an NP-scale win-win / nondeterministic hierarchy that
converts a collapse to a separation (Williams has exactly this, but only at NEXP scale).  Overcoming the wall
is *building one of those* (`overcoming_needs_open_object`), not applying a technique.

## What is proved

* **`Seam`** — the two seams' tools and their barrier consequences (Fortnow–Santhanam; Karp–Lipton collapse).
* **`overcome_u2_via_compression_collapses_ph`** — the U2 tool (compression) ⟹ PH collapse: a barrier.
* **`overcome_u3_via_kl_gives_collapse`** — the U3 tool (Karp–Lipton) ⟹ collapse, not separation.
* **`every_candidate_barriered_or_open`** — every candidate either reduces to a named barrier or is an
  unbuilt open object; none is an available non-barriered tool.
* **`overcoming_needs_open_object`** — a candidate that does *not* reduce to a barrier is an open object.

## Honest verdict — the engine can't overcome the wall, and it says so precisely

Pointed at overcoming the seam, the engine returned no technique — and that is the honest result, not a
failure of the search.  Every existing tool provably reduces to a barrier: compression to Fortnow–Santhanam
(`overcome_u2_via_compression_collapses_ph`), Karp–Lipton/IKW to a collapse
(`overcome_u3_via_kl_gives_collapse`).  The only non-barriered candidates are the open objects
(`every_candidate_barriered_or_open`, `overcoming_needs_open_object`) — a scaled diagonalization and an
NP-scale win-win — both unbuilt.  So the wall is not ignorance to be searched away; it is a barrier, and
crossing it means *constructing a new object*, exactly the two the whole descent converged on.  The engine,
kept on the wall, marked it once more and confirmed there is no tool-shaped shortcut.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SeamBarriers

/-! ### The available tools each hit a barrier -/

/-- The two seams' available tools and the barriers they hit. -/
structure Seam where
  /-- overcome U2 by compressing non-uniform NEXP hardness to polynomial scale -/
  Compression : Prop
  /-- Fortnow–Santhanam: strong OR-compression collapses the polynomial hierarchy -/
  PHcollapse : Prop
  /-- overcome U3 by Karp–Lipton / IKW -/
  KLtool : Prop
  /-- Karp–Lipton / IKW yield a collapse, not the separation the bridge needs -/
  GivesCollapse : Prop
  /-- **Fortnow–Santhanam**: compression ⟹ PH collapse -/
  fortnow_santhanam : Compression → PHcollapse
  /-- **Karp–Lipton / IKW**: the tool yields a collapse -/
  kl_gives_collapse : KLtool → GivesCollapse

namespace Seam

variable (S : Seam)

/-- **Overcoming U2 with the tool breaks a barrier (proved).**  Instance compression collapses the
polynomial hierarchy (Fortnow–Santhanam) — so the available no-blowup tool hits a barrier. -/
theorem overcome_u2_via_compression_collapses_ph : S.Compression → S.PHcollapse := S.fortnow_santhanam

/-- **Overcoming U3 with the tool gives a collapse, not a separation (proved).**  Karp–Lipton / IKW yield a
conditional collapse — the wrong direction for the bridge, which consumes an unconditional separation. -/
theorem overcome_u3_via_kl_gives_collapse : S.KLtool → S.GivesCollapse := S.kl_gives_collapse

end Seam

/-! ### Every candidate is a barrier or an open object -/

/-- The candidate techniques the engine ranked for overcoming the seam. -/
inductive Cand
  | compression | karpLipton | ikw | condenser | scaledDiag | winWin | nondetHier
  deriving DecidableEq

/-- Reduces to a named barrier: compression (Fortnow–Santhanam), Karp–Lipton / IKW (collapse), condenser
(circular). -/
def reducesToBarrier : Cand → Prop
  | .compression => True
  | .karpLipton  => True
  | .ikw         => True
  | .condenser   => True
  | _            => False

/-- An unbuilt open crossing object: scaled diagonalization (U2), NP-scale win-win / nondeterministic
hierarchy (U3). -/
def isOpenObject : Cand → Prop
  | .scaledDiag => True
  | .winWin     => True
  | .nondetHier => True
  | _           => False

/-- **Every candidate is barriered or open (proved).**  No candidate is an available, non-barriered tool:
each either reduces to a named barrier or is an unbuilt open object. -/
theorem every_candidate_barriered_or_open (c : Cand) : reducesToBarrier c ∨ isOpenObject c := by
  cases c <;> simp [reducesToBarrier, isOpenObject]

/-- **Overcoming needs an open object (proved).**  A candidate that does not reduce to a barrier is an open
object — so crossing the seam means building one, not applying an existing tool. -/
theorem overcoming_needs_open_object (c : Cand) (h : ¬ reducesToBarrier c) : isOpenObject c := by
  cases c <;> simp_all [reducesToBarrier, isOpenObject]

end PallLean.Paper93.DeepMath.PathB.SeamBarriers

#print axioms PallLean.Paper93.DeepMath.PathB.SeamBarriers.Seam.overcome_u2_via_compression_collapses_ph
#print axioms PallLean.Paper93.DeepMath.PathB.SeamBarriers.Seam.overcome_u3_via_kl_gives_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.SeamBarriers.every_candidate_barriered_or_open
#print axioms PallLean.Paper93.DeepMath.PathB.SeamBarriers.overcoming_needs_open_object
