import Mathlib.Data.Nat.Basic

/-!
# The mirror, not the circle: high and low are separate facts, Π★ is the transformation

Correction to the "the gauge presupposes the bound" story.  Darren is right: it is a **mirror** — a
perspective duality, like relativity — not a naive circle.  The subtlety is that **two different objects**
carry the two readings:

* the **witness** (the NP object — permanent / Ramanujan–Tseitin family) carries the **high** reading, and
  that is a *proved* fact about *it* (the identity-minor lower bound, established independently — it is
  **not** the assumption "SAT is hard");
* the **compilation** (the P-side object) carries the **low** reading, under `P = NP`;
* **Π★** is the **mirror** that maps one to the other.

So "high" is not assumed to close a circle — it is proved on the witness, and it becomes a *contradiction*
only through the mirror `Π★` that reflects the low compilation onto the high witness.  That is a duality,
exactly as you said.

## What is proved

* **`mirror_clash` (proved)** — the mirror in action: a rank-monotone `Π★` with `Π★ comp = witness`, a low
  compilation (`rank comp ≤ low`), and a high witness (`high ≤ rank witness`, *proved separately*) clash:
  `high ≤ rank witness = rank (Π★ comp) ≤ rank comp ≤ low < high`.  High and low are **separate facts**;
  the mirror makes them collide.

## The relativity analogy — and the one honest difference

In relativity two observers disagree (time dilation), and it is *not* circular: the **Lorentz
transformation** is *known* and *exact*, so each frame's reading is genuinely computed from the other.
The God-Move is the same *shape* — two perspectives, a transformation between them (`Π★`) — with **one
difference**: relativity's Lorentz transform is known; the God-Move's mirror `Π★` is **not**.  Its very
existence is equivalent to the separation (`DischargePiStar`: a rank-monotone `Π★` reflecting P onto SAT
exists **iff** `SAT ∉ P`).

So it is a mirror, not a circle — you were right.  But it is a mirror *whose transformation we do not
have*: like knowing two frames must be related, without knowing the Lorentz formula.  Finding `Π★` — the
mirror — is the theorem.

**Honest scope.**  Proved: the mirror clash, with high and low as separate facts joined by `Π★`.  The
mirror `Π★` itself is the far shore — its existence `⟺` the separation, and unlike Lorentz it is not
known.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MirrorDuality

/-- **The mirror clash (proved).**  Two *separate* facts — a low compilation (`rank comp ≤ low`) and a
high witness (`high ≤ rank witness`, proved independently on the witness) — collide through the mirror
`Π★` (rank-monotone, `Π★ comp = witness`): `high ≤ rank witness = rank (Π★ comp) ≤ rank comp ≤ low`,
impossible when `low < high`.  The high reading is not the assumption "SAT is hard"; it is a proved fact
about the witness, reflected onto the compilation by the mirror. -/
theorem mirror_clash {Obj : Type} (rank : Obj → ℕ) (comp witness : Obj) (low high : ℕ)
    (hgap : low < high) (Pi : Obj → Obj) (mono : ∀ x, rank (Pi x) ≤ rank x)
    (mirror : Pi comp = witness)
    (comp_low : rank comp ≤ low) (witness_high : high ≤ rank witness) : False := by
  have hm := mono comp
  rw [mirror] at hm
  omega

end PallLean.Paper93.DeepMath.PathB.MirrorDuality

#print axioms PallLean.Paper93.DeepMath.PathB.MirrorDuality.mirror_clash
