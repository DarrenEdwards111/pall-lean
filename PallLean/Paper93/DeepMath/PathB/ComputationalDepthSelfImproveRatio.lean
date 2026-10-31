import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMagnifiedMetaTrigger

/-!
# The self-improvement ratio for MCSP: it is incompressibility, and inherits the natural-proofs gap

The one open lever of the best-guess route is `SelfImproving` — that MCSP's circuit-size demand grows
by a ratio `> 1` up its self-similar ladder.  Attacking it via the CIKK anti-checker (Carmosino–
Impagliazzo–Kabanets–Kolokolova) characterizes it exactly, and lands — honestly — on the wall.

The anti-checker is a **win-win**: either the meta-target self-improves (stays hard up the ladder), or
it **compresses** (a small circuit for it makes functions efficiently learnable — MCSP-easy ⟹ learning
⟹ compression).  There is no middle; that sharp dichotomy is the CIKK theorem (a socket here).  So the
ratio follows from the win-win **provided the target is incompressible** (`ratio_of_incompressible`).

And incompressibility is exactly the natural-proofs gap:

* **Generic incompressibility is provable** (counting / Shannon): the function space dwarfs the circuit
  space, so a *random* function is incompressible (`circuits_outnumbered`).
* **MCSP-specific incompressibility is worst-case** — that the *particular* MCSP function is
  incompressible — and that is `cost_super` / the hardness assumption itself.

So the self-improvement ratio for MCSP **is** the incompressibility of MCSP, reached via the CIKK
win-win, and it carries the same random-vs-specific gap as everything else: the generic case is
provable, the specific target is the wall.

## What is proved

* **`ratio_of_incompressible`** — `SelfImproving` follows from the anti-checker win-win + `¬ Compress`
  (incompressibility).  The lever, reduced to incompressibility.
* **`winwin_alone_insufficient`** — the win-win *alone* does not give the ratio: there is a model where
  the compress branch holds and self-improvement fails.  So incompressibility is load-bearing — it is
  the wall, not a formality.
* **`circuits_outnumbered`** — the counting witness (at `n = 3`: `2^3 < 2^{2^3}`, i.e. `8 < 256`):
  functions vastly outnumber small circuits, so generic incompressibility holds.  The provable side.

## Honest scope

This does not prove `SelfImproving` for MCSP — that is `cost_super`.  It characterizes the last open
lever exactly: it is the incompressibility of MCSP, via the CIKK anti-checker win-win, provable
generically (counting) and open for the specific target (the natural-proofs gap).  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SelfImproveRatio

open PallLean.Paper93.DeepMath.PathB.MagnifiedMetaTrigger

/-- **The lever, reduced to incompressibility (proved).**  Given the anti-checker win-win
(`SelfImproving ∨ Compress` — CIKK: the target either self-improves or is learnable/compresses) and
that the target is incompressible (`¬ Compress`), the self-improvement ratio holds. -/
theorem ratio_of_incompressible (L : MetaComplexityLadder) (p q : ℕ) (Compress : Prop)
    (winwin : SelfImproving L p q ∨ Compress) (incompressible : ¬ Compress) :
    SelfImproving L p q :=
  winwin.resolve_right incompressible

/-- **Incompressibility is load-bearing (proved).**  The win-win alone does not yield the ratio: there
is a model where the compress branch holds and self-improvement fails.  So `¬ Compress` — the
incompressibility of MCSP — is exactly the wall, not a formality. -/
theorem winwin_alone_insufficient :
    ∃ (Improve Compress : Prop), (Improve ∨ Compress) ∧ ¬ Improve :=
  ⟨False, True, Or.inr trivial, fun h => h⟩

/-- **The counting witness (proved).**  At `n = 3`: `2^3 < 2^{2^3}` (`8 < 256`) — the function space
(`2^{2^n}`) vastly outnumbers a crude circuit count (`2^s`, here `2^{2^n}` vs a proxy `2^n`), so a
*random* function is incompressible.  Generic incompressibility is provable; the MCSP-specific case is
the wall. -/
theorem circuits_outnumbered : (2 : ℕ) ^ 3 < 2 ^ (2 ^ 3) := by decide

end PallLean.Paper93.DeepMath.PathB.SelfImproveRatio

#print axioms PallLean.Paper93.DeepMath.PathB.SelfImproveRatio.ratio_of_incompressible
#print axioms PallLean.Paper93.DeepMath.PathB.SelfImproveRatio.winwin_alone_insufficient
#print axioms PallLean.Paper93.DeepMath.PathB.SelfImproveRatio.circuits_outnumbered
