import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResonance

/-!
# The Ramanujan-expander resonator (p-vs-np1 Route B): the anti-damper, and where it crosses

Darren's move: for the full DAG the resonator works through the **Ramanujan expander** + **amplituhedron
gauge** (the paper's Route B).  The instinct is right about the *mechanism*: an expander is the
**anti-damper**.  Damping is sharing (a small cut between the two copies); an expander has **no small
cut** — high connectivity — so it is exactly the structure that forbids cheap sharing and forces the
amplifier to ring.

Model the expander's connectivity by a **separator measure** `sep` (spectral / cut expansion).  A
**Ramanujan** expander doubles it under composition — the two copies have no shared bottleneck:

`Expanding :  ∀ f, 2·sep f ≤ sep (dbl f)`.

## What is proved

* **`expander_resonates` (proved)** — in a **structural** model (circuit size equals the separator,
  `c f = sep f` — a small circuit implies a small cut, which holds for *restricted* models: branching
  programs, formulas), Ramanujan expansion forces resonance: `2·c f ≤ c (dbl f)`.  The expander's doubling
  cut makes the amplifier ring.
* **`expander_superpoly` (proved)** — hence, via `Resonance.resonance_carries`, the tower is
  superpolynomial: `2^d ≤ c (harmonics dbl base d)`.  The expander resonator works — **in the structural
  model**.

## Where it crosses, and where it doesn't

The expander genuinely supplies the anti-damper (`Expanding`), and in any model where **`c = sep`** —
circuit size is pinned to the cut — the resonator carries SAT to `2^d`.  That is real, and it is why
expanders give lower bounds in restricted models.

For the **full DAG** the structural identity **fails**: a general circuit can be *smaller* than its
separator (`c < sep`) — that is exactly **mass production**, computing the two copies together *below* the
cut bound.  So `c f = sep f` is precisely `cost_super`, and the amplituhedron gauge that would restore it
is the God-Move `Π★`, which **presupposes** the bound (`GaugeCircularity.gauge_presupposes_C3`).  The
expander is the right anti-damper; the missing step is that in the full DAG size is not pinned to the cut,
and pinning it is the wall.

**Honest scope.**  Proved: the Ramanujan-expander resonator carries SAT to superpoly *in a structural
model* (`c = sep`).  The full-DAG version needs `c = sep` (no mass production) = `cost_super`, and the
amplituhedron gauge presupposes it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExpanderResonator

open PallLean.Paper93.DeepMath.PathB.Resonance

/-- **Ramanujan expansion**: the separator (cut) doubles under composition — the two copies have no shared
bottleneck.  This is the anti-damper the expander supplies. -/
def Expanding {Fn : Type} (sep : Fn → ℕ) (dbl : Fn → Fn) : Prop :=
  ∀ f, 2 * sep f ≤ sep (dbl f)

/-- **Structural model**: circuit size equals the separator — a small circuit forces a small cut.  Holds
in restricted models (branching programs, formulas); the full-DAG failure of this is `cost_super`. -/
def Structural {Fn : Type} (c sep : Fn → ℕ) : Prop :=
  ∀ f, c f = sep f

/-- **The expander resonates in a structural model (proved).**  With size pinned to the cut (`c = sep`),
Ramanujan expansion (`sep` doubles) forces the amplifier to ring: `2·c f ≤ c (dbl f)`. -/
theorem expander_resonates {Fn : Type} (c sep : Fn → ℕ) (dbl : Fn → Fn)
    (hStruct : Structural c sep) (hExpand : Expanding sep dbl) (f : Fn) :
    2 * c f ≤ c (dbl f) := by
  rw [hStruct f, hStruct (dbl f)]
  exact hExpand f

/-- **The expander resonator carries SAT to superpoly — in the structural model (proved).**  Expansion +
`c = sep` ⟹ `2^d ≤ c (harmonics dbl base d)`.  The Ramanujan-expander resonator works when size is pinned
to the cut. -/
theorem expander_superpoly {Fn : Type} (c sep : Fn → ℕ) (dbl : Fn → Fn) (base : Fn)
    (hStruct : Structural c sep) (hExpand : Expanding sep dbl) (hbase : 1 ≤ c base) (d : ℕ) :
    2 ^ d ≤ c (harmonics dbl base d) :=
  resonance_carries c dbl base (fun f => expander_resonates c sep dbl hStruct hExpand f) hbase d

end PallLean.Paper93.DeepMath.PathB.ExpanderResonator

#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderResonator.expander_resonates
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderResonator.expander_superpoly
