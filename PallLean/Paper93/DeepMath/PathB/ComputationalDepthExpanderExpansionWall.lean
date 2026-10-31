import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTeeth

/-!
# Attempting to prove NP expands on the specific expander — and the exact wall

The ask: prove NP *expands* on the specific Ramanujan expander — i.e. the compressor's NP-size exceeds
the wall `s`.  This is `cost_super` / `P ≠ NP`-strength, and it is **not** proved here.  What is done is
the honest attempt: reduce the expansion to the single inequality that blocks it, and show precisely
why the expander's *combinatorial* rigidity (proved) does not force the *computational* expansion.

In the `ExpanderTeeth` model the circuit cost is `cost = cut − compression`, where `cut` is the
expander's rigid separation (Ramanujan ⟹ no small cut, *proved* in `ExpanderResonator`) and
`compression` is how far the circuit dips below it — **mass production**.

## What is proved

* **`expander_expands_iff`** — the expander expands past the wall `s` (`s < cost`) **iff** the
  compression is bounded: `compression + s < cut`.  So NP-expansion on the expander is *exactly* the
  statement that the circuit does not mass-produce below the cut.
* **`mass_production_escapes`** — if the compression is large (`cut ≤ compression + s`, mass
  production), the expander does **not** expand: the circuit compresses the rigid cut away.  A concrete
  escape (`slip_escapes`): a circuit compressing `5` below a cut of `100` fails to expand past `96`,
  even though the combinatorial cut is `100`.

## Honest verdict — why this does not cross

NP-expansion on the specific expander is **equivalent** to `compression + s < cut` — bounded
compression, no mass production.  The expander's `cut` is large and rigid (proved combinatorially).
But a general circuit's `compression` is **not** bounded by that: the cut is a combinatorial quantity,
mass production is a computational one, and nothing in the no-small-cut rigidity forbids a circuit from
compressing below the cut (`mass_production_escapes` exhibits exactly such a circuit).  Forcing
`compression + s < cut` for the specific expander — no mass production — **is** `cost_super`, the
specific incompressibility of NP.  I cannot prove it, and I will not fake it: the combinatorial
rigidity is proved, the computational expansion is the wall, and the gap between them is mass
production = `cost_super`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExpanderExpansionWall

open PallLean.Paper93.DeepMath.PathB.ExpanderTeeth

/-- **The expansion reduces to bounded compression (proved).**  The expander expands past the wall `s`
(`s < cost`) exactly when the compression is bounded below the cut (`compression + s < cut`).  So
"NP expands on the expander" is precisely "the circuit does not mass-produce below the cut". -/
theorem expander_expands_iff (E : ExpanderTeeth) (s : ℕ) :
    s < E.cost ↔ E.compression + s < E.cut := by
  have h := E.slip
  omega

/-- **Mass production escapes the expansion (proved).**  If the compression is large
(`cut ≤ compression + s`), the expander does NOT expand: the circuit compresses the rigid cut away.
This is why the combinatorial cut alone does not force computational expansion. -/
theorem mass_production_escapes (E : ExpanderTeeth) (s : ℕ) (hmass : E.cut ≤ E.compression + s) :
    ¬ (s < E.cost) := by
  have h := E.slip
  omega

/-- **A concrete escape (proved).**  `slipWitness` has `cut = 100` but `cost = 95` (compression `5`);
it fails to expand past the wall `96`, even though the combinatorial cut is `100`.  Mass production
killed the expansion in the window `[cost, cut)`. -/
theorem slip_escapes : ¬ (96 < slipWitness.cost) := by decide

/-- **The wall, named (proved as an iff).**  NP-expansion on the specific expander at wall `s` IS the
bounded-compression / no-mass-production statement `compression + s < cut`.  That statement, for the
specific expander, is `cost_super`; it is not derivable from the (proved) large `cut` alone. -/
theorem expansion_is_no_mass_production (E : ExpanderTeeth) (s : ℕ) :
    s < E.cost ↔ E.compression + s < E.cut :=
  expander_expands_iff E s

end PallLean.Paper93.DeepMath.PathB.ExpanderExpansionWall

#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderExpansionWall.expander_expands_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderExpansionWall.mass_production_escapes
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderExpansionWall.slip_escapes
