import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformityGapNamed
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIndirectDiagonalization

/-!
# The magnification/uniform braid: where a new dent cashes out at `P ≠ NP` scale

The two threads built earlier in this arc are braided here into a single machine-checked
assembly:

* **Route 4 (magnification)** — the lever: an `n^{1+ε}` lower bound for a SPARSE compression
  problem (gap-MCSP-like), in a uniform small-space model, amplifies to the full separation.
  The lever is a published theorem family (McKay–Murray–Williams; Oliveira–Pich–Santhanam) —
  here a named socket (`trigger`), formalization labor, NOT open mathematics.
* **The uniform engine** (`IndirectDiagonalization`) — the only machinery that has ever produced
  unconditional SAT-adjacent lower bounds: alternation trading refutes uniform small-space
  simulations up to exponent `√2` (`lipton_viglas_engine`, PROVED, four literature-standard
  ingredient sockets).

## What is proved

* **`braid_fires`** — the assembly: trigger + dent ⟹ `SAT ∉ P`.  All glue proved; the dent
  (the sparse problem has no uniform small-space `n^{p/q}` algorithm) is the braid's ONE open
  input.
* **`windows_overlap`** — THE quantitative heart, and the reason this braid is the live route:
  magnification demands a ratio `p/q > 1`; the engine refutes ratios `p/q < √2`
  (`p·p < 2·q·q`).  The demand window and the supply window INTERSECT — witnessed at `4/3`.
  No other route in the corpus has this property: everywhere else the demanded strength
  (superpolynomial) exceeds what any known engine supplies; here the demanded exponent sits
  strictly inside the supplied range.
* **`braid_from_engine`** — the engine route to the dent, assembled end-to-end: the four
  `TradingWorld` ingredients + the trigger + a completeness packaging for the sparse problem
  ⟹ `SAT ∉ P`, at any ratio in the window (`braid_at_four_thirds` instantiates `4/3`).

## Honest anatomy — exactly where this stands

`P ≠ NP` is here factored into named layers with STATUS LABELS:

1. `trigger` — published magnification theorem: formalization labor.
2. The four `TradingWorld` fields (padding, speedup, slowdown, hierarchy) — published
   theorems: formalization labor.
3. `dent` — the sparse problem's uniform `n^{1+ε}` lower bound: THE OPEN FRONTIER.  The known
   unconditional bounds of this exact shape exist for SAT (via completeness); moving them to
   the sparse target is the McKay–Murray–Williams "one inch".
4. `completeness` (only on the engine route) — the packaging "sparse easy ⟹ all of NTIME(n^q)
   easy".  For SAT this is Cook–Levin (literature); for sparse compression problems it is
   OPEN and DUBIOUS (MCSP-hardness-flavored: sparse targets are not known NP-hard under the
   needed reductions, and may not be).  This is flagged, not hidden: the engine route to the
   dent needs it; a DIRECT proof of the dent (new trading scheme aimed at the sparse problem
   itself) would not.

So: everything that can be glued is glued and proved; the braid's open core is a SINGLE
`n^{1+ε}`-strength uniform statement sitting inside the engine's reach window — the minimal
dent anywhere in the corpus that still cashes out at full scale.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MagnificationBraid

open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization

/-- **The braid**: a sparse magnifiable target, a uniform world, a dent ratio `p/q`, and the
magnification trigger.  `hpq : q < p` is the `ε > 0` — the demanded ratio is strictly
super-linear. -/
structure Braid where
  /-- the sparse (magnifiable) compression problem — gap-MCSP-like -/
  sparse : Lang
  /-- the uniform world (classes + the four trading ingredients) -/
  W : TradingWorld
  /-- dent ratio numerator -/
  p : ℕ
  /-- dent ratio denominator -/
  q : ℕ
  /-- positive scale -/
  hq : 1 ≤ q
  /-- the ratio is strictly super-linear: this is the `ε` of `n^{1+ε}` -/
  hpq : q < p
  /-- **THE TRIGGER (named socket — published magnification theorem, formalization labor).**
  If the sparse problem has no uniform small-space `n^{p/q}` algorithm, the separation
  follows. -/
  trigger : ¬ W.DTS p sparse → SAT_not_in_P

/-- **The assembly (proved).**  Trigger + dent ⟹ `SAT ∉ P`.  The dent is the braid's one open
input. -/
theorem braid_fires (B : Braid) (dent : ¬ B.W.DTS B.p B.sparse) : SAT_not_in_P :=
  B.trigger dent

/-- **The windows overlap (proved) — the braid's reason to exist.**  Magnification demands
`q < p` (super-linear); the engine refutes `p·p < 2·q·q` (below `√2`).  Both at once is
satisfiable — witnessed at `4/3`.  The demanded exponent sits strictly INSIDE the supplied
range: the only place in the corpus where demand does not exceed known supply. -/
theorem windows_overlap : ∃ p q : ℕ, 1 ≤ q ∧ q < p ∧ p * p < 2 * (q * q) :=
  ⟨4, 3, by omega, by omega, by omega⟩

/-- **The engine route to the dent, end-to-end (proved).**  If additionally the sparse problem
carries the completeness packaging (OPEN and flagged: MCSP-hardness-flavored), the four trading
ingredients produce the dent inside the window, and the braid fires. -/
theorem braid_from_engine (B : Braid) (hwin : B.p * B.p < 2 * (B.q * B.q))
    (completeness : B.W.DTS B.p B.sparse → ∀ L, B.W.NTIME B.q L → B.W.DTS B.p L) :
    SAT_not_in_P :=
  B.trigger (sat_time_space_reading B.W B.sparse B.p B.q B.hq (Nat.le_of_lt B.hpq)
    hwin completeness)

/-- The `4/3` instantiation: a braid at the witnessed window point needs ONLY its sockets —
the window arithmetic is discharged. -/
theorem braid_at_four_thirds (sparse : Lang) (W : TradingWorld)
    (trigger : ¬ W.DTS 4 sparse → SAT_not_in_P)
    (completeness : W.DTS 4 sparse → ∀ L, W.NTIME 3 L → W.DTS 4 L) :
    SAT_not_in_P :=
  braid_from_engine
    { sparse := sparse, W := W, p := 4, q := 3
      hq := by omega, hpq := by omega, trigger := trigger }
    (by show 4 * 4 < 2 * (3 * 3); omega) completeness

end PallLean.Paper93.DeepMath.PathB.MagnificationBraid

#print axioms PallLean.Paper93.DeepMath.PathB.MagnificationBraid.braid_fires
#print axioms PallLean.Paper93.DeepMath.PathB.MagnificationBraid.windows_overlap
#print axioms PallLean.Paper93.DeepMath.PathB.MagnificationBraid.braid_from_engine
#print axioms PallLean.Paper93.DeepMath.PathB.MagnificationBraid.braid_at_four_thirds
