import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaAmplify
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaIterate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaIndicator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaModGate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaModCompose
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaExtract
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaDepth2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaTower
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaTowerDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MixedTowerDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MixedTowerValue
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OrNode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerValue
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerExtract
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerBool
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerSparse

/-!
# Toda integer-route ladder — machine-checked manifest

A single verified entry point for the Beigel–Tarui **integer** route's core mechanism, built this run as
the genuine attack on the polynomial wall (exact-quasipoly for large/unbounded `MOD`).  All 17 rungs are
clean; the ladder rungs (1–4) depend on **no `Classical.choice`** (`[propext, Quot.sound]` only) — pure
ring/divisibility and `MvPolynomial` degree facts.

## The ladder (4 rungs)

1. **Amplification core** — `todaAmp_amplifies`: `A(y) = 3y²−2y³` maps `y ≡ b (mod m)` to `≡ b (mod m²)`
   for `b ∈ {0,1}` (modulus doubling).
2. **Iterated modulus** — `todaAmpIter_amplifies`: `A^{[k]}` preserves a `{0,1}` residue up to modulus
   `m^{2^k}`.
3. **Iterated degree** — `todaAmpIterP_totalDegree_le`: the polynomial iterate has
   `totalDegree (A^{[k]} q) ≤ 3^k · deg q`.
4. **The indicator (glue)** — `todaIterate_indicator`: from a degree-`d` mod-`p` `{0,1}` start `q`,
   `A^{[k]} q` is a degree-`≤ 3^k·d` polynomial with values `≡ b (mod p^{2^k})`.

So a `MOD_p` gate (`d = 1`) gets a degree-`3^k` polynomial computing its `{0,1}` value mod `p^{2^k}`;
with `2^k` past the fan-in and `k ≈ log log` this is the **exact, polylog-degree** representation of an
**unbounded-fan-in `MOD`** gate — modulus exponential-in-`k`, degree only `3^k`.

## The across-depth assembly (5 rungs — all-`MOD` tower, value-level)

5. **Single `MOD_p` gate** — `todaMod_amplifies`: the gate's value `≡ [p ∣ y] (mod p^{2^k})` via the
   Fermat lift `1 − y^{p−1}` fed through `A^{[k]}`.
6. **`MOD_p` over a rep layer** — `todaMod_compose`: the accepting count transfers from reps to values
   (`p ∣ ∑ g ↔ p ∣ ∑ b`).
7. **Exact extraction** — `todaMod_extract`: over the common modulus `ZMod (p^{2^k})` (uniform `k`), the
   rep **is** the gate's exact `{0,1}` output.
8. **Two-layer stack** — `toda_depth2`: `MOD_p∘MOD_p` composes (inner `mod p^{2^k}` weakens to `mod p`).
9. **Depth-`d` tower (value)** — `toda_tower`: for *every* `ModTower`, `p^{2^k} ∣ (rep t − val t)` — the
   all-`MOD` tower is Toda-represented at **arbitrary depth** with a uniform `k`.
10. **Depth-`d` tower (degree)** — `prep_totalDegree_le`: `deg(prep t) ≤ (3^k(p−1))^(pdepth t)` —
    polylog degree (`k ≈ log log`, constant depth) for the polynomial tower with degree-≤1 leaves.

So the ACC⁰[p] **`MOD`-skeleton** is fully Toda-represented across unbounded depth, bounded in **both**
value (exact mod `p^{2^k}`) and degree (`(3^k(p−1))^depth`).

11. **Mixed `MOD`/`AND` tower (degree)** — `mrep_totalDegree_le`: degree `≤ (max w (3^k(p−1)))^depth` for
    `MOD` (Toda, *any* modulus) + bounded-fan-in `AND` — the realistic ACC⁰[p], strictly more than
    `ExactBoundedAndOr` (which caps the `MOD` modulus).
12. **Mixed `MOD`/`AND` tower (value)** — `mixed_tower`: `p^{2^k} ∣ (mrepv t − mval t)` — the mixed tower's
    representation equals its Boolean value mod `p^{2^k}` (`MOD` via Toda, `AND` via the product
    congruence).  So the mixed tower is bounded in **both** value and degree.
13. **`OR`-gate laws** — `or_node_dvd` (value congruence) and `or_node_deg` (degree `≤ ∑`): the De Morgan
    gate `1 − ∏(1 − ·)`, generic, joining `MOD`/`AND` so every ACC⁰[p] gate has an integer-route law.
14. **Full `MOD`/`AND`/`OR` tower** — `frep_totalDegree_le` (degree `≤ (max w (3^k(p−1)))^depth`) and
    `full_tower` (value `p^{2^k} ∣ (vrep t − vval t)`): the complete gate set in **one** tower, bounded in
    **both** value and degree across arbitrary depth — the realistic ACC⁰[p] via the integer route.

## The `SYM∘AND` structure (3 rungs — the cash-out's representation half)

15. **Exact extraction** — `full_tower_extract`: `(vrep t : ZMod (p^{2^k})) = (vval t : ZMod (p^{2^k}))` —
    over the common modulus the rep **is** the value (no residual error).
16. **Boolean value** — `vval_mem_bool`: `vval t ∈ {0,1}` — so the extraction is an exact *Boolean* value.
17. **`SYM∘AND` width** — `full_tower_sparse`: `≤ (n+1)^{K^depth}` distinct monomial-`AND` sets.

So the full tower's polynomial is a **degree-`K^depth`, `(n+1)^{K^depth}`-sparse polynomial over
`ZMod (p^{2^k})` computing the circuit's exact Boolean output** — a quasipoly `SYM∘AND` for polylog `K`,
constant depth.  (NB: the Toda rep is a *large* integer; only its residue mod `p^{2^k}` is Boolean — the
cash-out is the `SYM∘AND` structure, not integer smallness.)

## The remaining wall

The full `MOD`/`AND`/`OR` tower's *representation* **and** its `SYM∘AND` *structure* (degree `K^depth`,
width `(n+1)^{K^depth}`, exact Boolean value over `ZMod (p^{2^k})`) are now complete.  The remaining
Beigel–Tarui cash-out is: the **`2^k`-vs-global-count choice** (so the `ZMod (p^{2^k})` readout is the
*whole* circuit's exact output) and the **`NEXP ⊄ ACC⁰`** contradiction (Williams diagonalization — the
algorithmic half).  Williams-strength, **not** built.  (Unbounded `AND`/`OR` stays the exact-degree no-go,
`ACC0ExactDegreeNoGo` — needs RS approximation.)  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaLadderManifest

#check @ACC0TodaAmplify.todaAmp_amplifies
#check @ACC0TodaIterate.todaAmpIter_amplifies
#check @ACC0TodaDegree.todaAmpIterP_totalDegree_le
#check @ACC0TodaIndicator.todaIterate_indicator

-- Across-depth assembly (5 rungs)
#check @ACC0TodaModGate.todaMod_amplifies
#check @ACC0TodaModCompose.todaMod_compose
#check @ACC0TodaExtract.todaMod_extract
#check @ACC0TodaDepth2.toda_depth2
#check @ACC0TodaTower.toda_tower
#check @ACC0TodaTowerDegree.prep_totalDegree_le
#check @ACC0MixedTowerDegree.mrep_totalDegree_le
#check @ACC0MixedTowerValue.mixed_tower
#check @ACC0OrNode.or_node_dvd
#check @ACC0OrNode.or_node_deg
#check @ACC0FullTowerDegree.frep_totalDegree_le
#check @ACC0FullTowerValue.full_tower
#check @ACC0FullTowerExtract.full_tower_extract
#check @ACC0FullTowerBool.vval_mem_bool
#check @ACC0FullTowerSparse.full_tower_sparse

-- Minimal-axiom confirmation (no Classical.choice on the ladder rungs)
#print axioms ACC0TodaAmplify.todaAmp_amplifies
#print axioms ACC0TodaIterate.todaAmpIter_amplifies
#print axioms ACC0TodaDegree.todaAmpIterP_totalDegree_le
#print axioms ACC0TodaIndicator.todaIterate_indicator
#print axioms ACC0TodaTower.toda_tower
#print axioms ACC0TodaTowerDegree.prep_totalDegree_le
#print axioms ACC0MixedTowerDegree.mrep_totalDegree_le
#print axioms ACC0MixedTowerValue.mixed_tower
#print axioms ACC0FullTowerDegree.frep_totalDegree_le
#print axioms ACC0FullTowerValue.full_tower
#print axioms ACC0FullTowerExtract.full_tower_extract
#print axioms ACC0FullTowerBool.vval_mem_bool
#print axioms ACC0FullTowerSparse.full_tower_sparse

end PallLean.Paper93.DeepMath.PathB.ACC0TodaLadderManifest
