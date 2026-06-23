import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaAmplify
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaIterate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaIndicator

/-!
# Toda integer-route ladder — machine-checked manifest

A single verified entry point for the Beigel–Tarui **integer** route's core mechanism, built this run as
the genuine attack on the polynomial wall (exact-quasipoly for large/unbounded `MOD`).  All four rungs
are clean and depend on **no `Classical.choice`** (`[propext, Quot.sound]` only) — pure ring/divisibility
and `MvPolynomial` degree facts.

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

## The remaining wall

Supplying `q` as the actual bottom-`AND` count of a depth-`d` ACC⁰ circuit and assembling the per-gate
indicators into **one** exact quasipoly `SYM∘AND` across depth (choosing `2^k` against the global count)
is the Beigel–Tarui integer construction body — Williams-strength, **not** built.  (Unbounded `AND`/`OR`
stays the exact-degree no-go, `ACC0ExactDegreeNoGo`.)  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TodaLadderManifest

#check @ACC0TodaAmplify.todaAmp_amplifies
#check @ACC0TodaIterate.todaAmpIter_amplifies
#check @ACC0TodaDegree.todaAmpIterP_totalDegree_le
#check @ACC0TodaIndicator.todaIterate_indicator

-- Minimal-axiom confirmation (no Classical.choice)
#print axioms ACC0TodaAmplify.todaAmp_amplifies
#print axioms ACC0TodaIterate.todaAmpIter_amplifies
#print axioms ACC0TodaDegree.todaAmpIterP_totalDegree_le
#print axioms ACC0TodaIndicator.todaIterate_indicator

end PallLean.Paper93.DeepMath.PathB.ACC0TodaLadderManifest
