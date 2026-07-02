import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWPatch

/-!
# Socket-2 (IKW): predictor cheapness — each other coordinate is a small junta

The NW predictor hard-wires the *other* output coordinates while varying the target coordinate's `q` seed bits.  Rung 5
showed each other coordinate reads only the overlap (`< k` bits) of the varying part.  This file quantifies the resulting
*cheapness*: as a function of the `q` varying bits, each other coordinate is a **junta on `< k` bits**, so it takes fewer
than `2^k` distinct configurations — while the target genuinely reads all `q` bits.

  `nwGen_other_config_lt` — **PROVED**: for distinct degree-`<k` polynomials, the number of overlap configurations bounding
        an other coordinate's dependence is `2^{|overlap|} < 2^k`.
  `nwGen_other_is_junta` — **PROVED**: the map `w ↦ nwGen f (patchSet z w p) p'` is a junta — it depends on `w` only through
        the `< k` overlap coordinates (a restatement of rung 5's `nwGen_patch_other`, packaged as the predictor's
        junta hypothesis).

So each of the `q^k` other coordinates is a `<k`-junta of the target's `q` seed bits — describable by `< 2^k` bits —
whereas the target output is `f` on all `q` bits: the size asymmetry the predictor turns into a small circuit for `f`.

## Honest scope — the cheapness bound, not the predictor's circuit

This bounds each other coordinate's configuration count (`< 2^k`) and packages the junta hypothesis — the *quantitative*
substrate of "the other coordinates are cheap to hard-wire".  It does **not** build the predictor as an actual small
circuit (which needs a circuit model and the `< 2^k`-table realisation), nor the probabilistic hybrid step, nor the IKW
collapse.  Those are the deep `NEXP`-strength content of socket 2, not established here.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NWDesign

open Polynomial

variable {q : ℕ} [Fact q.Prime]

/-- **Other-coordinate configuration bound (proved)**: an other coordinate depends on the target's `q` bits through only
the `< k` overlap, so its configuration count is `2^{|overlap|} < 2^k`. -/
theorem nwGen_other_config_lt (p p' : (ZMod q)[X]) (hne : p ≠ p') (k : ℕ)
    (hp : p.natDegree < k) (hp' : p'.natDegree < k) :
    2 ^ (nwSet p ∩ nwSet p').card < 2 ^ k :=
  Nat.pow_lt_pow_right (by norm_num) (nwSet_inter_lt p p' hne k hp hp')

/-- **Each other coordinate is a junta (proved)**: `w ↦ nwGen f (patchSet z w p) p'` depends on `w` only through the
overlap `nwSet p ∩ nwSet p'` — the junta hypothesis the predictor consumes. -/
theorem nwGen_other_is_junta (f : (ZMod q → Bool) → Bool) (z : ZMod q × ZMod q → Bool)
    (p p' : (ZMod q)[X]) (w w' : ZMod q × ZMod q → Bool)
    (h : ∀ x ∈ nwSet p ∩ nwSet p', w x = w' x) :
    nwGen f (patchSet z w p) p' = nwGen f (patchSet z w' p) p' :=
  nwGen_patch_other f z w w' p p' h

end PallLean.Paper93.DeepMath.PathB.NWDesign

#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwGen_other_config_lt
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwGen_other_is_junta
