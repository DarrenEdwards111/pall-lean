import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWGenerator

/-!
# Socket-2 (IKW): the hybrid-argument locality of the Nisan–Wigderson generator

Rung 2 gave the generator and its locality (output at `p` reads only `nwSet p`).  The Nisan–Wigderson *hybrid argument*
needs one more structural fact — the **cross-coordinate locality**: when we vary the seed only on the design set `nwSet p`
of one target coordinate `p` (fixing the seed elsewhere), any *other* output coordinate `p'` depends on only the
**overlap** `nwSet p ∩ nwSet p'`, which the design keeps to `< k` points.  So each other output bit is a function of
`< k` of the target's `q` seed bits — the read-`<k` structure that lets a distinguisher be converted into a small
predictor for the hard function.

  `nwGen_dep_overlap` — **PROVED**: if `z, z'` agree *outside* `nwSet p` **and** on the overlap `nwSet p ∩ nwSet p'`, then
        `nwGen f z p' = nwGen f z' p'` — output `p'` depends on the `nwSet p` seed bits only through the overlap.
  `nwGen_overlap_lt` — **PROVED**: for distinct `p ≠ p'` of degree `< k`, that overlap has `< k` points — so, with the
        seed fixed outside `nwSet p`, output `p'` is a function of `< k` bits of `nwSet p`.

## Honest scope — the hybrid's locality, not the hybrid

This is the combinatorial engine of the NW hybrid argument: varying the target coordinate's `q` seed bits, every other
output coordinate reads only `< k` of them.  What it does **not** do: the **hybrid / next-bit-predictor argument** itself —
that a circuit distinguishing the generator's output from uniform yields, at some hybrid, a small circuit predicting the
hard function `f` (using this read-`<k` structure to hard-wire the other coordinates), contradicting `f`'s hardness; and
the IKW easy-witness collapse built on it.  Those are the deep `NEXP`-strength content of socket 2, not established here.
This file supplies the read-`<k` cross-coordinate structure.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NWDesign

open Polynomial Finset

variable {q : ℕ} [Fact q.Prime]

/-- **Cross-coordinate locality (proved)**: with the seed fixed outside `nwSet p`, output coordinate `p'` depends on the
`nwSet p` seed bits only through the overlap `nwSet p ∩ nwSet p'`. -/
theorem nwGen_dep_overlap (f : (ZMod q → Bool) → Bool) (z z' : ZMod q × ZMod q → Bool)
    (p p' : (ZMod q)[X]) (hout : ∀ x, x ∉ nwSet p → z x = z' x)
    (hover : ∀ x ∈ nwSet p ∩ nwSet p', z x = z' x) :
    nwGen f z p' = nwGen f z' p' := by
  rw [nwGen, nwGen]
  congr 1
  funext a
  by_cases hx : (a, p'.eval a) ∈ nwSet p
  · exact hover (a, p'.eval a) (Finset.mem_inter.mpr ⟨hx, mem_nwSet.mpr rfl⟩)
  · exact hout (a, p'.eval a) hx

/-- **The overlap is `< k` (proved)**: for distinct degree-`<k` polynomials, output `p'` reads `< k` of the `nwSet p`
seed bits — the design's near-disjointness applied to the hybrid. -/
theorem nwGen_overlap_lt (p p' : (ZMod q)[X]) (hne : p ≠ p') (k : ℕ)
    (hp : p.natDegree < k) (hp' : p'.natDegree < k) :
    (nwSet p ∩ nwSet p').card < k :=
  nwSet_inter_lt p p' hne k hp hp'

end PallLean.Paper93.DeepMath.PathB.NWDesign

#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwGen_dep_overlap
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwGen_overlap_lt
