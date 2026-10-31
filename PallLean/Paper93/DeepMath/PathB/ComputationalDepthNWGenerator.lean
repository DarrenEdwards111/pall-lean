import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWDesign

/-!
# Socket-2 (IKW): the Nisan–Wigderson generator and its locality

Rung 1 built the NW design (near-disjoint sets `nwSet p`).  This file builds the **generator** on top of it: given a
*hard function* `f` on `q` bits, the NW generator maps a seed `z ∈ {0,1}^{q²}` (one bit per universe point `F_q × F_q`)
to an output bit for each degree-`<k` polynomial `p`, namely `f` evaluated on the `q` seed bits indexed by the design set
`nwSet p`.

  `nwRestrict z p` — the `q`-bit restriction of the seed to `p`'s design set: `a ↦ z (a, p(a))`.
  `nwGen f z p` — the generator's output at coordinate `p`: `f` applied to that restriction.
  `nwRestrict_eq_of_agree` / `nwGen_local` — **PROVED, locality**: the output at `p` depends **only** on the seed's values
        on `nwSet p` — the read-once-via-design structure that drives the NW hybrid argument.

Combined with the design (rung 1): the generator stretches `q²` seed bits to one output per degree-`<k` polynomial
(`q^k` of them), each output bit reading a *different* `q`-subset of the seed with pairwise overlaps `< k`.

## Honest scope — the generator and its locality, not the pseudorandomness

This supplies the NW generator map and its locality — the structural facts the analysis rests on.  What it does **not**
do: the **hybrid argument** proving that when `f` is hard for small circuits, the generator's output fools small circuits
(the actual pseudorandomness), and the IKW easy-witness collapse that consumes it.  Those are the deep `NEXP`-strength
content of socket 2, not established here.  This file supplies the generator and its read-once structure.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NWDesign

open Polynomial

variable {q : ℕ} [Fact q.Prime]

/-- The `q`-bit restriction of a seed `z` to the design set of `p`: `a ↦ z (a, p(a))`. -/
def nwRestrict (z : ZMod q × ZMod q → Bool) (p : (ZMod q)[X]) : ZMod q → Bool :=
  fun a => z (a, p.eval a)

/-- **The restriction depends only on the design set (proved)**: if `z, z'` agree on `nwSet p`, their restrictions to
`p`'s design set are equal. -/
theorem nwRestrict_eq_of_agree (z z' : ZMod q × ZMod q → Bool) (p : (ZMod q)[X])
    (h : ∀ x ∈ nwSet p, z x = z' x) : nwRestrict z p = nwRestrict z' p := by
  funext a
  exact h (a, p.eval a) (mem_nwSet.mpr rfl)

/-- The Nisan–Wigderson generator's output at coordinate `p`: the hard function `f` applied to the seed's restriction to
`p`'s design set. -/
def nwGen (f : (ZMod q → Bool) → Bool) (z : ZMod q × ZMod q → Bool) (p : (ZMod q)[X]) : Bool :=
  f (nwRestrict z p)

/-- **Locality (proved)**: the generator's output at `p` depends only on the seed's values on `nwSet p` — the
read-once-via-design structure at the heart of the NW hybrid argument. -/
theorem nwGen_local (f : (ZMod q → Bool) → Bool) (z z' : ZMod q × ZMod q → Bool) (p : (ZMod q)[X])
    (h : ∀ x ∈ nwSet p, z x = z' x) : nwGen f z p = nwGen f z' p := by
  rw [nwGen, nwGen, nwRestrict_eq_of_agree z z' p h]

end PallLean.Paper93.DeepMath.PathB.NWDesign

#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwRestrict_eq_of_agree
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwGen_local
