import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWHybrid

/-!
# Socket-2 (IKW): the patched-seed interface of the Nisan–Wigderson predictor

The NW next-bit predictor fixes the seed on a background `z` and *patches* the target coordinate `p`'s design set with a
variable `w`.  This file records the exact asymmetry that patch exposes — the structural heart of the predictor:

  `patchSet z w p` — the seed that uses `w` on `nwSet p` and the background `z` elsewhere.
  `nwGen_patch_target` — **PROVED**: the **target** coordinate reads *all* of the patch: `nwGen f (patchSet z w p) p =
        nwGen f w p` (all `q` bits of `w` on `nwSet p`).
  `nwGen_patch_other` — **PROVED**: every **other** coordinate `p'` reads the patch only through the overlap `nwSet p ∩
        nwSet p'` — patches agreeing on that overlap give the same output at `p'` (and the overlap is `< k` by the design).

So under the patch: the target output is `f` on all `q` variable bits, while each other output is a function of only the
`< k` overlap bits — exactly the asymmetry that turns a next-bit distinguisher into a small circuit for `f`.

## Honest scope — the predictor's structure, not the predictor's correctness

This is the concrete patched-seed interface: the target reads `q` bits, the others read `< k`.  It is the structural
substrate a next-bit predictor is built on — hard-wire the background `z` and the other coordinates (each a `<k`-junta of
the patch) and read off the target `f`.  It does **not** carry out the probabilistic **hybrid / next-bit-predictor**
argument (that a distinguisher yields a predictor with non-trivial advantage, contradicting `f`'s average-case hardness),
nor the IKW easy-witness collapse.  Those are the deep `NEXP`-strength content of socket 2, not established here.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NWDesign

open Polynomial Finset

variable {q : ℕ} [Fact q.Prime]

/-- The seed patched on the target's design set: `w` on `nwSet p`, background `z` elsewhere. -/
noncomputable def patchSet (z w : ZMod q × ZMod q → Bool) (p : (ZMod q)[X]) :
    ZMod q × ZMod q → Bool :=
  fun x => if x ∈ nwSet p then w x else z x

/-- **The target reads the whole patch (proved)**: `nwGen f (patchSet z w p) p = nwGen f w p` — the target coordinate `p`
sees all `q` patched bits of `w` on `nwSet p`. -/
theorem nwGen_patch_target (f : (ZMod q → Bool) → Bool) (z w : ZMod q × ZMod q → Bool)
    (p : (ZMod q)[X]) : nwGen f (patchSet z w p) p = nwGen f w p := by
  rw [nwGen, nwGen]
  congr 1
  funext a
  simp only [nwRestrict, patchSet]
  rw [if_pos (mem_nwSet.mpr rfl)]

/-- **Other coordinates read only the overlap of the patch (proved)**: if two patches `w, w'` agree on the overlap
`nwSet p ∩ nwSet p'`, then output `p'` is unchanged — so `p'` reads the patch through only the `< k` overlap bits. -/
theorem nwGen_patch_other (f : (ZMod q → Bool) → Bool) (z w w' : ZMod q × ZMod q → Bool)
    (p p' : (ZMod q)[X]) (h : ∀ x ∈ nwSet p ∩ nwSet p', w x = w' x) :
    nwGen f (patchSet z w p) p' = nwGen f (patchSet z w' p) p' := by
  apply nwGen_dep_overlap
  · intro x hx
    unfold patchSet
    rw [if_neg hx, if_neg hx]
  · intro x hx
    have hxp : x ∈ nwSet p := (Finset.mem_inter.mp hx).1
    unfold patchSet
    rw [if_pos hxp, if_pos hxp]
    exact h x hx

end PallLean.Paper93.DeepMath.PathB.NWDesign

#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwGen_patch_target
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwGen_patch_other
