import Mathlib

/-!
# Socket-2 (IKW): the Nisan–Wigderson combinatorial design

The Impagliazzo–Kabanets–Wigderson easy-witness route (socket 2 for Williams) turns a *hard function* into a
*pseudorandom generator* via the **Nisan–Wigderson design**: a family of near-disjoint sets.  This file builds that
design — the concrete combinatorial core — from low-degree polynomials over a prime field.

For each polynomial `p` of degree `< k` over `F_q`, the set `nwSet p = {(a, p(a)) : a ∈ F_q} ⊆ F_q × F_q` (the graph of
`p`) has size `q`, and two *distinct* low-degree polynomials agree on at most `k-1` points (a nonzero degree-`<k`
polynomial has `< k` roots), so their sets intersect in `< k` points.  This is exactly the NW design: `q^k` sets, each of
size `q`, pairwise intersection `< k`, in a universe of size `q^2`.

  `nwSet p` — the graph `{(a, p(a))}` of `p`, a set of size `q`.
  `nwSet_card` — **PROVED**: `|nwSet p| = q`.
  `mem_nwSet` — **PROVED**: `x ∈ nwSet p ↔ x.2 = p(x.1)`.
  `nwSet_inter_lt` — **PROVED, the design property**: for distinct `p ≠ p'` of degree `< k`, `|nwSet p ∩ nwSet p'| < k`
        — the near-disjointness at the heart of the Nisan–Wigderson generator.

## Honest scope — the design, not the full PRG or the collapse

This is the genuine NW combinatorial design (near-disjoint sets), the object the Nisan–Wigderson generator is built on.
What it does **not** do: (i) the generator itself — plugging a hard function `f` into the design to stretch a seed into a
pseudorandom string, and the hybrid argument that its output fools small circuits; (ii) the IKW easy-witness collapse
`¬EasyWitness ⇒ NEXP ⊆ P/poly ⇒ …` that this generator drives.  Those are the deep `NEXP`-strength content of socket 2,
not established here.  This file supplies the design.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NWDesign

open Polynomial Finset

variable {q : ℕ} [Fact q.Prime]

/-- The Nisan–Wigderson set of a polynomial: its graph `{(a, p(a)) : a ∈ F_q}`. -/
noncomputable def nwSet (p : (ZMod q)[X]) : Finset (ZMod q × ZMod q) :=
  Finset.univ.image (fun a => (a, p.eval a))

/-- **Membership (proved)**: `x ∈ nwSet p ↔ x.2 = p(x.1)`. -/
theorem mem_nwSet {p : (ZMod q)[X]} {x : ZMod q × ZMod q} : x ∈ nwSet p ↔ x.2 = p.eval x.1 := by
  rw [nwSet, Finset.mem_image]
  constructor
  · rintro ⟨a, _, rfl⟩; rfl
  · intro h; exact ⟨x.1, Finset.mem_univ _, by rw [← h]⟩

/-- **Each set has size `q` (proved)**: the graph of `p` has one point per `a ∈ F_q`. -/
theorem nwSet_card (p : (ZMod q)[X]) : (nwSet p).card = q := by
  rw [nwSet, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq .. ▸ h).1),
    Finset.card_univ, ZMod.card]

/-- **Root-count bound (proved)**: a nonzero polynomial over `F_q` vanishes at at most `natDegree` points. -/
theorem card_eval_zero_le_natDegree (p : (ZMod q)[X]) (hp : p ≠ 0) :
    (Finset.univ.filter (fun a => p.eval a = 0)).card ≤ p.natDegree := by
  have hsub : (Finset.univ.filter (fun a => p.eval a = 0)) ⊆ p.roots.toFinset := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Multiset.mem_toFinset, mem_roots hp]
    exact ha.2
  exact le_trans (Finset.card_le_card hsub) (le_trans (Multiset.toFinset_card_le _) p.card_roots')

/-- **Intersection ⊆ agreement set (proved)**: two graphs meet only where the polynomials agree. -/
theorem nwSet_inter_card_le (p p' : (ZMod q)[X]) :
    (nwSet p ∩ nwSet p').card ≤ (Finset.univ.filter (fun a => p.eval a = p'.eval a)).card := by
  refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_inter, mem_nwSet, mem_nwSet] at hx
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hx.1]; exact hx.2
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_inter, mem_nwSet, mem_nwSet] at hx hy
    have hxy2 : x.2 = y.2 := by rw [hx.1, hxy, ← hy.1]
    exact Prod.ext hxy hxy2

/-- **The design property (proved)**: distinct degree-`<k` polynomials give near-disjoint sets — `|nwSet p ∩ nwSet p'| <
k`.  This is the Nisan–Wigderson near-disjointness. -/
theorem nwSet_inter_lt (p p' : (ZMod q)[X]) (hne : p ≠ p') (k : ℕ)
    (hp : p.natDegree < k) (hp' : p'.natDegree < k) :
    (nwSet p ∩ nwSet p').card < k := by
  refine lt_of_le_of_lt (nwSet_inter_card_le p p') ?_
  have hd : p - p' ≠ 0 := sub_ne_zero.mpr hne
  have hfilter : (Finset.univ.filter (fun a => p.eval a = p'.eval a))
      = Finset.univ.filter (fun a => (p - p').eval a = 0) := by
    apply Finset.filter_congr
    intro a _
    rw [Polynomial.eval_sub, sub_eq_zero]
  rw [hfilter]
  refine lt_of_le_of_lt (card_eval_zero_le_natDegree (p - p') hd) ?_
  exact lt_of_le_of_lt (natDegree_sub_le p p') (max_lt hp hp')

end PallLean.Paper93.DeepMath.PathB.NWDesign

#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwSet_card
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwSet_inter_lt
