import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonGenerator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NonFieldObserverTheory

/-!
# The efficient Nisan–Wigderson design — low intersection from polynomial graphs (proved)

Entry 190 proved the *disjoint* NW design (the inefficient base case: `m` pairwise-disjoint blocks, seed length `m·k`).
The genuine NW generator needs the **efficient low-intersection design**: over a finite field `F`, the graphs of the
`|F|^k` distinct polynomials of degree `< k` form `|F|^k` sets, each of size `|F|`, with **pairwise intersection `< k`**.
This is the optimal NW design (seed `|F|² = O(k² / log m)` for `m = |F|^k` sets) and the source of the NW seed-length
bound.  This file *actually proves* the low-intersection property, reusing the field root-count bound
`field_root_card_le_natDegree` (entry 161): two distinct degree-`< k` polynomials agree on `< k` points, hence their
graphs meet in `< k` points.

## What is proved (clean axioms, no `sorry`)

* **`poly_agree_le_natDegree`** — two distinct polynomials `p ≠ q` agree on at most `(p − q).natDegree` field points
  (the agreement set is the root set of `p − q`; apply the entry-161 root-count bound).
* **`poly_agree_lt_of_degree_lt`** — if additionally `deg p, deg q < k`, they agree on `< k` points.
* **`nwSet`** / **`nwSet_card`** — the graph `{(a, p(a)) : a ∈ F}` of a polynomial, a set of size exactly `|F|`.
* **`nwSet_inter_le`** — the intersection of two graphs is bounded by the number of agreement points.
* **`nw_low_intersection_design`** — the capstone: distinct degree-`< k` polynomials yield graphs of size `|F|` with
  pairwise intersection `< k`.  This is the efficient NW design, fully proved.

## Honest scope

This proves the **combinatorial heart** of the efficient Nisan–Wigderson design — the low-intersection property of the
polynomial-graph family — completely and from first principles (via the entry-161 field root-count bound).  It is the
quantitative refinement of entry 190's disjoint base case.  What remains a named socket (entry 189/190
`NWGeneratorFromDesign`) is the **hybrid argument**: that a design + a hard function gives a generator fooling `ACC⁰`
(a circuit distinguishing the generator yields a small circuit for the hard function).  That step needs circuit-
complexity infrastructure absent here.  This file proves the *design*, not the *generator*.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonLowIntersection

open Polynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0NonFieldObserverTheory (field_root_card_le_natDegree)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Distinct polynomials agree on few points.**  Two distinct polynomials `p ≠ q` agree (`p(a) = q(a)`) on at most
`(p − q).natDegree` field points: the agreement set is exactly the root set of the nonzero polynomial `p − q`, so the
field root-count bound (entry 161, `field_root_card_le_natDegree`) applies. -/
theorem poly_agree_le_natDegree (p q : Polynomial F) (hpq : p ≠ q) :
    (Finset.univ.filter (fun a => p.eval a = q.eval a)).card ≤ (p - q).natDegree := by
  refine field_root_card_le_natDegree (p - q) _ (sub_ne_zero.mpr hpq) ?_
  intro a ha
  rw [Finset.mem_filter] at ha
  rw [eval_sub, ha.2, sub_self]

/-- **Low agreement for low-degree polynomials.**  If `p ≠ q` and both have degree `< k`, then `p` and `q` agree on
strictly fewer than `k` points (`(p − q).natDegree ≤ max (deg p) (deg q) < k`). -/
theorem poly_agree_lt_of_degree_lt (p q : Polynomial F) (k : ℕ) (hpq : p ≠ q)
    (hp : p.natDegree < k) (hq : q.natDegree < k) :
    (Finset.univ.filter (fun a => p.eval a = q.eval a)).card < k := by
  refine lt_of_le_of_lt (poly_agree_le_natDegree p q hpq) ?_
  have h : (p - q).natDegree ≤ max p.natDegree q.natDegree := natDegree_sub_le p q
  omega

/-- **The graph (NW set) of a polynomial.**  `nwSet p = {(a, p(a)) : a ∈ F} ⊆ F × F` — the design block associated to
`p`. -/
def nwSet (p : Polynomial F) : Finset (F × F) := Finset.univ.image (fun a => (a, p.eval a))

/-- **Every design block has size `|F|`.**  The map `a ↦ (a, p(a))` is injective (recover `a` from the first
coordinate), so the graph of `p` has exactly `|F|` points. -/
theorem nwSet_card (p : Polynomial F) : (nwSet p).card = Fintype.card F := by
  rw [nwSet, Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.mp hab).1),
    Finset.card_univ]

/-- **Graph intersection ≤ agreement count.**  A point `(a, b)` lies in both `nwSet p` and `nwSet q` iff
`b = p(a) = q(a)`, i.e. `a` is an agreement point; so the intersection injects into the agreement set. -/
theorem nwSet_inter_le (p q : Polynomial F) :
    (nwSet p ∩ nwSet q).card ≤ (Finset.univ.filter (fun a => p.eval a = q.eval a)).card := by
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_image_le (s := Finset.univ.filter (fun a => p.eval a = q.eval a))
      (f := fun a => (a, p.eval a)))
  rintro z hz
  simp only [Finset.mem_inter, nwSet, Finset.mem_image, Finset.mem_univ, true_and] at hz
  obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ := hz
  rw [← ha, Prod.mk.injEq] at ha'
  obtain ⟨haa, hbb⟩ := ha'
  rw [Finset.mem_image]
  refine ⟨a, ?_, ha⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ a, ?_⟩
  rw [haa] at hbb
  exact hbb.symm

/-- **The efficient NW low-intersection design (proved).**  Two distinct polynomials of degree `< k` give graphs
(`nwSet`) each of size exactly `|F|` with pairwise intersection strictly less than `k`.  Ranging over the `|F|^k`
degree-`< k` polynomials yields the genuine Nisan–Wigderson design: `m = |F|^k` blocks of size `|F|`, pairwise
intersection `< k`, seed length `|F|² = O(k² / log m)` — the efficient (low-intersection, not disjoint) refinement of
entry 190's base case. -/
theorem nw_low_intersection_design (p q : Polynomial F) (k : ℕ) (hpq : p ≠ q)
    (hp : p.natDegree < k) (hq : q.natDegree < k) :
    (nwSet p).card = Fintype.card F ∧ (nwSet q).card = Fintype.card F ∧
      (nwSet p ∩ nwSet q).card < k := by
  refine ⟨nwSet_card p, nwSet_card q, ?_⟩
  exact lt_of_le_of_lt (nwSet_inter_le p q) (poly_agree_lt_of_degree_lt p q k hpq hp hq)

end PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonLowIntersection

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonLowIntersection.nw_low_intersection_design
