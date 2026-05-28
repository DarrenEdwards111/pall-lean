import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinWidthKernel

/-!
# Concrete instantiation of the expander–Tseitin width kernel

This file discharges, concretely, the `HasExpansion` hypothesis of
`ComputationalDepthExpanderTseitinWidthKernel`: it exhibits an explicit graph
(`K4`, the complete graph on 4 vertices, 6 edges) and **proves** its expansion by
decision procedure — `HasExpansion` is therefore not a free predicate; it is
satisfied by a genuine object, and the width bound applies to it.

`K4_combination_width` is then a fully concrete, fully proved instance of the
BSW width lower bound: every combination of a medium vertex set's Tseitin
constraints on `K4` has width at least its size.

## Honest scope (two genuinely hard steps, only the first done here)

1. **Instantiate the expander — done, concretely.** `K4` with proven expansion
   shows the hypothesis is real and the kernel fires on a genuine graph.  What is
   *not* done is an asymptotic *family* with proven expansion: that needs an
   explicit infinite expander (Ramanujan-style) with a formalized spectral or
   combinatorial expansion bound — a deep formalization not attempted here.  A
   single graph gives non-vacuity and a concrete bound, not an asymptotic lower
   bound.

2. **Width → size — NOT done, and not faked.** The full Ben-Sasson–Wigderson
   result (a width lower bound `w` forces resolution refutation *size*
   `2^{Ω(w²/n)}`) requires formalizing a resolution proof system (clauses,
   resolution rule, refutation DAGs) and the size–width relation.  That is a
   major formalization.  It is **cited** here (Ben-Sasson–Wigderson, "Short
   proofs are narrow — resolution made simple", 2001), and deliberately **not**
   introduced as an assumed `Prop` field — assuming it would be the vacuity
   pattern this directory has otherwise fallen into.

So this file moves step 1 from "hypothesis" to "satisfied by a concrete graph,"
and leaves step 2 as honest cited future work.  It remains a restricted
(width / proof-complexity) result; it does not scale to P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-- Endpoints of the 6 edges of the complete graph `K4` on vertices `Fin 4`. -/
def k4endpoints : Fin 6 → Finset (Fin 4)
  | 0 => {0, 1}
  | 1 => {0, 2}
  | 2 => {0, 3}
  | 3 => {1, 2}
  | 4 => {1, 3}
  | 5 => {2, 3}

/-- The complete graph `K4` as a `TseitinGraph`: 4 vertices, 6 edges, each edge a
genuine 2-element endpoint set. -/
def K4 : TseitinGraph (Fin 4) (Fin 6) where
  endpoints := k4endpoints
  card_endpoints := by decide

/-- **Proven expansion.**  `K4` has vertex expansion `2`: every nonempty set of at
most half the vertices has edge boundary at least twice its size.  Verified by
decision procedure over all vertex subsets — a genuine discharge of
`HasExpansion`, not an assumption. -/
theorem K4_hasExpansion : K4.HasExpansion 2 := by
  unfold TseitinGraph.HasExpansion
  decide

/-- **Concrete BSW width bound.**  On `K4`, the F₂ combination of any medium
vertex set's Tseitin constraints has support (width) at least `2 · |S|`.  This is
a fully proved, concrete instance of `combination_support_card_ge_of_expansion`,
with expansion discharged by `K4_hasExpansion`. -/
theorem K4_combination_width (S : Finset (Fin 4))
    (h1 : 1 ≤ S.card) (h2 : 2 * S.card ≤ Fintype.card (Fin 4)) :
    2 * S.card ≤ (edgeSupport (K4.combination S)).card :=
  K4.combination_support_card_ge_of_expansion K4_hasExpansion S h1 h2

/-! ## Kernel-only axiom trace -/

#print axioms K4
#print axioms K4_hasExpansion
#print axioms K4_combination_width

end PallLean.Paper93.DeepMath.PathB
