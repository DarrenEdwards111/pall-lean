import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinResolutionWidth

/-!
# The ∅-lift core, constraint side: restricted Tseitin is Tseitin on the free edges

`ComputationalDepthExpanderTseitinRestriction` ("brick 1") handles the *resolution-clause* side of
restriction (live literals, width, satisfaction transfer).  This file is the complementary
*constraint* side: fixing a set `F` of edges to values `β` turns each Tseitin parity constraint at a
vertex into a Tseitin parity constraint over the **free** edges, with the charge shifted by the fixed
contribution.  This is the deterministic substrate of "the restricted Tseitin formula is itself a
Tseitin instance (on the free-edge subgraph)" — the fact behind *restricted-Tseitin-is-an-expander*.

* `parity_split` — the vertex parity splits over fixed/free edges (assignment agreeing with `β` on `F`).
* `restrictCharge` / `TConstr_restrict_iff` — the restricted constraint is the free-edge Tseitin
  constraint with the adjusted charge.

## What remains (honest)

This is the *deterministic* algebra.  The full ∅-lift further needs (a) the derivation-level
restriction `Der ↦ Der|ρ` (brick 2 of `…TseitinRestriction`, not built), and (b) the **probabilistic**
content: that for a good `ρ` the free-edge subgraph is still an **expander**, so the already-proved
`tseitinCNF_exp_size` applies, plus a union bound over `ρ`.  Crucially, that probabilistic
restriction-amplification is **subsumed** in the size route, which internalises it inside the
(proved) `tseitinCNF_exp_size`; `depth3_size_route_modulo_collapse` is modulo only the switching
collapse (Obligation 1).  This file does not build the probabilistic part.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- The charge adjusted by the fixed-edge contribution (`F` fixed to `β`). -/
def restrictCharge (G : TseitinGraph V Edge) (charge : V → ZMod 2) (β : Edge → ZMod 2)
    (F : Finset Edge) (v : V) : ZMod 2 :=
  charge v - ∑ e ∈ F, G.constraint v e * β e

/-- **The parity splits over fixed/free edges.**  If `a` agrees with `β` on the fixed set `F`, the
vertex parity is the residual (free-edge) parity plus the fixed contribution. -/
theorem parity_split (G : TseitinGraph V Edge) (a β : Edge → ZMod 2) (F : Finset Edge) (v : V)
    (hagree : ∀ e ∈ F, a e = β e) :
    parity G a v
      = (∑ e ∈ Finset.univ \ F, G.constraint v e * a e)
          + ∑ e ∈ F, G.constraint v e * β e := by
  unfold parity
  rw [← Finset.sum_sdiff (Finset.subset_univ F)]
  congr 1
  exact Finset.sum_congr rfl (fun e he => by rw [hagree e he])

/-- **Restricted-Tseitin constraint identity.**  An assignment agreeing with `β` on the fixed edges
`F` satisfies the Tseitin constraint at `v` iff the residual parity over the **free** edges equals the
adjusted charge.  So restricting a Tseitin formula yields Tseitin constraints on the free edges — the
deterministic heart of restriction-composition. -/
theorem TConstr_restrict_iff (G : TseitinGraph V Edge) (charge : V → ZMod 2) (β : Edge → ZMod 2)
    (F : Finset Edge) (v : V) (a : Edge → ZMod 2) (hagree : ∀ e ∈ F, a e = β e) :
    TConstr G charge v a
      ↔ (∑ e ∈ Finset.univ \ F, G.constraint v e * a e) = restrictCharge G charge β F v := by
  unfold TConstr restrictCharge
  rw [parity_split G a β F v hagree]
  constructor
  · intro h; rw [← h]; ring
  · intro h; rw [h]; ring

end PallLean.Paper93.DeepMath.PathB.TseitinResolution

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinResolution.parity_split
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinResolution.TConstr_restrict_iff
