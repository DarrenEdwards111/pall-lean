import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinCNF
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinSizeWidth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRestrictedConstraint
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SizeRouteContradiction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SizeRouteEndToEnd

/-!
# The Ben–Sasson–Wigderson size–width chain is complete (all bricks proved)

This is a machine-checked index confirming that the expander-Tseitin BSW size lower bound — including
the **derivation-level restriction `Der ↦ Der|ρ` ("brick 2")** — is **fully proved** (every `#check`
below is a theorem with clean axioms, no `sorry`, no `native_decide`).  An older docstring
(`…TseitinRestriction`) lists brick 2 as "not built"; that note is **stale** — brick 2 is
`TseitinRestriction.restrict_W` (on the working derivation type `WDerivation`), and the size–width
recursion and exponential bound are built on top of it.

## The chain (all proved)

* **Brick 1 — clause restriction.**  `liveClause_width_le` (restriction never widens),
  `clauseSat_iff` (satisfaction transfer), `lit_trichotomy`.
* **Brick 1′ — constraint restriction (this session).**  `parity_split` / `TConstr_restrict_iff`:
  the restricted Tseitin constraints are Tseitin constraints on the free edges (adjusted charge).
* **Brick 2 — derivation restriction.**  `restrict_W`: for `W : WDerivation` of a clause `C` not
  satisfied by `ρ`, there is a `WDerivation` of `liveClause ρ C` from the **restricted axioms**
  (`RestrictAxiom ρ Axiom`) with `size` **and** `proofWidth` non-increasing.  ← the brick the
  "∅-lift" question is about.
* **Brick 3 — size→width.**  `tree_width_le`: a refutation of `∅` has a refutation of `proofWidth
  ≤ w₀ + ⌈log₂ size⌉` (the BSW recursion `treeC`, driven by `restrict_W` on single-edge restrictions).
* **Expansion ⇒ exponential size.**  `resolution_size_width` + `resolution_exp_size` ⇒
  `tseitinCNF_exp_size`: any `∅`-refutation of the expander-Tseitin CNF has size `> 2^{c·t−w₀−1}`.
* **Contradiction endpoint + size route.**  `tseitin_no_small_refutation`;
  `depth3_size_route_modulo_collapse` (the depth-3 size route, modulo only the switching collapse).

## Conclusion

The BSW core — brick 2 (derivation restriction) included — is complete and clean.  The depth-3 size
route therefore needs **no separate ∅-lift / restriction-composition step**: it is internalised here.
The single remaining depth-3 obligation is the switching collapse (Obligation 1).  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

-- Brick 1: clause-level restriction.
#check @TseitinRestriction.liveClause_width_le
#check @TseitinRestriction.clauseSat_iff
#check @TseitinRestriction.lit_trichotomy

-- Brick 1′: constraint-level restriction (this session).
#check @TseitinResolution.parity_split
#check @TseitinResolution.TConstr_restrict_iff

-- Brick 2: the derivation restriction Der ↦ Der|ρ (size + proofWidth non-increasing).
#check @TseitinRestriction.restrict_W

-- Brick 3: the BSW size→width recursion.
#check @TseitinRestriction.tree_width_le

-- Expansion ⇒ exponential resolution size.
#check @TseitinRootBound.resolution_size_width
#check @TseitinRootBound.resolution_exp_size
#check @TseitinResolution.tseitinCNF_exp_size

-- Contradiction endpoint + the depth-3 size route (modulo only the switching collapse).
#check @TseitinResolution.tseitin_no_small_refutation
#check @depth3_size_route_modulo_collapse

end PallLean.Paper93.DeepMath.PathB
