import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinCNF

/-!
# The restriction-composition, via the size route (BSW internalized)

The width route to the depth-3 lower bound (`dtRef_refuting_depth_ge`) needs an `∅`-refutation, which
forced an explicit **restriction-composition** (lifting the good restriction's `falseSet ρ` residual
refutation to `∅`).  The **size** route avoids it: `tseitinCNF_exp_size` is the Ben–Sasson–Wigderson
size lower bound for expander Tseitin, with the size→width restriction amplification **internalized**.
So the depth-3 collapse need only produce a *small* `∅`-resolution refutation of the full `TseitinCNF`
— no separate restriction-composition by us.

`tseitin_no_small_refutation` is the clean contradiction endpoint: a refutation of `TseitinCNF` of
size `≤ 2^D` with `D ≤ c·t − w₀ − 1` is impossible.  This is what a shallow collapsed tree (size
`≤ 2^depth`) contradicts.

## Reframing the remaining gap (honest)

Via the size route, the restriction-composition sub-gap I had isolated is **subsumed** (BSW lives
inside `tseitinCNF_exp_size`).  What remains to make the depth-3 lower bound unconditional is exactly:
produce a *small* `∅`-resolution refutation of the full `TseitinCNF` from the collapsed circuit, i.e.

* the switching **depth bound** for a good restriction (the fenced Obligation 1), giving a shallow
  decision tree, and
* the tree → resolution conversion with `size ≤ 2^depth` (`leaves_le_two_pow_depth`) landing in
  `ResolutionDerivation` form.

Both are named, not faked.  The contradiction *target* is now a clean theorem, and the size route
removes the restriction-composition from the critical path.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P vs NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinResolution

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **No small refutation of expander Tseitin.**  Under the odd-charge / expansion / degree
hypotheses with `w₀ < c·t`, an `∅`-resolution refutation of `TseitinCNF G charge` of size `≤ 2^D`
with `D ≤ c·t − w₀ − 1` is impossible — the size lower bound `tseitinCNF_exp_size`
(`2^(c·t−w₀−1) < size`) is exceeded.  This is the contradiction a shallow collapsed tree
(`size ≤ 2^depth`) must hit. -/
theorem tseitin_no_small_refutation (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hodd : ∑ v : V, charge v = 1) {c t w₀ : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c)
    (ht1 : 1 ≤ t) (hcard : 4 * t ≤ Fintype.card V) (hdeg : ∀ v, (incident G v).card ≤ w₀)
    (hgap : w₀ < c * t)
    (Der : ResolutionDerivation tcompl (TseitinCNF G charge) (∅ : ResolutionClause (TLit Edge)))
    {D : ℕ} (hsize : ResolutionDerivation.size Der ≤ 2 ^ D) (hD : D ≤ c * t - w₀ - 1) :
    False := by
  have hexpsize := tseitinCNF_exp_size G charge hodd hc hexp ht1 hcard hdeg hgap Der
  have hmono : (2 : ℕ) ^ D ≤ 2 ^ (c * t - w₀ - 1) :=
    Nat.pow_le_pow_right (by norm_num) hD
  omega

end PallLean.Paper93.DeepMath.PathB.TseitinResolution

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinResolution.tseitin_no_small_refutation
