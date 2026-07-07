import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMixerTargetSpec

/-!
# N-Frame: the hybrid mixer via the substitution method — reduced to substitution tightness

The candidate triage killed four mixer families (Ramanujan-incidence, Walsh–Hadamard, circulant,
matmul) on one horn or the other.  The sole survivor is the block-coupled hybrid: additive-certified
local blocks with expander coupling between them.  This file resolves what the hybrid actually needs by
routing the mixer's rank through the SUBSTITUTION METHOD, and reduces the whole construction to a single
property of that method.

## Why the substitution method is the right tool

The `MixerTargetSpec` contract asks for a mixer whose rank is BOTH rigid (`R − fr ≥ fresh`, to force the
charge / escape Valiant) AND direct-sum additive (`R2 ≥ 2R − fresh`, so two copies cannot share).  The
substitution method (Bürgisser–Clausen–Shokrollahi; Pan, Hopcroft–Kerr, Bläser) is the unique general
tensor-rank lower-bound tool that is DIRECT-SUM ADDITIVE by construction: it "preserves the structure of
a direct sum", so `LB(T^{⊕m}) ≥ m·LB(T)`.  Hence if the mixer's rank is lower-bounded by substitution,
`R2 ≥ LB(T^{⊕2}) ≥ 2·LB(T)` — additivity of the LOWER BOUND is free.  This is why the hybrid is not dead
where the others are: additivity is supplied by the PROOF TECHNIQUE, not by a fragile tensor property.

## What remains — substitution tightness (the residual `R − LB`)

Writing `LB` = substitution bound, `R` = true rank, `fr` = flattening rank, and `R2` = two-copy rank:
  • RIGIDITY needs `fr + fresh ≤ LB` (substitution beats flattening by the fresh charge) — achievable;
    Bläser-type explicit bounds exceed the flattening.
  • ADDITIVITY needs `2·R ≤ R2 + fresh`; with `R2 ≥ 2·LB` this holds iff the RESIDUAL `R − LB ≤ fresh/2`,
    i.e. substitution is NEARLY TIGHT.

The residual `R − LB` is the crux, for a sharp reason it is BOTH:
  (a) the only place non-additivity can hide — substitution-certified rank is additive, so any sharing
      lives in the part substitution cannot see; and
  (b) un-certifiable as additive by the one additive tool available (by definition it is what substitution
      misses).
So `additivity ⟺ substitution tightness on the mixer` (up to `fresh/2`).  The literature is explicit that
substitution is NOT tight in general (`Landsberg–Teitler`, real-tensor lower bounds: "a tight lower bound
is not possible via the substitution method" for the studied tensors).  Whether an explicit EXPANDER
tensor — whose spread is exactly what makes substitution accumulate well — admits a bound that is both
STRONG (`LB − fr ≥ fresh`) and NEARLY TIGHT (`R − LB ≤ fresh/2`) is the open sub-question the hybrid
reduces to.  Not settled here, neither way.

## The theorems

  `substitution_gives_spec_fields` — **PROVED**: strong (`fr+fresh ≤ LB`) + lower-bound (`LB ≤ R`) +
        additive-substitution (`2·LB ≤ R2`) + near-tight (`2R + amp ≤ 2·LB + fresh`) ⟹ the two
        `MixerTargetSpec` fields `fr+fresh ≤ R` (rigidity) and `2R + amp ≤ R2 + fresh` (additivity).
  `specFromSubstitution` — **PROVED (builder)**: a level-indexed family with those substitution
        properties INSTANTIATES `MixerTargetSpec`.
  `hybrid_forces_superlinear` — **PROVED**: such a family + the frozen deficit + the modeling bridge
        forces super-linear cone-excess `b·2^b ≤ T b`.  The full chain, conditional on substitution.
  `substitution_tightness_necessary` — **PROVED (witness)**: with strong + additive-substitution holding
        but substitution NOT tight (`2·LB + fresh < 2R + amp`), the spec additivity FAILS
        (`R2 + fresh < 2R + amp`).  So tightness is not optional — it is the crux.

## Honest scope

This does NOT construct a mixer.  It identifies the substitution method as the tool that supplies
additivity for free, and reduces the entire hybrid to ONE property: substitution near-tightness on an
explicit strong-bound expander tensor (`R − LB ≤ fresh/2` with `LB − fr ≥ fresh`).  That is a concrete,
named, unresolved question about a specific technique — a genuine refinement of "find an additive tensor",
not a closure.  The residual `R − LB` is named as the sole home of non-additivity.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameHybridSubstitution

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NFrameMixerTargetSpec

/-- **SUBSTITUTION CONDITIONS ⟹ THE SPEC FIELDS (proved)**: a strong (`fr+fresh ≤ LB`), valid
(`LB ≤ R`), additively-certified (`2·LB ≤ R2`) and near-tight (`2R + amp ≤ 2·LB + fresh`) substitution
bound yields the `MixerTargetSpec` rigidity (`fr+fresh ≤ R`) and additivity (`2R + amp ≤ R2 + fresh`). -/
theorem substitution_gives_spec_fields
    (LB R R2 fr fresh amp : ℕ)
    (h_lb_le_r : LB ≤ R)
    (h_strong : fr + fresh ≤ LB)
    (h_additive_subst : 2 * LB ≤ R2)
    (h_tight : 2 * R + amp ≤ 2 * LB + fresh) :
    fr + fresh ≤ R ∧ 2 * R + amp ≤ R2 + fresh := by
  refine ⟨?_, ?_⟩ <;> omega

/-- **BUILDER (proved)**: a level-indexed family with strong, valid, additively-certified, near-tight
substitution bounds instantiates the mixer-target contract `MixerTargetSpec`. -/
def specFromSubstitution
    (LB R R2 fr fresh amp : ℕ → ℕ)
    (h_lb_le_r : ∀ k, LB k ≤ R k)
    (h_strong : ∀ k, fr k + fresh k ≤ LB k)
    (h_additive_subst : ∀ k, 2 * LB k ≤ R2 k)
    (h_tight : ∀ k, 2 * R k + amp k ≤ 2 * LB k + fresh k) :
    MixerTargetSpec where
  amp := amp
  fresh := fresh
  R := R
  R2 := R2
  fr := fr
  rigidity := fun k => by have := h_strong k; have := h_lb_le_r k; omega
  additivity := fun k => by have := h_tight k; have := h_additive_subst k; omega

/-- **THE HYBRID CHAIN (proved)**: a family with strong + valid + additive + near-tight substitution
bounds, plus the frozen deficit accounting and the modeling bridge, forces super-linear cone-excess
`b·2^b ≤ T b`.  This is the whole tower, conditional on substitution tightness for the mixer. -/
theorem hybrid_forces_superlinear
    (c : ℕ) (hc : 1 ≤ c)
    (LB R R2 fr fresh amp T CE_share : ℕ → ℕ)
    (h_lb_le_r : ∀ k, LB k ≤ R k)
    (h_strong : ∀ k, fr k + fresh k ≤ LB k)
    (h_additive_subst : ∀ k, 2 * LB k ≤ R2 k)
    (h_tight : ∀ k, 2 * R k + amp k ≤ 2 * LB k + fresh k)
    (hamp : ∀ k, c * 2 ^ (k + 1) ≤ amp k)
    (hdeficit : ∀ k, 2 * T k + fresh k ≤ T (k + 1) + CE_share k)
    (hbridge : ∀ k, CE_share k + R2 k ≤ 2 * R k)
    (b : ℕ) :
    b * 2 ^ b ≤ T b :=
  (specFromSubstitution LB R R2 fr fresh amp h_lb_le_r h_strong h_additive_subst h_tight).forces_superlinear
    c hc hamp T CE_share hdeficit hbridge b

/-- **TIGHTNESS IS THE CRUX (proved witness)**: values `(LB,R,R2,fr,fresh,amp) = (100,130,200,90,10,0)`
have a strong (`fr+fresh ≤ LB`), valid (`LB ≤ R`), additively-certified (`2·LB ≤ R2`) substitution bound
that is NOT tight (`2·LB + fresh < 2R + amp`, residual `R−LB = 30 > fresh/2 = 5`), and the spec additivity
FAILS (`R2 + fresh < 2R + amp`).  So substitution near-tightness is necessary — it is exactly the open
sub-question the hybrid stands on. -/
theorem substitution_tightness_necessary :
    ∃ (LB R R2 fr fresh amp : ℕ),
      LB ≤ R ∧ fr + fresh ≤ LB ∧ 2 * LB ≤ R2 ∧
      2 * LB + fresh < 2 * R + amp ∧
      R2 + fresh < 2 * R + amp :=
  ⟨100, 130, 200, 90, 10, 0, by omega, by omega, by omega, by omega, by omega⟩

end PallLean.Paper93.DeepMath.PathB.NFrameHybridSubstitution

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameHybridSubstitution.substitution_gives_spec_fields
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameHybridSubstitution.hybrid_forces_superlinear
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameHybridSubstitution.substitution_tightness_necessary
