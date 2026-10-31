import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRigidAdditiveMixer

/-!
# N-Frame: the exact mixer-tensor target specification

The capstone reduction (`ComputationalDepthNFrameRigidAdditiveMixer.lean`) showed the cross-branch
direct sum is equivalent to the existence of an explicit mixer whose incompressible rank is rigid and
direct-sum additive.  This file writes that target down as a precise CONTRACT: a `structure` bundling
the exact numeric properties a candidate mixer family must provide, and a theorem that ANY family
meeting the contract closes the whole tower (super-linear cone-excess).  A candidate (Ramanujan
incidence, Walsh–Hadamard, circulant, hybrid …) is admissible iff it instantiates `MixerTargetSpec`.

## The contract

For a mixer family indexed by level `k`, with `R k` = tensor/incompressible rank of one copy,
`R2 k` = rank of two disjoint copies, `fr k` = flattening (matrix) rank, `fresh k` = the mixer's gross
forced fresh cone-excess, and `amp k` = the amplification increment the recursion must net:

  • RIGIDITY / COUPLING — `fr k + fresh k ≤ R k`  (`R − fr ≥ fresh`): the rank exceeds every
    flattening by at least the fresh charge; this is what forces the `+fresh` cone-excess and escapes
    the linear/Valiant collapse (a linear/`R=fr` map has `R − fr = 0`).
  • ADDITIVITY — `2·R k + amp k ≤ R2 k + fresh k`  (`R2 ≥ 2R − (fresh − amp)`): two disjoint copies
    do not share more than the mixer's own slack, with amplification margin `amp`.

## The two theorems

  `MixerTargetSpec.forces_superlinear` — **PROVED**: any `MixerTargetSpec` `S`, given the frozen
        per-scale deficit accounting (`2·T k + fresh k ≤ T(k+1) + CE_share k`) and the modeling bridge
        (`CE_share k + R2 k ≤ 2·R k`: circuit sharing ≤ rank non-additivity deficit), forces
        `b·2^b ≤ T b` for every `b`.  Chains `rank_additivity_bounds_share` into
        `additive_mixer_forces_superlinear`.  The contract IS sufficient.
  `mixerTargetSpec_consistent` — **PROVED**: the contract is arithmetically SATISFIABLE with genuine
        coupling (`0 < fresh`, `fr < R`).  So the reduction is not vacuous, and — in contrast to
        `flattening_additivity_incompatible_with_coupling`, where the `R = fr` SUB-case is
        self-contradictory — the obstruction is precisely "no explicit TENSOR realizes the contract",
        NOT that the requirements conflict.

## Honest scope — this is the target, not a mixer

The spec fields are abstract `ℕ`-valued functions; `mixerTargetSpec_consistent` shows they can be
met by some assignment of numbers, but NOT by any exhibited explicit tensor.  Producing an explicit
`R, fr, R2` from a real Ramanujan/character/circulant family — with `R − fr ≥ fresh` (rigidity, an
open explicit lower bound) AND `R2 ≥ 2R − (fresh − amp)` (additivity in the rigid regime, Shitov's
zone) — is the entire open problem, unmoved.  This file only fixes the contract so candidate families
can be tested against a single precise interface.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameMixerTargetSpec

open PallLean.Paper93.DeepMath.PathB

/-- **THE MIXER-TENSOR TARGET CONTRACT**: the exact numeric properties an explicit mixer family must
provide to close the cross-branch direct sum.  `R` = rank of one copy, `R2` = rank of two disjoint
copies, `fr` = flattening rank, `fresh` = gross forced fresh cone-excess, `amp` = amplification
increment.  `rigidity`: `R − fr ≥ fresh` (coupling).  `additivity`: `R2 ≥ 2R − (fresh − amp)`. -/
structure MixerTargetSpec where
  amp : ℕ → ℕ
  fresh : ℕ → ℕ
  R : ℕ → ℕ
  R2 : ℕ → ℕ
  fr : ℕ → ℕ
  rigidity : ∀ k, fr k + fresh k ≤ R k
  additivity : ∀ k, 2 * R k + amp k ≤ R2 k + fresh k

/-- **THE CONTRACT IS SUFFICIENT (proved)**: any `MixerTargetSpec`, given the frozen deficit
accounting and the modeling bridge (circuit sharing ≤ rank non-additivity deficit), forces super-linear
cone-excess `b·2^b ≤ T b`.  This is the plug-in: an admissible mixer closes the whole tower. -/
theorem MixerTargetSpec.forces_superlinear
    (S : MixerTargetSpec) (c : ℕ) (hc : 1 ≤ c)
    (hamp : ∀ k, c * 2 ^ (k + 1) ≤ S.amp k)
    (T CE_share : ℕ → ℕ)
    (hdeficit : ∀ k, 2 * T k + S.fresh k ≤ T (k + 1) + CE_share k)
    (hbridge : ∀ k, CE_share k + S.R2 k ≤ 2 * S.R k)
    (b : ℕ) :
    b * 2 ^ b ≤ T b := by
  apply NFrameRigidAdditiveMixer.additive_mixer_forces_superlinear c hc T S.fresh CE_share hdeficit _ b
  intro k
  have hb := NFrameRigidAdditiveMixer.rank_additivity_bounds_share
    (S.R k) (S.R2 k) (CE_share k) (S.fresh k) (S.amp k) (hbridge k) (S.additivity k)
  have hamp' := hamp k
  omega

/-- A concrete numeric witness that the contract fields are jointly satisfiable WITH genuine coupling. -/
def exampleSpec : MixerTargetSpec where
  amp := fun _ => 1
  fresh := fun _ => 50
  R := fun _ => 100
  R2 := fun _ => 200
  fr := fun _ => 0
  rigidity := by intro k; omega
  additivity := by intro k; omega

/-- **THE CONTRACT IS CONSISTENT (proved)**: the target is arithmetically satisfiable with genuine
coupling (`0 < fresh`, `fr < R`).  The reduction is therefore non-vacuous, and the obstruction is "no
explicit tensor realizes it", NOT an internal contradiction — contrast the `R = fr` sub-case, which IS
contradictory (`flattening_additivity_incompatible_with_coupling`). -/
theorem mixerTargetSpec_consistent :
    ∃ S : MixerTargetSpec, ∀ k, 0 < S.fresh k ∧ S.fr k < S.R k :=
  ⟨exampleSpec, fun _ => ⟨by show (0 : ℕ) < 50; omega, by show (0 : ℕ) < 100; omega⟩⟩

end PallLean.Paper93.DeepMath.PathB.NFrameMixerTargetSpec

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMixerTargetSpec.MixerTargetSpec.forces_superlinear
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMixerTargetSpec.mixerTargetSpec_consistent
