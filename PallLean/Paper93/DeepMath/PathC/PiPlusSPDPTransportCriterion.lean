import PallLean.Paper93.DeepMath.PathC.PiPlusRankInvariantReduction

/-!
# Generator criterion for Pi+ SPDP subspace transport

`PiPlusRankInvariantReduction` reduced rank invariance to equality of SPDP
subspaces under the concrete `Pi+` linear equivalence.  This file reduces that
subspace equality one step further, to the only remaining hard algebra: transport
of the individual SPDP generators

`mlProj (m * iterDerivList S p)`.

This keeps the proof kernel-clean and avoids pretending that an arbitrary
block-Hadamard substitution automatically commutes with `mlProj` and iterated
partial derivatives.  The next file can now attack exactly those generator
commutation lemmas.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Forward generator transport: every SPDP generator for `p`, after applying
`Pi+`, lies in the SPDP subspace for `Pi+ p`. -/
def PiPlusSPDPForwardGeneratorTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : Nat) (p : PathB.SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : PathB.SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      piP.gauge (mlProj (m * iterDerivList S p)) ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge p)

/-- Backward generator transport: every SPDP generator for `Pi+ p` already lies
in the image under `Pi+` of the SPDP subspace for `p`. -/
def PiPlusSPDPBackwardGeneratorTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : Nat) (p : PathB.SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : PathB.SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      mlProj (m * iterDerivList S (piP.gauge p)) ∈
        Submodule.map piP.gauge
          (mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p)

/-- Forward/backward generator transport package. -/
structure PiPlusSPDPGeneratorTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop where
  forward : PiPlusSPDPForwardGeneratorTransport M n hn2 htb hns piP
  backward : PiPlusSPDPBackwardGeneratorTransport M n hn2 htb hns piP

/-- Forward generator transport gives the forward subspace inclusion. -/
theorem piPlusSPDPSubspace_forward_le_of_generatorTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hgen : PiPlusSPDPForwardGeneratorTransport M n hn2 htb hns piP)
    (κ ℓ : Nat) (p : PathB.SATDeciderGaugeSpace M n hn2 htb hns) :
    Submodule.map piP.gauge
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p) ≤
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge p) := by
  rw [mlBlockedSpdpSubspace]
  rw [Submodule.map_span_le]
  intro y hy
  rcases hy with ⟨S, m, hlen, hdeg, hvars, hadm, hy⟩
  rw [hy]
  exact hgen κ ℓ p S m hlen hdeg hvars hadm

/-- Backward generator transport gives the reverse subspace inclusion. -/
theorem piPlusSPDPSubspace_backward_le_of_generatorTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hgen : PiPlusSPDPBackwardGeneratorTransport M n hn2 htb hns piP)
    (κ ℓ : Nat) (p : PathB.SATDeciderGaugeSpace M n hn2 htb hns) :
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge p) ≤
    Submodule.map piP.gauge
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p) := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  rw [hq]
  exact hgen κ ℓ p S m hlen hdeg hvars hadm

/-- Generator-level transport implies the SPDP subspace transport condition. -/
theorem piPlusSPDPSubspaceTransport_of_generatorTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hgen : PiPlusSPDPGeneratorTransport M n hn2 htb hns piP) :
    PiPlusSPDPSubspaceTransport M n hn2 htb hns piP := by
  intro κ ℓ p
  apply le_antisymm
  · exact piPlusSPDPSubspace_forward_le_of_generatorTransport
      M n hn2 htb hns piP hgen.forward κ ℓ p
  · exact piPlusSPDPSubspace_backward_le_of_generatorTransport
      M n hn2 htb hns piP hgen.backward κ ℓ p

/-- Therefore generator-level transport is enough for rank invariance. -/
theorem piPlusRankInvariant_of_generatorTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hgen : PiPlusSPDPGeneratorTransport M n hn2 htb hns piP) :
    PiPlusRankInvariant M n hn2 htb hns piP :=
  piPlusRankInvariant_of_spdpSubspaceTransport M n hn2 htb hns piP
    (piPlusSPDPSubspaceTransport_of_generatorTransport M n hn2 htb hns piP hgen)

/-- Paper-scale generator transport for the concrete `Pi+`. -/
abbrev PaperScalePiPlusSPDPGeneratorTransport
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusSPDPGeneratorTransport M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale generator transport gives paper-scale rank invariance. -/
theorem cookLevinPiPlusRankInvariant_paperScale_of_generatorTransport
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hgen : PaperScalePiPlusSPDPGeneratorTransport M htb hns) :
    PiPlusRankInvariant M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns) :=
  piPlusRankInvariant_of_generatorTransport M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hgen

/-! ## Axiom audit anchors -/

#print axioms piPlusSPDPSubspace_forward_le_of_generatorTransport
#print axioms piPlusSPDPSubspace_backward_le_of_generatorTransport
#print axioms piPlusSPDPSubspaceTransport_of_generatorTransport
#print axioms piPlusRankInvariant_of_generatorTransport
#print axioms cookLevinPiPlusRankInvariant_paperScale_of_generatorTransport

end PallLean.Paper93.DeepMath.PathC
