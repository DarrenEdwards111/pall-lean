import PallLean.Paper93.Paper283.BridgeAKappaTwoPerPairCoefficients
import PallLean.Paper93.Paper283.BridgeAKappaTwoFourCoefficientIdentities
import PallLean.Paper93.Paper283.BridgeAKappaTwoFourFamilyComputation

/-!
# κ=2 Bridge A four-identities discharge composition

This file is the Step 4 follow-up to Steps 1-3:

* **Step 1** (`BridgeAKappaTwoTouchedListExplicit`): literal explicit
  touched-list at an interior block.
* **Step 2** (`BridgeAKappaTwoTwoFoldLeibnizExpansion`): two-fold
  Leibniz expansion of `pderiv w (pderiv v Q_b)` at the literal list.
* **Step 3** (`BridgeAKappaTwoPerPairCoefficients`): per-factor
  bilinear coefficient pre-computations on the literal list factors.

## Current status

Steps 1-3 delivered the structural infrastructure for the four
monomial-coefficient identities:

```
(1)  coeff(probeRight, mlProj(∂_{rowRight} Q_b)) = 2 K
(2)  coeff(probeRight, mlProj(∂_{rowLeft}  Q_b)) =   K
(3)  coeff(probeLeft , mlProj(∂_{rowRight} Q_b)) =   K
(4)  coeff(probeLeft , mlProj(∂_{rowLeft}  Q_b)) = 2 K
```

The concrete residual-active files now close the per-pair summations
kernel-only in the assembled downstream path.  This file keeps the
older residual-facing API and provides package-facing wrappers that
consume the closed package witness without importing the assembled
module or introducing an import cycle.

## Section A: package construction from coefficient identities

Given the four closed coefficient identities and the positivity
hypothesis for `K`, we can build the package directly.  This is just a
re-packaging of the existing `cookLevinLocalBlockQ_rank_two_le_real_unconditional`
of `BridgeAKappaTwoFourCoefficientIdentities`, exposed under a
discoverable name in the present module.

## Section B: residual-shaped Prop and closed wrappers

We preserve the residual-shaped `Nonempty` API for downstream files
that consume it, and expose wrappers from a closed package witness to
that residual shape.  The actual package construction lives downstream
in `BridgeAKappaTwoFourIdentitiesAssembled`, which imports this file.

No new axioms.  No `sorry`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeAKappaTwoPerPairCoefficients

attribute [local instance] Classical.dec

/-! ## Section A: re-export of the package-conditional rank lower bound -/

/-- The κ=2 rank lower bound on the real Cook-Levin local block product,
conditional on the typed four-identity package.  Re-export of
`cookLevinLocalBlockQ_rank_two_le_real_unconditional` for discoverability
under the present file's namespace. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_via_pkg
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (pkg :
      CookLevinLocalBlockQFourIdentitiesPackage
        M n hn htb hns k hk1 hk2) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩) :=
  cookLevinLocalBlockQ_rank_two_le_real_unconditional
    M n hn htb hns k hk1 hk2 pkg

/-! ## Section B: package-from-four-identities builder

We expose a builder that constructs a `CookLevinLocalBlockQFourIdentitiesPackage`
from the four explicit identities and a positivity hypothesis.  This is
just a `mk`-call wrapped for downstream use. -/

/-- Build a `CookLevinLocalBlockQFourIdentitiesPackage` from explicit
witnesses for `K`, the probe pair, and the four identities. -/
def cookLevinLocalBlockQFourIdentitiesPackage_of_witnesses
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (K : Rat) (hKpos : 0 < K)
    (probe : Fin 2 → Fin n →₀ Nat)
    (h00 :
      MvPolynomial.coeff (probe 0)
          (mlProj (iterDerivList
            [(⟨3 * k + 2, by omega⟩ : Fin n),
             (⟨3 * k + 3, hk2⟩ : Fin n)]
            (cookLevinLocalBlockQ M n hn htb hns
              ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
        2 * K)
    (h01 :
      MvPolynomial.coeff (probe 0)
          (mlProj (iterDerivList
            [(⟨3 * (k - 1) + 2, by
                have heq : 3 * (k - 1) + 3 = 3 * k := by
                  rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
                  congr 1; omega
                omega⟩ : Fin n),
             (⟨3 * k + 0, by omega⟩ : Fin n)]
            (cookLevinLocalBlockQ M n hn htb hns
              ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
        K)
    (h10 :
      MvPolynomial.coeff (probe 1)
          (mlProj (iterDerivList
            [(⟨3 * k + 2, by omega⟩ : Fin n),
             (⟨3 * k + 3, hk2⟩ : Fin n)]
            (cookLevinLocalBlockQ M n hn htb hns
              ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
        K)
    (h11 :
      MvPolynomial.coeff (probe 1)
          (mlProj (iterDerivList
            [(⟨3 * (k - 1) + 2, by
                have heq : 3 * (k - 1) + 3 = 3 * k := by
                  rw [show (3 : Nat) = 3 * 1 from rfl, ← Nat.mul_add]
                  congr 1; omega
                omega⟩ : Fin n),
             (⟨3 * k + 0, by omega⟩ : Fin n)]
            (cookLevinLocalBlockQ M n hn htb hns
              ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
        2 * K) :
    CookLevinLocalBlockQFourIdentitiesPackage M n hn htb hns k hk1 hk2 :=
  { K := K
    hKpos := hKpos
    probe := probe
    h00 := h00
    h01 := h01
    h10 := h10
    h11 := h11 }

/-! ## Section C: residual-shaped Prop and package-facing wrappers

We keep the old residual-shaped Prop as a stable downstream type, but
it is now just the `Nonempty` wrapper for a closed package witness.
This file cannot construct that witness directly without importing the
downstream assembled file and forming a cycle. -/

/-- Residual-shaped package witness type for the four κ=2 identities.
This used to mark the remaining per-pair summation work; it is now a
backward-compatible `Nonempty` wrapper around the closed package. -/
def kappaTwoFourIdentities_residual
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  Nonempty
    (CookLevinLocalBlockQFourIdentitiesPackage
      M n hn htb hns k hk1 hk2)

/-- Package-facing wrapper for the residual-shaped κ=2 API.  The
downstream assembled file supplies the closed package witness and can
use this theorem without creating an import cycle. -/
theorem kappaTwoFourIdentities_residual_of_package
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (pkg :
      CookLevinLocalBlockQFourIdentitiesPackage
        M n hn htb hns k hk1 hk2) :
    kappaTwoFourIdentities_residual
      M n hn htb hns k hk1 hk2 :=
  ⟨pkg⟩

/-- The κ=2 rank lower bound from the residual-shaped package witness
(equivalent to the package-conditional form). -/
theorem cookLevinLocalBlockQ_rank_two_le_real_of_residual
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (hres : kappaTwoFourIdentities_residual
      M n hn htb hns k hk1 hk2) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩) := by
  classical
  obtain ⟨pkg⟩ := hres
  exact cookLevinLocalBlockQ_rank_two_le_real_via_pkg
    M n hn htb hns k hk1 hk2 pkg

/-- Closed-package wrapper for the κ=2 rank lower bound. -/
theorem cookLevinLocalBlockQ_rank_two_le_real_discharged_of_closed_package
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (pkg :
      CookLevinLocalBlockQFourIdentitiesPackage
        M n hn htb hns k hk1 hk2) :
    (2 : Nat) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        2 2
        (cookLevinLocalBlockQ M n hn htb hns
          ⟨k, by rw [cook_levin_numBlocks]; omega⟩) :=
  cookLevinLocalBlockQ_rank_two_le_real_via_pkg
    M n hn htb hns k hk1 hk2 pkg

/-! ## Section D: status report

The κ=2 closure on the real Cook-Levin local block product is now
wired through this residual-facing layer.  The old
`kappaTwoFourIdentities_residual` name remains as a `Nonempty` package
wrapper, while `kappaTwoFourIdentities_residual_of_package` turns any
closed downstream package into that legacy shape.

The lower-level files deliver kernel-only:
* literal explicit touched-list at an interior block;
* two-fold Leibniz expansion at the literal list;
* per-factor bilinear and derivative coefficient computations;
* residual-active per-pair summations for identities (1), (2), (3),
  and (4);
* positivity of `crossBlockKValue (transCoeffSum M)`.

Consequently downstream files can feed the assembled package witness
through `cookLevinLocalBlockQ_rank_two_le_real_discharged_of_closed_package`
without depending on stale per-pair-sum hypotheses. -/

/-! ## Axiom audit anchors -/

#print axioms cookLevinLocalBlockQ_rank_two_le_real_via_pkg
#print axioms cookLevinLocalBlockQFourIdentitiesPackage_of_witnesses
#print axioms kappaTwoFourIdentities_residual_of_package
#print axioms cookLevinLocalBlockQ_rank_two_le_real_of_residual
#print axioms cookLevinLocalBlockQ_rank_two_le_real_discharged_of_closed_package

end PallLean.Paper93.Paper283
