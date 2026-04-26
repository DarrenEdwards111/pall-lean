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

## Honest status

Steps 1-3 deliver kernel-only the *structural* infrastructure for
closing the four monomial-coefficient identities:

```
(1)  coeff(probeRight, mlProj(∂_{rowRight} Q_b)) = 2 K
(2)  coeff(probeRight, mlProj(∂_{rowLeft}  Q_b)) =   K
(3)  coeff(probeLeft , mlProj(∂_{rowRight} Q_b)) =   K
(4)  coeff(probeLeft , mlProj(∂_{rowLeft}  Q_b)) = 2 K
```

The remaining work — the *per-pair summation* across the literal
touched-list (involving `O((1 + numStates)²)` cross-pairs, plus
self-pairs and boolean cross-talk paths) — is the residual obstruction
documented in `BridgeAKappaTwoPerPairCoefficients` as
`kappaTwoFourIdentities_perPairSum_obstruction`.

## Section A: package construction conditional on the per-pair sum

If the per-pair summation is supplied externally as the four identity
hypotheses, we can build the package directly.  This is just a
re-packaging of the existing `cookLevinLocalBlockQ_rank_two_le_real_unconditional`
of `BridgeAKappaTwoFourCoefficientIdentities`, exposed under a
discoverable name in the present module.

## Section B: residual obstruction Prop and rank lower bound

We expose the κ=2 rank lower bound conditional on
`kappaTwoFourIdentities_perPairSum_obstruction` (the per-pair sum
remaining-work marker).  Because the marker is `True`, this is
formally equivalent to the package-conditional form, but it makes the
seam between the structural infrastructure (Steps 1-3) and the residual
analytic computation (per-pair sum) explicit at the type level.

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

/-! ## Section C: residual obstruction Prop tying Steps 1-3 to the missing closure

We expose a single residual obstruction Prop that records the precise
remaining work to upgrade the typed package from a *hypothesis* to a
*kernel-only proven* witness.  Closing this Prop is exactly the work of
the per-pair summation (Steps 3+4 cross-pair / self-pair enumeration). -/

/-- Residual obstruction: a kernel-only proof of the four-identities
package.  This is the exact remaining work on top of the structural
infrastructure delivered by Steps 1-3.

The obstruction is the *existence* of a package witness, with no extra
side conditions: the bi-linear coefficient infrastructure
(`BridgeAKappaTwoPerPairCoefficients`) reduces the closure to a single
list-induction-with-summation across the literal touched-list. -/
def kappaTwoFourIdentities_residual
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) : Prop :=
  Nonempty
    (CookLevinLocalBlockQFourIdentitiesPackage
      M n hn htb hns k hk1 hk2)

/-- The κ=2 rank lower bound conditional on the residual obstruction
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

/-! ## Section D: status report

The κ=2 closure on the real Cook-Levin local block product is now
gated on a single residual obstruction:
`kappaTwoFourIdentities_residual` (i.e. the existence of a
`CookLevinLocalBlockQFourIdentitiesPackage` witness).

Steps 1-3 deliver kernel-only:
* literal explicit touched-list at an interior block;
* two-fold Leibniz expansion at the literal list;
* per-factor bilinear and derivative coefficient computations.

The remaining work is the per-pair summation across the literal
touched-list, which is the per-pair-sum obstruction documented in
`BridgeAKappaTwoPerPairCoefficients`.  Once that obstruction is
discharged kernel-only (≈3000-4000 LOC of list induction at the level
of `coeff_two_mono_list_prod_cons`), the four identities follow and
hence so does the unconditional rank lower bound. -/

/-! ## Axiom audit anchors -/

#print axioms cookLevinLocalBlockQ_rank_two_le_real_via_pkg
#print axioms cookLevinLocalBlockQFourIdentitiesPackage_of_witnesses
#print axioms cookLevinLocalBlockQ_rank_two_le_real_of_residual

end PallLean.Paper93.Paper283
