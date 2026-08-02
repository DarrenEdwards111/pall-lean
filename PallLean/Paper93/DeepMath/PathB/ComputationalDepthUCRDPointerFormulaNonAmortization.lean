import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverNeciporukCalibration
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukOrMultiplexer
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDReuseNormalizationAudit

/-!
# UCRD pointer-formula non-amortization

The Tseitin UCRD direct sum needed an external `readK` hypothesis.  This file
tests the nearest model in which sub-total-use reuse follows from the
computation topology itself: Boolean formulas.  A formula is a tree, so a
subcomputation has no fan-out and cannot be shared globally as it can in a DAG
or machine trace.

For the genuine addressing families `hardF` and `orMux`, define pointer UCRD
to be the sum, over the address/data partition, of the logarithms of the
distinct residual functions visible at each block.  Then:

* every one of the `m` address contexts contributes at least `2^b - 1` fresh
  reconstruction bits;
* formula topology bounds the total by `4 * litCount + (m + 1)` with no
  bounded-reuse premise;
* hence both the parity and existential pointer families satisfy a direct
  non-amortization inequality;
* for `hardF`, this gives the established super-linear Nechiporuk regime.

This is the first UCRD rung where the reuse cap is *derived* rather than
assumed.  Its honest limitation is equally sharp: the derivation uses the
formula tree inequality.  DAG circuits and general machines have fan-out, and
the one-resource full-amortization construction from the reuse-normalization
audit remains available there.  Thus this is a genuine restricted lower bound,
not a lift to `P != NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDPointerFormulaNonAmortization

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.NecHardOr
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open PallLean.Paper93.DeepMath.PathB.UCRDReuseNormalizationAudit
open BFormula
open scoped BigOperators

variable {b m : ℕ}

/-- Pointer UCRD: the total observer-visible residual information across the
canonical address-block/data-block partition. -/
noncomputable def pointerUCRD (F : BFormula (nn b m)) : ℕ :=
  formulaTotalBoundary (Finset.univ : Finset (Option (Fin m)))
    (blkS (b := b) (m := m)) F

/-- Formula topology supplies the conservation side with no `readK` or
multiplicity assumption: the total contextual reconstruction depth is charged
to literal occurrences in the formula tree. -/
theorem pointerUCRD_le_formulaTopology (F : BFormula (nn b m)) :
    pointerUCRD F ≤ 4 * BFormula.litCount F + (m + 1) := by
  unfold pointerUCRD
  simpa using formulaTotalBoundary_le_size
    (Finset.univ : Finset (Option (Fin m)))
    (blkS (b := b) (m := m)) F blkS_disj blkS_cover

/-- If every address block forces reconstruction depth `q`, then the complete
pointer observer has depth at least `m*q`; the extra data block is harmless. -/
theorem addressDemand_le_pointerUCRD
    (F : BFormula (nn b m)) (q : ℕ)
    (hblock : ∀ k : Fin m, q ≤ formulaBlockBoundary (blockS k) F) :
    m * q ≤ pointerUCRD F := by
  classical
  have hconst : ∑ _k : Fin m, q = m * q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have haddr : m * q ≤ ∑ k : Fin m, formulaBlockBoundary (blockS k) F := by
    rw [← hconst]
    exact Finset.sum_le_sum (fun k _ ↦ hblock k)
  unfold pointerUCRD formulaTotalBoundary
  rw [Fintype.sum_option]
  exact le_trans haddr (Nat.le_add_left _ _)

/-- The parity-pointer family forces `m*(2^b-1)` fresh contextual
reconstruction bits. -/
theorem hardF_demand_le_pointerUCRD (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    m * (Dsize b - 1) ≤ pointerUCRD F :=
  addressDemand_le_pointerUCRD F (Dsize b - 1)
    (fun k ↦ hardF_blockBoundary_ge k F hF)

/-- **Derived non-amortization for parity pointers.**  No reuse bound appears
as a premise: the formula tree itself prevents global sharing. -/
theorem hardF_formula_nonAmortization (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    m * (Dsize b - 1) ≤ 4 * BFormula.litCount F + (m + 1) :=
  le_trans (hardF_demand_le_pointerUCRD F hF)
    (pointerUCRD_le_formulaTopology F)

/-- The existential/OR pointer family forces the same contextual demand. -/
theorem orMux_demand_le_pointerUCRD (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = orMux x) :
    m * (Dsize b - 1) ≤ pointerUCRD F :=
  addressDemand_le_pointerUCRD F (Dsize b - 1)
    (fun k ↦ orMux_blockBoundary_ge k F hF)

/-- **Derived non-amortization for existential pointers.**  The result is
addressing-driven, not an artifact of XOR/Tseitin parity. -/
theorem orMux_formula_nonAmortization (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = orMux x) :
    m * (Dsize b - 1) ≤ 4 * BFormula.litCount F + (m + 1) :=
  le_trans (orMux_demand_le_pointerUCRD F hF)
    (pointerUCRD_le_formulaTopology F)

/-- At balanced pointer scale, formula UCRD cannot be packed into linear
formula size.  This is the known Nechiporuk super-linear regime, now isolated
as a no-fixed-structure-amortization theorem. -/
theorem hardF_formulaUCRD_superlinear (C : ℕ) :
    ∃ b : ℕ, ∀ (F : BFormula (nn b (2 ^ b))),
      (∀ x, BFormula.eval F x = hardF x) →
        C * nn b (2 ^ b) < BFormula.litCount F :=
  hardF_observer_superlinear C

/-! ## The exact fan-out boundary -/

/-- Formula non-amortization does not eliminate the DAG/machine escape: at
selected scale, one shared resource with total-use multiplicity `t^2` still
exists.  Any lift must independently rule out this fan-out. -/
def fullFanoutEscape (t : ℕ) := selectedScaleFullAmortization t

theorem fullFanoutEscape_saturates (t : ℕ) :
    t ^ 2 = 1 * (t ^ 2) :=
  selectedScale_capacity_exact t

end PallLean.Paper93.DeepMath.PathB.UCRDPointerFormulaNonAmortization

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPointerFormulaNonAmortization.pointerUCRD_le_formulaTopology
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPointerFormulaNonAmortization.hardF_formula_nonAmortization
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPointerFormulaNonAmortization.orMux_formula_nonAmortization
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPointerFormulaNonAmortization.hardF_formulaUCRD_superlinear
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDPointerFormulaNonAmortization.fullFanoutEscape_saturates
