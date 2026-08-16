import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth2AndParityCollapse

/-!
# XOR-DNF collapse to a finite union of target cosets

An XOR-DNF here is an OR of signed parity conjunctions.  Each conjunction accepts one target parity profile, so the
whole upper layer accepts a finite target set.  On a residual affine profile set `K + shift`, SAT is equivalent to
some target lying in that coset.

Consequently the branch shift need only be compared with the distinct target quotient classes.  The number of such
classes is at most the number of DNF terms, giving a direct extension of the single-conjunction Gaussian-elimination
base case to polynomially many target terms.
-/

namespace PallLean.Paper93.DeepMath.PathB.XorDNFCosetCollapse

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.UpperGateCosetSemantics
open PallLean.Paper93.DeepMath.PathB.Depth2AndParityCollapse

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]

/-- An OR of parity conjunctions accepts any profile listed as a term target. -/
def acceptsAnyTarget (targets : Finset V) (z : V) : Prop := z ∈ targets

/-- Distinct target cosets represented by the XOR-DNF terms. -/
noncomputable def targetCosetSet (K : Submodule F V) (targets : Finset V) : Finset (V ⧸ K) :=
  targets.image (Submodule.mkQ K)

/-- **XOR-DNF residual SAT = membership in a union of target cosets (proved).** -/
theorem upperSat_acceptsAnyTarget_iff (K : Submodule F V) (targets : Finset V) (shift : V) :
    upperSatOnCoset K (acceptsAnyTarget targets) shift ↔
      ∃ target ∈ targets, target - shift ∈ K := by
  constructor
  · rintro ⟨x, hx, htarget⟩
    change x + shift ∈ targets at htarget
    refine ⟨x + shift, htarget, ?_⟩
    simpa using hx
  · rintro ⟨target, htarget, hmem⟩
    refine ⟨target - shift, hmem, ?_⟩
    change target - shift + shift ∈ targets
    simpa using htarget

/-- Equivalently, the branch quotient must belong to the finite target-coset set. -/
theorem upperSat_acceptsAnyTarget_iff_quotient_mem (K : Submodule F V)
    (targets : Finset V) (shift : V) :
    upperSatOnCoset K (acceptsAnyTarget targets) shift ↔ Submodule.mkQ K shift ∈ targetCosetSet K targets := by
  rw [upperSat_acceptsAnyTarget_iff]
  constructor
  · rintro ⟨target, htarget, hmem⟩
    apply Finset.mem_image.mpr
    refine ⟨target, htarget, ?_⟩
    apply (Submodule.Quotient.eq (R := F) (p := K)).2
    exact hmem
  · intro hclass
    obtain ⟨target, htarget, heq⟩ := Finset.mem_image.mp hclass
    refine ⟨target, htarget, ?_⟩
    have h := (Submodule.Quotient.eq (R := F) (p := K)).1 heq
    exact h

/-- The number of relevant quotient classes is at most the number of XOR-DNF terms. -/
theorem targetCosetSet_card_le (K : Submodule F V) (targets : Finset V) :
    (targetCosetSet K targets).card ≤ targets.card := by
  exact Finset.card_image_le

end PallLean.Paper93.DeepMath.PathB.XorDNFCosetCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.XorDNFCosetCollapse.upperSat_acceptsAnyTarget_iff
#print axioms PallLean.Paper93.DeepMath.PathB.XorDNFCosetCollapse.upperSat_acceptsAnyTarget_iff_quotient_mem
#print axioms PallLean.Paper93.DeepMath.PathB.XorDNFCosetCollapse.targetCosetSet_card_le
