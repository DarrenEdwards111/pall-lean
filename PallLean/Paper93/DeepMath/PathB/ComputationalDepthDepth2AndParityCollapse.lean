import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUpperGateCosetSemantics

/-!
# Depth-2 AND-of-parity collapse to linear span membership

An AND of parity literals accepts exactly one parity-profile target (each literal specifies whether its parity gate
must output zero or one).  On an affine residual profile set `K + shift`, satisfiability is therefore equivalent to
the target lying in that coset, i.e. to the single linear condition `target - shift ∈ K`.

This is the first named upper class where nonlinear structure gives a complete semantic collapse: all residual
branches are classified by whether their quotient class equals the target quotient class.  Algorithmically this is a
Gaussian-elimination/span-membership problem for depth-2 AND-of-`MOD₂`, not exponential branch enumeration.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth2AndParityCollapse

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.UpperGateCosetSemantics

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- An AND of signed parity literals accepts its unique required output profile. -/
def acceptsTarget (target z : V) : Prop := z = target

/-- **AND-of-parity residual SAT = span membership (proved).** -/
theorem upperSat_acceptsTarget_iff (K : Submodule F V) (target shift : V) :
    upperSatOnCoset K (acceptsTarget target) shift ↔ target - shift ∈ K := by
  constructor
  · rintro ⟨x, hx, htarget⟩
    change x + shift = target at htarget
    rw [← htarget]
    simpa using hx
  · intro hmem
    refine ⟨target - shift, hmem, ?_⟩
    change target - shift + shift = target
    abel

/-- Equivalently, a residual branch is satisfiable exactly when its quotient class is the target class. -/
theorem upperSat_acceptsTarget_iff_quotient_eq (K : Submodule F V) (target shift : V) :
    upperSatOnCoset K (acceptsTarget target) shift ↔
      Submodule.mkQ K shift = Submodule.mkQ K target := by
  rw [upperSat_acceptsTarget_iff]
  constructor
  · intro h
    apply (Submodule.Quotient.eq (R := F) (p := K)).2
    have := K.neg_mem h
    simpa [sub_eq_add_neg, add_comm] using this
  · intro hq
    have h := (Submodule.Quotient.eq (R := F) (p := K)).1 hq
    have := K.neg_mem h
    simpa [sub_eq_add_neg, add_comm] using this

/-- At most one quotient class can be satisfiable for an AND of parity literals. -/
theorem satisfiable_branches_have_same_quotient (K : Submodule F V) (target : V) {a b : V}
    (ha : upperSatOnCoset K (acceptsTarget target) a)
    (hb : upperSatOnCoset K (acceptsTarget target) b) :
    Submodule.mkQ K a = Submodule.mkQ K b := by
  rw [upperSat_acceptsTarget_iff_quotient_eq K target a] at ha
  rw [upperSat_acceptsTarget_iff_quotient_eq K target b] at hb
  exact ha.trans hb.symm

end PallLean.Paper93.DeepMath.PathB.Depth2AndParityCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.Depth2AndParityCollapse.upperSat_acceptsTarget_iff
#print axioms PallLean.Paper93.DeepMath.PathB.Depth2AndParityCollapse.upperSat_acceptsTarget_iff_quotient_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Depth2AndParityCollapse.satisfiable_branches_have_same_quotient
