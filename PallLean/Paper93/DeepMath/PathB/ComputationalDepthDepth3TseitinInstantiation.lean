import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitTseitinBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinCNF

/-!
# Preimage-plumbing instantiation: the explicit Tseitin circuit over `RLit n`

The circuit→Tseitin bridge (`tautAx_dualDNF_implies`, `circuit_refutation_of_tlit_unsat`) reduces the
remaining work to a single concrete choice: the `RLit n` clause family whose `rlitToTlit`-images are
the explicit `tseitinClause`s.  This file makes that choice and discharges both named hypotheses
against the explicit `TseitinCNF` (with `Edge = Fin n`).

* `zmod2ToBool` / `boolToZMod2_zmod2ToBool` — the inverse of `boolToZMod2`.
* `rlitPreimageClause` — the `RLit n` preimage of `tseitinClause v α`, with `tseitinClause_image`
  (`(rlitPreimageClause v α).image rlitToTlit = tseitinClause v α`).
* `tseitinAxList` — the explicit `RLit n` clause family (one preimage clause per wrong-parity `(v,α)`).
* `tseitinAxList_implies` — every dual axiom of the circuit `dualDNF (tseitinAxList …)` is implied by a
  vertex constraint (the width LB's `hAxiom`).
* `tseitin_circuit_refutation` — under the odd-charge unsatisfiability (`tseitin_unsat`), the circuit
  `dualDNF (tseitinAxList …)` yields a refuting `DTRef` over its dual Tseitin axioms, of `depth ≤ fuel`.

So both hypotheses feeding the expander-Tseitin width lower bound are now discharged for an *explicit*
depth-3 circuit — closing the circuit-construction obligation (Obligation 2).  The only remaining
input is the *shallowness* of `fuel` (the good-restriction collapse, the fenced Obligation 1).
AC⁰/depth-3; `Depth3CollapseModel.collapse` and P vs NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open PallLean.Paper93.DeepMath.PathB.SemanticMeasure

namespace SearchDischarge

open Depth3

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The inverse of `boolToZMod2`: `z ↦ decide (z = 1)`. -/
def zmod2ToBool (z : ZMod 2) : Bool := decide (z = 1)

theorem boolToZMod2_zmod2ToBool (z : ZMod 2) : boolToZMod2 (zmod2ToBool z) = z := by
  revert z; decide

/-- The `RLit n` preimage of `tseitinClause v α`: literals `(e, zmod2ToBool (α e + 1))` over edges
incident to `v`. -/
def rlitPreimageClause (G : TseitinGraph V (Fin n)) (v : V) (α : Fin n → ZMod 2) :
    ResolutionClause (RLit n) :=
  (incident G v).image (fun e => ((e, zmod2ToBool (α e + 1)) : RLit n))

/-- **The preimage maps back to the Tseitin clause.**  `(rlitPreimageClause v α).image rlitToTlit =
tseitinClause v α`, by the `boolToZMod2 ∘ zmod2ToBool = id` round-trip. -/
theorem tseitinClause_image (G : TseitinGraph V (Fin n)) (v : V) (α : Fin n → ZMod 2) :
    (rlitPreimageClause G v α).image rlitToTlit = tseitinClause G v α := by
  unfold rlitPreimageClause tseitinClause
  rw [Finset.image_image]
  apply Finset.image_congr
  intro e _
  simp only [Function.comp_apply, rlitToTlit, boolToZMod2_zmod2ToBool]

/-- The explicit `RLit n` Tseitin clause family: one preimage clause per wrong-parity `(v, α)`. -/
noncomputable def tseitinAxList (G : TseitinGraph V (Fin n)) (charge : V → ZMod 2) :
    List (ResolutionClause (RLit n)) :=
  ((Finset.univ : Finset (V × (Fin n → ZMod 2))).filter
      (fun p => parity G p.2 p.1 ≠ charge p.1)).toList.map
    (fun p => rlitPreimageClause G p.1 p.2)

/-- Membership in `tseitinAxList` exposes the wrong-parity preimage form. -/
theorem mem_tseitinAxList {G : TseitinGraph V (Fin n)} {charge : V → ZMod 2}
    {C : ResolutionClause (RLit n)} (hC : C ∈ tseitinAxList G charge) :
    ∃ v α, parity G α v ≠ charge v ∧ C = rlitPreimageClause G v α := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC
  rw [Finset.mem_toList, Finset.mem_filter] at hp
  exact ⟨p.1, p.2, hp.2, rfl⟩

/-- **`hAxiom` for the explicit circuit.**  Every dual axiom of `dualDNF (tseitinAxList G charge)` is
implied by a vertex constraint — discharging the width LB's hypothesis. -/
theorem tseitinAxList_implies (G : TseitinGraph V (Fin n)) (charge : V → ZMod 2) :
    ∀ C' ∈ tautAx (dualDNF (tseitinAxList G charge)),
      ∃ v : V, Implies TSat (TConstr G charge) {v} C' := by
  refine tautAx_dualDNF_implies G charge ?_
  intro C hC
  obtain ⟨v, α, hwrong, rfl⟩ := mem_tseitinAxList hC
  exact ⟨v, by rw [tseitinClause_image]; exact implies_tseitinClause G charge v α hwrong⟩

/-- **Unsatisfiability of the explicit family.**  Under the odd-charge condition, every `ZMod 2`
assignment leaves some clause of `tseitinAxList` with all its image-literals unsatisfied. -/
theorem tseitinAxList_unsat (G : TseitinGraph V (Fin n)) (charge : V → ZMod 2)
    (hodd : ∑ v : V, charge v = 1) :
    ∀ a : Fin n → ZMod 2, ∃ C ∈ tseitinAxList G charge,
      ∀ p ∈ C, ¬ TSat a (rlitToTlit p) := by
  intro a
  obtain ⟨v, hv⟩ := tseitin_unsat G charge hodd a
  have hwrong : parity G a v ≠ charge v := hv
  refine ⟨rlitPreimageClause G v a, ?_, ?_⟩
  · refine List.mem_map.mpr ⟨(v, a), ?_, rfl⟩
    rw [Finset.mem_toList, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hwrong⟩
  · intro p hp
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hp
    simp only [rlitToTlit, boolToZMod2_zmod2ToBool, TSat]
    have : a e ≠ a e + 1 := by
      have := (by decide : ∀ x : ZMod 2, x ≠ x + 1) (a e); exact this
    exact this

/-- **The explicit circuit yields a refuting tree over the Tseitin axioms.**  Under the odd-charge
unsatisfiability, the concrete depth-3 circuit `dualDNF (tseitinAxList G charge)` produces a refuting
`DTRef` over `tautAx (dualDNF (tseitinAxList G charge))` of `depth ≤ fuel`.  Its axioms are implied by
vertex constraints (`tseitinAxList_implies`), so the expander width lower bound applies. -/
theorem tseitin_circuit_refutation (G : TseitinGraph V (Fin n)) (charge : V → ZMod 2)
    (hodd : ∑ v : V, charge v = 1) (fuel : ℕ)
    (hfuel : SwitchingCounting.stars (fun _ : Fin n => (none : Option Bool)) ≤ fuel) :
    ∃ T : DTRef (TLit (Fin n)),
      DTRef.Labeled (· ∈ tautAx (dualDNF (tseitinAxList G charge))) T ∧
      DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit (Fin n))) ∧
      T.depth ≤ fuel :=
  circuit_refutation_of_tlit_unsat (tseitinAxList_unsat G charge hodd) fuel hfuel

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.tseitinAxList_implies
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.tseitin_circuit_refutation
