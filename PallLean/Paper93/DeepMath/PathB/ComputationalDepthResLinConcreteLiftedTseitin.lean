import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinLiftedTseitinInterface
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinRestrictedBooleanCleanup
import Mathlib.Tactic

/-!
# Concrete Tseitin instances, block gadgets, and restriction survival

This file replaces the bare `LiftedTseitinFamily` placeholder by actual finite objects.

* A Tseitin instance is an incidence matrix over `𝔽₂`, a charge vector of odd total parity, and the
  graph identity that every edge column has even parity.
* Each vertex contributes one affine parity equation.  Summing all equations proves the instance
  unsatisfiable.
* A block gadget maps `b` lifted bits to one base edge bit.
* The lifted clause set is the exact finite truth-table CNF: for every lifted assignment whose
  gadget output violates the base instance, include the clause excluding that assignment.
* For the projection gadget, an explicit restriction fixes all non-leading block coordinates and
  recovers the base Tseitin semantics exactly.

The truth-table encoding is intentionally semantic and may be exponentially large.  The paper's
size-efficient local CNF for Inner Product, its Fourier-fooling estimates, and the high-probability
random-restriction theorem remain separate lower-bound mathematics; they are not assumed here.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

open Classical BigOperators

/-! ## Concrete base Tseitin contradictions -/

/-- Finite Tseitin data.  `incidence v e = 1` means edge `e` is incident to vertex `v`; the only
graph identity needed for semantic inconsistency is that every edge column sums to zero in `𝔽₂`.
-/
structure ConcreteTseitin where
  vertexCount : ℕ
  edgeCount : ℕ
  incidence : Fin vertexCount → Fin edgeCount → ZMod 2
  evenColumns : ∀ e, ∑ v, incidence v e = 0
  charge : Fin vertexCount → ZMod 2
  oddCharge : (∑ v, charge v) ≠ 0

/-- The parity equation at one vertex. -/
def ConcreteTseitin.vertexEquation (T : ConcreteTseitin) (v : Fin T.vertexCount) :
    Equation T.edgeCount where
  coeff e := T.incidence v e
  rhs := T.charge v

/-- The finite set of all vertex equations, represented as singleton `Res(⊕)` clauses. -/
def ConcreteTseitin.axioms (T : ConcreteTseitin) : Finset (Clause T.edgeCount) :=
  Finset.univ.image fun v => {T.vertexEquation v}

theorem ConcreteTseitin.models_iff (T : ConcreteTseitin)
    (x : Fin T.edgeCount → ZMod 2) :
    Models x T.axioms ↔ ∀ v, SatisfiesEq x (T.vertexEquation v) := by
  constructor
  · intro h v
    have hv := h ({T.vertexEquation v} : Clause T.edgeCount)
      (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)
    simpa [SatisfiesClause] using hv
  · intro h C hC
    rw [ConcreteTseitin.axioms, Finset.mem_image] at hC
    rcases hC with ⟨v, _, rfl⟩
    exact ⟨T.vertexEquation v, Finset.mem_singleton_self _, h v⟩

/-- **Concrete Tseitin inconsistency.**  Summing all vertex equations cancels every edge column,
while the total charge is nonzero. -/
theorem ConcreteTseitin.unsatisfiable (T : ConcreteTseitin) :
    ¬ ∃ x : Fin T.edgeCount → ZMod 2, Models x T.axioms := by
  rintro ⟨x, hx⟩
  have hver : ∀ v, (∑ e, T.incidence v e * x e) = T.charge v := by
    intro v
    exact (T.models_iff x).mp hx v
  have hsum : (∑ v, ∑ e, T.incidence v e * x e) = ∑ v, T.charge v :=
    Finset.sum_congr rfl (fun v _ => hver v)
  have hleft : (∑ v, ∑ e, T.incidence v e * x e) = 0 := by
    rw [Finset.sum_comm]
    calc
      (∑ e, ∑ v, T.incidence v e * x e) =
          ∑ e, (∑ v, T.incidence v e) * x e := by
            apply Finset.sum_congr rfl
            intro e _
            rw [Finset.sum_mul]
      _ = 0 := by simp [T.evenColumns]
  apply T.oddCharge
  rw [← hsum, hleft]

/-- Edge boundary detected by odd incidence into a vertex set. -/
def ConcreteTseitin.boundary (T : ConcreteTseitin)
    (S : Finset (Fin T.vertexCount)) : Finset (Fin T.edgeCount) :=
  Finset.univ.filter fun e => (∑ v ∈ S, T.incidence v e) ≠ 0

/-- A checkable edge-expansion certificate attached to a concrete Tseitin instance. -/
structure TseitinExpansionCertificate (T : ConcreteTseitin) where
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator
  expands : ∀ S : Finset (Fin T.vertexCount), 2 * S.card ≤ T.vertexCount →
    denominator * S.card ≤ numerator * (T.boundary S).card

/-! ## Exact finite gadget lifting -/

/-- A Boolean block gadget. -/
structure BlockGadget where
  bits : ℕ
  bits_pos : 0 < bits
  eval : (Fin bits → ZMod 2) → ZMod 2

/-- Flatten block `e`, coordinate `j` into the lifted variable space. -/
def blockIndex (edgeCount : ℕ) {bits : ℕ} (_hbits : 0 < bits)
    (e : Fin edgeCount) (j : Fin bits) : Fin (edgeCount * bits) :=
  ⟨e.val * bits + j.val, by
    calc
      e.val * bits + j.val < e.val * bits + bits := Nat.add_lt_add_left j.isLt _
      _ = (e.val + 1) * bits := by ring
      _ ≤ edgeCount * bits := Nat.mul_le_mul_right bits (Nat.succ_le_iff.mpr e.isLt)⟩

/-- Apply a gadget independently to every edge block. -/
def gadgetOutput (T : ConcreteTseitin) (g : BlockGadget)
    (x : Fin (T.edgeCount * g.bits) → ZMod 2) : Fin T.edgeCount → ZMod 2 :=
  fun e => g.eval fun j => x (blockIndex T.edgeCount g.bits_pos e j)

/-- Literal `xᵢ ≠ aᵢ`, written over `𝔽₂` as the equation `xᵢ = 1 - aᵢ`. -/
def excludingLiteral {n : ℕ} (a : Fin n → ZMod 2) (i : Fin n) : Equation n :=
  unitEquation n i (1 - a i)

/-- The clause excluding exactly one complete assignment. -/
def excludeAssignment {n : ℕ} (a : Fin n → ZMod 2) : Clause n :=
  Finset.univ.image (excludingLiteral a)

theorem satisfiesEq_excludingLiteral_iff {n : ℕ}
    (x a : Fin n → ZMod 2) (i : Fin n) :
    SatisfiesEq x (excludingLiteral a i) ↔ x i = 1 - a i := by
  simp [SatisfiesEq, excludingLiteral, unitEquation]

theorem not_satisfies_excludeAssignment_self {n : ℕ} (a : Fin n → ZMod 2) :
    ¬ SatisfiesClause a (excludeAssignment a) := by
  rintro ⟨e, he, hsat⟩
  rw [excludeAssignment, Finset.mem_image] at he
  rcases he with ⟨i, _, rfl⟩
  rw [satisfiesEq_excludingLiteral_iff] at hsat
  exact (by decide : ∀ z : ZMod 2, z ≠ 1 - z) (a i) hsat

/-- Exact truth-table CNF for the block lift: include one exclusion clause for every lifted
assignment whose gadget output violates the base Tseitin axioms. -/
noncomputable def liftedAxioms (T : ConcreteTseitin) (g : BlockGadget) :
    Finset (Clause (T.edgeCount * g.bits)) :=
  (Finset.univ.filter fun a : Fin (T.edgeCount * g.bits) → ZMod 2 =>
      ¬ Models (gadgetOutput T g a) T.axioms).image excludeAssignment

/-- **Exact semantics of the finite lift.** -/
theorem models_liftedAxioms_iff (T : ConcreteTseitin) (g : BlockGadget)
    (x : Fin (T.edgeCount * g.bits) → ZMod 2) :
    Models x (liftedAxioms T g) ↔ Models (gadgetOutput T g x) T.axioms := by
  constructor
  · intro hlift
    by_contra hbad
    have hmem : excludeAssignment x ∈ liftedAxioms T g := by
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hbad⟩, rfl⟩
    exact not_satisfies_excludeAssignment_self x (hlift _ hmem)
  · intro hbase C hC
    rw [liftedAxioms, Finset.mem_image] at hC
    rcases hC with ⟨a, ha, rfl⟩
    have hbad : ¬ Models (gadgetOutput T g a) T.axioms := (Finset.mem_filter.mp ha).2
    have hne : x ≠ a := by
      intro hxa
      subst a
      exact hbad hbase
    have hcoord : ∃ i, x i ≠ a i := by
      by_contra hall
      push_neg at hall
      exact hne (funext hall)
    rcases hcoord with ⟨i, hi⟩
    have hcomp : x i = 1 - a i :=
      (by decide : ∀ u v : ZMod 2, u ≠ v → u = 1 - v) _ _ hi
    exact ⟨excludingLiteral a i,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
      (satisfiesEq_excludingLiteral_iff x a i).mpr hcomp⟩

theorem liftedAxioms_unsatisfiable (T : ConcreteTseitin) (g : BlockGadget) :
    ¬ ∃ x, Models x (liftedAxioms T g) := by
  rintro ⟨x, hx⟩
  exact T.unsatisfiable ⟨gadgetOutput T g x, (models_liftedAxioms_iff T g x).mp hx⟩

/-! ## A concrete recovery restriction -/

/-- Projection to the first coordinate of a nonempty block. -/
def projectionGadget (bits : ℕ) (hbits : 0 < bits) : BlockGadget where
  bits := bits
  bits_pos := hbits
  eval x := x ⟨0, hbits⟩

/-- Fix every non-leading coordinate of every block to zero, leaving its first bit free. -/
def projectionRestriction (T : ConcreteTseitin) (bits : ℕ) (hbits : 0 < bits) :
    Restriction (T.edgeCount * bits) :=
  fun k => if k.val % bits = 0 then none else some 0

/-- Read the surviving first coordinate of each block. -/
def firstBits (T : ConcreteTseitin) (bits : ℕ) (_hbits : 0 < bits)
    (x : Fin (T.edgeCount * bits) → ZMod 2) : Fin T.edgeCount → ZMod 2 :=
  fun e => x (blockIndex T.edgeCount hbits e ⟨0, hbits⟩)

theorem projectionRestriction_leaves_firstBits (T : ConcreteTseitin)
    (bits : ℕ) (hbits : 0 < bits) (x : Fin (T.edgeCount * bits) → ZMod 2) :
    gadgetOutput T (projectionGadget bits hbits)
        (complete (projectionRestriction T bits hbits) x) = firstBits T bits hbits x := by
  funext e
  simp [gadgetOutput, projectionGadget, complete, projectionRestriction, firstBits,
    blockIndex]

/-- **Deterministic restriction survival.**  Under the projection restriction, the lifted CNF is
satisfied exactly when the surviving first bits satisfy the original Tseitin instance. -/
theorem projectionRestriction_survival (T : ConcreteTseitin)
    (bits : ℕ) (hbits : 0 < bits) (x : Fin (T.edgeCount * bits) → ZMod 2) :
    Models x (restrictPremises (projectionRestriction T bits hbits)
        (liftedAxioms T (projectionGadget bits hbits))) ↔
      Models (firstBits T bits hbits x) T.axioms := by
  rw [models_restrictPremises_iff]
  exact (models_liftedAxioms_iff T (projectionGadget bits hbits) _).trans (by
    rw [projectionRestriction_leaves_firstBits])

/-! ## Concrete realization of the family interface -/

/-- Turn concrete Tseitin instances and gadgets into the exact family consumed by the lower-bound
interface. -/
noncomputable def concreteLiftedTseitinFamily
    (T : ℕ → ConcreteTseitin) (g : ℕ → BlockGadget) :
    LiftedTseitinFamily where
  variableCount m := (T m).edgeCount * (g m).bits
  baseVertices m := (T m).vertexCount
  gadgetBits m := (g m).bits
  axioms m := liftedAxioms (T m) (g m)
  unsatisfiable m := liftedAxioms_unsatisfiable (T m) (g m)

#print axioms ConcreteTseitin.unsatisfiable
#print axioms models_liftedAxioms_iff
#print axioms liftedAxioms_unsatisfiable
#print axioms projectionRestriction_survival
#print axioms concreteLiftedTseitinFamily

end PallLean.Paper93.DeepMath.PathB.ResLinParity
