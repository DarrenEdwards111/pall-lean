import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposablePpolyDischarge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniformityGapDiagonal

/-!
# The uniformity gap, NAMED — and proved strict: `P ⊊ P/poly` in the faithful model

"Gap = uniformity" has been a phrase in the corpus notes; this file makes it a pair of
theorem-shaped objects and proves the strictness that justifies the phrase.

## The two targets, side by side

* `NonUniformSATTarget` — `∀ k, ∃ n, n^k + k < cbudget (SATFamily n)`: the circuit
  route's one open statement (`SAT ∉ P/poly`-strength, against ALL circuit families).
* `UniformSATTarget` — `SAT_not_in_P` (`¬ InP SATLang`): the actual separation target
  (`P ≠ NP`), against machine-generated circuit families only.

`nonuniform_implies_uniform` (via the discharged `composableP_subset_Ppoly`) is the
one-way street between them.

## The gap is STRICT (the new content)

`uniformity_gap_strict`: there is a language whose fixed-length slices have CONSTANT
circuit budget (`cbudget ≤ 1` per slice — one `cst` gate) yet which lies outside the
faithful uniform `P`.  The witness is a length language `lengthLang A` from the Cantor
diagonal of `UniformityGapDiagonal`; its slices are constant functions
(`lengthSlice_lengthLang`), and constants are one-gate circuits (`cbudget_const_le_one`).

Combined with the discharged simulation, `capture_inclusion_strict` states both halves
in one place: the faithful `P` sits STRICTLY inside the non-uniform `PolyCBudget`
capture — `P ⊊ P/poly`, machine-checked against this repository's actual `cbudget` and
`InP`, not abstract stand-ins.

## Honest scope

The strictness is the classic advice/countability separation (folklore); the value is
that the corpus's uniformity gap is now a NAMED, PROVED object: the uniform target
demands strictly less than the non-uniform target, and the difference is inhabited.
It does NOT make the uniform target easier to prove by itself — it locates it: proving
`UniformSATTarget` may exploit uniformity (enumeration, hierarchy theorems — see
`IndirectDiagonalization` for the engine), which `NonUniformSATTarget` cannot.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniformityGapNamed

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal
open PallLean.Paper93.DeepMath.PathB.ComposablePpolyDischarge

/-! ### Constant slices are one-gate circuits -/

/-- A constant function is computed by the single gate `[cst b]`. -/
theorem cbudget_const_le_one (n : ℕ) (b : Bool) :
    cbudget (fun _ : Fin n → Bool => b) ≤ 1 := by
  apply Nat.sInf_le
  exact ⟨[CGate.cst b], fun _ => rfl, rfl⟩

/-- The fixed-length slices of a length language are constant functions. -/
theorem lengthSlice_lengthLang (A : ℕ → Bool) (n : ℕ) :
    lengthSlice (lengthLang A) n = fun _ : Fin n → Bool => A n := by
  funext x
  show A (wordOfFin x).length = A n
  rw [wordOfFin_length]

/-- Every length language has polynomially bounded slice budget — indeed constant:
one gate per slice. -/
theorem polyCBudget_lengthLang (A : ℕ → Bool) :
    PolyCBudget (lengthSlice (lengthLang A)) := by
  refine ⟨1, fun n => ?_⟩
  rw [lengthSlice_lengthLang]
  have h1 : cbudget (fun _ : Fin n → Bool => A n) ≤ 1 := cbudget_const_le_one n (A n)
  have h2 : 1 ≤ n ^ 1 + 1 := by rw [Nat.pow_one]; omega
  omega

/-! ### The strictness -/

/-- **The uniformity gap is strict.**  Some language has polynomial (constant!) circuit
budget on every slice yet is outside the faithful uniform `P`: non-uniform capture does
NOT imply uniform capture. -/
theorem uniformity_gap_strict :
    ∃ L : List Bool → Bool, PolyCBudget (lengthSlice L) ∧ ¬ InP L := by
  obtain ⟨A, hA⟩ := exists_lengthLang_not_inP
  exact ⟨lengthLang A, polyCBudget_lengthLang A, hA⟩

/-- **`P ⊊ P/poly` in the faithful model**: the discharged simulation gives the
inclusion, the diagonal gives its strictness — both halves in one statement, against
the repository's actual `InP` and `cbudget`. -/
theorem capture_inclusion_strict :
    (∀ L : List Bool → Bool, InP L → PolyCBudget (lengthSlice L)) ∧
      (∃ L : List Bool → Bool, PolyCBudget (lengthSlice L) ∧ ¬ InP L) :=
  ⟨fun L hL => composableP_subset_Ppoly L hL, uniformity_gap_strict⟩

/-! ### The two targets, named -/

/-- **The non-uniform target** (the circuit route's one open statement): the SAT slices
have super-polynomial circuit budget — a bound against ALL circuit families. -/
def NonUniformSATTarget : Prop := ∀ k, ∃ n, n ^ k + k < cbudget (SATFamily n)

/-- **The uniform target** (the actual separation): `SAT ∉ P` for the faithful machine
model — a bound against machine-generated circuit families only. -/
def UniformSATTarget : Prop :=
  PallLean.Paper93.DeepMath.PathB.SeparationTarget.SAT_not_in_P

/-- The `InP` of the separation target and the `InP` of the machine corpus are the same
proposition (both are `∃ M T, PolyBounded T ∧ Decides M L T`). -/
theorem target_inP_iff (L : List Bool → Bool) :
    PallLean.Paper93.DeepMath.PathB.SeparationTarget.InP L ↔ InP L := Iff.rfl

/-- **The one-way street**: the non-uniform target implies the uniform one, through
the discharged `P ⊆ P/poly` simulation.  `uniformity_gap_strict` is exactly why no
converse of this kind is available: the inclusion it rides is strict. -/
theorem nonuniform_implies_uniform : NonUniformSATTarget → UniformSATTarget :=
  fun hard => sat_superpoly_cbudget_implies_SAT_not_in_P hard

end PallLean.Paper93.DeepMath.PathB.UniformityGapNamed

#print axioms PallLean.Paper93.DeepMath.PathB.UniformityGapNamed.uniformity_gap_strict
#print axioms PallLean.Paper93.DeepMath.PathB.UniformityGapNamed.capture_inclusion_strict
#print axioms PallLean.Paper93.DeepMath.PathB.UniformityGapNamed.nonuniform_implies_uniform
