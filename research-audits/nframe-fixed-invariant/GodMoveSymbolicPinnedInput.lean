import GodMovePinnedSATQueries
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWireTreeCircuit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATCircuitSeparationBridge

/-!
# Symbolic pinned input without assignment enumeration

The coordinate codec places a literal's sign in one bit.  Hence an entire
assignment-pinned SAT query can be written once as a list of constants and
assignment variables. Its length is independent of the assignment, with
quadratic overhead in the number of pinned variables. Substituting these
closed gates for a circuit's input gates preserves every wire value and the
gate count, including all sharing and rereading of intermediate wires.

These are representation and Boolean semantics results. They do not bound
the derivative rank of an arithmetized circuit or the cost of multilinearizing
its output.
-/

namespace GodMoveSymbolicPinnedInput

open GodMovePinnedSATQueries
open PallLean.Paper93.DeepMath.PathB
open CookLevinReduction CookLevinEmit CookLevinEmitCodec NFrameBoundaryTransducer

/-- The encoded unit clause fixing variable `i`, with its sign left symbolic. -/
def unitTemplate {n : ℕ} (i : Fin n) : List (CGate n) :=
  (encodeNat 1 ++ encodeVar' i.val).map CGate.cst ++ [CGate.var i]

/-- One symbolic input template for every assignment-pinned query of `φ`.
Only `n` variables are traversed; no list of the `2^n` assignments is used. -/
def inputTemplate (φ : Formula) (n : ℕ) : List (CGate n) :=
  (encodeNat (φ.length + n) ++ (φ.map encodeClause').flatten).map CGate.cst
    ++ ((List.finRange n).map unitTemplate).flatten

theorem unitTemplate_closed {n : ℕ} (i : Fin n) :
    ∀ g ∈ unitTemplate i, IsClosedGate g := by
  intro g hg
  simp only [unitTemplate, List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with ⟨b, _, rfl⟩ | rfl <;> trivial

theorem inputTemplate_closed (φ : Formula) (n : ℕ) :
    ∀ g ∈ inputTemplate φ n, IsClosedGate g := by
  intro g hg
  simp only [inputTemplate, List.mem_append, List.mem_map, List.mem_flatten] at hg
  rcases hg with ⟨b, _, rfl⟩ | ⟨gs, ⟨i, _, rfl⟩, hg⟩
  · trivial
  · exact unitTemplate_closed i g hg

theorem unitTemplate_eval {n : ℕ} (a : Fin n → Bool) (i : Fin n) :
    (unitTemplate i).map (closedEval a) = encodeClause' [(i.val, a i)] := by
  simp [unitTemplate, encodeClause', encodeLit', List.map_map, Function.comp_def, closedEval]

/-- The symbolic template evaluates to the actual faithful input encoding. -/
theorem inputTemplate_eval {n : ℕ} (φ : Formula) (a : Fin n → Bool) :
    (inputTemplate φ n).map (closedEval a) = encodeFormula' (pinnedFormula φ a) := by
  simp [inputTemplate, List.map_flatten, List.map_map, Function.comp_def,
    closedEval, unitTemplate_eval, encodeFormula', pinnedFormula, assignmentUnits,
    List.append_assoc]

theorem unitTemplate_length {n : ℕ} (i : Fin n) :
    (unitTemplate i).length = (encodeVar' i.val).length + 3 := by
  simp only [unitTemplate, List.length_append, List.length_map, encodeNat_length,
    List.length_singleton]
  omega

theorem unitTemplate_length_le {n : ℕ} (i : Fin n) :
    (unitTemplate i).length ≤ 2 * n + 8 := by
  have h := encodeVar'_length_le i.val n (Nat.le_of_lt i.isLt)
  rw [unitTemplate_length]
  omega

theorem inputTemplate_length (φ : Formula) (n : ℕ) :
    (inputTemplate φ n).length = (encodeFormula' φ).length + n
      + (((List.finRange n).map unitTemplate).map List.length).sum := by
  simp only [inputTemplate, encodeFormula', List.length_append, List.length_map,
    List.length_flatten, encodeNat_length]
  omega

/-- Explicit polynomial overhead relative to the original encoded formula. -/
theorem inputTemplate_length_le (φ : Formula) (n : ℕ) :
    (inputTemplate φ n).length ≤ (encodeFormula' φ).length + n * (2 * n + 9) := by
  have hsum : ((((List.finRange n).map unitTemplate).map List.length).sum)
      ≤ n * (2 * n + 8) := by
    calc
      _ ≤ ((((List.finRange n).map unitTemplate).map List.length).length)
          • (2 * n + 8) := by
        apply List.sum_le_card_nsmul
        intro l hl
        obtain ⟨gs, hgs, rfl⟩ := List.mem_map.mp hl
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hgs
        exact unitTemplate_length_le i
      _ = _ := by simp [smul_eq_mul]
  rw [inputTemplate_length]
  nlinarith

/-- All pinning assignments have exactly the same machine input length. -/
theorem encoded_pinned_length {n : ℕ} (φ : Formula) (a : Fin n → Bool) :
    (encodeFormula' (pinnedFormula φ a)).length = (inputTemplate φ n).length := by
  rw [← inputTemplate_eval φ a, List.length_map]

/-- Substitute closed input gates while retaining every internal wire index. -/
def specializeGate {m n : ℕ} (σ : Fin m → CGate n) : CGate m → CGate n
  | .var i => σ i
  | .cst b => .cst b
  | .un op j => .un op j
  | .bin op j k => .bin op j k

def specializeCircuit {m n : ℕ} (σ : Fin m → CGate n)
    (c : List (CGate m)) : List (CGate n) := c.map (specializeGate σ)

@[simp] theorem specializeCircuit_length {m n : ℕ} (σ : Fin m → CGate n)
    (c : List (CGate m)) : (specializeCircuit σ c).length = c.length := by
  simp [specializeCircuit]

theorem evalGate_specialize {m n : ℕ} (σ : Fin m → CGate n)
    (hσ : ∀ i, IsClosedGate (σ i)) (a : Fin n → Bool) (vals : List Bool)
    (g : CGate m) :
    evalGate a vals (specializeGate σ g) =
      evalGate (fun i => closedEval a (σ i)) vals g := by
  cases g with
  | var i =>
    have h := hσ i
    cases hs : σ i <;> simp_all [specializeGate, evalGate, closedEval, IsClosedGate]
  | cst b => rfl
  | un op j => rfl
  | bin op j k => rfl

/-- Specialization preserves the complete sequence of computed wire values. -/
theorem runFrom_specialize {m n : ℕ} (σ : Fin m → CGate n)
    (hσ : ∀ i, IsClosedGate (σ i)) (a : Fin n → Bool)
    (c : List (CGate m)) (vals : List Bool) :
    runFrom a vals (specializeCircuit σ c) =
      runFrom (fun i => closedEval a (σ i)) vals c := by
  induction c generalizing vals with
  | nil => rfl
  | cons g gs ih =>
    simp only [specializeCircuit, List.map_cons, runFrom]
    rw [evalGate_specialize σ hσ]
    exact ih _

theorem output_specialize {m n : ℕ} (σ : Fin m → CGate n)
    (hσ : ∀ i, IsClosedGate (σ i)) (a : Fin n → Bool)
    (c : List (CGate m)) :
    output (specializeCircuit σ c) a =
      output c (fun i => closedEval a (σ i)) := by
  simp only [output, specializeCircuit_length, runFrom_specialize σ hσ]

/-- The closed-gate input substitution consumed by a simulated machine circuit. -/
def pinnedSubstitution (φ : Formula) (n : ℕ) :
    Fin (inputTemplate φ n).length → CGate n := (inputTemplate φ n).get

theorem pinnedSubstitution_closed (φ : Formula) (n : ℕ)
    (i : Fin (inputTemplate φ n).length) :
    IsClosedGate (pinnedSubstitution φ n i) :=
  inputTemplate_closed φ n _ (List.get_mem _ _)

theorem pinnedSubstitution_wordOfFin {n : ℕ} (φ : Formula) (a : Fin n → Bool) :
    SATCircuitSeparationBridge.wordOfFin
      (fun i => closedEval a (pinnedSubstitution φ n i)) =
      encodeFormula' (pinnedFormula φ a) := by
  change (List.finRange (inputTemplate φ n).length).map
    ((closedEval a) ∘ (inputTemplate φ n).get) = _
  rw [← List.map_map, List.map_get_finRange]
  exact inputTemplate_eval φ a

end GodMoveSymbolicPinnedInput

#print axioms GodMoveSymbolicPinnedInput.inputTemplate_closed
#print axioms GodMoveSymbolicPinnedInput.inputTemplate_eval
#print axioms GodMoveSymbolicPinnedInput.inputTemplate_length_le
#print axioms GodMoveSymbolicPinnedInput.encoded_pinned_length
#print axioms GodMoveSymbolicPinnedInput.runFrom_specialize
#print axioms GodMoveSymbolicPinnedInput.output_specialize
#print axioms GodMoveSymbolicPinnedInput.specializeCircuit_length
#print axioms GodMoveSymbolicPinnedInput.pinnedSubstitution_wordOfFin
