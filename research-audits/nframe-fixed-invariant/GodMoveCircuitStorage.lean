import GodMoveSymbolicPinnedInput

/-!
# Explicit bit storage for Boolean circuits

The circuit semantics reads nonexistent wires as `false`. Sanitization folds
those reads into local Boolean operations, preserves every computed wire value,
and bounds all remaining references by the gate count. Each operation is stored
by its two- or four-bit truth table, rather than an opaque function object.
Constructor tags and unary indices give an explicit bit-list serialization
whose length is polynomial in input arity and gate count.

The results measure storage. They do not construct a compiler in the machine
model, or bound its runtime, polynomial normalization, or derivative ranks.
-/

namespace GodMoveCircuitStorage

open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer CookLevinEmit

/-- Every wire reference in a gate is below `B`. -/
def ReferencesBelow {n : ℕ} (B : ℕ) : CGate n → Prop
  | .var _ | .cst _ => True
  | .un _ j => j < B
  | .bin _ j k => j < B ∧ k < B

theorem ReferencesBelow.mono {n B C : ℕ} {g : CGate n}
    (h : ReferencesBelow B g) (hBC : B ≤ C) : ReferencesBelow C g := by
  cases g <;> simp only [ReferencesBelow] at * <;> omega

/-- Fold nonexistent wire reads into the gate's fixed Boolean truth table. -/
def sanitizeGate {n : ℕ} (pos : ℕ) : CGate n → CGate n
  | .var i => .var i
  | .cst b => .cst b
  | .un op j => if j < pos then .un op j else .cst (op false)
  | .bin op j k =>
      if j < pos then
        if k < pos then .bin op j k else .un (fun b => op b false) j
      else if k < pos then .un (op false) k else .cst (op false false)

theorem sanitizeGate_referencesBelow {n : ℕ} (pos : ℕ) (g : CGate n) :
    ReferencesBelow pos (sanitizeGate pos g) := by
  cases g with
  | var i => trivial
  | cst b => trivial
  | un op j =>
    by_cases hj : j < pos <;> simp [sanitizeGate, ReferencesBelow, hj]
  | bin op j k =>
    by_cases hj : j < pos <;> by_cases hk : k < pos <;>
      simp [sanitizeGate, ReferencesBelow, hj, hk]

theorem evalGate_sanitize {n : ℕ} (a : Fin n → Bool)
    (vals : List Bool) (g : CGate n) :
    evalGate a vals (sanitizeGate vals.length g) = evalGate a vals g := by
  cases g with
  | var i => rfl
  | cst b => rfl
  | un op j =>
    by_cases hj : j < vals.length <;> simp [sanitizeGate, evalGate, hj]
  | bin op j k =>
    by_cases hj : j < vals.length <;> by_cases hk : k < vals.length <;>
      simp [sanitizeGate, evalGate, hj, hk]

def sanitizeFrom {n : ℕ} : ℕ → List (CGate n) → List (CGate n)
  | _, [] => []
  | pos, g :: gs => sanitizeGate pos g :: sanitizeFrom (pos + 1) gs

def sanitize {n : ℕ} (c : List (CGate n)) : List (CGate n) := sanitizeFrom 0 c

@[simp] theorem sanitizeFrom_length {n : ℕ} (pos : ℕ) (c : List (CGate n)) :
    (sanitizeFrom pos c).length = c.length := by
  induction c generalizing pos with
  | nil => rfl
  | cons g gs ih => simp [sanitizeFrom, ih]

@[simp] theorem sanitize_length {n : ℕ} (c : List (CGate n)) :
    (sanitize c).length = c.length := sanitizeFrom_length 0 c

/-- Sanitization preserves the entire run, including shared/repeated reads. -/
theorem runFrom_sanitizeFrom {n : ℕ} (a : Fin n → Bool)
    (c : List (CGate n)) (vals : List Bool) :
    runFrom a vals (sanitizeFrom vals.length c) = runFrom a vals c := by
  induction c generalizing vals with
  | nil => rfl
  | cons g gs ih =>
    simp only [sanitizeFrom, runFrom, evalGate_sanitize]
    rw [show vals.length + 1 = (vals ++ [evalGate a vals g]).length by simp]
    exact ih _

theorem output_sanitize {n : ℕ} (c : List (CGate n)) (a : Fin n → Bool) :
    output (sanitize c) a = output c a := by
  unfold output
  rw [sanitize_length]
  exact congrArg (fun vals : List Bool => vals.getD (c.length - 1) false)
    (runFrom_sanitizeFrom a c [])

theorem sanitizeFrom_referencesBelow {n : ℕ} (pos : ℕ) (c : List (CGate n)) :
    ∀ g ∈ sanitizeFrom pos c, ReferencesBelow (pos + c.length) g := by
  induction c generalizing pos with
  | nil => simp [sanitizeFrom]
  | cons g gs ih =>
    intro q hq
    simp only [sanitizeFrom, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact (sanitizeGate_referencesBelow pos g).mono (by omega)
    · have h := ih (pos + 1) q hq
      convert h using 1
      simp [Nat.add_assoc, Nat.add_comm]

theorem sanitize_referencesBelow {n : ℕ} (c : List (CGate n)) :
    ∀ g ∈ sanitize c, ReferencesBelow c.length g := by
  simpa [sanitize] using sanitizeFrom_referencesBelow 0 c

/-- Two-bit constructor tags, finite truth tables, and self-delimiting unary
indices. The input arity `n` is the external type parameter of the codec. -/
def encodeGate {n : ℕ} : CGate n → List Bool
  | .var i => [false, false] ++ encodeNat i.val
  | .cst b => [false, true, b]
  | .un op j => [true, false, op false, op true] ++ encodeNat j
  | .bin op j k =>
      [true, true, op false false, op false true, op true false, op true true]
        ++ encodeNat j ++ encodeNat k

/-- Decode one gate at the known input arity, retaining the unread suffix. -/
def decodeGate (n : ℕ) : List Bool → Option (CGate n × List Bool)
  | false :: false :: bs =>
      let p := decodeNat bs
      if h : p.1 < n then some (.var ⟨p.1, h⟩, p.2) else none
  | false :: true :: b :: bs => some (.cst b, bs)
  | true :: false :: b₀ :: b₁ :: bs =>
      let p := decodeNat bs
      some (.un (fun b => if b then b₁ else b₀) p.1, p.2)
  | true :: true :: b₀₀ :: b₀₁ :: b₁₀ :: b₁₁ :: bs =>
      let p := decodeNat bs
      let q := decodeNat p.2
      some (.bin (fun b c => if b then (if c then b₁₁ else b₁₀)
        else (if c then b₀₁ else b₀₀)) p.1 q.1, q.2)
  | _ => none

theorem decodeGate_encodeGate {n : ℕ} (g : CGate n) (rest : List Bool) :
    decodeGate n (encodeGate g ++ rest) = some (g, rest) := by
  cases g with
  | var i => simp [encodeGate, decodeGate, decodeNat_encodeNat, i.isLt]
  | cst b => simp [encodeGate, decodeGate]
  | un op j =>
    have h : (fun b => if b then op true else op false) = op := by
      funext b
      cases b <;> rfl
    simp [encodeGate, decodeGate, decodeNat_encodeNat, h]
  | bin op j k =>
    have h : (fun b c => if b then (if c then op true true else op true false)
        else (if c then op false true else op false false)) = op := by
      funext b c
      cases b <;> cases c <;> rfl
    simp [encodeGate, decodeGate, List.append_assoc, decodeNat_encodeNat, h]

/-- Exact serialized bit cost, including operation truth-table entries. -/
def gateStorage {n : ℕ} : CGate n → ℕ
  | .var i => 3 + i.val
  | .cst _ => 3
  | .un _ j => 5 + j
  | .bin _ j k => 8 + j + k

theorem encodeGate_length {n : ℕ} (g : CGate n) :
    (encodeGate g).length = gateStorage g := by
  cases g <;> simp [encodeGate, gateStorage, encodeNat_length] <;> omega

theorem gateStorage_le {n B : ℕ} (g : CGate n) (h : ReferencesBelow B g) :
    gateStorage g ≤ 8 + 2 * (n + B) := by
  cases g with
  | var i => have hi := i.isLt; simp only [gateStorage]; omega
  | cst b => simp only [gateStorage]; omega
  | un op j => simp only [ReferencesBelow, gateStorage] at *; omega
  | bin op j k => simp only [ReferencesBelow, gateStorage] at *; omega

/-- The gate-count header makes the representation self-delimiting. -/
def encodeCircuit {n : ℕ} (c : List (CGate n)) : List Bool :=
  encodeNat c.length ++ (c.map encodeGate).flatten

def decodeGates (n : ℕ) : ℕ → List Bool → Option (List (CGate n) × List Bool)
  | 0, bs => some ([], bs)
  | m + 1, bs => do
      let (g, bs₁) ← decodeGate n bs
      let (gs, bs₂) ← decodeGates n m bs₁
      pure (g :: gs, bs₂)

def decodeCircuit (n : ℕ) (bs : List Bool) : Option (List (CGate n) × List Bool) :=
  let p := decodeNat bs
  decodeGates n p.1 p.2

theorem decodeGates_encode {n : ℕ} (c : List (CGate n)) (rest : List Bool) :
    decodeGates n c.length ((c.map encodeGate).flatten ++ rest) =
      some (c, rest) := by
  induction c with
  | nil => rfl
  | cons g gs ih =>
    simp [decodeGates, List.append_assoc, decodeGate_encodeGate, ih]

/-- The bit serialization recovers the exact typed circuit and suffix,
including the finite truth tables of every stored Boolean operation. -/
theorem decodeCircuit_encodeCircuit {n : ℕ} (c : List (CGate n)) (rest : List Bool) :
    decodeCircuit n (encodeCircuit c ++ rest) = some (c, rest) := by
  simp only [decodeCircuit, encodeCircuit, List.append_assoc, decodeNat_encodeNat]
  exact decodeGates_encode c rest

def circuitStorage {n : ℕ} (c : List (CGate n)) : ℕ :=
  c.length + 1 + (c.map gateStorage).sum

theorem encodeCircuit_length {n : ℕ} (c : List (CGate n)) :
    (encodeCircuit c).length = circuitStorage c := by
  simp only [encodeCircuit, circuitStorage, List.length_append, encodeNat_length,
    List.length_flatten, List.map_map]
  congr 2
  exact List.map_congr_left (fun g _ => encodeGate_length g)

theorem circuitStorage_le {n B : ℕ} (c : List (CGate n))
    (h : ∀ g ∈ c, ReferencesBelow B g) :
    circuitStorage c ≤ (9 + 2 * (n + B)) * c.length + 1 := by
  have hsum : (c.map gateStorage).sum ≤ c.length * (8 + 2 * (n + B)) := by
    calc
      _ ≤ (c.map gateStorage).length • (8 + 2 * (n + B)) := by
        apply List.sum_le_card_nsmul
        intro v hv
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
        exact gateStorage_le g (h g hg)
      _ = _ := by simp [smul_eq_mul]
  unfold circuitStorage
  nlinarith

/-- A concrete polynomial bound on serialized storage, with no unit-cost
assumption for arbitrary natural wire indices or Boolean operation objects. -/
theorem encodeCircuit_sanitize_length_le {n : ℕ} (c : List (CGate n)) :
    (encodeCircuit (sanitize c)).length ≤
      (9 + 2 * (n + c.length)) * c.length + 1 := by
  rw [encodeCircuit_length]
  have h := circuitStorage_le (sanitize c) (sanitize_referencesBelow c)
  simpa using h

end GodMoveCircuitStorage

#print axioms GodMoveCircuitStorage.evalGate_sanitize
#print axioms GodMoveCircuitStorage.runFrom_sanitizeFrom
#print axioms GodMoveCircuitStorage.output_sanitize
#print axioms GodMoveCircuitStorage.sanitize_referencesBelow
#print axioms GodMoveCircuitStorage.encodeGate_length
#print axioms GodMoveCircuitStorage.decodeGate_encodeGate
#print axioms GodMoveCircuitStorage.decodeCircuit_encodeCircuit
#print axioms GodMoveCircuitStorage.encodeCircuit_length
#print axioms GodMoveCircuitStorage.encodeCircuit_sanitize_length_le
