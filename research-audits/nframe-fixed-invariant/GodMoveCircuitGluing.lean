import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact gluing of shared-wire Boolean circuits

The left circuit is compiled once. Each interface input in the right circuit
becomes an identity gate reading its chosen existing left wire. Internal right
references are shifted by the left gate count. Thus the gate count is exactly
the sum of the two counts; neither shared wires nor assignments are expanded.

Correctness holds even for forward/out-of-range references, with the production
evaluator's default-false semantics. No runtime lower bound follows merely from
the existence of this composition.
-/

namespace GodMoveCircuitGluing

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {a b r off : ℕ}

/-- Relabel circuit inputs, retaining all internal shared references. -/
def renameGate (f : Fin a → Fin b) : CGate a → CGate b
  | .var i => .var (f i)
  | .cst v => .cst v
  | .un op j => .un op j
  | .bin op j k => .bin op j k

theorem evalGate_rename (f : Fin a → Fin b) (x : Fin b → Bool)
    (vals : List Bool) (g : CGate a) :
    evalGate x vals (renameGate f g) = evalGate (fun i => x (f i)) vals g := by
  cases g <;> rfl

theorem runFrom_rename (f : Fin a → Fin b) (x : Fin b → Bool)
    (vals : List Bool) (c : List (CGate a)) :
    runFrom x vals (c.map (renameGate f)) =
      runFrom (fun i => x (f i)) vals c := by
  induction c generalizing vals with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, runFrom, evalGate_rename, ih]

theorem runFrom_length (x : Fin a → Bool) (vals : List Bool)
    (c : List (CGate a)) :
    (runFrom x vals c).length = vals.length + c.length := by
  induction c generalizing vals with
  | nil => simp [runFrom]
  | cons g gs ih => simp [runFrom, ih, Nat.add_assoc, Nat.add_comm]

/-- Join interface bits and the independent right inputs. -/
def rightInput (u : Fin r → Bool) (v : Fin b → Bool) (i : Fin (r + b)) : Bool :=
  if h : i.val < r then u ⟨i.val, h⟩ else v ⟨i.val - r, by omega⟩

theorem rightInput_eq_append (u : Fin r → Bool) (v : Fin b → Bool) :
    rightInput u v = Fin.append u v := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [rightInput, j.isLt]
  · intro j
    rw [Fin.append_right]
    simp [rightInput, Fin.natAdd, Nat.not_lt.mpr (Nat.le_add_right r j.val)]

/-- The existing left wires selected as interface ports. Repeated ports are legal. -/
def wireValues (ports : Fin r → Fin off) (prior : List Bool) (i : Fin r) : Bool :=
  prior.getD (ports i).val false

/-- Rewire a right gate to existing left ports and offset its shared references. -/
def wireRight (ports : Fin r → Fin off) : CGate (r + b) → CGate (a + b)
  | .var i =>
      if h : i.val < r then .un id (ports ⟨i.val, h⟩).val
      else .var ⟨a + (i.val - r), by omega⟩
  | .cst v => .cst v
  | .un op j => .un op (off + j)
  | .bin op j k => .bin op (off + j) (off + k)

theorem evalGate_wireRight (ports : Fin r → Fin off) (x : Fin (a + b) → Bool)
    (prior vals : List Bool) (hlen : prior.length = off) (g : CGate (r + b)) :
    evalGate x (prior ++ vals) (wireRight ports g) =
      evalGate (rightInput (wireValues ports prior) (fun i => x (Fin.natAdd a i))) vals g := by
  cases g with
  | var i =>
      by_cases h : i.val < r
      · simp only [wireRight, h, dite_true, evalGate, id_eq, rightInput, wireValues]
        rw [List.getD_append prior vals false _ (by rw [hlen]; exact (ports ⟨i.val, h⟩).isLt)]
      · simp only [wireRight, h, dite_false, evalGate, rightInput]
        rfl
  | cst v => rfl
  | un op j =>
      simp only [wireRight, evalGate]
      rw [List.getD_append_right prior vals false _ (by omega), hlen, Nat.add_sub_cancel_left]
  | bin op j k =>
      simp only [wireRight, evalGate]
      rw [List.getD_append_right prior vals false (off + j) (by omega),
        List.getD_append_right prior vals false (off + k) (by omega), hlen,
        Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]

/-- Strong simulation: all right wire values agree, with the left wire prefix retained. -/
theorem runFrom_wireRight (ports : Fin r → Fin off) (x : Fin (a + b) → Bool)
    (prior vals : List Bool) (hlen : prior.length = off) (c : List (CGate (r + b))) :
    runFrom x (prior ++ vals) (c.map (wireRight ports)) =
      prior ++ runFrom
        (rightInput (wireValues ports prior) (fun i => x (Fin.natAdd a i))) vals c := by
  induction c generalizing vals with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.map_cons, runFrom, evalGate_wireRight ports x prior vals hlen]
      rw [List.append_assoc, ih]

/-- Compile both circuits once, connecting the chosen left wires to right input ports. -/
def glue (cL : List (CGate a)) (ports : Fin r → Fin cL.length)
    (cR : List (CGate (r + b))) : List (CGate (a + b)) :=
  cL.map (renameGate (Fin.castAdd b)) ++ cR.map (wireRight ports)

@[simp] theorem glue_length (cL : List (CGate a)) (ports : Fin r → Fin cL.length)
    (cR : List (CGate (r + b))) :
    (glue cL ports cR).length = cL.length + cR.length := by
  simp [glue]

/-- The computed interface depends only on the left input. -/
def portValues (cL : List (CGate a)) (ports : Fin r → Fin cL.length)
    (x : Fin a → Bool) : Fin r → Bool :=
  wireValues ports (runFrom x [] cL)

/-- Exact wire-trace decomposition through the computed interface. -/
theorem runFrom_glue (cL : List (CGate a)) (ports : Fin r → Fin cL.length)
    (cR : List (CGate (r + b))) (x : Fin (a + b) → Bool) :
    runFrom x [] (glue cL ports cR) =
      runFrom (fun i => x (Fin.castAdd b i)) [] cL ++
        runFrom (rightInput (portValues cL ports (fun i => x (Fin.castAdd b i)))
          (fun i => x (Fin.natAdd a i))) [] cR := by
  unfold glue
  rw [runFrom_append, runFrom_rename]
  have hlen : (runFrom (fun i => x (Fin.castAdd b i)) [] cL).length = cL.length := by
    simp [runFrom_length]
  simpa only [List.append_nil, portValues] using
    runFrom_wireRight ports x (runFrom (fun i => x (Fin.castAdd b i)) [] cL) [] hlen cR

/-- The right circuit computes the output from the actual left interface and its own inputs. -/
theorem output_glue (cL : List (CGate a)) (ports : Fin r → Fin cL.length)
    (cR : List (CGate (r + b))) (hR : cR ≠ []) (x : Fin (a + b) → Bool) :
    output (glue cL ports cR) x =
      output cR (rightInput (portValues cL ports (fun i => x (Fin.castAdd b i)))
        (fun i => x (Fin.natAdd a i))) := by
  have hpos : 0 < cR.length := List.length_pos_iff.mpr hR
  have hlen : (runFrom (fun i => x (Fin.castAdd b i)) [] cL).length = cL.length := by
    simp [runFrom_length]
  unfold output
  rw [runFrom_glue, glue_length]
  rw [List.getD_append_right _ _ false _ (by omega), hlen]
  congr 1
  omega

/-- Explicit two-input form, suitable for interface-matrix factorization. -/
theorem output_glue_append (cL : List (CGate a)) (ports : Fin r → Fin cL.length)
    (cR : List (CGate (r + b))) (hR : cR ≠ [])
    (x : Fin a → Bool) (y : Fin b → Bool) :
    output (glue cL ports cR) (Fin.append x y) =
      output cR (rightInput (portValues cL ports x) y) := by
  simpa only [Fin.append_left, Fin.append_right] using
    output_glue cL ports cR hR (Fin.append x y)

/-- One left wire can supply both ports without duplicating the left circuit. -/
def sharedExampleLeft : List (CGate 1) := [.var 0]

def sharedExamplePorts : Fin 2 → Fin sharedExampleLeft.length := fun _ => ⟨0, by decide⟩

def sharedExampleRight : List (CGate (2 + 1)) :=
  [.var 0, .var 1, .bin Bool.and 0 1, .var 2, .bin Bool.xor 2 3]

example : (glue sharedExampleLeft sharedExamplePorts sharedExampleRight).length = 6 := by decide

example : output (glue sharedExampleLeft sharedExamplePorts sharedExampleRight)
    (fun _ => true) = false := by decide

example : output (glue sharedExampleLeft sharedExamplePorts sharedExampleRight)
    (fun i => i.val == 0) = true := by decide

end GodMoveCircuitGluing

#print axioms GodMoveCircuitGluing.runFrom_rename
#print axioms GodMoveCircuitGluing.runFrom_length
#print axioms GodMoveCircuitGluing.evalGate_wireRight
#print axioms GodMoveCircuitGluing.runFrom_wireRight
#print axioms GodMoveCircuitGluing.glue_length
#print axioms GodMoveCircuitGluing.runFrom_glue
#print axioms GodMoveCircuitGluing.output_glue
#print axioms GodMoveCircuitGluing.output_glue_append
