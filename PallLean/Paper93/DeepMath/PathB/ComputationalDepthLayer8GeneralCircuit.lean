import Mathlib.Data.Fintype.Card

/-!
# Layer 8 (general circuits, R0) — the general fan-in-`≤2` Boolean circuit model

Infrastructure for `SCOPE_LAYER8_GENERAL_CIRCUITS.md`: a general (unrestricted-depth) Boolean circuit
model — the model underlying `P/poly` — with a **finite gate set** (so size-bounded circuits are
countable, which the Shannon counting bound R1 needs).

**No lower bound is claimed in this file.**  It defines the model, evaluation, size, the `Computes`
relation, and the nonuniform class `SIZE n s`.  The honest first *theorem* (R1, Shannon counting) lives in
a later file; the *explicit* super-polynomial frontier is open and fenced in the scope doc.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer8

/-- A **general Boolean circuit** on `n` inputs: fan-in-`≤2` gates over the finite basis
`{input, const, ¬, ∧, ∨}`, arbitrary depth.  (Finite gate set ⇒ `DecidableEq` ⇒ countable, unlike the
unbounded-fan-in `BoolCircuitSyntax`.) -/
inductive Circuit (n : ℕ) : Type
  | input : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n
  deriving DecidableEq

namespace Circuit

/-- The Boolean function computed by a circuit. -/
def eval {n : ℕ} : Circuit n → (Fin n → Bool) → Bool
  | input i, x => x i
  | const b, _ => b
  | not c, x => !(c.eval x)
  | and c d, x => (c.eval x) && (d.eval x)
  | or c d, x => (c.eval x) || (d.eval x)

/-- Circuit **size**: the number of gates/leaves. -/
def size {n : ℕ} : Circuit n → ℕ
  | input _ => 1
  | const _ => 1
  | not c => c.size + 1
  | and c d => c.size + d.size + 1
  | or c d => c.size + d.size + 1

theorem one_le_size {n : ℕ} (c : Circuit n) : 1 ≤ c.size := by
  cases c <;> simp [size] <;> omega

end Circuit

/-- `c` **computes** the Boolean function `f`: they agree on every input. -/
def Computes {n : ℕ} (c : Circuit n) (f : (Fin n → Bool) → Bool) : Prop := ∀ x, c.eval x = f x

/-- The nonuniform class **`SIZE n s`**: functions computed by some size-`≤ s` circuit on `n` inputs. -/
def SIZE (n s : ℕ) : Set ((Fin n → Bool) → Bool) :=
  { f | ∃ c : Circuit n, c.size ≤ s ∧ Computes c f }

/-- Constants are in `SIZE n 1`. -/
theorem const_mem_SIZE (n : ℕ) (b : Bool) : (fun _ => b) ∈ SIZE n 1 :=
  ⟨Circuit.const b, le_refl _, fun _ => rfl⟩

end PallLean.Paper93.DeepMath.PathB.Layer8

#print axioms PallLean.Paper93.DeepMath.PathB.Layer8.Circuit.eval
#print axioms PallLean.Paper93.DeepMath.PathB.Layer8.SIZE
