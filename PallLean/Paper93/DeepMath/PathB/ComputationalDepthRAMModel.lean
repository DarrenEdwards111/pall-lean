import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostModel
import Mathlib.Tactic

/-!
# RAM machine model — core semantics (PROVED)

The bit-cost efficiency of the flat memo DP (`bitBounded_efficient`) is a *RAM* cost — it assumes addressable
memory — and the Kleene `Code` model cannot host it (everything is one `Nat`, which blows up;
`ComputationalDepthBitHierarchyFuelDom`).  This file starts a genuine RAM machine model in which the memo
table lives in addressable memory, so building it costs only polynomially many *bits*.

Core: `Mem = ℕ → ℕ` (addressable memory), a minimal accumulator ISA with **indirect addressing**
(`loadIndI`/`storeIndI` — the power `Code` lacks), `step` (single-step semantics), `run` (iterate).  The
example confirms store-indirect writes through an address held in memory.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- Addressable memory: address → value. -/
abbrev Mem := ℕ → ℕ

/-- Point update of memory. -/
def Mem.set (m : Mem) (a v : ℕ) : Mem := fun a' => if a' = a then v else m a'

@[simp] theorem Mem.set_get_eq (m : Mem) (a v : ℕ) : (m.set a v) a = v := by simp [Mem.set]
@[simp] theorem Mem.set_get_ne (m : Mem) (a v a' : ℕ) (h : a' ≠ a) : (m.set a v) a' = m a' := by
  simp [Mem.set, h]

/-- A minimal accumulator-RAM instruction set with **indirect addressing** (the key power `Code` lacks). -/
inductive Instr
  | constI (v : ℕ)      -- acc := v
  | loadI (a : ℕ)       -- acc := mem[a]
  | storeI (a : ℕ)      -- mem[a] := acc
  | loadIndI (a : ℕ)    -- acc := mem[mem[a]]      (addressable indirection)
  | storeIndI (a : ℕ)   -- mem[mem[a]] := acc
  | addI (a : ℕ)        -- acc := acc + mem[a]
  | subI (a : ℕ)        -- acc := acc - mem[a]
  | jzI (t : ℕ)         -- if acc = 0 then pc := t else pc := pc+1
  | jmpI (t : ℕ)        -- pc := t
  | haltI               -- stop
  deriving Repr, DecidableEq

/-- Machine configuration. -/
structure State where
  mem : Mem
  acc : ℕ
  pc : ℕ
  halted : Bool

/-- Single-step semantics.  Out-of-range `pc` halts (default instruction `haltI`). -/
def step (prog : List Instr) (s : State) : State :=
  if s.halted then s else
  match prog.getD s.pc Instr.haltI with
  | .constI v    => { s with acc := v, pc := s.pc + 1 }
  | .loadI a     => { s with acc := s.mem a, pc := s.pc + 1 }
  | .storeI a    => { s with mem := s.mem.set a s.acc, pc := s.pc + 1 }
  | .loadIndI a  => { s with acc := s.mem (s.mem a), pc := s.pc + 1 }
  | .storeIndI a => { s with mem := s.mem.set (s.mem a) s.acc, pc := s.pc + 1 }
  | .addI a      => { s with acc := s.acc + s.mem a, pc := s.pc + 1 }
  | .subI a      => { s with acc := s.acc - s.mem a, pc := s.pc + 1 }
  | .jzI t       => { s with pc := if s.acc = 0 then t else s.pc + 1 }
  | .jmpI t      => { s with pc := t }
  | .haltI       => { s with halted := true }

/-- Run `n` steps. -/
def run (prog : List Instr) (s : State) : ℕ → State
  | 0 => s
  | k + 1 => run prog (step prog s) k

theorem run_succ (prog : List Instr) (s : State) (k : ℕ) :
    run prog s (k + 1) = run prog (step prog s) k := rfl

/-- A halted state is a fixed point of `step`. -/
theorem step_halted (prog : List Instr) (s : State) (h : s.halted = true) : step prog s = s := by
  unfold step; rw [if_pos h]

/-- Sanity: store-indirect writes through an address held in memory. -/
example (m : Mem) :
    (step [Instr.storeIndI 0] (⟨m.set 0 5, 7, 0, false⟩ : State)).mem 5 = 7 := by
  simp [step, List.getD]

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.step
