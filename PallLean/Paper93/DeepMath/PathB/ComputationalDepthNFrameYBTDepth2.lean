import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameYBTCompiler

/-!
# Discharging the depth-2 `MOD∘AND` `YBTCompiler` instance

The `YBTCompiler` interface isolates the open problem to a single structure instance.  This file **discharges** the
first real case: depth-2 `MOD∘AND` circuits — a `MOD_m` gate over `AND` gates.

The key fact: a `MOD` gate is **symmetric** (a function of the *count* of accepting sub-gates), so a depth-2 `MOD∘AND`
circuit is *already* `SYM∘AND` — no arithmetisation, no root of unity, no characteristic condition.  The compilation is
therefore exact and definitional:

  `ModAndCircuit n size` — a depth-2 `MOD_m∘AND` circuit: `m ≤ size` monomial-`AND` gates under a `MOD_modulus` residue
        top `[· ≡ residue mod modulus]`.
  `ModAndCircuit.eval` — its semantics: `[#(satisfied AND gates) ≡ residue mod modulus]`.
  `modAnd_ybtCompiler` — **the discharged instance (proved)**: a `YBTCompiler` for `ModAndCircuit`, `exact := rfl` (the
        `MOD` residue *is* the symmetric top over the `AND`-count).
  `modAnd_fastSATModel` / `modAnd_fastSATSpeedup` — the fast-SAT model and speedup, via the proved bridge.

## Honest scope — and where the barrier really is

This discharges depth-2 `MOD∘AND` for **any** modulus — prime, prime-power, *or composite*.  A single `MOD` gate is
symmetric, so no `char`/prime-power condition is needed here.  That pins down the real location of the composite-`MOD`
barrier: it is **not** a single `MOD` gate, but the composition of *different-modulus* `MOD` gates across depth `> 2`
(the `MOD_6 = MOD_2 ∘ ⋯ ∘ MOD_3` linearisation), where a single symmetric count no longer captures the circuit and the
`YBTCompiler` instance becomes the open classical theorem.  So: depth-2 `MOD∘AND` — discharged (this file, any modulus);
depth `> 2` mixed composite `MOD` — the standing open rung.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (symEval gateCount)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup (Satisfiable)

attribute [local instance] Classical.propDecidable

/-- A depth-2 `MOD_m∘AND` circuit over `n` bits with size budget `size`: `m ≤ size` monomial-`AND` gates under a
`MOD_modulus` residue top. -/
structure ModAndCircuit (n size : ℕ) where
  m : ℕ
  hm : m ≤ size
  ands : Fin m → Finset (Fin n)
  modulus : ℕ
  residue : ℕ

/-- Semantics of a depth-2 `MOD∘AND` circuit: the number of satisfied `AND` gates is `≡ residue (mod modulus)`. -/
def ModAndCircuit.eval {n size : ℕ} (C : ModAndCircuit n size) (x : Fin n → Bool) : Bool :=
  decide ((∑ j : Fin C.m, if monoAND (C.ands j) x then 1 else 0) % C.modulus = C.residue)

/-- **The discharged instance (proved)**: a depth-2 `MOD∘AND` circuit family is a `YBTCompiler` — the `MOD` residue *is*
the symmetric top over the `AND`-gate count, so the exact `SYM∘AND` form holds by definition (`exact := rfl`). -/
def modAnd_ybtCompiler (n size k : ℕ) (hkn : k ≤ n) (hfit : size + 1 ≤ 2 ^ (n - k)) :
    YBTCompiler n (ModAndCircuit n size) ModAndCircuit.eval where
  size C := C.m
  gates C := fun j x => monoAND (C.ands j) x
  top C := fun c => decide (c % C.modulus = C.residue)
  exact _ := rfl
  budget := k
  budget_le := hkn
  size_fit C := le_trans (Nat.succ_le_succ C.hm) hfit

/-- The fast-SAT model for depth-2 `MOD∘AND`, obtained from the discharged compiler through the proved bridge. -/
noncomputable def modAnd_fastSATModel (n size k : ℕ) (hkn : k ≤ n) (hfit : size + 1 ≤ 2 ^ (n - k)) :
    FastSATModel n (ModAndCircuit n size) (fun C => decide (Satisfiable (ModAndCircuit.eval C))) :=
  ybtCompiler_fastSATModel (modAnd_ybtCompiler n size k hkn hfit)

/-- **Depth-2 `MOD∘AND` has an N-Frame fast-SAT speedup (proved)** — a real `ACC⁰` subclass discharged into the Williams
pivot, with the savings `2^k · fastSatWork m ≤ 2^n`. -/
theorem modAnd_fastSATSpeedup (n size k : ℕ) (hkn : k ≤ n) (hfit : size + 1 ≤ 2 ^ (n - k)) :
    NFrameFastSATSpeedup n (ModAndCircuit n size) (fun C => decide (Satisfiable (ModAndCircuit.eval C))) :=
  ⟨modAnd_fastSATModel n size k hkn hfit⟩

/-- A concrete **prime-power** `MOD_{p^e}∘AND` circuit — the case the ladder called out.  (No prime-power hypothesis is
needed for the compilation itself; a single `MOD` gate is symmetric for any modulus.) -/
def mkPrimePowerModAnd {n size : ℕ} (p e : ℕ) (m : ℕ) (hm : m ≤ size)
    (ands : Fin m → Finset (Fin n)) (residue : ℕ) : ModAndCircuit n size :=
  { m := m, hm := hm, ands := ands, modulus := p ^ e, residue := residue }

end PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.modAnd_ybtCompiler
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.modAnd_fastSATSpeedup
