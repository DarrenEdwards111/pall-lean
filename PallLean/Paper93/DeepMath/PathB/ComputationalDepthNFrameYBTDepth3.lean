import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameYBTDepth2

/-!
# The depth-3 `MOD∘MOD∘AND` rung — and exactly where the prime-power arithmetisation fires

Depth-3: a `MOD_{p^e}` top over depth-2 `MOD_b∘AND` middle gates.  This file builds the circuit class over the
already-discharged `ModAndCircuit` (depth-2) and discharges its `YBTCompiler` — in the repo's **count-cell observer
model**.

  `Depth3Circuit n size sizeMid` — `MOD_{topMod}` over `m ≤ size` middle `ModAndCircuit` (depth-2 `MOD∘AND`) gates.
  `Depth3Circuit.eval` — `[#(accepting middle gates) ≡ topRes mod topMod]`.
  `depth3_ybtCompiler` — **the discharged `YBTCompiler` (proved, `exact := rfl`)**: the top `MOD` is symmetric over the
        *middle-gate count*, so the observer form holds by definition.
  `depth3_fastSATModel` / `depth3_fastSATSpeedup` — the fast-SAT model + speedup via the bridge.

## The honest scope — where the arithmetisation *actually* fires (correcting the naïve expectation)

A subtlety worth stating plainly: **in the count-cell observer model, the arithmetisation does *not* need to fire at
depth 3.**  A `MOD` gate is symmetric over the layer *directly below it*, so `MOD_{p^e} ∘ (middle gates)` is observed by
the middle-gate count for *any* top modulus — exactly as depth-2 was (`…YBTDepth2`).  The `exact := rfl` here is the same
symmetry, one level up.

The prime-power arithmetisation becomes load-bearing at a *different* place: to make this a **true Williams speedup** the
cell count must be over the **bottom `AND` gates** (a genuine quasipolynomial `SYM∘AND`), not over the middle gates —
because per-cell achievability must be structured/cheap.  Reaching bottom-`AND` cells requires *flattening the middle
`MOD_b∘AND` layer into a low-degree sum of monomial-`AND`s* — and that is the Razborov–Smolensky / Beigel–Tarui
arithmetisation: over `F_p`, a `MOD_p∘AND` gate is `1 − (∑ AND)^{p−1}`, a degree-`(p−1)` polynomial (C15's Fermat form),
which on the cube is an exact monomial-`AND` family.  **That flattening is dischargeable exactly for prime-power `MOD`
matched to the field characteristic**, and fails for a middle modulus coprime to the characteristic — the C14/C15/C16
barrier, one layer down.

So: depth-3 discharges *in the observer model* for any top modulus (this file); the *true* depth-reduction — flatten to
bottom-`AND` cells — is the prime-power arithmetisation step, load-bearing for prime-power, open for composite middle
moduli.  The composite barrier is now localised to the *middle-layer flattening*, not the top gate.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (symEval gateCount)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup (Satisfiable)

attribute [local instance] Classical.propDecidable

/-- A depth-3 `MOD_{topMod} ∘ (MOD∘AND)` circuit: a `MOD` top over `m ≤ size` depth-2 `MOD∘AND` middle gates. -/
structure Depth3Circuit (n size sizeMid : ℕ) where
  m : ℕ
  hm : m ≤ size
  mid : Fin m → ModAndCircuit n sizeMid
  topMod : ℕ
  topRes : ℕ

/-- Semantics: the number of accepting middle `MOD∘AND` gates is `≡ topRes (mod topMod)`. -/
def Depth3Circuit.eval {n size sizeMid : ℕ} (C : Depth3Circuit n size sizeMid) (x : Fin n → Bool) : Bool :=
  decide ((∑ j : Fin C.m, if (C.mid j).eval x then 1 else 0) % C.topMod = C.topRes)

/-- **The discharged depth-3 instance (proved)**: a `MOD∘MOD∘AND` circuit is a `YBTCompiler`, the top `MOD` being the
symmetric observer over the middle-gate count (`exact := rfl`).  (In the count-cell observer model — see the file
docstring for where the prime-power arithmetisation is actually load-bearing.) -/
def depth3_ybtCompiler (n size sizeMid k : ℕ) (hkn : k ≤ n) (hfit : size + 1 ≤ 2 ^ (n - k)) :
    YBTCompiler n (Depth3Circuit n size sizeMid) Depth3Circuit.eval where
  size C := C.m
  gates C := fun j x => (C.mid j).eval x
  top C := fun c => decide (c % C.topMod = C.topRes)
  exact _ := rfl
  budget := k
  budget_le := hkn
  size_fit C := le_trans (Nat.succ_le_succ C.hm) hfit

/-- The fast-SAT model for depth-3 `MOD∘MOD∘AND`, via the proved bridge. -/
noncomputable def depth3_fastSATModel (n size sizeMid k : ℕ) (hkn : k ≤ n) (hfit : size + 1 ≤ 2 ^ (n - k)) :
    FastSATModel n (Depth3Circuit n size sizeMid) (fun C => decide (Satisfiable (Depth3Circuit.eval C))) :=
  ybtCompiler_fastSATModel (depth3_ybtCompiler n size sizeMid k hkn hfit)

/-- **Depth-3 `MOD∘MOD∘AND` has an N-Frame fast-SAT speedup (proved, observer model)**. -/
theorem depth3_fastSATSpeedup (n size sizeMid k : ℕ) (hkn : k ≤ n) (hfit : size + 1 ≤ 2 ^ (n - k)) :
    NFrameFastSATSpeedup n (Depth3Circuit n size sizeMid)
      (fun C => decide (Satisfiable (Depth3Circuit.eval C))) :=
  ⟨depth3_fastSATModel n size sizeMid k hkn hfit⟩

/-- A concrete **prime-power-top** depth-3 circuit `MOD_{p^e} ∘ MOD∘AND`. -/
def mkPrimePowerDepth3 {n size sizeMid : ℕ} (p e : ℕ) (m : ℕ) (hm : m ≤ size)
    (mid : Fin m → ModAndCircuit n sizeMid) (topRes : ℕ) : Depth3Circuit n size sizeMid :=
  { m := m, hm := hm, mid := mid, topMod := p ^ e, topRes := topRes }

end PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.depth3_ybtCompiler
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.depth3_fastSATSpeedup
