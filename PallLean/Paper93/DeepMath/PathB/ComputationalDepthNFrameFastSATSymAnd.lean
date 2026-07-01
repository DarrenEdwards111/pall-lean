import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFastSAT

/-!
# A real `FastSATModel`: the `SYM∘AND` bounded-degree case

The `NFrameFastSAT` interface was proved with a *toy* inhabitant.  This file replaces the toy with a **real, proved
circuit class**: the `SYM∘AND` bounded-degree family, whose Williams fast-SAT is already proved in
`ACC0WilliamsFastSat` (`symAnd_williams_fastSat`: SAT is decided by the count-cell image, the cell count fits the
budget, and the work delivers `2^k` savings).  This turns the Williams pivot from "schema + toy" into "schema + real
bounded case".

  `SymAndCircuit n D` — a `SYM∘AND` circuit: `m` injective monomial-`AND` gates of degree `≤ D` under a symmetric top `h`.
  `symAnd_fastSATModel` — **the instance (proved)**: `FastSATModel` for `SymAndCircuit`, in the regime where the
        quasipolynomial gate count fits the budget `2^{n−k}`.  `encode` = count-cell SAT decision; `correct` from
        `observed_sat_iff` (the cell-search decides SAT exactly); `work_le` from `fastSatWork_le_of_degree`.
  `symAnd_nframe_fastSAT_savings` — the fast-SAT savings `2^k · fastSatWork m ≤ 2^n` *through the interface*.
  `symAnd_nframe_fastSATSpeedup` — the `NFrameFastSATSpeedup` for the `SYM∘AND` family (inhabits Williams' speedup slot).

## Honest scope — where on the ladder this sits

`toy → ` **`SYM∘AND` (here)** ` → BT normal form → ACC⁰ → Williams implication fires`.

This is the *bounded-degree* rung: the `SYM∘AND` fast-SAT is genuinely proved (correctness + quasipolynomial cell count
+ savings), and now it faithfully inhabits the `FastSATModel` interface — a real circuit class, not a placeholder.  It is
**not** full `ACC⁰`: the next rungs are the Beigel–Tarui `P(∑∏)` normal form (with explicit parameter blowup) and then
recursive depth / composite-`MOD` handling.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (symEval gateCount)
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver (observed_sat_iff)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup (Satisfiable)
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat (fastSatWork fastSatWork_le_of_degree)

attribute [local instance] Classical.propDecidable

/-- A `SYM∘AND` circuit over `n` bits, bottom degree `≤ D`: `m` injective monomial-`AND` gates under a symmetric top `h`. -/
structure SymAndCircuit (n D : ℕ) where
  m : ℕ
  mono : Fin m → Finset (Fin n)
  h : ℕ → Bool
  hinj : Function.Injective mono
  hdeg : ∀ j, (mono j).card ≤ D

/-- The monomial-`AND` sub-gate family of a `SYM∘AND` circuit. -/
def SymAndCircuit.gates {n D : ℕ} (C : SymAndCircuit n D) : Fin C.m → (Fin n → Bool) → Bool :=
  fun j x => monoAND (C.mono j) x

/-- The true SAT predicate of a `SYM∘AND` circuit, as a `Bool`. -/
noncomputable def symAndSatOf {n D : ℕ} (C : SymAndCircuit n D) : Bool :=
  decide (Satisfiable (symEval C.gates C.h))

/-- **The real instance (proved)**: the `SYM∘AND` bounded-degree family is a `FastSATModel`, in the regime where the
quasipolynomial gate count fits the budget `2^{n−k}`.  Correctness is `observed_sat_iff` (the count-cell search decides
SAT exactly); the work bound is `fastSatWork_le_of_degree` composed with the fit hypothesis. -/
noncomputable def symAnd_fastSATModel (n D k : ℕ) (hkn : k ≤ n)
    (hfit : (∑ i ∈ Finset.range (D + 1), n.choose i) + 1 ≤ 2 ^ (n - k)) :
    FastSATModel n (SymAndCircuit n D) symAndSatOf where
  encode C :=
    ⟨C.m, decide (∃ c ∈ Finset.univ.image (gateCount C.gates), C.h c = true)⟩
  correct C := decide_eq_decide.mpr (observed_sat_iff C.h (fun _ => rfl)).symm
  budget := k
  budget_le := hkn
  work_le C := le_trans (fastSatWork_le_of_degree C.mono C.hinj C.hdeg) hfit

/-- **Savings through the interface (proved)**: the `SYM∘AND` fast-SAT delivers `2^k · fastSatWork m ≤ 2^n`, obtained
from the generic `fastSATModel_savings` applied to the real instance. -/
theorem symAnd_nframe_fastSAT_savings (n D k : ℕ) (hkn : k ≤ n)
    (hfit : (∑ i ∈ Finset.range (D + 1), n.choose i) + 1 ≤ 2 ^ (n - k)) (C : SymAndCircuit n D) :
    2 ^ k * fastSatWork C.m ≤ 2 ^ n :=
  fastSATModel_savings (symAnd_fastSATModel n D k hkn hfit) C

/-- **The `NFrameFastSATSpeedup` for the `SYM∘AND` family (proved)**: it inhabits Williams' abstract speedup slot with a
real proved circuit class. -/
theorem symAnd_nframe_fastSATSpeedup (n D k : ℕ) (hkn : k ≤ n)
    (hfit : (∑ i ∈ Finset.range (D + 1), n.choose i) + 1 ≤ 2 ^ (n - k)) :
    NFrameFastSATSpeedup n (SymAndCircuit n D) symAndSatOf :=
  ⟨symAnd_fastSATModel n D k hkn hfit⟩

end PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.symAnd_fastSATModel
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.symAnd_nframe_fastSAT_savings
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.symAnd_nframe_fastSATSpeedup
