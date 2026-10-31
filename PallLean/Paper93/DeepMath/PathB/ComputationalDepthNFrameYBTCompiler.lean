import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFastSATBT

/-!
# The YBT-compiler interface: the last rung, stated precisely

The fast-SAT side of the Williams ladder is now proved for the full BT `SYM∘AND` normal form (`…FastSATBT`).  The one
remaining rung is the **Yao–Beigel–Tarui compilation**: turning an arbitrary constant-depth `ACC⁰` circuit *into* that
normal form with quasipolynomial size.  This file makes that rung a **named interface** with the size/budget parameters
explicit, and proves it discharges into a `FastSATModel` — so the open problem is isolated to *one* structure.

  `YBTCompiler n Circuit evalC` — the interface: a circuit family compiles to an *exact* `SYM∘AND` form
        (`exact : evalC C = symEval (gates C) (top C)`) with size within the fast-SAT budget
        (`size_fit : size C + 1 ≤ 2^{n−budget}`).
  `ybtCompiler_fastSATModel` — **the bridge (proved)**: a `YBTCompiler` yields a `FastSATModel` for the family
        (`correct` from `observed_sat_iff`, `work_le` from `size_fit`).  Everything downstream — savings, the Williams
        implication — then fires.
  `ybtCompiler_fastSATSpeedup` — the `NFrameFastSATSpeedup` from a compiler.
  `btYBTCompiler` — non-vacuity: the BT rung itself is trivially a `YBTCompiler` (it is already in normal form).

## What is open, stated exactly

A `YBTCompiler` instance for a circuit family is *provable* precisely when that family's YBT compilation is available:
* **trivial base** — `btYBTCompiler`: a `BTCircuit` (already `SYM∘AND`) compiles by identity;
* **dischargeable** — depth-`2` and prime-power `MOD` (the polynomial/root-of-unity arithmetisation of C11–C13, `char`
  large enough) give explicit compilers;
* **open** — a `YBTCompiler` instance for arbitrary `ACC⁰` (composite `MOD`, depth `> 1`) is the classical YBT theorem
  with quasipolynomial size, the genuinely hard structural step (the corpus's `HasExactSymAndForm` /
  `MixedACCDepthReductionSocket`).  It is **not** provided here.

So the ladder's last rung is now one precise object: an instance `YBTCompiler (ACC0Circuit n) eval`.  The composite-`MOD`
barrier is localised entirely there — not in the fast-SAT machinery, which is proved.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (symEval gateCount)
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver (observed_sat_iff)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup (Satisfiable)

attribute [local instance] Classical.propDecidable

/-- **The YBT-compiler interface**: a circuit family `Circuit` with semantics `evalC` compiles to an *exact* `SYM∘AND`
normal form — `evalC C = symEval (gates C) (top C)` — with the number of sub-gates within the fast-SAT budget
`2^{n−budget}`.  Instantiating this for a circuit class *is* providing its Yao–Beigel–Tarui normal form. -/
structure YBTCompiler (n : ℕ) (Circuit : Type) (evalC : Circuit → (Fin n → Bool) → Bool) where
  size : Circuit → ℕ
  gates : (C : Circuit) → Fin (size C) → (Fin n → Bool) → Bool
  top : Circuit → (ℕ → Bool)
  exact : ∀ C, evalC C = symEval (gates C) (top C)
  budget : ℕ
  budget_le : budget ≤ n
  size_fit : ∀ C, size C + 1 ≤ 2 ^ (n - budget)

/-- **The bridge (proved): a YBT compiler yields a fast-SAT model.**  The exact `SYM∘AND` form makes SAT a count-cell
search (`observed_sat_iff`), and the size budget bounds the work — so the family is a `FastSATModel`, inheriting the
Williams savings and (with the classical sockets) the separation. -/
noncomputable def ybtCompiler_fastSATModel {n : ℕ} {Circuit : Type}
    {evalC : Circuit → (Fin n → Bool) → Bool} (Y : YBTCompiler n Circuit evalC) :
    FastSATModel n Circuit (fun C => decide (Satisfiable (evalC C))) where
  encode C :=
    ⟨Y.size C, decide (∃ c ∈ Finset.univ.image (gateCount (Y.gates C)), Y.top C c = true)⟩
  correct C := by
    rw [Y.exact C]
    exact decide_eq_decide.mpr (observed_sat_iff (Y.top C) (fun _ => rfl)).symm
  budget := Y.budget
  budget_le := Y.budget_le
  work_le C := Y.size_fit C

/-- The `NFrameFastSATSpeedup` obtained from a YBT compiler. -/
theorem ybtCompiler_fastSATSpeedup {n : ℕ} {Circuit : Type}
    {evalC : Circuit → (Fin n → Bool) → Bool} (Y : YBTCompiler n Circuit evalC) :
    NFrameFastSATSpeedup n Circuit (fun C => decide (Satisfiable (evalC C))) :=
  ⟨ybtCompiler_fastSATModel Y⟩

/-- **Non-vacuity (proved)**: the BT rung is trivially a `YBTCompiler` — a `BTCircuit` is already in `SYM∘AND` normal
form, so it compiles by identity.  (The genuinely hard instances are the `ACC⁰` compilations.) -/
def btYBTCompiler (n size k : ℕ) (hkn : k ≤ n) (hfit : size + 1 ≤ 2 ^ (n - k)) :
    YBTCompiler n (BTCircuit n size) (fun BC => symEval BC.gates BC.h) where
  size BC := BC.m
  gates BC := BC.gates
  top BC := BC.h
  exact _ := rfl
  budget := k
  budget_le := hkn
  size_fit BC := le_trans (Nat.succ_le_succ BC.hm) hfit

end PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.ybtCompiler_fastSATModel
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.ybtCompiler_fastSATSpeedup
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.btYBTCompiler
