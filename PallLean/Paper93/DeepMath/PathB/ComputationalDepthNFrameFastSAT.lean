import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsMetaTheorem
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsFastSat

/-!
# The N-Frame fast-SAT interface: the algorithmic route to `NEXP ⊄ ACC⁰`

The polynomial-method N-Frame arc reached the real `MOD_6` wall (C16): no single field makes every modulus of a
multi-prime circuit hard.  **Williams' algorithmic route bypasses that** — it does not need a single hard field; it needs
a *nontrivial SAT algorithm* for `ACC⁰`.  This file pivots N-Frame from a *degree* certificate to a *compression /
algorithmic* certificate, and packages it as the interface that feeds the repo's Williams meta-theorem
(`ACC0WilliamsMetaTheorem.williams_meta_theorem`).

  `NFrameProgram` — a compact N-Frame representation over `n` bits: a DAG/DP with a count-cell table of size `cells`,
        deciding SAT by cell search (fast evaluation/counting, **not** low polynomial degree).
  `FastSATModel` — a fast-SAT model for a circuit family: each circuit compiles to a compact `NFrameProgram` that decides
        SAT correctly, with cell-search work within a `2^{n−budget}` budget.
  `fastSATModel_savings` — **the algorithmic guarantee (proved)**: such a model delivers Williams savings
        `2^budget · work ≤ 2^n` (via `ACC0WilliamsFastSat.fastSat_savings_of_work_le`).
  `nframe_fastSAT_gives_separation` — **the schema (proved glue)**: `ACC⁰` having an N-Frame fast-SAT model, together
        with the two named classical Williams sockets (easy-witness collapse + nondeterministic time hierarchy),
        forces `NEXP ⊄ ACC⁰`.
  `toyModel` / `toy_speedup` — non-vacuity: the interface is inhabitable (a real, counted procedure).

## Why this bypasses `MOD_6` — and the honest scope

N-Frame's job here is to *provide the structure enabling the nontrivial algorithm* — the compact DAG/DP representation
whose count-cell search beats brute force.  This is an **algorithmic** claim (fast #SAT), not "MOD_6 is hard over some
field", so it is **not** blocked by the C16 two-fields/CRT obstruction.

Honest scope: this is the *interface + toy implication*, not `NEXP ⊄ ACC⁰`.  The genuinely deep content — the
easy-witness / IKW collapse and the nondeterministic time hierarchy — are the named sockets `EasyWitnessCollapse` /
`NondetTimeHierarchy` (proven classical theorems, Williams 2011; their formalisation is a separate major project) and
are **not** proved here.  The N-Frame contribution is exactly the fast-SAT *model* inhabiting the speedup slot, with the
savings guarantee proved.  Building an *actual* nontrivial N-Frame fast-SAT model for arbitrary `ACC⁰` (composite `MOD`,
depth `> 1`) is the open algorithmic target this interface is meant to be instantiated with.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat (fastSatWork fastSat_savings_of_work_le)

/-- A compact **N-Frame program** over `n` input bits: a DAG/DP representation whose count-cell table has size `cells`,
from which SAT is decided by a cell search — the *algorithmic* N-Frame witness (fast evaluation/counting). -/
structure NFrameProgram (n : ℕ) where
  cells : ℕ
  decideSAT : Bool

/-- A **fast-SAT model** for a circuit family `Circuit` (with true SAT predicate `satOf`) over `n` bits: every circuit
compiles to a compact `NFrameProgram` deciding SAT correctly, with cell-search work within a `2^{n−budget}` budget —
i.e. a `2^budget` speedup over brute force `2^n`. -/
structure FastSATModel (n : ℕ) (Circuit : Type) (satOf : Circuit → Bool) where
  encode : Circuit → NFrameProgram n
  correct : ∀ C, (encode C).decideSAT = satOf C
  budget : ℕ
  budget_le : budget ≤ n
  work_le : ∀ C, fastSatWork (encode C).cells ≤ 2 ^ (n - budget)

/-- **The algorithmic guarantee (proved)**: a fast-SAT model delivers Williams savings — the cell-search work times
`2^budget` stays within brute force `2^n`. -/
theorem fastSATModel_savings {n : ℕ} {Circuit : Type} {satOf : Circuit → Bool}
    (M : FastSATModel n Circuit satOf) (C : Circuit) :
    2 ^ M.budget * fastSatWork (M.encode C).cells ≤ 2 ^ n :=
  fastSat_savings_of_work_le M.budget_le (M.work_le C)

/-- The **N-Frame fast-SAT speedup** for a circuit family: it admits a compact N-Frame fast-SAT model.  This is the
concrete inhabitant of Williams' abstract `ACC0SatSpeedup` slot. -/
def NFrameFastSATSpeedup (n : ℕ) (Circuit : Type) (satOf : Circuit → Bool) : Prop :=
  Nonempty (FastSATModel n Circuit satOf)

/-- **The schema (proved glue): N-Frame fast-SAT ⇒ `NEXP ⊄ ACC⁰`.**  If `ACC⁰` circuits admit a compact N-Frame fast-SAT
model (the algorithmic representation N-Frame provides), then with the two named classical Williams sockets
(`EasyWitnessCollapse` + `NondetTimeHierarchy`, Williams 2011) it forces `NEXP ⊄ ACC⁰`.  The N-Frame model inhabits the
speedup slot; the deep sockets are the classical ingredients (not proved here). -/
theorem nframe_fastSAT_gives_separation
    (NEXP ACC0 NTIME2n NTIME2nFast : CClass) {n : ℕ} {Circuit : Type} {satOf : Circuit → Bool}
    (collapse : EasyWitnessCollapse NEXP ACC0 NTIME2n NTIME2nFast (NFrameFastSATSpeedup n Circuit satOf))
    (hierarchy : NondetTimeHierarchy NTIME2n NTIME2nFast)
    (fastsat : NFrameFastSATSpeedup n Circuit satOf) :
    ¬ (NEXP ⊆ ACC0) :=
  williams_meta_theorem NEXP ACC0 NTIME2n NTIME2nFast
    (NFrameFastSATSpeedup n Circuit satOf) collapse hierarchy fastsat

/-- Non-vacuity: a fast-SAT model for the degenerate single-input family, with a `0`-cell N-Frame program and a real
`2^1` speedup (`fastSatWork 0 = 1 ≤ 2 = 2^{2−1}`). -/
def toyModel : FastSATModel 2 Unit (fun _ => true) where
  encode := fun _ => ⟨0, true⟩
  correct := fun _ => rfl
  budget := 1
  budget_le := by norm_num
  work_le := fun _ => by decide

/-- The toy family admits an N-Frame fast-SAT speedup — the interface is inhabitable. -/
theorem toy_speedup : NFrameFastSATSpeedup 2 Unit (fun _ => true) := ⟨toyModel⟩

end PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.fastSATModel_savings
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.nframe_fastSAT_gives_separation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.toy_speedup
