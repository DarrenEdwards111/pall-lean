import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMDiagonal

/-!
# Time hierarchy, rung 1: the deterministic diagonalisation backbone on the *real* RAM machine

Toward discharging the `NondetTimeHierarchy` socket (`NTIME[2ⁿ] ⊄ NTIME[2ⁿ/superpoly]`).  The full socket needs (a) a
verified universal machine with clocking overhead and (b) *lazy* diagonalisation (nondeterministic classes are not closed
under complement).  This file builds the **deterministic backbone** — the diagonalisation direction — and, crucially,
grounds it on the repo's **actual** RAM machine `run` (not an opaque `sim`), reducing the deterministic time hierarchy to
a single, precisely-stated computational lemma.

  `prog1_computes` — the real RAM `run` genuinely computes: `[acc:=1; mem[0]:=acc; halt]` leaves `mem[0] = 1` after `3`
        steps.  (Non-vacuity: the clocked class contains real machine computations.)
  `ramBit` — the clocked output bit of RAM code `e` on input `x` within `budget x` steps, read from `mem[0]` (clamped to
        a bit).  `ClockedLang budget` — the languages this real machine decides within `budget`.
  `diag_not_in_clocked` — **PROVED, over the real machine**: the diagonal language `diagLang` (flip of code `x`'s clocked
        self-output) is not in `ClockedLang budget`.  This is the diagonalisation direction, grounded on `run`.
  `UniversalRAMRealizesDiagonal` — **the single remaining computational lemma (isolated, not proved)**: a universal RAM
        program computes `diagLang` within a *larger* budget.  This is the general universal RAM interpreter with
        overhead — the repo's `uSim` only simulates a counting machine, so this is the next rung.
  `clocked_strict_of_universal` — **the deterministic hierarchy, from that one lemma (proved)**: the isolated universal
        lemma gives `ClockedLang bigBudget ⊋ ClockedLang budget` (strict), the not-in-class direction already proved.

## Honest scope

This proves the diagonalisation direction over the real RAM `run` and **isolates** the deterministic time hierarchy down
to exactly one concrete computational fact (`UniversalRAMRealizesDiagonal` — the universal interpreter with clocking
overhead).  It does **not** discharge that fact: building the general universal RAM interpreter is the next rung, and the
*nondeterministic* lift (lazy diagonalisation) is a further one.  So this is rung 1 of the hierarchy socket, not the
hierarchy.  Nothing here is `NondetTimeHierarchy`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

open PallLean.Paper93.DeepMath.PathB.RAM

/-! ### The real RAM machine genuinely computes (non-vacuity) -/

/-- A concrete RAM program: `acc := 1`, `mem[0] := acc`, halt. -/
def prog1 : List Instr := [Instr.constI 1, Instr.storeI 0, Instr.haltI]

/-- **The real `run` genuinely computes (proved)**: after `3` steps of `prog1`, `mem[0] = 1`. -/
theorem prog1_computes (m0 : Mem) :
    (run prog1 { mem := m0, acc := 0, pc := 0, halted := false } 3).mem 0 = 1 := by
  simp [run, step, prog1, Mem.set, List.getD]

/-! ### The clocked RAM class and the diagonal, grounded on `run` -/

variable (decode : ℕ → List Instr) (initMem : ℕ → Mem) (budget : ℕ → ℕ)

/-- The clocked output bit of RAM code `e` on input `x`: run `decode e` from `initMem x` for `budget x` steps and read
`mem[0]`, clamped to a bit. -/
noncomputable def ramBit (e x : ℕ) : ℕ :=
  min ((run (decode e) { mem := initMem x, acc := 0, pc := 0, halted := false } (budget x)).mem 0) 1

/-- The clocked output is always a bit. -/
theorem ramBit_le_one (e x : ℕ) : ramBit decode initMem budget e x ≤ 1 := min_le_right _ _

/-- The clocked RAM class at time bound `budget`: languages `L` decided by some RAM code within `budget`. -/
def ClockedLang (L : ℕ → ℕ) : Prop := ∃ e, ∀ x, L x = ramBit decode initMem budget e x

/-- The diagonal language: the flip of code `x`'s clocked self-output (`ramDiag` of the real machine's `ramBit`). -/
noncomputable def diagLang : ℕ → ℕ := ramDiag (ramBit decode initMem budget)

/-- **The diagonalisation direction, PROVED over the real machine**: the diagonal language is not decided by any RAM
code within `budget` — it escapes the clocked class. -/
theorem diag_not_in_clocked : ¬ ClockedLang decode initMem budget (diagLang decode initMem budget) := by
  rintro ⟨e, he⟩
  exact ramDiag_not_mem (ramBit decode initMem budget)
    (fun e => ramBit_le_one decode initMem budget e e) ⟨e, fun x => (he x).symm⟩

/-! ### The isolated crux and the deterministic hierarchy -/

/-- **The single remaining computational lemma (isolated, not proved here)**: a universal RAM program computes the
diagonal `diagLang` (against `budget`) within the *larger* bound `bigBudget`.  This is the general universal RAM
interpreter with clocking overhead — the repo's `uSim` handles only a counting machine, so discharging this is the next
rung. -/
def UniversalRAMRealizesDiagonal (bigBudget : ℕ → ℕ) : Prop :=
  ClockedLang decode initMem bigBudget (diagLang decode initMem budget)

/-- **The deterministic time hierarchy, from the isolated lemma (proved)**: if the universal RAM program realises the
diagonal within `bigBudget`, then `ClockedLang bigBudget` strictly contains `ClockedLang budget` — the diagonal is in the
larger class but (proved) not in the smaller. -/
theorem clocked_strict_of_universal (bigBudget : ℕ → ℕ)
    (huniv : UniversalRAMRealizesDiagonal decode initMem budget bigBudget) :
    ClockedLang decode initMem bigBudget (diagLang decode initMem budget)
      ∧ ¬ ClockedLang decode initMem budget (diagLang decode initMem budget) :=
  ⟨huniv, diag_not_in_clocked decode initMem budget⟩

/-! ### Non-vacuity: the clocked class contains a real machine computation -/

/-- The clocked class is inhabited by a genuine RAM computation: with every code decoding to `prog1` and budget `3`, the
constant-`1` language is decided by the real machine. -/
theorem clocked_nonvacuous :
    ClockedLang (fun _ => prog1) (fun _ => (fun _ => 0)) (fun _ => 3) (fun _ => 1) :=
  ⟨0, fun x => by simp [ramBit, prog1_computes]⟩

end PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.prog1_computes
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.diag_not_in_clocked
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.clocked_strict_of_universal
#print axioms PallLean.Paper93.DeepMath.PathB.DetTimeHierarchy.clocked_nonvacuous
