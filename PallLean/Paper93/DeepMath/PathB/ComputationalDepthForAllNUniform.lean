import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRoutingParallelize

/-!
# The "for all n, to infinity" trick — it works, on the uniform axis; the uniformity gap blocks the circuit

Darren: the tower has unified structure across all levels (depth-2 → depth-3 → … → ACC → NP → EXP → ∞), so
can a single "for all n" global rule run to infinity?  Yes — but only on the **uniform** axis, and this
file shows exactly why it reaches infinity there and not on the circuit wall.

A **uniform** diagonal (one function `uniformDiag M n = !(M n)`) beats a single machine `M` at *every* `n`
— an unconditional "for all n, to infinity" bound.  This is the diagonalization / time hierarchy /
Lipton–Viglas engine (`UniformAxisReach`): a general global rule, self-similar across the whole tower,
holding to infinity.  But the wall (`SAT ∈ P?`) is **non-uniform**: a circuit *family* has a *different*
circuit for each `n`, and each one can *hardcode* the answer at `n`.  So "beats every single machine
everywhere" does **not** beat a non-uniform family — the **uniformity gap**.

## What is proved

* **`uniform_diag_beats_all_n`** — the uniform diagonal differs from `M` at *every* `n`: a single global
  rule beating one machine for all `n`, to infinity.
* **`nonuniform_family_matches`** — for *any* target, a non-uniform family (a custom entry per `n`) matches
  it at every `n`: non-uniformity hardcodes the answer.
* **`uniformity_gap`** — both at once: the uniform diagonal beats `M` for all `n`, yet a non-uniform family
  matches that very diagonal at every `n`.  "For all n" beats every *uniform* machine but no *non-uniform*
  family.

## Honest verdict — the trick reaches infinity uniformly; the uniformity gap is the circuit wall

Darren's "for all n, to infinity" is real — on the **uniform** axis.  The tower's unified structure lets a
single diagonal beat any one machine at *every* `n` (`uniform_diag_beats_all_n`), unconditionally, forever
— the time hierarchy (`P ⊊ EXP`) and the Lipton–Viglas SAT time–space bounds (`UniformAxisReach`, capped
at `√2`).  A genuine global rule to infinity.  But it caps twice: (1) at a *fixed gap* (`P ⊊ EXP`, not
`P ≠ NP` — SAT sits *inside*), and (2) at the **uniformity gap**: `SAT ∈ P?` is about *non-uniform*
circuits — a *family*, one circuit per `n` — and a family can hardcode the answer at each `n`
(`nonuniform_family_matches`), so the "for all n" uniform diagonal does not bound it (`uniformity_gap`).
The unified structure that powers the uniform "for all n" argument is exactly what a non-uniform circuit
family *breaks*: each `n` gets its own circuit, so there is no single object to diagonalize against.  So
the trick reaches infinity — but on the uniform axis, where it gives `P ⊊ EXP` and `√2`, not `P ≠ NP`;
crossing to the non-uniform circuit wall is `cost_super`, and the obstruction is the uniformity gap.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForAllNUniform

/-- The **uniform diagonal** against a single machine `M`: `!(M n)` at each `n`. -/
def uniformDiag (M : ℕ → Bool) (n : ℕ) : Bool := ! (M n)

/-! ### The uniform "for all n" bound reaches infinity -/

/-- **The uniform diagonal beats `M` at every `n` (proved).**  `uniformDiag M n ≠ M n` for all `n` — a
single global rule beating one machine for all `n`, to infinity (diagonalization / time hierarchy). -/
theorem uniform_diag_beats_all_n (M : ℕ → Bool) : ∀ n, uniformDiag M n ≠ M n := by
  intro n
  simp only [uniformDiag]
  cases M n <;> decide

/-! ### But a non-uniform family evades it -/

/-- **A non-uniform family matches any target (proved).**  For any `target : ℕ → Bool`, the family
`fun n _ => target n` — a custom circuit per `n`, hardcoding the answer — matches `target` at every `n`.
Non-uniformity evades the "for all n" uniform argument. -/
theorem nonuniform_family_matches (target : ℕ → Bool) :
    ∃ family : ℕ → ℕ → Bool, ∀ n, family n n = target n :=
  ⟨fun n _ => target n, fun _ => rfl⟩

/-! ### The uniformity gap -/

/-- **The uniformity gap (proved).**  The uniform diagonal beats `M` at every `n`, *and* a non-uniform
family matches that very diagonal at every `n`.  So "for all n" defeats every *uniform* machine but no
*non-uniform* family — the gap between the uniform axis (where the trick reaches infinity) and the circuit
wall. -/
theorem uniformity_gap (M : ℕ → Bool) :
    (∀ n, uniformDiag M n ≠ M n)
    ∧ (∃ family : ℕ → ℕ → Bool, ∀ n, family n n = uniformDiag M n) :=
  ⟨uniform_diag_beats_all_n M, nonuniform_family_matches (uniformDiag M)⟩

end PallLean.Paper93.DeepMath.PathB.ForAllNUniform

#print axioms PallLean.Paper93.DeepMath.PathB.ForAllNUniform.uniform_diag_beats_all_n
#print axioms PallLean.Paper93.DeepMath.PathB.ForAllNUniform.nonuniform_family_matches
#print axioms PallLean.Paper93.DeepMath.PathB.ForAllNUniform.uniformity_gap
