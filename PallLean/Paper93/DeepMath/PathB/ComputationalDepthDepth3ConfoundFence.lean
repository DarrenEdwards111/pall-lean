import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CleanSkipReconstruction

/-!
# The confound is real and uncovered: a machine-checked fence

The closed satisfy-step regimes are no-skip (no empty blocks), clean-skip (`hskip`: empty block ⟺
falsified leaf clause), and `align`.  Their union leaves exactly the **confound**: a clause *falsified
at the leaf that also received satisfy steps*.  This file exhibits a concrete restriction that is
**outside all three** — proving the confound regime is non-empty and irreducible by the `(2w)^s`
positional decoders, not merely a fenced suspicion.

Witness: `cs = [{x₀}, {x₁, x₂}]` over `Fin 3`, `ρ` everywhere free.  The canonical deepest path is

* `x₀ := false` — *falsifies* `{x₀}` (a single falsify step, **no** satisfy step), so `{x₀}` is a
  **clean skip**: an **empty** replay block, yet present in `leafClauses`;
* `x₁ := true` — *satisfies* a literal of `{x₁, x₂}` (a satisfy step, recorded);
* `x₂ := false` — *falsifies* `{x₁, x₂}`.

So `{x₁, x₂}` is **falsified at the leaf yet carries a non-empty satisfy block** — the confound — while
`{x₀}` contributes an empty block.

* `clA_clean_skip` / `clB_confound` — the two clauses' end-state behaviour (`decide`).
* `confound_uncovered` — the instance has an **empty** replay block (so `reconstruction_no_skip`'s
  `hns` fails) **and** violates `hskip` (so `reconstruction_clean_skip` does not apply); the interior
  empty also breaks `halign`.  Hence no closed regime covers it.

## What remains (honest)

Decoding this requires *attributing* `{x₁, x₂}`'s satisfy positions to it despite its being falsified
at the leaf — indistinguishable, from `(deepestEnd, (2w)^s label)`, from the clean skip `{x₀}`.  That
attribution is recovered only by a **forward-replay / clause-order reconstruction of `ρ`** (Razborov's
decoder) — i.e. Håstad's switching lemma itself.  This file does **not** build that decoder; it fences
the confound as the genuine residual.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

/-- The witness DNF `[{x₀}, {x₁, x₂}]` over `Fin 3`. -/
def confCs : List (Clause 3) :=
  [⟨[Rung4Literal.pos 0]⟩, ⟨[Rung4Literal.pos 1, Rung4Literal.pos 2]⟩]

/-- Everywhere-free restriction. -/
def confRho : Fin 3 → Option Bool := fun _ => none

/-- The clean-skip clause `{x₀}`. -/
def clA : Clause 3 := ⟨[Rung4Literal.pos 0]⟩

/-- The confound clause `{x₁, x₂}`. -/
def clB : Clause 3 := ⟨[Rung4Literal.pos 1, Rung4Literal.pos 2]⟩

/-- **`{x₀}` is a clean skip.**  On the deepest path it is falsified with no satisfy step — an empty
block. -/
theorem clA_clean_skip :
    deepestSatPositions confCs 3 confRho clA = [] ∧
      SwitchingCounting.termFalsified (deepestEnd confCs 3 confRho) clA = true := by
  decide

/-- **`{x₁, x₂}` is the confound.**  On the deepest path it receives a satisfy step (non-empty block)
yet is falsified at the leaf. -/
theorem clB_confound :
    deepestSatPositions confCs 3 confRho clB ≠ [] ∧
      SwitchingCounting.termFalsified (deepestEnd confCs 3 confRho) clB = true := by
  decide

/-- **The instance is outside every closed regime.**  It has an empty replay block (so
`reconstruction_no_skip`'s all-blocks-non-empty hypothesis fails) and it violates the clean-skip
hypothesis `hskip` (so `reconstruction_clean_skip` does not apply).  The confound is therefore a
genuine, non-empty residual — not faked. -/
theorem confound_uncovered :
    (∃ b ∈ replayLabel confCs 3 confRho, b = []) ∧
      ¬ (∀ C ∈ leafClauses confCs (deepestEnd confCs 3 confRho),
          (deepestSatPositions confCs 3 confRho C = [] ↔
            SwitchingCounting.termFalsified (deepestEnd confCs 3 confRho) C = true)) := by
  decide

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.clB_confound
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.confound_uncovered
