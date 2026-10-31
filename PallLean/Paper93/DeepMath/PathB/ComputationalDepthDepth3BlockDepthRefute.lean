import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockCircuitCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalTree

/-!
# Block-DT model, audit: `blockStream` length does NOT bound `canonicalDTree` depth (branch `razborov-recoverRho-wip`)

The **direction audit** for the would-be depth bridge `canonicalDTree.depth ≤ blockStream.length · w` (which the
block route would need to connect `circuit_collapse_uncond` to the parity pipeline).  **It is FALSE**, refuted
by a concrete counterexample, so the block route's shallowness (`blockStream length < s`) does **not** imply
the gate's decision tree is shallow.

Root cause: `blockStream` follows only the `killTerm` (one specific falsifying) branch, whereas
`canonicalDTree.depth` is the **max over all branches**.  When every term shares a pivot variable, `killTerm`
of the first term sets that variable to falsify *all* terms at once (so `blockStream` stops immediately), while
the *other* setting of the pivot keeps the chain alive and deep.

Counterexample (`n = 5`): `cs = [{x₀,x₁}, {x₀,x₂}, {x₀,x₃}, {x₀,x₄}]` (AND-terms, all containing `x₀`), the
all-free restriction.  `killTerm` of the first term sets `x₀ = false`, falsifying every term ⟹ `blockStream`
has length `1`.  But the `x₀ = true` branch processes `{x₀,x₁}` (queries `x₁`), then `{x₀,x₂}` (queries `x₂`),
… so the canonical tree has depth `5`.  Hence `5 = depth > 1·2 = blockStream.length · w`, and with `s = 2`:
`blockStream.length = 1 < 2 = s` yet `depth = 5 ≥ 4 = s·w`.

**Consequence:** `block_switching_count_tight` / `circuit_collapse_uncond` (bricks 146–151) are clean, correct
theorems, but they control the `killTerm` *path*, not the tree *depth* — the wrong quantity for the parity
connection.  The correct route is the **depth-graded** `descent_switching_prob` (graded by
`(canonicalDTree …).depth`, the max branch), made `F`-independent (route 2).

* `csCex`, `rhoCex` — the counterexample family.
* `blockStream_length_not_bound_depth` — `∃ cs ρ, blockStream.length · w < canonicalDTree.depth`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

/-- The counterexample CNF/DNF: four AND-terms over `Fin 5`, all sharing the pivot variable `x₀`. -/
def csCex : List (Clause 5) :=
  [⟨[Rung4Literal.pos 0, Rung4Literal.pos 1]⟩,
   ⟨[Rung4Literal.pos 0, Rung4Literal.pos 2]⟩,
   ⟨[Rung4Literal.pos 0, Rung4Literal.pos 3]⟩,
   ⟨[Rung4Literal.pos 0, Rung4Literal.pos 4]⟩]

/-- The all-free restriction. -/
def rhoCex : Fin 5 → Option Bool := fun _ => none

/-- **The block route does not bound the tree depth.**  There is a clause family and a restriction whose
`killTerm` block stream is short (`length · w = 2`) while the canonical decision tree is deep (`depth = 5`).
So `canonicalDTree.depth ≤ blockStream.length · w` is FALSE — `blockStream` length (the `killTerm` branch) does
not control the tree depth (the max branch). -/
theorem blockStream_length_not_bound_depth :
    ∃ (cs : List (Clause 5)) (ρ : Fin 5 → Option Bool),
      (blockStream cs 10 ρ).length * 2 < (canonicalDTree cs 2 10 ρ).depth :=
  ⟨csCex, rhoCex, by decide⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockStream_length_not_bound_depth
