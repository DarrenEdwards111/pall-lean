import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonLabel

/-!
# Status of the clause-block side conditions `hne` / `hlen` / `hmem`

`canonMarkLabel_switching_count` (the general `(2w)^s` labeled count) carries three side conditions
on the bad set.  Their honest status:

* **`hlen`** (canonical flat length `= s`) — discharged *by definition* for the path-length bad set:
  `canon_count_pathLenBad` consumes it from `pathLenBad`'s filter membership.
* **`hmem`** (completion lands in `Short`) — discharged by `completion_mem_stars`: a bad `ρ` in the
  star-`K` family with path length `s` has `complete ρ (encLits ρ cs) ∈ {stars = K−s}`
  (`stars_complete_encLits`), so `Short := {stars = K−s}` works.
* **`hne`** (every canonical block nonempty) — **genuinely false for the raw `termSat`-filter.**  A
  clause `C` satisfied by `ρ` *alone* has `freeLits ρ C = []`, so `encLits` records no path literal
  for it, yet `C` is in `cs.filter (termSat (complete ρ (encLits ρ cs)))` (it stays satisfied under
  the completion).  Its canonical variable block `termBlock (encLits ρ cs) C \ claimed` is then
  empty, and so is its position block — violating `hne`.

This file proves the **mechanism** behind the `hne` failure, cleanly:

* `canonPosBlock_eq_nil_of_block_empty` — an empty variable block forces an empty position block.
  (Its variables are exactly `termBlock litList C \ claimed` by `canonPosBlock_blockVars`; a nonempty
  position block would contribute a variable, so the block must be `[]`.)

So `hne` cannot be discharged for the raw filter.  The honest resolutions, neither faked here:
the **tokenized** count (`tokFlatten`/`tokFlatten_inj`, empty-block-tolerant — no `hne`) at the cost
of a delimiter-padded label, or restricting the clause family so no clause is satisfied by `ρ`
alone.  `hlen` and `hmem` are genuinely discharged (above).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **The `hne` mechanism.**  If a clause's canonical variable block `termBlock litList C \ claimed`
is empty, its canonical *position* block is the empty list — so the delimiter-free `(2w)^s` count's
`hne` (all blocks nonempty) fails exactly when a clause contributes no fresh path variable. -/
theorem canonPosBlock_eq_nil_of_block_empty (litList : List (Rung4Literal n))
    (claimed : Finset (Fin n)) (C : Clause n)
    (h : termBlock litList C \ claimed = ∅) : canonPosBlock litList claimed C = [] := by
  by_contra hne
  obtain ⟨i, t, ht⟩ := List.exists_cons_of_ne_nil hne
  have hi : i ∈ canonPosBlock litList claimed C := by rw [ht]; exact List.mem_cons_self
  have hi' := hi
  rw [canonPosBlock, List.mem_filter] at hi'
  obtain ⟨_, hP⟩ := hi'
  cases hg : C.lits[i]? with
  | none => rw [hg] at hP; simp at hP
  | some ℓ =>
    have hv : litVar ℓ ∈ blockVars C (canonPosBlock litList claimed C) :=
      mem_blockVars.mpr ⟨i, hi, by rw [hg]; rfl⟩
    rw [canonPosBlock_blockVars, h] at hv
    exact absurd hv (Finset.notMem_empty _)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonPosBlock_eq_nil_of_block_empty
