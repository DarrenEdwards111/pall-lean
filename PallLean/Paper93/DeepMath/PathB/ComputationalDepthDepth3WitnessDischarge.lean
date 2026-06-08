import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessSeqProps

/-!
# Tight switching, step 30: discharging the witnessed count — `hnf` DROPPED (branch `razborov-recoverRho-wip`)

The final packaging.  Bricks 68/69 give the `hnf`-free reconstruction correctness
(`witDecode cs (deepestWitSeq cs F ρ) = deepestSel cs F ρ`) plus the structural facts (length `= depth`,
entries in range).  Here we reindex the `ℕ`-valued witness sequence into the `Fintype` `WitLabel w s m`
(`witToFin` clamps by `%`, total; `finToWit` reads `.val` back) and prove the round-trip on the bad set
`{depth = s}` (length `= s`, entries `< w`, `< m`), so the `WitLabel`-decode equals `witDecode`.  This builds
`WitnessReconstructionCorrect` with **no `hnf`**, and `deepest_count_of_witness` (step 25) then gives:

```
  |Bad| ≤ |Short| · (2·w·m)^s,
```

`F`-independent and **unconditional** — the `hnf`/empty-skip hypothesis is gone from the tight count.

* `deepest_count_witness_unconditional` — the `hnf`-free tight depth count.

## Honest scope

This drops `hnf` for the *deepest-branch* count (`deepestSel`/`deepestEnd`), at label cost `(2wm)^s`
(`F`-independent; `m` a clause-count bound).  Substituting it for the `hnf`-bearing
`deepest_switching_count_of_reconstruction` throughout `descent_switching_le_tight` →
`tight_switching_budget` → the tight arc (bricks 50–62) makes those unconditional — a mechanical rewrite of
each consumer's hypothesis and `(2w)^s → (2wm)^s` cap.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

variable {n : ℕ}

/-- Clamp a `(position, clause-index)` pair into the finite witness step (mod for totality). -/
def witToFin (w m : ℕ) [NeZero w] [NeZero m] (pc : ℕ × ℕ) : Fin w × Bool × Fin m :=
  (⟨pc.1 % w, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne w))⟩, false,
   ⟨pc.2 % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩)

/-- Read a finite witness step back to `(position, clause-index)`. -/
def finToWit {w m : ℕ} (t : Fin w × Bool × Fin m) : ℕ × ℕ := (t.1.val, t.2.2.val)

/-- Pack a witness sequence into a fixed-length `WitLabel` (indexing with a default outside range). -/
def flatToWitLabel (w s m : ℕ) [NeZero w] [NeZero m] (l : List (ℕ × ℕ)) : WitLabel w s m :=
  fun i => (l[i.val]?).elim default (witToFin w m)

/-- **Round-trip.**  On a length-`s` witness list with in-range entries, packing then reading back is the
identity. -/
theorem map_finToWit_flatToWitLabel {w s m : ℕ} [NeZero w] [NeZero m] (l : List (ℕ × ℕ))
    (hlen : l.length = s) (hb : ∀ pc ∈ l, pc.1 < w ∧ pc.2 < m) :
    (List.ofFn (flatToWitLabel w s m l)).map finToWit = l := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_ofFn, hlen]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_ofFn]
    have hi : i < l.length := by rw [hlen]; rwa [List.length_map, List.length_ofFn] at h1
    have hsome : l[i]? = some l[i] := List.getElem?_eq_getElem hi
    have hbnd := hb l[i] (List.getElem_mem hi)
    simp only [flatToWitLabel, hsome, Option.elim_some, finToWit, witToFin,
      Nat.mod_eq_of_lt hbnd.1, Nat.mod_eq_of_lt hbnd.2]

end SwitchingCounting

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The `hnf`-free tight depth count.**  With the active terms width-`≤ w`, the clause count `≤ m`, and the
deepest tree depth `= s` on `Bad`, the deepest end-state lands in `Short`, and the witnessed reconstruction
(`witDecode_deepestWitSeq`, no `hnf`) gives `|Bad| ≤ |Short|·(2wm)^s` — the empty-skip wall is gone. -/
theorem deepest_count_witness_unconditional {w F s m : ℕ} [NeZero w] [NeZero m]
    {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s)
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short) :
    Bad.card ≤ Short.card * (2 * w * m) ^ s := by
  refine deepest_count_of_witness hmem ⟨fun ρ => flatToWitLabel w s m (deepestWitSeq cs F ρ),
    fun _ wl => witDecode cs ((List.ofFn wl).map finToWit), ?_⟩
  intro ρ hρ
  show witDecode cs (List.map finToWit (List.ofFn
    (flatToWitLabel w s m (deepestWitSeq cs F ρ)))) = deepestSel cs F ρ
  have hlen : (deepestWitSeq cs F ρ).length = s :=
    (deepestWitSeq_length_eq_depth cs F ρ).trans (hdepth ρ hρ)
  have hb : ∀ pc ∈ deepestWitSeq cs F ρ, pc.1 < w ∧ pc.2 < m := fun pc hpc =>
    ⟨(deepestWitSeq_bounds cs hw F ρ pc hpc).1,
     lt_of_lt_of_le (deepestWitSeq_bounds cs hw F ρ pc hpc).2 hm⟩
  rw [map_finToWit_flatToWitLabel (deepestWitSeq cs F ρ) hlen hb, witDecode_deepestWitSeq]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_count_witness_unconditional
