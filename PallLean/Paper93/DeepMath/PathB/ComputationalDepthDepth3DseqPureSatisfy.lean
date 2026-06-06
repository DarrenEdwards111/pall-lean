import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqDecoder
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEncLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyReconstruction

/-!
# `Dseq` correctness in the pure-satisfy regime (branch `razborov-recoverRho-wip`)

We instantiate the encoder for `Dseq` with the **correct Side-B label** and prove `Dseq` reproduces
`deepestSatSeq` in the pure-satisfy regime.

**Encoder choice — a correction.**  `packLabel` is the *Side-A* (satisfying-completion / `encLits`)
encoder: `packLabel = flatToLabel (toFinW (ungroupBlocks (encBlocks …)))` with `encBlocks` filtering the
clauses *satisfied under the completion*.  That is a different route from `Dseq`, which walks
`leafClauses` (the Side-B / deepest-branch route where `deepestSatSeq` lives).  So the encoder that pairs
with `Dseq` is the **`replayLabel`-based** one:

  `lab ρ := flatToLabel (toFinW w (ungroupBlocks (replayLabel cs F ρ)))`,

with `replayLabel = (leafClauses cs (deepestEnd …)).map (deepestSatPositions …)` over the *same*
`leafClauses` and the `ungroupBlocks` `isLast` bit = the block-delimiter `takeBlock` reads.

**Pure-satisfy regime.**  One clause `T` stays active throughout (no falsify step), so
`leafClauses cs (deepestEnd …) = [T]` and every entry of `deepestSatSeq` is on `T`.  The label is then a
single block, `takeBlock` consumes it whole, and `Dseq` reproduces `deepestSatSeq`.  We take the two
structural facts (single leaf clause; all entries on `T`) as hypotheses — they are the genuine
characterisation of the pure-satisfy bad set (cf. `activeTerm_deepestEnd_pure_satisfy`).

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-! ## Decoder round-trip on a single block -/

/-- If the whole token list is one block (`takeBlock` leaves no remainder), a one-clause walk emits
every token attributed to that clause. -/
theorem replayBlocksFlat_single {w : ℕ} (C : Clause n) (toks : List (Fin w × Bool))
    (h : (takeBlock toks).2 = []) :
    replayBlocksFlat [C] toks = toks.map (fun t => (C, (t.1 : ℕ))) := by
  have hblk : (takeBlock toks).1 = toks := by
    have ht := takeBlock_fst_append_snd toks; rw [h, List.append_nil] at ht; exact ht
  show (takeBlock toks).1.map (fun t => (C, (t.1 : ℕ)))
      ++ replayBlocksFlat ([] : List (Clause n)) (takeBlock toks).2
        = toks.map (fun t => (C, (t.1 : ℕ)))
  rw [h, replayBlocksFlat_nil, List.append_nil, hblk]

/-! ## `markLast` / `toFinW` round-trip -/

/-- `markLast` preserves the underlying indices. -/
theorem markLast_map_fst : ∀ b : List ℕ, (markLast b).map Prod.fst = b
  | [] => rfl
  | [_] => rfl
  | x :: y :: xs => by
      rw [markLast, List.map_cons, markLast_map_fst (y :: xs)]

/-- A `markLast` block is a single block: `takeBlock` (after the `Fin w` coercion) leaves no remainder
(the only `true` bit is on the last element). -/
theorem takeBlock_snd_nil_of_markLast {w : ℕ} [NeZero w] :
    ∀ b : List ℕ, (takeBlock (toFinW w (markLast b))).2 = []
  | [] => rfl
  | [_] => rfl
  | x :: y :: xs => by
      have hb : toFinW w (markLast (x :: y :: xs))
          = (SwitchingCounting.natToFin w x, false) :: toFinW w (markLast (y :: xs)) := rfl
      have key : (takeBlock ((SwitchingCounting.natToFin w x, false)
            :: toFinW w (markLast (y :: xs)))).2
          = (takeBlock (toFinW w (markLast (y :: xs)))).2 := by
        rw [takeBlock]
        cases takeBlock (toFinW w (markLast (y :: xs))) with
        | mk b r => rfl
      rw [hb, key]
      exact takeBlock_snd_nil_of_markLast (y :: xs)

/-- The coerced `markLast` tokens, attributed to a clause, give back the original index blocks. -/
theorem map_toFinW_markLast {w : ℕ} [NeZero w] :
    ∀ (b : List ℕ) (T : Clause n), (∀ p ∈ b, p < w) →
      (toFinW w (markLast b)).map (fun t => (T, (t.1 : ℕ))) = b.map (fun p => (T, p))
  | [], _, _ => rfl
  | [x], T, hlt => by
      have hx : x < w := hlt x (List.mem_cons_self)
      simp [markLast, toFinW, SwitchingCounting.natToFin_val hx]
  | x :: y :: xs, T, hlt => by
      have hx : x < w := hlt x List.mem_cons_self
      have hb : toFinW w (markLast (x :: y :: xs))
          = (SwitchingCounting.natToFin w x, false) :: toFinW w (markLast (y :: xs)) := rfl
      rw [hb, List.map_cons, List.map_cons,
          show ((SwitchingCounting.natToFin w x : Fin w) : ℕ) = x from
            SwitchingCounting.natToFin_val hx,
          map_toFinW_markLast (y :: xs) T (fun p hp => hlt p (List.mem_cons_of_mem x hp))]

/-! ## Pure-satisfy correctness of `Dseq` -/

/-- **`Dseq` reproduces `deepestSatSeq` in the pure-satisfy regime.**  With the `replayLabel`-based
Side-B encoder, and the two structural facts of the pure-satisfy bad set — a single leaf clause `T`,
all `deepestSatSeq` entries on `T` — the concrete decoder `Dseq` recovers `deepestSatSeq` exactly. -/
theorem Dseq_correct_pure_satisfy {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {ρ : Fin n → Option Bool} {T : Clause n}
    (hleaf1 : leafClauses cs (deepestEnd cs F ρ) = [T])
    (hseq : deepestSatSeq cs F ρ = (deepestSatPositions cs F ρ T).map (fun p => (T, p)))
    (hlen : (deepestSatPositions cs F ρ T).length = s)
    (hlt : ∀ p ∈ deepestSatPositions cs F ρ T, p < w) :
    Dseq cs (deepestEnd cs F ρ)
        (SwitchingCounting.flatToLabel
            (toFinW w (ungroupBlocks (replayLabel cs F ρ))) : SwitchingCounting.PathLabel w s)
      = deepestSatSeq cs F ρ := by
  have hrl : replayLabel cs F ρ = [deepestSatPositions cs F ρ T] := by
    rw [replayLabel, hleaf1, List.map_cons, List.map_nil]
  have hug : ungroupBlocks (replayLabel cs F ρ) = markLast (deepestSatPositions cs F ρ T) := by
    rw [hrl, ungroupBlocks, ungroupBlocks, List.append_nil]
  have hlenF : (toFinW w (markLast (deepestSatPositions cs F ρ T))).length = s := by
    rw [toFinW, List.length_map, markLast_length, hlen]
  rw [Dseq, hleaf1, hug, ofFn_flatToLabel hlenF,
      replayBlocksFlat_single T _ (takeBlock_snd_nil_of_markLast _),
      map_toFinW_markLast _ T hlt]
  exact hseq.symm

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Dseq_correct_pure_satisfy
