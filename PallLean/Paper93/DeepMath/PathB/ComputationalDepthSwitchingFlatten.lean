import Mathlib.Data.List.Basic

/-!
# Flatten / group: packing per-term index-blocks into a delimited flat sequence

**STATUS: REAL.  THE COMBINATORIAL CORE OF THE `(2w)^s` LABEL.**

The compact `(2w)^s` label is a flat sequence of `(index, isLastInBlock)` steps; the
per-term index-blocks are recovered by splitting at the `isLast = true` delimiters.  This
file proves the round-trip (group ∘ ungroup = id on nonempty-block lists), giving the
flatten injective — the key fact for `hlabdet` (the label determines the blocks).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

/-- Mark a block's last element with `true` (the delimiter), the rest with `false`. -/
def markLast : List ℕ → List (ℕ × Bool)
  | [] => []
  | [x] => [(x, true)]
  | x :: y :: xs => (x, false) :: markLast (y :: xs)

/-- Ungroup (flatten/encode): concatenate the delimiter-marked blocks. -/
def ungroupBlocks : List (List ℕ) → List (ℕ × Bool)
  | [] => []
  | b :: bs => markLast b ++ ungroupBlocks bs

/-- Group (decode): split the flat sequence into blocks at the `true` delimiters. -/
def groupBlocks : List (ℕ × Bool) → List (List ℕ)
  | [] => []
  | (x, true) :: rest => [x] :: groupBlocks rest
  | (x, false) :: rest =>
    match groupBlocks rest with
    | [] => [[x]]
    | b :: bs => (x :: b) :: bs

/-- Grouping a marked nonempty block (prepended to a tail) recovers the block. -/
theorem groupBlocks_markLast_append (b : List ℕ) (hb : b ≠ []) (rest : List (ℕ × Bool)) :
    groupBlocks (markLast b ++ rest) = b :: groupBlocks rest := by
  induction b with
  | nil => exact absurd rfl hb
  | cons x xs ih =>
    cases xs with
    | nil => simp [markLast, groupBlocks]
    | cons y ys =>
      show groupBlocks ((x, false) :: (markLast (y :: ys) ++ rest)) = _
      show (match groupBlocks (markLast (y :: ys) ++ rest) with
        | [] => [[x]] | b :: bs => (x :: b) :: bs) = _
      rw [ih (by simp)]

/-- **Round-trip.**  Grouping the ungrouped blocks recovers them (nonempty blocks) — so the
flatten `ungroupBlocks` is injective. -/
theorem groupBlocks_ungroupBlocks (bs : List (List ℕ)) (hbs : ∀ b ∈ bs, b ≠ []) :
    groupBlocks (ungroupBlocks bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [ungroupBlocks,
      groupBlocks_markLast_append b (hbs b (List.mem_cons.mpr (Or.inl rfl))) _,
      ih (fun b' hb' => hbs b' (List.mem_cons.mpr (Or.inr hb')))]

/-- The flatten is injective on nonempty-block lists. -/
theorem ungroupBlocks_inj {bs cs : List (List ℕ)}
    (hbs : ∀ b ∈ bs, b ≠ []) (hcs : ∀ b ∈ cs, b ≠ [])
    (h : ungroupBlocks bs = ungroupBlocks cs) : bs = cs := by
  have := groupBlocks_ungroupBlocks bs hbs
  rw [h, groupBlocks_ungroupBlocks cs hcs] at this
  exact this.symm

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.groupBlocks_ungroupBlocks
