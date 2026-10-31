import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBoundaryTransducer

/-!
# N-Frame: cut-based boundary *dimension* (treewidth-flavoured refinement)

The boundary-transducer file measured the *volume* (node count) of the boundary graph.  This file adds the refinement
book1's "SPDP event horizon" is really about: the **boundary dimension** — not how big the graph is, but how *wide* its
computational cut is.  For a bounded-degree transducer tree the natural cut measure is the **register / cut-width** (the
Horton–Strahler number): the maximum number of values that must be simultaneously live as evaluation sweeps through the
graph.  This is the width of the "boundary front" an observer must hold — the low-dimensional / low-curvature quantity.

  `width` — the Horton–Strahler cut-width of a transducer (two equal-width children need one extra register; otherwise the
        wider child dominates).
  `boundaryDim f` — the minimum cut-width over transducers computing `f`.
  `boundaryDim_const_le` / `boundaryDim_var_le` — constants and variables have boundary dimension `≤ 1`.
  `boundaryDim_fullAnd_le` — **the sharp inversion correction**: the full-AND has boundary dimension `≤ 2` — **constant**,
        independent of `n` — while its raw multilinear degree is the *maximal* `n`.  The cut-based dimension rates the
        trivial local structure at `O(1)`, far sharper than the linear volume bound.
  `boundaryDim_bin_le` — **composition raises the dimension by at most one** (`≤ max(dim f, dim g) + 1`).  Unlike volume
        (which adds), the boundary *dimension* grows only logarithmically in balanced composition and not at all along an
        unbalanced chain — the genuinely low-dimensional behaviour of a low-curvature boundary.

## Honest scope — a finer boundary, capturing a finer class

Cut-width is a *space / width* measure, not size: `boundaryDim f` small means `f` has *some* narrow-cut (sequentially
evaluable) transducer, e.g. an iterated chain (AND, OR, parity, thresholds).  So the low-`boundaryDim` class is a genuine
**width/space-bounded** class — *finer* than `P`, and matching book1's SPDP-rank "codimension" picture more closely than
raw size does.  The two boundary measures are complementary: *volume* (previous file) has `P`-capture for free; *dimension*
(here) captures a width-bounded class with far sharper anti-inversion.  The "tearing" gap — an `NP`/`VNP` target forcing a
*wide* cut under *every* admissible embedding — is now a concrete cut-width lower bound.  That gap is unproved (it is a
width/space lower bound, still open), and low boundary dimension does **not** by itself imply low size.  This file supplies
the refined dimension and its (sharp) tests; it does not prove the gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-- The **Horton–Strahler cut-width** of a boundary transducer: the number of simultaneously-live registers needed to
sweep the graph.  Two equal-width children force one extra register; an unequal split is dominated by the wider child. -/
def width : Trans n → ℕ
  | .var _ => 1
  | .cst _ => 1
  | .un _ t => width t
  | .bin _ t₁ t₂ => if width t₁ = width t₂ then width t₁ + 1 else max (width t₁) (width t₂)

/-- The **minimum boundary dimension** of `f`: the least cut-width over transducers computing `f`. -/
noncomputable def boundaryDim (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {w | ∃ t : Trans n, eval t = f ∧ width t = w}

/-- **Constants have boundary dimension `≤ 1` (proved).** -/
theorem boundaryDim_const_le (b : Bool) : boundaryDim (fun _ : Fin n → Bool => b) ≤ 1 :=
  Nat.sInf_le ⟨Trans.cst b, rfl, rfl⟩

/-- **Variables have boundary dimension `≤ 1` (proved).** -/
theorem boundaryDim_var_le (i : Fin n) : boundaryDim (fun x : Fin n → Bool => x i) ≤ 1 :=
  Nat.sInf_le ⟨Trans.var i, rfl, rfl⟩

/-- **The full-AND chain has constant cut-width `≤ 2` (proved).** -/
theorem width_andVars_le (is : List (Fin n)) : width (andVars is) ≤ 2 := by
  induction is with
  | nil => simp [andVars, width]
  | cons i is ih =>
    simp only [andVars, width]
    split <;> omega

/-- **The full-AND has boundary dimension `≤ 2` — constant (proved).**  Its cut-width is `O(1)` while its raw multilinear
degree is the maximal `n` (`nframeComplexity_sqfEval_univ_eq`): the cut-based dimension corrects the raw-degree inversion
*sharply*, rating the trivial local structure at constant dimension. -/
theorem boundaryDim_fullAnd_le : boundaryDim (fullAndFn n) ≤ 2 :=
  le_trans
    (Nat.sInf_le ⟨andVars (List.finRange n), by funext x; rw [eval_andVars]; rfl, rfl⟩)
    (width_andVars_le _)

/-- **Composition raises boundary dimension by at most one (proved).**  Combining two realisable sub-computations by a
bounded-degree gate costs at most one extra register — so the boundary *dimension* grows logarithmically under balanced
composition and not at all along an unbalanced chain. -/
theorem boundaryDim_bin_le (op : Bool → Bool → Bool) (f g : (Fin n → Bool) → Bool)
    (hf : ∃ t : Trans n, eval t = f) (hg : ∃ t : Trans n, eval t = g) :
    boundaryDim (fun x => op (f x) (g x)) ≤ max (boundaryDim f) (boundaryDim g) + 1 := by
  have hnf : {w | ∃ t : Trans n, eval t = f ∧ width t = w}.Nonempty := by
    obtain ⟨t, ht⟩ := hf; exact ⟨width t, t, ht, rfl⟩
  have hng : {w | ∃ t : Trans n, eval t = g ∧ width t = w}.Nonempty := by
    obtain ⟨t, ht⟩ := hg; exact ⟨width t, t, ht, rfl⟩
  obtain ⟨tf, hef, hwf⟩ := Nat.sInf_mem hnf
  obtain ⟨tg, heg, hwg⟩ := Nat.sInf_mem hng
  refine le_trans (Nat.sInf_le ⟨Trans.bin op tf tg, ?_, rfl⟩) ?_
  · funext x; simp only [eval]; rw [hef, heg]
  · simp only [width, boundaryDim]
    rw [hwf, hwg]
    split <;> omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.boundaryDim_fullAnd_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.boundaryDim_bin_le
