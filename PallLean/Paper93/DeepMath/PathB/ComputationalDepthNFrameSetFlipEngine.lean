import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameWholeBlockAssembly

/-!
# N-Frame: the set-flip engine — squares and triples from agreement, not single flips

The generalization named at the two-mass residual: the kill patterns need not be single-coordinate
flips.  Any four points forming an **agreement rectangle** — `w₂` agreeing with `w₁` on `S`, `w₃`
agreeing with `w₁` off `S`, `w₄` agreeing with `w₃` on `S` and with `w₂` off `S` — present the full 2×2
op-submatrix, because blindness collapses each side.  Set-flips (`p, p⊕A, p⊕B, p⊕A⊕B` with `A ⊆ S`,
`B ⊆ Sᶜ`) are the constructible special case; L-triples need only three points.

  `set_squares_kill_split` — **PROVED, the engine**: an agreement-rectangle odd square, an agreement
        V1 triple, and an agreement V0 triple — at arbitrary, possibly unrelated point families — kill
        any split.  Core (`odd_matrix_triples_kill`) reused verbatim; the entire proof is eight blindness
        applications.  Subsumes both prior engines (single-coordinate updates satisfy the agreements).

## Honest scope — a discovery recorded

While instantiating this for the two-mass cut, a simpler route surfaced: the pair
(slot-2 selector on pinned `j₀`, pin-sign of `j₀`) has the table `sel ∧ bvec j₀` at the empty-designated
context — pure AND, carrying **V0 and odd with single flips** (the identification lemma makes the
pin-sign flip a `bvec` flip).  In the two-mass cut both this pair and the OR-carrying
(sign, selector) pair are separated, so the mixed single-coordinate engine suffices once the
pinned-selector eval (`f = sel && bvec j₀`) is produced — a modest workhorse mirror, named next.  The
set-flip engine remains the general tool for cuts whose known-side structure is coarser than single
coordinates.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE SET-FLIP ENGINE (proved)**: agreement-rectangle odd square + agreement L-triples kill any
split — blindness alone exposes the op-matrix cells. -/
theorem set_squares_kill_split {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (op : Bool → Bool → Bool) (g h : (Fin n → Bool) → Bool)
    (hg : ∀ x y : Fin n → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y)
    (hf : ∀ x, f x = op (g x) (h x))
    (w₁ w₂ w₃ w₄ u₁ u₂ u₄ z₁ z₂ z₄ : Fin n → Bool)
    -- the odd agreement rectangle
    (hw2 : ∀ i, i ∈ S → w₂ i = w₁ i) (hw3 : ∀ i, i ∉ S → w₃ i = w₁ i)
    (hw4S : ∀ i, i ∈ S → w₄ i = w₃ i) (hw4T : ∀ i, i ∉ S → w₄ i = w₂ i)
    (hodd : xor (xor (f w₁) (f w₃)) (xor (f w₂) (f w₄)) = true)
    -- the V1 agreement triple
    (hu2S : ∀ i, i ∈ S → u₂ i = u₁ i) (hu2T : ∀ i, i ∉ S → u₂ i = u₄ i)
    (h11 : f u₁ = true) (h12 : f u₄ = true) (h13 : f u₂ = false)
    -- the V0 agreement triple
    (hz2S : ∀ i, i ∈ S → z₂ i = z₁ i) (hz2T : ∀ i, i ∉ S → z₂ i = z₄ i)
    (h01 : f z₁ = false) (h02 : f z₄ = false) (h03 : f z₂ = true) : False := by
  have e2 : g w₂ = g w₁ := hg _ _ hw2
  have e3 : h w₃ = h w₁ := hh _ _ hw3
  have e4g : g w₄ = g w₃ := hg _ _ hw4S
  have e4h : h w₄ = h w₂ := hh _ _ hw4T
  have eu2g : g u₂ = g u₁ := hg _ _ hu2S
  have eu2h : h u₂ = h u₄ := hh _ _ hu2T
  have ez2g : g z₂ = g z₁ := hg _ _ hz2S
  have ez2h : h z₂ = h z₄ := hh _ _ hz2T
  rw [hf, hf, hf, hf] at hodd
  rw [hf] at h11 h12 h13 h01 h02 h03
  rw [e3, e2, e4g, e4h] at hodd
  rw [eu2g, eu2h] at h13
  rw [ez2g, ez2h] at h03
  exact odd_matrix_triples_kill op
    (g w₁) (h w₁) (g w₃) (h w₂)
    (g u₁) (h u₁) (g u₄) (h u₄)
    (g z₁) (h z₁) (g z₄) (h z₄)
    hodd h11 h12 h13 h01 h02 h03

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.set_squares_kill_split
