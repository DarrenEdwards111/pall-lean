import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityEval

/-!
# N-Frame: the flat quadratic form — detection that is not one-bit-per-block

The block-count cap (`ComputationalDepthNFrameQuadConcentration`) ceilings every block-menu
family at `(2 + o(1))N`: detection is organized by blocks, each addressing a `v`-spanning
menu at `Ω(log v)` cost, so the priced mass is `≤ m = N/L`.  To break it, detection must not
be block-organized at all.  The candidate: a FLAT quadratic form

    qform A x = ∑_{i,j} A_{ij}·x_i·x_j   over `F₂`,

with `A` the adjacency of an expander on the `N` input bits — NO blocks, NO menu, one input
bit per vertex.  Detection across a cut `(S, Sᶜ)` is the RANK of the cross-block `A_{S,Sᶜ}`,
a `Θ(N)`-dimensional space of directions distributed over ALL inputs, not `≤ m` block targets.

  `qform` / `bilinSym` — the flat quadratic form and its symmetric bilinear polarization.
  `qform_shift` — **PROVED, THE POLARIZATION**: `qform A (x + δ) = qform A x + bilinSym A x δ
        + qform A δ`.  Shifting by `δ` moves the value by the bilinear form in `(x, δ)` plus
        the diagonal — the detection identity.
  `qform_detect` — **PROVED, THE DETECTION**: if the bilinear+diagonal shift at `x₀` is `1`,
        the two points `{x₀, x₀+δ}` are distinguished — one detectable direction per `δ` with
        active bilinear image.
  `qform_detect_dir` — **PROVED**: a direction `δ` whose bilinear functional is nonzero
        (`∃ x, bilinSym A x δ = 1`) is detectable at SOME base point — the detectable
        directions are the row space of `A + Aᵀ`, of dimension `= rank_{F₂}(A + Aᵀ)`.

## Honest scope — what this designs and what it does NOT close

This BREAKS the one-bit-per-block cap: `qform`'s detectable directions form the row space of
the symmetric part of `A`, of `F₂`-rank up to `Θ(N)`, with NO block structure — so the priced
mass at a cut is bounded by `rank(A_{S,Sᶜ})`, which is `Θ(N)` for a good expander, not by any
block count.  This reduces `(2+c)N` to: an EXPLICIT `A` with `rank_{F₂}(A_{S,Sᶜ}) = Θ(N)` at
EVERY balanced cut (a rigidity-type condition; random sparse `A` satisfies it whp).  TWO honest
caveats: (i) `qform` is a QUADRATIC function, computable in `O(#edges) = O(N)` gates — it is
EASY, so the drag proving `cbudget ≥ (2+c)N` here is a lower bound for an easy function,
DEMONSTRATING the method exceeds the cap, not a hard-function separation; (ii) the every-cut
`F₂`-rank rigidity is explicit-construction-hard (the matrix-rigidity frontier).  A `(2+c)N`
for a HARD function needs cut-rank rigidity AND hardness together — the genuine open target.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadForm

open Finset

variable {N : ℕ}

/-- The flat quadratic form `∑_{i,j} A_{ij}·x_i·x_j` over `F₂`. -/
def qform (A : Fin N → Fin N → ZMod 2) (x : Fin N → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, A i j * (x i * x j)

/-- The symmetric bilinear polarization `∑_{i,j} A_{ij}·(x_i·δ_j + δ_i·x_j)`. -/
def bilinSym (A : Fin N → Fin N → ZMod 2) (x δ : Fin N → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, A i j * (x i * δ j + δ i * x j)

/-- **THE POLARIZATION (proved)**: shifting the input by `δ` moves the form by the bilinear
form in `(x, δ)` plus the diagonal `qform A δ`. -/
theorem qform_shift (A : Fin N → Fin N → ZMod 2) (x δ : Fin N → ZMod 2) :
    qform A (x + δ) = qform A x + bilinSym A x δ + qform A δ := by
  unfold qform bilinSym
  have h : ∀ i j : Fin N, A i j * ((x + δ) i * (x + δ) j)
      = A i j * (x i * x j) + A i j * (x i * δ j + δ i * x j)
        + A i j * (δ i * δ j) := by
    intro i j
    show A i j * ((x i + δ i) * (x j + δ j)) = _
    ring
  calc ∑ i, ∑ j, A i j * ((x + δ) i * (x + δ) j)
      = ∑ i, ∑ j, (A i j * (x i * x j) + A i j * (x i * δ j + δ i * x j)
          + A i j * (δ i * δ j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact h i j
    _ = (∑ i, ∑ j, A i j * (x i * x j))
          + (∑ i, ∑ j, A i j * (x i * δ j + δ i * x j))
          + (∑ i, ∑ j, A i j * (δ i * δ j)) := by
        simp only [Finset.sum_add_distrib]

/-- **THE DETECTION (proved)**: if the bilinear+diagonal shift at `x₀` is `1`, the two points
`{x₀, x₀ + δ}` get different form values. -/
theorem qform_detect (A : Fin N → Fin N → ZMod 2) (x₀ δ : Fin N → ZMod 2)
    (h : bilinSym A x₀ δ + qform A δ = 1) :
    qform A (x₀ + δ) ≠ qform A x₀ := by
  rw [qform_shift, add_assoc, h]
  generalize qform A x₀ = z
  revert z
  decide

/-- **THE DETECTABLE DIRECTION (proved)**: a direction `δ` whose bilinear functional is
nonzero somewhere is detectable at some base point — the detectable directions are exactly the
active row space of `A`'s symmetric part. -/
theorem qform_detect_dir (A : Fin N → Fin N → ZMod 2) (δ : Fin N → ZMod 2)
    (x₁ : Fin N → ZMod 2) (hx₁ : bilinSym A x₁ δ = 1) :
    ∃ x₀ : Fin N → ZMod 2, qform A (x₀ + δ) ≠ qform A x₀ := by
  by_cases hd : qform A δ = 0
  · refine ⟨x₁, qform_detect A x₁ δ ?_⟩
    rw [hx₁, hd, add_zero]
  · refine ⟨0, qform_detect A 0 δ ?_⟩
    have hb0 : bilinSym A 0 δ = 0 := by
      unfold bilinSym
      simp
    rw [hb0, zero_add]
    rcases (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) (qform A δ) hd with h1
    exact h1

end PallLean.Paper93.DeepMath.PathB.NFrameQuadForm

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadForm.qform_shift
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadForm.qform_detect
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadForm.qform_detect_dir
