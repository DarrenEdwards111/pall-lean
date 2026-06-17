import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndFanIn

/-!
# The additive bottom-layer merge — pooling monomials into one symmetric gate (proved)

The `…ACC0SymAndFanIn` file proves the `SYM∘AND` *tree* merge `hasSymAndFormFanIn_combine`, whose count is
**multiplicative** (`s₁ + (s₁+1)·s₂`) — the Beigel–Tarui bottleneck, exponential in general.  That multiplicative blow-up
happens because the tree keeps the two sub-counts *separate* (mixed-radix, so a higher symmetric gate can read each).
This file proves the complementary **additive** merge: when the monomials of both sides feed **one common symmetric
gate** (the genuine `SYM∘AND` bottom layer), the counts simply **add** — `s₁ + s₂` — with no blow-up.  This is the
`FanInStaysPolylog`-style additive count at a single symmetric layer.

## What is proved (clean axioms, no `sorry`)

* **`hasSymAndFormFanIn_pool`** — pooling: a symmetric top `h` applied to the *sum* of two monomial-count families
  `h (saCount mono₁ x + saCount mono₂ x)` has size `card ι₁ + card ι₂` (**additive**) and fan-in `w` — via
  `saCount_sum_elim` (the pooled `Sum.elim` count is the sum) and `Fintype.card_sum`.
* **`hasSymAndFormFanIn_family`** — the canonical `SYM∘AND` over a concrete family of `m` monomials
  (`mono : Fin m → Finset (Fin n)`) has size exactly `m` (additive in the *number* of monomials).

## Honest scope

This proves the **additive** per-layer count of `SYM∘AND`: pooling `m` monomials feeding one symmetric gate has size
`m` (and pooling two families is additive `s₁ + s₂`), in contrast to the multiplicative *tree* merge.  This is exactly
the regime where the count stays small — a single symmetric layer over polynomially many monomials.  What this does
**not** prove is the deep Beigel–Tarui theorem that an *entire* constant-depth `ACC⁰` circuit collapses to **one** such
symmetric layer with only *quasipolynomially* many monomials; that collapse (the multiplicative tree replaced by a
single additive layer) is the genuine BT construction and remains the socket.  This proves the additive bottom layer,
not the depth-collapse.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymAndPool

open PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn (HasSymAndFormFanIn)
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose (saCount saCount_sum_elim)

variable {n : ℕ}

/-- **The additive pooled merge (PROVED).**  When the monomials of two families both feed *one* symmetric gate — i.e.
the top reads the *sum* of the two counts `saCount mono₁ x + saCount mono₂ x` — the `SYM∘AND` has size
`card ι₁ + card ι₂` (**additive**, no blow-up) and fan-in `w`.  The pooled index is `ι₁ ⊕ ι₂`, the pooled count is the
sum (`saCount_sum_elim`), and `Fintype.card_sum` gives the additive size. -/
theorem hasSymAndFormFanIn_pool {ι1 ι2 : Type} [Fintype ι1] [Fintype ι2]
    (mono1 : ι1 → Finset (Fin n)) (mono2 : ι2 → Finset (Fin n)) (h : ℕ → Bool) {w : ℕ}
    (hw1 : ∀ j, (mono1 j).card ≤ w) (hw2 : ∀ j, (mono2 j).card ≤ w) :
    HasSymAndFormFanIn (fun x => h (saCount mono1 x + saCount mono2 x))
      (Fintype.card ι1 + Fintype.card ι2) w := by
  refine ⟨ι1 ⊕ ι2, inferInstance, Sum.elim mono1 mono2, h, ?_, ?_, ?_⟩
  · rw [Fintype.card_sum]
  · rintro (a | b)
    · exact hw1 a
    · exact hw2 b
  · funext x; rw [saCount_sum_elim]

/-- **The canonical bottom layer (PROVED).**  A `SYM∘AND` over a concrete family of `m` monomials
`mono : Fin m → Finset (Fin n)` (fan-in `≤ w`) has size exactly `m` — additive in the *number* of monomials, the BT
bottom-layer count. -/
theorem hasSymAndFormFanIn_family {m : ℕ} (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool) {w : ℕ}
    (hw : ∀ j, (mono j).card ≤ w) :
    HasSymAndFormFanIn (fun x => h (saCount mono x)) m w :=
  ⟨Fin m, inferInstance, mono, h, by rw [Fintype.card_fin], hw, rfl⟩

end PallLean.Paper93.DeepMath.PathB.ACC0SymAndPool

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndPool.hasSymAndFormFanIn_pool
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndPool.hasSymAndFormFanIn_family
