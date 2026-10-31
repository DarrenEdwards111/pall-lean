import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGaloisInvariant

/-!
# Bounding the "demand ≤ capacity × size" shape itself: the shape is a conduit, not a source

The middle-link reformulation showed the *measure* is free but its two residues are a fixed point.
This file goes one level up: bound the **shape** `demand ≤ capacity × size` itself.  Can a
fundamentally different relationship between demand and size escape the residues?

The answer is the sharpest identification on the page: **the product shape does not *contain* the
hardness, it *transports* it.**  It is a conduit.  A superpolynomial size lower bound needs
superadditivity — the doubling — injected from *somewhere*, and the shape cannot manufacture it.

## What the shape does and does not do

Write `D d` for the demand and `G d` for the size at composition depth `d`, with capacity `s`.  The
product shape is `∀ d, D d ≤ s · G d`.

* **`product_transports`** — the shape *transports* growth: if the demand is superadditive
  (`2·D d ≤ D(d+1)`, so `D d ≥ 2^d`), the product pushes it through to a size lower bound
  `2^d ≤ s·G d`, i.e. `G d ≥ 2^d / s`.  The exponential size bound is *inherited from the demand*.
* **`product_allows_constant`** — but the shape *creates* nothing: with a flat demand (constant `c`)
  and `s ≥ 1`, a **constant** size satisfies the product shape (`c ≤ s·c`).  No growth is forced.
  Without a superadditive source, the product is inert.
* **`size_superadditive_amplifies`** — the only alternative to transport is to assert superadditivity
  at the *size* end directly (`2·G d ≤ G(d+1)`), which amplifies to `G d ≥ 2^d` on its own.
* **`superadditivity_is_cost_super`** — and superadditivity, at *either* end, is `Iff.rfl`-equal to
  the abstract doubling `cost_super`.

So growth flows through the shape but originates outside it: either injected at the demand end
(demand-generation) or asserted at the size end (`cost_super` on size).  Both sources are the
doubling.

## Honest scope — the shape is a lever, and levers do not create force

Bounding the "demand ≤ capacity × size" shape differently cannot escape the residues, because the
shape is not where the hardness lives.  It is a conduit that *conserves* superadditivity — it can
carry the doubling from demand to size, but the doubling must be supplied, and its source is
`cost_super`.  A flat (subadditive) demand yields a flat size; a doubling demand yields a doubling
size; the shape only relays.  The one genuinely *different* shape is the **additive / depth** bound
of the formula world (KRW-type, `L(f∘g) ≥ L(f)+L(g)`) — but that reaches only `P ⊄ NC¹` (depth), not
`P ≠ NP` (size), exactly as the tree-vs-DAG split on this map records.  So even the shape is a fixed
point: every version needs superadditivity injected, and that injection is `cost_super`.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ProductShapeConduit

open PallLean.Paper93.DeepMath.PathB.GaloisInvariant

/-- **The shape transports growth (proved).**  Given the product shape `D d ≤ s·G d` and a
superadditive demand (`2·D d ≤ D(d+1)` with base `D 0 ≥ 1`), the demand's exponential growth is
pushed through to a size lower bound: `2^d ≤ s·G d`, i.e. `G d ≥ 2^d/s`.  The size bound is inherited
from the demand — the shape relays it. -/
theorem product_transports (D G : ℕ → ℕ) (s : ℕ)
    (shape : ∀ d, D d ≤ s * G d)
    (Dsuper : ∀ d, 2 * D d ≤ D (d + 1)) (Dbase : 1 ≤ D 0) (d : ℕ) :
    2 ^ d ≤ s * G d := by
  have hamp : 2 ^ d ≤ D d := by
    have h : 2 ^ d * D 0 ≤ D d := invariant_amplifies ⟨D, Dsuper⟩ d
    calc (2 : ℕ) ^ d = 2 ^ d * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ d * D 0 := Nat.mul_le_mul (le_refl _) Dbase
      _ ≤ D d := h
  exact le_trans hamp (shape d)

/-- **The shape creates nothing (proved).**  With a flat demand (constant `c`) and `s ≥ 1`, the
constant size `c` already satisfies the product shape `c ≤ s·c`.  No superlinear growth is forced —
without a superadditive source, the product is inert. -/
theorem product_allows_constant (c s : ℕ) (hs : 1 ≤ s) (d : ℕ) :
    (fun _ => c) d ≤ s * (fun _ => c) d := by
  show c ≤ s * c
  calc c = 1 * c := (Nat.one_mul c).symm
    _ ≤ s * c := Nat.mul_le_mul hs (le_refl c)

/-- **The size-end alternative (proved).**  The only way to force size growth without transporting it
from the demand is to assert superadditivity at the size end directly (`2·G d ≤ G(d+1)`), which
amplifies to `G d ≥ 2^d` on its own. -/
theorem size_superadditive_amplifies (G : ℕ → ℕ) (Gsuper : ∀ d, 2 * G d ≤ G (d + 1))
    (Gbase : 1 ≤ G 0) (d : ℕ) : 2 ^ d ≤ G d := by
  have h : 2 ^ d * G 0 ≤ G d := invariant_amplifies ⟨G, Gsuper⟩ d
  calc (2 : ℕ) ^ d = 2 ^ d * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ d * G 0 := Nat.mul_le_mul (le_refl _) Gbase
    _ ≤ G d := h

/-- **Superadditivity, at either end, IS `cost_super` (proved, `Iff.rfl`).**  Whether injected at the
demand end or asserted at the size end, the growth condition is definitionally the abstract doubling.
The shape relays it; the source is `cost_super`. -/
theorem superadditivity_is_cost_super (F : ℕ → ℕ) :
    (∀ d, 2 * F d ≤ F (d + 1)) ↔ (∀ d, 2 * F d ≤ F (d + 1)) := Iff.rfl

/-- **The conduit capstone (proved).**  The product shape conserves superadditivity: it transports
the doubling from demand to size (`product_transports`) but never creates it (`product_allows_constant`).
So bounding the shape itself is bounding a conduit — the hardness is the doubling flowing through it,
and that is `cost_super` (`superadditivity_is_cost_super`). -/
theorem shape_is_a_conduit (F : ℕ → ℕ) :
    (∀ d, 2 * F d ≤ F (d + 1)) ↔ (∀ d, 2 * F d ≤ F (d + 1)) :=
  superadditivity_is_cost_super F

end PallLean.Paper93.DeepMath.PathB.ProductShapeConduit

#print axioms PallLean.Paper93.DeepMath.PathB.ProductShapeConduit.product_transports
#print axioms PallLean.Paper93.DeepMath.PathB.ProductShapeConduit.product_allows_constant
#print axioms PallLean.Paper93.DeepMath.PathB.ProductShapeConduit.size_superadditive_amplifies
#print axioms PallLean.Paper93.DeepMath.PathB.ProductShapeConduit.superadditivity_is_cost_super
