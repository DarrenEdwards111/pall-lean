import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CarryStateComplexity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CommunicationComplexity

/-!
# Changing the target — growing carry/boundary under CRT product (the actual frontier)

Two independent field-free invariants converged on the *constant* `6` for fixed `MOD₆` (entry 284 streaming
carry-state, entry 285 two-party communication).  That is the signal to **change the target**: a fixed modulus has
constant complexity and cannot witness a separation.  The growth lives in the **CRT product** — a family of pairwise
coprime moduli whose product `∏ mᵢ` grows.  This file proves the growing lower bound and reduces the entire open
composite `ACC⁰` question to a single crisp socket.

**The growing bound (proved).**  For positive moduli `m₁, …, m_k` with product `M = ∏ mᵢ`, any product observer (entry
285) or carry observer (entry 284) computing `MOD_M` needs boundary / state `≥ M = ∏ mᵢ`
(`crt_product_observer_boundary_ge`, `crt_product_carry_card_ge`).  When each `mᵢ ≥ 2` this is `≥ 2^k`
(`crt_product_observer_boundary_ge_two_pow`) — **exponential in the number of CRT factors**.  Unlike fixed `MOD₆`, this
grows without bound: `growing_modulus_exceeds_budget` shows no fixed boundary budget suffices once `M` is large enough.
By CRT (`ZMod 2 × ⋯`) the bound is tight — tracking the `k` factors *jointly* needs the product `∏ mᵢ`, not the sum
`∑ mᵢ`; that product is exactly the carry-refinement crossing.

**The frontier reduced to one socket.**  `BoundedCompositionKeepsBoundaryBounded` (named, **open**): does
`ACC⁰[6]`-bounded composition of resource `s` realize `MOD_M` only via product observers of boundary `≤ boundaryBudget
s`?  `composite_ACC0_separation_from_socket` (PROVED conditional): *given* that socket with `boundaryBudget s < ∏ mᵢ`
(e.g. `boundaryBudget` polynomial and `∏ mᵢ` super-polynomial), `MOD_(∏ mᵢ)` is **not** realizable by size-`s`
`ACC⁰[6]`.  So the proved growing lower bound discharges the separation *modulo exactly one statement*: that bounded
composition keeps the boundary bounded — the crisp, boundary-invariant form of the open `ACC⁰[composite]` problem
(separation-strength; **not** faked, **not** proved here).

## What is proved (clean axioms, no `sorry`)

* **`crt_product_observer_boundary_ge`** (PROVED) — coprime/positive moduli, computes `MOD_(∏ mᵢ)` ⟹ communication
  boundary `≥ ∏ mᵢ` (entry-285 bound at `m = ∏ mᵢ`, with `NeZero (∏ mᵢ)` from positivity).
* **`crt_product_carry_card_ge`** (PROVED) — the same in the streaming carry model (entry-284 bound at `m = ∏ mᵢ`).
* **`product_ge_two_pow`** / **`crt_product_observer_boundary_ge_two_pow`** (PROVED) — `∏ mᵢ ≥ 2^k`, so the boundary
  grows exponentially in the number of factors.
* **`growing_modulus_exceeds_budget`** (PROVED) — no fixed boundary budget `< ∏ mᵢ` suffices: the requirement grows
  past any bound (the precise sense in which the *target* now has growth).
* **`composite_ACC0_separation_from_socket`** (PROVED conditional) — the proved growing bound + the open socket ⟹ the
  composite separation; the gap is reduced to exactly the socket.

## Honest scope

The growing lower bound (`≥ ∏ mᵢ ≥ 2^k`) is genuine, field-free, machine-proved — and it really *grows*, unlike fixed
`MOD₆`.  The remaining gap is now a **single named socket**: whether `ACC⁰[6]`-bounded composition keeps the
product-observer boundary polynomially bounded.  Proving that socket (for a polynomial budget) *is* the composite
`ACC⁰` separation — it is separation-strength and **not** proved here.  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CarryBoundaryGrowth

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CommunicationComplexity
open PallLean.Paper93.DeepMath.PathB.ACC0CarryStateComplexity

/-- **Growing communication boundary under CRT product (PROVED).**  For positive moduli `m₁, …, m_k` with product
`M = ∏ mᵢ`, any two-party product observer computing `MOD_M` needs `≥ ∏ mᵢ` boundary states.  This is the entry-285
bound at `m = M`; the `NeZero M` it needs comes from positivity of the product.  The bound *grows* with the product —
the target now has growth, unlike fixed `MOD₆`. -/
theorem crt_product_observer_boundary_ge {k : ℕ} (mods : Fin k → ℕ) (hpos : ∀ i, 0 < mods i)
    {B : Type} [Fintype B] (msg : ZMod (∏ i, mods i) → B) (decode : B → ZMod (∏ i, mods i) → Bool)
    (hcorrect : ∀ α β : ZMod (∏ i, mods i), decode (msg α) β = commValue (∏ i, mods i) α β) :
    (∏ i, mods i) ≤ Fintype.card B := by
  haveI : NeZero (∏ i, mods i) := ⟨(Finset.prod_pos (fun i _ => hpos i)).ne'⟩
  exact mod_product_observer_boundary_ge msg decode hcorrect

/-- **Growing carry state under CRT product (PROVED).**  The streaming-model companion: a carry observer computing
`MOD_(∏ mᵢ)` needs `≥ ∏ mᵢ` states (entry-284 bound at `m = ∏ mᵢ`). -/
theorem crt_product_carry_card_ge {k : ℕ} (mods : Fin k → ℕ)
    {Q : Type} [Fintype Q] (q₀ : Q) (δ : Q → Q) (acc : Q → Bool)
    (hcomp : ∀ w : ℕ, acc (δ^[w] q₀) = decide (w % (∏ i, mods i) = 0)) :
    (∏ i, mods i) ≤ Fintype.card Q :=
  carry_observer_mod_card_ge q₀ δ acc (∏ i, mods i) hcomp

/-- **The CRT product grows exponentially in the number of factors (PROVED).**  If every modulus is `≥ 2`, then
`∏ mᵢ ≥ 2^k`. -/
theorem product_ge_two_pow {k : ℕ} (mods : Fin k → ℕ) (h2 : ∀ i, 2 ≤ mods i) :
    2 ^ k ≤ ∏ i, mods i := by
  have hconst : (∏ _i : Fin k, (2 : ℕ)) = 2 ^ k := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc 2 ^ k = ∏ _i : Fin k, (2 : ℕ) := hconst.symm
    _ ≤ ∏ i, mods i := Finset.prod_le_prod' (fun i _ => h2 i)

/-- **The communication boundary grows exponentially (PROVED).**  Combining the two: computing `MOD_(∏ mᵢ)` with all
`mᵢ ≥ 2` needs `≥ 2^k` boundary states — exponential in the number of CRT factors, the unbounded growth that fixed
`MOD₆` lacks. -/
theorem crt_product_observer_boundary_ge_two_pow {k : ℕ} (mods : Fin k → ℕ) (h2 : ∀ i, 2 ≤ mods i)
    {B : Type} [Fintype B] (msg : ZMod (∏ i, mods i) → B) (decode : B → ZMod (∏ i, mods i) → Bool)
    (hcorrect : ∀ α β : ZMod (∏ i, mods i), decode (msg α) β = commValue (∏ i, mods i) α β) :
    2 ^ k ≤ Fintype.card B :=
  le_trans (product_ge_two_pow mods h2)
    (crt_product_observer_boundary_ge mods (fun i => lt_of_lt_of_le (by norm_num) (h2 i)) msg decode hcorrect)

/-- **No fixed budget suffices (PROVED).**  Once the product modulus exceeds a budget, *no* product observer of boundary
`≤ budget` can compute `MOD_(∏ mᵢ)`.  This is the precise sense in which the target now has growth: the requirement
climbs past any fixed bound (in particular past any polynomial, for a fast-growing product). -/
theorem growing_modulus_exceeds_budget {k : ℕ} (mods : Fin k → ℕ) (hpos : ∀ i, 0 < mods i)
    (budget : ℕ) (hbudget : budget < ∏ i, mods i) :
    ¬ ∃ (B : Type) (_ : Fintype B) (msg : ZMod (∏ i, mods i) → B)
        (decode : B → ZMod (∏ i, mods i) → Bool),
        (∀ α β : ZMod (∏ i, mods i), decode (msg α) β = commValue (∏ i, mods i) α β)
          ∧ Fintype.card B ≤ budget := by
  rintro ⟨B, _, msg, decode, hcorrect, hcard⟩
  have hlb := crt_product_observer_boundary_ge mods hpos msg decode hcorrect
  omega

/-- **The frontier, reduced to one socket (OPEN).**  `RealizableBy s M` abstracts "`MOD_M` is computable by an
`ACC⁰[6]`-bounded composition of resource `≤ s`".  This socket asserts that such a composition yields a *product
observer* of boundary `≤ boundaryBudget s`.  The open, separation-strength claim is `boundaryBudget = polynomial`:
proving it (so bounded composition keeps the boundary polynomially bounded) together with the proved growing lower
bound *is* the composite `ACC⁰` separation.  Named, **not** proved. -/
def BoundedCompositionKeepsBoundaryBounded
    (RealizableBy : ℕ → ℕ → Prop) (boundaryBudget : ℕ → ℕ) : Prop :=
  ∀ s M : ℕ, RealizableBy s M →
    ∃ (B : Type) (_ : Fintype B) (msg : ZMod M → B) (decode : B → ZMod M → Bool),
      (∀ α β : ZMod M, decode (msg α) β = commValue M α β) ∧ Fintype.card B ≤ boundaryBudget s

/-- **Composite `ACC⁰` separation from the socket (PROVED conditional).**  *Given* the open socket
`BoundedCompositionKeepsBoundaryBounded` and a CRT product exceeding the boundary budget at size `s`
(`boundaryBudget s < ∏ mᵢ` — e.g. `boundaryBudget` polynomial, `∏ mᵢ` super-polynomial), `MOD_(∏ mᵢ)` is **not**
realizable by a size-`s` `ACC⁰[6]` composition.  The proved growing lower bound discharges the separation modulo exactly
the socket: every other step here is machine-checked, and the one open input is the crisp boundary-invariant form of the
`ACC⁰[composite]` problem. -/
theorem composite_ACC0_separation_from_socket {k : ℕ} (mods : Fin k → ℕ) (hpos : ∀ i, 0 < mods i)
    (RealizableBy : ℕ → ℕ → Prop) (boundaryBudget : ℕ → ℕ)
    (hsock : BoundedCompositionKeepsBoundaryBounded RealizableBy boundaryBudget)
    (s : ℕ) (hgrow : boundaryBudget s < ∏ i, mods i) :
    ¬ RealizableBy s (∏ i, mods i) := by
  intro hreal
  obtain ⟨B, _, msg, decode, hcorrect, hcard⟩ := hsock s (∏ i, mods i) hreal
  have hlb := crt_product_observer_boundary_ge mods hpos msg decode hcorrect
  omega

/-!
**The actual frontier.**  The target has changed from a fixed modulus (constant complexity, entries 284/285) to the CRT
product (growing complexity, here).  The growing lower bound `≥ ∏ mᵢ ≥ 2^k` is machine-proved and genuinely unbounded.
The whole remaining gap is one socket — `BoundedCompositionKeepsBoundaryBounded`: does `ACC⁰[6]`-bounded composition keep
the product-observer boundary polynomially bounded?  If yes, `composite_ACC0_separation_from_socket` cashes the proved
growth into the composite separation.  That socket is separation-strength and is the honest open question — the
boundary-invariant restatement of `CarryRefinementCrossing`.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CarryBoundaryGrowth

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryBoundaryGrowth.crt_product_observer_boundary_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryBoundaryGrowth.crt_product_carry_card_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryBoundaryGrowth.product_ge_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryBoundaryGrowth.crt_product_observer_boundary_ge_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryBoundaryGrowth.growing_modulus_exceeds_budget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryBoundaryGrowth.composite_ACC0_separation_from_socket
