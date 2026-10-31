import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompositeModCharSum
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompositeModSym

/-!
# Composite `MOD_m`: the character-sum arithmetisation as a polynomial in the input bits

Rung 4 (`…CharSum`) represented the `MOD_m` indicator as a normalised character sum `m⁻¹ ∑_{j<m} ζ^{j·k}` over a field
with a primitive `m`-th root of unity — valid for composite `m`.  That is a function of the *count* `k`.  This file makes
it a genuine **polynomial in the input bits**, the object the Beigel–Tarui degree analysis operates on: since a bit
`xᵢ ∈ {0,1}` gives `ζ^{xᵢ} = 1 + (ζ-1)·xᵢ`, the power `ζ^k = ζ^{∑ xᵢ}` factors as a **multilinear** polynomial
`∏ᵢ (1 + (ζ-1)·xᵢ)`.

  `powBool` / `powBool_eq` — **PROVED**: `ζ^{[xᵢ]}` (the bit's contribution) is the affine `1 + (ζ-1)·[xᵢ]`.
  `pow_boolCount` — **PROVED**: `ζ^{count} = ∏ᵢ (1 + (ζ-1)·[xᵢ])` — the count-power as a multilinear polynomial in the bits.
  `modZero_charsum_poly` — **PROVED, the arithmetisation**: `m⁻¹ ∑_{j<m} ∏ᵢ (1 + (ζʲ-1)·[xᵢ]) = [m ∣ count]` — a single
        `MOD_m` gate written as a sum of `m` multilinear polynomials over the field, **valid for composite `m`**.

## Honest scope — the arithmetisation, and its degree

This closes the loop from "character sum in the count" to "polynomial in the bits": a `MOD_m` gate is `m⁻¹ ∑_{j<m} Pⱼ(x)`
with each `Pⱼ` the multilinear polynomial `∏ᵢ (1 + (ζʲ-1)·xᵢ)` over a field with roots of unity — the Toda / Beigel–Tarui
representation of one gate, uniform in prime vs. composite `m`.  Its degree is `n` (each `Pⱼ` is a full product over all
inputs).  The `NEXP`-strength content Williams' method needs is *not* this single-gate representation but the
**degree reduction**: composing such representations through a depth-`d` `ACC⁰[m]` circuit while keeping the total degree
**quasipolynomial** (via low-degree approximation of the products), so the final `SYM⁺`-circuit has quasipolynomially many
monomials.  That circuit-level degree-reduction is the deep open piece, **not** established here.  This file supplies the
single-gate arithmetisation and states its degree honestly.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CompositeMod

open Finset

variable {K : Type*} [Field K] {n : ℕ}

/-- The contribution of a single bit to `ζ^{count}`: `ζ` if the bit is set, `1` otherwise. -/
def powBool (ζ : K) (b : Bool) : K := if b then ζ else 1

/-- **A bit's power is affine (proved)**: `powBool ζ b = 1 + (ζ-1)·[b]`. -/
theorem powBool_eq (ζ : K) (b : Bool) :
    powBool ζ b = 1 + (ζ - 1) * (if b then 1 else 0) := by
  cases b <;> simp [powBool]

/-- **The count-power as a multilinear polynomial (proved)**: `ζ^{count} = ∏ᵢ (1 + (ζ-1)·[xᵢ])`. -/
theorem pow_boolCount (ζ : K) (x : Fin n → Bool) :
    ζ ^ (boolCount x) = ∏ i, (1 + (ζ - 1) * (if x i then 1 else 0)) := by
  rw [boolCount, Finset.card_filter, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← powBool_eq]
  cases x i <;> simp [powBool]

/-- **The single-gate arithmetisation (proved)**: a `MOD_m` gate is `m⁻¹ ∑_{j<m} ∏ᵢ (1 + (ζʲ-1)·[xᵢ])` — a sum of `m`
multilinear polynomials over a field with a primitive `m`-th root `ζ`, equal to the zero-indicator `[m ∣ count]`.  Valid
for composite `m`. -/
theorem modZero_charsum_poly {m : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ m) (hm : (m : K) ≠ 0)
    (x : Fin n → Bool) :
    (m : K)⁻¹ * ∑ j ∈ Finset.range m, ∏ i, (1 + (ζ ^ j - 1) * (if x i then 1 else 0))
      = if m ∣ boolCount x then 1 else 0 := by
  rw [← charSum_indicator hζ hm (boolCount x)]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_mul]
  exact (pow_boolCount (ζ ^ j) x).symm

end PallLean.Paper93.DeepMath.PathB.CompositeMod

#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.pow_boolCount
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.modZero_charsum_poly
