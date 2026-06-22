import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Agreement
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky

/-!
# Prime-modulus exact existence via the union bound — and the exact-vs-quasipoly cost (PROVED)

The prime side, taken to **exact**.  `composed_error_le` gives, for a single modulus `p`, an oracle `ω`
with `#errors · p^t ≤ #subcircuits · 2^n`.  When the form-space dominates — `p^t > #subcircuits · 2^n`
— the error count is forced to **zero**: the RS approximant `toAgree` is **exactly** the circuit on the
whole Boolean cube.

  `exists_exact_toAgree` — for prime `p`, if `#subcircuits(C) · 2^n < p^t`, there is an oracle `ω` with
  `toAgree p t (oracleOf … ω) C` agreeing with `C` at **every** input (zero error, exact).

This completes the prime approx→exact route to an **exact** representation — but it exposes the
exact-vs-quasipoly cost concretely.  Exactness needs `p^t > 2^n`, i.e. `t ≳ n / log p`, so the degree
`((p−1)·t)^{depth} ≳ n^{depth}` is **large** — hence the support `(n+1)^{degree}` is **not**
quasipolynomial.  This is the same wall, now proved on the prime side: *exact ⇒ large `t` ⇒ high degree*;
*quasipoly ⇒ small `t` ⇒ only approximate* (`ACC0RSDepthComposition`).  You cannot have both from this
encoding — the genuine Beigel–Tarui difficulty.

## What is proved (clean axioms, no `sorry`)

* `exists_exact_toAgree` — prime-modulus exact RS representation on the cube, when `p^t > #subcircuits·2^n`.

## Honest scope

Exact for prime `p` via the union bound, at the cost of `t ≳ n/log p` (high degree, non-quasipoly).  The
quasipoly-*and*-exact representation (the Beigel–Tarui integer construction) is **not** here, and the
composite-modulus amplification remains the Razborov–Smolensky barrier.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimeExactExists

open scoped Classical
open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3

variable {n : ℕ}

/-- **Prime-modulus exact existence (proved).**  For a single-modulus-`p` circuit `C`, if the form space
dominates the error budget (`#subcircuits(C) · 2^n < p^t`), then there is an oracle `ω` whose RS
approximant agrees with `C` at **every** Boolean input — an *exact* representation. -/
theorem exists_exact_toAgree (p t : ℕ) [Fact p.Prime]
    (C : BoolCircuitSyntax n)
    (hmod : ∀ q r cs, (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax n) ∈ subcircuits C →
      q = p)
    (hlarge : (subcircuits C).toFinset.card * Fintype.card (Fin n → Bool) < p ^ t) :
    ∃ ω : FormSpace p t C, ∀ x : Fin n → Bool,
      eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
        = boolToZMod p (C.eval x) := by
  obtain ⟨ω, herr⟩ := composed_error_le p t C hmod
  refine ⟨ω, ?_⟩
  set bad := Finset.univ.filter (fun x : Fin n → Bool =>
      eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
        ≠ boolToZMod p (C.eval x)) with hbad
  have hzero : bad.card = 0 := by
    by_contra h
    have h1 : 0 < bad.card := Nat.pos_of_ne_zero h
    have hmul : p ^ t ≤ bad.card * p ^ t := Nat.le_mul_of_pos_left (p ^ t) h1
    omega
  intro x
  by_contra hx
  have hxmem : x ∈ bad := by rw [hbad]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
  rw [Finset.card_eq_zero] at hzero
  rw [hzero] at hxmem
  simp at hxmem

/-!
**Prime exact existence proved.**  When `p^t > #subcircuits·2^n`, the RS approximant is exact on the
cube — but this forces `t ≳ n/log p`, hence degree `≳ n^{depth}` and non-quasipoly support.  Exact ⇒
high degree; quasipoly ⇒ approximate — the exact-vs-quasipoly wall, on the prime side.  The composite
barrier and the quasipoly-and-exact Beigel–Tarui construction are untouched.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PrimeExactExists

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeExactExists.exists_exact_toAgree
