import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RSPerPoint

/-!
# The gate-encoding — the subset-sum test is the `OR`-gate Fermat indicator over `F_p` (proved)

Entry 213 proved the abstract per-point detection bound: a random subset detects a nonzero vector (`∑_{i∈S} x i ≠ 0`)
with probability `≥ 1/2`.  This file *encodes the gate*: that subset-sum test **is** the Razborov–Smolensky `OR`-gate
approximant `(∑_{i∈S} x i)^{p−1}` over `F_p` — the **Fermat indicator** — and that the `OR(x)=0` case is always correct
(no false positive).

The encoding.  Over `F_p` (`p` prime), Fermat's little theorem gives `y^{p−1} = 1` for `y ≠ 0` and `0^{p−1} = 0`, so
`y^{p−1}` is the indicator `[y ≠ 0]`.  Hence the `OR`-approximant `orApprox x S := (∑_{i∈S} x i)^{p−1}` outputs `1` iff
the subset sum is nonzero (`orApprox_eq_one_iff`).  On the all-zero input the sum is `0`, so the approximant outputs `0`
— matching `OR = 0` always (`orApprox_zero`, no false positive).  On a nonzero input, the entry-213 detection bound
applies verbatim to the approximant (`orApprox_detection`): a random `S` makes `orApprox x S = 1` with probability
`≥ 1/2`.

## What is proved (clean axioms, no `sorry`)

* **`fermat_ind`** — the Fermat indicator: `y^{p−1} = if y = 0 then 0 else 1` over `ZMod p` (`p` prime), from
  `ZMod.pow_card_sub_one_eq_one` and `zero_pow`.
* **`orApprox`** / **`orApprox_eq_one_iff`** — the `OR`-approximant `(∑_{i∈S} x i)^{p−1}` outputs `1` iff `∑_{i∈S} x i ≠ 0`.
* **`orApprox_zero`** — no false positive: on an input that is `0` on `S`, the approximant outputs `0` (matching
  `OR = 0`).
* **`orApprox_detection`** — the per-point gate detection: if `x j ≠ 0`, then `2^s ≤ 2 · #{S | orApprox x S = 1}` — the
  entry-213 detection bound, transported to the actual `OR`-gate Fermat-indicator approximant.

## Honest scope

This proves the **gate-encoding** completely — that the abstract subset-sum detection of entry 213 *is* the `OR`-gate
`(∑)^{p−1}` Fermat-indicator approximant over `F_p`, with the `OR=0` case always correct — in pure `ZMod p`/`Finset`
arithmetic (Fermat's little theorem `ZMod.pow_card_sub_one_eq_one`).  Combined with entries 209–213 this gives, for a
single `OR` gate, a per-input `≥3/4` random approximant (the `Uniform34` ingredient at the gate level).  What remains to
fully discharge `Uniform34` for a *circuit* is the **RS composition**: composing per-gate approximants across the
constant-depth `ACC⁰[p]` circuit (each `MOD`/`AND`/`OR` layer approximated, errors union-bounded over the gates) to get
a per-input `≥3/4` approximant for the *whole* circuit — the structural part of the probabilistic polynomial method.
This proves the single-gate encoding, not the circuit composition.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0GateEncoding

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RSPerPoint (detection_half)

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **The Fermat indicator (PROVED).**  Over `ZMod p` (`p` prime), `y^{p−1} = if y = 0 then 0 else 1`: for `y ≠ 0`,
`y^{p−1} = 1` (Fermat's little theorem, `ZMod.pow_card_sub_one_eq_one`); for `y = 0`, `0^{p−1} = 0` (`zero_pow`, as
`p − 1 ≥ 1`). -/
theorem fermat_ind (y : ZMod p) : y ^ (p - 1) = if y = 0 then 0 else 1 := by
  by_cases h : y = 0
  · rw [if_pos h, h]; exact zero_pow (by have := (Fact.out : p.Prime).one_lt; omega)
  · rw [if_neg h]; exact ZMod.pow_card_sub_one_eq_one h

/-- **The `OR`-gate approximant** of Razborov–Smolensky: for a random subset `S`, `orApprox x S := (∑_{i∈S} x i)^{p−1}`
— the Fermat indicator of the subset sum, an `F_p`-polynomial of degree `p − 1`. -/
def orApprox (x : Fin s → ZMod p) (S : Finset (Fin s)) : ZMod p := (∑ i ∈ S, x i) ^ (p - 1)

/-- **The approximant outputs `1` iff the subset sum is nonzero (PROVED).**  By `fermat_ind`: `orApprox x S = 1` exactly
when `∑_{i∈S} x i ≠ 0`. -/
theorem orApprox_eq_one_iff (x : Fin s → ZMod p) (S : Finset (Fin s)) :
    orApprox x S = 1 ↔ (∑ i ∈ S, x i) ≠ 0 := by
  unfold orApprox; rw [fermat_ind]
  constructor
  · intro hh; by_contra hsum; rw [if_pos hsum] at hh; exact zero_ne_one hh
  · intro hsum; rw [if_neg hsum]

/-- **No false positive (PROVED).**  If the input is `0` on all of `S`, the subset sum is `0`, so the approximant
outputs `0` — matching `OR = 0`.  (The `OR(x)=0` case of the gate is *always* correct, for every `S`.) -/
theorem orApprox_zero (x : Fin s → ZMod p) (S : Finset (Fin s)) (hx : ∀ i ∈ S, x i = 0) :
    orApprox x S = 0 := by
  unfold orApprox; rw [Finset.sum_eq_zero hx]
  exact zero_pow (by have := (Fact.out : p.Prime).one_lt; omega)

/-- **Per-point gate detection (PROVED).**  If some coordinate `x j ≠ 0` (so `OR(x) = 1`), then a random subset makes
the `OR`-approximant output `1` with probability `≥ 1/2`: `2^s ≤ 2 · #{S | orApprox x S = 1}`.  This transports the
entry-213 abstract detection bound (`∑_{i∈S} x i ≠ 0`) to the actual `OR`-gate Fermat-indicator approximant, via
`orApprox_eq_one_iff`. -/
theorem orApprox_detection (x : Fin s → ZMod p) (j : Fin s) (hj : x j ≠ 0) :
    2 ^ s ≤ 2 * (Finset.univ.filter (fun S : Finset (Fin s) => orApprox x S = 1)).card := by
  have heq : (Finset.univ.filter (fun S : Finset (Fin s) => orApprox x S = 1))
      = (Finset.univ.filter (fun S : Finset (Fin s) => (∑ i ∈ S, x i) ≠ 0)) :=
    Finset.filter_congr (fun S _ => by rw [orApprox_eq_one_iff])
  rw [heq]; exact detection_half x j hj

end PallLean.Paper93.DeepMath.PathB.ACC0GateEncoding

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GateEncoding.fermat_ind
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GateEncoding.orApprox_eq_one_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GateEncoding.orApprox_detection
