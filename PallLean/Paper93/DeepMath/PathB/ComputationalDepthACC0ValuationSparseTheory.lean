import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimePowerDigitObserver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CRTGatePolys

/-!
# Route 1 — valuation / `p`-adic sparse theory: the sparse top-structure of `MOD_{p^e}` and the carry barrier

The non-field observer scorecard left one open breakthrough: making a non-field (ring / valuation / digit) observer
*computationally usable* — a quasipolynomial low-degree sparse representation of `MOD_{p^e}` in the input bits.  That is
the `ACC⁰[composite]` lower bound and is not claimed here.  What this file does is **isolate exactly where the cost
lives** by exhibiting the sparse structure that genuinely exists and proving where it breaks down.

The result is a clean three-part anatomy of `MOD_{p^e}` along the `p`-adic tower:

* **Sparse top-structure (decomposition).**  `MOD_{p^e}` is an `e`-fold **AND of `MOD_p` tests on the down-shifted
  counts**: `p^e ∣ s ↔ ∀ i < e, p ∣ (s / p^i)`.  The top of the representation is sparse — `e` conjuncts — and each
  conjunct is a plain prime-modulus test.

* **Each conjunct is low-degree (the modular part is cheap).**  Every conjunct `p ∣ (s / p^i)` is decided by the
  degree-`(p-1)` Fermat gate `modPGate p = 1 − X^{p−1}` over `F_p`, evaluated at the down-shifted count `s / p^i`.  So
  the *arithmetic* in each test costs only degree `p-1` — no blow-up there.

* **The carry barrier (where the cost actually is).**  The cost is pushed entirely into the **down-shift** `s ↦ s/p^i`.
  The down-shift `s ↦ s/p` is **not additive** (`(p-1)/p + (p-1)/p ≠ (2(p-1))/p`), so it destroys the linear/additive
  structure of the count `s = ∑ xᵢ` that makes `MOD_p` cheap (the cheap `MOD_p` polynomial is degree `p-1` in the
  *linear form* `∑ Xᵢ`).  After one down-shift the argument is no longer a linear form in the input bits, so the higher
  conjuncts cannot reuse the linear-form mechanism — the irreducible difficulty is the carry/division, not the
  modular arithmetic.

## What is proved (clean axioms, no `sorry`)

* **`modPrimePower_eq_and_of_downshift_modP`** — `p^e ∣ s ↔ ∀ i < e, p ∣ (s / p^i)` (the `e`-fold AND decomposition).
* **`downshift_conjunct_decided_by_lowdegree_gate`** — each conjunct `p ∣ (s/p^i)` is decided by the degree-`(p-1)`
  gate `modPGate p` at the down-shifted count.
* **`downshift_breaks_additivity`** — `(p-1)/p + (p-1)/p ≠ (2(p-1))/p` for `p ≥ 2`: the down-shift is not additive.

## Honest scope

This locates the `ACC⁰[composite]` wall precisely *inside* the valuation route: the top structure is sparse (`e`-fold
AND) and the modular arithmetic of each conjunct is low-degree; the entire residual difficulty is expressing the
down-shifted count `s/p^i` as a low-degree object in the input bits, and the down-shift is provably non-additive, which
is why the linear-form trick that makes `MOD_p` cheap does **not** transfer.  No quasipolynomial low-degree sparse
representation in the input bits is constructed — that is the open lower bound.  What is established is a sharper
*target*: a sparse representation of the down-shift / carry, not of the modulus.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ValuationSparseTheory

open MvPolynomial

/-- **Sparse top-structure (proved): `MOD_{p^e}` is an `e`-fold AND of `MOD_p` down-shift tests.**
`p^e ∣ s ↔ ∀ i < e, p ∣ (s / p^i)` — the count `s` passes `MOD_{p^e}` iff each of the `e` down-shifted counts
`s, s/p, s/p², …, s/p^{e-1}` passes `MOD_p`.  The top of the representation is sparse (`e` conjuncts), each a plain
prime-modulus test.  (Equivalent to the digit decomposition: `p ∣ (s/p^i) ↔ digit p i s = 0`.) -/
theorem modPrimePower_eq_and_of_downshift_modP (p e s : ℕ) (hp : 0 < p) :
    p ^ e ∣ s ↔ ∀ i, i < e → p ∣ (s / p ^ i) := by
  rw [ACC0PrimePowerDigitObserver.digit_observer_decides p e s hp]
  refine forall_congr' (fun i => imp_congr_right (fun _ => ?_))
  show (s / p ^ i) % p = 0 ↔ p ∣ (s / p ^ i)
  exact Nat.dvd_iff_mod_eq_zero.symm

/-- **Each conjunct is low-degree (proved): the modular part of every down-shift test costs only degree `p-1`.**  The
conjunct `p ∣ (s/p^i)` is decided by the Fermat gate `modPGate p = 1 − X^{p−1}` (degree `≤ p-1`, `modPGate_degree`)
evaluated at the down-shifted count `s/p^i`.  So no degree blow-up comes from the arithmetic — only from forming
`s/p^i`. -/
theorem downshift_conjunct_decided_by_lowdegree_gate (p : ℕ) [Fact p.Prime] (s i : ℕ) :
    eval (fun _ => ((s / p ^ i : ℕ) : ZMod p)) (ACC0CRTGatePolys.modPGate p) = 1
      ↔ p ∣ (s / p ^ i) :=
  ACC0CRTGatePolys.modPGate_decides_dvd p (s / p ^ i)

/-- **The carry barrier (proved): the down-shift is not additive.**  `(p-1)/p + (p-1)/p ≠ (2(p-1))/p` for `p ≥ 2`
(LHS `= 0`, RHS `= 1`).  So `s ↦ s/p` does not preserve the additive structure of the count `s = ∑ xᵢ`; after one
down-shift the argument of the next `MOD_p` test is no longer a linear form in the input bits, and the linear-form
mechanism that makes `MOD_p` low-degree cannot be reused.  This is the precise location of the residual difficulty in
the valuation route: the carry/division, not the modular arithmetic. -/
theorem downshift_breaks_additivity (p : ℕ) (hp : 2 ≤ p) :
    (p - 1) / p + (p - 1) / p ≠ (2 * (p - 1)) / p := by
  have h1 : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  have h2 : (2 * (p - 1)) / p = 1 := by
    have he : 2 * (p - 1) = (p - 2) + p := by omega
    rw [he, Nat.add_div_right _ (by omega : 0 < p), Nat.div_eq_of_lt (by omega : p - 2 < p)]
  rw [h1, h2]; omega

end PallLean.Paper93.DeepMath.PathB.ACC0ValuationSparseTheory

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ValuationSparseTheory.modPrimePower_eq_and_of_downshift_modP
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ValuationSparseTheory.downshift_conjunct_decided_by_lowdegree_gate
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ValuationSparseTheory.downshift_breaks_additivity
