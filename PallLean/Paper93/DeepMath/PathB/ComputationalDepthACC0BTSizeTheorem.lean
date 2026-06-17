import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ApproxBTInstantiation

/-!
# The Beigel–Tarui size theorem over a concrete datatype — the prime-`p` route, proved

Entry 175's partial discharge reduced `DynamicClosesAtBT` to one residual socket `hSize`: the BT *size analysis* keeping
the combined `SYM∘AND` quasipolynomial-size for an arbitrary `ACC⁰` circuit.  This file discharges the **size content of
`hSize` for the main case** — the AC⁰[p] / prime-modulus route, over the concrete `BoolCircuitSyntax` datatype.

The `SYM∘AND` **size** of a polynomial representation is the number of distinct `AND`-features it uses — i.e. the number
of distinct monomial-supports.  For the Razborov–Smolensky approximant `toApprox p t R C` (`…Layer3`,
`∨`/`∧` via `genOrApprox`, `MOD_p` via the Fermat indicator), entry 173 proved this count is `≤ (n+1)^{((p−1)·t)^{depth}}`
and `≤ (n+1)^{L^D}` for `(p−1)·t ≤ L`, `depth ≤ D`.  Here that bound is packaged as the **BT size theorem**: for polylog
`L` (the RS error parameter) and *constant* depth `D`, the `SYM∘AND` size is `n^{polylog}` — quasipolynomial.

## What is proved (clean axioms, no `sorry`)

* **`btSymAndSize`** — the `SYM∘AND` size of a polynomial representation (number of distinct `AND`-features).
* **`QuasipolyBTSize` / `quasipolyBTSize_proved`** — the BT size theorem: the RS approximant of any `BoolCircuitSyntax`
  circuit has `SYM∘AND` size `≤ (n+1)^{L^D}` (`(p−1)·t ≤ L`, `depth ≤ D`) — quasipolynomial for polylog `L`, constant `D`.

## Honest scope

This proves the **size half** of `hSize` over a concrete datatype, for the prime-`p` (AC⁰[p]) route: the `SYM∘AND` size
of the RS approximant is genuinely quasipolynomial, fully from the proved entry-173 count.  It does **not** discharge
`hSize` in full — two residuals remain, both genuine BT content (proven classically, large to formalise):

1. **Correctness / error** — that the `SYM∘AND` of size `btSymAndSize` actually *computes* (or `1/poly`-approximates) the
   circuit; this is the RS *agreement* content (`…Layer3` correlation lemmas, `circuit_error_bound`,
   `parity_function_lower_bound`), separate from the size.
2. **Composite / prime-power modulus** — the prime-`p` approximant computes only `MOD_p` correctly; squarefree composite
   runs per prime over `∏ F_p` (entry 171), and prime-power `MOD` uses the exact mixed-radix `SYM∘AND` (entry 174) whose
   *quasipoly* size is the genuine BT mixed-radix size analysis, not covered by the degree-governed prime-`p` count.

So the size theorem is proved for the AC⁰[p] route; the full quasipoly size for arbitrary `ACC⁰` (all moduli, with
correctness) is the remaining BT formalisation.  Beigel–Tarui and `NEXP ⊄ ACC⁰` (Williams 2011) are proven classical
theorems ⇒ formalisation, not an open problem.  NOT a new separation, NOT `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BTSizeTheorem

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3 (toApprox)

variable {n : ℕ}

/-- The **`SYM∘AND` size** of a polynomial representation: the number of distinct `AND`-features (monomial supports) —
the bottom-layer gate count of the `SYM∘AND` form, with the symmetric top reading off the cube sum. -/
def btSymAndSize (p : ℕ) (P : MvPolynomial (Fin n) (ZMod p)) : ℕ :=
  (P.support.image (fun d => d.support)).card

/-- **The BT size theorem (prime-`p` route): the RS approximant's `SYM∘AND` size is quasipolynomial.**  For any
`BoolCircuitSyntax` circuit `C` with `(p−1)·t ≤ L` and `depth ≤ D`, the approximant `toApprox p t R C` has `SYM∘AND`
size `≤ (n+1)^{L^D}` — for polylog `L` (the RS error parameter) and *constant* depth `D`, `n^{polylog}`, quasipolynomial. -/
def QuasipolyBTSize : Prop :=
  ∀ {n : ℕ} (p t : ℕ), p.Prime → 1 ≤ t → ∀ (R : (k : ℕ) → Fin t → Fin k → ZMod p)
    (C : BoolCircuitSyntax n) (L D : ℕ), 1 ≤ L → (p - 1) * t ≤ L → C.depth ≤ D →
    btSymAndSize p (toApprox p t R C) ≤ (n + 1) ^ (L ^ D)

/-- **The BT size theorem is proved (over the concrete `BoolCircuitSyntax` datatype, prime-`p` route).**  Directly from
the entry-173 quasipoly count bound `approx_endToEnd_BT`: the `SYM∘AND` size of the RS approximant is `≤ (n+1)^{L^D}`. -/
theorem quasipolyBTSize_proved : QuasipolyBTSize := by
  intro n p t hp ht R C L D hL hK hd
  haveI : Fact p.Prime := ⟨hp⟩
  exact (ACC0ApproxBTInstantiation.approx_endToEnd_BT p t ht R C L D hL hK hd).2

end PallLean.Paper93.DeepMath.PathB.ACC0BTSizeTheorem

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BTSizeTheorem.quasipolyBTSize_proved
