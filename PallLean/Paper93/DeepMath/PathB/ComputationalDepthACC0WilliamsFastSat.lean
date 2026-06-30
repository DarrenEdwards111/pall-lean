import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSpeedupMargin

/-!
# The Williams `fastSat` ingredient, made concrete and quantitative

In `…ObserverWilliams` / `…WilliamsCashout` the `fastSat` step — "a structured circuit ⇒ a faster‑than‑brute‑force
SAT algorithm" — is an abstract `Prop`.  This file *grounds* it: the `SYM∘AND` normal form (the Yao–Beigel–Tarui
target the corpus already builds, `…ACC0PolyToSymAnd` / `…ACC0SymmetricObserver`) gives a SAT decision procedure that
examines only the **count‑cell image** (`≤ m+1` cells for `m` gates), and the quantitative savings over brute force
`2^n` is computed exactly via the `…SpeedupMargin` arithmetic.

The algorithmic core of Williams' method (in the cell/decision model):

```
ACC⁰ circuit  ──[YBT, socket]──►  SYM∘AND of m gates  ──[PROVED here]──►  SAT decided in ≤ m+1 cells
                                                                              │
                          m ≤ ∑_{i≤D} C(n,i) ≤ (D+1)·n^D  (degree-≤D, PROVED here)
                                                                              ▼
                          D = polylog (const depth)  ⇒  m+1 = 2^{polylog(n)} ≪ 2^n
                                                                              ▼
                          work ≤ 2^{n−k}  ⇒  savings ≥ 2^k  with  k = n − polylog = Ω(n)
```

## What is proved (clean axioms, no `sorry`)

* `fastSatWork` — the cell count `m + 1` of the `SYM∘AND` fast‑SAT.
* `fastSat_savings_of_work_le` — **the savings**: `work ≤ 2^{n−k}` ⇒ `2^k · work ≤ 2^n` (savings `≥ 2^k`).
* `fastSatWork_le_of_degree` — a degree‑`≤D` injective monomial‑`AND` family has work `≤ (∑_{i≤D} C(n,i)) + 1`.
* `lowDegMonomialCount_le_pow` — the gate count is quasipolynomial: `∑_{i≤D} C(n,i) ≤ (D+1)·n^D`.
* `lowDegMonomialCount_le_pow_size` — the **bit-width form**: `∑_{i≤D} C(n,i) ≤ (D+1)·2^{D·size n}`, making
  "`D` polylog ⇒ subexponential" explicit (`D·size n = polylog(n)·O(log n) = o(n)`).
* **`symAnd_williams_fastSat`** — the headline: a `SYM∘AND` (degree `≤D`, injective) decides SAT by the count‑cell
  search, the cell count fits the budget `2^{n−k}`, **and** that work delivers Williams savings `≥ 2^k`.
* **`symAnd_williams_fastSat_quasipoly`** — the explicit quasipolynomial regime: with `(D+1)·n^D + 1 ≤ 2^{n−k}`,
  the savings is `≥ 2^k` (for `D` polylog, `k = Ω(n)` — the Williams speedup margin).

## Honest scope — what this is and is *not*

This makes the `fastSat`/`savings` ingredient *concrete*: the speedup is a real, counted procedure with an exact
margin, not an assumed `Prop`.  It does **not** prove `NEXP ⊄ ACC⁰`.  Two genuinely open links remain, exactly as
the cash‑out files document and **do not fake**:

1. **The YBT *exact* normal form for arbitrary `ACC⁰`** (depth `> 1`, composite `MOD`) — the open structural socket
   `MixedACCDepthReductionSocket` (`…ACC0YBTSocket`); the polynomial method gives only the *approximate* form
   (`…ACC0ApproxConsequence`) and stops at prime‑power `MOD` (`…ACC0ModPExact`, the composite‑`MOD` barrier).
2. **Uniform realization** — the cell/decision model here is not a Turing‑machine time bound; `UniformWilliams
   RealizationSocket` (`…ACC0WilliamsCashout`) is the open TM‑encoding step, and `williams_socket_iff_separation`
   there proves each cash‑out socket is itself `NEXP ⊄ ACC⁰`‑strength.

So this file supplies the *combinatorial* `fastSat` with its quantitative margin; the separation‑strength content
stays in the named sockets.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.SpeedupMargin

variable {n m D : ℕ}

/-- The work of the `SYM∘AND` fast‑SAT: the number of count‑cells it examines, `m + 1`. -/
def fastSatWork (m : ℕ) : ℕ := m + 1

/-- **The savings (proved).**  If the fast‑SAT work fits in `2^{n−k}`, it beats brute force `2^n` by a factor
`≥ 2^k`: `2^k · work ≤ 2^n`. -/
theorem fastSat_savings_of_work_le {k : ℕ} (hkn : k ≤ n) (hw : fastSatWork m ≤ 2 ^ (n - k)) :
    2 ^ k * fastSatWork m ≤ 2 ^ n :=
  savings_ge_of_work_le hkn hw

/-- **The gate count bounds the work (proved).**  A degree‑`≤D` injective monomial‑`AND` family has fast‑SAT work
`≤ (∑_{i≤D} C(n,i)) + 1`. -/
theorem fastSatWork_le_of_degree (mono : Fin m → Finset (Fin n)) (hinj : Function.Injective mono)
    (hdeg : ∀ j, (mono j).card ≤ D) :
    fastSatWork m ≤ (∑ i ∈ Finset.range (D + 1), n.choose i) + 1 :=
  Nat.succ_le_succ (monomial_count_le mono hinj hdeg)

/-- **The gate count is quasipolynomial (proved): `∑_{i≤D} C(n,i) ≤ (D+1)·n^D`.**  For `D` polylog and constant
depth this is `n^{polylog} = 2^{polylog(n)}` — the quasipolynomial `SYM∘AND` size of the YBT normal form. -/
theorem lowDegMonomialCount_le_pow (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range (D + 1), n.choose i ≤ (D + 1) * n ^ D := by
  calc ∑ i ∈ Finset.range (D + 1), n.choose i
      ≤ ∑ _i ∈ Finset.range (D + 1), n ^ D := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range, Nat.lt_succ_iff] at hi
        exact le_trans (Nat.choose_le_pow n i) (Nat.pow_le_pow_right hn hi)
    _ = (D + 1) * n ^ D := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **The gate count in bit-width form (proved): `∑_{i≤D} C(n,i) ≤ (D+1)·2^{D·size n}`.**  Since `n < 2^{size n}`
(`size n = bitlen n`), `n^D ≤ 2^{D·size n}`, so the quasipolynomial gate count is `≤ (D+1)·2^{D·size n}`.  This is
the explicit form behind "`D` polylog and constant depth ⇒ subexponential": `D·size n = polylog(n)·O(log n) = o(n)`,
so the count is `2^{o(n)} ≪ 2^n` — the savings exponent `k = n − D·size n − O(log D) = Ω(n)`. -/
theorem lowDegMonomialCount_le_pow_size (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range (D + 1), n.choose i ≤ (D + 1) * 2 ^ (D * n.size) := by
  refine le_trans (lowDegMonomialCount_le_pow hn) ?_
  have hns : n ≤ 2 ^ n.size := le_of_lt (Nat.size_le.mp (le_refl n.size))
  have hpow : n ^ D ≤ 2 ^ (D * n.size) := by
    calc n ^ D ≤ (2 ^ n.size) ^ D := Nat.pow_le_pow_left hns D
      _ = 2 ^ (D * n.size) := by rw [← pow_mul, Nat.mul_comm]
  exact Nat.mul_le_mul (le_refl (D + 1)) hpow

/-- **The `SYM∘AND` Williams fast‑SAT (proved).**  A symmetric top `h` over a degree‑`≤D` injective monomial‑`AND`
family `mono`:
* decides SAT by examining only the **count‑cell image** (no `2^n` enumeration);
* that image fits in the work budget `2^{n−k}` once the gate count does; and
* the work delivers Williams savings `≥ 2^k` over brute force `2^n`. -/
theorem symAnd_williams_fastSat (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool)
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ D)
    {k : ℕ} (hkn : k ≤ n)
    (hfit : (∑ i ∈ Finset.range (D + 1), n.choose i) + 1 ≤ 2 ^ (n - k)) :
    (Satisfiable (symEval (fun j x => monoAND (mono j) x) h)
        ↔ ∃ c ∈ Finset.univ.image (gateCount (fun j x => monoAND (mono j) x)), h c = true)
    ∧ (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card ≤ 2 ^ (n - k)
    ∧ 2 ^ k * (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card ≤ 2 ^ n := by
  -- the count-cell image bounds: card ≤ m+1 ≤ (∑ C(n,i)) + 1 ≤ 2^{n-k}
  have hcell : (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card ≤ 2 ^ (n - k) :=
    le_trans (sym_count_card_le _)
      (le_trans (fastSatWork_le_of_degree mono hinj hdeg) hfit)
  refine ⟨observed_sat_iff h (fun _ => rfl), hcell, ?_⟩
  -- savings: 2^k · (cell count) ≤ 2^k · 2^{n-k} = 2^n
  exact savings_ge_of_work_le hkn hcell

/-- **The explicit quasipolynomial regime (proved).**  Combining the quasipolynomial gate bound with the savings:
if `(D+1)·n^D + 1 ≤ 2^{n−k}` then the `SYM∘AND` fast‑SAT cell count fits the budget and delivers savings `≥ 2^k`.
For constant depth and `D = polylog`, `(D+1)·n^D = 2^{polylog(n)}`, so `k = n − polylog = Ω(n)` — the Williams
speedup margin, super‑polynomially above the `ω(log n)` the time hierarchy needs. -/
theorem symAnd_williams_fastSat_quasipoly (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool)
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ D)
    (hn : 1 ≤ n) {k : ℕ} (hkn : k ≤ n) (hfit : (D + 1) * n ^ D + 1 ≤ 2 ^ (n - k)) :
    (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card ≤ 2 ^ (n - k)
    ∧ 2 ^ k * (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card ≤ 2 ^ n := by
  have hfit' : (∑ i ∈ Finset.range (D + 1), n.choose i) + 1 ≤ 2 ^ (n - k) :=
    le_trans (Nat.succ_le_succ (lowDegMonomialCount_le_pow hn)) hfit
  obtain ⟨_, hcell, hsav⟩ := symAnd_williams_fastSat mono h hinj hdeg hkn hfit'
  exact ⟨hcell, hsav⟩

end PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat.symAnd_williams_fastSat
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat.symAnd_williams_fastSat_quasipoly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat.lowDegMonomialCount_le_pow_size
