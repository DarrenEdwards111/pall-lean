import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFastSATSymAnd

/-!
# The Beigel–Tarui rung: general `SYM∘AND` `FastSATModel`, with explicit parameter blowup

The `SYM∘AND` rung (`…FastSATSymAnd`) used *monomial-`AND`* gates with an injective family and a degree bound.  This file
moves to the full **Beigel–Tarui normal form**: an *arbitrary* `SYM∘AND` circuit — a symmetric top over any `m`
sub-gates — bounded only by a size budget, plus the **explicit quasipolynomial parameter blowup** that makes
"`ACC⁰` ⇒ subexponential fast-SAT ⇒ `Ω(n)` savings" concrete.

  `BTCircuit n size` — a general `SYM∘AND` circuit: `m ≤ size` arbitrary Boolean sub-gates under a symmetric top `h`
        (the full BT layer, not just monomial-`AND`).
  `bt_fastSATModel` — **the instance (proved)**: `FastSATModel` for `BTCircuit`, budget `k`, when `size + 1 ≤ 2^{n−k}`.
        Correctness (`observed_sat_iff`) and the count-cell work bound hold for *any* sub-gates.
  `SymAndCircuit.toBT` — the previous rung embeds: a monomial-`AND` `SymAndCircuit` is a `BTCircuit` of size `∑_{i≤D}C(n,i)`.
  `symAnd_fastSATSpeedup_quasipoly` — **explicit parameter blowup**: the fast-SAT budget stated as the BT quasipolynomial
        `(D+1)·2^{D·⌈log n⌉} + 1 ≤ 2^{n−k}` — for `D` polylog this is `2^{o(n)}`, so `k = Ω(n)`.

## Honest scope — the ladder

`toy → SYM∘AND → ` **`BT normal form (here)`** ` → ACC⁰ → Williams fires`.

The BT rung is genuinely proved: the general `SYM∘AND` fast-SAT (correctness + count-cell work) faithfully inhabits the
interface for any bounded-size symmetric-of-sub-gates circuit, and the quasipolynomial budget is made explicit.  It is
**not** full `ACC⁰`: the remaining rung is compiling an arbitrary constant-depth `ACC⁰` circuit (composite `MOD`,
depth `> 1`) *into* this BT normal form with the size staying quasipolynomial — the classical Yao–Beigel–Tarui theorem,
the genuinely hard structural step (and the open socket the corpus tracks).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (symEval gateCount)
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver (observed_sat_iff)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup (Satisfiable)
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat
  (fastSatWork fastSatWork_le_of_degree lowDegMonomialCount_le_pow_size)

attribute [local instance] Classical.propDecidable

/-- A **Beigel–Tarui `SYM∘AND` circuit** over `n` bits with size budget `size`: a symmetric top `h` over `m ≤ size`
arbitrary Boolean sub-gates (the full BT layer — no monomial/degree restriction). -/
structure BTCircuit (n size : ℕ) where
  m : ℕ
  hm : m ≤ size
  gates : Fin m → (Fin n → Bool) → Bool
  h : ℕ → Bool

/-- The true SAT predicate of a BT circuit, as a `Bool`. -/
noncomputable def btSatOf {n size : ℕ} (C : BTCircuit n size) : Bool :=
  decide (Satisfiable (symEval C.gates C.h))

/-- **The BT instance (proved)**: an arbitrary bounded-size `SYM∘AND` circuit is a `FastSATModel`, budget `k`, whenever
the size budget fits `2^{n−k}`.  Correctness is `observed_sat_iff` (the count-cell search decides SAT exactly, for *any*
sub-gates); the work bound is `m + 1 ≤ size + 1 ≤ 2^{n−k}`. -/
noncomputable def bt_fastSATModel (n size k : ℕ) (hkn : k ≤ n) (hfit : size + 1 ≤ 2 ^ (n - k)) :
    FastSATModel n (BTCircuit n size) btSatOf where
  encode C :=
    ⟨C.m, decide (∃ c ∈ Finset.univ.image (gateCount C.gates), C.h c = true)⟩
  correct C := decide_eq_decide.mpr (observed_sat_iff C.h (fun _ => rfl)).symm
  budget := k
  budget_le := hkn
  work_le C := by exact le_trans (Nat.succ_le_succ C.hm) hfit

/-- **BT savings through the interface (proved)**: `2^k · fastSatWork m ≤ 2^n`. -/
theorem bt_nframe_fastSAT_savings (n size k : ℕ) (hkn : k ≤ n) (hfit : size + 1 ≤ 2 ^ (n - k))
    (C : BTCircuit n size) : 2 ^ k * fastSatWork C.m ≤ 2 ^ n :=
  fastSATModel_savings (bt_fastSATModel n size k hkn hfit) C

/-- **The BT `NFrameFastSATSpeedup` (proved)**: the general bounded-size `SYM∘AND` family inhabits Williams' speedup
slot. -/
theorem bt_nframe_fastSATSpeedup (n size k : ℕ) (hkn : k ≤ n) (hfit : size + 1 ≤ 2 ^ (n - k)) :
    NFrameFastSATSpeedup n (BTCircuit n size) btSatOf :=
  ⟨bt_fastSATModel n size k hkn hfit⟩

/-- **The `SYM∘AND` rung embeds into BT (proved)**: a monomial-`AND` `SymAndCircuit` of degree `≤ D` is a general
`BTCircuit` of size `∑_{i≤D} C(n,i)` (its gate count is bounded by the distinct low-degree monomials). -/
def SymAndCircuit.toBT {n D : ℕ} (C : SymAndCircuit n D) :
    BTCircuit n (∑ i ∈ Finset.range (D + 1), n.choose i) :=
  ⟨C.m, Nat.le_of_succ_le_succ (fastSatWork_le_of_degree C.mono C.hinj C.hdeg), C.gates, C.h⟩

/-- The embedding preserves the SAT predicate. -/
theorem btSatOf_toBT {n D : ℕ} (C : SymAndCircuit n D) : btSatOf C.toBT = symAndSatOf C := rfl

/-- **Explicit parameter blowup (proved)**: with the fast-SAT budget stated as the Beigel–Tarui *quasipolynomial*
`(D+1)·2^{D·⌈log n⌉} + 1 ≤ 2^{n−k}`, the `SYM∘AND` family admits a fast-SAT speedup.  For `D` polylog and constant depth,
`D·⌈log n⌉ = o(n)`, so the quasipolynomial budget is `2^{o(n)}` and the savings exponent `k = Ω(n)` — the Williams
speedup margin, super-polynomially above the `ω(log n)` the time hierarchy needs. -/
theorem symAnd_fastSATSpeedup_quasipoly (n D k : ℕ) (hn : 1 ≤ n) (hkn : k ≤ n)
    (hfit : (D + 1) * 2 ^ (D * n.size) + 1 ≤ 2 ^ (n - k)) :
    NFrameFastSATSpeedup n (SymAndCircuit n D) symAndSatOf :=
  symAnd_nframe_fastSATSpeedup n D k hkn
    (le_trans (Nat.succ_le_succ (lowDegMonomialCount_le_pow_size hn)) hfit)

end PallLean.Paper93.DeepMath.PathB.NFrameFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.bt_fastSATModel
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.btSatOf_toBT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFastSAT.symAnd_fastSATSpeedup_quasipoly
