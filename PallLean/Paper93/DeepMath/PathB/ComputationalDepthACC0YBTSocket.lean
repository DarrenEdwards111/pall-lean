import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# The Yao–Beigel–Tarui exact normal-form socket

YBT: every `ACC⁰` function is **exactly** a depth-2 `SYM ∘ AND` circuit — a symmetric output gate over quasipolynomially
many bounded-fan-in `AND` gates.  This is a known classical theorem; **formalizing the reduction is the open structural
work** (the RS low-degree approximation made exact via the symmetric count, composed across constant depth).  This file
names that exact form as a socket and proves the **conditional cash-out**: once a circuit `C` is in exact `SYM ∘ AND`
form with sub-`2^n` gates, it is SAT-searchable below brute force — by the now-complete searchability lane
(`…ACC0PolyToSymAnd`, `…ACC0SymmetricObserver`).

* `HasExactSymAndForm C` — `eval C` *equals* a `SYM` (count) gate over `m` monomial-`AND`s, with `m + 1 < 2^n`.
* `ybt_socket_searchable` — the socket ⇒ SAT-searchable in `< 2^n` (proved, the cash-out).

The socket holding for **arbitrary** `ACC⁰` `C` (with `m` quasipolynomial) **is** the YBT theorem — not proved here.

## What is proved (clean axioms, no `sorry`)

* `HasExactSymAndForm` — the exact `SYM∘AND` normal-form predicate.
* `ybt_socket_searchable` — `HasExactSymAndForm C ⇒` `Satisfiable (eval C)` is decided by a `< 2^n`-cell search.

## Honest scope

This is the honest socket form of YBT: the *exact* reduction `ACC⁰ → SYM∘AND` is the structural wall (a known but
unformalized theorem; cf. `MixedACCDepthReductionSocket`), and `ybt_socket_searchable` is the conditional that, given
the form, the searchability lane delivers a sub-brute-force search.  Note the cash-out needs the **exact** form: an
*approximate* `SYM∘AND` only bounds the solution count (`…ACC0ApproxConsequence.sat_card_le_of_disagree`), not SAT.  A
small cell count is not a uniform algorithm.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd

variable {n : ℕ}

/-- **The exact Yao–Beigel–Tarui normal form (socket): `eval C` equals a `SYM` (count) gate over `m` monomial-`AND`s,
with `m + 1 < 2^n`.**  The YBT theorem asserts this holds for arbitrary `ACC⁰` `C` with `m` quasipolynomial — that
reduction is the open structural step, not proved here. -/
def HasExactSymAndForm (C : ACC0Circuit n) : Prop :=
  ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool),
    (eval C = symEval (fun j x => monoAND (mono j) x) h) ∧ m + 1 < 2 ^ n

/-- **The YBT cash-out (proved): the exact `SYM∘AND` form ⇒ SAT-searchable in `< 2^n`.**  Once `C` is in exact
`SYM∘AND` form (the socket), the symmetric count observer makes its SAT a `< 2^n`-cell search. -/
theorem ybt_socket_searchable (C : ACC0Circuit n) (hC : HasExactSymAndForm C) :
    ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool),
      (Satisfiable (eval C) ↔
          ∃ c ∈ Finset.univ.image (gateCount (fun j x => monoAND (mono j) x)), h c = true)
        ∧ (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card < 2 ^ n := by
  obtain ⟨m, mono, h, heq, hreg⟩ := hC
  refine ⟨m, mono, h, ?_⟩
  rw [heq]
  exact lowDegreePoly_searchable mono h hreg

end PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket.ybt_socket_searchable
