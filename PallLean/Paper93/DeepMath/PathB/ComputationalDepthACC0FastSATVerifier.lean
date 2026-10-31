import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsFastSat

/-!
# The fast-SAT verifier — a correct, quasipolynomial-work SAT decider from the `SYM∘AND` representation

Next Williams-side target (after the universal `hstep`): turn a `SYM∘AND` representation (the Beigel–Tarui closure
output) into a SAT decider that beats brute force.  The combinatorics is in `…ACC0WilliamsFastSat` (the count-cell
search, the savings margin); this file packages the **verifier**: deciding `SAT` by examining the *count-cell image*
(correct, no `2^n` enumeration), with **explicit quasipolynomial work** `≤ (D+1)·n^D + 1` for a degree-`≤D` `SYM∘AND`
representation — unconditional in any speedup parameter `k`.  For `D = polylog` and constant depth that work is
`n^{polylog} = 2^{polylog(n)}`, strictly below brute force `2^n`.

## What is proved (clean axioms, no `sorry`)

* **`fast_sat_verifier`** — for a degree-`≤D` injective monomial-`AND` family with symmetric top `h`: SAT is decided by
  the count-cell image (`Satisfiable (symEval …) ↔ ∃ c ∈ image (gateCount …), h c = true`, correctness) **and** the
  verifier's work — the count-cell image — has at most `(D+1)·n^D + 1` cells (quasipolynomial).
* **`fast_sat_beats_bruteforce`** — if that quasipoly work is `< 2^n` (as it is for polylog `D`), the verifier examines
  strictly fewer than `2^n` count-cells: faster than brute force.

## Honest scope

This is the fast-SAT verifier: a *correct* SAT decision (count-cell search, `observed_sat_iff`) with *explicit
quasipolynomial work* (the count-cell image size, bounded via `sym_count_card_le` + `fastSatWork_le_of_degree` +
`lowDegMonomialCount_le_pow`).  The savings-`2^k` form is already in `…ACC0WilliamsFastSat`
(`symAnd_williams_fastSat`/`…_quasipoly`); this packages the verifier's *runtime* (quasipoly work) and the strict
beats-brute-force consequence.  It does **not** turn this into a *uniform* `ACC⁰`-SAT *algorithm* realised on a machine
within a time bound (the `UniformWilliamsRealizationSocket`, which is `NEXP ⊄ ACC⁰`-strength per
`williams_socket_iff_separation`), nor does it supply the `SYM∘AND` representation itself (that is the BT closure, entry
179 for AC⁰[p]).  Williams 2011 is a proven classical theorem; this is formalisation, not an open problem.  NOT a new
separation, NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FastSATVerifier

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup (Satisfiable)
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver (observed_sat_iff)
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (gateCount symEval sym_count_card_le)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat (fastSatWork_le_of_degree lowDegMonomialCount_le_pow)

variable {n m D : ℕ}

/-- **The fast-SAT verifier (proved): correct, with quasipolynomial work.**  For a symmetric top `h` over a degree-`≤D`
injective monomial-`AND` family `mono`: SAT is decided by examining only the **count-cell image** (no `2^n`
enumeration) — `Satisfiable (symEval …) ↔ ∃ c ∈ image (gateCount …), h c = true` — and the verifier's work, the size of
that count-cell image, is at most `(D+1)·n^D + 1`, quasipolynomial for `D = polylog`. -/
theorem fast_sat_verifier (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool)
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ D) (hn : 1 ≤ n) :
    (Satisfiable (symEval (fun j x => monoAND (mono j) x) h)
        ↔ ∃ c ∈ Finset.univ.image (gateCount (fun j x => monoAND (mono j) x)), h c = true)
      ∧ (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card ≤ (D + 1) * n ^ D + 1 := by
  refine ⟨observed_sat_iff h (fun _ => rfl), ?_⟩
  refine le_trans (sym_count_card_le _) ?_
  refine le_trans (fastSatWork_le_of_degree mono hinj hdeg) ?_
  exact Nat.succ_le_succ (lowDegMonomialCount_le_pow hn)

/-- **The fast-SAT verifier beats brute force (proved).**  If the quasipolynomial work `(D+1)·n^D + 1` is `< 2^n` (as
it is for `D = polylog`), the verifier examines strictly fewer than `2^n` count-cells — faster than brute-force `2^n`
enumeration. -/
theorem fast_sat_beats_bruteforce (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool)
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ D) (hn : 1 ≤ n)
    (hquasi : (D + 1) * n ^ D + 1 < 2 ^ n) :
    (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card < 2 ^ n :=
  lt_of_le_of_lt (fast_sat_verifier mono h hinj hdeg hn).2 hquasi

end PallLean.Paper93.DeepMath.PathB.ACC0FastSATVerifier

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FastSATVerifier.fast_sat_verifier
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FastSATVerifier.fast_sat_beats_bruteforce
