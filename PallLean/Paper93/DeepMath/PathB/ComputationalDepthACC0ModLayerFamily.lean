import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModLayerFastSAT

/-!
# Bridge — the `MOD`-layer fast-SAT beats brute force unconditionally at large arity (proved)

Strengthening the algorithmic payoff: `modLayer_beats_bruteforce` needed the hypothesis `(s+1)^t < 2^n`.  For a *family* of
`MOD`-layer circuits with **constant** parameters `s` (support size) and `t` (fan-in), `(s+1)^t` is a constant, and a constant
is eventually below `2^n` (`const_lt_two_pow`).  Hence the weight-cell search beats the `2^n` brute force at *every*
sufficiently large arity (`modLayer_family_beats_bruteforce`) — no side hypothesis.

So for any fixed `s, t`, the symmetric cell-count fast-SAT is unconditionally sub-`2^n` once `n ≥ (s+1)^t`: the Williams
speedup holds for the whole constant-parameter `MOD`-layer family.

## What is proved (clean axioms, no `sorry`)

* **`const_lt_two_pow`** (PROVED) — `c ≤ n → c < 2^n` (a constant is eventually below `2^n`).
* **`modLayer_family_beats_bruteforce`** (PROVED) — for `n ≥ (s+1)^t`, the `MOD`-layer cell search has `< 2^n` cells.

## Honest scope

This removes the side hypothesis from the brute-force-beating statement for the constant-parameter family; it is still the
fast-SAT *ingredient*, not the unconditional `NEXP ⊄ ACC⁰` (P≠NP-strength, the collapse socket).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModLayerFamily

open Finset
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn)
open PallLean.Paper93.DeepMath.PathB.ACC0ModLayerFastSAT (modLayer_fastsat)

/-- **A constant is eventually below `2^n` (PROVED).** -/
theorem const_lt_two_pow (c n : ℕ) (hn : c ≤ n) : c < 2 ^ n :=
  calc c < 2 ^ c := Nat.lt_two_pow_self
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

/-- **The `MOD`-layer fast-SAT beats brute force unconditionally at large arity (PROVED).**  For constant `s, t` and any
`n ≥ (s+1)^t`, the weight-cell search examines `< 2^n` cells. -/
theorem modLayer_family_beats_bruteforce {n t s : ℕ} (hn : (s + 1) ^ t ≤ n)
    (S : Fin t → Finset (Fin n)) (hs : ∀ i, (S i).card ≤ s)
    (H : (Fin t → ℕ) → Bool) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, F x = H (fun i => weightOn (S i) x)) :
    (Finset.univ.image (fun x (i : Fin t) => weightOn (S i) x)).card < 2 ^ n :=
  lt_of_le_of_lt (modLayer_fastsat S hs H F hF).2 (const_lt_two_pow _ n hn)

/-!
**`MOD`-layer fast-SAT, unconditional at large arity, proved.**  For fixed `s, t` the weight-cell search is `< 2^n` once
`n ≥ (s+1)^t` — the brute-force-beating speedup holds for the whole constant-parameter family, with no side hypothesis.
Remaining (open, not faked): the collapse socket to `NEXP ⊄ ACC⁰` (P≠NP-strength).  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModLayerFamily

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModLayerFamily.modLayer_family_beats_bruteforce
