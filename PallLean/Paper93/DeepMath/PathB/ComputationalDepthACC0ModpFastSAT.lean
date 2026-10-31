import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModpEndToEnd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqSuperpoly

/-!
# Hard math (BT count ⇒ fast-SAT regime) — the quasipoly SYM∘AND count drops below `2^n` (proved)

The link from the Beigel–Tarui `SYM∘AND` composition count to the Williams **fast-SAT** ingredient.  `modp_endToEnd` bounds
the `MOD_p`-circuit's `SYM∘AND` `AND`-term count by `(n+1)^{(p−1)^{d+1}}` — quasipolynomial for constant depth `d`.  Since a
fixed-degree polynomial is eventually below `2^n` (`exp_beats_poly`), the count drops below `2^n`
(`quasipoly_lt_exp`), so the cell-model SAT search examines `< 2^n` cells (`modp_fastsat_regime`) — beating brute force.  This
is exactly the regime in which the count-cell observer gives the Williams algorithmic speedup.

## What is proved (clean axioms, no `sorry`)

* **`quasipoly_lt_exp`** (PROVED) — for any constant `D`, there is an `n ≥ 1` with `(n+1)^D < 2^n`.
* **`modp_fastsat_regime`** (PROVED) — for an odd prime `p` and constant depth `d`, there is an arity `n` at which *every*
  depth-`d` `MOD_p`-circuit has `SYM∘AND` `AND`-term count `< 2^n`.

## Honest scope

This connects the proved BT count to the sub-`2^n` fast-SAT regime — the algorithmic-counting ingredient.  Turning the
sub-`2^n` cell search into the full Williams `NEXP ⊄ ACC⁰` still needs the realization/collapse sockets (the collapse socket is
P≠NP-strength, proved separation-equivalent in `ACC0NFrameWilliamsAnatomy`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModpFastSAT

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitSubstitution (Circ)
open PallLean.Paper93.DeepMath.PathB.ACC0ModpEndToEnd (substP modp_endToEnd)
open PallLean.Paper93.DeepMath.PathB.ACC0Superpoly (exp_beats_poly)

/-- **A fixed-degree polynomial is eventually below `2^n` (PROVED).**  For any `D`, some `n ≥ 1` has `(n+1)^D < 2^n`. -/
theorem quasipoly_lt_exp (D : ℕ) : ∃ n, 1 ≤ n ∧ (n + 1) ^ D < 2 ^ n := by
  obtain ⟨t, ht1, hexp⟩ := exp_beats_poly (2 ^ D) D 2 (by norm_num)
  refine ⟨t, ht1, ?_⟩
  calc (t + 1) ^ D ≤ (2 * t) ^ D := Nat.pow_le_pow_left (by omega) D
    _ = 2 ^ D * t ^ D := by rw [mul_pow]
    _ < 2 ^ t := hexp

/-- **The BT count drops below `2^n` — the fast-SAT regime (PROVED).**  For an odd prime `p` and constant depth `d`, there is
an arity `n` at which every depth-`d` `MOD_p`-circuit has `SYM∘AND` `AND`-term count `< 2^n`. -/
theorem modp_fastsat_regime (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (d : ℕ) :
    ∃ n, 1 ≤ n ∧ ∀ c : Circ n, ACC0LowDegreeSubstitution.depth c ≤ d →
      ((substP p c).support.image (fun e => e.support)).card < 2 ^ n := by
  obtain ⟨n, hn1, hlt⟩ := quasipoly_lt_exp ((p - 1) ^ (d + 1))
  refine ⟨n, hn1, fun c hc => ?_⟩
  refine lt_of_le_of_lt (modp_endToEnd p hp3 c).2.1 (lt_of_le_of_lt ?_ hlt)
  exact Nat.pow_le_pow_right (by omega)
    (Nat.pow_le_pow_right (by omega) (by omega))

/-!
**BT count ⇒ fast-SAT regime, proved.**  The quasipolynomial `SYM∘AND` count of a constant-depth `MOD_p`-circuit drops below
`2^n` — the sub-exponential cell search that is Williams' algorithmic ingredient.  Remaining (open, not faked): the
realization/collapse sockets to `NEXP ⊄ ACC⁰` (the collapse socket is P≠NP-strength).  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModpFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModpFastSAT.modp_fastsat_regime
