import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneRank

/-!
# Kleene interpreter project — rank decode (PROVED)

The measure-monotone rank `cfgRank E B k ec n = (k·(E+1)+ec)·(B+1)+n` is **invertible** by div/mod (within
the value bounds `ec < E+1`, `n < B+1`): the per-cell body recovers `(k, ec, n)` from the rank.

  `cfgRank_decode` —
    `cfgRank E B k ec n % (B+1) = n`,
    `cfgRank E B k ec n / (B+1) % (E+1) = ec`,
    `cfgRank E B k ec n / (B+1) / (E+1) = k`.

This is the Lean-level correctness of the decode; the per-cell body realizes it with `divmodCode` (applied
to `B+1` then `E+1`).

## What is proved (clean axioms, no `sorry`)

* `cfgRank_decode` — the rank is invertible by div/mod.

## Honest scope

The decode correctness.  The per-cell body (using `divmodCode` + `mkDispatch` + `lookupCode`), the
correctness chain, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneRank

/-- **The rank is invertible by div/mod (proved).** -/
theorem cfgRank_decode (E B k ec n : ℕ) (hec : ec < E + 1) (hn : n < B + 1) :
    cfgRank E B k ec n % (B + 1) = n ∧
    cfgRank E B k ec n / (B + 1) % (E + 1) = ec ∧
    cfgRank E B k ec n / (B + 1) / (E + 1) = k := by
  unfold cfgRank
  have hB : 0 < B + 1 := Nat.succ_pos B
  have hE : 0 < E + 1 := Nat.succ_pos E
  have hmod : ((k * (E + 1) + ec) * (B + 1) + n) % (B + 1) = n := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hn]
  have hdiv : ((k * (E + 1) + ec) * (B + 1) + n) / (B + 1) = k * (E + 1) + ec := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hn, Nat.zero_add]
  refine ⟨hmod, ?_, ?_⟩
  · rw [hdiv, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hec]
  · rw [hdiv, Nat.add_comm, Nat.add_mul_div_right _ _ hE, Nat.div_eq_of_lt hec, Nat.zero_add]

/-!
**Rank decode proved.**  `cfgRank` inverts by div/mod within the value bounds — the per-cell body recovers
`(k, ec, n)` from the rank (realized with `divmodCode`).  The per-cell body, the correctness chain, the
interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneRank

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneRank.cfgRank_decode
