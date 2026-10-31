import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW6

/-!
# KRW brick 7: DeMorgan formula depth is not `O(log arity)`

The concrete gadgets of KRW6 give, for every constant `c`, a function on `2^k`
bits whose DeMorgan formula depth exceeds `c·k = c·log₂(arity)`.  So depth is
unbounded relative to `log₂(arity)`:

* **`sq_le_two_pow` (proved)** — `n² ≤ 2^n` for `n ≥ 4`;
* **`depth_not_log_bounded` (proved, UNCONDITIONAL)** — `∀ c, ∃ k` and a function
  `g` on `2^k` bits with `c·k < dmdepth g`.

SCOPE — read carefully.  This is the NON-UNIFORM statement: it exhibits, by
counting, functions of super-logarithmic DeMorgan formula depth (the depth
hierarchy).  It is the honest formal shadow of the `NC¹` ceiling, but it is NOT
`P ⊄ NC¹`: that requires a UNIFORM / explicit family in `P`, and the gadgets here
are non-uniform (existence via `exists_deep_pow2`).  Producing an explicit `P`
gadget is the genuine open difficulty the KRW program addresses; the composition
machinery of KRW1–6 (under `KRWConjectureDepth`) is its amplification engine.
Nothing here is `P ≠ NP`, and nothing here closes the KRW conjecture.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- `n² ≤ 2^n` for `n ≥ 4`. -/
theorem sq_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    nlinarith [ih, hn, h2]

/-- **DeMorgan formula depth is not `O(log arity)` (proved, unconditional)**: for
every `c` there is a function on `2^k` bits (so `log₂(arity) = k`) whose depth
exceeds `c·k`.  Non-uniform (counting); NOT `P ⊄ NC¹`. -/
theorem depth_not_log_bounded (c : ℕ) :
    ∃ (k : ℕ) (g : (Fin (2 ^ k) → Bool) → Bool), c * k < dmdepth g := by
  refine ⟨c + 5, ?_⟩
  obtain ⟨g, hg⟩ := exists_deep_pow2 (c + 5) (by omega)
  refine ⟨g, ?_⟩
  have he : (c + 5) - 1 = c + 4 := by omega
  rw [he] at hg
  have hsq : (c + 4) ^ 2 ≤ 2 ^ (c + 4) := sq_le_two_pow (c + 4) (by omega)
  have hkey : c * (c + 5) + 1 < 2 ^ (c + 4) := by nlinarith [hsq]
  omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.depth_not_log_bounded
