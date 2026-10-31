import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW7

/-!
# KRW brick 8: the log-depth class and non-membership of the hard family

Packages KRW7 as a class-membership statement: the (non-uniform) family of hard
gadgets is not `O(log arity)`-depth, i.e. it is not in the DeMorgan-formula depth
analogue of `NC¹`.

* **`hardFamily`** — for each `k`, a fixed depth-`≥ 2^{k-1}-1` function on `2^k`
  bits (chosen from `exists_deep_pow2`); **`hardFamily_depth`**;
* **`LogDepthBounded`** — the `NC¹`-depth condition on such a family: some `c`
  with `dmdepth (F k) ≤ c·k = c·log₂(arity)` for all `k`;
* **`hardFamily_not_logDepthBounded` (proved)** — the hard family is NOT
  log-depth-bounded.

HONEST SCOPE — precise.  `LogDepthBounded` is a DEPTH-ONLY condition (no
uniformity), so non-membership is exactly the non-uniform depth hierarchy
(counting).  This theorem does NOT invoke `KRWConjectureDepth` — the non-uniform
statement does not need it; the conjecture's role is UNIFORMITY, which this does
not address.  So this is the formal `NC¹`-depth ceiling for a non-uniform family,
NOT `P ⊄ NC¹` (which needs an explicit family in `P`).  Nothing here is `P ≠ NP`,
and nothing here closes or uses the KRW conjecture.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- A fixed hard function on `2^k` bits (depth `≥ 2^{k-1}-1` for `k ≥ 4`), chosen
from `exists_deep_pow2`.  Non-uniform (a choice per `k`). -/
noncomputable def hardFamily (k : ℕ) : (Fin (2 ^ k) → Bool) → Bool :=
  if hk : 4 ≤ k then (exists_deep_pow2 k hk).choose else fun _ => false

theorem hardFamily_depth (k : ℕ) (hk : 4 ≤ k) :
    2 ^ (k - 1) - 1 ≤ dmdepth (hardFamily k) := by
  rw [hardFamily, dif_pos hk]
  exact (exists_deep_pow2 k hk).choose_spec

/-- The `NC¹`-depth condition on a family on `2^k` bits: depth `O(log₂ arity)`,
i.e. `dmdepth (F k) ≤ c·k` for some constant `c` and all `k`. -/
def LogDepthBounded (F : (k : ℕ) → (Fin (2 ^ k) → Bool) → Bool) : Prop :=
  ∃ c, ∀ k, dmdepth (F k) ≤ c * k

/-- **The hard family is not log-depth-bounded (proved, non-uniform)**: the formal
`NC¹`-depth ceiling.  Not `P ⊄ NC¹` (the family is non-uniform). -/
theorem hardFamily_not_logDepthBounded : ¬ LogDepthBounded hardFamily := by
  rintro ⟨c, hc⟩
  have hk : 4 ≤ c + 5 := by omega
  have hd := hardFamily_depth (c + 5) hk
  have he : (c + 5) - 1 = c + 4 := by omega
  rw [he] at hd
  have hle := hc (c + 5)
  have hsq : (c + 4) ^ 2 ≤ 2 ^ (c + 4) := sq_le_two_pow (c + 4) (by omega)
  have hkey : c * (c + 5) + 1 < 2 ^ (c + 4) := by nlinarith [hsq]
  omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.hardFamily_not_logDepthBounded
