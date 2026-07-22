import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW16

/-!
# KRW brick 17: the tight deterministic partition bound

KRW14 gave `D(U_N) ≥ N/2` (loose — a half-maximal hard function).  The proper
DETERMINISTIC bound is near-maximal: `D(U_N) ≥ N − log₂ N − O(1)`.  This reflects
that the universal relation's PARTITION number is `≈ 2^N` (deterministic CC),
whereas its COVER number — what fooling/nondeterminism see (KRW16) — is only
`O(log N)`.  The gap `2^N` vs `poly(N)` is exactly the partition-vs-cover
phenomenon; certifying it needs the deterministic partition characterisation
(Karchmer–Wigderson: deterministic CC = formula depth), via a near-maximally-hard
function.

* **`hard_pow2_hnum_tight` (proved)** — the counting condition at the tight
  parameter `s = 2^k − k − 4` (so `dmsize ≈ 2^{2^k}/2^k`, near the maximum);
* **`exists_deep_pow2_tight` (proved)** — a function on `2^k` bits of depth
  `≥ 2^k − k − 4` (near-maximal, `≈ N − log N`);
* **`uprotocol_lower_bound_tight` / `ucc_pow2_tight` (proved)** —
  `ucc (2^k) ≥ 2^k − k − 5`, i.e. `D(U_N) ≥ N − log₂ N − 5` for `N = 2^k`.

With KRW15's `ucc (2^k) ≤ 2·2^k`, the deterministic CC of `U_N` is pinned to
`N − log N ≤ D(U_N) ≤ 2N` — tight up to the `log N` and constants.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- **The counting condition at the tight parameter (proved)**: `a = 2^k`,
`B = 2^{2^k − k − 4}` (near the maximum `2^{2^k}/2^k`). -/
theorem hard_pow2_hnum_tight (k : ℕ) (hk : 5 ≤ k) :
    (2 * 2 ^ (2 ^ k - k - 4) + 1) * (2 * 2 ^ k + 4) ^ (2 * 2 ^ (2 ^ k - k - 4))
      < 2 ^ (2 ^ (2 ^ k)) := by
  have hkk : k + 4 ≤ 2 ^ k := add4_le_two_pow k (by omega)
  have h24 : 2 * 2 ^ k + 4 ≤ 2 ^ (k + 2) := by
    have e1 : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
    have e2 : (2 : ℕ) ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by rw [pow_succ]; ring
    have h4 : (4 : ℕ) ≤ 2 ^ (k + 1) :=
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set E : ℕ := 2 * 2 ^ (2 ^ k - k - 4) with hEdef
  have hE : E = 2 ^ (2 ^ k - k - 3) := by
    rw [hEdef]
    conv_rhs => rw [show 2 ^ k - k - 3 = (2 ^ k - k - 4) + 1 from by omega]
    rw [pow_succ]; ring
  have hp1 : (2 * 2 ^ k + 4) ^ E ≤ (2 ^ (k + 2)) ^ E := Nat.pow_le_pow_left h24 _
  have hp2 : (2 ^ (k + 2)) ^ E = 2 ^ ((k + 2) * E) := by rw [← pow_mul]
  have hp3 : E + 1 ≤ 2 ^ E := by have := Nat.lt_two_pow_self (n := E); omega
  have hExp : (k + 3) * E < 2 ^ (2 ^ k) := by
    rw [hE]
    have hsplit : (2 : ℕ) ^ (2 ^ k) = 2 ^ (2 ^ k - k - 3) * 2 ^ (k + 3) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    have hpos : 0 < 2 ^ (2 ^ k - k - 3) := pow_pos (by norm_num) _
    have hk3 : k + 3 < 2 ^ (k + 3) := Nat.lt_two_pow_self
    nlinarith [hk3, hpos]
  calc (E + 1) * (2 * 2 ^ k + 4) ^ E
      ≤ 2 ^ E * (2 ^ (k + 2)) ^ E := Nat.mul_le_mul hp3 hp1
    _ = 2 ^ E * 2 ^ ((k + 2) * E) := by rw [hp2]
    _ = 2 ^ (E + (k + 2) * E) := by rw [← pow_add]
    _ = 2 ^ ((k + 3) * E) := by rw [show E + (k + 2) * E = (k + 3) * E from by ring]
    _ < 2 ^ (2 ^ (2 ^ k)) := Nat.pow_lt_pow_right (by norm_num) hExp

/-- **A near-maximally-hard function (proved)**: on `2^k` bits, depth `≥ 2^k−k−4`. -/
theorem exists_deep_pow2_tight (k : ℕ) (hk : 5 ≤ k) :
    ∃ f : (Fin (2 ^ k) → Bool) → Bool, 2 ^ k - k - 4 ≤ dmdepth f :=
  exists_deep (2 ^ k) (2 ^ (2 ^ k - k - 4)) (2 ^ k - k - 4)
    (pow_pos (by norm_num) k) (le_refl _) (hard_pow2_hnum_tight k hk)

/-- **THE TIGHT DETERMINISTIC LOWER BOUND (proved)**: every `U`-protocol on `2^k`
bits costs `≥ 2^k − k − 5` (`≈ N − log N`). -/
theorem uprotocol_lower_bound_tight (k : ℕ) (hk : 5 ≤ k) {d : ℕ}
    (h : HasUProtocol (Finset.univ : Finset (Fin (2 ^ k) → Bool)) Finset.univ d) :
    2 ^ k - k - 5 ≤ d := by
  obtain ⟨f, hf⟩ := exists_deep_pow2_tight k hk
  have hn : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hle := uprotocol_cost_lower hn h f
  omega

/-- **`ucc (2^k) ≥ 2^k − k − 5` (proved)**: the tight deterministic partition
bound.  With `ucc (2^k) ≤ 2·2^k` (KRW15), `D(U_N) ∈ [N − log₂ N − 5, 2N]`. -/
theorem ucc_pow2_tight (k : ℕ) (hk : 5 ≤ k) : 2 ^ k - k - 5 ≤ ucc (2 ^ k) := by
  have hn : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hne : {d | HasUProtocol (Finset.univ : Finset (Fin (2 ^ k) → Bool)) Finset.univ d}.Nonempty :=
    ⟨2 * 2 ^ k, uprotocol_exists hn⟩
  exact uprotocol_lower_bound_tight k hk (Nat.sInf_mem hne)

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.exists_deep_pow2_tight
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.ucc_pow2_tight
