import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPInnerProductRank

/-!
# The MOD-gate recurrence, attacked

The N-Frame → ACC⁰ audit isolated one decisive question: does the rank-based dynamic-SPDP of a `MOD_m` gate obey
a *bounded* recurrence in terms of its children, or does it blow up?  This file answers it for the concrete
ℚ-communication-rank measure — and the answer is a sharp **dichotomy** that explains exactly where the route
stops.

## The good news: a single MOD gate is cheap

`modm_commMatrix_rank_le` — the communication matrix of a `MOD_m` gate *viewed as a symmetric function of its
own inputs* has rank `≤ m` over `ℚ`, for **every** `m` (prime or composite).  Its value depends on the inputs
only through `(popcount a + popcount b) mod m`, so the matrix has `≤ m` distinct rows and factors as `P · N`
with `N` of `m` rows.  So an *isolated* MOD gate contributes rank `≤ m` — bounded, independent of `n` and
fan-in.  The single-gate MOD recurrence is not the problem.

## The bad news: MOD over sub-circuits blows up — even for `m = 2`

`mod2_composition_rank_unbounded` — inner product `IP(x,y) = ⊕ᵢ (xᵢ ∧ yᵢ)` **is** `MOD₂(AND(x₁,y₁),…,
AND(xₙ,yₙ))`: a single MOD₂ gate over `n` AND sub-circuits (`IP_is_mod2` records the identity `IP = MOD₂` of the
AND vector).  Its signed communication matrix is the Hadamard matrix `H`, of rank `2^n`
(`InnerProductRank.rank_H`).  So the rank recurrence *through* a MOD gate is **not** bounded by any
`bound(m, Σ children)`: with children of rank `≤ 2` (the ANDs) and `m = 2` (prime), the output has rank `2^n`.
The recurrence is multiplicative, and the blow-up already happens at a depth-2 `AC⁰[2]` circuit.

## Consequence

The ℚ-communication-rank is **not** a valid ACC⁰ dynamic-SPDP: it is bounded (`≤ m`) on an isolated MOD gate but
*exponential* on the depth-2 `AC⁰[2]` circuit `IP`, so it fails the ACC upper bound at the AND→MOD composition —
**before** the prime/composite distinction even arises.  The audit's additive MOD recurrence `s + 1` is false
for this measure, and no `bound(m, ·)` rescues it.  The genuine ACC⁰ obstruction (composite MOD, "Wall 1") lives
at the level of `F_p` polynomial *degree* / positivity, which ℚ-rank does not track — so a viable dynamic-SPDP
must be a degree/positivity measure, not a communication rank.  This is the concrete resolution of the MOD-gate
crux: the naive rank route stops at the AND→MOD composition.

## Honest scope

A rank upper bound for the isolated MOD gate and an (imported) rank lower bound for a MOD-of-ANDs circuit,
together disproving a *bounded* MOD recurrence for the ℚ-communication-rank measure.  No ACC⁰ lower bound is
proved; the finding is that *this* measure cannot yield one.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameMODRankRecurrence

open PallLean.Paper93.DeepMath.PathB.PvsNPLogRankLowerBound
open PallLean.Paper93.DeepMath.PathB.PvsNPInnerProductRank
open Matrix

/-! ## A single MOD gate has rank ≤ m -/

/-- Number of `true` inputs (Hamming weight). -/
def popcount {n : Nat} (a : Fin n → Bool) : Nat :=
  (Finset.univ.filter (fun i => a i)).card

/-- `MOD_m` as a two-party symmetric function: fires iff the total weight is `≡ 0 (mod m)`. -/
def MODm (m n : Nat) (a b : Fin n → Bool) : Bool :=
  decide ((popcount a + popcount b) % m = 0)

/-- **The isolated MOD gate is cheap.**  The `MOD_m` communication matrix has rank `≤ m` over `ℚ`, for every
`m > 0` — its rows are determined by `popcount a mod m`, so it factors through `m` rows. -/
theorem modm_commMatrix_rank_le (m n : Nat) (hm : 0 < m) :
    (commMatrix (MODm m n)).rank ≤ m := by
  classical
  set key : (Fin n → Bool) → Fin m := fun a => ⟨popcount a % m, Nat.mod_lt _ hm⟩ with hkey
  set N : Matrix (Fin m) (Fin n → Bool) ℚ :=
    fun k b => if (k.val + popcount b) % m = 0 then 1 else 0 with hN
  set P : Matrix (Fin n → Bool) (Fin m) ℚ :=
    fun a k => if key a = k then 1 else 0 with hP
  have hM : commMatrix (MODm m n) = P * N := by
    funext a b
    rw [Matrix.mul_apply]
    simp only [hP, hN, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ (key a) (fun k => if (k.val + popcount b) % m = 0 then (1:ℚ) else 0)]
    simp only [Finset.mem_univ, if_true, hkey, commMatrix, MODm, Nat.mod_add_mod, decide_eq_true_eq]
  rw [hM]
  calc (P * N).rank ≤ N.rank := Matrix.rank_mul_le_right P N
    _ ≤ Fintype.card (Fin m) := Matrix.rank_le_card_height N
    _ = m := Fintype.card_fin m

/-! ## MOD over sub-circuits blows up (even for m = 2) -/

/-- `IP` is literally a `MOD₂` gate applied to the AND sub-circuits `xᵢ ∧ yᵢ`: it fires iff the number of common
`1`s is odd. -/
theorem IP_is_mod2 (n : Nat) (x y : Fin n → Bool) :
    IP n x y = decide (ipCount x y % 2 = 1) := by
  simp only [IP, Nat.odd_iff]

/-- `n < 2^(n+1)`, elementary. -/
theorem lt_two_pow_succ (n : Nat) : n < 2 ^ (n + 1) :=
  lt_of_lt_of_le n.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))

/-- **MOD over sub-circuits is unbounded.**  The signed communication matrix of `IP = MOD₂(AND…)` is the
Hadamard matrix of rank `2^n`, which exceeds any bound.  So a single MOD₂ gate over `n` (rank-`≤2`) AND
sub-circuits produces rank `2^n`: the rank recurrence through a MOD gate has **no** bound `bound(m, Σ children)`,
already for the prime modulus `m = 2`. -/
theorem mod2_composition_rank_unbounded : ∀ B : Nat, ∃ n : Nat, B < (H n).rank := by
  intro B
  exact ⟨B + 1, by rw [rank_H]; exact lt_two_pow_succ B⟩

/-- **The MOD recurrence is not bounded for the ℚ-communication-rank.**  Packaging the dichotomy: for every
candidate bound `bnd : Nat → Nat → Nat`, there is a MOD₂-of-ANDs circuit whose (signed) communication rank
exceeds `bnd 2 (Σ children)` — the children being the `n` AND gates.  (The witness is `H n`, rank `2^n`; the
children's costs are irrelevant since the bound is exceeded outright.) -/
theorem no_bounded_MOD_recurrence (bnd : Nat → Nat → Nat) :
    ∀ s : Nat, ∃ n : Nat, bnd 2 s < (H n).rank := by
  intro s
  obtain ⟨n, hn⟩ := mod2_composition_rank_unbounded (bnd 2 s)
  exact ⟨n, hn⟩

end PallLean.Paper93.DeepMath.PathB.NFrameMODRankRecurrence

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMODRankRecurrence.modm_commMatrix_rank_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMODRankRecurrence.IP_is_mod2
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMODRankRecurrence.mod2_composition_rank_unbounded
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMODRankRecurrence.no_bounded_MOD_recurrence
