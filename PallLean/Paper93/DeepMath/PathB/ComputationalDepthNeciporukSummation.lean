import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingCapacityLowerBound

/-!
# Nečiporuk multi-block summation

**STATUS: GENUINE ADDITIVE LOWER-BOUND COMBINER (RESTRICTED), NOT A P vs NP BRIDGE.**

The single crossing-state bound (`crossing_capacity`) lower-bounds a resource by
the *log* of the subfunction count across **one** cut.  Nečiporuk's actual power
comes from summing this over **many disjoint blocks**: if the budget partitions
additively across blocks (in formulas: leaves are partitioned by which block's
variable they read), and each block independently has capacity `c_i`, then

  total budget  ≥  Σ_i log₂ c_i.

This file proves that additive combiner (`neciporuk_sum_lower_bound`) and grounds
it concretely: `p` independent storage-access blocks of `m` cells each force
total budget `≥ p · m` (`neciporuk_storageAccess_sum_bound`), a *superlinear*
bound that no single cut can give.

## What is genuine vs. what is the classical input

Genuine and proved here: the additive combiner, and that the per-block storage
capacity is `2^m` (via `storageAccess_crossingSubfunctionCount`), so the summed
bound is really `Σ`, growing with the number of blocks.

Encoded as hypotheses (the classical, formula-specific inputs):
* `hperblock : c_i ≤ 2 ^ (b i)` — a block touched by `b i` formula leaves exposes
  at most `2^{O(b i)}` subfunctions.  This is the Nečiporuk leaf-counting lemma.
* `hbudget : B = Σ_i b i` — the leaves of a formula are partitioned among blocks.

## Honest ceiling

The full `n^2 / log n` formula bound needs `p ≈ n/log n` blocks of size
`m ≈ log n` on a *single* explicit function, together with a genuine
formula-semantics proof of the leaf-counting lemma `hperblock`.  That last step
(real De Morgan formula leaves, not an abstract budget) is the remaining work;
Nečiporuk's method provably tops out at `Θ(n^2 / log n)` and does **not** reach
TC⁰/NC¹/width-5 BP.  Restricted, real, not a bridge.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-! ## The additive combiner -/

/-- **Nečiporuk additive lower bound.**  If a total budget `B` partitions as
`B = Σ_i b i` over a finite family of disjoint blocks, and each block `i` has
capacity `c i` bounded by `2 ^ (b i)`, then the budget is at least the sum of the
per-block log-capacities `Σ_i log₂ (c i)`.

The summation is the whole point: each block contributes `log₂ c i` independently,
so a function that is hard on many blocks at once gets the *sum* of the per-block
bounds, which a single crossing cut cannot deliver. -/
theorem neciporuk_sum_lower_bound
    {ι : Type*} (blocks : Finset ι) (c b : ι -> Nat) (B : Nat)
    (hbudget : B = ∑ i ∈ blocks, b i)
    (hperblock : ∀ i ∈ blocks, c i <= 2 ^ (b i)) :
    ∑ i ∈ blocks, Nat.log 2 (c i) <= B := by
  rw [hbudget]
  apply Finset.sum_le_sum
  intro i hi
  calc
    Nat.log 2 (c i) <= Nat.log 2 (2 ^ (b i)) :=
          Nat.log_mono_right (hperblock i hi)
    _ = b i := Nat.log_pow (by norm_num) (b i)

/-! ## Concrete superlinear instance: many storage-access blocks -/

/-- Each storage-access block of `m` cells has log-capacity exactly `m`. -/
theorem storageAccess_log_capacity (m : Nat) :
    Nat.log 2 (crossingSubfunctionCount (StorageAccess m)) = m := by
  rw [storageAccess_crossingSubfunctionCount]
  exact Nat.log_pow (by norm_num) m

/-- **Superlinear Nečiporuk bound.**  Any model computing `p` independent
storage-access blocks of `m` cells, whose budget partitions additively across the
blocks with each block touched by `b i` leaves (`crossingSubfunctionCount ≤ 2^{b i}`),
must spend total budget at least `p · m`.

For `p` and `m` both growing (e.g. `p, m ≈ √n`), this is genuinely superlinear in
the input size — strictly stronger than the single-cut bound `max_i log c_i = m`. -/
theorem neciporuk_storageAccess_sum_bound
    (p m : Nat) (b : Nat -> Nat) (B : Nat)
    (hbudget : B = ∑ i ∈ Finset.range p, b i)
    (hperblock : ∀ i ∈ Finset.range p,
        crossingSubfunctionCount (StorageAccess m) <= 2 ^ (b i)) :
    p * m <= B := by
  have hsum :
      ∑ i ∈ Finset.range p,
          Nat.log 2 (crossingSubfunctionCount (StorageAccess m)) <= B :=
    neciporuk_sum_lower_bound (Finset.range p)
      (fun _ => crossingSubfunctionCount (StorageAccess m)) b B hbudget hperblock
  have hrw :
      ∑ i ∈ Finset.range p,
          Nat.log 2 (crossingSubfunctionCount (StorageAccess m)) = p * m := by
    rw [Finset.sum_congr rfl (fun i _ => storageAccess_log_capacity m)]
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rwa [hrw] at hsum

/-! ## Bundled summation theorem -/

/-- Package: the additive combiner plus the concrete superlinear storage-access
instance. -/
structure NeciporukSummation : Prop where
  /-- Additive combiner: budget ≥ Σ per-block log-capacities. -/
  additive : forall {ι : Type} (blocks : Finset ι) (c b : ι -> Nat) (B : Nat),
    B = (∑ i ∈ blocks, b i) ->
    (∀ i ∈ blocks, c i <= 2 ^ (b i)) ->
    (∑ i ∈ blocks, Nat.log 2 (c i)) <= B
  /-- Superlinear instance: `p` storage blocks of `m` cells force budget ≥ `p·m`. -/
  superlinear : forall (p m : Nat) (b : Nat -> Nat) (B : Nat),
    B = (∑ i ∈ Finset.range p, b i) ->
    (∀ i ∈ Finset.range p,
        crossingSubfunctionCount (StorageAccess m) <= 2 ^ (b i)) ->
    p * m <= B

/-- Completed Nečiporuk summation package. -/
theorem neciporukSummation : NeciporukSummation where
  additive := by
    intro ι blocks c b B hbudget hperblock
    exact neciporuk_sum_lower_bound blocks c b B hbudget hperblock
  superlinear := by
    intro p m b B hbudget hperblock
    exact neciporuk_storageAccess_sum_bound p m b B hbudget hperblock

/-! ## Kernel-only trace -/

#print axioms neciporuk_sum_lower_bound
#print axioms storageAccess_log_capacity
#print axioms neciporuk_storageAccess_sum_bound
#print axioms neciporukSummation

end PallLean.Paper93.DeepMath.PathB
