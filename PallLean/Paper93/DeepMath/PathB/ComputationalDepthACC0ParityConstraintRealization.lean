import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DisjointFragmentSpeedup

/-!
# Parity (MOD₂) constraint realization: realizable ⟺ the F₂ linear system is consistent

`…ACC0OracleRestrictionRealization` proved realizability for *disjoint* MOD supports and a no-go for conflicting
overlaps.  The honest middle case is a *linear-algebra* characterization, cleanest for **parity (MOD₂) gates**: forcing
a parity gate is a linear equation `∑_{i∈Sⱼ} xᵢ = cⱼ (mod 2)`, so an overlapping family is realizable **iff** the F₂
linear system is consistent (has a Boolean = F₂ solution).

The key simplification first: realizability does **not** need disjointness to *characterize* — it is exactly the
existence of a single achieving input (`realizable_iff_achievable`, for arbitrary MOD gates).  Disjointness was only
used to *construct* that input; the no-go is exactly the case where no achieving input exists.  For parity, an
achieving input exists iff the linear system is consistent.

The reachable gate-output image (`control_sat_iff_reachable_image`) is then the genuine observer boundary — the SAT
search is over the *reachable* outputs, not a pretended-independent `2^k`.  For parity that reachable set is an
**F₂-subspace** (`parityVector_xor`, `parity_reachable_zero_mem`, `parity_reachable_add_mem`), so its size is `2^rank`
— `2^k` only in the disjoint (full-rank) case.

## What is proved (clean axioms, no `sorry`)

* `realizable_iff_achievable` — (arbitrary MOD) realizable `ρ` ⟺ `∃ x, ∀ j b, ρ j = some b → (gateⱼ).eval x = b`.
* `parityGate`, `parity_force_linear` — a parity gate is `MOD₂`; forcing it is the equation `parity = cⱼ`.
* `parity_realizable_iff_consistent` — realizable ⟺ the F₂ parity system has a Boolean solution.
* `control_sat_iff_reachable_image` — (arbitrary MOD) SAT ⟺ search the *reachable* gate-output image.
* `parityVector_xor` / `parity_reachable_zero_mem` / `parity_reachable_add_mem` — the reachable parity image is an
  F₂-subspace (closed under `0` and `+`), so `|image| = 2^rank`.

## Honest scope

This characterizes realizability (= F₂ consistency) and shows the reachable image is linear — the structural content
of `2^rank`.  The exact cardinality `|image| = 2^rank` as a closed form needs Mathlib's finite-field `finrank`-card
machinery; the subspace facts here are the structural half, the quantitative `finrank` step is left for a follow-up.
General `MOD_q` (`q` prime) is a 0/1 feasibility problem over `ZMod q` (not free linear algebra), harder — MOD₂ is the
clean first target.  Still the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl
open PallLean.Paper93.DeepMath.PathB.ACC0OracleRestrictionRealization

variable {n k : ℕ}

/-! ## Realizability ⟺ an achieving input exists (arbitrary MOD gates) -/

/-- **Realizability needs no disjointness to characterize (proved): `ρ` is realizable iff a single input achieves the
fixed pattern.**  Disjointness was only used to *construct* the input; the no-go is when no such input exists. -/
theorem realizable_iff_achievable (ρ : Fin k → Option Bool) (gate : Fin k → ModGate n) :
    RealizableByInputRestriction ρ gate ↔ ∃ x, ∀ j b, ρ j = some b → (gate j).eval x = b := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨fun i => (σ i).getD false, fun j b hjb => hσ j b hjb _ (by intro i v hv; simp [hv])⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun i => if ∃ j, (∃ b', ρ j = some b') ∧ i ∈ (gate j).support
        then some (x i) else none, ?_⟩
    intro j b hjb x' hx'
    have hagree : ∀ i ∈ (gate j).support, x' i = x i := by
      intro i hi
      have hex : ∃ j', (∃ b', ρ j' = some b') ∧ i ∈ (gate j').support := ⟨j, ⟨b, hjb⟩, hi⟩
      exact hx' i (x i) (dif_pos hex)
    rw [modGate_eval_congr (gate j) hagree]
    exact hx j b hjb

/-! ## Parity gates as MOD₂ -/

/-- A parity (MOD₂) gate: accept when the support count is `t` mod `2`. -/
def parityGate (S : Finset (Fin n)) (t : ZMod 2) : ModGate n := ⟨2, S, t⟩

/-- Over `ZMod 2`, two elements are unequal iff they differ by `1`. -/
theorem zmod2_ne_iff (s t : ZMod 2) : ¬ s = t ↔ s = t + 1 := by
  revert s t; decide

/-- **Forcing a parity gate is a linear equation (proved): `eval = b ⟺ parity = (t if b else t+1)`.** -/
theorem parity_force_linear (S : Finset (Fin n)) (t : ZMod 2) (x : Fin n → Bool) (b : Bool) :
    (parityGate S t).eval x = b ↔ modQStatOn S 2 x = (if b then t else t + 1) := by
  unfold parityGate ModGate.eval
  cases b with
  | true => simp
  | false =>
      show decide (modQStatOn S 2 x = t) = false ↔ modQStatOn S 2 x = t + 1
      rw [decide_eq_false_iff_not]
      exact zmod2_ne_iff _ _

/-- **Parity realizability ⟺ the F₂ system is consistent (proved): a forced family of parity gates is realizable iff
the linear system `parity(Sⱼ) = (tⱼ if bⱼ else tⱼ+1)` has a Boolean solution.** -/
theorem parity_realizable_iff_consistent (ρ : Fin k → Option Bool)
    (S : Fin k → Finset (Fin n)) (t : Fin k → ZMod 2) :
    RealizableByInputRestriction ρ (fun j => parityGate (S j) (t j)) ↔
      ∃ x : Fin n → Bool, ∀ j b, ρ j = some b →
        modQStatOn (S j) 2 x = (if b then t j else t j + 1) := by
  rw [realizable_iff_achievable]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun j b hjb => (parity_force_linear (S j) (t j) x b).mp (hx j b hjb)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, fun j b hjb => (parity_force_linear (S j) (t j) x b).mpr (hx j b hjb)⟩

/-! ## The reachable gate-output image is the observer boundary -/

/-- **SAT searches the *reachable* gate-output image (proved, arbitrary MOD).**  The boundary is exactly the set of
achievable output vectors — not a pretended-independent `2^k`. -/
theorem control_sat_iff_reachable_image (C : OracleControl k) (gate : Fin k → ModGate n) :
    Satisfiable (fun x => controlEval C (fun j => (gate j).eval x)) ↔
      ∃ y ∈ Finset.univ.image (fun x => fun j => (gate j).eval x), controlEval C y = true :=
  observed_sat_iff (controlEval C) (fun _ => rfl)

/-! ## The reachable parity image is an F₂-subspace (size `2^rank`) -/

/-- The parity-statistic vector of an input. -/
def parityVector (S : Fin k → Finset (Fin n)) (x : Fin n → Bool) : Fin k → ZMod 2 :=
  fun j => modQStatOn (S j) 2 x

/-- The mod-2 support statistic as a sum of per-bit `ZMod 2` values. -/
theorem modQStatOn_two_eq_sum (S : Finset (Fin n)) (x : Fin n → Bool) :
    modQStatOn S 2 x = ∑ i ∈ S, (if x i then (1 : ZMod 2) else 0) := by
  unfold modQStatOn weightOn
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => by by_cases h : x i <;> simp [h])

/-- **Parity is additive over `xor` (proved): `parityVector` of the bitwise `xor` is the `ZMod 2` sum.** -/
theorem parityVector_xor (S : Fin k → Finset (Fin n)) (x x' : Fin n → Bool) :
    parityVector S (fun i => xor (x i) (x' i)) = parityVector S x + parityVector S x' := by
  funext j
  simp only [parityVector, Pi.add_apply, modQStatOn_two_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by cases x i <;> cases x' i <;> decide)

/-- **The reachable parity image contains `0` (proved).** -/
theorem parity_reachable_zero_mem (S : Fin k → Finset (Fin n)) :
    (0 : Fin k → ZMod 2) ∈ Set.range (parityVector S) := by
  refine ⟨fun _ => false, ?_⟩
  funext j
  simp [parityVector, modQStatOn_two_eq_sum]

/-- **The reachable parity image is closed under addition (proved): it is an F₂-subspace, so `|image| = 2^rank`.** -/
theorem parity_reachable_add_mem (S : Fin k → Finset (Fin n)) {u v : Fin k → ZMod 2}
    (hu : u ∈ Set.range (parityVector S)) (hv : v ∈ Set.range (parityVector S)) :
    u + v ∈ Set.range (parityVector S) := by
  obtain ⟨x, hx⟩ := hu
  obtain ⟨x', hx'⟩ := hv
  exact ⟨fun i => xor (x i) (x' i), by rw [parityVector_xor, hx, hx']⟩

end PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization.realizable_iff_achievable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization.parity_realizable_iff_consistent
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization.parity_reachable_add_mem
