import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRankContextualWidth

/-!
# Hypergraph holonomy SPDP — a cycle‑obstruction invariant (first calibration)

Fixed‑order SPDP sees only a Hamming ball; it misses *global* obstruction.  The holonomy upgrade is a genuine
cycle invariant, **not** renamed SPDP: on a graph of parity constraints (Tseitin), the **holonomy of a cycle `C`**
is the `F₂` sum of the vertex charges around it,

`cycleHolonomy C charge = ⊕_{v ∈ C} charge(v)`  (parity of the charged vertices on `C`).

Summing the vertex constraints around a cycle, every edge is counted twice and cancels over `F₂`, so a *satisfiable*
charge has zero holonomy on every cycle; a charge whose sum around `C` is odd is **globally inconsistent on `C`** —
the Tseitin UNSAT obstruction.  Crucially this obstruction is visible at **Hamming weight 1**: a single charged
vertex on `C` already flips the holonomy.  So holonomy is *less local* without raising any derivative order — it
reads a global cycle obstruction from a weight‑1 difference, exactly the regime the affine‑indicator collapse
(`…AffineIndicatorCollapse`) showed plain local SPDP cannot reach.

## What is proved (clean axioms, no `sorry`) — HAL's three calibration tests

* **Easy collapse (test 1):** `holonomy_zero_charge` / `holSig_zero_charge` — a consistent (zero) charge has
  *trivial* holonomy on every cycle.  (Equality/IP‑style satisfiable configurations carry no obstruction.)
* **Tseitin survival (test 2):** `cycleHolonomy_singleton` — a single charge on a cycle gives *nontrivial*
  holonomy (`= true`).  `holonomy_realizes_all` — over `m` disjoint cycles the holonomy signature realizes **all
  `2^m` patterns**: charged expander cycles survive with exponentially many holonomy classes.
* **The contrast that matters:** zero charge → `0`, weight‑1 charge → `1` on the same cycle, so holonomy
  distinguishes them at Hamming weight `≤ 1` — global obstruction seen by a maximally local probe.

## Honest scope

This is the first calibration: it defines the cycle‑obstruction invariant and proves the easy/hard split
(consistent → trivial, charged → `2^m` classes).  It does **not** yet prove an ACC⁰ lower bound.  The live targets
remain: (P‑side) modular gate layers create only controlled holonomy classes — the `ACC0LowRealizedGodelSPDP`
analogue — and (hard side) the Tseitin/expander survival above must be paired with that P‑side control.  And the
naturalness caveat from `…DynamicSPDPNaturalnessRange` still applies: holonomy is efficiently computable and
large/useful, so against PRF‑containing classes (`P/poly`) the Razborov–Rudich barrier returns — holonomy‑SPDP is
a promising ACC⁰/Tseitin invariant, **not** a path to `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP

variable {V : Type*}

/-- **Cycle holonomy:** the `F₂` sum of charges around a cycle `C` — the parity of the charged vertices on `C`. -/
def cycleHolonomy (C : Finset V) (charge : V → Bool) : Bool :=
  decide ((C.filter (fun v => charge v = true)).card % 2 = 1)

/-- The holonomy **signature** of a charge over a family of `m` cycles. -/
def holSig {m : ℕ} (cycle : Fin m → Finset V) (charge : V → Bool) : Fin m → Bool :=
  fun i => cycleHolonomy (cycle i) charge

/-- **Easy collapse (proved): a consistent (zero) charge has trivial holonomy on every cycle.** -/
theorem holonomy_zero_charge (C : Finset V) : cycleHolonomy C (fun _ => false) = false := by
  unfold cycleHolonomy
  simp

/-- The zero charge has the trivial holonomy signature. -/
theorem holSig_zero_charge {m : ℕ} (cycle : Fin m → Finset V) :
    holSig cycle (fun _ => false) = (fun _ => false) := by
  funext i
  exact holonomy_zero_charge (cycle i)

/-- **Tseitin survival, single charge (proved): one charge on a cycle gives nontrivial holonomy.**  The obstruction
is visible at Hamming weight `1` — a single charged vertex flips the holonomy from `0` to `1`. -/
theorem cycleHolonomy_singleton [DecidableEq V] (C : Finset V) (v0 : V) (hv : v0 ∈ C) :
    cycleHolonomy C (fun v => decide (v = v0)) = true := by
  unfold cycleHolonomy
  have hset : C.filter (fun v => (decide (v = v0)) = true) = {v0} := by
    ext v
    simp only [Finset.mem_filter, decide_eq_true_eq, Finset.mem_singleton]
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · rintro rfl; exact ⟨hv, rfl⟩
  rw [hset]
  simp

/-- A family of `m` pairwise‑separated cycles, each with a representative vertex that lies *only* in its own
cycle (the local independence an expander cycle basis provides). -/
structure DisjointCycles (V : Type*) (m : ℕ) where
  cycle : Fin m → Finset V
  rep : Fin m → V
  rep_mem : ∀ i, rep i ∈ cycle i
  rep_only_own : ∀ i j, rep i ∈ cycle j → i = j

/-- **Holonomy of a charge that charges exactly the representatives in `S` (proved): `= [i ∈ S]`.**  Charging the
representative of cycle `i` flips precisely cycle `i`'s holonomy and no other's. -/
theorem holSig_chargeRep [DecidableEq V] {m : ℕ} (G : DisjointCycles V m) (S : Finset (Fin m)) (i : Fin m) :
    cycleHolonomy (G.cycle i) (fun v => decide (v ∈ S.image G.rep)) = decide (i ∈ S) := by
  unfold cycleHolonomy
  by_cases hiS : i ∈ S
  · have hset : (G.cycle i).filter (fun v => (decide (v ∈ S.image G.rep)) = true) = {G.rep i} := by
      ext v
      simp only [Finset.mem_filter, decide_eq_true_eq, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨hvc, j, hjS, hrep⟩
        have hmem : G.rep j ∈ G.cycle i := hrep ▸ hvc
        have hji : j = i := G.rep_only_own j i hmem
        rw [← hrep, hji]
      · rintro rfl
        exact ⟨G.rep_mem i, i, hiS, rfl⟩
    rw [hset]; simp [hiS]
  · have hset : (G.cycle i).filter (fun v => (decide (v ∈ S.image G.rep)) = true) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hvc
      rw [decide_eq_true_eq, Finset.mem_image]
      rintro ⟨j, hjS, hrep⟩
      have hmem : G.rep j ∈ G.cycle i := hrep ▸ hvc
      have hji : j = i := G.rep_only_own j i hmem
      exact hiS (hji ▸ hjS)
    rw [hset]; simp [hiS]

/-- **Tseitin survival, full (proved): the holonomy signature realizes all `2^m` patterns.**  For every target
obstruction pattern `t`, a charge realizes it (`holSig = t`).  So `m` disjoint charged cycles give `2^m` distinct
holonomy classes — exponential survival, the hard‑side signal. -/
theorem holonomy_realizes_all [DecidableEq V] {m : ℕ} (G : DisjointCycles V m) (t : Fin m → Bool) :
    ∃ charge : V → Bool, holSig G.cycle charge = t := by
  refine ⟨fun v => decide (v ∈ (Finset.univ.filter (fun i => t i = true)).image G.rep), ?_⟩
  funext i
  rw [holSig, holSig_chargeRep G (Finset.univ.filter (fun i => t i = true)) i]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases t i <;> simp

end PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP.holonomy_zero_charge
#print axioms PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP.cycleHolonomy_singleton
#print axioms PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP.holonomy_realizes_all
