import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellCountCharacterization
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RefinedObserverModel

/-!
# MOD gate semantics, no-go, and the residual observer — the ACC⁰ battlefield

This file grounds the `MOD` obstruction in *gate semantics* and then builds the `MOD`-residual observer the refined
route asks for — and proves the honest punchline: **the residual observer reduces to the membership observer for
`MOD`, so it inherits the membership hard-regime ceiling.**  The variable-fixing / observer-cell programme cannot
collapse `MOD` gates, and the reason is exact.

## Part A — gate semantics: why `AND`/`OR` switch but `MOD` blocks

We model the effective value `effVal ρ x i := (ρ i).getD (x i)` (fixed coordinates take `ρ`'s value, free ones take
`x`).  A parity gate's value is `parityVal ρ S x := ∑_{i∈S} [effVal ρ x i]` over `ZMod 2`.

* **`parity_constant_iff_support_fully_fixed`** — a parity (`MOD₂`) gate is constant under `ρ` **iff its support is
  entirely fixed**.  The forward direction *is* the **no-absorbing-value** statement: a *single* free input already
  forces the gate to vary, so no fixing of other inputs can deactivate it.
* **`and_constant_of_absorbing`** (contrast) — an `AND` gate *is* deactivated by one fixed-`false` input, even with
  free inputs remaining.  `AND` has an absorbing value; parity has none.  This is exactly why `AC⁰` switches and
  `ACC⁰` does not.

## Part B — the residual observer reduces to membership (the no-escape)

A coordinate's *residual contribution* to a linear/`MOD` gate is a free summand iff it is free and in the support —
which for a free coordinate is exactly its membership.  So:

* **`residual_eq_membership_of_free`** — for a free coordinate the residual signature **equals** the membership pattern.
* **`residual_merge_iff_sameCell`** — two free coordinates merge under the residual observer **iff** they share a
  membership cell.
* **`residualPatternCount_eq_membership_on_free`** — over a free live set the residual cell count **equals** the
  membership cell count.
* **`residual_no_escape_in_hardRegime`** — in the hard regime distinct free coordinates never merge: the residual
  observer does **not** rescue the collapse.

## Honest conclusion

The `MOD`-residual observer is *not* a new escape: a coordinate's affine contribution to a linear gate is its
membership, so the residual observer **is** the membership observer on free coordinates, with the same proved ceiling
(`…ACC0CellCountCharacterization`).  This localizes the `ACC⁰` barrier sharply: the entire observer / coordinate-merging
programme (membership, rank, cell-count, variable-fixing, residual) is membership-bounded for `MOD`, which is why
`ACC⁰` lower bounds need the *polynomial method* (low-degree approximation / rank), not observer cells.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0CellCountRoute
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0RefinedObserverModel

variable {k n : ℕ}

/-! ## Part A — gate semantics -/

/-- The effective value of a coordinate under `ρ`: fixed coordinates take `ρ`'s value, free ones take `x`. -/
def effVal (ρ : Restriction n) (x : Fin n → Bool) (i : Fin n) : Bool := (ρ i).getD (x i)

/-- The parity (`MOD₂`) charge of a gate on the effective assignment. -/
def parityVal (ρ : Restriction n) (S : Finset (Fin n)) (x : Fin n → Bool) : ZMod 2 :=
  ∑ i ∈ S, (if effVal ρ x i then 1 else 0)

/-- A parity gate is **constant under `ρ`** if its value does not depend on the free assignment. -/
def ParityConstant (ρ : Restriction n) (S : Finset (Fin n)) : Prop :=
  ∀ x y : Fin n → Bool, parityVal ρ S x = parityVal ρ S y

/-- **A parity gate is constant iff its support is entirely fixed (proved).**  The forward direction is the
no-absorbing-value statement: one free input already makes the gate vary. -/
theorem parity_constant_iff_support_fully_fixed (ρ : Restriction n) (S : Finset (Fin n)) :
    ParityConstant ρ S ↔ ∀ i ∈ S, ρ i ≠ none := by
  constructor
  · intro hconst i₀ hi₀S hi₀free
    set x : Fin n → Bool := fun _ => false with hxdef
    have key := hconst x (Function.update x i₀ true)
    have hpar : ∀ z : Fin n → Bool, parityVal ρ S z
        = (if effVal ρ z i₀ then (1 : ZMod 2) else 0)
          + ∑ i ∈ S.erase i₀, (if effVal ρ z i then (1 : ZMod 2) else 0) := by
      intro z
      simp only [parityVal]
      rw [← Finset.add_sum_erase S _ hi₀S]
    have herase : (∑ i ∈ S.erase i₀, (if effVal ρ x i then (1 : ZMod 2) else 0))
        = ∑ i ∈ S.erase i₀, (if effVal ρ (Function.update x i₀ true) i then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [effVal, effVal, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    have hx0 : effVal ρ x i₀ = false := by simp [effVal, hxdef, hi₀free]
    have hy0 : effVal ρ (Function.update x i₀ true) i₀ = true := by
      simp [effVal, hi₀free, Function.update_self]
    rw [hpar x, hpar (Function.update x i₀ true), hx0, hy0, herase] at key
    simp at key
  · intro hfix x y
    apply Finset.sum_congr rfl
    intro i hiS
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (hfix i hiS)
    simp [effVal, hb]

/-! ### Contrast: `AND` has an absorbing value -/

/-- An `AND` gate's value on the effective assignment. -/
def andVal (ρ : Restriction n) (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∀ i ∈ S, effVal ρ x i = true)

/-- An `AND` gate is **constant** under `ρ` if its value does not depend on the free assignment. -/
def AndConstant (ρ : Restriction n) (S : Finset (Fin n)) : Prop :=
  ∀ x y : Fin n → Bool, andVal ρ S x = andVal ρ S y

/-- **`AND` has an absorbing value (proved): one fixed-`false` input deactivates the gate**, even with free inputs
remaining — the opposite of parity.  This is why `AC⁰` switches under restriction. -/
theorem and_constant_of_absorbing (ρ : Restriction n) (S : Finset (Fin n))
    (h : ∃ i ∈ S, ρ i = some false) : AndConstant ρ S := by
  obtain ⟨i₀, hi₀S, hi₀⟩ := h
  have hfalse : ∀ x : Fin n → Bool, andVal ρ S x = false := by
    intro x
    simp only [andVal, decide_eq_false_iff_not]
    intro hall
    have h2 := hall i₀ hi₀S
    simp [effVal, hi₀] at h2
  intro x y
  rw [hfalse x, hfalse y]

/-! ## Part B — the residual observer reduces to membership -/

/-- The **residual signature** of a coordinate: it is a free summand of a `MOD` gate iff it is free and in the support. -/
def residualSignature (ρ : Restriction n) (supports : Fin k → Finset (Fin n)) (v : Fin n) :
    Fin k → ZMod 2 :=
  fun j => if ρ v = none ∧ v ∈ supports j then 1 else 0

/-- **For a free coordinate the residual signature equals the membership pattern (proved).** -/
theorem residual_eq_membership_of_free (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (v : Fin n) (hv : ρ v = none) :
    residualSignature ρ supports v = cellPatternVec supports v := by
  funext j
  simp only [residualSignature, cellPatternVec]
  by_cases hvj : v ∈ supports j
  · rw [if_pos ⟨hv, hvj⟩, if_pos hvj]
  · rw [if_neg (fun hc => hvj hc.2), if_neg hvj]

/-- **No merging gain (proved): two free coordinates merge under the residual observer iff they share a membership
cell** — the residual observer is the membership observer on free coordinates. -/
theorem residual_merge_iff_sameCell (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (v w : Fin n) (hv : ρ v = none) (hw : ρ w = none) :
    residualSignature ρ supports v = residualSignature ρ supports w ↔ SameCell supports v w := by
  rw [residual_eq_membership_of_free ρ supports v hv,
      residual_eq_membership_of_free ρ supports w hw, sameCell_iff_pattern]

/-- The number of distinct residual observer types over a live set. -/
def residualPatternCount (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (L : Finset (Fin n)) : ℕ :=
  (L.image (residualSignature ρ supports)).card

/-- **Over a free live set the residual cell count equals the membership cell count (proved).** -/
theorem residualPatternCount_eq_membership_on_free (ρ : Restriction n)
    (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) (hL : ∀ v ∈ L, ρ v = none) :
    residualPatternCount ρ supports L = cellPatternCount supports L := by
  unfold residualPatternCount cellPatternCount cellPatternImage
  congr 1
  apply Finset.image_congr
  intro v hv
  exact residual_eq_membership_of_free ρ supports v (hL v (Finset.mem_coe.mp hv))

/-- **The residual observer gives no escape in the hard regime (proved).**  If the supports separate every coordinate
(membership injective — the hard regime), then distinct free coordinates never merge under the residual observer
either: the variable-fixing / residual route inherits the membership ceiling for `MOD`. -/
theorem residual_no_escape_in_hardRegime (ρ : Restriction n) (supports : Fin k → Finset (Fin n))
    (hsep : ∀ v w, SameCell supports v w → v = w) (v w : Fin n)
    (hv : ρ v = none) (hw : ρ w = none) (hne : v ≠ w) :
    residualSignature ρ supports v ≠ residualSignature ρ supports w := by
  intro hmerge
  exact hne (hsep v w ((residual_merge_iff_sameCell ρ supports v w hv hw).mp hmerge))

end PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver.parity_constant_iff_support_fully_fixed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver.and_constant_of_absorbing
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver.residual_eq_membership_of_free
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver.residual_merge_iff_sameCell
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver.residualPatternCount_eq_membership_on_free
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MODResidualObserver.residual_no_escape_in_hardRegime
