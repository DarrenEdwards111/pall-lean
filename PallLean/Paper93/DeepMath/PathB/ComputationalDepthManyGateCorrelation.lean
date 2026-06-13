import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwoGateCorrelation

/-!
# Many gates: the cell‑covering obstruction

`…TwoGateCorrelation` reduced two‑gate composition to a common‑cell condition.  This file takes it to `k` gates and
makes the obstruction a precise **covering / shattering** condition on the holonomy support `D`.

For supports `S₁, …, S_k ⊆ Fin n`, the **cell** of a coordinate `v` is its membership pattern
`(v ∈ S₁, …, v ∈ S_k)`.  The off‑diagonal flip‑both `pairSwap v w` preserves *every* support‑count (hence every
`MOD q_j` gate, any moduli) **iff `v` and `w` lie in the same cell** (`SameCell`), because each support‑count is
preserved exactly when `v, w` are on the same side of that support (`weightOn_pairSwap_eq`).

So the correlation engine bites **iff there is a `D`‑witness edge inside a cell**: distinct `v ∈ D`, `w ∉ D` with
`SameCell v w`.  Its negation is exactly that **`D` respects the cell partition** — `D` is a union of whole cells
(`RespectsCells`).  This is the composition frontier:

* **Coarse supports (few gates):** few cells, so any `D` that is neither a union of cells crosses one — a witness
  exists and the engine bites.
* **Shattering supports (many gates):** if the supports separate points into singleton cells
  (`respectsCells_of_separating`), *every* `D` respects the cells, **no witness exists**, and the involution
  method fails.  Separating `Fin n` into singletons needs `≥ ⌈log₂ n⌉` gates — so once an ACC⁰ predictor reads
  enough independent modular statistics to shatter the coordinates, the elementary involution engine dies.  This
  is the matching/flow wall in its sharpest form, `NP ⊄ ACC⁰`‑strength.

## What is proved (clean axioms, no `sorry`)

* `weightVec`, `weightVec_pairSwap` — the `k`‑gate weight vector is preserved by the flip‑both on a same‑cell pair.
* `kGate_offdiag_balanced`, `kGate_low_correlation_offdiagonal` — **a same‑cell `D`‑witness ⇒ exact balance and no
  correlation advantage** for the `k`‑gate predictor against the holonomy parity (any moduli, any gate function).
* `cellWitness_iff_not_respects` — **the covering characterization**: a witness exists *iff* `D` does not respect
  the cell partition.
* `respectsCells_of_separating` — **the shattering obstruction**: if the supports separate all coordinates into
  singleton cells, every `D` respects the cells, so no witness exists and the engine has nothing to act on.
-/

namespace PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation

open PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments
open PallLean.Paper93.DeepMath.PathB.ModQGateBalance
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation

variable {n k : ℕ}

/-! ## Cells and the `k`‑gate weight vector -/

/-- Two coordinates are in the **same cell** of the support family if they have the same membership pattern. -/
def SameCell (supports : Fin k → Finset (Fin n)) (v w : Fin n) : Prop :=
  ∀ j, (v ∈ supports j ↔ w ∈ supports j)

theorem SameCell.symm {supports : Fin k → Finset (Fin n)} {v w : Fin n}
    (h : SameCell supports v w) : SameCell supports w v := fun j => (h j).symm

/-- The `k`‑gate statistic: the vector of support‑counts (every `MOD q_j` gate factors through this). -/
def weightVec (supports : Fin k → Finset (Fin n)) (x : Fin n → Bool) : Fin k → ℕ :=
  fun j => weightOn (supports j) x

/-- **The weight vector is preserved by the flip‑both on a same‑cell pair (proved).** -/
theorem weightVec_pairSwap (supports : Fin k → Finset (Fin n)) (v w : Fin n) (hvw : v ≠ w)
    (hcell : SameCell supports v w) (x : Fin n → Bool) (hoff : x v ≠ x w) :
    weightVec supports (pairSwap v w x) = weightVec supports x := by
  funext j
  exact weightOn_pairSwap_eq (supports j) v w hvw (hcell j) x hoff

/-! ## A same‑cell witness makes the engine bite -/

/-- **`k`‑gate off‑diagonal balance from a same‑cell witness (proved).**  For a `D`‑witness pair `(v ∈ D, w ∉ D)`
in a common cell, the holonomy parity is exactly balanced inside each class of the `k`‑gate weight vector on the
off‑diagonal. -/
theorem kGate_offdiag_balanced (supports : Fin k → Finset (Fin n)) (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) (hcell : SameCell supports v w) :
    ∀ c ∈ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).image (weightVec supports),
      ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => weightVec supports x = c)).filter (fun x => fParity D x = true)).card
        = ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
            (fun x => weightVec supports x = c)).filter (fun x => fParity D x = false)).card :=
  balanced_offdiag_of_pres (weightVec supports) D v w hvw hvD hwD
    (fun x h => weightVec_pairSwap supports v w hvw hcell x h)

set_option maxHeartbeats 1000000 in
/-- **`k`‑gate no correlation advantage from a same‑cell witness (proved).**  Any gate function `g` of the
`k` modular statistics has no correlation advantage against the holonomy parity on the off‑diagonal. -/
theorem kGate_low_correlation_offdiagonal (supports : Fin k → Finset (Fin n)) (D : Finset (Fin n))
    (v w : Fin n) (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) (hcell : SameCell supports v w)
    (g : (Fin k → ℕ) → Bool) :
    2 * (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => g (weightVec supports x) = fParity D x)).card
      ≤ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).card :=
  low_correlation_of_pres (weightVec supports) g D v w hvw hvD hwD
    (fun x h => weightVec_pairSwap supports v w hvw hcell x h)

/-! ## The covering characterization -/

/-- `D` **respects the cell partition** if it is a union of whole cells (constant on each cell). -/
def RespectsCells (supports : Fin k → Finset (Fin n)) (D : Finset (Fin n)) : Prop :=
  ∀ v w, SameCell supports v w → (v ∈ D ↔ w ∈ D)

/-- A `D`‑witness edge inside a cell: distinct `v ∈ D`, `w ∉ D` with `SameCell v w`. -/
def CellWitness (supports : Fin k → Finset (Fin n)) (D : Finset (Fin n)) : Prop :=
  ∃ v w, v ≠ w ∧ v ∈ D ∧ w ∉ D ∧ SameCell supports v w

/-- **The covering characterization (proved): the engine bites iff `D` does not respect the cell partition.** -/
theorem cellWitness_iff_not_respects (supports : Fin k → Finset (Fin n)) (D : Finset (Fin n)) :
    CellWitness supports D ↔ ¬ RespectsCells supports D := by
  constructor
  · rintro ⟨v, w, _, hvD, hwD, hcell⟩ hresp
    exact hwD ((hresp v w hcell).mp hvD)
  · intro hnr
    by_contra hcw
    apply hnr
    intro v w hcell
    constructor
    · intro hvD
      by_contra hwD
      exact hcw ⟨v, w, (fun h => hwD (h ▸ hvD)), hvD, hwD, hcell⟩
    · intro hwD
      by_contra hvD
      exact hcw ⟨w, v, (fun h => hvD (h ▸ hwD)), hwD, hvD, hcell.symm⟩

/-- **The shattering obstruction (proved): if the supports separate every coordinate into a singleton cell, then
every `D` respects the cells** — so by `cellWitness_iff_not_respects` no witness exists and the involution engine
has nothing to act on.  (Separating `Fin n` into singletons requires `≥ ⌈log₂ n⌉` gates.) -/
theorem respectsCells_of_separating (supports : Fin k → Finset (Fin n)) (D : Finset (Fin n))
    (hsep : ∀ v w, SameCell supports v w → v = w) : RespectsCells supports D :=
  fun v w hcell => by rw [hsep v w hcell]

end PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation

#print axioms PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation.weightVec_pairSwap
#print axioms PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation.kGate_offdiag_balanced
#print axioms PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation.kGate_low_correlation_offdiagonal
#print axioms PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation.cellWitness_iff_not_respects
#print axioms PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation.respectsCells_of_separating
