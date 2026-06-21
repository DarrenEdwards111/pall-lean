import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitModel

/-!
# Brick (circuit repr) — faithful polynomial representation of the AND/OR/NOT fragment (proved)

The model bridge from the `ACC0Circuit` type (`…ACC0CircuitModel`) to `MvPolynomial`.  By structural recursion, every
`mod`-free circuit (`const`/`var`/`not`/`and`/`or`) is represented by a polynomial `repr C` over any commutative ring such
that, on Boolean inputs, `eval (repr C)` equals the Boolean value of `eval C` — and `repr C` has total degree at most the
leaf measure `reprDeg C`.  This is the exact `circuit.eval = poly.eval` bridge that the polynomial-method bricks need to
attach to the actual circuit model.

`mod` gates are *excluded* (`ModFree`): over `F_p`, a `MOD_q` gate with `q ≠ p` is provably *not* low-degree (Razborov–
Smolensky), and `q = p^e` (`e ≥ 2`) has the A.3 obstruction — so a faithful single-field representation of the full circuit
does not exist.  This brick is the honest mod-free (AC⁰) model bridge; the quasipoly `composite_BT_degree` for arbitrary
`ACC⁰` is *not* attempted (it needs the approximate polynomials and the prime-power method — open, not faked).

## What is proved (clean axioms, no `sorry`)

* **`repr`**, **`reprDeg`**, **`ModFree`** — the representation, its degree measure, the mod-free predicate.
* **`repr_eval`** (PROVED) — `ModFree C → eval (bv ∘ x) (repr C) = bv (ACC0CircuitModel.eval C x)` (faithful on Booleans).
* **`repr_totalDegree_le`** (PROVED) — `(repr C).totalDegree ≤ reprDeg C`.

## Honest scope

The faithful representation of the **mod-free** (`AC⁰`) fragment, exact, with a leaf-degree bound.  It does **not** represent
`MOD` gates (RS / prime-power obstruction), give quasipolynomial degree (the exact degree is the leaf count, not polylog),
nor discharge `composite_BT_degree`.  General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)

variable {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]

/-- Boolean value embedding into `F`. -/
def bv (b : Bool) : F := if b then 1 else 0

theorem bv_not (b : Bool) : bv (!b) = 1 - bv (F := F) b := by cases b <;> simp [bv]

theorem bv_and (a b : Bool) : bv (a && b) = bv (F := F) a * bv b := by
  cases a <;> cases b <;> simp [bv]

theorem bv_or (a b : Bool) : bv (a || b) = bv (F := F) a + bv b - bv a * bv b := by
  cases a <;> cases b <;> simp only [bv] <;> norm_num

/-- A circuit with no `mod` gates (the `AC⁰` fragment). -/
def ModFree : ACC0Circuit n → Prop
  | .const _ => True
  | .var _ => True
  | .not c => ModFree c
  | .and a b => ModFree a ∧ ModFree b
  | .or a b => ModFree a ∧ ModFree b
  | .mod _ _ _ => False

/-- Faithful polynomial representation of the `AND`/`OR`/`NOT` fragment. -/
noncomputable def repr : ACC0Circuit n → MvPolynomial (Fin n) F
  | .const b => if b then 1 else 0
  | .var i => X i
  | .not c => 1 - repr c
  | .and a b => repr a * repr b
  | .or a b => repr a + repr b - repr a * repr b
  | .mod _ _ _ => 0

/-- The leaf-degree measure bounding `repr`'s total degree. -/
def reprDeg : ACC0Circuit n → ℕ
  | .const _ => 0
  | .var _ => 1
  | .not c => reprDeg c
  | .and a b => reprDeg a + reprDeg b
  | .or a b => reprDeg a + reprDeg b
  | .mod _ _ _ => 0

/-- **Faithfulness (PROVED): `repr` computes the circuit on Boolean inputs.** -/
theorem repr_eval (C : ACC0Circuit n) (x : Fin n → Bool) :
    ModFree C →
      eval (fun i => (bv (x i) : F)) (repr C) = bv (ACC0CircuitModel.eval C x) := by
  induction C with
  | const b => intro _; cases b <;> simp [repr, ACC0CircuitModel.eval, bv]
  | var i => intro _; simp [repr, ACC0CircuitModel.eval, bv]
  | not c ih =>
      intro h
      simp only [ModFree] at h
      simp only [repr, ACC0CircuitModel.eval, map_sub, map_one]
      rw [ih h, bv_not]
  | and a b iha ihb =>
      intro h
      simp only [ModFree] at h
      simp only [repr, ACC0CircuitModel.eval, map_mul]
      rw [iha h.1, ihb h.2, bv_and]
  | or a b iha ihb =>
      intro h
      simp only [ModFree] at h
      simp only [repr, ACC0CircuitModel.eval, map_sub, map_add, map_mul]
      rw [iha h.1, ihb h.2, bv_or]
  | mod q S t => intro h; simp only [ModFree] at h

/-- **Degree bound (PROVED): `repr C` has total degree at most the leaf measure.** -/
theorem repr_totalDegree_le (C : ACC0Circuit n) :
    (repr C : MvPolynomial (Fin n) F).totalDegree ≤ reprDeg C := by
  induction C with
  | const b => cases b <;> simp [repr, reprDeg]
  | var i => simp [repr, reprDeg, MvPolynomial.totalDegree_X]
  | not c ih =>
      simp only [repr, reprDeg]
      refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ih)
      rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _
  | and a b iha ihb =>
      simp only [repr, reprDeg]
      exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add iha ihb)
  | or a b iha ihb =>
      simp only [repr, reprDeg]
      refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
      · exact le_trans (MvPolynomial.totalDegree_add _ _)
          (max_le (le_trans iha (Nat.le_add_right _ _)) (le_trans ihb (Nat.le_add_left _ _)))
      · exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add iha ihb)
  | mod q S t => simp [repr, reprDeg]

/-!
**The mod-free model bridge, proved.**  Every `AC⁰` (mod-free) circuit is faithfully a polynomial (`repr_eval`) of degree
`≤` its leaf measure (`repr_totalDegree_le`) — the exact `circuit.eval = poly.eval` connection.  Remaining for general YBT
(open, not faked): `MOD` gates (RS / prime-power obstruction), quasipolynomial (approximate) degree, and the full
`composite_BT_degree`.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr.repr_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr.repr_totalDegree_le
