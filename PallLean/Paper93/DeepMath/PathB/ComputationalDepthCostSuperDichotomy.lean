import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade

/-!
# Why `cost_super` is a wall: the linear/nonlinear two-horn dichotomy, machine-checked

The whole NP-ceiling route (`SuperAdditiveComposition`) reduces `P ≠ NP` to a single open field
`cost_super : ∀ d, 2·cost d ≤ cost (d+1)` — that composing SAT's codec with itself at least *doubles*
circuit cost.  In the straight-line `CGate` model (gates read earlier wires — sharing allowed), this
is not a lemma one can grind: sharing across the two copies is exactly the Uhlig phenomenon.  This
file does not fake the doubling.  Instead it **machine-checks the structure of the wall**: it proves
`cost_super` follows from *exactly two* named sub-bounds, one per horn, and that the horns are
**exhaustive** over all circuits.

The split is anchored in the real gate model.  A binary op `op : Bool → Bool → Bool` is **affine**
(GF(2) degree `≤ 1`) iff its ANF quadratic coefficient vanishes,
`op₀₀ ⊕ op₀₁ ⊕ op₁₀ ⊕ op₁₁ = false`.  Every unary/var/const gate is affine; a binary gate is affine
iff its op is.  A circuit is `AffineMixed` iff every gate is affine — i.e. it is a GF(2)-**linear**
circuit, the regime where lower bounds are the **matrix-rigidity / Valiant** program.  A circuit with
a nonlinear gate is the **Uhlig-sharing** regime.

* **`isAffineOp_xor` / `not_isAffineOp_and` (proved)** — the classification is non-vacuous: `XOR` is
  affine, `AND` is not.
* **`lb_from_horns` (proved)** — the dichotomy + reduction: if the linear horn bounds every
  affine-mixed circuit for `f` and the nonlinear horn bounds every non-affine-mixed one, then
  `t ≤ cbudget f`.  Exhaustive case split on `AffineMixed c`, lower-bounding `sInf`.
* **`tower_field_from_horns` (proved)** — plugging the reduction into the tower: both horns at every
  level (at threshold `2·cost d` for the level-composite) give exactly the tower's open field
  `∀ d, 2·cost d ≤ cost (d+1)` = `cost_super`.

**Honest scope.**  Proved here: the classification, the exhaustive dichotomy, and the reduction
`(linear horn) ∧ (nonlinear horn) ⟹ cost_super`.  **Not** proved: either horn — `LinearHorn` is a
rigidity lower bound for GF(2)-linear circuits computing the composite (Valiant's open problem),
`NonlinearHorn` is an Uhlig-style no-sharing bound (also open).  This is the precise, machine-checked
statement of *why* `cost_super` is a wall: it is the conjunction of two named classical open bounds,
covering all circuits.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### Classifying gates: affine (GF(2) degree ≤ 1) vs nonlinear -/

/-- A binary op is **affine** iff its ANF quadratic coefficient vanishes:
`op₀₀ ⊕ op₀₁ ⊕ op₁₀ ⊕ op₁₁ = false`.  The affine 2-bit functions are exactly
`{0,1,a,b,¬a,¬b,a⊕b,a⊕b⊕1}`; the other eight (`AND`/`OR` and variants) are nonlinear. -/
def IsAffineOp (op : Bool → Bool → Bool) : Prop :=
  Bool.xor (Bool.xor (op false false) (op false true)) (Bool.xor (op true false) (op true true))
    = false

/-- `XOR` is affine (the classification is non-vacuous). -/
theorem isAffineOp_xor : IsAffineOp (fun a b => Bool.xor a b) := by
  unfold IsAffineOp; decide

/-- `AND` is **not** affine — the nonlinear witness. -/
theorem not_isAffineOp_and : ¬ IsAffineOp (fun a b => a && b) := by
  unfold IsAffineOp; decide

/-- A gate is **affine** if it is a variable, a constant, any unary op (all `1`-bit functions have
GF(2) degree `≤ 1`), or a binary op whose `op` is affine. -/
def IsAffineGate : CGate n → Prop
  | .var _ => True
  | .cst _ => True
  | .un _ _ => True
  | .bin op _ _ => IsAffineOp op

/-- A circuit is **affine-mixed** iff every gate is affine — i.e. it is a GF(2)-linear circuit, the
matrix-rigidity / Valiant regime. -/
def AffineMixed (c : List (CGate n)) : Prop := ∀ g ∈ c, IsAffineGate g

/-! ### The dichotomy and the reduction -/

/-- **The two-horn dichotomy + reduction (proved).**  Fix a target `f` (circuit-computable, `hcomp`)
and a threshold `t`.  If the **linear horn** bounds every affine-mixed circuit computing `f`
(`t ≤ length`) and the **nonlinear horn** bounds every non-affine-mixed one, then `t ≤ cbudget f`.
Every circuit is affine-mixed or not, so the two horns cover all circuits; each is then a lower bound
on the whole `cbudget` `sInf`. -/
theorem lb_from_horns (f : (Fin n → Bool) → Bool) (t : ℕ)
    (hcomp : ∃ c : List (CGate n), computes c f)
    (linHorn : ∀ c : List (CGate n), computes c f → AffineMixed c → t ≤ c.length)
    (nonlinHorn : ∀ c : List (CGate n), computes c f → ¬ AffineMixed c → t ≤ c.length) :
    t ≤ cbudget f := by
  classical
  obtain ⟨c0, hc0⟩ := hcomp
  unfold cbudget
  apply le_csInf
  · exact ⟨c0.length, c0, hc0, rfl⟩
  · rintro s ⟨c, hc, rfl⟩
    by_cases h : AffineMixed c
    · exact linHorn c hc h
    · exact nonlinHorn c hc h

/-- **`cost_super` from the two horns (proved).**  If, at every level `d`, both horns hold for the
level-composite `composite d` at threshold `2·cost d`, and the composite's `cbudget` realizes
`cost (d+1)`, then the tower's open field `∀ d, 2·cost d ≤ cost (d+1)` holds.  This is exactly
`SuperAdditiveTower.cost_super`, exhibited as the conjunction of the two named horns. -/
theorem tower_field_from_horns {arity cost : ℕ → ℕ}
    (composite : (d : ℕ) → (Fin (arity (d + 1)) → Bool) → Bool)
    (hcomp : ∀ d, ∃ c : List (CGate (arity (d + 1))), computes c (composite d))
    (linHorn : ∀ d (c : List (CGate (arity (d + 1)))),
      computes c (composite d) → AffineMixed c → 2 * cost d ≤ c.length)
    (nonlinHorn : ∀ d (c : List (CGate (arity (d + 1)))),
      computes c (composite d) → ¬ AffineMixed c → 2 * cost d ≤ c.length)
    (hrel : ∀ d, cbudget (composite d) ≤ cost (d + 1)) :
    ∀ d, 2 * cost d ≤ cost (d + 1) := by
  intro d
  exact le_trans (lb_from_horns (composite d) (2 * cost d) (hcomp d) (linHorn d) (nonlinHorn d))
    (hrel d)

end PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy

#print axioms PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy.isAffineOp_xor
#print axioms PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy.not_isAffineOp_and
#print axioms PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy.lb_from_horns
#print axioms PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy.tower_field_from_horns
