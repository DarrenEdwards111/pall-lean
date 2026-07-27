import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFixedPointSlotTwo

/-!
# Using SAT's Tseitin self-encoding to force the fixed point — structure yes, diagonalization no

The last request: use SAT's Tseitin self-encoding (SAT expresses circuit evaluation) to force
`Diagonalizes f sat` — that SAT *is* the self-referential fixed point.  If that were provable, it would
be `P ≠ NP`.  It is not proved here.  What is built is the honest anatomy of why the self-encoding
provides the *structure* but not the *diagonalization*.

## The self-encoding is the right structural ingredient

Tseitin gives SAT a **self-referential structure**: SAT can *reference* every circuit (encode "circuit
`i` evaluates to true").  A random truth table cannot do this — which is exactly why SAT, not a coin
flip, is the fixed-point candidate.  `SelfEncoding` models this reference map.  This is real, and it is
what grounds the rare/self-referential slot.

## But it does not force the fixed point — the diagonalization IS the lower bound

Being the fixed point means SAT *disagrees* with circuit `f i` at index `i` for every `i`.  Two proved
facts show the self-encoding cannot supply that:

* **`correct_circuit_blocks_diagonal`** — if an enumerated circuit `f i` *correctly computes* SAT
  (`f i = sat`), then SAT *agrees* with it at `i` (`sat i = f i i`), so it does NOT disagree there.  A
  correct circuit blocks the diagonal outright.
* **`diagonal_requires_lower_bound`** — therefore `Diagonalizes f sat` *requires* that no enumerated
  circuit computes SAT — which is the circuit lower bound itself.  The fixed point for SAT *contains*
  the lower bound; it is not weaker than it.

And `expressibility_does_not_force_fixedpoint` exhibits a self-encodable SAT with a correct circuit that
is therefore *not* the fixed point: expressibility (behavior at encoded instances) is orthogonal to
diagonalization (disagreement at the diagonal index).

## Honest verdict

Tseitin self-encoding supplies the self-referential *structure* — the reason SAT is the candidate — but
forcing the fixed point would require SAT to disagree with every circuit at the diagonal, which *is*
`SAT ∉ (circuit class)` = `cost_super`, and which any correct circuit blocks.  So the self-encoding
gets you the structure and not one inch of the diagonalization.  The gap between "SAT expresses
circuits" (Tseitin, true) and "SAT diagonalizes against circuits" (the fixed point) is exactly the
wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinForceFixedPoint

open PallLean.Paper93.DeepMath.PathB.FixedPointSlotTwo

/-- **A correct circuit blocks the diagonal (proved).**  If enumerated circuit `f i` computes SAT
(`f i = sat`), then SAT agrees with it at `i` — so `sat i = !(f i i)` is false.  Being the fixed point
fails against any correct circuit. -/
theorem correct_circuit_blocks_diagonal {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool)
    (sat : Fin (m + 1) → Bool) (i : Fin (m + 1)) (hc : f i = sat) :
    ¬ (sat i = !(f i i)) := by
  rw [hc]
  cases sat i <;> decide

/-- **The fixed point for SAT requires the lower bound (proved).**  `Diagonalizes f sat` forces that no
enumerated circuit computes SAT — the circuit lower bound.  So the self-encoding cannot force the fixed
point for free: forcing it would force the lower bound (`cost_super`). -/
theorem diagonal_requires_lower_bound {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool)
    (sat : Fin (m + 1) → Bool) (h : Diagonalizes f sat) : ∀ i, f i ≠ sat := by
  intro i hc
  exact correct_circuit_blocks_diagonal f sat i hc (h i)

/-- **The Tseitin self-encoding (structure).**  SAT references each circuit via an encoding map — the
self-referential structure a random function lacks.  (Abstract: `enc i` is the SAT-instance dedicated
to circuit `i`.) -/
structure SelfEncoding (n : ℕ) where
  enc : Fin n → Fin n

/-- **Expressibility does not force the fixed point (proved).**  A self-encodable SAT can have a correct
circuit — and then it is NOT the fixed point.  Expressibility (behavior at encoded instances) is
orthogonal to diagonalization (disagreement at the diagonal index). -/
theorem expressibility_does_not_force_fixedpoint :
    ∃ (sat : Fin 1 → Bool) (f : Fin 1 → Fin 1 → Bool) (_E : SelfEncoding 1),
      f 0 = sat ∧ ¬ Diagonalizes f sat := by
  refine ⟨fun _ => true, fun _ _ => true, ⟨id⟩, rfl, ?_⟩
  intro h
  exact absurd (h 0) (by decide)

end PallLean.Paper93.DeepMath.PathB.TseitinForceFixedPoint

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinForceFixedPoint.correct_circuit_blocks_diagonal
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinForceFixedPoint.diagonal_requires_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinForceFixedPoint.expressibility_does_not_force_fixedpoint
