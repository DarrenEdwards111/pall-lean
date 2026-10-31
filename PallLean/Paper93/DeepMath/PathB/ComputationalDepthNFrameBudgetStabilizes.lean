import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameJointBudget

/-!
# N-Frame: the GodMove limit is attained at finite dimension

Book1's language casts the GodMove as the *idealized infinite-dimensional observer* — the limit of the finite-observer
hierarchy as the boundary-dimension constraint is relaxed without bound.  This file proves that in the finite Boolean
setting that limit is **attained at a finite index**: the joint budget `budgetAt w f` stabilizes to the unconstrained
energy `budget f` as soon as `w ≥ budget f`.  The idealized observer is not an infinite object or an axiom — it is the
eventual value of the finite budget curve, reached at a dimension no larger than the optimum's own energy.

  `width_le_volume` — **PROVED, the key inequality**: a boundary observer's dimension never exceeds its energy.
  `budgetAt_stabilizes` — **PROVED**: for all `w ≥ budget f`, `budgetAt w f = budget f` — the budget curve is eventually
        constant at the unconstrained optimum.
  `exists_godMove_free` — **PROVED**: the unconstrained GodMove exists with finite dimension: an optimal representation
        attaining `budget f` whose width is at most `budget f` itself.

So the observer hierarchy is exact and finite end-to-end: `budgetAt · f` is a (weakly) decreasing curve in the dimension
budget, constant from `w = budget f` onward, with the "GodMove observer" as its eventual value — Darren's limit-object
reading, formalized with nothing infinite and nothing assumed.

## Honest scope

This closes the *structure* of the dimension–energy trade-off curve (well-defined, eventually constant, optimum attained,
optimum's dimension self-bounded).  It says nothing about the curve's *height* on hard functions beyond the proven
Nečiporuk tearing — the super-polynomial questions remain exactly as named in the identity and circuit-upgrade files.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-- **Dimension never exceeds energy (proved)**: `width t ≤ volume t` for every boundary observer. -/
theorem width_le_volume (t : Trans n) : width t ≤ volume t := by
  induction t with
  | var i => simp [width, volume]
  | cst b => simp [width, volume]
  | un op t ih => simp only [width, volume]; omega
  | bin op t₁ t₂ ih₁ ih₂ => simp only [width, volume]; split <;> omega

/-- **The stabilization theorem (proved)**: the joint budget curve is constant at the unconstrained optimum from
`w = budget f` onward.  The GodMove limit — the idealized unbounded-dimension observer — is attained at this finite
index. -/
theorem budgetAt_stabilizes (f : (Fin n → Bool) → Bool) {w : ℕ} (hw : budget f ≤ w) :
    budgetAt w f = budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  -- the unconstrained minimizer …
  have hmem := Nat.sInf_mem hne
  obtain ⟨t, he, hv⟩ := hmem
  -- … has dimension within the budget `w`
  have hwidth : width t ≤ w := by
    have h1 : width t ≤ volume t := width_le_volume t
    have h2 : volume t = budget f := hv
    omega
  refine le_antisymm ?_ (budget_le_budgetAt w ⟨t, he, hwidth⟩)
  calc budgetAt w f ≤ volume t := Nat.sInf_le ⟨t, he, hwidth, rfl⟩
    _ = budget f := hv

/-- **The unconstrained GodMove, with finite dimension (proved)**: an optimal boundary representation attaining
`budget f` whose dimension is at most its own energy.  The "infinite-dimensional ideal observer" is realized by a finite
object whose dimension is self-bounded. -/
theorem exists_godMove_free (f : (Fin n → Bool) → Bool) :
    ∃ t : Trans n, eval t = f ∧ volume t = budget f ∧ width t ≤ budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  unfold budget
  obtain ⟨t, he, hv⟩ := Nat.sInf_mem hne
  refine ⟨t, he, hv, ?_⟩
  rw [← hv]
  exact width_le_volume t

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.width_le_volume
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budgetAt_stabilizes
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.exists_godMove_free
