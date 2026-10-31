import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGuardedTwoKillChain

/-!
# Three-kill foundation: bit-mediation and gate-value substitution

Toward the three-kill step theorem.  Working the case analysis identifies the TRUE
guard — and it is not xor-factoring.  The `≤ 2`-kill escapes for a single `var i`
gate are exactly the **single-reader** circuits, where all of `xᵢ`'s influence flows
through one Boolean value `op (xᵢ, u)` — including mixed-row readers
(`op(0,·)` constant, `op(1,·) = id`), not only xor-type.  Hence:

* `BitMediated f i` — `f = H (op (xᵢ, u(x))) x` with `H`, `u` blind to `xᵢ`.
  **RETRACTION (see `ComputationalDepthThreeKillNoGo.lean`)**: this predicate is
  VACUOUS — every `f` bit-mediates at every `i` (`bitMediated_trivial`), so the
  guard `¬ BitMediated` proposed here is unsatisfiable, and moreover NO per-step
  semantic three-kill exists (`threekill_per_step_no_go`: `(x₀ ⊕ x₁) ∧ x₂`
  satisfies the two-kill guard and loses exactly two gates).  The definition is
  kept as the machine-checked record of the refuted design;
* `runFrom_gate_swap` / `output_gate_swap` — **PROVED**: replacing one gate by any
  gate of equal value at its position preserves the whole run — the primitive for
  extracting `H` from a single-reader circuit (freeze the mediating wire to `w`).

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- All of `xᵢ`'s influence on `f` flows through a single Boolean value: there are
`xᵢ`-blind `H`, `u` and a two-place op with `f x = H (op (x i) (u x)) x`.  This is
the semantic residue of a single-`var`, single-reader circuit — the exact family of
`≤ 2`-kill escapes once the two-kill guard holds. -/
def BitMediated {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ (H : Bool → (Fin n → Bool) → Bool) (op : Bool → Bool → Bool)
    (u : (Fin n → Bool) → Bool),
    (∀ x b, u (Function.update x i b) = u x) ∧
    (∀ w x b, H w (Function.update x i b) = H w x) ∧
    (∀ x, f x = H (op (x i) (u x)) x)

/-- **Gate-value substitution (proved)**: replacing one gate by any gate of equal
value at its position preserves the entire wire list. -/
theorem runFrom_gate_swap {n : ℕ} (x : Fin n → Bool) (c₁ : List (CGate n))
    (g₁ g₂ : CGate n) (c₂ : List (CGate n))
    (hval : evalGate x (runFrom x [] c₁) g₁ = evalGate x (runFrom x [] c₁) g₂) :
    runFrom x [] (c₁ ++ g₁ :: c₂) = runFrom x [] (c₁ ++ g₂ :: c₂) := by
  have h1 : runFrom x [] (c₁ ++ g₁ :: c₂)
      = runFrom x (runFrom x [] c₁ ++ [evalGate x (runFrom x [] c₁) g₁]) c₂ := by
    rw [show c₁ ++ g₁ :: c₂ = (c₁ ++ [g₁]) ++ c₂ by simp, runFrom_append, runFrom_append]
    rfl
  have h2 : runFrom x [] (c₁ ++ g₂ :: c₂)
      = runFrom x (runFrom x [] c₁ ++ [evalGate x (runFrom x [] c₁) g₂]) c₂ := by
    rw [show c₁ ++ g₂ :: c₂ = (c₁ ++ [g₂]) ++ c₂ by simp, runFrom_append, runFrom_append]
    rfl
  rw [h1, h2, hval]

/-- Output form of gate-value substitution. -/
theorem output_gate_swap {n : ℕ} (x : Fin n → Bool) (c₁ : List (CGate n))
    (g₁ g₂ : CGate n) (c₂ : List (CGate n))
    (hval : evalGate x (runFrom x [] c₁) g₁ = evalGate x (runFrom x [] c₁) g₂) :
    output (c₁ ++ g₁ :: c₂) x = output (c₁ ++ g₂ :: c₂) x := by
  show (runFrom x [] (c₁ ++ g₁ :: c₂)).getD ((c₁ ++ g₁ :: c₂).length - 1) false
    = (runFrom x [] (c₁ ++ g₂ :: c₂)).getD ((c₁ ++ g₂ :: c₂).length - 1) false
  rw [runFrom_gate_swap x c₁ g₁ g₂ c₂ hval,
    show (c₁ ++ g₁ :: c₂).length = (c₁ ++ g₂ :: c₂).length by simp]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.runFrom_gate_swap
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.output_gate_swap
