import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameW2YaoBrick2

/-!
# N-Frame: Yao bricks 3 — the output normal form (last-activation decomposition)

The counting argument needs to know *what the output can depend on*.  This brick proves the canonical decomposition
every width-2 lower-bound argument starts from:

  `last_active_split` — **PROVED**: on any input, either no step activates, or the program splits as
        `p₁ ++ s :: p₂` with `s` the **last** active step and the suffix `p₂` all-passive.
  `w2run_after_active` — **PROVED**: across such a split the output is `c_s(x_{v_s}) ⊕ progPar p₂ x` — the prefix `p₁`
        and the initial register are *erased*; only the last activation's constant and the suffix parity survive.
  `w2run_normal_form` — **PROVED, the normal form**: every output is either `r₀ ⊕ progPar p x` (all-passive regime) or
        `c_s(x_{v_s}) ⊕ progPar p₂ x` (last-activation regime) — on each regime class a **fixed affine function** of the
        input, with at most `length + 1` classes.

## Honest scope — a negative finding, and where the open heart actually is

A tempting corollary — "`f` needs many affine pieces, so programs must be long" — is **provably vacuous**: the two
constant functions cover *any* `f` in the piece-agreement sense, so unstructured affine-cover counting can never exceed
a constant.  The real content of Yao's argument is therefore *not* the affine cover but **which inputs land in which
class**: as the input moves along a monotone path crossing majority's threshold, the last-activation class must change,
and the fixed read order makes those changes chargeable to distinct steps.  Formalizing that charging argument — the
threshold-crossing count — is the remaining open heart of Y3; nothing here claims it.  This brick supplies the normal
form it will consume.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-- **The last-activation split (proved)**: either all steps are passive on `x`, or the program splits at its last
active step with an all-passive suffix. -/
theorem last_active_split (p : W2Prog n) (x : Fin n → Bool) :
    (∀ s ∈ p, ¬ stepActive s x) ∨
    ∃ (p₁ : W2Prog n) (s : (Bool → Bool → Bool) × Fin n) (p₂ : W2Prog n),
      p = p₁ ++ s :: p₂ ∧ stepActive s x ∧ ∀ s' ∈ p₂, ¬ stepActive s' x := by
  induction p with
  | nil =>
    left
    intro s hs
    exact absurd hs List.not_mem_nil
  | cons a t ih =>
    rcases ih with hall | ⟨p₁, s, p₂, heq, hact, hpass⟩
    · by_cases ha : stepActive a x
      · right
        exact ⟨[], a, t, rfl, ha, hall⟩
      · left
        intro s hs
        rcases List.mem_cons.mp hs with h | h
        · exact h ▸ ha
        · exact hall s h
    · right
      exact ⟨a :: p₁, s, p₂, by rw [heq]; rfl, hact, hpass⟩

/-- **Erasure across the last activation (proved)**: the output is the activation constant XOR the suffix parity — the
prefix and the initial register are gone. -/
theorem w2run_after_active (p₁ : W2Prog n) (s : (Bool → Bool → Bool) × Fin n) (p₂ : W2Prog n)
    (x : Fin n → Bool) (hact : stepActive s x) (hpass : ∀ s' ∈ p₂, ¬ stepActive s' x)
    (r0 : Bool) :
    w2run (p₁ ++ s :: p₂) r0 x = xor (s.1 false (x s.2)) (progPar p₂ x) := by
  have hconst : ∀ r, s.1 r (x s.2) = s.1 false (x s.2) := by
    intro r
    cases r
    · rfl
    · exact hact.symm
  rw [w2run_append]
  show w2run p₂ (s.1 (w2run p₁ r0 x) (x s.2)) x = _
  rw [hconst (w2run p₁ r0 x)]
  exact w2run_allPassive p₂ x hpass _

/-- **THE OUTPUT NORMAL FORM (proved)**: every output is either the all-passive affine value `r₀ ⊕ progPar p x`, or the
last-activation value `c_s(x_{v_s}) ⊕ progPar p₂ x` for the split at the last active step.  On each regime class the
program agrees with a fixed affine function; there are at most `length + 1` classes. -/
theorem w2run_normal_form (p : W2Prog n) (x : Fin n → Bool) (r0 : Bool) :
    ((∀ s ∈ p, ¬ stepActive s x) ∧ w2run p r0 x = xor r0 (progPar p x)) ∨
    ∃ (p₁ : W2Prog n) (s : (Bool → Bool → Bool) × Fin n) (p₂ : W2Prog n),
      p = p₁ ++ s :: p₂ ∧ stepActive s x ∧ (∀ s' ∈ p₂, ¬ stepActive s' x) ∧
      w2run p r0 x = xor (s.1 false (x s.2)) (progPar p₂ x) := by
  rcases last_active_split p x with hall | ⟨p₁, s, p₂, heq, hact, hpass⟩
  · exact Or.inl ⟨hall, w2run_allPassive p x hall r0⟩
  · refine Or.inr ⟨p₁, s, p₂, heq, hact, hpass, ?_⟩
    rw [heq]
    exact w2run_after_active p₁ s p₂ x hact hpass r0

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.last_active_split
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.w2run_after_active
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.w2run_normal_form
