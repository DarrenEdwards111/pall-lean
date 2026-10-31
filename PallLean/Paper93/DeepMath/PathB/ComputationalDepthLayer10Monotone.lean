import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7CircuitFamily

/-!
# Layer 10C — the monotone circuit model and its structural lower bound

The honest "10C" rung: a **known result in a restricted model** the monotone-circuit setting the
frontier note flagged as promising.  We build the monotone circuit model and prove its foundational
structural theorem — **monotone circuits compute only monotone functions** — and deduce that explicit
*non-monotone* functions (`¬x₀`, PARITY) have **no** monotone circuit at all.

* `MCircuit` / `eval` / `size` — the monotone model (`input / const / ∧ / ∨`, no negation).
* `eval_monotone` / `MonotoneFn` / `mcircuit_eval_monotone` — monotone circuits are monotone.
* `not_mcircuit_of_not_monotone` — a non-monotone function has no monotone circuit.
* `no_mcircuit_computes_notFirst`, `no_mcircuit_computes_parity` — explicit instances: `¬x₀` and PARITY
  (`n ≥ 2`) are not monotone-computable.  Hence **monotone circuits ⊊ general circuits**.

**Honest status.**  This is a *qualitative* separation (the monotone model is strictly weaker — negation
is genuinely needed), via the clean structural theorem.  It is **not** a *quantitative* size lower bound
for a function that *is* monotone — the famous strong monotone bounds (Razborov's exponential CLIQUE
bound via the approximation method) are a separate, large formalization, **not** attempted here.  This is
the achievable, sorry-free floor of monotone circuit complexity; it makes no progress toward `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer10

open Finset

/-- A **monotone circuit**: `input / const / ∧ / ∨`, with no negation. -/
inductive MCircuit (n : ℕ) : Type
  | input : Fin n → MCircuit n
  | const : Bool → MCircuit n
  | and : MCircuit n → MCircuit n → MCircuit n
  | or : MCircuit n → MCircuit n → MCircuit n

namespace MCircuit

/-- Evaluation of a monotone circuit. -/
def eval {n : ℕ} : MCircuit n → (Fin n → Bool) → Bool
  | input i, x => x i
  | const b, _ => b
  | and c d, x => c.eval x && d.eval x
  | or c d, x => c.eval x || d.eval x

/-- Monotone-circuit size (number of gates/leaves). -/
def size {n : ℕ} : MCircuit n → ℕ
  | input _ => 1
  | const _ => 1
  | and c d => c.size + d.size + 1
  | or c d => c.size + d.size + 1

private theorem band_mono {a b c d : Bool} (h1 : a ≤ b) (h2 : c ≤ d) : (a && c) ≤ (b && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem bor_mono {a b c d : Bool} (h1 : a ≤ b) (h2 : c ≤ d) : (a || c) ≤ (b || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- Monotone circuits are **monotone**: `x ≤ y ⇒ eval x ≤ eval y`. -/
theorem eval_monotone {n : ℕ} (c : MCircuit n) {x y : Fin n → Bool} (h : x ≤ y) :
    c.eval x ≤ c.eval y := by
  induction c with
  | input i => exact h i
  | const b => exact le_refl b
  | and c d ihc ihd => exact band_mono ihc ihd
  | or c d ihc ihd => exact bor_mono ihc ihd

end MCircuit

/-- A boolean function is **monotone**. -/
def MonotoneFn {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∀ x y, x ≤ y → f x ≤ f y

/-- The function computed by a monotone circuit is monotone. -/
theorem mcircuit_eval_monotone {n : ℕ} (c : MCircuit n) : MonotoneFn c.eval :=
  fun _ _ h => c.eval_monotone h

/-- **No monotone circuit computes a non-monotone function.** -/
theorem not_mcircuit_of_not_monotone {n : ℕ} (f : (Fin n → Bool) → Bool) (hf : ¬ MonotoneFn f) :
    ¬ ∃ c : MCircuit n, ∀ x, c.eval x = f x := by
  rintro ⟨c, hc⟩
  refine hf (fun x y hxy => ?_)
  rw [← hc x, ← hc y]; exact c.eval_monotone hxy

/-- The (non-monotone) function `¬ x₀`. -/
def notFirst (n : ℕ) (h : 0 < n) : (Fin n → Bool) → Bool := fun x => !(x ⟨0, h⟩)

theorem notFirst_not_monotone {n : ℕ} (h : 0 < n) : ¬ MonotoneFn (notFirst n h) := by
  intro hmono
  have hle : (fun _ => false : Fin n → Bool) ≤ (fun _ => true) := fun i => by simp
  have hcmp := hmono _ _ hle
  have hv1 : notFirst n h (fun _ => false) = true := by simp [notFirst]
  have hv2 : notFirst n h (fun _ => true) = false := by simp [notFirst]
  rw [hv1, hv2] at hcmp
  exact absurd hcmp (by decide)

/-- **Negation needs a non-monotone gate:** no monotone circuit computes `¬ x₀`. -/
theorem no_mcircuit_computes_notFirst {n : ℕ} (h : 0 < n) :
    ¬ ∃ c : MCircuit n, ∀ x, c.eval x = notFirst n h x :=
  not_mcircuit_of_not_monotone _ (notFirst_not_monotone h)

/-- The PARITY function. -/
def parityFn (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x => decide (Odd (Finset.univ.filter (fun i => x i = true)).card)

theorem parityFn_not_monotone {n : ℕ} (hn : 2 ≤ n) : ¬ MonotoneFn (parityFn n) := by
  intro hmono
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set x : Fin n → Bool := fun i => decide (i = i0) with hx
  set y : Fin n → Bool := fun i => decide (i = i0 ∨ i = i1) with hy
  have hxy : x ≤ y := by intro i; simp only [hx, hy]; by_cases h : i = i0 <;> simp [h]
  have hi01 : i0 ≠ i1 := by rw [hi0, hi1]; simp [Fin.ext_iff]
  have hcardx : (Finset.univ.filter (fun i => x i = true)).card = 1 := by
    have : Finset.univ.filter (fun i => x i = true) = {i0} := by ext i; simp [hx]
    rw [this, Finset.card_singleton]
  have hcardy : (Finset.univ.filter (fun i => y i = true)).card = 2 := by
    have : Finset.univ.filter (fun i => y i = true) = {i0, i1} := by ext i; simp [hy]
    rw [this, Finset.card_pair hi01]
  have hpx : parityFn n x = true := by simp only [parityFn, hcardx]; decide
  have hpy : parityFn n y = false := by simp only [parityFn, hcardy]; decide
  have hcmp := hmono x y hxy
  rw [hpx, hpy] at hcmp
  exact absurd hcmp (by decide)

/-- **PARITY is not monotone-computable:** no monotone circuit computes PARITY (`n ≥ 2`).  Together with
`no_mcircuit_computes_notFirst`, this witnesses **monotone circuits ⊊ general circuits**. -/
theorem no_mcircuit_computes_parity {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ c : MCircuit n, ∀ x, c.eval x = parityFn n x :=
  not_mcircuit_of_not_monotone _ (parityFn_not_monotone hn)

end PallLean.Paper93.DeepMath.PathB.Layer10

#print axioms PallLean.Paper93.DeepMath.PathB.Layer10.mcircuit_eval_monotone
#print axioms PallLean.Paper93.DeepMath.PathB.Layer10.no_mcircuit_computes_parity
