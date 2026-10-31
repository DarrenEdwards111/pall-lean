import Mathlib

/-!
# Step (2): the uniform charged gate language

Replaces the arbitrary function-field traces of the black-hole/MERA model with **finite syntax**:

* bounded-arity local gates (`input`, `not`, `and`, `xor`) acting on `w` Boolean wires;
* the `input i t` gate is the **only** source of input bits — the program description contains no input values;
* charged preparation: execution starts from the all-`false` wire state, and every action (loading an input bit,
  routing, evolution, ancilla use) is a gate, each costing `1` (`Prog.cost` = gate count);
* **no target-oracle gate**: every gate's semantics is fixed and independent of any target function, by
  construction of the inductive syntax.

The load-bearing theorem is the **anti-oracle-loading bound**: a program that never reads input bit `i` computes a
function independent of `i` (`run_update_of_not_read`), hence any program computing `f` pays at least the number of
input bits `f` depends on (`cost_ge_deps`).  The old model's `oracleLoadedTrace` — a one-step preparation that
delivers the target bit — is therefore **not representable**: delivering a target that depends on `≥ 2` input bits
requires an actual charged program of cost `≥ 2` (`no_answer_loading`); delivering the all-`AND` requires cost `≥ n`
(`andAll_cost`).  In this language, the target can only arrive by *computing it during the charged sequence*.

## Honest scope

This is the step-(2) language only.  The dependency bound is input-counting strength (**linear** — Shannon-style);
it kills oracle-loading but proves nothing superlinear.  The compiler (step 3), the dynamic invariant (step 4), and
the derived horizon laws (step 5) are separate builds; the SAT-forcing target (step 6) is separation-strength and
open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedGate

/-- The finite gate syntax: bounded arity, fixed semantics, no oracle gate. -/
inductive Gate (n w : ℕ)
  /-- `wire t := x i` — the ONLY source of input bits. -/
  | input (i : Fin n) (t : Fin w)
  /-- `wire t := ¬ wire a`. -/
  | notg (a t : Fin w)
  /-- `wire t := wire a ∧ wire b`. -/
  | andg (a b t : Fin w)
  /-- `wire t := wire a ⊕ wire b`. -/
  | xorg (a b t : Fin w)

/-- A charged program: a gate list and an output wire.  The description is independent of input values. -/
structure Prog (n w : ℕ) where
  /-- The charged gate sequence. -/
  gates : List (Gate n w)
  /-- The output wire. -/
  out : Fin w

variable {n w : ℕ}

/-- One charged step. -/
def step (x : Fin n → Bool) (s : Fin w → Bool) : Gate n w → (Fin w → Bool)
  | .input i t => Function.update s t (x i)
  | .notg a t => Function.update s t (! s a)
  | .andg a b t => Function.update s t (s a && s b)
  | .xorg a b t => Function.update s t (xor (s a) (s b))

/-- Sequential execution from a wire state. -/
def runGates (x : Fin n → Bool) (gs : List (Gate n w)) (s : Fin w → Bool) : Fin w → Bool :=
  gs.foldl (step x) s

/-- Charged run: from the all-`false` state (preparation is charged — no free initial data). -/
def Prog.run (P : Prog n w) (x : Fin n → Bool) : Bool :=
  runGates x P.gates (fun _ => false) P.out

/-- The charge: every gate costs `1`. -/
def Prog.cost (P : Prog n w) : ℕ := P.gates.length

/-- The input bit a gate reads, if any. -/
def Gate.readsInput : Gate n w → Option (Fin n)
  | .input i _ => some i
  | _ => none

/-- The set of input bits a program reads. -/
def Prog.inputsRead (P : Prog n w) : Finset (Fin n) :=
  (P.gates.filterMap Gate.readsInput).toFinset

/-- A program reads at most `cost` many input bits. -/
theorem inputsRead_card_le (P : Prog n w) : P.inputsRead.card ≤ P.cost :=
  le_trans (List.toFinset_card_le _) (List.length_filterMap_le _ _)

/-- A gate's action depends only on the input bits it reads. -/
theorem step_congr (x x' : Fin n → Bool) (s : Fin w → Bool) (g : Gate n w)
    (h : ∀ i, g.readsInput = some i → x i = x' i) : step x s g = step x' s g := by
  cases g with
  | input i t => rw [step, step, h i rfl]
  | notg a t => rfl
  | andg a b t => rfl
  | xorg a b t => rfl

/-- Execution depends only on the input bits read. -/
theorem runGates_congr (x x' : Fin n → Bool) (gs : List (Gate n w)) (s : Fin w → Bool)
    (h : ∀ i, (∃ g ∈ gs, Gate.readsInput g = some i) → x i = x' i) :
    runGates x gs s = runGates x' gs s := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    show runGates x gs (step x s g) = runGates x' gs (step x' s g)
    rw [step_congr x x' s g (fun i hg => h i ⟨g, List.mem_cons_self, hg⟩)]
    exact ih _ (fun i ⟨g', hg', hr⟩ => h i ⟨g', List.mem_cons_of_mem g hg', hr⟩)

/-- **The anti-oracle-loading core.**  A program that never reads input bit `i` computes a function independent
of `i`. -/
theorem run_update_of_not_read (P : Prog n w) (i : Fin n) (hi : i ∉ P.inputsRead)
    (x : Fin n → Bool) (b : Bool) : P.run (Function.update x i b) = P.run x := by
  unfold Prog.run
  rw [runGates_congr (Function.update x i b) x P.gates _ (fun j hj => ?_)]
  have hji : j ≠ i := by
    rintro rfl
    exact hi (List.mem_toFinset.mpr (List.mem_filterMap.mpr hj))
  rw [Function.update_of_ne hji]

/-- The input bits a function genuinely depends on. -/
noncomputable def deps (f : (Fin n → Bool) → Bool) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ x b, f (Function.update x i b) ≠ f x)

/-- Any program computing `f` reads every bit `f` depends on. -/
theorem deps_subset_inputsRead (P : Prog n w) (f : (Fin n → Bool) → Bool)
    (hP : ∀ x, P.run x = f x) : deps f ⊆ P.inputsRead := by
  classical
  intro i hi
  by_contra hnr
  simp only [deps, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨x, b, hne⟩ := hi
  exact hne (by rw [← hP, ← hP, run_update_of_not_read P i hnr])

/-- **The charged cost bound.**  Any program computing `f` pays at least the number of input bits `f` depends
on.  This is the theorem `oracleLoadedTrace` violated: in the charged language, the answer cannot be loaded — it
must be computed, reading the inputs gate by charged gate. -/
theorem cost_ge_deps (P : Prog n w) (f : (Fin n → Bool) → Bool) (hP : ∀ x, P.run x = f x) :
    (deps f).card ≤ P.cost :=
  le_trans (Finset.card_le_card (deps_subset_inputsRead P f hP)) (inputsRead_card_le P)

/-! ## The oracle-loading refutation, instantiated -/

/-- The all-`AND` target (any input-sensitive target works). -/
def andAll (x : Fin n → Bool) : Bool := decide (∀ i, x i)

/-- `andAll` depends on every input bit. -/
theorem deps_andAll : deps (andAll (n := n)) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro i
  simp only [deps, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun _ => true, false, ?_⟩
  have h1 : andAll (Function.update (fun _ => true) i false) = false := by
    apply decide_eq_false
    intro hall
    have := hall i
    rw [Function.update_self] at this
    exact Bool.false_ne_true this
  have h2 : andAll (fun _ : Fin n => true) = true := by
    apply decide_eq_true
    intro j
    rfl
  rw [h1, h2]
  exact Bool.false_ne_true

/-- Computing `andAll` costs at least `n` — the target must actually be computed. -/
theorem andAll_cost (P : Prog n w) (hP : ∀ x, P.run x = andAll x) : n ≤ P.cost := by
  have h := cost_ge_deps P andAll hP
  rw [deps_andAll, Finset.card_univ, Fintype.card_fin] at h
  exact h

/-- **`oracleLoadedTrace` is not representable.**  No cost-`≤ 1` program (a "one-step preparation") delivers an
input-sensitive target: the old model's answer-loading encoder does not exist in the charged language. -/
theorem no_answer_loading (hn : 2 ≤ n) :
    ¬ ∃ (w : ℕ) (P : Prog n w), P.cost ≤ 1 ∧ ∀ x, P.run x = andAll x := by
  rintro ⟨w, P, hcost, hP⟩
  have := andAll_cost P hP
  omega

end PallLean.Paper93.DeepMath.PathB.ChargedGate

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedGate.cost_ge_deps
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedGate.no_answer_loading
