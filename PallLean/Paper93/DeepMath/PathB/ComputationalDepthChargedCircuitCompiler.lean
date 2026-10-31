import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedGateLanguage

/-!
# Step (3), general half: the circuit compiler

Compiles **every** bounded-fan-in Boolean circuit (the inductive tree type `BForm`: variables, NOT, AND, XOR —
a complete basis) into the charged gate language, with:

* **semantic correctness** — `(compile f).run z = f.eval z` for all inputs (`compile_correct`);
* **uniformity** — `compile` is a syntactic function of the circuit description alone; the program never depends
  on input values (by construction: it is a `def` from `BForm`);
* **overhead exactly one** — `(compile f).cost = f.size`, one charged gate per circuit node (`compile_cost`),
  and wire count `stackS f ≤ f.size` (`compile_wires`) — better than the polynomial overhead required;
* **exact decoding** — the value sits on the output wire; no decoder needed.

The scheme is a stack machine: `compile' f d` leaves `f.eval z` on wire `d` using only wires `≥ d` as scratch
(`compile_spec`: wire `d` receives the value, wires `< d` are untouched), so a binary node evaluates its left
child on `d`, its right child on `d + 1`, and combines.  The required stack height `stackS f` (`max` over the
tree) is the wire budget.

Together with the calibrations (`ChargedCompiler`) this completes step (3): the charged language simulates all
circuits at cost = size, so every polynomial-size circuit family has polynomial charged dynamic cost — while the
static all-order MPS cost of `QF A` stays exponential.  The dynamic/static split stands on general ground.

## Honest scope

Tree circuits (formulas); DAG sharing is not needed for this statement.  A compiler, not a lower bound: nothing
here bounds anything below.  The SAT-forcing target (step 6) remains separation-strength and open.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedCircuit

open PallLean.Paper93.DeepMath.PathB.ChargedGate

variable {n w : ℕ}

/-- Bounded-fan-in Boolean circuits (tree form; `{¬, ∧, ⊕}` with variables is a complete basis —
`a ∨ b = ¬(¬a ∧ ¬b)`). -/
inductive BForm (n : ℕ)
  /-- An input variable. -/
  | var (i : Fin n)
  /-- Negation. -/
  | notf (f : BForm n)
  /-- Conjunction. -/
  | andf (f g : BForm n)
  /-- Exclusive or. -/
  | xorf (f g : BForm n)

/-- Circuit semantics. -/
def BForm.eval (z : Fin n → Bool) : BForm n → Bool
  | .var i => z i
  | .notf f => ! f.eval z
  | .andf f g => f.eval z && g.eval z
  | .xorf f g => xor (f.eval z) (g.eval z)

/-- Circuit size (node count). -/
def BForm.size : BForm n → ℕ
  | .var _ => 1
  | .notf f => f.size + 1
  | .andf f g => f.size + g.size + 1
  | .xorf f g => f.size + g.size + 1

/-- Required stack height (wire budget). -/
def stackS : BForm n → ℕ
  | .var _ => 1
  | .notf f => stackS f
  | .andf f g => max (stackS f) (stackS g + 1)
  | .xorf f g => max (stackS f) (stackS g + 1)

theorem one_le_stackS (f : BForm n) : 1 ≤ stackS f := by
  induction f with
  | var i => exact le_refl 1
  | notf f ih => exact ih
  | andf f g ihf ihg => exact le_trans ihf (le_max_left _ _)
  | xorf f g ihf ihg => exact le_trans ihf (le_max_left _ _)

theorem stackS_le_size (f : BForm n) : stackS f ≤ f.size := by
  induction f with
  | var i => exact le_refl 1
  | notf f ih => rw [stackS, BForm.size]; omega
  | andf f g ihf ihg =>
    rw [stackS, BForm.size]
    have := one_le_stackS f
    have := one_le_stackS g
    omega
  | xorf f g ihf ihg =>
    rw [stackS, BForm.size]
    have := one_le_stackS f
    have := one_le_stackS g
    omega

/-- The stack-machine compiler: leaves `f.eval z` on wire `d`, scratch on wires `> d`. -/
def compile' (w : ℕ) : (f : BForm n) → (d : ℕ) → (d + stackS f ≤ w) → List (Gate n w)
  | .var i, d, h =>
    have h' : d + 1 ≤ w := h
    [.input i ⟨d, by omega⟩]
  | .notf f, d, h =>
    have h' : d + stackS f ≤ w := h
    have hd : d < w := by have := one_le_stackS f; omega
    compile' w f d h' ++ [.notg ⟨d, hd⟩ ⟨d, hd⟩]
  | .andf f g, d, h =>
    have h' : d + max (stackS f) (stackS g + 1) ≤ w := h
    have hmf := le_max_left (stackS f) (stackS g + 1)
    have hmg := le_max_right (stackS f) (stackS g + 1)
    have hgd : d + 1 + stackS g ≤ w := by omega
    have hd : d < w := by have := one_le_stackS g; omega
    have hd1 : d + 1 < w := by have := one_le_stackS g; omega
    compile' w f d (by omega) ++ compile' w g (d + 1) hgd
      ++ [.andg ⟨d, hd⟩ ⟨d + 1, hd1⟩ ⟨d, hd⟩]
  | .xorf f g, d, h =>
    have h' : d + max (stackS f) (stackS g + 1) ≤ w := h
    have hmf := le_max_left (stackS f) (stackS g + 1)
    have hmg := le_max_right (stackS f) (stackS g + 1)
    have hgd : d + 1 + stackS g ≤ w := by omega
    have hd : d < w := by have := one_le_stackS g; omega
    have hd1 : d + 1 < w := by have := one_le_stackS g; omega
    compile' w f d (by omega) ++ compile' w g (d + 1) hgd
      ++ [.xorg ⟨d, hd⟩ ⟨d + 1, hd1⟩ ⟨d, hd⟩]

/-- Sequential execution splits over append (general wire count). -/
theorem runGates_append' (z : Fin n → Bool) (l1 l2 : List (Gate n w)) (s : Fin w → Bool) :
    runGates z (l1 ++ l2) s = runGates z l2 (runGates z l1 s) :=
  List.foldl_append

/-- **The compiler invariant**: wire `d` receives `f.eval z`; wires below `d` are untouched. -/
theorem compile_spec (z : Fin n → Bool) (f : BForm n) :
    ∀ (d : ℕ) (h : d + stackS f ≤ w) (hd : d < w) (s : Fin w → Bool),
      (runGates z (compile' w f d h) s) ⟨d, hd⟩ = f.eval z
      ∧ ∀ j : Fin w, j.val < d → (runGates z (compile' w f d h) s) j = s j := by
  induction f with
  | var i =>
    intro d h hd s
    constructor
    · show (Function.update s ⟨d, hd⟩ (z i)) ⟨d, hd⟩ = z i
      exact Function.update_self ..
    · intro j hj
      show (Function.update s ⟨d, hd⟩ (z i)) j = s j
      exact Function.update_of_ne (Fin.ne_of_val_ne (show j.val ≠ d by omega)) _ _
  | notf f ih =>
    intro d h hd s
    have h' : d + stackS f ≤ w := h
    obtain ⟨ih1, ih2⟩ := ih d h' hd s
    have hsplit : ∀ j : Fin w, (runGates z (compile' w (.notf f) d h) s) j
        = (Function.update (runGates z (compile' w f d h') s) ⟨d, hd⟩
            (! (runGates z (compile' w f d h') s) ⟨d, hd⟩)) j := by
      intro j
      show (runGates z (compile' w f d h' ++ [.notg ⟨d, hd⟩ ⟨d, hd⟩]) s) j = _
      rw [runGates_append']
      rfl
    constructor
    · rw [hsplit, Function.update_self, ih1]
      rfl
    · intro j hj
      rw [hsplit, Function.update_of_ne (Fin.ne_of_val_ne (show j.val ≠ d by omega)), ih2 j hj]
  | andf f g ihf ihg =>
    intro d h hd s
    have h' : d + max (stackS f) (stackS g + 1) ≤ w := h
    have hmf := le_max_left (stackS f) (stackS g + 1)
    have hmg := le_max_right (stackS f) (stackS g + 1)
    have hpf : d + stackS f ≤ w := by omega
    have hgd : d + 1 + stackS g ≤ w := by omega
    have hd1 : d + 1 < w := by have := one_le_stackS g; omega
    obtain ⟨if1, if2⟩ := ihf d hpf hd s
    set s1 := runGates z (compile' w f d hpf) s with hs1
    obtain ⟨ig1, ig2⟩ := ihg (d + 1) hgd hd1 s1
    set s2 := runGates z (compile' w g (d + 1) hgd) s1 with hs2
    have hsplit : ∀ j : Fin w, (runGates z (compile' w (.andf f g) d h) s) j
        = (Function.update s2 ⟨d, hd⟩ (s2 ⟨d, hd⟩ && s2 ⟨d + 1, hd1⟩)) j := by
      intro j
      show (runGates z (compile' w f d hpf ++ compile' w g (d + 1) hgd
          ++ [.andg ⟨d, hd⟩ ⟨d + 1, hd1⟩ ⟨d, hd⟩]) s) j = _
      rw [runGates_append', runGates_append']
      rfl
    constructor
    · rw [hsplit, Function.update_self,
        show s2 ⟨d, hd⟩ = s1 ⟨d, hd⟩ from ig2 ⟨d, hd⟩ (Nat.lt_succ_self d), if1, ig1]
      rfl
    · intro j hj
      rw [hsplit, Function.update_of_ne (Fin.ne_of_val_ne (show j.val ≠ d by omega)),
        ig2 j (by omega), if2 j hj]
  | xorf f g ihf ihg =>
    intro d h hd s
    have h' : d + max (stackS f) (stackS g + 1) ≤ w := h
    have hmf := le_max_left (stackS f) (stackS g + 1)
    have hmg := le_max_right (stackS f) (stackS g + 1)
    have hpf : d + stackS f ≤ w := by omega
    have hgd : d + 1 + stackS g ≤ w := by omega
    have hd1 : d + 1 < w := by have := one_le_stackS g; omega
    obtain ⟨if1, if2⟩ := ihf d hpf hd s
    set s1 := runGates z (compile' w f d hpf) s with hs1
    obtain ⟨ig1, ig2⟩ := ihg (d + 1) hgd hd1 s1
    set s2 := runGates z (compile' w g (d + 1) hgd) s1 with hs2
    have hsplit : ∀ j : Fin w, (runGates z (compile' w (.xorf f g) d h) s) j
        = (Function.update s2 ⟨d, hd⟩ (xor (s2 ⟨d, hd⟩) (s2 ⟨d + 1, hd1⟩))) j := by
      intro j
      show (runGates z (compile' w f d hpf ++ compile' w g (d + 1) hgd
          ++ [.xorg ⟨d, hd⟩ ⟨d + 1, hd1⟩ ⟨d, hd⟩]) s) j = _
      rw [runGates_append', runGates_append']
      rfl
    constructor
    · rw [hsplit, Function.update_self,
        show s2 ⟨d, hd⟩ = s1 ⟨d, hd⟩ from ig2 ⟨d, hd⟩ (Nat.lt_succ_self d), if1, ig1]
      rfl
    · intro j hj
      rw [hsplit, Function.update_of_ne (Fin.ne_of_val_ne (show j.val ≠ d by omega)),
        ig2 j (by omega), if2 j hj]

/-- One charged gate per circuit node. -/
theorem compile'_length (f : BForm n) :
    ∀ (d : ℕ) (h : d + stackS f ≤ w), (compile' w f d h).length = f.size := by
  induction f with
  | var i => intro d h; rfl
  | notf f ih =>
    intro d h
    have h' : d + stackS f ≤ w := h
    have hd : d < w := by have := one_le_stackS f; omega
    show (compile' w f d h' ++ [Gate.notg ⟨d, hd⟩ ⟨d, hd⟩]).length = f.size + 1
    rw [List.length_append, ih]
    rfl
  | andf f g ihf ihg =>
    intro d h
    have h' : d + max (stackS f) (stackS g + 1) ≤ w := h
    have hmf := le_max_left (stackS f) (stackS g + 1)
    have hmg := le_max_right (stackS f) (stackS g + 1)
    have hpf : d + stackS f ≤ w := by omega
    have hgd : d + 1 + stackS g ≤ w := by omega
    have hd : d < w := by have := one_le_stackS g; omega
    have hd1 : d + 1 < w := by have := one_le_stackS g; omega
    show (compile' w f d hpf ++ compile' w g (d + 1) hgd
        ++ [Gate.andg ⟨d, hd⟩ ⟨d + 1, hd1⟩ ⟨d, hd⟩]).length = f.size + g.size + 1
    rw [List.length_append, List.length_append, ihf, ihg]
    rfl
  | xorf f g ihf ihg =>
    intro d h
    have h' : d + max (stackS f) (stackS g + 1) ≤ w := h
    have hmf := le_max_left (stackS f) (stackS g + 1)
    have hmg := le_max_right (stackS f) (stackS g + 1)
    have hpf : d + stackS f ≤ w := by omega
    have hgd : d + 1 + stackS g ≤ w := by omega
    have hd : d < w := by have := one_le_stackS g; omega
    have hd1 : d + 1 < w := by have := one_le_stackS g; omega
    show (compile' w f d hpf ++ compile' w g (d + 1) hgd
        ++ [Gate.xorg ⟨d, hd⟩ ⟨d + 1, hd1⟩ ⟨d, hd⟩]).length = f.size + g.size + 1
    rw [List.length_append, List.length_append, ihf, ihg]
    rfl

/-- **The compiler**: circuit → charged program on `stackS f` wires. -/
def BForm.compile (f : BForm n) : Prog n (stackS f) :=
  ⟨compile' (stackS f) f 0 (by omega), ⟨0, one_le_stackS f⟩⟩

/-- **Semantic correctness.** -/
theorem compile_correct (f : BForm n) (z : Fin n → Bool) : f.compile.run z = f.eval z :=
  (compile_spec z f 0 (by omega) (one_le_stackS f) (fun _ => false)).1

/-- **Overhead exactly one**: cost = circuit size. -/
theorem compile_cost (f : BForm n) : f.compile.cost = f.size :=
  compile'_length f 0 (by omega)

/-- Wire budget ≤ circuit size. -/
theorem compile_wires (f : BForm n) : stackS f ≤ f.size := stackS_le_size f

/-- **Step (3), general half, packaged.**  Every bounded-fan-in circuit compiles into the charged language:
correct on all inputs, cost = size, wires ≤ size. -/
theorem general_circuit_compiler (f : BForm n) :
    ∃ (w : ℕ) (P : Prog n w),
      (∀ z, P.run z = f.eval z) ∧ P.cost = f.size ∧ w ≤ f.size :=
  ⟨stackS f, f.compile, fun z => compile_correct f z,
    compile_cost f, compile_wires f⟩

end PallLean.Paper93.DeepMath.PathB.ChargedCircuit

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedCircuit.compile_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedCircuit.general_circuit_compiler
