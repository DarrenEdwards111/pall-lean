import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBudgetIdentity

/-!
# N-Frame: the circuit upgrade — boundary observers with sharing, aimed at `P/poly`

The identity theorem showed the tree-transducer boundary energy *is* `B₂` formula complexity — so its ceiling is `NC¹`,
below the class `P vs NP` talks about.  This file upgrades the boundary model with **sharing**: a boundary observer is now
a **DAG** — a straight-line program of bounded-fan-in gates whose intermediate values may be reused.  Polynomial circuit
energy over the full binary basis is (non-uniform) `P/poly` — the model is now aimed at the right class.

  `CGate` / `runFrom` / `output` — straight-line circuits: each gate reads input variables or *earlier wire values*
        (sharing); evaluation threads the wire-value list.
  `compile` / `compile_spec` — **PROVED, the verified compiler**: every tree transducer compiles to a circuit of exactly
        its volume computing the same function (trees are the sharing-free special case).
  `cbudget f` — the circuit energy: minimal gate count over circuits computing `f`.
  `cbudget_le_budget` — **PROVED**: sharing can only lower the energy — the upgrade subsumes the tree model.
  `cbudget_le_exp` — **PROVED**: the exponential ceiling transfers.

## Honest scope — the right class, and the honestly-lost tearing bound

What the upgrade buys: polynomial `cbudget` is exactly non-uniform polynomial circuit size (`P/poly`), so a
super-polynomial `cbudget` lower bound for an `NP` target would genuinely be `NP ⊄ P/poly` (hence `P ≠ NP`).  The model
finally *states* the right question.  What the upgrade costs — stated plainly: **the Nečiporuk tearing bound does not
transfer.**  Nečiporuk's argument charges each formula *leaf* once via the block partition; with sharing, a single wire
can feed many gates and the leaf-accounting collapses.  No `ω(n)`-style circuit analogue is known — the best known
explicit circuit lower bounds are linear (`~c·n`), and that is the state of the field, not a defect of this file.  So the
upgraded model has: capture definitional (`P/poly` = poly energy), the compiler and ceiling proved, and its tearing gap =
**the** circuit lower bound problem, named and open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

/-! ### Straight-line circuits: gates with sharing -/

/-- A circuit gate: an input variable, a constant, or a unary/binary gate reading **earlier wire values** by index —
the sharing the tree model lacked. -/
inductive CGate (n : ℕ) where
  | var : Fin n → CGate n
  | cst : Bool → CGate n
  | un : (Bool → Bool) → ℕ → CGate n
  | bin : (Bool → Bool → Bool) → ℕ → ℕ → CGate n

/-- Evaluate one gate against the current wire values (out-of-range reads default to `false`). -/
def evalGate (x : Fin n → Bool) (vals : List Bool) : CGate n → Bool
  | .var i => x i
  | .cst b => b
  | .un op j => op (vals.getD j false)
  | .bin op j k => op (vals.getD j false) (vals.getD k false)

/-- Run a gate list, threading the wire-value list. -/
def runFrom (x : Fin n → Bool) (vals : List Bool) : List (CGate n) → List Bool
  | [] => vals
  | g :: gs => runFrom x (vals ++ [evalGate x vals g]) gs

theorem runFrom_append (x : Fin n → Bool) (vals : List Bool) (c₁ c₂ : List (CGate n)) :
    runFrom x vals (c₁ ++ c₂) = runFrom x (runFrom x vals c₁) c₂ := by
  induction c₁ generalizing vals with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, runFrom]; exact ih _

/-- The circuit's output: the last wire value. -/
def output (c : List (CGate n)) (x : Fin n → Bool) : Bool :=
  (runFrom x [] c).getD (c.length - 1) false

/-- The circuit computes `f`. -/
def computes (c : List (CGate n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, output c x = f x

/-- The **circuit energy**: minimal gate count over circuits computing `f` — the boundary budget with sharing. -/
noncomputable def cbudget (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {s | ∃ c : List (CGate n), computes c f ∧ c.length = s}

/-! ### The verified compiler: trees are the sharing-free special case -/

theorem volume_pos (t : Trans n) : 1 ≤ volume t := by
  cases t <;> simp [volume]

theorem getD_concat (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  rw [List.getD_append_right l [a] false l.length (le_refl _)]
  simp

/-- Compile a tree transducer to a gate list, emitting gates at absolute offset `off`. -/
def compile : ℕ → Trans n → List (CGate n)
  | _, .var i => [.var i]
  | _, .cst b => [.cst b]
  | off, .un op t => compile off t ++ [.un op (off + volume t - 1)]
  | off, .bin op t₁ t₂ =>
      compile off t₁ ++ compile (off + volume t₁) t₂
        ++ [.bin op (off + volume t₁ - 1) (off + volume t₁ + volume t₂ - 1)]

theorem compile_length (t : Trans n) : ∀ off, (compile off t).length = volume t := by
  induction t with
  | var i => intro off; rfl
  | cst b => intro off; rfl
  | un op t ih =>
    intro off
    simp only [compile, volume, List.length_append, ih]
    rfl
  | bin op t₁ t₂ ih₁ ih₂ =>
    intro off
    simp only [compile, volume, List.length_append, ih₁, ih₂]
    rfl

/-- **The compiler is correct (proved).**  Running the compiled gates from any wire state of length `off` appends exactly
`volume t` wires, the last carrying `eval t x`. -/
theorem compile_spec (t : Trans n) (x : Fin n → Bool) :
    ∀ vals : List Bool,
      ∃ w : List Bool, runFrom x vals (compile vals.length t) = vals ++ w ∧
        w.length = volume t ∧
        (vals ++ w).getD (vals.length + volume t - 1) false = eval t x := by
  induction t with
  | var i =>
    intro vals
    refine ⟨[x i], rfl, rfl, ?_⟩
    show (vals ++ [x i]).getD (vals.length + 1 - 1) false = x i
    rw [Nat.add_sub_cancel]
    exact getD_concat vals (x i)
  | cst b =>
    intro vals
    refine ⟨[b], rfl, rfl, ?_⟩
    show (vals ++ [b]).getD (vals.length + 1 - 1) false = b
    rw [Nat.add_sub_cancel]
    exact getD_concat vals b
  | un op t ih =>
    intro vals
    obtain ⟨w₁, hrun, hlen, hval⟩ := ih vals
    refine ⟨w₁ ++ [op (eval t x)], ?_, ?_, ?_⟩
    · show runFrom x vals (compile vals.length t ++ [.un op (vals.length + volume t - 1)])
        = vals ++ (w₁ ++ [op (eval t x)])
      rw [runFrom_append, hrun]
      show (vals ++ w₁) ++ [evalGate x (vals ++ w₁) (.un op (vals.length + volume t - 1))]
        = vals ++ (w₁ ++ [op (eval t x)])
      rw [show evalGate x (vals ++ w₁) (.un op (vals.length + volume t - 1)) = op (eval t x) by
        simp only [evalGate]; rw [hval]]
      rw [List.append_assoc]
    · simp [hlen, volume]
    · rw [← List.append_assoc]
      have hL : (vals ++ w₁).length = vals.length + volume t := by
        rw [List.length_append, hlen]
      show ((vals ++ w₁) ++ [op (eval t x)]).getD (vals.length + (volume t + 1) - 1) false
        = op (eval t x)
      rw [show vals.length + (volume t + 1) - 1 = (vals ++ w₁).length by omega]
      exact getD_concat _ _
  | bin op t₁ t₂ ih₁ ih₂ =>
    intro vals
    obtain ⟨w₁, hrun₁, hlen₁, hval₁⟩ := ih₁ vals
    obtain ⟨w₂, hrun₂, hlen₂, hval₂⟩ := ih₂ (vals ++ w₁)
    have hL₁ : (vals ++ w₁).length = vals.length + volume t₁ := by
      rw [List.length_append, hlen₁]
    have hpos₁ := volume_pos t₁
    have hpos₂ := volume_pos t₂
    have hval₁' : ((vals ++ w₁) ++ w₂).getD (vals.length + volume t₁ - 1) false = eval t₁ x := by
      rw [List.getD_append (vals ++ w₁) w₂ false _ (by omega), hval₁]
    have hval₂' : ((vals ++ w₁) ++ w₂).getD (vals.length + volume t₁ + volume t₂ - 1) false
        = eval t₂ x := by
      have := hval₂
      rw [hL₁] at this
      exact this
    refine ⟨w₁ ++ w₂ ++ [op (eval t₁ x) (eval t₂ x)], ?_, ?_, ?_⟩
    · show runFrom x vals
        (compile vals.length t₁ ++ compile (vals.length + volume t₁) t₂
          ++ [.bin op (vals.length + volume t₁ - 1) (vals.length + volume t₁ + volume t₂ - 1)])
        = vals ++ (w₁ ++ w₂ ++ [op (eval t₁ x) (eval t₂ x)])
      rw [runFrom_append, runFrom_append, hrun₁]
      rw [show compile (vals.length + volume t₁) t₂ = compile (vals ++ w₁).length t₂ by rw [hL₁]]
      rw [hrun₂]
      show ((vals ++ w₁) ++ w₂)
          ++ [evalGate x ((vals ++ w₁) ++ w₂)
              (.bin op (vals.length + volume t₁ - 1) (vals.length + volume t₁ + volume t₂ - 1))]
        = vals ++ (w₁ ++ w₂ ++ [op (eval t₁ x) (eval t₂ x)])
      rw [show evalGate x ((vals ++ w₁) ++ w₂)
            (.bin op (vals.length + volume t₁ - 1) (vals.length + volume t₁ + volume t₂ - 1))
          = op (eval t₁ x) (eval t₂ x) by
        simp only [evalGate]; rw [hval₁', hval₂']]
      simp [List.append_assoc]
    · simp [hlen₁, hlen₂, volume]; omega
    · have hLL : (vals ++ (w₁ ++ w₂)).length = vals.length + volume t₁ + volume t₂ := by
        simp [List.length_append, hlen₁, hlen₂]; omega
      show (vals ++ (w₁ ++ w₂ ++ [op (eval t₁ x) (eval t₂ x)])).getD
          (vals.length + (volume t₁ + volume t₂ + 1) - 1) false = op (eval t₁ x) (eval t₂ x)
      rw [show vals ++ (w₁ ++ w₂ ++ [op (eval t₁ x) (eval t₂ x)])
          = (vals ++ (w₁ ++ w₂)) ++ [op (eval t₁ x) (eval t₂ x)] by simp [List.append_assoc]]
      rw [show vals.length + (volume t₁ + volume t₂ + 1) - 1
          = (vals ++ (w₁ ++ w₂)).length by omega]
      exact getD_concat _ _

/-- **Compiled trees compute their function (proved).** -/
theorem compile_computes (t : Trans n) : computes (compile 0 t) (fun x => eval t x) := by
  intro x
  obtain ⟨w, hrun, hlen, hval⟩ := compile_spec t x []
  unfold output
  rw [show compile 0 t = compile ([] : List Bool).length t from rfl, hrun, compile_length]
  simpa using hval

/-! ### The upgrade: sharing only lowers the energy, the ceiling transfers -/

/-- **Sharing can only lower the energy (proved)**: `cbudget f ≤ budget f` — circuits subsume the tree model. -/
theorem cbudget_le_budget (f : (Fin n → Bool) → Bool) : cbudget f ≤ budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  unfold budget
  obtain ⟨t, he, hv⟩ := Nat.sInf_mem hne
  rw [← hv, ← compile_length t 0]
  refine Nat.sInf_le ⟨compile 0 t, ?_, rfl⟩
  have := compile_computes t
  rwa [show (fun x => eval t x) = f from funext (fun x => by rw [he])] at this

/-- **The exponential ceiling transfers (proved).** -/
theorem cbudget_le_exp (f : (Fin n → Bool) → Bool) :
    cbudget f ≤ (3 * n + 2) * 2 ^ n + 1 :=
  le_trans (cbudget_le_budget f)
    (le_trans (budget_le_budgetAt 3 (exists_width_le_three f)) (budgetAt_three_le_exp f))

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.compile_spec
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.compile_computes
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_le_budget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_le_exp
