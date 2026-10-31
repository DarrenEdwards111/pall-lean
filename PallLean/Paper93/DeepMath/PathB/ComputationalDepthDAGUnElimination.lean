import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDAGWireSurgery

/-!
# DAG two-kill, brick 1: unary-gate elimination

Toward the DAG two-kill step theorem.  The constant-elimination surgery
(`elimGate`) deletes a `cst` wire, absorbing the constant into readers.  After a
restriction, the killed `var` gate's *readers* become unary gates — deleting those
needs the second surgery primitive, sound precisely because the gate basis is
arbitrary: **a unary gate's op can be absorbed into every reader by composition**.

* `elimUnGate p op q` — rewire one gate after deleting wire `p` (which held
  `un op q`, `q < p`): readers of `p` precompose `op` and read `q` directly — in
  either operand position, including double reads; later references shift down;
* `evalGate_elimUn` / `runFrom_elimUn` — **PROVED**: the simulation invariant is
  `eraseIdx p`, carried by the relation `vals.getD p = op (vals.getD q)`;
* `computes_elimUn` — **PROVED**: a non-final in-range unary gate can be deleted —
  the circuit computes the same function with one gate fewer;
* `cbudget_elimUn_le` — the budget interface;
* `computes_un_oob` — an out-of-range unary gate is a constant in disguise
  (`op false`), converting that case to the existing constant surgery.

Assembly of the two-kill itself (case analysis: second `var` gate / constant-ized
reader / eliminable unary reader / the output-reader case refuted by the
independent-restrictions hypothesis) is the next brick.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The rewiring map -/

/-- Rewire one gate after deleting wire `p`, which held `un op q` with `q < p`:
readers of `p` precompose `op` and read `q`; later references shift down. -/
def elimUnGate {n : ℕ} (p : ℕ) (op : Bool → Bool) (q : ℕ) : CGate n → CGate n
  | .var i => .var i
  | .cst c => .cst c
  | .un op2 j => if j = p then .un (fun a => op2 (op a)) q else .un op2 (elimRef p j)
  | .bin op2 j k =>
      if j = p then
        (if k = p then .bin (fun a b => op2 (op a) (op b)) q q
         else .bin (fun a b => op2 (op a) b) q (elimRef p k))
      else if k = p then .bin (fun a b => op2 a (op b)) (elimRef p j) q
      else .bin op2 (elimRef p j) (elimRef p k)

theorem getD_eraseIdx_lt (l : List Bool) (p q : ℕ) (hqp : q < p) :
    (l.eraseIdx p).getD q false = l.getD q false := by
  have h := getD_eraseIdx_elimRef l p q (by omega)
  rwa [show elimRef p q = q from if_pos hqp] at h

theorem evalGate_elimUn {n : ℕ} (x : Fin n → Bool) (vals : List Bool) (p q : ℕ)
    (op : Bool → Bool) (hqp : q < p)
    (hrel : vals.getD p false = op (vals.getD q false)) (g : CGate n) :
    evalGate x (vals.eraseIdx p) (elimUnGate p op q g) = evalGate x vals g := by
  cases g with
  | var i => rfl
  | cst c => rfl
  | un op2 j =>
    show evalGate x (vals.eraseIdx p)
        (if j = p then CGate.un (fun a => op2 (op a)) q else CGate.un op2 (elimRef p j))
        = op2 (vals.getD j false)
    by_cases hj : j = p
    · rw [if_pos hj]
      show op2 (op ((vals.eraseIdx p).getD q false)) = op2 (vals.getD j false)
      rw [getD_eraseIdx_lt vals p q hqp, hj, hrel]
    · rw [if_neg hj]
      show op2 ((vals.eraseIdx p).getD (elimRef p j) false) = op2 (vals.getD j false)
      rw [getD_eraseIdx_elimRef vals p j hj]
  | bin op2 j k =>
    show evalGate x (vals.eraseIdx p)
        (if j = p then
          (if k = p then CGate.bin (fun a b => op2 (op a) (op b)) q q
           else CGate.bin (fun a b => op2 (op a) b) q (elimRef p k))
         else if k = p then CGate.bin (fun a b => op2 a (op b)) (elimRef p j) q
         else CGate.bin op2 (elimRef p j) (elimRef p k))
        = op2 (vals.getD j false) (vals.getD k false)
    by_cases hj : j = p
    · by_cases hk : k = p
      · rw [if_pos hj, if_pos hk]
        show op2 (op ((vals.eraseIdx p).getD q false)) (op ((vals.eraseIdx p).getD q false))
            = op2 (vals.getD j false) (vals.getD k false)
        rw [getD_eraseIdx_lt vals p q hqp, hj, hk, hrel]
      · rw [if_pos hj, if_neg hk]
        show op2 (op ((vals.eraseIdx p).getD q false))
            ((vals.eraseIdx p).getD (elimRef p k) false)
            = op2 (vals.getD j false) (vals.getD k false)
        rw [getD_eraseIdx_lt vals p q hqp, hj, hrel, getD_eraseIdx_elimRef vals p k hk]
    · by_cases hk : k = p
      · rw [if_neg hj, if_pos hk]
        show op2 ((vals.eraseIdx p).getD (elimRef p j) false)
            (op ((vals.eraseIdx p).getD q false))
            = op2 (vals.getD j false) (vals.getD k false)
        rw [getD_eraseIdx_lt vals p q hqp, hk, hrel, getD_eraseIdx_elimRef vals p j hj]
      · rw [if_neg hj, if_neg hk]
        show op2 ((vals.eraseIdx p).getD (elimRef p j) false)
            ((vals.eraseIdx p).getD (elimRef p k) false)
            = op2 (vals.getD j false) (vals.getD k false)
        rw [getD_eraseIdx_elimRef vals p j hj, getD_eraseIdx_elimRef vals p k hk]

/-! ### The simulation invariant -/

theorem runFrom_elimUn {n : ℕ} (x : Fin n → Bool) (p q : ℕ) (op : Bool → Bool)
    (hqp : q < p) :
    ∀ (gs : List (CGate n)) (vals : List Bool), p < vals.length →
      vals.getD p false = op (vals.getD q false) →
      runFrom x (vals.eraseIdx p) (gs.map (elimUnGate p op q))
        = (runFrom x vals gs).eraseIdx p := by
  intro gs
  induction gs with
  | nil => intro vals _ _; rfl
  | cons g rest ih =>
    intro vals hp hrel
    show runFrom x (vals.eraseIdx p ++ [evalGate x (vals.eraseIdx p) (elimUnGate p op q g)])
        (rest.map (elimUnGate p op q))
        = (runFrom x (vals ++ [evalGate x vals g]) rest).eraseIdx p
    rw [evalGate_elimUn x vals p q op hqp hrel g]
    rw [← List.eraseIdx_append_of_lt_length hp [evalGate x vals g]]
    exact ih (vals ++ [evalGate x vals g])
      (by rw [List.length_append]; show p < vals.length + 1; omega)
      (by rw [List.getD_append vals [evalGate x vals g] false p hp,
        List.getD_append vals [evalGate x vals g] false q (by omega)]; exact hrel)

/-! ### The surgery: a non-final in-range unary gate can be deleted -/

/-- **The unary-gate surgery (proved)**: a non-final unary gate with an in-range
source can be deleted — every reader precomposes its op, every later reference
shifts, and the circuit still computes `f` with one gate fewer. -/
theorem computes_elimUn {n : ℕ} (c₁ c₂ : List (CGate n)) (op : Bool → Bool) (q : ℕ)
    (f : (Fin n → Bool) → Bool)
    (hcomp : computes (c₁ ++ CGate.un op q :: c₂) f) (hne : c₂ ≠ [])
    (hq : q < c₁.length) :
    computes (c₁ ++ c₂.map (elimUnGate c₁.length op q)) f := by
  have hc2 : 1 ≤ c₂.length := by
    cases c₂ with
    | nil => exact absurd rfl hne
    | cons g rest => show 1 ≤ rest.length + 1; omega
  intro x
  have hx := hcomp x
  have hV : (runFrom x [] c₁).length = c₁.length := by
    rw [runFrom_length]
    simp
  have hsplit : runFrom x [] (c₁ ++ CGate.un op q :: c₂)
      = runFrom x (runFrom x [] c₁ ++ [op ((runFrom x [] c₁).getD q false)]) c₂ := by
    rw [show c₁ ++ CGate.un op q :: c₂ = (c₁ ++ [CGate.un op q]) ++ c₂ by simp,
      runFrom_append, runFrom_append]
    rfl
  have hVe : (runFrom x [] c₁ ++ [op ((runFrom x [] c₁).getD q false)]).eraseIdx c₁.length
      = runFrom x [] c₁ := by
    rw [List.eraseIdx_append_of_length_le (le_of_eq hV) _]
    rw [show c₁.length - (runFrom x [] c₁).length = 0 by omega]
    rw [show ([op ((runFrom x [] c₁).getD q false)] : List Bool).eraseIdx 0
      = ([] : List Bool) from rfl, List.append_nil]
  have hnew : runFrom x (runFrom x [] c₁) (c₂.map (elimUnGate c₁.length op q))
      = (runFrom x (runFrom x [] c₁ ++ [op ((runFrom x [] c₁).getD q false)]) c₂).eraseIdx
          c₁.length := by
    have h1 := runFrom_elimUn x c₁.length q op hq c₂
      (runFrom x [] c₁ ++ [op ((runFrom x [] c₁).getD q false)])
      (by rw [List.length_append, hV]; show c₁.length < c₁.length + 1; omega)
      (by
        rw [List.getD_append _ _ false q (by omega),
          show c₁.length = (runFrom x [] c₁).length from hV.symm]
        exact getD_concat _ _)
    rw [hVe] at h1
    exact h1
  show (runFrom x [] (c₁ ++ c₂.map (elimUnGate c₁.length op q))).getD
      ((c₁ ++ c₂.map (elimUnGate c₁.length op q)).length - 1) false = f x
  rw [runFrom_append, hnew]
  rw [show (c₁ ++ c₂.map (elimUnGate c₁.length op q)).length = c₁.length + c₂.length by
    rw [List.length_append, List.length_map]]
  rw [getD_eraseIdx_ge _ c₁.length (c₁.length + c₂.length - 1) (by omega)]
  rw [show c₁.length + c₂.length - 1 + 1 = c₁.length + c₂.length by omega]
  have hxold : (runFrom x (runFrom x [] c₁ ++ [op ((runFrom x [] c₁).getD q false)]) c₂).getD
      ((c₁ ++ CGate.un op q :: c₂).length - 1) false = f x := by
    rw [← hsplit]
    exact hx
  rw [show (c₁ ++ CGate.un op q :: c₂).length - 1 = c₁.length + c₂.length by
    rw [List.length_append, List.length_cons]; omega] at hxold
  exact hxold

/-- The budget interface: deleting the unary gate certifies one gate saved. -/
theorem cbudget_elimUn_le {n : ℕ} (c₁ c₂ : List (CGate n)) (op : Bool → Bool) (q : ℕ)
    (f : (Fin n → Bool) → Bool)
    (hcomp : computes (c₁ ++ CGate.un op q :: c₂) f) (hne : c₂ ≠ [])
    (hq : q < c₁.length) :
    cbudget f ≤ c₁.length + c₂.length := by
  have hmem : (c₁ ++ c₂.map (elimUnGate c₁.length op q)).length
      ∈ {s | ∃ c : List (CGate n), computes c f ∧ c.length = s} :=
    ⟨c₁ ++ c₂.map (elimUnGate c₁.length op q), computes_elimUn c₁ c₂ op q f hcomp hne hq, rfl⟩
  have h := Nat.sInf_le hmem
  rwa [List.length_append, List.length_map] at h

/-! ### Out-of-range unary gates are constants in disguise -/

/-- A unary gate reading past the wire frontier always outputs `op false`: it may be
replaced by that constant, converting to the existing constant surgery. -/
theorem computes_un_oob {n : ℕ} (c₁ c₂ : List (CGate n)) (op : Bool → Bool) (q : ℕ)
    (f : (Fin n → Bool) → Bool)
    (hcomp : computes (c₁ ++ CGate.un op q :: c₂) f) (hq : c₁.length ≤ q) :
    computes (c₁ ++ CGate.cst (op false) :: c₂) f := by
  intro x
  have hx := hcomp x
  have hV : (runFrom x [] c₁).length = c₁.length := by
    rw [runFrom_length]
    simp
  have hv : op ((runFrom x [] c₁).getD q false) = op false := by
    rw [List.getD_eq_default _ _ (by omega)]
  have hsA : runFrom x [] (c₁ ++ CGate.un op q :: c₂)
      = runFrom x (runFrom x [] c₁ ++ [op ((runFrom x [] c₁).getD q false)]) c₂ := by
    rw [show c₁ ++ CGate.un op q :: c₂ = (c₁ ++ [CGate.un op q]) ++ c₂ by simp,
      runFrom_append, runFrom_append]
    rfl
  have hsB : runFrom x [] (c₁ ++ CGate.cst (op false) :: c₂)
      = runFrom x (runFrom x [] c₁ ++ [op false]) c₂ := by
    rw [show c₁ ++ CGate.cst (op false) :: c₂ = (c₁ ++ [CGate.cst (op false)]) ++ c₂ by simp,
      runFrom_append, runFrom_append]
    rfl
  have hrun : runFrom x [] (c₁ ++ CGate.cst (op false) :: c₂)
      = runFrom x [] (c₁ ++ CGate.un op q :: c₂) := by
    rw [hsA, hsB, hv]
  have h2 : (c₁ ++ CGate.un op q :: c₂).length
      = (c₁ ++ CGate.cst (op false) :: c₂).length := by
    simp
  show (runFrom x [] (c₁ ++ CGate.cst (op false) :: c₂)).getD
      ((c₁ ++ CGate.cst (op false) :: c₂).length - 1) false = f x
  rw [hrun, ← h2]
  exact hx

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.computes_elimUn
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_elimUn_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.computes_un_oob
