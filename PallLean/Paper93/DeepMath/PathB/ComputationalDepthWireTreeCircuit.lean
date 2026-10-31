import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade

/-!
# Wire trees: the layered-circuit fabric for machine simulation

The verified compiler of the circuit upgrade turns *input-leaf* trees (`Trans n`) into
straight-line circuits.  Simulating a machine step-by-step needs one more device: trees
whose leaves read **earlier wires** — the previous snapshot layer — rather than circuit
inputs.  This file provides that fabric, machine-independently:

* `WTree P` — trees over an abstract port type `P` (`port`/`cst`/`un`/`bin`), with
  evaluation `weval` against a port valuation and volume `wvol`;
* `compileW` / `compileW_spec` — **PROVED**: compiling a wire tree at offset `off`
  against a port-position map `pos` appends exactly `wvol t` wires, the last carrying
  `weval t v`, whenever the wires at `pos` currently hold `v` (leaves become
  `.un id (pos p)` gates — sharing of the previous layer is exactly wire reuse);
* `slotW` / `slotW_spec` — **PROVED**: a tree padded to a fixed slot size `V` by
  output-copy gates, so every slot has the same length and affine output positions;
* `layerW` / `layerW_spec` — **PROVED**: a list of slotted trees laid out consecutively;
  output `j` sits at offset `(j+1)·V - 1` into the block;
* `orListW` with exact evaluation (`List.any`) and exact volume;
* `any_finRange_select` — the one-hot selection lemma: an OR of `(index = p) ∧ g p`
  over all `p` collapses to `g` at the hot index;
* `runFrom_closed` — a block of input/constant gates appends exactly its values (the
  initial snapshot layer).

Everything here is proved; nothing is machine-specific.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ} {P : Type}

/-! ### Wire trees over an abstract port type -/

/-- A tree whose leaves are abstract **ports** (wire references) or constants. -/
inductive WTree (P : Type) where
  | port : P → WTree P
  | cst : Bool → WTree P
  | un : (Bool → Bool) → WTree P → WTree P
  | bin : (Bool → Bool → Bool) → WTree P → WTree P → WTree P

/-- Evaluate a wire tree against a port valuation. -/
def weval : WTree P → (P → Bool) → Bool
  | .port p, v => v p
  | .cst b, _ => b
  | .un op t, v => op (weval t v)
  | .bin op t₁ t₂, v => op (weval t₁ v) (weval t₂ v)

/-- Volume of a wire tree: the number of gates it compiles to. -/
def wvol : WTree P → ℕ
  | .port _ => 1
  | .cst _ => 1
  | .un _ t => wvol t + 1
  | .bin _ t₁ t₂ => wvol t₁ + wvol t₂ + 1

theorem wvol_pos (t : WTree P) : 1 ≤ wvol t := by
  cases t <;> simp only [wvol] <;> omega

/-! ### The wire-tree compiler -/

/-- Compile a wire tree to gates at absolute offset `off`, reading port `p` from wire
`pos p`. -/
def compileW (pos : P → ℕ) : ℕ → WTree P → List (CGate n)
  | _, .port p => [.un id (pos p)]
  | _, .cst b => [.cst b]
  | off, .un op t => compileW pos off t ++ [.un op (off + wvol t - 1)]
  | off, .bin op t₁ t₂ =>
      compileW pos off t₁ ++ compileW pos (off + wvol t₁) t₂
        ++ [.bin op (off + wvol t₁ - 1) (off + wvol t₁ + wvol t₂ - 1)]

theorem compileW_length (pos : P → ℕ) (t : WTree P) :
    ∀ off, (compileW (n := n) pos off t).length = wvol t := by
  induction t with
  | port p => intro off; rfl
  | cst b => intro off; rfl
  | un op t ih =>
    intro off
    simp only [compileW, wvol, List.length_append, ih]
    rfl
  | bin op t₁ t₂ ih₁ ih₂ =>
    intro off
    simp only [compileW, wvol, List.length_append, ih₁, ih₂]
    rfl

/-- **The wire-tree compiler is correct (proved).**  If the wires at `pos` hold the port
valuation `v`, running the compiled gates from any wire state of length `off` appends
exactly `wvol t` wires, the last carrying `weval t v`. -/
theorem compileW_spec (t : WTree P) (x : Fin n → Bool) (pos : P → ℕ) (v : P → Bool) :
    ∀ vals : List Bool,
      (∀ p : P, pos p < vals.length ∧ vals.getD (pos p) false = v p) →
      ∃ w : List Bool, runFrom x vals (compileW pos vals.length t) = vals ++ w ∧
        w.length = wvol t ∧
        (vals ++ w).getD (vals.length + wvol t - 1) false = weval t v := by
  induction t with
  | port p =>
    intro vals hv
    refine ⟨[v p], ?_, rfl, ?_⟩
    · show runFrom x (vals ++ [evalGate x vals (CGate.un id (pos p))]) [] = vals ++ [v p]
      rw [show evalGate x vals (CGate.un id (pos p)) = v p from by
        simp only [evalGate, id_eq]; exact (hv p).2]
      rfl
    · show (vals ++ [v p]).getD (vals.length + 1 - 1) false = v p
      rw [Nat.add_sub_cancel]
      exact getD_concat vals (v p)
  | cst b =>
    intro vals _
    refine ⟨[b], rfl, rfl, ?_⟩
    show (vals ++ [b]).getD (vals.length + 1 - 1) false = b
    rw [Nat.add_sub_cancel]
    exact getD_concat vals b
  | un op t ih =>
    intro vals hv
    obtain ⟨w₁, hrun, hlen, hval⟩ := ih vals hv
    refine ⟨w₁ ++ [op (weval t v)], ?_, ?_, ?_⟩
    · show runFrom x vals (compileW pos vals.length t ++ [.un op (vals.length + wvol t - 1)])
        = vals ++ (w₁ ++ [op (weval t v)])
      rw [runFrom_append, hrun]
      show (vals ++ w₁) ++ [evalGate x (vals ++ w₁) (.un op (vals.length + wvol t - 1))]
        = vals ++ (w₁ ++ [op (weval t v)])
      rw [show evalGate x (vals ++ w₁) (CGate.un op (vals.length + wvol t - 1))
          = op (weval t v) by
        simp only [evalGate]; rw [hval]]
      rw [List.append_assoc]
    · simp [hlen, wvol]
    · rw [← List.append_assoc]
      show ((vals ++ w₁) ++ [op (weval t v)]).getD (vals.length + (wvol t + 1) - 1) false
        = op (weval t v)
      rw [show vals.length + (wvol t + 1) - 1 = (vals ++ w₁).length by
        rw [List.length_append, hlen]; omega]
      exact getD_concat _ _
  | bin op t₁ t₂ ih₁ ih₂ =>
    intro vals hv
    obtain ⟨w₁, hrun₁, hlen₁, hval₁⟩ := ih₁ vals hv
    have hL₁ : (vals ++ w₁).length = vals.length + wvol t₁ := by
      rw [List.length_append, hlen₁]
    have hv' : ∀ p : P, pos p < (vals ++ w₁).length ∧ (vals ++ w₁).getD (pos p) false = v p := by
      intro p
      obtain ⟨h1, h2⟩ := hv p
      refine ⟨by rw [List.length_append]; omega, ?_⟩
      rw [List.getD_append vals w₁ false (pos p) h1]
      exact h2
    obtain ⟨w₂, hrun₂, hlen₂, hval₂⟩ := ih₂ (vals ++ w₁) hv'
    have hpos₁ := wvol_pos t₁
    have hpos₂ := wvol_pos t₂
    have hval₁' : ((vals ++ w₁) ++ w₂).getD (vals.length + wvol t₁ - 1) false = weval t₁ v := by
      rw [List.getD_append (vals ++ w₁) w₂ false _ (by omega), hval₁]
    have hval₂' : ((vals ++ w₁) ++ w₂).getD (vals.length + wvol t₁ + wvol t₂ - 1) false
        = weval t₂ v := by
      have := hval₂
      rw [hL₁] at this
      exact this
    refine ⟨w₁ ++ w₂ ++ [op (weval t₁ v) (weval t₂ v)], ?_, ?_, ?_⟩
    · show runFrom x vals
        (compileW pos vals.length t₁ ++ compileW pos (vals.length + wvol t₁) t₂
          ++ [.bin op (vals.length + wvol t₁ - 1) (vals.length + wvol t₁ + wvol t₂ - 1)])
        = vals ++ (w₁ ++ w₂ ++ [op (weval t₁ v) (weval t₂ v)])
      rw [runFrom_append, runFrom_append, hrun₁]
      rw [show compileW (n := n) pos (vals.length + wvol t₁) t₂
          = compileW pos (vals ++ w₁).length t₂ by rw [hL₁]]
      rw [hrun₂]
      show ((vals ++ w₁) ++ w₂)
          ++ [evalGate x ((vals ++ w₁) ++ w₂)
              (.bin op (vals.length + wvol t₁ - 1) (vals.length + wvol t₁ + wvol t₂ - 1))]
        = vals ++ (w₁ ++ w₂ ++ [op (weval t₁ v) (weval t₂ v)])
      rw [show evalGate x ((vals ++ w₁) ++ w₂)
            (CGate.bin op (vals.length + wvol t₁ - 1) (vals.length + wvol t₁ + wvol t₂ - 1))
          = op (weval t₁ v) (weval t₂ v) by
        simp only [evalGate]; rw [hval₁', hval₂']]
      simp [List.append_assoc]
    · simp [hlen₁, hlen₂, wvol]; omega
    · show (vals ++ (w₁ ++ w₂ ++ [op (weval t₁ v) (weval t₂ v)])).getD
          (vals.length + (wvol t₁ + wvol t₂ + 1) - 1) false = op (weval t₁ v) (weval t₂ v)
      rw [show vals ++ (w₁ ++ w₂ ++ [op (weval t₁ v) (weval t₂ v)])
          = (vals ++ (w₁ ++ w₂)) ++ [op (weval t₁ v) (weval t₂ v)] by simp [List.append_assoc]]
      have hLL : (vals ++ (w₁ ++ w₂)).length = vals.length + wvol t₁ + wvol t₂ := by
        simp [List.length_append, hlen₁, hlen₂]; omega
      rw [show vals.length + (wvol t₁ + wvol t₂ + 1) - 1
          = (vals ++ (w₁ ++ w₂)).length by omega]
      exact getD_concat _ _

/-! ### Padded slots: every tree in a fixed-size slot with an affine output position -/

/-- `k` copy gates, all reading wire `src`. -/
def padTo (k src : ℕ) : List (CGate n) := List.replicate k (.un id src)

theorem getD_replicate_lt (b : Bool) : ∀ (k i : ℕ), i < k →
    (List.replicate k b).getD i false = b := by
  intro k
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact ih i (by omega)

theorem runFrom_padTo (x : Fin n → Bool) (src : ℕ) :
    ∀ (k : ℕ) (vals : List Bool), src < vals.length →
      runFrom x vals (padTo k src) = vals ++ List.replicate k (vals.getD src false) := by
  intro k
  induction k with
  | zero =>
    intro vals _
    show vals = vals ++ []
    rw [List.append_nil]
  | succ k ih =>
    intro vals hsrc
    show runFrom x (vals ++ [evalGate x vals (CGate.un id src)]) (padTo k src)
      = vals ++ List.replicate (k + 1) (vals.getD src false)
    rw [show evalGate x vals (CGate.un id src) = vals.getD src false from by
      simp only [evalGate, id_eq]]
    rw [ih (vals ++ [vals.getD src false]) (by rw [List.length_append]; omega)]
    rw [List.getD_append vals [vals.getD src false] false src hsrc]
    rw [List.append_assoc, List.singleton_append, ← List.replicate_succ]

/-- A tree in a slot of fixed size `V`: the compiled tree followed by output copies. -/
def slotW (pos : P → ℕ) (V off : ℕ) (t : WTree P) : List (CGate n) :=
  compileW pos off t ++ padTo (V - wvol t) (off + wvol t - 1)

theorem slotW_length (pos : P → ℕ) (V off : ℕ) (t : WTree P) (hV : wvol t ≤ V) :
    (slotW (n := n) pos V off t).length = V := by
  rw [slotW, List.length_append, compileW_length, padTo, List.length_replicate]
  omega

/-- **The slot is correct (proved)**: it appends exactly `V` wires, the last carrying the
tree's value. -/
theorem slotW_spec (t : WTree P) (x : Fin n → Bool) (pos : P → ℕ) (v : P → Bool)
    (V : ℕ) (hV : wvol t ≤ V) :
    ∀ vals : List Bool,
      (∀ p : P, pos p < vals.length ∧ vals.getD (pos p) false = v p) →
      ∃ w : List Bool, runFrom x vals (slotW pos V vals.length t) = vals ++ w ∧
        w.length = V ∧
        (vals ++ w).getD (vals.length + V - 1) false = weval t v := by
  intro vals hv
  obtain ⟨w₁, hrun, hlen, hval⟩ := compileW_spec t x pos v vals hv
  have hw1 : 1 ≤ wvol t := wvol_pos t
  have hsrc : vals.length + wvol t - 1 < (vals ++ w₁).length := by
    rw [List.length_append, hlen]; omega
  refine ⟨w₁ ++ List.replicate (V - wvol t) (weval t v), ?_, ?_, ?_⟩
  · rw [slotW, runFrom_append, hrun, runFrom_padTo x _ _ (vals ++ w₁) hsrc, hval,
      List.append_assoc]
  · rw [List.length_append, hlen, List.length_replicate]; omega
  · by_cases hEq : wvol t = V
    · rw [show V - wvol t = 0 by omega, List.replicate_zero, List.append_nil, ← hEq]
      exact hval
    · have hlt : wvol t < V := lt_of_le_of_ne hV hEq
      rw [← List.append_assoc]
      rw [List.getD_append_right (vals ++ w₁) _ false (vals.length + V - 1)
        (by rw [List.length_append, hlen]; omega)]
      exact getD_replicate_lt _ _ _ (by rw [List.length_append, hlen]; omega)

/-! ### Layers: consecutive slots with affine output positions -/

/-- A layer: each tree in its own size-`V` slot, laid out consecutively from `off`. -/
def layerW (pos : P → ℕ) (V : ℕ) : ℕ → List (WTree P) → List (CGate n)
  | _, [] => []
  | off, t :: ts => slotW pos V off t ++ layerW pos V (off + V) ts

theorem layerW_length (pos : P → ℕ) (V : ℕ) :
    ∀ (ts : List (WTree P)) (off : ℕ), (∀ t ∈ ts, wvol t ≤ V) →
      (layerW (n := n) pos V off ts).length = ts.length * V := by
  intro ts
  induction ts with
  | nil => intro off _; simp [layerW]
  | cons t ts ih =>
    intro off hV
    rw [layerW, List.length_append, slotW_length pos V off t (hV t List.mem_cons_self),
      ih (off + V) (fun t' ht' => hV t' (List.mem_cons_of_mem t ht')), List.length_cons,
      Nat.succ_mul]
    omega

/-- **The layer is correct (proved)**: it appends `ts.length · V` wires, and the value of
tree `j` sits at offset `(j+1)·V - 1` into the block. -/
theorem layerW_spec (x : Fin n → Bool) (pos : P → ℕ) (v : P → Bool) (V : ℕ) :
    ∀ (ts : List (WTree P)) (vals : List Bool), (∀ t ∈ ts, wvol t ≤ V) →
      (∀ p : P, pos p < vals.length ∧ vals.getD (pos p) false = v p) →
      ∃ w : List Bool, runFrom x vals (layerW pos V vals.length ts) = vals ++ w ∧
        w.length = ts.length * V ∧
        ∀ j : Fin ts.length, (vals ++ w).getD (vals.length + (j.val + 1) * V - 1) false
          = weval (ts.get j) v := by
  intro ts
  induction ts with
  | nil =>
    intro vals _ _
    refine ⟨[], ?_, by simp, fun j => absurd j.isLt (by simp)⟩
    show vals = vals ++ []
    rw [List.append_nil]
  | cons t ts ih =>
    intro vals hV hv
    have hVt : wvol t ≤ V := hV t List.mem_cons_self
    have hV1 : 1 ≤ V := le_trans (wvol_pos t) hVt
    obtain ⟨w₀, hrun₀, hlen₀, hval₀⟩ := slotW_spec t x pos v V hVt vals hv
    have hL₀ : (vals ++ w₀).length = vals.length + V := by
      rw [List.length_append, hlen₀]
    have hv' : ∀ p : P, pos p < (vals ++ w₀).length ∧ (vals ++ w₀).getD (pos p) false = v p := by
      intro p
      obtain ⟨h1, h2⟩ := hv p
      refine ⟨by rw [List.length_append]; omega, ?_⟩
      rw [List.getD_append vals w₀ false (pos p) h1]
      exact h2
    obtain ⟨w₁, hrun₁, hlen₁, hval₁⟩ :=
      ih (vals ++ w₀) (fun t' ht' => hV t' (List.mem_cons_of_mem t ht')) hv'
    refine ⟨w₀ ++ w₁, ?_, ?_, ?_⟩
    · show runFrom x vals (slotW pos V vals.length t ++ layerW pos V (vals.length + V) ts)
        = vals ++ (w₀ ++ w₁)
      rw [runFrom_append, hrun₀,
        show vals.length + V = (vals ++ w₀).length from hL₀.symm, hrun₁, List.append_assoc]
    · rw [List.length_append, hlen₀, hlen₁, List.length_cons, Nat.succ_mul]
      omega
    · intro j
      rcases j with ⟨j, hj⟩
      cases j with
      | zero =>
        have hpos_lt : vals.length + (0 + 1) * V - 1 < (vals ++ w₀).length := by
          rw [hL₀, Nat.one_mul]; omega
        rw [← List.append_assoc, List.getD_append (vals ++ w₀) w₁ false _ hpos_lt]
        show (vals ++ w₀).getD (vals.length + 1 * V - 1) false = weval t v
        rw [Nat.one_mul]
        exact hval₀
      | succ j =>
        have hj' : j < ts.length := by simpa using hj
        have harith : vals.length + (j + 1 + 1) * V - 1
            = (vals ++ w₀).length + (j + 1) * V - 1 := by
          rw [hL₀]
          congr 1
          ring
        rw [← List.append_assoc]
        show ((vals ++ w₀) ++ w₁).getD (vals.length + (j + 1 + 1) * V - 1) false
          = weval ((t :: ts).get ⟨j + 1, hj⟩) v
        rw [harith, List.get_cons_succ]
        exact hval₁ ⟨j, hj'⟩

/-! ### OR-lists, evaluation and volume -/

/-- Right-fold OR of a list of trees. -/
def orListW : List (WTree P) → WTree P
  | [] => .cst false
  | t :: ts => .bin (fun a b => a || b) t (orListW ts)

theorem weval_orListW (l : List (WTree P)) (v : P → Bool) :
    weval (orListW l) v = l.any (fun t => weval t v) := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [orListW, weval, ih]

theorem wvol_orListW (l : List (WTree P)) :
    wvol (orListW l) = (l.map wvol).sum + l.length + 1 := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [orListW, wvol, ih]; omega

/-- Sum of a constant map (volume bookkeeping helper). -/
theorem sum_map_const {α : Type} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Nat.succ_mul]; omega

/-! ### One-hot selection -/

/-- **The one-hot selection lemma.**  An OR of `(h = p) ∧ g p` over all `p < m`
collapses to `g` at the hot index `h`. -/
theorem any_finRange_select {m : ℕ} (h : ℕ) (hh : h < m) (g : Fin m → Bool) :
    ((List.finRange m).any fun p => decide (h = p.val) && g p) = g ⟨h, hh⟩ := by
  cases hg : g ⟨h, hh⟩
  · rw [List.any_eq_false]
    intro p _
    by_cases hph : h = p.val
    · have hpe : p = ⟨h, hh⟩ := Fin.ext hph.symm
      rw [hpe, hg, Bool.and_false]
      simp
    · simp [hph]
  · rw [List.any_eq_true]
    exact ⟨⟨h, hh⟩, List.mem_finRange _, by simp [hg]⟩

/-- One-hot selection at a `Fin`-valued hot index. -/
theorem any_finRange_select_fin {m : ℕ} (h : Fin m) (g : Fin m → Bool) :
    ((List.finRange m).any fun p => decide (h = p) && g p) = g h := by
  cases hg : g h
  · rw [List.any_eq_false]
    intro p _
    by_cases hph : h = p
    · rw [← hph, hg, Bool.and_false]
      simp
    · simp [hph]
  · rw [List.any_eq_true]
    exact ⟨h, List.mem_finRange _, by simp [hg]⟩

/-! ### Closed gates: the initial layer -/

/-- A gate reading no wires. -/
def IsClosedGate : CGate n → Prop
  | .var _ => True
  | .cst _ => True
  | .un _ _ => False
  | .bin _ _ _ => False

/-- The value of a closed gate. -/
def closedEval (x : Fin n → Bool) : CGate n → Bool
  | .var i => x i
  | .cst b => b
  | .un _ _ => false
  | .bin _ _ _ => false

/-- **A closed-gate block appends exactly its values (proved).** -/
theorem runFrom_closed (x : Fin n → Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool), (∀ g ∈ gs, IsClosedGate g) →
      runFrom x vals gs = vals ++ gs.map (closedEval x) := by
  intro gs
  induction gs with
  | nil =>
    intro vals _
    show vals = vals ++ []
    rw [List.append_nil]
  | cons g gs ih =>
    intro vals hcl
    have hg : IsClosedGate g := hcl g List.mem_cons_self
    have hev : evalGate x vals g = closedEval x g := by
      cases g with
      | var i => rfl
      | cst b => rfl
      | un op j => exact hg.elim
      | bin op j k => exact hg.elim
    show runFrom x (vals ++ [evalGate x vals g]) gs
      = vals ++ (closedEval x g :: gs.map (closedEval x))
    rw [hev, ih (vals ++ [closedEval x g]) (fun g' hg' => hcl g' (List.mem_cons_of_mem g hg'))]
    rw [List.append_assoc, List.singleton_append]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.compileW_spec
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.slotW_spec
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.layerW_spec
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.runFrom_closed
