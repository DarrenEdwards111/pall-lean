import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSimultaneousTrackingCost

/-!
# N-Frame: dead-gate elimination — Normal Form IV

The last structural surgery: a gate whose wire nothing above it reads is deleted by pure re-indexing — no
absorption, because there is nothing to absorb into.

  `elimDeadGate` / `computes_elim_dead` — **PROVED, the surgery**: delete an interior gate none of whose
        successors read it; every later reference shifts down, garbage references below stay garbage, and
        the circuit computes the same function with one gate fewer.
  `minimal_wire_read` — **PROVED, Normal Form IV**: in a minimal circuit, every interior wire is read by
        some later gate.  With Normal Forms I–III (no constants, unary only at the output, binary gates
        bidependent), the anatomy of minimal DAG observers is complete: interiors are `var`/`bin`-pure,
        genuinely two-input, and fully consumed.

## Honest scope

This completes the structural side of the campaign.  In particular the mediation tower now has no dead ends:
every mediator wire's own wire is read again above it, so tracked obligations propagate upward through live
gates only.  The one open statement is unchanged — the semantic closing inequality of the vise.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The surgery -/

/-- Re-index after deleting the unread position `p` — no absorption needed. -/
def elimDeadGate {n : ℕ} (p : ℕ) : CGate n → CGate n
  | .var i => .var i
  | .cst c => .cst c
  | .un op j => .un op (elimRef p j)
  | .bin op j k => .bin op (elimRef p j) (elimRef p k)

theorem evalGate_elimDead {n : ℕ} (x : Fin n → Bool) (vals : List Bool) (p : ℕ)
    (g : CGate n) (hg : readsWire p g = false) :
    evalGate x (vals.eraseIdx p) (elimDeadGate p g) = evalGate x vals g := by
  cases g with
  | var i => rfl
  | cst c => rfl
  | un op j =>
    have hj : j ≠ p := by
      intro h
      rw [h] at hg
      simp [readsWire] at hg
    show op ((vals.eraseIdx p).getD (elimRef p j) false) = op (vals.getD j false)
    rw [getD_eraseIdx_elimRef vals p j hj]
  | bin op j k =>
    have hj : j ≠ p := by
      intro h
      rw [h] at hg
      simp [readsWire] at hg
    have hk : k ≠ p := by
      intro h
      rw [h] at hg
      simp [readsWire] at hg
    show op ((vals.eraseIdx p).getD (elimRef p j) false)
        ((vals.eraseIdx p).getD (elimRef p k) false)
      = op (vals.getD j false) (vals.getD k false)
    rw [getD_eraseIdx_elimRef vals p j hj, getD_eraseIdx_elimRef vals p k hk]

theorem runFrom_elimDead {n : ℕ} (x : Fin n → Bool) (p : ℕ) :
    ∀ (gs : List (CGate n)) (vals : List Bool), p < vals.length →
      (∀ g ∈ gs, readsWire p g = false) →
      runFrom x (vals.eraseIdx p) (gs.map (elimDeadGate p))
        = (runFrom x vals gs).eraseIdx p := by
  intro gs
  induction gs with
  | nil => intro vals _ _; rfl
  | cons g rest ih =>
    intro vals hp hread
    show runFrom x (vals.eraseIdx p ++ [evalGate x (vals.eraseIdx p) (elimDeadGate p g)])
        (rest.map (elimDeadGate p))
        = (runFrom x (vals ++ [evalGate x vals g]) rest).eraseIdx p
    rw [evalGate_elimDead x vals p g (hread g List.mem_cons_self)]
    rw [← List.eraseIdx_append_of_lt_length hp [evalGate x vals g]]
    exact ih (vals ++ [evalGate x vals g])
      (by rw [List.length_append]; show p < vals.length + 1; omega)
      (fun g' hg' => hread g' (List.mem_cons_of_mem g hg'))

/-- **The dead-gate surgery (proved)**: an interior gate read by no successor is deleted by re-indexing. -/
theorem computes_elim_dead {n : ℕ} (c₁ c₂ : List (CGate n)) (g : CGate n)
    (f : (Fin n → Bool) → Bool) (hcomp : computes (c₁ ++ g :: c₂) f) (hne : c₂ ≠ [])
    (hnoread : ∀ g' ∈ c₂, readsWire c₁.length g' = false) :
    computes (c₁ ++ c₂.map (elimDeadGate c₁.length)) f := by
  have hc2 : 1 ≤ c₂.length := by
    cases c₂ with
    | nil => exact absurd rfl hne
    | cons a l => show 1 ≤ l.length + 1; omega
  intro x
  have hx := hcomp x
  have hV : (runFrom x [] c₁).length = c₁.length := by
    rw [runFrom_length]
    simp
  set v₀ : Bool := evalGate x (runFrom x [] c₁) g with hv₀
  have hsplit : runFrom x [] (c₁ ++ g :: c₂)
      = runFrom x (runFrom x [] c₁ ++ [v₀]) c₂ := by
    rw [show c₁ ++ g :: c₂ = (c₁ ++ [g]) ++ c₂ by simp, runFrom_append, runFrom_append]
    rfl
  have hVe : (runFrom x [] c₁ ++ [v₀]).eraseIdx c₁.length = runFrom x [] c₁ := by
    rw [List.eraseIdx_append_of_length_le (le_of_eq hV) [v₀]]
    rw [show c₁.length - (runFrom x [] c₁).length = 0 by omega]
    rw [show ([v₀] : List Bool).eraseIdx 0 = ([] : List Bool) from rfl, List.append_nil]
  have hnew : runFrom x (runFrom x [] c₁) (c₂.map (elimDeadGate c₁.length))
      = (runFrom x (runFrom x [] c₁ ++ [v₀]) c₂).eraseIdx c₁.length := by
    have h1 := runFrom_elimDead x c₁.length c₂ (runFrom x [] c₁ ++ [v₀])
      (by rw [List.length_append, hV]; show c₁.length < c₁.length + 1; omega) hnoread
    rw [hVe] at h1
    exact h1
  show (runFrom x [] (c₁ ++ c₂.map (elimDeadGate c₁.length))).getD
      ((c₁ ++ c₂.map (elimDeadGate c₁.length)).length - 1) false = f x
  rw [runFrom_append, hnew]
  rw [show (c₁ ++ c₂.map (elimDeadGate c₁.length)).length = c₁.length + c₂.length by
    rw [List.length_append, List.length_map]]
  rw [getD_eraseIdx_ge _ c₁.length (c₁.length + c₂.length - 1) (by omega)]
  rw [show c₁.length + c₂.length - 1 + 1 = c₁.length + c₂.length by omega]
  have hxold : (runFrom x (runFrom x [] c₁ ++ [v₀]) c₂).getD
      ((c₁ ++ g :: c₂).length - 1) false = f x := by
    rw [← hsplit]
    exact hx
  rw [show (c₁ ++ g :: c₂).length - 1 = c₁.length + c₂.length by
    rw [List.length_append, List.length_cons]; omega] at hxold
  exact hxold

/-! ### Normal Form IV -/

/-- **NORMAL FORM IV (proved)**: in a minimal circuit, every interior wire is read by some later gate. -/
theorem minimal_wire_read {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (p : ℕ) (hp : p < c.length - 1) :
    ∃ q, p < q ∧ readsWire p (c.getD q (CGate.cst false)) = true := by
  by_contra hno
  push_neg at hno
  have hsplit := circuit_split_at c p (by omega)
  have hcomp' : computes (c.take p ++ c.getD p (CGate.cst false) :: c.drop (p + 1)) f := by
    rw [← hsplit]
    exact hcomp
  have htlen : (c.take p).length = p := take_len c p (by omega)
  have hdne : c.drop (p + 1) ≠ [] := by
    intro hcon
    have h := congrArg List.length hcon
    rw [List.length_drop] at h
    simp at h
    omega
  have hnoread : ∀ g' ∈ c.drop (p + 1), readsWire (c.take p).length g' = false := by
    intro g' hg'
    obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hg'
    have hq : g' = c.getD (p + 1 + idx) (CGate.cst false) := by
      rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop, List.getElem?_eq_getElem hidx]
      exact hget.symm
    rw [htlen, hq]
    cases h3 : readsWire p (c.getD (p + 1 + idx) (CGate.cst false)) with
    | false => rfl
    | true => exact absurd h3 (hno (p + 1 + idx) (by omega))
  have hres := computes_elim_dead (c.take p) (c.drop (p + 1))
    (c.getD p (CGate.cst false)) f hcomp' hdne hnoread
  have hb : cbudget f ≤ (c.take p ++ (c.drop (p + 1)).map
      (elimDeadGate (c.take p).length)).length := Nat.sInf_le ⟨_, hres, rfl⟩
  rw [List.length_append, List.length_map, List.length_drop, htlen] at hb
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.computes_elim_dead
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.minimal_wire_read
