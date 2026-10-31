import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinTransition

/-!
# Cook–Levin M2 — the state/head one-hot window (well-formedness, with soundness)

The transition window represents the head and state of each row as **one-hot** vectors: at every time exactly one
head position and exactly one state bit is on.  The dynamics clause (next state/head match `δ`) for an arbitrary
`State` + `δ`-table is the deferred fiddly remainder; its self-contained, provable companion — built here — is the
**one-hot well-formedness**: the assignment that reads the *real run* off the tableau variables satisfies the head
and state one-hot constraints.

The head part is a `ℕ`-position one-hot; the state part uses `State ≃ Fin (card)` (`Fintype.equivFin`) to index the
finite, arbitrary state set.  Both soundnesses cash out to "a configuration has a unique head and a unique state,"
via the `oneHot` primitive and the injective variable scheme.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex

/-- The state bit `s[t][q]`: "the state at time `t` is the `q`-th state" (`q` indexing via `State ≃ Fin card`). -/
noncomputable def stateBit (M : Machine) (x : List Bool) (t q : ℕ) : Bool :=
  if h : q < Fintype.card M.State then
    decide ((run M t (init M x)).st = (Fintype.equivFin M.State).symm ⟨q, h⟩)
  else false

/-- The trace-reading assignment for all three families: cell = the tape cell, head = "head at `p`", state = the
`q`-th-state bit. -/
noncomputable def fullAssign (M : Machine) (x : List Bool) (v : ℕ) : Bool :=
  if v % 3 = 0 then (run M (Nat.unpair (v / 3)).1 (init M x)).tp.getD (Nat.unpair (v / 3)).2 false
  else if v % 3 = 1 then decide ((run M (Nat.unpair (v / 3)).1 (init M x)).hd = (Nat.unpair (v / 3)).2)
  else stateBit M x (Nat.unpair (v / 3)).1 (Nat.unpair (v / 3)).2

theorem fullAssign_head (M : Machine) (x : List Bool) (t p : ℕ) :
    fullAssign M x (headVar t p) = decide ((run M t (init M x)).hd = p) := by
  unfold fullAssign headVar
  rw [show (3 * Nat.pair t p + 1) % 3 = 1 from by omega,
    show (3 * Nat.pair t p + 1) / 3 = Nat.pair t p from by omega, Nat.unpair_pair]
  simp

theorem fullAssign_state (M : Machine) (x : List Bool) (t q : ℕ) :
    fullAssign M x (stateVar t q) = stateBit M x t q := by
  unfold fullAssign stateVar
  rw [show (3 * Nat.pair t q + 2) % 3 = 2 from by omega,
    show (3 * Nat.pair t q + 2) / 3 = Nat.pair t q from by omega, Nat.unpair_pair]
  simp

/-! ## The head one-hot -/

/-- The head one-hot at time `t` over positions `[0, P]`. -/
def headOneHot (t P : ℕ) : Formula := oneHot ((List.range (P + 1)).map (headVar t))

/-- **Head one-hot soundness.**  If the real head at time `t` is within `[0, P]`, the trace assignment satisfies the
head one-hot — exactly the head's position is on. -/
theorem headOneHot_sound (M : Machine) (x : List Bool) (t P : ℕ)
    (hle : (run M t (init M x)).hd ≤ P) :
    evalFormula (fullAssign M x) (headOneHot t P) = true := by
  rw [headOneHot, oneHot_iff]
  refine ⟨⟨headVar t (run M t (init M x)).hd, ?_, ?_⟩, ?_⟩
  · exact List.mem_map.mpr ⟨(run M t (init M x)).hd, List.mem_range.mpr (by omega), rfl⟩
  · rw [fullAssign_head]; simp
  · rw [List.pairwise_map]
    refine List.nodup_range.imp (fun {p p'} hne => ?_)
    rw [fullAssign_head, fullAssign_head]
    by_cases h : (run M t (init M x)).hd = p
    · exact Or.inr (decide_eq_false (by rw [h]; exact hne))
    · exact Or.inl (decide_eq_false h)

/-! ## The state one-hot -/

/-- The state one-hot at time `t` over the `card` state indices. -/
def stateOneHot (M : Machine) (t : ℕ) : Formula :=
  oneHot ((List.range (Fintype.card M.State)).map (stateVar t))

/-- **State one-hot soundness.**  The trace assignment always satisfies the state one-hot — exactly the run's actual
state (indexed via `State ≃ Fin card`) is on. -/
theorem stateOneHot_sound (M : Machine) (x : List Bool) (t : ℕ) :
    evalFormula (fullAssign M x) (stateOneHot M t) = true := by
  rw [stateOneHot, oneHot_iff]
  refine ⟨⟨stateVar t (Fintype.equivFin M.State (run M t (init M x)).st), ?_, ?_⟩, ?_⟩
  · exact List.mem_map.mpr ⟨_, List.mem_range.mpr (Fin.isLt _), rfl⟩
  · rw [fullAssign_state, stateBit, dif_pos (Fin.isLt _)]
    simp [Equiv.symm_apply_apply]
  · rw [List.pairwise_map]
    refine List.nodup_range.imp (fun {q q'} hne => ?_)
    rw [fullAssign_state, fullAssign_state, stateBit, stateBit]
    by_cases hq : q < Fintype.card M.State
    · by_cases hq' : q' < Fintype.card M.State
      · rw [dif_pos hq, dif_pos hq']
        by_cases hst : (run M t (init M x)).st = (Fintype.equivFin M.State).symm ⟨q, hq⟩
        · refine Or.inr (decide_eq_false (fun hst' => hne ?_))
          have : (Fintype.equivFin M.State).symm ⟨q, hq⟩ = (Fintype.equivFin M.State).symm ⟨q', hq'⟩ :=
            hst ▸ hst'
          have := (Fintype.equivFin M.State).symm.injective this
          exact Fin.mk.injEq .. ▸ this
        · exact Or.inl (decide_eq_false hst)
      · exact Or.inr (by rw [dif_neg hq'])
    · exact Or.inl (by rw [dif_neg hq])

end PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
