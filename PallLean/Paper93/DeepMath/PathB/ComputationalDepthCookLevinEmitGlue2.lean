import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitGlue

/-!
# Cook–Levin M2 emitter — E6 step 9: THE SATISFIABILITY GLUE

The two eval-level halves over `emittedFormula`:

* **Forward (`emittedFormula_sound`)** — the real-run assignment satisfies every emitted
  clause.  The dynamics extras need NO head bound: `dynamicsClause_sound` is unconditional in
  `(t, p)`, so the left-mover's shifted windows (including the spurious `p = P + 1` one) and
  the `p = 0` one-shots are all members of sound two-clause formulas.
* **Backward (`emittedFormula_tableau`)** — any satisfying assignment of `emittedFormula`
  satisfies the tableau's `assembledFormula`, the accept clause, the write family, and the two
  init units: the one-hot families reassemble from loop + top blocks (through the emission
  permutation), and every `dynamicsClause` member is located inside `dynAFormula`/`dynBFormula`
  (non-left directly; left movers: state window at `p`, head member at `p = 0` from the
  one-shots, at `p ≥ 1` from the shifted window of round `p − 1`).

With `masterOut2_encode`, this ties the machine's output stream to `fullTableau`'s
satisfiability — only the init-cell clauses (their own emitter, brick 27) stay outside.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue2

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTriangleHead
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue

/-! ## Forward: the real-run assignment satisfies every emitted clause -/

theorem dynQBF_sound (M : Machine) (x : List Bool) (t : ℕ)
    (q : Fin (Fintype.card M.State)) (b : Bool) (k : ℕ) :
    evalFormula (fullAssign M x) (dynQBF M t q b k) = true := by
  by_cases h0 : mvN M q.val b = 0
  · rw [dynQBF, if_pos h0]
    have h1 := dynamicsClause_sound M x t q k b
    have h2 := dynamicsClause_sound M x t q (k + 1) b
    simp only [dynamicsClause, evalFormula, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨h1.1, h2.2⟩
  · rw [dynQBF, if_neg h0]
    exact dynamicsClause_sound M x t q k b

theorem leftFq_sound (M : Machine) (x : List Bool) (t : ℕ)
    (q : Fin (Fintype.card M.State)) (b : Bool) :
    evalFormula (fullAssign M x) (leftFq M t q b) = true := by
  by_cases h0 : mvN M q.val b = 0
  · rw [leftFq, if_pos h0]
    have h2 := dynamicsClause_sound M x t q 0 b
    simp only [dynamicsClause, evalFormula, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h2 ⊢
    exact h2.2
  · rw [leftFq, if_neg h0]
    rfl

theorem dynAFormula_sound (M : Machine) (x : List Bool) (P B : ℕ) :
    evalFormula (fullAssign M x) (dynAFormula M P B) = true := by
  rw [dynAFormula, bigAnd_map_iff]
  intro t _
  rw [bigAnd_map_iff]
  intro q _
  rw [bigAnd_map_iff]
  intro k _
  rw [evalFormula_append, Bool.and_eq_true]
  exact ⟨dynQBF_sound M x t q false k, dynQBF_sound M x t q true k⟩

theorem dynBFormula_sound (M : Machine) (x : List Bool) (B : ℕ) :
    evalFormula (fullAssign M x) (dynBFormula M B) = true := by
  rw [dynBFormula, bigAnd_map_iff]
  intro t _
  rw [bigAnd_map_iff]
  intro q _
  rw [evalFormula_append, Bool.and_eq_true]
  exact ⟨leftFq_sound M x t q false, leftFq_sound M x t q true⟩

/-- **Forward soundness**: an accepting, head-bounded run satisfies the whole emission. -/
theorem emittedFormula_sound (M : Machine) (x : List Bool) (P B : ℕ)
    (hb : ∀ t, t ≤ B → (run M t (init M x)).hd ≤ P)
    (hhalt : M.halt (run M B (init M x)).st = true)
    (hacc : M.accept (run M B (init M x)).st = true) :
    evalFormula (fullAssign M x) (emittedFormula M P B) = true := by
  simp only [emittedFormula, evalFormula_append, Bool.and_eq_true]
  refine ⟨tapeFamily_sound M x P B, writeFamily_sound M x P B,
    dynAFormula_sound M x P B, ?_, ?_, dynBFormula_sound M x B,
    stateOneHot_sound M x B, ?_, acceptFormula_sound M x B hhalt hacc, ?_⟩
  · rw [bigAnd_map_iff]
    intro t ht
    rw [evalFormula_perm _ (headOneHotEmit_perm t P)]
    exact headOneHot_sound M x t P (hb t (by rw [List.mem_range] at ht; omega))
  · rw [bigAnd_map_iff]
    intro t _
    exact stateOneHot_sound M x t
  · rw [evalFormula_perm _ (headOneHotEmit_perm B P)]
    exact headOneHot_sound M x B P (hb B (le_refl B))
  · rw [show ([[(stateVar 0 (Fintype.equivFin M.State M.start).val, true)],
        [(headVar 0 0, true)]] : Formula)
      = fixBits [(stateVar 0 (Fintype.equivFin M.State M.start).val, true),
          (headVar 0 0, true)] from rfl, fixBits_iff]
    intro pr hpr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
    rcases hpr with rfl | rfl
    · exact init_state_sat M x
    · exact init_head_sat M x

/-! ## Backward: the emission implies the tableau -/

theorem emitted_dynamics (M : Machine) (P B : ℕ) (a : ℕ → Bool)
    (hA : evalFormula a (dynAFormula M P B) = true)
    (hB : evalFormula a (dynBFormula M B) = true) :
    evalFormula a (dynamicsFamily M P B) = true := by
  rw [dynamicsFamily, bigAnd_map_iff]
  intro t ht
  rw [bigAnd_map_iff]
  intro q hq
  rw [bigAnd_map_iff]
  intro p hp
  rw [bigAnd_map_iff]
  intro b _
  rw [dynAFormula, bigAnd_map_iff] at hA
  have hAt := hA t ht
  rw [bigAnd_map_iff] at hAt
  have hAq := hAt q hq
  rw [bigAnd_map_iff] at hAq
  rw [dynBFormula, bigAnd_map_iff] at hB
  have hBt := hB t ht
  rw [bigAnd_map_iff] at hBt
  have hBq := hBt q hq
  rw [evalFormula_append, Bool.and_eq_true] at hBq
  by_cases h0 : mvN M q.val b = 0
  · have hkp := hAq p hp
    rw [evalFormula_append, Bool.and_eq_true] at hkp
    have hqb : evalFormula a (dynQBF M t q b p) = true := by
      cases b
      · exact hkp.1
      · exact hkp.2
    rw [dynQBF, if_pos h0] at hqb
    simp only [evalFormula, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hqb
    have hm2 : evalClause a (implClause (stateVar t q.val, true) (headVar t p, true)
        (cellVar t p, b) (headVar (t + 1) (nextHead M q p b), true)) = true := by
      rcases p with _ | p'
      · have hbq : evalFormula a (leftFq M t q b) = true := by
          cases b
          · exact hBq.1
          · exact hBq.2
        rw [leftFq, if_pos h0] at hbq
        simp only [evalFormula, List.all_cons, List.all_nil, Bool.and_true] at hbq
        exact hbq
      · have hkp' := hAq p' (by rw [List.mem_range] at hp ⊢; omega)
        rw [evalFormula_append, Bool.and_eq_true] at hkp'
        have hqb' : evalFormula a (dynQBF M t q b p') = true := by
          cases b
          · exact hkp'.1
          · exact hkp'.2
        rw [dynQBF, if_pos h0] at hqb'
        simp only [evalFormula, List.all_cons, List.all_nil, Bool.and_true,
          Bool.and_eq_true] at hqb'
        exact hqb'.2
    simp only [dynamicsClause, evalFormula, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true]
    exact ⟨hqb.1, hm2⟩
  · have hkp := hAq p hp
    rw [evalFormula_append, Bool.and_eq_true] at hkp
    have hqb : evalFormula a (dynQBF M t q b p) = true := by
      cases b
      · exact hkp.1
      · exact hkp.2
    rw [dynQBF, if_neg h0] at hqb
    exact hqb

theorem emitted_head (P B : ℕ) (a : ℕ → Bool)
    (hLoop : evalFormula a (bigAnd ((List.range B).map
      (fun t => headOneHotEmit t P))) = true)
    (hTop : evalFormula a (headOneHotEmit B P) = true) :
    evalFormula a (headFamily P B) = true := by
  rw [headFamily, bigAnd_map_iff]
  intro t ht
  rw [List.mem_range] at ht
  rw [← evalFormula_perm a (headOneHotEmit_perm t P)]
  by_cases htB : t < B
  · rw [bigAnd_map_iff] at hLoop
    exact hLoop t (List.mem_range.mpr htB)
  · have hEq : t = B := by omega
    subst hEq
    exact hTop

theorem emitted_state (M : Machine) (B : ℕ) (a : ℕ → Bool)
    (hLoop : evalFormula a (bigAnd ((List.range B).map
      (fun t => stateOneHot M t))) = true)
    (hTop : evalFormula a (stateOneHot M B) = true) :
    evalFormula a (stateFamily M B) = true := by
  rw [stateFamily, bigAnd_map_iff]
  intro t ht
  rw [List.mem_range] at ht
  by_cases htB : t < B
  · rw [bigAnd_map_iff] at hLoop
    exact hLoop t (List.mem_range.mpr htB)
  · have hEq : t = B := by omega
    subst hEq
    exact hTop

/-- **Backward**: any satisfying assignment of the emission satisfies the tableau's assembled
transition families, the accept clause, the write family, and the two init units. -/
theorem emittedFormula_tableau (M : Machine) (P B : ℕ) (a : ℕ → Bool)
    (h : evalFormula a (emittedFormula M P B) = true) :
    evalFormula a (assembledFormula M P B) = true
    ∧ evalFormula a (acceptFormula M B) = true
    ∧ evalFormula a (writeFamily M P B) = true
    ∧ a (stateVar 0 (Fintype.equivFin M.State M.start).val) = true
    ∧ a (headVar 0 0) = true := by
  simp only [emittedFormula, evalFormula_append, Bool.and_eq_true] at h
  obtain ⟨hTape, hWrite, hDynA, hHeadL, hStateL, hDynB, hStateT, hHeadT, hAcc, hUnits⟩ := h
  rw [show ([[(stateVar 0 (Fintype.equivFin M.State M.start).val, true)],
      [(headVar 0 0, true)]] : Formula)
    = fixBits [(stateVar 0 (Fintype.equivFin M.State M.start).val, true),
        (headVar 0 0, true)] from rfl, fixBits_iff] at hUnits
  refine ⟨?_, hAcc, hWrite, hUnits _ List.mem_cons_self,
    hUnits _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  rw [assembledFormula]
  simp only [evalFormula_append, Bool.and_eq_true]
  exact ⟨⟨⟨emitted_head P B a hHeadL hHeadT, emitted_state M B a hStateL hStateT⟩,
    hTape⟩, emitted_dynamics M P B a hDynA hDynB⟩

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue2
