import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTrackedPortContexts

/-!
# N-Frame: selector tracked contexts — the workhorse eval for slot-2 flips, and the selector lift

The named next rung, built: the evaluation lemma for the empty-designated-block context with a single
slot-2 literal, and with it the selector version of the context lift.

  `sat3_selector_workhorse_eval` — **PROVED, the eval**: at any pin context, with the designated block empty
        except the flipped slot-2 selector on an *unpinned* variable, SAT reads exactly the flip: on = `true`
        (the free variable satisfies the lone literal, pins and tautologies carry the rest), off = `false`
        (empty clause).
  `sat3_selector_port_tracks_contexts` — **PROVED, the selector lift**: a mediated slot-2 selector on an
        unpinned variable has its mediator wire flip at **every one** of the `2^(m−2)` pin contexts — the
        selector version of the family tracking, unconditional across the whole context cube.

## Honest scope

For pinned variables (`j < m−2`) the flip value is `bvec j`, so sensitivity holds on the half-cube
`bvec j = true` — the unpinned case (`m−2 ≤ j < v`, plentiful since `m ≈ √N/3 ≪ v = √N`) gives the clean
unconditional family and suffices for the aggregate.  The standing face is unchanged: obligations are flips,
pass-through satisfies them at unit cost, and the open charge is *simultaneous* satisfaction of many
coordinates' obligation families through shared budget-priced wires.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

theorem sat3Bit_ne_of_slot {n₀ : ℕ} {c c' : Fin (sat3M n₀)} {t t' : Fin 3} {f f' : ℕ}
    (hf : f < sat3V n₀ + 1) (hf' : f' < sat3V n₀ + 1) (h : t ≠ t') :
    sat3Bit n₀ c t f hf ≠ sat3Bit n₀ c' t' f' hf' :=
  fun hcon => h (sat3Bit_inj n₀ hf hf' hcon).2.1

/-- **THE SELECTOR WORKHORSE (proved)**: empty designated block, single slot-2 literal on an unpinned
variable — SAT reads exactly the flip, at every pin context. -/
theorem sat3_selector_workhorse_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N)) (hjv : sat3M N - 2 ≤ j.val)
    (bvec : Fin (sat3M N - 2) → Bool) :
    sat3Family N (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
      (fun _ => false)) (sat3S2Sel N cIdx j) true) = true ∧
    sat3Family N (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
      (fun _ => false)) (sat3S2Sel N cIdx j) false) = false := by
  classical
  constructor
  · -- ON: the free variable satisfies the lone literal; pins and tautologies carry the rest
    apply sat3Family_of_witness N _
      (fun jj => if h : jj.val < sat3M N - 2 then bvec ⟨jj.val, h⟩ else true)
    apply sat3Eval_true_of_all
    intro cl
    by_cases hcl : cl = cIdx
    · subst hcl
      refine ⟨⟨2, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨2, by omega⟩ j ?_ ?_⟩
      · show Function.update (sat3Patch N cl (sat3Context N cl hk bvec) (fun _ => false))
            (sat3S2Sel N cl j) true (sat3S2Sel N cl j) = true
        rw [Function.update_self]
      · have hne : sat3Bit N cl ⟨2, by omega⟩ (sat3V N) (by omega) ≠ sat3S2Sel N cl j :=
          sat3Bit_ne_of_field N _ _ _ _ (by have := j.isLt; omega)
        rw [Function.update_of_ne hne]
        rw [sat3Patch_own N cl _ _ ⟨2, by omega⟩ (sat3V N) (by omega)]
        show xor (if h : j.val < sat3M N - 2 then bvec ⟨j.val, h⟩ else true) false = true
        rw [dif_neg (by omega)]
        rfl
    · have hclv : cl.val ≠ cIdx.val := fun h => hcl (Fin.ext h)
      by_cases hpin : ∃ j' : Fin (sat3M N - 2), sat3PinClause N cIdx hk j' = cl
      · -- pin clause: the forced literal is satisfied
        obtain ⟨j', rfl⟩ := hpin
        have hjlt : j'.val < sat3V N := by have := j'.isLt; omega
        refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N _ _ _ ⟨0, by omega⟩
          ⟨j'.val, hjlt⟩ ?_ ?_⟩
        · have hne : sat3Bit N (sat3PinClause N cIdx hk j') ⟨0, by omega⟩
              (⟨j'.val, hjlt⟩ : Fin (sat3V N)).val (by omega) ≠ sat3S2Sel N cIdx j :=
            sat3Bit_ne_of_clause N _ _ _ _
              (fun h => sat3PinClause_ne N cIdx hk j' h)
          rw [Function.update_of_ne hne]
          exact pin_read_sel N cIdx hk hkv bvec _ j'
        · have hne : sat3Bit N (sat3PinClause N cIdx hk j') ⟨0, by omega⟩ (sat3V N)
              (by omega) ≠ sat3S2Sel N cIdx j :=
            sat3Bit_ne_of_clause N _ _ _ _
              (fun h => sat3PinClause_ne N cIdx hk j' h)
          rw [Function.update_of_ne hne]
          rw [pin_read_sign N cIdx hk hkv bvec _ j']
          show xor (if h : j'.val < sat3M N - 2 then bvec ⟨j'.val, h⟩ else true)
              (decide (bvec j' = false)) = true
          rw [dif_pos j'.isLt]
          have hb : bvec ⟨j'.val, j'.isLt⟩ = bvec j' := by
            congr 1
          rw [hb]
          cases bvec j' <;> rfl
      · -- tautology clause: satisfied by either slot, depending on the assignment's bit 0
        push_neg at hpin
        have hnp : ∀ j' : Fin (sat3M N - 2),
            cl.val ≠ (sat3PinClause N cIdx hk j').val :=
          fun j' h => hpin j' (Fin.ext h.symm)
        have hread : ∀ (t : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
            Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
              (fun _ => false)) (sat3S2Sel N cIdx j) true (sat3Bit N cl t fI hfI)
            = sat3Context N cIdx hk bvec (sat3Bit N cl t fI hfI) := by
          intro t fI hfI
          have hne : sat3Bit N cl t fI hfI ≠ sat3S2Sel N cIdx j :=
            sat3Bit_ne_of_clause N _ _ _ _ hclv
          rw [Function.update_of_ne hne]
          exact sat3Patch_out N cIdx _ _ cl (fun h => hcl h) t fI hfI
        by_cases ha0 : (if h : (0 : ℕ) < sat3M N - 2 then bvec ⟨0, h⟩ else true) = true
        · -- slot 0: positive literal on variable 0
          refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩
            ⟨0, hv⟩ ?_ ?_⟩
          · rw [hread ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)]
            show decide _ = true
            rw [decide_eq_true_eq]
            refine Or.inr ⟨?_, ?_, ?_, Or.inl ?_⟩
            · rw [sat3Bit_clause]
              exact cl.isLt
            · rw [sat3Bit_clause]
              exact hclv
            · intro j'
              rw [sat3Bit_clause]
              exact hnp j'
            · rw [sat3Bit_rem]
              show (0 : ℕ) * (sat3V N + 1) + 0 = 0
              omega
          · rw [hread ⟨0, by omega⟩ (sat3V N) (by omega)]
            have hsg : sat3Context N cIdx hk bvec
                (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
              show decide _ = false
              rw [decide_eq_false_iff_not]
              rintro (⟨j', hdiv, hrem⟩ | ⟨-, -, -, hrem⟩)
              · rw [sat3Bit_clause] at hdiv
                exact hnp j' hdiv
              · rcases hrem with h | h | h <;> rw [sat3Bit_rem] at h
                · have h' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 0 := h
                  omega
                · have h' : (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 := h
                  omega
                · have h' : (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 + sat3V N := h
                  omega
            rw [hsg, ha0]
            rfl
        · -- slot 1: negative literal on variable 0
          have ha0' : (if h : (0 : ℕ) < sat3M N - 2 then bvec ⟨0, h⟩ else true) = false :=
            Bool.eq_false_iff.mpr ha0
          refine ⟨⟨1, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨1, by omega⟩
            ⟨0, hv⟩ ?_ ?_⟩
          · rw [hread ⟨1, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)]
            show decide _ = true
            rw [decide_eq_true_eq]
            refine Or.inr ⟨?_, ?_, ?_, Or.inr (Or.inl ?_)⟩
            · rw [sat3Bit_clause]
              exact cl.isLt
            · rw [sat3Bit_clause]
              exact hclv
            · intro j'
              rw [sat3Bit_clause]
              exact hnp j'
            · rw [sat3Bit_rem]
              show (1 : ℕ) * (sat3V N + 1) + 0 = sat3V N + 1
              omega
          · rw [hread ⟨1, by omega⟩ (sat3V N) (by omega)]
            have hsg : sat3Context N cIdx hk bvec
                (sat3Bit N cl ⟨1, by omega⟩ (sat3V N) (by omega)) = true := by
              show decide _ = true
              rw [decide_eq_true_eq]
              refine Or.inr ⟨?_, ?_, ?_, Or.inr (Or.inr ?_)⟩
              · rw [sat3Bit_clause]
                exact cl.isLt
              · rw [sat3Bit_clause]
                exact hclv
              · intro j'
                rw [sat3Bit_clause]
                exact hnp j'
              · rw [sat3Bit_rem]
                show (1 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 + sat3V N
                omega
            rw [hsg, ha0']
            rfl
  · -- OFF: the designated clause is empty
    apply sat3Family_false_of_empty_clause N _ cIdx
    intro t i
    by_cases hb : sat3Bit N cIdx t i.val (by have := i.isLt; omega) = sat3S2Sel N cIdx j
    · rw [hb, Function.update_self]
    · rw [Function.update_of_ne hb]
      rw [sat3Patch_own N cIdx _ _ t i.val (by have := i.isLt; omega)]

/-- **THE SELECTOR LIFT (proved)**: a mediated slot-2 selector on an unpinned variable has its mediator wire
flip at every one of the `2^(m−2)` pin contexts. -/
theorem sat3_selector_port_tracks_contexts (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N)) (hjv : sat3M N - 2 ≤ j.val)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N)) (p r : ℕ)
    (hmed : MediatedAt c (sat3S2Sel N cIdx j) p r) :
    ∀ bvec : Fin (sat3M N - 2) → Bool,
      (runFrom (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
          (fun _ => false)) (sat3S2Sel N cIdx j) true) [] c).getD r false
      ≠ (runFrom (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
          (fun _ => false)) (sat3S2Sel N cIdx j) false) [] c).getD r false := by
  intro bvec
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  obtain ⟨hon, hoff⟩ := sat3_selector_workhorse_eval N hv hk hkv cIdx j hjv bvec
  have hsens : sat3Family N (Function.update (sat3Patch N cIdx
        (sat3Context N cIdx hk bvec) (fun _ => false)) (sat3S2Sel N cIdx j) true)
      ≠ sat3Family N (Function.update (sat3Patch N cIdx
        (sat3Context N cIdx hk bvec) (fun _ => false)) (sat3S2Sel N cIdx j) false) := by
    rw [hon, hoff]
    decide
  have h := slice_ports_must_flip (sat3Family N) c hcomp
    [(⟨sat3S2Sel N cIdx j, p, r⟩ : Fin N × ℕ × ℕ)]
    (by
      intro t' ht'
      rw [List.mem_singleton] at ht'
      subst ht'
      exact hmed)
    (⟨sat3S2Sel N cIdx j, p, r⟩ : Fin N × ℕ × ℕ) List.mem_cons_self
    (sat3Patch N cIdx (sat3Context N cIdx hk bvec) (fun _ => false)) hsens
  obtain ⟨t', ht', hflip⟩ := h
  rw [List.mem_singleton] at ht'
  subst ht'
  exact hflip

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_workhorse_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_port_tracks_contexts
