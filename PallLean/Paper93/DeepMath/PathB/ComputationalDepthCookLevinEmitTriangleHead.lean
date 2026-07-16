import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitInterGrand

/-!
# Cook–Levin M2 emitter — THE TRIANGLE CASHES OUT: the head at-most-one stream

The triangle engine meets the tableau.  The reindexed pair body `amoPairRowHeadBody` emits, at
row `j` and inner round `k`, exactly `encodeClause' [(headVar t k, F), (headVar t j, F)]` — so
`rep_triangle_run` instantiated with it emits `⋃_{t<B} ⋃_{1≤j≤P} ⋃_{k<j}` of the head one-hot's
at-most-one pair clauses, all times, ONE machine (`rep_triangleHead_run`).

The triangle enumerates the pairs by their **larger** coordinate (TRIANGLE_PLAN.md's reindexing
— forced by the grand loop's fixed row count), while the tableau's `atMostOne` enumerates by
the **smaller**.  The two streams are clause-for-clause the same family in a different order:
`amoTriHead_perm` proves the `List.Perm`, and `evalFormula_perm`/`satisfiable_perm` show
satisfaction is blind to the order — the same free-serialisation choice as the coordinate
codec (SCOPE_EMITTER.md E0), to be consumed by the primed target `EmitsTableau'`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitTriangleHead

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterGrand

/-! ## The reindexed pair body

Sources under the triangle layout: `a := t` (the `t`-mirror), `c := j` (the `j`-source mirror
— the row's own index, the clause's LARGER coordinate), live `k = 0..j-1` (the smaller). -/

/-- The head at-most-one pair body, reindexed by the larger coordinate. -/
def amoPairRowHeadBody : List L3Instr :=
  bitsI3 [true, true, false] ++ (sA ++ (sJ ++ (bitsI3 [true, false] ++ (bitsI3 [false]
    ++ (sA ++ (sC ++ (bitsI3 [true, false] ++ bitsI3 [false])))))))

/-- The state variant (tag block `encodeNat 2`). -/
def amoPairRowStateBody : List L3Instr :=
  bitsI3 [true, true, false] ++ (sA ++ (sJ ++ (bitsI3 [true, true, false] ++ (bitsI3 [false]
    ++ (sA ++ (sC ++ (bitsI3 [true, true, false] ++ bitsI3 [false])))))))

/-- **The reindexed head pair clause factors**: inner round `k` of row `j` emits the pair
`(k, j)`. -/
theorem amoPairRowHead_prog3Out (t j k : ℕ) :
    prog3Out amoPairRowHeadBody t j k
      = encodeClause' [(headVar t k, false), (headVar t j, false)] := by
  rw [encodeClause'_amoPair_head, amoPairRowHeadBody]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA, prog3Out_sC, prog3Out_sJ]
  simp [encodeNat, List.append_assoc]

theorem amoPairRowState_prog3Out (t j k : ℕ) :
    prog3Out amoPairRowStateBody t j k
      = encodeClause' [(stateVar t k, false), (stateVar t j, false)] := by
  rw [encodeClause'_amoPair_state, amoPairRowStateBody]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA, prog3Out_sC, prog3Out_sJ]
  simp [encodeNat, List.append_assoc]

/-- One triangle row factors through the loop denotation: row `j` is the pairs `(k, j)`,
`k < j`. -/
theorem amoPairRowHead_split (t j : ℕ) :
    loop3Out amoPairRowHeadBody t j j
      = ((List.range j).map (fun k =>
          encodeClause' [(headVar t k, false), (headVar t j, false)])).flatten := by
  rw [loop3Out_eq_flatten]
  exact congrArg List.flatten (List.map_congr_left (fun k _ => amoPairRowHead_prog3Out t j k))

theorem amoPairRowState_split (t j : ℕ) :
    loop3Out amoPairRowStateBody t j j
      = ((List.range j).map (fun k =>
          encodeClause' [(stateVar t k, false), (stateVar t j, false)])).flatten := by
  rw [loop3Out_eq_flatten]
  exact congrArg List.flatten
    (List.map_congr_left (fun k _ => amoPairRowState_prog3Out t j k))

/-! ## The triangle-ordered at-most-one, at the `Formula` level -/

/-- The head at-most-one pairs in triangle order: rows `j = 1..P`, row `j` carrying the pairs
`(k, j)` for `k < j`. -/
def amoTriHead (t : ℕ) : ℕ → Formula
  | 0 => []
  | j + 1 => amoTriHead t j ++ (List.range (j + 1)).map (fun k =>
      [(headVar t k, false), (headVar t (j + 1), false)])

/-- **The row loop's stream IS the triangle-ordered family** (clause encodings, flattened). -/
theorem triRowOut_amoTriHead (t : ℕ) : ∀ P,
    triRowOut amoPairRowHeadBody t P = ((amoTriHead t P).map encodeClause').flatten
  | 0 => rfl
  | P + 1 => by
    rw [show triRowOut amoPairRowHeadBody t (P + 1)
        = triRowOut amoPairRowHeadBody t P
            ++ loop3Out amoPairRowHeadBody t (P + 1) (P + 1) from rfl,
      triRowOut_amoTriHead t P, amoPairRowHead_split,
      show amoTriHead t (P + 1)
        = amoTriHead t P ++ (List.range (P + 1)).map (fun k =>
            [(headVar t k, false), (headVar t (P + 1), false)]) from rfl,
      List.map_append, List.flatten_append, List.map_map]
    rfl

/-- The grand stream: all times, triangle order within each. -/
theorem triOut_amoTriHead (P : ℕ) : ∀ B,
    triOut amoPairRowHeadBody P B
      = ((List.range B).map (fun t => ((amoTriHead t P).map encodeClause').flatten)).flatten
  | 0 => rfl
  | B + 1 => by
    rw [show triOut amoPairRowHeadBody P (B + 1)
        = triOut amoPairRowHeadBody P B ++ triRowOut amoPairRowHeadBody B P from rfl,
      triOut_amoTriHead P B, triRowOut_amoTriHead, List.range_succ, List.map_append,
      List.flatten_append]
    simp

/-! ## The order bridge — triangle order is a permutation of `atMostOne`

Appending a variable to the pool adds exactly one pair per existing variable, up to
permutation; iterating gives the transpose of the triangular enumeration. -/

/-- The one pure shuffle the snoc step needs. -/
theorem perm_snoc_middle {α : Type} (A C B : List α) (p : α) :
    ((A ++ [p]) ++ (C ++ B)).Perm ((A ++ C) ++ (p :: B)) := by
  have h1 : (A ++ [p]) ++ (C ++ B) = A ++ ([p] ++ (C ++ B)) := by
    rw [List.append_assoc]
  have h2 : (A ++ C) ++ (p :: B) = A ++ (C ++ ([p] ++ B)) := by
    rw [List.append_assoc]
    rfl
  rw [h1, h2]
  exact List.Perm.append_left A (List.perm_append_comm_assoc [p] C B)

theorem atMostOne_snoc (w : ℕ) : ∀ l : List ℕ,
    (atMostOne (l ++ [w])).Perm
      (atMostOne l ++ l.map (fun v => [(v, false), (w, false)]))
  | [] => by simp [atMostOne]
  | v :: vs => by
    rw [show (v :: vs) ++ [w] = v :: (vs ++ [w]) from rfl,
      show atMostOne (v :: (vs ++ [w]))
        = (vs ++ [w]).map (fun u => [(v, false), (u, false)]) ++ atMostOne (vs ++ [w])
        from rfl,
      List.map_append,
      show atMostOne (v :: vs)
        = vs.map (fun u => [(v, false), (u, false)]) ++ atMostOne vs from rfl,
      show [w].map (fun u => [(v, false), (u, false)]) = [[(v, false), (w, false)]]
        from rfl,
      show (v :: vs).map (fun u => [(u, false), (w, false)])
        = [(v, false), (w, false)] :: vs.map (fun u => [(u, false), (w, false)])
        from rfl]
    exact List.Perm.trans
      (List.Perm.append_left _ (atMostOne_snoc w vs))
      (perm_snoc_middle _ _ _ _)

/-- **The triangle order is a permutation of the tableau's `atMostOne`.** -/
theorem amoTriHead_perm (t : ℕ) : ∀ P,
    (amoTriHead t P).Perm (atMostOne ((List.range (P + 1)).map (headVar t)))
  | 0 => by simp [amoTriHead, atMostOne]
  | P + 1 => by
    rw [show amoTriHead t (P + 1)
        = amoTriHead t P ++ (List.range (P + 1)).map (fun k =>
            [(headVar t k, false), (headVar t (P + 1), false)]) from rfl,
      show P + 1 + 1 = (P + 1) + 1 from rfl, List.range_succ (n := P + 1),
      List.map_append]
    refine List.Perm.trans ?_ (atMostOne_snoc (headVar t (P + 1))
      ((List.range (P + 1)).map (headVar t))).symm
    refine List.Perm.append (amoTriHead_perm t P) ?_
    rw [List.map_map]
    rfl

/-! ## Satisfaction is blind to the order -/

theorem evalFormula_perm (a : ℕ → Bool) {φ ψ : Formula} (h : φ.Perm ψ) :
    evalFormula a φ = evalFormula a ψ := by
  simp only [evalFormula]
  rcases hb : ψ.all (evalClause a) with _ | _
  · rw [List.all_eq_false] at hb ⊢
    obtain ⟨c, hc, hcf⟩ := hb
    exact ⟨c, h.mem_iff.mpr hc, hcf⟩
  · rw [List.all_eq_true] at hb ⊢
    exact fun c hc => hb c (h.mem_iff.mp hc)

theorem satisfiable_perm {φ ψ : Formula} (h : φ.Perm ψ) :
    Satisfiable φ ↔ Satisfiable ψ :=
  exists_congr (fun a => by rw [evalFormula_perm a h])

/-- The head-family instance: the triangle-ordered stream at time `t` is satisfaction-blind
interchangeable with the tableau's at-most-one block. -/
theorem satisfiable_amoTriHead (t P : ℕ) :
    Satisfiable (amoTriHead t P)
      ↔ Satisfiable (atMostOne ((List.range (P + 1)).map (headVar t))) :=
  satisfiable_perm (amoTriHead_perm t P)

/-! ## THE HEAD AT-MOST-ONE STREAM, ALL TIMES, ONE MACHINE -/

/-- **THE TRIANGLE CASHES OUT**: the triangle machine at body `amoPairRowHeadBody` emits every
at-most-one pair clause of the head one-hot family — all times `t < B`, all pairs
`0 ≤ k < j ≤ P`, in triangle order — and re-arms itself between rounds. -/
theorem rep_triangleHead_run (B P CB C1 C2 NV : ℕ) (hP : 0 < P) (hCB : P < CB)
    (hC2 : P < C2) (hNV : P ≤ NV) (hBC1 : B ≤ C1) (out : List Bool) :
    run (repMachine (seqMachine
        (repPMachine (seqMachine (pairTMachine amoPairRowHeadBody) interRowMachine))
        interGrandMachine))
      (repRounds (fun t =>
          (repPRounds B (fun r =>
              pairTClock amoPairRowHeadBody B P CB C1 C2 NV t (r + 1) (r + 1)
                  ((out ++ ((List.range t).map (fun t' =>
                      ((amoTriHead t' P).map encodeClause').flatten)).flatten)
                    ++ ((amoTriHead t r).map encodeClause').flatten).length + 1
                + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
            + (4 * B + 4 * P + 8)) + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 16)) B + (4 * B + 4))
      (init (repMachine (seqMachine
          (repPMachine (seqMachine (pairTMachine amoPairRowHeadBody) interRowMachine))
          interGrandMachine))
        (cntT B 0 ++ (unaryD P ++ (jT CB 1 ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ ((List.range B).map (fun t =>
                ((amoTriHead t P).map encodeClause').flatten)).flatten))))))⟩ := by
  have h := rep_triangle_run amoPairRowHeadBody B P CB C1 C2 NV hP hCB hC2 hNV hBC1 out
  simpa only [triOut_amoTriHead, triRowOut_amoTriHead] using h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitTriangleHead
