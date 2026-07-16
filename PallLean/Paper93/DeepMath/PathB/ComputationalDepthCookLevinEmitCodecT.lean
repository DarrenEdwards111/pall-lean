import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitPackage2

/-!
# Cook–Levin M2 emitter — E6 step 12: THE TERMINATOR CODEC

`encodeFormula'` prefixes the clause COUNT — a unary header the machine would need dedicated
counter arithmetic (triangular numbers) to compute.  The terminator codec removes the need:
every clause encoding of a NONEMPTY clause starts with `true` (its length header), so a single
`[false]` terminates the formula — `encodeFormulaT φ := payload ++ [false]` — and the header
phase collapses to ONE already-proven machine (`snoc6Machine false`, brick 43).

* `decodeFormulaT_encodeFormulaT` — faithfulness for formulas with no empty clause;
* `emittedTotal_clauses_ne` — the emission has no empty clause, given `acceptStates M ≠ []`
  (the one genuine corner: a machine with NO accepting-halting state has an empty accept
  clause, which the terminator cannot distinguish — such machines decide the constantly-false
  question and are excluded by hypothesis);
* `emittedReductionStreamT` — the machines' stream plus the terminator IS
  `encodeFormulaT (emittedReduction …)`;
* `EmitsEmittedT` + semantics — the final target: a poly transducer for the terminator-coded
  emission, satisfiable iff the clocked run accepts.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodecT

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinReduce
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTriangleHead
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMaster2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2

/-! ## The codec -/

/-- Terminator-coded formula: the clause payloads, then a single `false`. -/
def encodeFormulaT (φ : Formula) : List Bool := (φ.map encodeClause').flatten ++ [false]

/-- Decode clauses while the head bit is `true` (a nonempty clause's length header);
`false` terminates.  Fuel decreases once per clause. -/
def decodeClausesT : ℕ → List Bool → Formula
  | 0, _ => []
  | _ + 1, [] => []
  | _ + 1, false :: _ => []
  | fuel + 1, true :: bs =>
      (decodeClause' (true :: bs)).1 :: decodeClausesT fuel (decodeClause' (true :: bs)).2

def decodeFormulaT (bs : List Bool) : Formula := decodeClausesT bs.length bs

theorem decodeClausesT_true (fuel : ℕ) (bs : List Bool) :
    decodeClausesT (fuel + 1) (true :: bs)
      = (decodeClause' (true :: bs)).1 :: decodeClausesT fuel (decodeClause' (true :: bs)).2
  := rfl

/-- One decode step consumes one nonempty clause's encoding. -/
theorem decodeClausesT_step (fuel : ℕ) (c : Clause) (hc : c ≠ []) (rest : List Bool) :
    decodeClausesT (fuel + 1) (encodeClause' c ++ rest)
      = c :: decodeClausesT fuel rest := by
  obtain ⟨l, ls, rfl⟩ : ∃ l ls, c = l :: ls := by
    rcases c with _ | ⟨l, ls⟩
    · exact absurd rfl hc
    · exact ⟨l, ls, rfl⟩
  have he : encodeClause' (l :: ls) ++ rest
      = true :: ((List.replicate ls.length true ++ [false])
          ++ (((l :: ls).map encodeLit').flatten ++ rest)) := by
    simp [encodeClause', encodeNat, List.replicate_succ, List.append_assoc]
  rw [he, decodeClausesT_true, ← he, decodeClause'_encodeClause']

/-- **Terminator faithfulness** for formulas with no empty clause. -/
theorem decodeClausesT_flatten : ∀ (φ : Formula) (fuel : ℕ),
    (∀ c ∈ φ, c ≠ []) → φ.length < fuel →
    decodeClausesT fuel ((φ.map encodeClause').flatten ++ [false]) = φ
  | [], fuel, _, hf => by
    rcases fuel with _ | f
    · omega
    · rfl
  | c :: φ, fuel, h, hf => by
    rcases fuel with _ | f
    · omega
    · rw [List.map_cons, List.flatten_cons, List.append_assoc,
        decodeClausesT_step f c (h c List.mem_cons_self),
        decodeClausesT_flatten φ f
          (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
          (by simpa using Nat.lt_of_succ_lt_succ hf)]

/-- Each clause payload is at least one bit (its length header). -/
theorem payload_length_ge (φ : Formula) :
    φ.length ≤ ((φ.map encodeClause').flatten).length := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
    rw [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have h1 : 1 ≤ (encodeClause' c).length := by
      rw [encodeClause', List.length_append]
      have h2 : 0 < (encodeNat c.length).length := by simp [encodeNat]
      omega
    omega

/-- **The terminator codec is faithful** on formulas with no empty clause. -/
theorem decodeFormulaT_encodeFormulaT (φ : Formula) (h : ∀ c ∈ φ, c ≠ []) :
    decodeFormulaT (encodeFormulaT φ) = φ := by
  rw [decodeFormulaT, encodeFormulaT]
  apply decodeClausesT_flatten φ _ h
  rw [List.length_append, List.length_cons, List.length_nil]
  have := payload_length_ge φ
  omega

/-! ## The emission has no empty clause -/

theorem atMostOne_mem_ne : ∀ (l : List ℕ), ∀ c ∈ atMostOne l, c ≠ []
  | [], c, hc => absurd hc (by simp [atMostOne])
  | v :: vs, c, hc => by
    rw [atMostOne, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨w, _, rfl⟩ := List.mem_map.mp hc
      simp
    · exact atMostOne_mem_ne vs c hc

theorem dynQBF_ne (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (b : Bool)
    (k : ℕ) : ∀ c ∈ dynQBF M t q b k, c ≠ [] := by
  intro c hc
  by_cases h0 : mvN M q.val b = 0
  · rw [dynQBF, if_pos h0] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals simp [implClause]
  · rw [dynQBF, if_neg h0, dynamicsClause] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals simp [implClause]

theorem leftFq_ne (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (b : Bool) :
    ∀ c ∈ leftFq M t q b, c ≠ [] := by
  intro c hc
  by_cases h0 : mvN M q.val b = 0
  · rw [leftFq, if_pos h0] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp [implClause]
  · rw [leftFq, if_neg h0] at hc
    exact absurd hc List.not_mem_nil

theorem oneHot_range_ne (f : ℕ → ℕ) (n : ℕ) (hn : 0 < n) :
    ∀ c ∈ oneHot ((List.range n).map f), c ≠ [] := by
  intro c hc
  rw [oneHot, List.mem_cons] at hc
  rcases hc with rfl | hc
  · apply List.ne_nil_of_length_pos
    rw [atLeastOne, List.length_map, List.length_map, List.length_range]
    omega
  · exact atMostOne_mem_ne _ c hc

/-- **The emission has no empty clause** — given at least one accepting-halting state. -/
theorem emittedTotal_clauses_ne (M : Machine) (x : List Bool) (P B : ℕ)
    (hAcc : acceptStates M ≠ []) : ∀ c ∈ emittedTotal M x P B, c ≠ [] := by
  have hcard : 0 < Fintype.card M.State := @Fintype.card_pos _ _ ⟨M.start⟩
  intro c hc
  rw [emittedTotal, emittedFormula] at hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · -- cell fixes
    rw [cellFixes, fixBits] at hc
    obtain ⟨pr, _, rfl⟩ := List.mem_map.mp hc
    simp
  · -- tape family
    rw [tapeFamily, bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hF
    rw [bigAnd] at hc
    obtain ⟨F', hF', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hF'
    rw [cellCopyClause, guardedIff] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals simp
  · -- write family
    rw [writeFamily, bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hF
    rw [bigAnd] at hc
    obtain ⟨F', hF', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hF'
    rw [bigAnd] at hc
    obtain ⟨F'', hF'', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hF''
    rw [bigAnd] at hc
    obtain ⟨F3, hF3, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hF3
    rw [writeClause] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp [implClause]
  · -- dynamics A
    rw [dynAFormula, bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hF
    rw [bigAnd] at hc
    obtain ⟨F', hF', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hF'
    rw [bigAnd] at hc
    obtain ⟨F'', hF'', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hF''
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact dynQBF_ne M t q false k c hc
    · exact dynQBF_ne M t q true k c hc
  · -- head loop
    rw [bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hF
    rw [(headOneHotEmit_perm t P).mem_iff, headOneHot] at hc
    exact oneHot_range_ne (headVar t) (P + 1) (by omega) c hc
  · -- state loop
    rw [bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hF
    rw [stateOneHot] at hc
    exact oneHot_range_ne (stateVar t) (Fintype.card M.State) hcard c hc
  · -- dynamics B
    rw [dynBFormula, bigAnd] at hc
    obtain ⟨F, hF, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hF
    rw [bigAnd] at hc
    obtain ⟨F', hF', hc⟩ := List.mem_flatten.mp hc
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hF'
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact leftFq_ne M t q false c hc
    · exact leftFq_ne M t q true c hc
  · -- state top
    rw [stateOneHot] at hc
    exact oneHot_range_ne (stateVar B) (Fintype.card M.State) hcard c hc
  · -- head top
    rw [(headOneHotEmit_perm B P).mem_iff, headOneHot] at hc
    exact oneHot_range_ne (headVar B) (P + 1) (by omega) c hc
  · -- accept
    rw [acceptFormula] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    apply List.ne_nil_of_length_pos
    rw [atLeastOne, List.length_map, List.length_map]
    exact Nat.pos_of_ne_zero (fun h => hAcc (List.eq_nil_of_length_eq_zero h))
  · -- init units
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals simp

/-! ## The terminator-coded target -/

/-- **The machines' stream plus the terminator IS the coded target** — the last phase is one
`snoc6Machine false` pass (brick 43, already proven). -/
theorem emittedReductionStreamT (M : Machine) (x : List Bool) (clock : ℕ) :
    (((List.range (x.length + clock + 1)).map (fun p =>
        encodeClause' [(cellVar 0 p, x.getD p false)])).flatten
      ++ masterOut2 M (x.length + clock) clock) ++ [false]
    = encodeFormulaT (emittedReduction M x clock) := by
  rw [encodeFormulaT, ← emittedReductionStream_encode]

/-- **Terminator-codec correctness for the emission.** -/
theorem satisfiable_decodeT_emitted (M : Machine) (x : List Bool) (clock : ℕ)
    (hAcc : acceptStates M ≠ []) :
    Satisfiable (decodeFormulaT (encodeFormulaT (emittedReduction M x clock)))
      ↔ (HaltsBy M x clock ∧ decideOut M x clock = true) := by
  rw [decodeFormulaT_encodeFormulaT (emittedReduction M x clock)
    (fun c hc => emittedTotal_clauses_ne M x (x.length + clock) clock hAcc c hc)]
  exact emittedReduction_correct M x clock

/-- **THE FINAL TARGET**: a poly transducer for the terminator-coded emission.  The header
phase is `snoc6 false`; the payload is the init-cell stream plus `masterOut2`. -/
def EmitsEmittedT (M : Machine) (clock : ℕ → ℕ) : Prop :=
  PolyComputable (fun x => encodeFormulaT (emittedReduction M x (clock x.length)))

theorem EmitsEmittedT_semantics (M : Machine) (clock : ℕ → ℕ) (x : List Bool)
    (hAcc : acceptStates M ≠ []) :
    Satisfiable (decodeFormulaT (encodeFormulaT (emittedReduction M x (clock x.length))))
      ↔ (HaltsBy M x (clock x.length) ∧ decideOut M x (clock x.length) = true) :=
  satisfiable_decodeT_emitted M x (clock x.length) hAcc

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodecT
