import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCodecT

/-!
# Cook–Levin M2 emitter — E6 step 13: THE EMISSION SIZE BOUND

The clause-count bound for `emittedTotal`, mirroring `fullTableau_length_le` — the polynomial
(degree ≤ 3 in `(P, B)`, `card` a machine constant) that feeds the `PolyBounded` clock and
output-size obligations of the `Transduces` wrapper.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitSizeT

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinReduce
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2

/-! ## Per-piece bounds -/

theorem dynQBF_length_le (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (b : Bool)
    (k : ℕ) : (dynQBF M t q b k).length ≤ 2 := by
  by_cases h0 : mvN M q.val b = 0
  · simp [dynQBF, h0]
  · simp [dynQBF, h0, dynamicsClause]

theorem leftFq_length_le (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (b : Bool) :
    (leftFq M t q b).length ≤ 1 := by
  by_cases h0 : mvN M q.val b = 0
  · simp [leftFq, h0]
  · simp [leftFq, h0]

theorem headOneHotEmit_length_le (t P : ℕ) :
    (headOneHotEmit t P).length ≤ (P + 1) * (P + 1) + 1 := by
  rw [(headOneHotEmit_perm t P).length_eq]
  unfold headOneHot
  exact le_trans (oneHot_length_le _)
    (le_of_eq (by rw [List.length_map, List.length_range]))

theorem stateOneHot_length_le (M : Machine) (t : ℕ) :
    (stateOneHot M t).length ≤ Fintype.card M.State * Fintype.card M.State + 1 := by
  unfold stateOneHot
  exact le_trans (oneHot_length_le _)
    (le_of_eq (by rw [List.length_map, List.length_range]))

theorem dynAFormula_length_le (M : Machine) (P B : ℕ) :
    (dynAFormula M P B).length ≤ B * (Fintype.card M.State * ((P + 1) * 4)) := by
  rw [dynAFormula]
  have := bigAnd_map_length_le (List.range B)
    (fun t => bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
      bigAnd ((List.range (P + 1)).map (fun k =>
        dynQBF M t q false k ++ dynQBF M t q true k)))))
    (Fintype.card M.State * ((P + 1) * 4)) (by
      intro t _
      have h2 := bigAnd_map_length_le (List.finRange (Fintype.card M.State))
        (fun q => bigAnd ((List.range (P + 1)).map (fun k =>
          dynQBF M t q false k ++ dynQBF M t q true k)))
        ((P + 1) * 4) (by
          intro q _
          have h3 := bigAnd_map_length_le (List.range (P + 1))
            (fun k => dynQBF M t q false k ++ dynQBF M t q true k) 4 (by
              intro k _
              rw [List.length_append]
              have := dynQBF_length_le M t q false k
              have := dynQBF_length_le M t q true k
              omega)
          rwa [List.length_range] at h3)
      rwa [List.length_finRange] at h2)
  rwa [List.length_range] at this

theorem dynBFormula_length_le (M : Machine) (B : ℕ) :
    (dynBFormula M B).length ≤ B * (Fintype.card M.State * 2) := by
  rw [dynBFormula]
  have := bigAnd_map_length_le (List.range B)
    (fun t => bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
      leftFq M t q false ++ leftFq M t q true)))
    (Fintype.card M.State * 2) (by
      intro t _
      have h2 := bigAnd_map_length_le (List.finRange (Fintype.card M.State))
        (fun q => leftFq M t q false ++ leftFq M t q true) 2 (by
          intro q _
          rw [List.length_append]
          have := leftFq_length_le M t q false
          have := leftFq_length_le M t q true
          omega)
      rwa [List.length_finRange] at h2)
  rwa [List.length_range] at this

theorem headLoop_length_le (P B : ℕ) :
    (bigAnd ((List.range B).map (fun t => headOneHotEmit t P))).length
      ≤ B * ((P + 1) * (P + 1) + 1) := by
  have := bigAnd_map_length_le (List.range B) (fun t => headOneHotEmit t P)
    ((P + 1) * (P + 1) + 1) (fun t _ => headOneHotEmit_length_le t P)
  rwa [List.length_range] at this

theorem stateLoop_length_le (M : Machine) (B : ℕ) :
    (bigAnd ((List.range B).map (fun t => stateOneHot M t))).length
      ≤ B * (Fintype.card M.State * Fintype.card M.State + 1) := by
  have := bigAnd_map_length_le (List.range B) (fun t => stateOneHot M t)
    (Fintype.card M.State * Fintype.card M.State + 1)
    (fun t _ => stateOneHot_length_le M t)
  rwa [List.length_range] at this

/-! ## The emission size bound -/

/-- The explicit clause-count polynomial for the emission — degree ≤ 3 in `(P, B)`. -/
def emittedSizeBound (P B s : ℕ) : ℕ :=
  (P + 1) + B * ((P + 1) * 2) + B * (s * ((P + 1) * 2)) + B * (s * ((P + 1) * 4))
    + B * ((P + 1) * (P + 1) + 1) + B * (s * s + 1) + B * (s * 2)
    + (s * s + 1) + ((P + 1) * (P + 1) + 1) + 1 + 2

/-- **The emission's clause count is polynomially bounded.** -/
theorem emittedTotal_length_le (M : Machine) (x : List Bool) (P B : ℕ) :
    (emittedTotal M x P B).length ≤ emittedSizeBound P B (Fintype.card M.State) := by
  have h1 : (cellFixes x P).length = P + 1 := by
    simp [cellFixes, fixBits]
  have h2 := tapeFamily_length_le P B
  have h3 := writeFamily_length_le M P B
  have h4 := dynAFormula_length_le M P B
  have h5 := headLoop_length_le P B
  have h6 := stateLoop_length_le M B
  have h7 := dynBFormula_length_le M B
  have h8 := stateOneHot_length_le M B
  have h9 := headOneHotEmit_length_le B P
  have h10 := acceptFormula_length_le M B
  simp only [emittedTotal, emittedFormula, List.length_append]
  unfold emittedSizeBound
  simp only [List.length_cons, List.length_nil]
  omega

/-- **Polynomial output size at the reduction parameters** — for a fixed machine (`card` a
constant), a polynomial in `|x|` and the clock. -/
theorem emittedReduction_length_le (M : Machine) (x : List Bool) (clock : ℕ) :
    (emittedReduction M x clock).length
      ≤ emittedSizeBound (x.length + clock) clock (Fintype.card M.State) :=
  emittedTotal_length_le M x (x.length + clock) clock

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitSizeT
