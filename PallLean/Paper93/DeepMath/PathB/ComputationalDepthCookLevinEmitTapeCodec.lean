import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitBits

/-!
# Cook–Levin M2 emitter — E6 step 15: THE TAPE CODEC (the compaction finale dissolves)

`transOut` is the raw final tape — but no compaction machine is needed: the codec is a free
design choice, and the final tape is SELF-DESCRIBING.  The two leading counters are
self-delimiting (`2n` trues then the `[false, true]` marker), `B` and `P` determine every
mirror region's length once the chain fixes the concrete sizes
`CB = C2 = NV := P + 2`, `C1 := B + 2`, and the doubled output region is self-delimiting
(`[b, b]` pairs, `[false, true]` end marker).  So the decoder — a plain function on strings —
parses `B`, `P`, skips the four mirrors by computed length, un-doubles, and reads clauses to
the terminator:

* `unDouble_encodeD` — the doubled region decodes exactly;
* `decodeTape_spec` — the decoder reads ANY final-shape tape (mirror values free) down to
  `decodeFormulaT` of the doubled payload;
* `decodeTape_emitted` — **end-to-end**: on the master chain's exit tape (with the terminator
  bit from `snoc6 false` in the payload), the decoder returns `emittedReduction M x clock`
  exactly.

The finale phase therefore needs NO erasing, NO un-doubling machine, NO copy-down — the chain
halts and the tape IS the coded output.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitTapeCodec

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMaster2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodecT

/-! ## The primitives -/

/-- Leading-`true` count. -/
def countTrues : List Bool → ℕ
  | true :: bs => countTrues bs + 1
  | _ => 0

theorem countTrues_replicate (n : ℕ) (l : List Bool) :
    countTrues (List.replicate n true ++ false :: l) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, countTrues] using ih

/-- Un-double: read `[b, b]` pairs, stop at the (unequal) `[false, true]` end marker. -/
def unDouble : List Bool → List Bool
  | b1 :: b2 :: bs => if b1 = b2 then b1 :: unDouble bs else []
  | _ => []

theorem unDouble_encodeD (bs : List Bool) : unDouble (encodeD bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show unDouble (b :: b :: encodeD bs) = b :: bs
    rw [unDouble]
    simp [ih]

/-! ## The tape decoder -/

/-- The tape decoder: parse `B`, `P` from the self-delimiting counters, skip the four mirrors
(sizes `P+2, B+2, P+2, P+2` — the chain's concrete choices), un-double, read clauses. -/
def decodeTape (bs : List Bool) : Formula :=
  let B := countTrues bs / 2
  let bs1 := bs.drop (2 * B + 2)
  let P := countTrues bs1 / 2
  let bs2 := bs1.drop (2 * P + 2)
  let bs3 := bs2.drop ((2 * (P + 2) + 2) + ((2 * (B + 2) + 2) + ((2 * (P + 2) + 2)
    + (2 * (P + 2) + 2))))
  decodeFormulaT (unDouble bs3)

/-- **The decoder reads the final tape shape** — mirror values free, only the sizes pinned. -/
theorem decodeTape_spec (B P v1 t v2 w : ℕ) (payload : List Bool)
    (hv1 : v1 ≤ P + 2) (ht : t ≤ B + 2) (hv2 : v2 ≤ P + 2) (hw : w ≤ P + 2) :
    decodeTape (unaryD B ++ (unaryD P ++ (jT (P + 2) v1 ++ (jT (B + 2) t
      ++ (jT (P + 2) v2 ++ (jT (P + 2) w ++ encodeD payload))))))
      = decodeFormulaT payload := by
  have hB : countTrues (unaryD B ++ (unaryD P ++ (jT (P + 2) v1 ++ (jT (B + 2) t
      ++ (jT (P + 2) v2 ++ (jT (P + 2) w ++ encodeD payload)))))) = 2 * B := by
    rw [unaryD_eq, List.append_assoc]
    exact countTrues_replicate (2 * B) _
  have hd1 : (unaryD B ++ (unaryD P ++ (jT (P + 2) v1 ++ (jT (B + 2) t
      ++ (jT (P + 2) v2 ++ (jT (P + 2) w ++ encodeD payload)))))).drop (2 * B + 2)
      = unaryD P ++ (jT (P + 2) v1 ++ (jT (B + 2) t
        ++ (jT (P + 2) v2 ++ (jT (P + 2) w ++ encodeD payload)))) := by
    rw [show 2 * B + 2 = (unaryD B).length from (unaryD_length B).symm, List.drop_left]
  have hP : countTrues (unaryD P ++ (jT (P + 2) v1 ++ (jT (B + 2) t
      ++ (jT (P + 2) v2 ++ (jT (P + 2) w ++ encodeD payload))))) = 2 * P := by
    rw [unaryD_eq, List.append_assoc]
    exact countTrues_replicate (2 * P) _
  have hd2 : (unaryD P ++ (jT (P + 2) v1 ++ (jT (B + 2) t
      ++ (jT (P + 2) v2 ++ (jT (P + 2) w ++ encodeD payload))))).drop (2 * P + 2)
      = jT (P + 2) v1 ++ (jT (B + 2) t ++ (jT (P + 2) v2 ++ (jT (P + 2) w
        ++ encodeD payload))) := by
    rw [show 2 * P + 2 = (unaryD P).length from (unaryD_length P).symm, List.drop_left]
  have hd3 : (jT (P + 2) v1 ++ (jT (B + 2) t ++ (jT (P + 2) v2 ++ (jT (P + 2) w
      ++ encodeD payload)))).drop ((2 * (P + 2) + 2) + ((2 * (B + 2) + 2)
        + ((2 * (P + 2) + 2) + (2 * (P + 2) + 2))))
      = encodeD payload := by
    rw [show jT (P + 2) v1 ++ (jT (B + 2) t ++ (jT (P + 2) v2 ++ (jT (P + 2) w
        ++ encodeD payload)))
      = (jT (P + 2) v1 ++ (jT (B + 2) t ++ (jT (P + 2) v2 ++ jT (P + 2) w)))
        ++ encodeD payload from by simp [List.append_assoc]]
    rw [show (2 * (P + 2) + 2) + ((2 * (B + 2) + 2) + ((2 * (P + 2) + 2)
        + (2 * (P + 2) + 2)))
      = (jT (P + 2) v1 ++ (jT (B + 2) t ++ (jT (P + 2) v2 ++ jT (P + 2) w))).length from by
        simp only [List.length_append, jT_length (P + 2) v1 hv1, jT_length (B + 2) t ht,
          jT_length (P + 2) v2 hv2, jT_length (P + 2) w hw],
      List.drop_left]
  show decodeFormulaT (unDouble _) = decodeFormulaT payload
  rw [hB, show 2 * (2 * B / 2) + 2 = 2 * B + 2 from by omega, hd1, hP,
    show 2 * (2 * P / 2) + 2 = 2 * P + 2 from by omega, hd2,
    show 2 * (2 * P / 2 + 2) + 2 + (2 * (2 * B / 2 + 2) + 2 + (2 * (2 * P / 2 + 2) + 2
        + (2 * (2 * P / 2 + 2) + 2)))
      = (2 * (P + 2) + 2) + ((2 * (B + 2) + 2) + ((2 * (P + 2) + 2) + (2 * (P + 2) + 2)))
      from by omega, hd3, unDouble_encodeD]

/-! ## End-to-end: the master chain's exit tape decodes to the emission -/

/-- **THE FINAL TAPE IS THE CODED OUTPUT.**  On the master chain's exit tape at the concrete
sizes (`CB = C2 = NV := P + 2`, `C1 := B + 2`, mirrors at their proven final values, the
terminator bit in the payload), the decoder returns `emittedReduction M x clock` exactly —
no finale machine work beyond the already-proven `snoc6 false`. -/
theorem decodeTape_emitted (M : Machine) (x : List Bool) (clock : ℕ)
    (hAcc : acceptStates M ≠ []) :
    decodeTape (unaryD clock ++ (unaryD (x.length + clock)
      ++ (jT (x.length + clock + 2) 1 ++ (jT (clock + 2) (clock + 2)
      ++ (jT (x.length + clock + 2) (x.length + clock + 1)
      ++ (jT (x.length + clock + 2) 0
      ++ encodeD ((((List.range (x.length + clock + 1)).map (fun p =>
            encodeClause' [(cellVar 0 p, x.getD p false)])).flatten
          ++ masterOut2 M (x.length + clock) clock) ++ [false])))))))
      = emittedReduction M x clock := by
  rw [decodeTape_spec clock (x.length + clock) 1 (clock + 2) (x.length + clock + 1) 0 _
      (by omega) (by omega) (by omega) (by omega),
    emittedReductionStreamT M x clock,
    decodeFormulaT_encodeFormulaT (emittedReduction M x clock)
      (fun c hc => emittedTotal_clauses_ne M x (x.length + clock) clock hAcc c hc)]

/-- The decoded output decides the clocked acceptance question — the tape-codec form of the
target's semantics. -/
theorem decodeTape_emitted_correct (M : Machine) (x : List Bool) (clock : ℕ)
    (hAcc : acceptStates M ≠ []) :
    Satisfiable (decodeTape (unaryD clock ++ (unaryD (x.length + clock)
      ++ (jT (x.length + clock + 2) 1 ++ (jT (clock + 2) (clock + 2)
      ++ (jT (x.length + clock + 2) (x.length + clock + 1)
      ++ (jT (x.length + clock + 2) 0
      ++ encodeD ((((List.range (x.length + clock + 1)).map (fun p =>
            encodeClause' [(cellVar 0 p, x.getD p false)])).flatten
          ++ masterOut2 M (x.length + clock) clock) ++ [false]))))))))
      ↔ (HaltsBy M x clock ∧ decideOut M x clock = true) := by
  rw [decodeTape_emitted M x clock hAcc]
  exact emittedReduction_correct M x clock

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitTapeCodec
