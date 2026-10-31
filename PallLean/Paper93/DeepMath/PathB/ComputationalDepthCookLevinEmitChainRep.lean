import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRearmP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRep

/-!
# Cook–Levin M2 emitter — the grand loop over a chained per-round body

The three assembly layers land together: a **prefixed loop engine** (`loopProg2PMachine`) and a
**prefixed re-armer** (`rearm2PMachine`) compose by `seqMachine` into a per-round body whose tape
interface is *self-restoring* — it maps
`cntT B (t+1) ++ (unaryD N ++ (unaryD a ++ (jT N 0 ++ encodeD out)))` to the same shape with the
family stream appended — and `repMachine` drives that body `B` times: `rep_chain2_run`.  One
machine, `B` grand rounds, each round a full engine run plus a full re-arm, the family stream
appended `B` times, self-halting at the explicit clock.  `rep_cellCopyP_chain_run` instantiates it
with the real tape-copy family.

**Scope honesty.**  The per-round body here has a *fixed* source region (`unaryD a` does not change
between rounds), so the demonstration emits `B` copies of the *same* family stream.  The tableau's
per-`t` families additionally need the live round index `t` as a splice source — a `t`-mirror
counter incremented between rounds.  In-place increment of an exact unary counter (`unaryD t ↦
unaryD (t+1)`) requires either capacity padding in the source region (and pad-tolerant source
scans) or a copy stage regenerating the mirror from the grand counter; that is the named remaining
E4 design item, not discharged here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitChainRep

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2P
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRearmP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep

/-- `B` grand rounds of the two-source family stream. -/
def repChain2Out (body : List LInstr) (a N : ℕ) : ℕ → List Bool
  | 0 => []
  | t + 1 => repChain2Out body a N t ++ loop2Out body a N

/-- **THE GRAND LOOP OVER A CHAINED BODY.**  The per-round body — the prefixed two-source loop
engine sequenced with the prefixed re-armer — is driven `B` times by `repMachine`: every grand
round marks the next `cntT B` pair, runs the full engine (family stream appended, prefix verbatim),
re-arms the saturated variable, and hands the restored interface to the next round.  Self-halting
at the explicit clock with the stream appended `B` times. -/
theorem rep_chain2_run (body : List LInstr) (N a : ℕ) (hN : 0 < N) (B : ℕ)
    (out : List Bool) :
    run (repMachine (seqMachine (loopProg2PMachine body) rearm2PMachine))
      (repRounds (fun t =>
          lp2pClock body B N a (out ++ repChain2Out body a N t).length + 1
            + (2 * B + 2 * N + 2 * a + 2 * N + 8)) B + (4 * B + 4))
      (init (repMachine (seqMachine (loopProg2PMachine body) rearm2PMachine))
        (cntT B 0 ++ (unaryD N ++ (unaryD a ++ (jT N 0 ++ encodeD out)))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD N ++ (unaryD a ++ (jT N 0
            ++ encodeD (out ++ repChain2Out body a N B))))⟩ := by
  have h := rep_run (seqMachine (loopProg2PMachine body) rearm2PMachine) B
    (fun t => unaryD N ++ (unaryD a ++ (jT N 0
      ++ encodeD (out ++ repChain2Out body a N t))))
    (fun t => lp2pClock body B N a (out ++ repChain2Out body a N t).length + 1
        + (2 * B + 2 * N + 2 * a + 2 * N + 8))
    (fun _ => Sum.inr (11, false)) (fun _ => 2 * B + 2 * N + 2 * a + 2 * N + 7)
    (fun t ht => by
      constructor
      · have heng := loopProg2P_run body B (t + 1) (by omega) N a
          (out ++ repChain2Out body a N t)
        have hrearm := rearm2P_run B (t + 1) (by omega) N a N hN
          (encodeD ((out ++ repChain2Out body a N t) ++ loop2Out body a N))
        rw [jT_full] at hrearm
        have hseq := seq_run (loopProg2PMachine body) rearm2PMachine _ _ _ _ _ _ _ _ _
          heng rfl hrearm rfl
        rw [List.append_assoc,
          show repChain2Out body a N t ++ loop2Out body a N
            = repChain2Out body a N (t + 1) from rfl] at hseq
        exact hseq
      · rfl)
  simp only [show repChain2Out body a N 0 = [] from rfl, List.append_nil] at h
  exact h

/-- **The grand loop over a real family**: `B` grand rounds, each emitting the whole tape-copy
family stream at time `t₀` and re-arming — one machine, self-halting at the explicit clock. -/
theorem rep_cellCopyP_chain_run (t₀ P B : ℕ) (out : List Bool) :
    run (repMachine (seqMachine (loopProg2PMachine cellCopyBody) rearm2PMachine))
      (repRounds (fun t =>
          lp2pClock cellCopyBody B (P + 1) t₀
              (out ++ repChain2Out cellCopyBody t₀ (P + 1) t).length + 1
            + (2 * B + 2 * (P + 1) + 2 * t₀ + 2 * (P + 1) + 8)) B + (4 * B + 4))
      (init (repMachine (seqMachine (loopProg2PMachine cellCopyBody) rearm2PMachine))
        (cntT B 0 ++ (unaryD (P + 1) ++ (unaryD t₀ ++ (jT (P + 1) 0 ++ encodeD out)))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD (P + 1) ++ (unaryD t₀ ++ (jT (P + 1) 0
            ++ encodeD (out ++ repChain2Out cellCopyBody t₀ (P + 1) B))))⟩ :=
  rep_chain2_run cellCopyBody (P + 1) t₀ (by omega) B out

/-- One grand round's contribution is the full family: the stream splits per round. -/
theorem repChain2Out_cellCopy_succ (t₀ P t : ℕ) :
    repChain2Out cellCopyBody t₀ (P + 1) (t + 1)
      = repChain2Out cellCopyBody t₀ (P + 1) t
        ++ ((List.range (P + 1)).map (fun p =>
            encodeClause' [(headVar t₀ p, true), (cellVar (t₀ + 1) p, false),
              (cellVar t₀ p, true)]
              ++ encodeClause' [(headVar t₀ p, true), (cellVar (t₀ + 1) p, true),
                   (cellVar t₀ p, false)])).flatten := by
  rw [show repChain2Out cellCopyBody t₀ (P + 1) (t + 1)
      = repChain2Out cellCopyBody t₀ (P + 1) t ++ loop2Out cellCopyBody t₀ (P + 1)
      from rfl,
    cellCopy_split]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitChainRep