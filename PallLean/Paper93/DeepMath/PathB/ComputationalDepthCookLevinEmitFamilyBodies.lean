import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitLoopProg2

/-!
# Cook–Levin M2 emitter — the family bodies

The remaining tableau families as **body instantiations** of the two-source looped emitter.  Three
observations make every window shape a `List LInstr` body over the sources `(A := t, J := p)`:

* **offsets are free**: `encodeNat (v + c) = 1^c ++ encodeNat v`, so `t+1`, `p+1`, `p+2` splice as a
  fixed `true`-prefix before the splice instruction (`spA c`/`spJ c`);
* **left-moves reindex**: a window concluding at `p - 1` is emitted with the live variable `j := p - 1`
  — the guards read `j + 1`, the conclusion `j`, all nonnegative offsets;
* **the `δ`-data are machine constants**: `nextStateIdx` is head-independent
  (`nextStateIdx_head_independent`, proved here) and `writtenBit` depends only on `(state, bit)` — so
  per `(q̂, b)` the conclusion blocks are fixed bits, and the family is finitely many hardwired bodies.

Delivered, all sorry-free: the `prog2Out` homomorphism algebra; the **state one-hot at-least-one**
family (body + split + machine run, completing the one-hot pair with the head family); the **tape-copy
family** — `cellCopyBody` emits *both* clauses of `cellCopyClause t p` per round, and
`cellCopy_family_run` runs the machine over `p = 0..P` in one shot; the **write family** —
`writeBody q̂ b wb` is the write implication window, `write_family_run` runs its `p`-loop for each of
the finitely many `(q̂, b)`; and the **dynamics windows** — the shared guard prefix `winPre` and the
four conclusion variants (state-conclusion, head stay/right/reset) plus the reindexed left-mover, each
factored against `encodeClause'_implWindow`.  The at-most-one pair families quantify over *pairs*
`(i, j)`, `i < j` — a triangular double loop needing a third splice region; they are the one remaining
machine mechanism, explicitly deferred.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat encodeNat_length)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2

/-! ## The `prog2Out` homomorphism algebra -/

/-- Fixed bits as instructions. -/
def bitsI (l : List Bool) : List LInstr := l.map .bit

/-- Splice the source with a constant offset: `encodeNat (a + c)`. -/
def spA (c : ℕ) : List LInstr := bitsI (List.replicate c true) ++ [.spliceA]

/-- Splice the live variable with a constant offset: `encodeNat (k + c)`. -/
def spJ (c : ℕ) : List LInstr := bitsI (List.replicate c true) ++ [.spliceJ]

theorem prog2Out_eq_flatten (body : List LInstr) (a k : ℕ) :
    prog2Out body a k = (body.map (instr2Out a k)).flatten := by
  show prog2OutN body a k body.length = _
  suffices h : ∀ n, n ≤ body.length →
      prog2OutN body a k n = ((body.take n).map (instr2Out a k)).flatten by
    rw [h body.length (le_refl _), List.take_length]
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show prog2OutN body a k (n + 1)
        = prog2OutN body a k n ++ instr2Out a k (body.getD n .spliceJ) from rfl,
      ih (by omega), take_snoc_getD body .spliceJ n (by omega), List.map_append,
      List.flatten_append]
    simp

theorem prog2Out_append (b1 b2 : List LInstr) (a k : ℕ) :
    prog2Out (b1 ++ b2) a k = prog2Out b1 a k ++ prog2Out b2 a k := by
  simp [prog2Out_eq_flatten, List.map_append]

theorem prog2Out_bits (l : List Bool) (a k : ℕ) : prog2Out (bitsI l) a k = l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    rw [show bitsI (b :: bs) = [.bit b] ++ bitsI bs from rfl, prog2Out_append, ih]
    rfl

theorem prog2Out_singleA (a k : ℕ) : prog2Out [LInstr.spliceA] a k = encodeNat a := by
  simp [prog2Out_eq_flatten, instr2Out]

theorem prog2Out_singleJ (a k : ℕ) : prog2Out [LInstr.spliceJ] a k = encodeNat k := by
  simp [prog2Out_eq_flatten, instr2Out]

/-- The offset law: a `true`-prefix shifts the spliced value. -/
theorem encodeNat_add (v c : ℕ) :
    encodeNat (v + c) = List.replicate c true ++ encodeNat v := by
  show List.replicate (v + c) true ++ [false] = _
  rw [show v + c = c + v from by omega, List.replicate_add, List.append_assoc]
  rfl

theorem prog2Out_spA (c a k : ℕ) : prog2Out (spA c) a k = encodeNat (a + c) := by
  rw [spA, prog2Out_append, prog2Out_bits, prog2Out_singleA, encodeNat_add]

theorem prog2Out_spJ (c a k : ℕ) : prog2Out (spJ c) a k = encodeNat (k + c) := by
  rw [spJ, prog2Out_append, prog2Out_bits, prog2Out_singleJ, encodeNat_add]

/-! ## Family 1 — the state one-hot at-least-one

The mirror of the head family: `encodeClause'_atLeastOne_state` pins the clause at time `t` to
`encodeNat card ++ (for q in 0..card-1: encodeNat t · encodeNat q · encodeNat 2 · [true])`. -/

def aloStateBody : List LInstr :=
  [.spliceA, .spliceJ, .bit true, .bit true, .bit false, .bit true]

theorem aloState_prog2Out (t q : ℕ) :
    prog2Out aloStateBody t q = encodeNat t ++ (encodeNat q ++ (encodeNat 2 ++ [true])) := by
  show prog2OutN aloStateBody t q 6 = _
  simp [prog2OutN, instr2Out, aloStateBody, encodeNat, List.append_assoc]

/-- **The clause factors through the loop denotation.** -/
theorem aloState_split (t card : ℕ) :
    encodeClause' (atLeastOne ((List.range card).map (stateVar t)))
      = encodeNat card ++ loop2Out aloStateBody t card := by
  rw [encodeClause'_atLeastOne_state, loop2Out_eq_flatten]
  congr 2
  apply List.map_congr_left
  intro q hq
  exact (aloState_prog2Out t q).symm

/-- **The state one-hot at-least-one family emitter**: with the count block on the output, the loop
completes exactly the clause's encoding. -/
theorem aloState_family_run (t card : ℕ) (out : List Bool) :
    run (loopProg2Machine aloStateBody)
      (lp2Clock aloStateBody card t (out ++ encodeNat card).length)
      (init (loopProg2Machine aloStateBody)
        (unaryD card ++ (unaryD t ++ (jT card 0 ++ encodeD (out ++ encodeNat card)))))
      = ⟨(78, ⟨0, Nat.succ_pos _⟩, false), 2 * card + 1,
          unaryD card ++ (unaryD t ++ (unaryD card ++ encodeD (out
            ++ encodeClause' (atLeastOne ((List.range card).map (stateVar t))))))⟩ := by
  rw [loopProg2_run, aloState_split, List.append_assoc]

/-! ## Family 2 — the tape-copy family

`cellCopyClause t p` is two three-literal clauses; **one body emits both per round**, so the whole
family at time `t` is a single `P+1`-round loop. -/

def cellCopyFstBody : List LInstr :=
  bitsI [true, true, true, false] ++ (spA 0 ++ (spJ 0 ++ (bitsI [true, false, true]
    ++ (spA 1 ++ (spJ 0 ++ (bitsI [false, false] ++ (spA 0 ++ (spJ 0
      ++ bitsI [false, true]))))))))

def cellCopySndBody : List LInstr :=
  bitsI [true, true, true, false] ++ (spA 0 ++ (spJ 0 ++ (bitsI [true, false, true]
    ++ (spA 1 ++ (spJ 0 ++ (bitsI [false, true] ++ (spA 0 ++ (spJ 0
      ++ bitsI [false, false]))))))))

def cellCopyBody : List LInstr := cellCopyFstBody ++ cellCopySndBody

theorem cellCopyFst_prog2Out (t p : ℕ) :
    prog2Out cellCopyFstBody t p
      = encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false), (cellVar t p, true)] := by
  rw [encodeClause'_cellCopy_fst, cellCopyFstBody]
  simp only [prog2Out_append, prog2Out_bits, prog2Out_spA, prog2Out_spJ]
  simp [encodeNat, List.append_assoc]

theorem cellCopySnd_prog2Out (t p : ℕ) :
    prog2Out cellCopySndBody t p
      = encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true), (cellVar t p, false)] := by
  rw [encodeClause'_cellCopy_snd, cellCopySndBody]
  simp only [prog2Out_append, prog2Out_bits, prog2Out_spA, prog2Out_spJ]
  simp [encodeNat, List.append_assoc]

/-- One round emits **both** clauses of `cellCopyClause t p`. -/
theorem cellCopy_prog2Out (t p : ℕ) :
    prog2Out cellCopyBody t p
      = encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false), (cellVar t p, true)]
        ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
             (cellVar t p, false)] := by
  rw [cellCopyBody, prog2Out_append, cellCopyFst_prog2Out, cellCopySnd_prog2Out]

/-- **The tape-copy family at time `t` factors through the loop denotation.** -/
theorem cellCopy_split (t P : ℕ) :
    loop2Out cellCopyBody t (P + 1)
      = ((List.range (P + 1)).map (fun p =>
          encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false), (cellVar t p, true)]
            ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
                 (cellVar t p, false)])).flatten := by
  rw [loop2Out_eq_flatten]
  exact congrArg List.flatten (List.map_congr_left (fun p _ => cellCopy_prog2Out t p))

/-- **The tape-copy family emitter**: one machine run emits the whole family at time `t` — both clauses
of every `cellCopyClause t p`, `p = 0..P`, in order. -/
theorem cellCopy_family_run (t P : ℕ) (out : List Bool) :
    run (loopProg2Machine cellCopyBody) (lp2Clock cellCopyBody (P + 1) t out.length)
      (init (loopProg2Machine cellCopyBody)
        (unaryD (P + 1) ++ (unaryD t ++ (jT (P + 1) 0 ++ encodeD out))))
      = ⟨(78, ⟨0, Nat.succ_pos _⟩, false), 2 * (P + 1) + 1,
          unaryD (P + 1) ++ (unaryD t ++ (unaryD (P + 1) ++ encodeD (out
            ++ ((List.range (P + 1)).map (fun p =>
                encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false),
                  (cellVar t p, true)]
                  ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
                       (cellVar t p, false)])).flatten)))⟩ := by
  rw [loopProg2_run, cellCopy_split]

/-! ## Family 3 — the write family

The implication-window guard prefix is shared by the write and dynamics families; the write
conclusion is the written cell bit — a machine constant per `(q̂, b)` (`writtenBit`). -/

/-- The shared implication-window guard prefix: count block `4`, the three negated guards at
`(t, q̂)`, `(t, p)`, `(t, p)` with tag blocks `2, 1, 0` and signs `false, false, !b`. -/
def winPre (qi : ℕ) (b : Bool) : List LInstr :=
  bitsI [true, true, true, true, false] ++ (spA 0 ++ (bitsI (encodeNat qi)
    ++ (bitsI [true, true, false, false] ++ (spA 0 ++ (spJ 0
      ++ (bitsI [true, false, false] ++ (spA 0 ++ (spJ 0 ++ bitsI [false, !b]))))))))

theorem winPre_prog2Out (qi : ℕ) (b : Bool) (t p : ℕ) :
    prog2Out (winPre qi b) t p
      = encodeNat 4 ++ (encodeNat t ++ (encodeNat qi ++ (encodeNat 2 ++ ([false]
          ++ (encodeNat t ++ (encodeNat p ++ (encodeNat 1 ++ ([false]
          ++ (encodeNat t ++ (encodeNat p ++ (encodeNat 0 ++ [!b]))))))))))) := by
  rw [winPre]
  simp only [prog2Out_append, prog2Out_bits, prog2Out_spA, prog2Out_spJ]
  simp [encodeNat, List.append_assoc]

/-- The write window's body at guard `(q̂, b)`, written bit `wb`. -/
def writeBody (qi : ℕ) (b wb : Bool) : List LInstr :=
  winPre qi b ++ (spA 1 ++ (spJ 0 ++ bitsI [false, wb]))

/-- **The write window factors.** -/
theorem writeBody_prog2Out (qi : ℕ) (b wb : Bool) (t p : ℕ) :
    prog2Out (writeBody qi b wb) t p
      = encodeClause' (implClause (stateVar t qi, true) (headVar t p, true) (cellVar t p, b)
          (cellVar (t + 1) p, wb)) := by
  rw [encodeClause'_implWindow, encodeLit'_cellVar, writeBody]
  simp only [prog2Out_append, winPre_prog2Out, prog2Out_bits, prog2Out_spA, prog2Out_spJ]
  simp [encodeNat, List.append_assoc]

/-- The write family's `p`-loop at guard `(q̂, b)` factors through the loop denotation. -/
theorem write_split (qi : ℕ) (b wb : Bool) (t P : ℕ) :
    loop2Out (writeBody qi b wb) t (P + 1)
      = ((List.range (P + 1)).map (fun p =>
          encodeClause' (implClause (stateVar t qi, true) (headVar t p, true) (cellVar t p, b)
            (cellVar (t + 1) p, wb)))).flatten := by
  rw [loop2Out_eq_flatten]
  exact congrArg List.flatten (List.map_congr_left (fun p _ => writeBody_prog2Out qi b wb t p))

/-- **The write family emitter**: for each of the finitely many guards `(q̂, b)`, one machine run emits
the write windows at every head position `p = 0..P` at time `t`.  At instantiation
`wb := writtenBit M ((Fintype.equivFin M.State).symm q̂) b` these are exactly the members of
`writeClause M t q̂ p b` (`writeClause_members`). -/
theorem write_family_run (qi : ℕ) (b wb : Bool) (t P : ℕ) (out : List Bool) :
    run (loopProg2Machine (writeBody qi b wb))
      (lp2Clock (writeBody qi b wb) (P + 1) t out.length)
      (init (loopProg2Machine (writeBody qi b wb))
        (unaryD (P + 1) ++ (unaryD t ++ (jT (P + 1) 0 ++ encodeD out))))
      = ⟨(78, ⟨0, Nat.succ_pos _⟩, false), 2 * (P + 1) + 1,
          unaryD (P + 1) ++ (unaryD t ++ (unaryD (P + 1) ++ encodeD (out
            ++ ((List.range (P + 1)).map (fun p =>
                encodeClause' (implClause (stateVar t qi, true) (headVar t p, true)
                  (cellVar t p, b) (cellVar (t + 1) p, wb)))).flatten)))⟩ := by
  rw [loopProg2_run, write_split]

/-! ## Family 4 — the dynamics windows

Two windows per guard: the state conclusion and the head conclusion.  `nextStateIdx` is
head-independent (proved below), so the state conclusion's index is a machine constant per `(q̂, b)`;
the head conclusion has four shapes by the move — stay, right (`p+1`, a free offset), reset (`0`,
fixed bits), and left (`p-1`, emitted with the reindexed live variable `j := p-1`). -/

/-- **`δ`'s next state does not depend on the head position** — the dynamics state-conclusion block is
a machine constant per `(q̂, b)`. -/
theorem nextStateIdx_head_independent (M : Machine) (q : Fin (Fintype.card M.State))
    (b : Bool) (p p' : ℕ) : nextStateIdx M q p b = nextStateIdx M q p' b := by
  unfold nextStateIdx stepStateHead
  by_cases hh : M.halt ((Fintype.equivFin M.State).symm q) = true <;> simp [hh]

/-- The state-conclusion dynamics window (`qc` = the `δ`-next state index). -/
def dynStateBody (qi qc : ℕ) (b : Bool) : List LInstr :=
  winPre qi b ++ (spA 1 ++ (bitsI (encodeNat qc) ++ bitsI [true, true, false, true]))

theorem dynStateBody_prog2Out (qi qc : ℕ) (b : Bool) (t p : ℕ) :
    prog2Out (dynStateBody qi qc b) t p
      = encodeClause' (implClause (stateVar t qi, true) (headVar t p, true) (cellVar t p, b)
          (stateVar (t + 1) qc, true)) := by
  rw [encodeClause'_implWindow, encodeLit'_stateVar, dynStateBody]
  simp only [prog2Out_append, winPre_prog2Out, prog2Out_bits, prog2Out_spA]
  simp [encodeNat, List.append_assoc]

/-- The head-conclusion window, **stay** (`h = p`; also the halting self-loop). -/
def dynHeadStayBody (qi : ℕ) (b : Bool) : List LInstr :=
  winPre qi b ++ (spA 1 ++ (spJ 0 ++ bitsI [true, false, true]))

theorem dynHeadStayBody_prog2Out (qi : ℕ) (b : Bool) (t p : ℕ) :
    prog2Out (dynHeadStayBody qi b) t p
      = encodeClause' (implClause (stateVar t qi, true) (headVar t p, true) (cellVar t p, b)
          (headVar (t + 1) p, true)) := by
  rw [encodeClause'_implWindow, encodeLit'_headVar, dynHeadStayBody]
  simp only [prog2Out_append, winPre_prog2Out, prog2Out_bits, prog2Out_spA, prog2Out_spJ]
  simp [encodeNat, List.append_assoc]

/-- The head-conclusion window, **right** (`h = p + 1`, a free offset). -/
def dynHeadRightBody (qi : ℕ) (b : Bool) : List LInstr :=
  winPre qi b ++ (spA 1 ++ (spJ 1 ++ bitsI [true, false, true]))

theorem dynHeadRightBody_prog2Out (qi : ℕ) (b : Bool) (t p : ℕ) :
    prog2Out (dynHeadRightBody qi b) t p
      = encodeClause' (implClause (stateVar t qi, true) (headVar t p, true) (cellVar t p, b)
          (headVar (t + 1) (p + 1), true)) := by
  rw [encodeClause'_implWindow, encodeLit'_headVar, dynHeadRightBody]
  simp only [prog2Out_append, winPre_prog2Out, prog2Out_bits, prog2Out_spA, prog2Out_spJ]
  simp [encodeNat, List.append_assoc]

/-- The head-conclusion window, **reset** (`h = 0`, fixed bits). -/
def dynHeadResetBody (qi : ℕ) (b : Bool) : List LInstr :=
  winPre qi b ++ (spA 1 ++ bitsI [false, true, false, true])

theorem dynHeadResetBody_prog2Out (qi : ℕ) (b : Bool) (t p : ℕ) :
    prog2Out (dynHeadResetBody qi b) t p
      = encodeClause' (implClause (stateVar t qi, true) (headVar t p, true) (cellVar t p, b)
          (headVar (t + 1) 0, true)) := by
  rw [encodeClause'_implWindow, encodeLit'_headVar, dynHeadResetBody]
  simp only [prog2Out_append, winPre_prog2Out, prog2Out_bits, prog2Out_spA]
  simp [encodeNat, List.append_assoc]

/-- The reindexed guard prefix for the left-mover: the live variable is `j := p - 1`, so the head and
cell guards read `j + 1`. -/
def winPreL (qi : ℕ) (b : Bool) : List LInstr :=
  bitsI [true, true, true, true, false] ++ (spA 0 ++ (bitsI (encodeNat qi)
    ++ (bitsI [true, true, false, false] ++ (spA 0 ++ (spJ 1
      ++ (bitsI [true, false, false] ++ (spA 0 ++ (spJ 1 ++ bitsI [false, !b]))))))))

/-- The head-conclusion window, **left** (`h = p - 1`), emitted at the reindexed variable `j = p - 1`:
guards at `j + 1`, conclusion at `j`. -/
def dynHeadLeftBody (qi : ℕ) (b : Bool) : List LInstr :=
  winPreL qi b ++ (spA 1 ++ (spJ 0 ++ bitsI [true, false, true]))

theorem dynHeadLeftBody_prog2Out (qi : ℕ) (b : Bool) (t j : ℕ) :
    prog2Out (dynHeadLeftBody qi b) t j
      = encodeClause' (implClause (stateVar t qi, true) (headVar t (j + 1), true)
          (cellVar t (j + 1), b) (headVar (t + 1) j, true)) := by
  rw [encodeClause'_implWindow, encodeLit'_headVar, dynHeadLeftBody, winPreL]
  simp only [prog2Out_append, prog2Out_bits, prog2Out_spA, prog2Out_spJ]
  simp [encodeNat, List.append_assoc]

/-- The dynamics head-window family's `p`-loops factor: shown for the right-mover (the stay, reset,
and state-conclusion variants are verbatim analogues via their own `_prog2Out` lemmas). -/
theorem dynHeadRight_split (qi : ℕ) (b : Bool) (t P : ℕ) :
    loop2Out (dynHeadRightBody qi b) t (P + 1)
      = ((List.range (P + 1)).map (fun p =>
          encodeClause' (implClause (stateVar t qi, true) (headVar t p, true) (cellVar t p, b)
            (headVar (t + 1) (p + 1), true)))).flatten := by
  rw [loop2Out_eq_flatten]
  exact congrArg List.flatten
    (List.map_congr_left (fun p _ => dynHeadRightBody_prog2Out qi b t p))

theorem dynState_split (qi qc : ℕ) (b : Bool) (t P : ℕ) :
    loop2Out (dynStateBody qi qc b) t (P + 1)
      = ((List.range (P + 1)).map (fun p =>
          encodeClause' (implClause (stateVar t qi, true) (headVar t p, true) (cellVar t p, b)
            (stateVar (t + 1) qc, true)))).flatten := by
  rw [loop2Out_eq_flatten]
  exact congrArg List.flatten
    (List.map_congr_left (fun p _ => dynStateBody_prog2Out qi qc b t p))

/-- **A dynamics family emitter** (the state-conclusion window, one guard `(q̂, b)`): one machine run
emits the window at every head position.  At instantiation `qc := nextStateIdx M q̂ 0 b`
(head-independence making the choice of `0` immaterial), these are the first members of
`dynamicsClause M t q̂ p b` across `p` (`dynamicsClause_members`). -/
theorem dynState_family_run (qi qc : ℕ) (b : Bool) (t P : ℕ) (out : List Bool) :
    run (loopProg2Machine (dynStateBody qi qc b))
      (lp2Clock (dynStateBody qi qc b) (P + 1) t out.length)
      (init (loopProg2Machine (dynStateBody qi qc b))
        (unaryD (P + 1) ++ (unaryD t ++ (jT (P + 1) 0 ++ encodeD out))))
      = ⟨(78, ⟨0, Nat.succ_pos _⟩, false), 2 * (P + 1) + 1,
          unaryD (P + 1) ++ (unaryD t ++ (unaryD (P + 1) ++ encodeD (out
            ++ ((List.range (P + 1)).map (fun p =>
                encodeClause' (implClause (stateVar t qi, true) (headVar t p, true)
                  (cellVar t p, b) (stateVar (t + 1) qc, true)))).flatten)))⟩ := by
  rw [loopProg2_run, dynState_split]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies