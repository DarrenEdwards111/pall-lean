import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCodec

/-!
# Cook–Levin M2 emitter, E3 (ii) — the five clause-shape bit-layouts (pure)

Second brick of E3 (`SCOPE_EMITTER.md` §3): the **emission specifications** of the tableau's clause templates.
For each clause shape the tableau uses — unit / at-most-one pair / guarded-iff triple / implication window /
at-least-one — this file proves the exact coordinate-codec bit-layout: the clause's `encodeClause'` string
**is** a fixed skeleton (literal-count blocks, tag blocks, sign bits) with the loop counters spliced in as
unary coordinate blocks.  This is where the E0 emitter-friendliness lemmas
(`encodeLit'_cellVar`/`_headVar`/`_stateVar`) are consumed: no `Nat.pair`, no `×3` appears in any layout —
only `encodeNat` blocks of values the emitting loop already holds (`t`, `p`, `q̂`, `t+1`, …) and fixed bits.

Layout convention: right-associated `++` of `encodeNat`-blocks and literal sign bits — exactly the block
stream the E3 machines produce (`...EmitAppendBlock` appends the fixed blocks; the counter-splice machine,
next, appends the `encodeNat (counter)` blocks).  Also proved: the template-instantiation identities
(`cellCopyClause_members`, `dynamicsClause_members`, `writeClause_members`, `initFormula_members`) pinning
each tableau family to these five shapes, and the at-least-one layouts in per-literal mapped form (the
at-least-one is the one *loop-shaped* template — its literal count is a counter, so its emitter is a loop
over `p`; its per-iteration block stream is pinned here, the loop itself belongs with E4's machinery).

Everything is pure and definitional-plus-`E0`; no machine content.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec

/-! ## Shape 1 — the unit clause (the init fixes)

One literal: count block `encodeNat 1`, one coordinate literal.  The sign of the cell unit is the spliced
input bit (`x.getD p false` — E5's concern); the state/head units are fully fixed. -/

theorem encodeClause'_unit_cell (t p : ℕ) (s : Bool) :
    encodeClause' [(cellVar t p, s)]
      = encodeNat 1 ++ (encodeNat t ++ (encodeNat p ++ (encodeNat 0 ++ [s]))) := by
  simp [encodeClause', encodeLit'_cellVar, List.append_assoc]

theorem encodeClause'_unit_head (t p : ℕ) (s : Bool) :
    encodeClause' [(headVar t p, s)]
      = encodeNat 1 ++ (encodeNat t ++ (encodeNat p ++ (encodeNat 1 ++ [s]))) := by
  simp [encodeClause', encodeLit'_headVar, List.append_assoc]

theorem encodeClause'_unit_state (t q : ℕ) (s : Bool) :
    encodeClause' [(stateVar t q, s)]
      = encodeNat 1 ++ (encodeNat t ++ (encodeNat q ++ (encodeNat 2 ++ [s]))) := by
  simp [encodeClause', encodeLit'_stateVar, List.append_assoc]

/-- The init family is exactly a stream of unit clauses: one fixed state unit, one fixed head unit, and the
input-spliced cell units. -/
theorem initFormula_members (M : Machine) (x : List Bool) (P : ℕ) :
    initFormula M x P
      = [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
          :: [(headVar 0 0, true)]
          :: (List.range (P + 1)).map (fun p => [(cellVar 0 p, x.getD p false)]) := by
  simp [initFormula, fixBits]

/-! ## Shape 2 — the at-most-one pair (the one-hot families' quadratic parts)

Two negative literals of the same kind at a shared time `t`: count block `encodeNat 2`, two coordinate
literals with fixed tags and fixed `false` signs — the counters spliced are `t, i, t, j`. -/

theorem encodeClause'_amoPair_head (t i j : ℕ) :
    encodeClause' [(headVar t i, false), (headVar t j, false)]
      = encodeNat 2 ++ (encodeNat t ++ (encodeNat i ++ (encodeNat 1 ++ ([false]
          ++ (encodeNat t ++ (encodeNat j ++ (encodeNat 1 ++ [false]))))))) := by
  simp [encodeClause', encodeLit'_headVar, List.append_assoc]

theorem encodeClause'_amoPair_state (t i j : ℕ) :
    encodeClause' [(stateVar t i, false), (stateVar t j, false)]
      = encodeNat 2 ++ (encodeNat t ++ (encodeNat i ++ (encodeNat 2 ++ ([false]
          ++ (encodeNat t ++ (encodeNat j ++ (encodeNat 2 ++ [false]))))))) := by
  simp [encodeClause', encodeLit'_stateVar, List.append_assoc]

/-! ## Shape 3 — the guarded-iff triple (the tape-copy family)

`cellCopyClause t p` is two three-literal clauses over the coordinates `(t, p)` and `(t+1, p)`: fixed count
blocks `encodeNat 3`, fixed tags and signs, spliced counters `t, p, t+1`. -/

/-- The tape-copy template's exact members. -/
theorem cellCopyClause_members (t p : ℕ) :
    cellCopyClause t p
      = [[(headVar t p, true), (cellVar (t + 1) p, false), (cellVar t p, true)],
         [(headVar t p, true), (cellVar (t + 1) p, true), (cellVar t p, false)]] := rfl

theorem encodeClause'_cellCopy_fst (t p : ℕ) :
    encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false), (cellVar t p, true)]
      = encodeNat 3 ++ (encodeNat t ++ (encodeNat p ++ (encodeNat 1 ++ ([true]
          ++ (encodeNat (t + 1) ++ (encodeNat p ++ (encodeNat 0 ++ ([false]
          ++ (encodeNat t ++ (encodeNat p ++ (encodeNat 0 ++ [true]))))))))))) := by
  simp [encodeClause', encodeLit'_headVar, encodeLit'_cellVar, List.append_assoc]

theorem encodeClause'_cellCopy_snd (t p : ℕ) :
    encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true), (cellVar t p, false)]
      = encodeNat 3 ++ (encodeNat t ++ (encodeNat p ++ (encodeNat 1 ++ ([true]
          ++ (encodeNat (t + 1) ++ (encodeNat p ++ (encodeNat 0 ++ ([true]
          ++ (encodeNat t ++ (encodeNat p ++ (encodeNat 0 ++ [false]))))))))))) := by
  simp [encodeClause', encodeLit'_headVar, encodeLit'_cellVar, List.append_assoc]

/-! ## Shape 4 — the implication window (the dynamics and write families)

Four literals: the three negated window guards (state `q̂` on, head at `p`, cell reads `b` — all at time `t`)
and a conclusion literal at time `t+1`.  Count block `encodeNat 4`, fixed tags, signs `false, false, !b`;
spliced counters `t, q̂, t, p, t, p`, then the conclusion's own coordinate literal. -/

theorem encodeClause'_implWindow (t qi p : ℕ) (b : Bool) (concl : Lit) :
    encodeClause' (implClause (stateVar t qi, true) (headVar t p, true) (cellVar t p, b) concl)
      = encodeNat 4 ++ (encodeNat t ++ (encodeNat qi ++ (encodeNat 2 ++ ([false]
          ++ (encodeNat t ++ (encodeNat p ++ (encodeNat 1 ++ ([false]
          ++ (encodeNat t ++ (encodeNat p ++ (encodeNat 0 ++ ((!b)
          :: encodeLit' concl)))))))))))) := by
  simp [implClause, encodeClause', encodeLit'_stateVar, encodeLit'_headVar, encodeLit'_cellVar,
    List.append_assoc]

/-- The dynamics template's exact members: two implication windows, concluding in the `δ`-next state and the
`δ`-next head. -/
theorem dynamicsClause_members (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (p : ℕ)
    (b : Bool) :
    dynamicsClause M t q p b
      = [implClause (stateVar t q.val, true) (headVar t p, true) (cellVar t p, b)
           (stateVar (t + 1) (nextStateIdx M q p b), true),
         implClause (stateVar t q.val, true) (headVar t p, true) (cellVar t p, b)
           (headVar (t + 1) (nextHead M q p b), true)] := rfl

/-- The write template's exact member: one implication window, concluding in the written cell bit. -/
theorem writeClause_members (M : Machine) (t : ℕ) (q : Fin (Fintype.card M.State)) (p : ℕ)
    (b : Bool) :
    writeClause M t q p b
      = [implClause (stateVar t q.val, true) (headVar t p, true) (cellVar t p, b)
           (cellVar (t + 1) p, writtenBit M ((Fintype.equivFin M.State).symm q) b)] := rfl

/-! ## Shape 5 — the at-least-one (the loop-shaped template)

The one template whose literal count is itself a counter (`P + 1`, `card`, `|acceptStates|`): its emitter is a
loop over the varying coordinate.  Pinned here: the count block is the counter's `encodeNat`, and each loop
iteration's block stream is one fixed-tag coordinate literal with the loop counter spliced. -/

theorem encodeClause'_atLeastOne_head (t P : ℕ) :
    encodeClause' (atLeastOne ((List.range (P + 1)).map (headVar t)))
      = encodeNat (P + 1)
          ++ ((List.range (P + 1)).map
                (fun p => encodeNat t ++ (encodeNat p ++ (encodeNat 1 ++ [true])))).flatten := by
  simp [atLeastOne, encodeClause', List.map_map, Function.comp_def, encodeLit'_headVar,
    List.append_assoc]

theorem encodeClause'_atLeastOne_state (t card : ℕ) :
    encodeClause' (atLeastOne ((List.range card).map (stateVar t)))
      = encodeNat card
          ++ ((List.range card).map
                (fun q => encodeNat t ++ (encodeNat q ++ (encodeNat 2 ++ [true])))).flatten := by
  simp [atLeastOne, encodeClause', List.map_map, Function.comp_def, encodeLit'_stateVar,
    List.append_assoc]

/-- The accept clause's layout: an at-least-one over the accepting-halting state indices at time `B` — the
loop runs over the fixed accepting-state list, splicing `B` and each index. -/
theorem encodeClause'_accept (M : Machine) (B : ℕ) :
    encodeClause' (atLeastOne ((acceptStates M).map (fun q => stateVar B q.val)))
      = encodeNat (acceptStates M).length
          ++ ((acceptStates M).map
                (fun q => encodeNat B ++ (encodeNat q.val ++ (encodeNat 2 ++ [true])))).flatten := by
  simp [atLeastOne, encodeClause', List.map_map, Function.comp_def, encodeLit'_stateVar,
    List.append_assoc]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
