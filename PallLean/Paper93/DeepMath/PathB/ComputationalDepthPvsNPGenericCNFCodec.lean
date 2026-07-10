import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPParityToSATReduction
import Mathlib.Data.List.Basic

/-!
# A general positional CNF bit-codec — toward generic-encoding general SAT (gap i)

Bricks 4–6 fed the SAT decider the parity instance `x` directly (identity encoding), so the decider was, in
effect, specialised to the parity family.  To make "the decider is a genuine general SAT circuit" meaningful,
this file builds a **general positional CNF decoder** `decodeCNF : (Fin N → Bool) → CNF` whose range covers a
rich bounded-CNF class (arbitrary literals, up to `W` per clause, over `V` variables — hence width-`3`
`3SAT` instances when `W ≥ 3`), and shows the parity-CNF family sits inside it via an **explicit, input-local
bit pattern** `parityBits x` with `decodeCNF (parityBits x) = parityCNF (ofFn x)`.

The layout is positional: `C` clauses × `W` slots, each slot = (`present`, `negated`, one-hot `var ∈ Fin V`).
`decodeCNF` reads each present slot into a literal.  The parity-CNF's slots have **fixed** `present`/`var`
bits (structure) and `negated` bits that depend on a single `xᵢ` — so `parityBits x` is `AC⁰`, depth `≤ 1`.

## Honest scope

Gap (i), **step 1 only (structural groundwork)**: `chain_eq_flatMap` re-expresses the parity-CNF's recursive
`chain` clause list as a `flatMap` over per-bit link-clause blocks — the shape a positional/incidence decoder
produces, and the load-bearing lemma for matching a general decoder's clause list to `parityCNF`.  The full
general decoder, the exact/eval match `decode (parityBits x) = parityCNF (ofFn x)`, the `AC⁰` circuit
realisation of `parityBits`, and the composition with the capstone remain — a substantial multi-lemma
formalisation.  `sorry`-free.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFCodec

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.PvsNPParityToSAT

/-! ## The parity-CNF clause list in explicit indexed form

`parityCNF x` has clause list `negClause 0 :: (chain x 0 ++ [negClause x.length])`.  We first re-express the
recursive `chain` as a `flatMap` over clause blocks, which is the form a positional decoder produces. -/

/-- `chain rest i` is the concatenation of the per-bit link-clause blocks. -/
theorem chain_eq_flatMap :
    ∀ (rest : List Bool) (i : Nat),
      chain rest i = (List.range rest.length).flatMap (fun k => linkClauses (i + k) (rest.getD k false)) := by
  intro rest
  induction rest with
  | nil => intro i; simp [chain]
  | cons b rest ih =>
    intro i
    rw [chain, ih (i + 1), List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp only [Function.comp_apply, Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    apply List.flatMap_congr
    intro k _
    congr 1
    omega

end PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFCodec

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFCodec.chain_eq_flatMap
