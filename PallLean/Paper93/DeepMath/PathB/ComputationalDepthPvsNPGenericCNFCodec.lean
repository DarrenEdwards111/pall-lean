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

/-! ## A general per-clause incidence decoder

`decodeClause V inc` reads an incidence function `inc : Fin V → Bool → Bool` (for each variable and sign,
is that literal present?) into a clause.  This covers **arbitrary** clauses over `V` variables (any width),
so the whole-CNF decoder built on it covers arbitrary bounded CNFs — a genuine general SAT encoding. -/

open SATDepthMachine

/-- Decode one clause from a variable-indexed incidence function. -/
def decodeClause (V : Nat) (inc : Fin V → Bool → Bool) : Clause :=
  (List.finRange V).flatMap (fun v =>
    (if inc v true then [({ var := v.val, pol := Polarity.pos } : Lit)] else []) ++
    (if inc v false then [({ var := v.val, pol := Polarity.neg } : Lit)] else []))

/-- Membership in a decoded clause is exactly the incidence. -/
theorem mem_decodeClause (V : Nat) (inc : Fin V → Bool → Bool) (lit : Lit) :
    lit ∈ decodeClause V inc ↔
      ∃ v : Fin V, (inc v true = true ∧ lit = ⟨v.val, Polarity.pos⟩) ∨
                   (inc v false = true ∧ lit = ⟨v.val, Polarity.neg⟩) := by
  simp only [decodeClause, List.mem_flatMap, List.mem_finRange, true_and, List.mem_append]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    rcases hv with hv | hv
    · left
      by_cases hc : inc v true = true
      · simp only [hc, if_true, List.mem_singleton] at hv; exact ⟨hc, hv⟩
      · simp only [Bool.not_eq_true] at hc; simp [hc] at hv
    · right
      by_cases hc : inc v false = true
      · simp only [hc, if_true, List.mem_singleton] at hv; exact ⟨hc, hv⟩
      · simp only [Bool.not_eq_true] at hc; simp [hc] at hv
  · rintro ⟨v, hv | hv⟩
    · exact ⟨v, Or.inl (by simp [hv.1, hv.2])⟩
    · exact ⟨v, Or.inr (by simp [hv.1, hv.2])⟩

/-- Two clauses with the same literal membership evaluate identically under any assignment. -/
theorem clause_eval_congr (a : RawAssignment) (c1 c2 : Clause)
    (h : ∀ lit, lit ∈ c1 ↔ lit ∈ c2) : Clause.eval a c1 = Clause.eval a c2 := by
  simp only [Clause.eval]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨lit, hm, he⟩; exact ⟨lit, (h lit).mp hm, he⟩
  · rintro ⟨lit, hm, he⟩; exact ⟨lit, (h lit).mpr hm, he⟩

/-! ## The whole-CNF decoder, laid out to match `parityCNF`

`decodeCNF n headInc blockInc1 blockInc2 tailInc` produces a CNF over `n+1` variables with `2n+2` clauses in
the layout `head :: (blocks ++ [tail])`, where each clause's contents are read from its own incidence
function — so the range is **arbitrary bounded CNFs**.  The layout mirrors `parityCNF`'s clause order, which
makes the equivalence proof component-by-component. -/

/-- General bounded-CNF decoder, laid out `head :: (n link-blocks of 2) ++ [tail]`. -/
def decodeCNF (n : Nat)
    (headInc : Fin (n + 1) → Bool → Bool)
    (blockInc1 blockInc2 : Nat → Fin (n + 1) → Bool → Bool)
    (tailInc : Fin (n + 1) → Bool → Bool) : CNF :=
  { vars := n + 1,
    clauses := decodeClause (n + 1) headInc ::
      ((List.range n).flatMap (fun k =>
          [decodeClause (n + 1) (blockInc1 k), decodeClause (n + 1) (blockInc2 k)])
        ++ [decodeClause (n + 1) tailInc]) }

/-- Head incidence: the single literal `¬p₀`. -/
def bvHead (n : Nat) : Fin (n + 1) → Bool → Bool := fun v s => decide (v.val = 0) && !s

/-- Tail incidence: the single literal `¬pₙ`. -/
def bvTail (n : Nat) : Fin (n + 1) → Bool → Bool := fun v s => decide (v.val = n) && !s

/-- First link-clause incidence of block `k`: literals `p_{k+1}` and `(sign `xₖ`) pₖ`. -/
def bvBlock1 {n : Nat} (x : Fin n → Bool) (k : Nat) : Fin (n + 1) → Bool → Bool := fun v s =>
  (decide (v.val = k + 1) && s) || (decide (v.val = k) && (s == (List.ofFn x).getD k false))

/-- Second link-clause incidence of block `k`: literals `¬p_{k+1}` and `(sign `¬xₖ`) pₖ`. -/
def bvBlock2 {n : Nat} (x : Fin n → Bool) (k : Nat) : Fin (n + 1) → Bool → Bool := fun v s =>
  (decide (v.val = k + 1) && !s) || (decide (v.val = k) && (s == !((List.ofFn x).getD k false)))

/-- Membership of a `negClause`. -/
theorem mem_negClause (j : Nat) (lit : Lit) :
    lit ∈ negClause j ↔ lit = ⟨j, Polarity.neg⟩ := by
  simp [negClause]

/-- **Head component:** the decoded head clause has the same literals as `negClause 0`. -/
theorem decodeClause_bvHead_mem (n : Nat) (lit : Lit) :
    lit ∈ decodeClause (n + 1) (bvHead n) ↔ lit ∈ negClause 0 := by
  rw [mem_decodeClause, mem_negClause]
  constructor
  · rintro ⟨v, hv | hv⟩
    · simp only [bvHead, Bool.and_eq_true, Bool.not_eq_true'] at hv; simp at hv
    · simp only [bvHead, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hv0, _⟩, hlit⟩ := hv
      rw [hlit, hv0]
  · intro hlit
    refine ⟨⟨0, by omega⟩, Or.inr ⟨?_, ?_⟩⟩
    · simp [bvHead]
    · rw [hlit]

/-- **Tail component:** the decoded tail clause has the same literals as `negClause n`. -/
theorem decodeClause_bvTail_mem (n : Nat) (lit : Lit) :
    lit ∈ decodeClause (n + 1) (bvTail n) ↔ lit ∈ negClause n := by
  rw [mem_decodeClause, mem_negClause]
  constructor
  · rintro ⟨v, hv | hv⟩
    · simp only [bvTail, Bool.and_eq_true, Bool.not_eq_true'] at hv; simp at hv
    · simp only [bvTail, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hvn, _⟩, hlit⟩ := hv
      rw [hlit, hvn]
  · intro hlit
    refine ⟨⟨n, by omega⟩, Or.inr ⟨?_, ?_⟩⟩
    · simp [bvTail]
    · rw [hlit]

/-- The two clauses of a link block, explicitly. -/
def linkClause1 (k : Nat) (b : Bool) : Clause :=
  [⟨k + 1, Polarity.pos⟩, ⟨k, if b then Polarity.pos else Polarity.neg⟩]

def linkClause2 (k : Nat) (b : Bool) : Clause :=
  [⟨k + 1, Polarity.neg⟩, ⟨k, if b then Polarity.neg else Polarity.pos⟩]

theorem linkClauses_eq (k : Nat) (b : Bool) :
    linkClauses k b = [linkClause1 k b, linkClause2 k b] := by
  cases b <;> simp [linkClauses, linkClause1, linkClause2]

/-- **First link-clause component:** the decoded first block clause matches `linkClause1`. -/
theorem decodeClause_bvBlock1_mem {n : Nat} (x : Fin n → Bool) (k : Nat) (hk : k < n) (lit : Lit) :
    lit ∈ decodeClause (n + 1) (bvBlock1 x k) ↔
      lit ∈ linkClause1 k ((List.ofFn x).getD k false) := by
  rw [mem_decodeClause]
  simp only [linkClause1, List.mem_cons, List.not_mem_nil, or_false,
    bvBlock1, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.and_true,
    Bool.and_false, Bool.false_or, Bool.or_false]
  constructor
  · rintro ⟨v, ⟨hc, rfl⟩ | ⟨hc, rfl⟩⟩
    · rcases hc with h1 | ⟨h1, _⟩
      · exact Or.inl (by rw [h1])
      · right; rw [h1]; rcases hx : (List.ofFn x).getD k false <;> simp_all
    · rcases hc with ⟨h1, _⟩
      right; rw [h1]; rcases hx : (List.ofFn x).getD k false <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨⟨k + 1, by omega⟩, Or.inl ⟨Or.inl rfl, rfl⟩⟩
    · rcases hx : (List.ofFn x).getD k false <;>
        [exact ⟨⟨k, by omega⟩, Or.inr ⟨⟨rfl, by simp [hx]⟩, by simp [hx]⟩⟩;
         exact ⟨⟨k, by omega⟩, Or.inl ⟨Or.inr ⟨rfl, by simp [hx]⟩, by simp [hx]⟩⟩]

/-- **Second link-clause component:** the decoded second block clause matches `linkClause2`. -/
theorem decodeClause_bvBlock2_mem {n : Nat} (x : Fin n → Bool) (k : Nat) (hk : k < n) (lit : Lit) :
    lit ∈ decodeClause (n + 1) (bvBlock2 x k) ↔
      lit ∈ linkClause2 k ((List.ofFn x).getD k false) := by
  have hget : (List.ofFn x).getD k false = x ⟨k, hk⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [hk]
  rw [mem_decodeClause, hget, linkClause2]
  rcases hxk : x ⟨k, hk⟩ <;>
  · simp only [bvBlock2, hget, hxk, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.false_or, Bool.or_false,
      Bool.true_beq, Bool.false_beq, beq_self_eq_true, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, if_true, if_false]
    constructor
    · rintro ⟨v, hv⟩
      aesop
    · rintro (rfl | rfl)
      · exact ⟨⟨k + 1, by omega⟩, by aesop⟩
      · exact ⟨⟨k, by omega⟩, by aesop⟩

/-! ## Assembly: `decodeCNF` of the parity bit-pattern is satisfiability-equivalent to `parityCNF` -/

/-- `List.all` congruence over list membership. -/
theorem all_congr_mem {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons]
    rw [h c (by simp), ih (fun a ha => h a (List.mem_cons_of_mem c ha))]

/-- **The general decoder of the parity bit-pattern has the same Boolean value as `parityCNF`** on every
assignment — proved clause-by-clause from the four component membership lemmas. -/
theorem decodeCNF_eval_eq {n : Nat} (x : Fin n → Bool) (a : RawAssignment) :
    CNF.eval (decodeCNF n (bvHead n) (bvBlock1 x) (bvBlock2 x) (bvTail n)) a
      = CNF.eval (parityCNF (List.ofFn x)) a := by
  have hhead : Clause.eval a (decodeClause (n + 1) (bvHead n)) = Clause.eval a (negClause 0) :=
    clause_eval_congr a _ _ (decodeClause_bvHead_mem n)
  have htail : Clause.eval a (decodeClause (n + 1) (bvTail n)) = Clause.eval a (negClause n) :=
    clause_eval_congr a _ _ (decodeClause_bvTail_mem n)
  have hmid : ((List.range n).flatMap (fun k =>
        [decodeClause (n + 1) (bvBlock1 x k), decodeClause (n + 1) (bvBlock2 x k)])).all
        (fun c => Clause.eval a c)
      = (chain (List.ofFn x) 0).all (fun c => Clause.eval a c) := by
    rw [chain_eq_flatMap, List.length_ofFn, List.all_flatMap, List.all_flatMap]
    apply all_congr_mem
    intro k hk_mem
    have hk : k < n := List.mem_range.mp hk_mem
    have h1 := clause_eval_congr a _ _ (decodeClause_bvBlock1_mem x k hk)
    have h2 := clause_eval_congr a _ _ (decodeClause_bvBlock2_mem x k hk)
    rw [linkClauses_eq, Nat.zero_add]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [h1, h2]
  simp only [decodeCNF, parityCNF, CNF.eval, List.length_ofFn, List.all_cons, List.all_append,
    List.all_nil, Bool.and_true]
  rw [hhead, htail, hmid]

/-- **Codec satisfiability equivalence.** -/
theorem decodeCNF_sat_iff {n : Nat} (x : Fin n → Bool) :
    Satisfiable (decodeCNF n (bvHead n) (bvBlock1 x) (bvBlock2 x) (bvTail n))
      ↔ Satisfiable (parityCNF (List.ofFn x)) := by
  have hvars : (decodeCNF n (bvHead n) (bvBlock1 x) (bvBlock2 x) (bvTail n)).vars
      = (parityCNF (List.ofFn x)).vars := by simp [decodeCNF, parityCNF]
  constructor
  · rintro ⟨a, hlen, heval⟩
    exact ⟨a, by rw [← hvars]; exact hlen, by rw [← decodeCNF_eval_eq]; exact heval⟩
  · rintro ⟨a, hlen, heval⟩
    exact ⟨a, by rw [hvars]; exact hlen, by rw [decodeCNF_eval_eq]; exact heval⟩

/-- **The general decoder realises the parity family: `Satisfiable (decode …) ↔ ⊕ x = 0`** (via brick 1). -/
theorem decodeCNF_sat_iff_even {n : Nat} (x : Fin n → Bool) :
    Satisfiable (decodeCNF n (bvHead n) (bvBlock1 x) (bvBlock2 x) (bvTail n))
      ↔ bxor (List.ofFn x) = false :=
  (decodeCNF_sat_iff x).trans (parityCNF_sat_iff_even (List.ofFn x))

end PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFCodec

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFCodec.chain_eq_flatMap
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFCodec.decodeClause_bvBlock2_mem
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFCodec.decodeCNF_eval_eq
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFCodec.decodeCNF_sat_iff_even
