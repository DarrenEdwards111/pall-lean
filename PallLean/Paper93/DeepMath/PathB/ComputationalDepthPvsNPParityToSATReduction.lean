import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMachineSemantics

/-!
# Parity (`MOD₂`) ≤ SAT — the reduction, brick 1 of the cross-model bridge

The cross-model bridge (uniform `MachineModel`/CNF-SAT ⟷ non-uniform `AC⁰[p]` capstones) needs a
**non-circular** reduction from an `AC⁰[p]`-hard function to SAT. The naive "compute the function, output
SAT/UNSAT" is circular (the reduction computes the function). The genuine reduction is the **parity counter
CNF**: auxiliary variables `p₀,…,pₙ`, local clauses forcing `p₀ = 0`, `p_{i+1} = pᵢ ⊕ xᵢ`, `pₙ = 0`. It is
`Satisfiable ⟺ (⊕ x = 0)`, and the map `x ↦ φₓ` is local (each `xᵢ` touches one clause block) — hence `AC⁰`.

This file builds the CNF and proves **both** directions of correctness, i.e. the genuine many-one reduction

```lean
parityCNF_sat_iff_even :  Satisfiable (parityCNF x)  ↔  ⊕ x = 0
```

`(⇐)` the forced prefix-parity assignment witnesses satisfiability; `(⇒)` any satisfying assignment is forced
to equal the prefix-parity assignment (`p₀ = 0`, each link forces `p_{i+1} = pᵢ ⊕ xᵢ`), so the final clause
`¬pₙ` forces `⊕ x = pₙ = 0`. The remaining bricks — the `AC⁰`-ness of `x ↦ φₓ`, `AC⁰[p]` closure under
`AC⁰` composition, and wiring `mod_q_not_ac0p` — are the rest of the bridge.

## Honest scope

Brick 1: the reduction CNF and its two-sided correctness `MOD₂ ≤ SAT`. `AC⁰`/counter level. Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`; it is one component of a from-scratch multi-file bridge toward an elementary
`SAT ∉ AC⁰[p]`. In particular this file proves nothing about the *complexity* of `x ↦ φₓ` — only that the
map is a correct reduction; the `AC⁰`-locality of the map (the load-bearing non-circular claim) is a later
brick, and the `AC⁰[p]`-closure step after it is `SAT ∉ AC⁰[p]`-strength, not proved here.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPParityToSAT

open SATDepthMachine

/-- Parity (XOR of all bits).  XOR is commutative-associative, so this fold-from-the-right computes the
same value as the running prefix parity used by the forced assignment. -/
def bxor (l : List Bool) : Bool := l.foldr (· ^^ ·) false

@[simp] theorem bxor_nil : bxor [] = false := rfl

@[simp] theorem bxor_cons (b : Bool) (l : List Bool) : bxor (b :: l) = (b ^^ bxor l) := rfl

/-- The custom `RawAssignment.lookup` is list `getElem?`. -/
theorem lookup_eq_getElem? (l : RawAssignment) (j : Nat) : l.lookup j = l[j]? := by
  induction l generalizing j with
  | nil => cases j <;> rfl
  | cons b rest ih =>
    cases j with
    | zero => rfl
    | succ j => simp [RawAssignment.lookup, ih]

/-- Clause forcing variable `j` to be false: `¬pⱼ`. -/
def negClause (j : Nat) : Clause := [{ var := j, pol := Polarity.neg }]

/-- The two clauses encoding `p_{i+1} = pᵢ ⊕ b`. -/
def linkClauses (i : Nat) (b : Bool) : List Clause :=
  if b then
    [ [{ var := i + 1, pol := Polarity.pos }, { var := i, pol := Polarity.pos }],
      [{ var := i + 1, pol := Polarity.neg }, { var := i, pol := Polarity.neg }] ]
  else
    [ [{ var := i + 1, pol := Polarity.pos }, { var := i, pol := Polarity.neg }],
      [{ var := i + 1, pol := Polarity.neg }, { var := i, pol := Polarity.pos }] ]

/-- The chain of link clauses for bits `rest`, starting at variable index `i`. -/
def chain : List Bool → Nat → List Clause
  | [], _ => []
  | b :: rest, i => linkClauses i b ++ chain rest (i + 1)

/-- The parity reduction CNF for input `x`. -/
def parityCNF (x : List Bool) : CNF :=
  { vars := x.length + 1,
    clauses := negClause 0 :: (chain x 0 ++ [negClause x.length]) }

/-- The forced (prefix-parity) assignment: `pᵢ = ⊕ (first i bits)`. -/
def forcedAssign (x : List Bool) : RawAssignment :=
  (List.range (x.length + 1)).map (fun i => bxor (x.take i))

theorem forcedAssign_length (x : List Bool) : (forcedAssign x).length = x.length + 1 := by
  simp [forcedAssign]

theorem forcedAssign_lookup (x : List Bool) (j : Nat) (h : j < x.length + 1) :
    (forcedAssign x).lookup j = some (bxor (x.take j)) := by
  rw [lookup_eq_getElem?, forcedAssign, List.getElem?_map, List.getElem?_range h]
  rfl

/-- A negated literal is true under `a` iff the variable is set to `false`. -/
theorem negLit_eval (a : RawAssignment) (j : Nat) (b : Bool) (h : a.lookup j = some b) :
    Lit.eval a { var := j, pol := Polarity.neg } = !b := by
  simp [Lit.eval, h]

/-- A positive literal is true under `a` iff the variable is set to `true`. -/
theorem posLit_eval (a : RawAssignment) (j : Nat) (b : Bool) (h : a.lookup j = some b) :
    Lit.eval a { var := j, pol := Polarity.pos } = b := by
  simp [Lit.eval, h]

/-- **Link clauses are satisfied when the assignment respects the XOR step.** -/
theorem linkClauses_eval (a : RawAssignment) (i : Nat) (b u : Bool)
    (hi : a.lookup i = some u) (hi1 : a.lookup (i + 1) = some (u ^^ b)) :
    (linkClauses i b).all (fun c => c.eval a) = true := by
  have hpi := posLit_eval a i u hi
  have hni := negLit_eval a i u hi
  have hpi1 := posLit_eval a (i + 1) (u ^^ b) hi1
  have hni1 := negLit_eval a (i + 1) (u ^^ b) hi1
  cases b <;> cases u <;>
    simp_all [linkClauses, Clause.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
      Bool.or_false]

/-- **The whole chain is satisfied by an assignment respecting the running prefix parity.** -/
theorem chain_eval (a : RawAssignment) :
    ∀ (rest : List Bool) (i : Nat) (s : Bool),
      (∀ k, k ≤ rest.length → a.lookup (i + k) = some (s ^^ bxor (rest.take k))) →
      (chain rest i).all (fun c => c.eval a) = true := by
  intro rest
  induction rest with
  | nil => intro i s _; simp [chain]
  | cons b rest ih =>
    intro i s hvals
    have h0 : a.lookup i = some s := by
      have := hvals 0 (by omega)
      simpa [bxor_nil, List.take_zero, Bool.xor_false] using this
    have h1 : a.lookup (i + 1) = some (s ^^ b) := by
      have hc := hvals 1 (Nat.le_add_left 1 rest.length)
      simpa using hc
    have hrestvals : ∀ k, k ≤ rest.length →
        a.lookup ((i + 1) + k) = some ((s ^^ b) ^^ bxor (rest.take k)) := by
      intro k hk
      have hval := hvals (k + 1) (by simpa using Nat.succ_le_succ hk)
      simp only [List.take_succ_cons, bxor_cons] at hval
      rw [show (i + 1) + k = i + (k + 1) by omega, Bool.xor_assoc]
      exact hval
    have hlink := linkClauses_eval a i b s h0 h1
    have hrest := ih (i + 1) (s ^^ b) hrestvals
    rw [chain, List.all_eq_true]
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact List.all_eq_true.mp hlink c hc
    · exact List.all_eq_true.mp hrest c hc

/-- **The forward reduction (proved): `⊕ x = 0 → Satisfiable φₓ`.**  The forced prefix-parity assignment
satisfies every clause of `parityCNF x` when `x` has even parity. -/
theorem parityCNF_sat_of_even (x : List Bool) (heven : bxor x = false) :
    Satisfiable (parityCNF x) := by
  refine ⟨forcedAssign x, ?_, ?_⟩
  · rw [forcedAssign_length, parityCNF]
  · have e0 : Clause.eval (forcedAssign x) (negClause 0) = true := by
      have h0 := forcedAssign_lookup x 0 (by omega)
      simp only [negClause, Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
      rw [negLit_eval _ 0 (bxor (x.take 0)) h0]; simp [bxor_nil, List.take_zero]
    have ec : (chain x 0).all (fun c => c.eval (forcedAssign x)) = true := by
      refine chain_eval (forcedAssign x) x 0 false ?_
      intro k hk
      have := forcedAssign_lookup x (0 + k) (by omega)
      simpa using this
    have en : Clause.eval (forcedAssign x) (negClause x.length) = true := by
      have hn := forcedAssign_lookup x x.length (by omega)
      rw [List.take_length] at hn
      simp only [negClause, Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
      rw [negLit_eval _ x.length (bxor x) hn]; simp [heven]
    rw [parityCNF, CNF.eval]
    refine List.all_eq_true.mpr ?_
    intro c hc
    rw [List.mem_cons, List.mem_append, List.mem_singleton] at hc
    rcases hc with rfl | hc | rfl
    · exact e0
    · exact List.all_eq_true.mp ec c hc
    · exact en

/-! ## The converse (soundness): `Satisfiable φₓ → ⊕ x = 0`

For `x ↦ φₓ` to be a genuine many-one reduction `MOD₂ ≤ SAT`, we also need the converse.  A satisfying
assignment is forced to be the prefix-parity assignment (`p₀ = 0` and each link forces `p_{i+1} = pᵢ ⊕ xᵢ`),
so the final clause `¬pₙ` forces `⊕ x = pₙ = 0`. -/

/-- A satisfied negated literal forces its variable to `false`. -/
theorem negLit_forces (a : RawAssignment) (j : Nat)
    (h : Lit.eval a { var := j, pol := Polarity.neg } = true) : a.lookup j = some false := by
  cases hl : a.lookup j with
  | none => simp [Lit.eval, hl] at h
  | some b =>
    cases b with
    | false => rfl
    | true => simp [Lit.eval, hl] at h

/-- A satisfied `¬pⱼ` clause forces `pⱼ = false`. -/
theorem negClause_forces (a : RawAssignment) (j : Nat)
    (h : (negClause j).eval a = true) : a.lookup j = some false := by
  simp only [negClause, Clause.eval, List.any_cons, List.any_nil, Bool.or_false] at h
  exact negLit_forces a j h

/-- Lookups are defined within range. -/
theorem lookup_isSome_of_lt (a : RawAssignment) (j : Nat) (h : j < a.length) :
    ∃ b, a.lookup j = some b := by
  rw [lookup_eq_getElem?]
  exact ⟨a[j], List.getElem?_eq_getElem h⟩

/-- **Converse of `linkClauses_eval`:** a satisfied link forces the XOR step. -/
theorem linkClauses_forces (a : RawAssignment) (i : Nat) (b u v : Bool)
    (hi : a.lookup i = some u) (hi1 : a.lookup (i + 1) = some v)
    (hsat : (linkClauses i b).all (fun c => c.eval a) = true) :
    v = (u ^^ b) := by
  have hpi := posLit_eval a i u hi
  have hni := negLit_eval a i u hi
  have hpi1 := posLit_eval a (i + 1) v hi1
  have hni1 := negLit_eval a (i + 1) v hi1
  cases b <;> cases u <;> cases v <;>
    simp_all [linkClauses, Clause.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
      Bool.or_false]

/-- **A satisfied chain forces the running prefix parity at every index.** -/
theorem chain_forces (a : RawAssignment) :
    ∀ (rest : List Bool) (i : Nat) (s : Bool),
      (chain rest i).all (fun c => c.eval a) = true →
      a.lookup i = some s →
      (∀ k, k ≤ rest.length → ∃ bk, a.lookup (i + k) = some bk) →
      ∀ k, k ≤ rest.length → a.lookup (i + k) = some (s ^^ bxor (rest.take k)) := by
  intro rest
  induction rest with
  | nil =>
    intro i s _ hi _ k hk
    have hk0 : k = 0 := Nat.le_zero.mp (by simpa using hk)
    subst hk0
    simpa using hi
  | cons b rest ih =>
    intro i s hsat hi htot
    rw [chain] at hsat
    have hall := List.all_eq_true.mp hsat
    have hsat1 : (linkClauses i b).all (fun c => c.eval a) = true :=
      List.all_eq_true.mpr (fun c hc => hall c (List.mem_append_left _ hc))
    have hsat2 : (chain rest (i + 1)).all (fun c => c.eval a) = true :=
      List.all_eq_true.mpr (fun c hc => hall c (List.mem_append_right _ hc))
    obtain ⟨v, hv⟩ := htot 1 (Nat.le_add_left 1 rest.length)
    have hstep : v = (s ^^ b) := linkClauses_forces a i b s v hi hv hsat1
    have hv' : a.lookup (i + 1) = some (s ^^ b) := by rw [← hstep]; exact hv
    have htot' : ∀ k, k ≤ rest.length → ∃ bk, a.lookup ((i + 1) + k) = some bk := by
      intro k hk
      have hk' := htot (k + 1) (by simpa using Nat.succ_le_succ hk)
      rwa [show (i + 1) + k = i + (k + 1) by omega]
    intro k hk
    cases k with
    | zero => simpa using hi
    | succ k' =>
      have hk' : k' ≤ rest.length := Nat.le_of_succ_le_succ hk
      have hih := ih (i + 1) (s ^^ b) hsat2 hv' htot' k' hk'
      rw [show i + (k' + 1) = (i + 1) + k' by omega, hih]
      congr 1
      rw [List.take_succ_cons, bxor_cons, Bool.xor_assoc]

/-- **The converse reduction (proved): `Satisfiable φₓ → ⊕ x = 0`.** -/
theorem parityCNF_even_of_sat (x : List Bool) (h : Satisfiable (parityCNF x)) :
    bxor x = false := by
  obtain ⟨a, hlen, heval⟩ := h
  simp only [parityCNF] at hlen
  simp only [parityCNF, CNF.eval] at heval
  have hall := List.all_eq_true.mp heval
  have hc0 : (negClause 0).eval a = true := hall (negClause 0) (by simp)
  have hchain : (chain x 0).all (fun c => c.eval a) = true :=
    List.all_eq_true.mpr (fun c hc => hall c (by
      simp only [List.mem_cons, List.mem_append, List.mem_singleton]
      exact Or.inr (Or.inl hc)))
  have hcn : (negClause x.length).eval a = true :=
    hall (negClause x.length) (by simp)
  have h0 : a.lookup 0 = some false := negClause_forces a 0 hc0
  have hn : a.lookup x.length = some false := negClause_forces a x.length hcn
  have htot : ∀ k, k ≤ x.length → ∃ bk, a.lookup (0 + k) = some bk := by
    intro k hk
    have hklt : k < a.length := by rw [hlen]; omega
    simpa using lookup_isSome_of_lt a k hklt
  have hforce := chain_forces a x 0 false hchain (by simpa using h0) htot x.length (Nat.le_refl _)
  rw [Nat.zero_add, List.take_length, hn] at hforce
  have := Option.some.inj hforce
  simpa [Bool.false_xor] using this.symm

/-- **Brick 1 complete: the reduction is correct in both directions.**
`MOD₂(x) = 0 ⟺ parityCNF x ∈ SAT`.  This is a genuine many-one reduction `MOD₂ ≤ SAT`. -/
theorem parityCNF_sat_iff_even (x : List Bool) :
    Satisfiable (parityCNF x) ↔ bxor x = false :=
  ⟨parityCNF_even_of_sat x, parityCNF_sat_of_even x⟩

end PallLean.Paper93.DeepMath.PathB.PvsNPParityToSAT

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParityToSAT.parityCNF_sat_of_even
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParityToSAT.parityCNF_even_of_sat
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParityToSAT.parityCNF_sat_iff_even
