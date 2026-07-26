import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWhatRemains

/-!
# Concretizing `Universal`: closing the free-Prop vacuity trap in the self-reference conjecture

An audit of `NonNaturalIdea` found a **vacuity trap** (the Route-W socket pattern): there,
`SelfReferenceForcesDoubling cbudget Universal := Universal → WhatIsLeft cbudget` takes `Universal` as
a **free `Prop`**, so it "fires" on degenerate instantiations — `Universal := WhatIsLeft cbudget`
gives `id`; `Universal := False` gives vacuity — producing a `P ≠ NP`-shaped theorem with nothing
inside, while `#print axioms` on the leaf stays clean.  The formalization did not *force* honesty on
whoever fills the hole.

This file closes the trap the right way: **replace the free `Prop` with a fixed, concrete statement
about the real circuit `output`** — a Tseitin encoding of `List (CGate n)` circuits into
`CookLevinReduction.Formula`.

## The encoding

`tseitin c : Formula` introduces one CNF variable per input (`i ↦ i`) and per wire
(`wire m ↦ n + m`), a forced-false variable (`n + |c|`) for out-of-range reads, gadget clauses pinning
each wire to its gate's value, and an output clause forcing the last wire true.  `CircuitEvalExpressible`
is the intended correctness: `Satisfiable (tseitin c) ↔ ∃ x, output c x = true` — "SAT expresses
circuit evaluation", the concrete self-reference fact.

* **`tseitin_witness`** — a non-degenerate witness: for the constant-true circuit the biconditional
  holds, both sides genuinely.  This rules out a vacuous encoding (the statement is not trivially true
  for the wrong reasons).
* **`Universality`** — the fixed statement `∀ n c, CircuitEvalExpressible c`.  It is a **concrete
  named proposition**, not a parameter: it cannot be instantiated degenerately.

## The un-fakeable conjecture

`SelfReferenceForcesDoubling cbudget := Universality → WhatIsLeft cbudget`.  Now `Universality` is
fixed, so the degenerate escapes are gone: you cannot pick it `:= WhatIsLeft` (it is a specific
statement about `output`) nor `:= False` (it is *true* — a correct encoding — witnessed non-vacuously).
`selfref_closes` proves that *given* a proof of `Universality` and a proof of the conjecture, the wall
falls — and both inputs are now real: `Universality` is the Tseitin-correctness theorem, and the
conjecture is the genuine open implication.

## Honest scope — the trap is closed; the correctness theorem is a fixed open obligation

This **closes the free-Prop vacuity** (the schema is now a statement) and proves the encoding is
non-degenerate (`tseitin_witness`).  It does **not** prove `Universality` — the full
`∀ c, Satisfiable (tseitin c) ↔ ∃ x, output c x = true` over arbitrary-op circuits is a real
several-hundred-line construction (the remaining arc), and it is *true* (a theorem of ZFC), not
hardness-strength.  The `P ≠ NP` content stays entirely in the open implication
`Universality → WhatIsLeft`, which is `cost_super`.  Nothing here is `P ≠ NP`, and nothing here can be
faked into looking like it.
-/

namespace PallLean.Paper93.DeepMath.PathB.CircuitUniversality

open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.WhatRemains

/-- The CNF variable a gate at position `m` reads for wire index `j`: the wire variable `n + j` if it
is an earlier wire (`j < m`), else the forced-false variable `n + L` (out-of-range reads are `false`,
matching `evalGate`). -/
def readVar (n L j m : ℕ) : ℕ := if j < m then n + j else n + L

/-- The gadget clauses pinning wire `m`'s variable (`n + m`) to gate `g`'s value. -/
def gateClauses (n L m : ℕ) : CGate n → Formula
  | .var i => [[(n + m, false), (i.val, true)], [(i.val, false), (n + m, true)]]
  | .cst b => [[(n + m, b)]]
  | .un op j =>
      let y := readVar n L j m
      [[(y, true), (n + m, op false)], [(y, false), (n + m, op true)]]
  | .bin op j k =>
      let y := readVar n L j m
      let z := readVar n L k m
      [[(y, true), (z, true), (n + m, op false false)],
       [(y, true), (z, false), (n + m, op false true)],
       [(y, false), (z, true), (n + m, op true false)],
       [(y, false), (z, false), (n + m, op true true)]]

/-- A default gate, so wire indexing can use `getD` without `Fin` proofs. -/
instance : Inhabited (CGate n) := ⟨CGate.cst false⟩

/-- The gadget clauses for a suffix of the circuit, threading the absolute wire index `m`. -/
def gadgets (n L : ℕ) : ℕ → List (CGate n) → Formula
  | _, [] => []
  | m, g :: gs => gateClauses n L m g ++ gadgets n L (m + 1) gs

/-- The Tseitin encoding of a circuit into CNF: gadget clauses per gate, a forced-false variable, and
the output clause forcing the last wire true. -/
def tseitin {n : ℕ} (c : List (CGate n)) : Formula :=
  gadgets n c.length 0 c
    ++ [[(n + c.length, false)], [(n + (c.length - 1), true)]]

/-! ### Wire semantics: the runtime values a circuit produces -/

/-- The wire values of a circuit on input `x`: the list of gate outputs. -/
def wvals (x : Fin n → Bool) (c : List (CGate n)) : List Bool := runFrom x [] c

theorem runFrom_length (x : Fin n → Bool) :
    ∀ (vals : List Bool) (c : List (CGate n)), (runFrom x vals c).length = vals.length + c.length := by
  intro vals c
  induction c generalizing vals with
  | nil => simp [runFrom]
  | cons g gs ih =>
      rw [runFrom, ih (vals ++ [evalGate x vals g])]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem wvals_length (x : Fin n → Bool) (c : List (CGate n)) : (wvals x c).length = c.length := by
  simp [wvals, runFrom_length]

/-- Appending a gate appends its evaluation over the current wires. -/
theorem wvals_snoc (x : Fin n → Bool) (c : List (CGate n)) (g : CGate n) :
    wvals x (c ++ [g]) = wvals x c ++ [evalGate x (wvals x c) g] := by
  simp only [wvals, runFrom_append]
  rfl

/-- `getD` at the end of a snoc is the appended element. -/
theorem getD_snoc {α : Type*} (l : List α) (e d : α) : (l ++ [e]).getD l.length d = e := by
  induction l with
  | nil => rfl
  | cons a as ih => simpa using ih

/-- **The wire recurrence.**  Wire `m` is `gate m` evaluated over the first `m` wires. -/
theorem wire_eq (x : Fin n → Bool) (c : List (CGate n)) (m : ℕ) (hm : m < c.length) :
    (wvals x c).getD m false = evalGate x (wvals x (c.take m)) (c.getD m default) := by
  induction c using List.reverseRecOn with
  | nil => simp at hm
  | append_singleton c g ih =>
      rw [wvals_snoc]
      rw [List.length_append, List.length_singleton] at hm
      rcases Nat.lt_or_ge m c.length with hlt | hge
      · rw [List.getD_append _ _ _ _ (by rw [wvals_length]; exact hlt)]
        rw [List.take_append_of_le_length (by omega)]
        rw [List.getD_append _ _ _ _ (by omega)]
        exact ih hlt
      · have hm' : m = c.length := by omega
        subst hm'
        rw [List.take_left, getD_snoc, ← wvals_length x c, getD_snoc]

/-- `getD` on a prefix agrees with the full list below the cut. -/
theorem getD_take_lt {α : Type*} : ∀ (l : List α) (m j : ℕ) (d : α), j < m →
    (l.take m).getD j d = l.getD j d := by
  intro l
  induction l with
  | nil => intro m j d _; simp
  | cons a as ih =>
      intro m j d h
      cases m with
      | zero => omega
      | succ m' =>
          cases j with
          | zero => simp
          | succ j' =>
              rw [List.take_succ_cons, List.getD_cons_succ, List.getD_cons_succ]
              exact ih m' j' d (by omega)

/-- `getD` past the end is the default. -/
theorem getD_eq_default {α : Type*} : ∀ (l : List α) (j : ℕ) (d : α), l.length ≤ j →
    l.getD j d = d := by
  intro l
  induction l with
  | nil => intro j d _; simp
  | cons a as ih =>
      intro j d h
      cases j with
      | zero => simp at h
      | succ j' => rw [List.getD_cons_succ]; exact ih j' d (by simp only [List.length_cons] at h; omega)

/-- `runFrom` only extends its wire list. -/
theorem runFrom_extends (x : Fin n → Bool) :
    ∀ (vals : List Bool) (c : List (CGate n)), ∃ suf, runFrom x vals c = vals ++ suf := by
  intro vals c
  induction c generalizing vals with
  | nil => exact ⟨[], by simp [runFrom]⟩
  | cons g gs ih =>
      obtain ⟨suf, hsuf⟩ := ih (vals ++ [evalGate x vals g])
      exact ⟨evalGate x vals g :: suf, by rw [runFrom, hsuf, List.append_assoc]; rfl⟩

/-- The first `m` wire values of the whole circuit are the wire values of its length-`m` prefix. -/
theorem wvals_take (x : Fin n → Bool) (c : List (CGate n)) (m : ℕ) (hm : m ≤ c.length) :
    (wvals x c).take m = wvals x (c.take m) := by
  obtain ⟨suf, hsuf⟩ := runFrom_extends x (runFrom x [] (c.take m)) (c.drop m)
  have hc : wvals x c = wvals x (c.take m) ++ suf := by
    have h2 := hsuf
    rw [← runFrom_append, List.take_append_drop] at h2
    exact h2
  rw [hc, List.take_append_of_le_length (by rw [wvals_length, List.length_take]; omega),
      List.take_of_length_le (by rw [wvals_length, List.length_take]; omega)]

/-! ### The canonical assignment -/

/-- The satisfying assignment built from a circuit input: inputs to `x`, wires to their values. -/
def canon (x : Fin n → Bool) (c : List (CGate n)) : ℕ → Bool :=
  fun v => if h : v < n then x ⟨v, h⟩ else (wvals x c).getD (v - n) false

theorem canon_input (x : Fin n → Bool) (c : List (CGate n)) (i : Fin n) :
    canon x c i.val = x i := by
  show (if h : (i.val) < n then x ⟨i.val, h⟩ else _) = x i
  rw [dif_pos i.isLt]

theorem canon_wire (x : Fin n → Bool) (c : List (CGate n)) (m : ℕ) :
    canon x c (n + m) = (wvals x c).getD m false := by
  show (if h : (n + m) < n then _ else (wvals x c).getD ((n + m) - n) false) = _
  rw [dif_neg (by omega)]
  congr 1
  omega

theorem canon_false (x : Fin n → Bool) (c : List (CGate n)) :
    canon x c (n + c.length) = false := by
  rw [canon_wire]
  exact getD_eq_default _ _ _ (le_of_eq (wvals_length x c))

/-- **Read matching.**  Under the canonical assignment, the CNF variable a gate reads carries exactly
the wire value `evalGate` reads. -/
theorem read_canon (x : Fin n → Bool) (c : List (CGate n)) (j m : ℕ) (hm : m ≤ c.length) :
    canon x c (readVar n c.length j m) = (wvals x (c.take m)).getD j false := by
  unfold readVar
  split
  · rename_i hj
    rw [canon_wire, ← wvals_take x c m hm, getD_take_lt (wvals x c) m j false hj]
  · rename_i hj
    rw [canon_false]
    symm
    exact getD_eq_default _ _ _ (by rw [wvals_length, List.length_take]; omega)

/-- The canonical assignment sends wire variable `m` to gate `m`'s value. -/
theorem canon_gate (x : Fin n → Bool) (c : List (CGate n)) (m : ℕ) (hm : m < c.length) :
    canon x c (n + m) = evalGate x (wvals x (c.take m)) (c.getD m default) := by
  rw [canon_wire, wire_eq x c m hm]

/-! ### Soundness: the canonical assignment satisfies the encoding -/

/-- **Each gate's gadget is satisfied by the canonical assignment.** -/
theorem gate_clauses_sound (x : Fin n → Bool) (c : List (CGate n)) (m : ℕ) (hm : m < c.length) :
    evalFormula (canon x c) (gateClauses n c.length m (c.getD m default)) = true := by
  have hmaster := canon_gate x c m hm
  cases hg : c.getD m default with
  | var i =>
      rw [hg] at hmaster
      simp only [evalGate] at hmaster
      simp only [hg, gateClauses, evalFormula, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]
      rw [hmaster, ← canon_input x c i]
      cases canon x c i.val <;> decide
  | cst b =>
      rw [hg] at hmaster
      simp only [evalGate] at hmaster
      simp only [hg, gateClauses, evalFormula, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]
      rw [hmaster]
      cases b <;> decide
  | un op j =>
      rw [hg] at hmaster
      simp only [evalGate] at hmaster
      rw [← read_canon x c j m (le_of_lt hm)] at hmaster
      simp only [hg, gateClauses, evalFormula, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]
      rw [hmaster]
      cases canon x c (readVar n c.length j m) <;> simp
  | bin op j k =>
      rw [hg] at hmaster
      simp only [evalGate] at hmaster
      rw [← read_canon x c j m (le_of_lt hm), ← read_canon x c k m (le_of_lt hm)] at hmaster
      simp only [hg, gateClauses, evalFormula, evalClause, evalLit, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]
      rw [hmaster]
      cases canon x c (readVar n c.length j m) <;>
        cases canon x c (readVar n c.length k m) <;> simp

/-- Every clause in `gadgets` comes from a gate's gadget. -/
theorem gadgets_mem (n L m₀ : ℕ) : ∀ (gs : List (CGate n)) (cl : Clause),
    cl ∈ gadgets n L m₀ gs →
    ∃ i, i < gs.length ∧ cl ∈ gateClauses n L (m₀ + i) (gs.getD i default) := by
  intro gs
  induction gs generalizing m₀ with
  | nil => intro cl h; simp [gadgets] at h
  | cons g gs ih =>
      intro cl h
      simp only [gadgets, List.mem_append] at h
      cases h with
      | inl h => exact ⟨0, by simp, by simpa using h⟩
      | inr h =>
          obtain ⟨i, hi, hmem⟩ := ih (m₀ + 1) cl h
          refine ⟨i + 1, by simpa using hi, ?_⟩
          rw [List.getD_cons_succ, show m₀ + (i + 1) = m₀ + 1 + i from by omega]
          exact hmem

/-- **The whole gadget block is satisfied by the canonical assignment.** -/
theorem gadgets_all_sound (x : Fin n → Bool) (c : List (CGate n)) :
    evalFormula (canon x c) (gadgets n c.length 0 c) = true := by
  rw [evalFormula, List.all_eq_true]
  intro cl hcl
  obtain ⟨i, hi, hmem⟩ := gadgets_mem n c.length 0 c cl hcl
  have hsound := gate_clauses_sound x c i hi
  rw [evalFormula, List.all_eq_true] at hsound
  simp only [Nat.zero_add] at hmem
  exact hsound cl hmem

/-- **Soundness.**  A circuit output on `x` yields a satisfying assignment `canon x c`. -/
theorem tseitin_sound (x : Fin n → Bool) (c : List (CGate n)) (hx : output c x = true) :
    Satisfiable (tseitin c) := by
  refine ⟨canon x c, ?_⟩
  rw [tseitin, evalFormula, List.all_append, Bool.and_eq_true]
  refine ⟨gadgets_all_sound x c, ?_⟩
  have hfv : evalClause (canon x c) [(n + c.length, false)] = true := by
    simp [evalClause, evalLit, canon_false]
  have hout : evalClause (canon x c) [(n + (c.length - 1), true)] = true := by
    have hval : canon x c (n + (c.length - 1)) = true := by rw [canon_wire]; exact hx
    simp [evalClause, evalLit, hval]
  simp [List.all_cons, List.all_nil, hfv, hout]

/-! ### Completeness: a satisfying assignment yields a circuit input -/

/-- Gate `m`'s gadget clauses all sit inside the gadget block. -/
theorem gadgets_contains (n L : ℕ) : ∀ (gs : List (CGate n)) (m₀ m : ℕ), m < gs.length →
    gateClauses n L (m₀ + m) (gs.getD m default) ⊆ gadgets n L m₀ gs := by
  intro gs
  induction gs with
  | nil => intro m₀ m hm; simp at hm
  | cons g gs ih =>
      intro m₀ m hm
      cases m with
      | zero =>
          simp only [Nat.add_zero, List.getD_cons_zero, gadgets]
          exact List.subset_append_left _ _
      | succ m' =>
          simp only [gadgets, List.getD_cons_succ]
          rw [show m₀ + (m' + 1) = (m₀ + 1) + m' from by omega]
          exact (ih (m₀ + 1) m' (by simpa using hm)).trans (List.subset_append_right _ _)

/-- Gate `m`'s gadget is satisfied by any assignment satisfying the whole gadget block. -/
theorem gate_clauses_sat_of_gadgets (a : ℕ → Bool) (c : List (CGate n)) (m : ℕ) (hm : m < c.length)
    (hg : evalFormula a (gadgets n c.length 0 c) = true) :
    evalFormula a (gateClauses n c.length m (c.getD m default)) = true := by
  rw [evalFormula, List.all_eq_true]
  intro cl hcl
  rw [evalFormula, List.all_eq_true] at hg
  apply hg
  have hsub := gadgets_contains n c.length c 0 m hm
  rw [Nat.zero_add] at hsub
  exact hsub hcl

/-- **Wire agreement.**  A satisfying assignment carries exactly the circuit's wire values. -/
theorem wire_agree (a : ℕ → Bool) (c : List (CGate n))
    (hg : evalFormula a (gadgets n c.length 0 c) = true) (hfv : a (n + c.length) = false) :
    ∀ m, m < c.length → a (n + m) = (wvals (fun i => a i.val) c).getD m false := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    set x : Fin n → Bool := fun i => a i.val with hxdef
    have hread : ∀ j, a (readVar n c.length j m) = (wvals x (c.take m)).getD j false := by
      intro j
      unfold readVar
      split
      · rename_i hj
        rw [ih j hj (by omega), ← wvals_take x c m (le_of_lt hm),
          getD_take_lt (wvals x c) m j false hj]
      · rename_i hj
        rw [hfv]
        symm
        exact getD_eq_default _ _ _ (by rw [wvals_length, List.length_take]; omega)
    have hgm : evalFormula a (gateClauses n c.length m (c.getD m default)) = true :=
      gate_clauses_sat_of_gadgets a c m hm hg
    rw [wire_eq x c m hm]
    cases hgd : c.getD m default with
    | var i =>
        rw [hgd] at hgm
        simp only [hgd, gateClauses, evalFormula, evalClause, evalLit, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, Bool.and_true, Bool.or_false, Bool.and_eq_true,
          Bool.or_eq_true, beq_iff_eq] at hgm
        simp only [evalGate]
        show a (n + m) = a i.val
        cases hp : a (n + m) <;> cases hq : a i.val <;> simp_all
    | cst b =>
        rw [hgd] at hgm
        simp only [hgd, gateClauses, evalFormula, evalClause, evalLit, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, Bool.and_true, Bool.or_false, beq_iff_eq] at hgm
        simpa only [evalGate] using hgm
    | un op j =>
        rw [hgd] at hgm
        simp only [hgd, gateClauses, evalFormula, evalClause, evalLit, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, Bool.and_true, Bool.or_false, Bool.and_eq_true,
          Bool.or_eq_true, beq_iff_eq] at hgm
        simp only [evalGate]
        rw [← hread j]
        cases hy : a (readVar n c.length j m) <;> simp_all
    | bin op j k =>
        rw [hgd] at hgm
        simp only [hgd, gateClauses, evalFormula, evalClause, evalLit, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, Bool.and_true, Bool.or_false, Bool.and_eq_true,
          Bool.or_eq_true, beq_iff_eq] at hgm
        simp only [evalGate]
        rw [← hread j, ← hread k]
        cases hy : a (readVar n c.length j m) <;>
          cases hz : a (readVar n c.length k m) <;> simp_all

/-- **Completeness.**  A satisfying assignment gives an input on which the circuit outputs `true`. -/
theorem tseitin_complete (c : List (CGate n)) (h : Satisfiable (tseitin c)) :
    ∃ x, output c x = true := by
  obtain ⟨a, ha⟩ := h
  rw [tseitin, evalFormula, List.all_append, Bool.and_eq_true] at ha
  obtain ⟨hgad, htail⟩ := ha
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at htail
  obtain ⟨hfvc, houtc⟩ := htail
  have hfv : a (n + c.length) = false := by
    simp only [evalClause, evalLit, List.any_cons, List.any_nil, Bool.or_false, beq_iff_eq] at hfvc
    exact hfvc
  have hout : a (n + (c.length - 1)) = true := by
    simp only [evalClause, evalLit, List.any_cons, List.any_nil, Bool.or_false, beq_iff_eq] at houtc
    exact houtc
  refine ⟨fun i => a i.val, ?_⟩
  by_cases hcl : c.length = 0
  · exfalso
    rw [hcl] at hfv hout
    simp only [Nat.add_zero, Nat.zero_sub, Nat.sub_zero] at hfv hout
    rw [hfv] at hout
    exact Bool.noConfusion hout
  · have hlt : c.length - 1 < c.length := by omega
    have hwa := wire_agree a c hgad hfv (c.length - 1) hlt
    show output c (fun i => a i.val) = true
    rw [show output c (fun i => a i.val)
        = (wvals (fun i => a i.val) c).getD (c.length - 1) false from rfl, ← hwa, hout]

/-- **Circuit evaluation is expressible as satisfiability** — the concrete self-reference fact:
`tseitin c` is satisfiable iff the circuit outputs `true` on some input. -/
def CircuitEvalExpressible {n : ℕ} (c : List (CGate n)) : Prop :=
  Satisfiable (tseitin c) ↔ ∃ x : Fin n → Bool, output c x = true

/-- **A non-degenerate witness (proved).**  For the constant-true circuit, the biconditional holds
with both sides genuinely true — the encoding computes, so `CircuitEvalExpressible` is not vacuous. -/
theorem tseitin_witness : CircuitEvalExpressible ([CGate.cst true] : List (CGate 1)) := by
  constructor
  · intro _
    exact ⟨fun _ => false, by decide⟩
  · intro _
    exact ⟨fun v => decide (v = 1), by decide⟩

/-- **The fixed universality statement** — the concretized `Universal`, no longer a free `Prop`:
circuit evaluation is expressible as satisfiability for *every* circuit.  This is a theorem of ZFC
(true), and its full proof is the remaining Tseitin-correctness arc. -/
def Universality : Prop := ∀ (n : ℕ) (c : List (CGate n)), CircuitEvalExpressible c

/-- **Universality is a THEOREM (proved).**  The full Tseitin correctness — circuit evaluation is
expressible as satisfiability, for every circuit — assembled from soundness and completeness.  The
concretized `Universal` is no longer just a fixed statement: it is now a machine-checked fact, so the
self-reference conjecture stands alone as the pure open implication. -/
theorem universality : Universality :=
  fun _ c => ⟨tseitin_complete c, fun ⟨x, hx⟩ => tseitin_sound x c hx⟩

/-- **The self-reference conjecture, un-fakeable.**  With `Universality` now a proved theorem, this is
the pure open implication — no free `Prop`, no degenerate escape.  The `P ≠ NP` content is entirely
here. -/
def SelfReferenceForcesDoubling (cbudget : ℕ → ℕ) : Prop :=
  Universality → WhatIsLeft cbudget

/-- **Self-reference closes the wall, if it holds (proved reduction).**  `Universality` is discharged
by `universality`; the conjecture is applied to it and the separation follows.  The only open input is
the conjecture itself. -/
theorem selfref_closes (cbudget : ℕ → ℕ) (hbase : 1 ≤ cbudget 0)
    (hconj : SelfReferenceForcesDoubling cbudget)
    (B : ℕ) (hbdd : ∀ d, cbudget d ≤ B) : False :=
  left_breaks_P cbudget (hconj universality) hbase B hbdd

end PallLean.Paper93.DeepMath.PathB.CircuitUniversality

#print axioms PallLean.Paper93.DeepMath.PathB.CircuitUniversality.universality
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitUniversality.tseitin_witness
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitUniversality.selfref_closes
