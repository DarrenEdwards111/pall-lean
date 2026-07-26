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

/-- **The self-reference conjecture, un-fakeable.**  `Universality` is now fixed, so this cannot be
discharged by degenerate instantiation.  The `P ≠ NP` content is the genuine open implication. -/
def SelfReferenceForcesDoubling (cbudget : ℕ → ℕ) : Prop :=
  Universality → WhatIsLeft cbudget

/-- **Self-reference closes the wall, if it holds (proved reduction).**  *Given* a proof of
`Universality` (the Tseitin-correctness theorem) and of the conjecture, the separation follows.  Both
inputs are now real statements — no free `Prop`, no degenerate escape. -/
theorem selfref_closes (cbudget : ℕ → ℕ) (hbase : 1 ≤ cbudget 0)
    (huniv : Universality) (hconj : SelfReferenceForcesDoubling cbudget)
    (B : ℕ) (hbdd : ∀ d, cbudget d ≤ B) : False :=
  left_breaks_P cbudget (hconj huniv) hbase B hbdd

end PallLean.Paper93.DeepMath.PathB.CircuitUniversality

#print axioms PallLean.Paper93.DeepMath.PathB.CircuitUniversality.tseitin_witness
#print axioms PallLean.Paper93.DeepMath.PathB.CircuitUniversality.selfref_closes
