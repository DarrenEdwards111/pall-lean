import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.Pi

/-!
# `AC0pCircuit p` and the union-bound composition lemma

This is the first genuine step of the Razborov–Smolensky circuit-approximation repair (the semantic theorem that
`NFrameACCDepthDegree` is *not*).  It supplies two of the missing pieces:

* **`AC0pCircuit p`** — the `AC⁰[p]` circuit datatype whose MOD gates are **fixed to modulus `p`** (the `mod`
  constructor carries no modulus), so a polynomial that computes MOD_p is semantically correct at every MOD gate.
  This removes the "MOD clause ignores its modulus" gap.

* **the union-bound composition lemma** (`errCard_le_gateCount_mul`) — the structural core of "circuit error
  `≤ size · (per-gate error)".  For any approximator `A : AC0pCircuit p n → (Fin n → Bool) → Bool`, write
  `errCard A C` for the number of inputs where `A C` disagrees with `eval C`.  If the error obeys the per-gate
  bound `errCard A (gate children) ≤ Σ errCard A (child) + B` — i.e. a gate errs only where a child already errs
  (union of propagated errors) or on a local set of `≤ B` inputs — then

  ```text
    errCard A C  ≤  gateCount C · B.
  ```

  This is the union bound: total error `≤ (#gates) · (per-gate local error)`.  Fed a local error `B ≤ p^{-t}·2^n`
  (from the amplification, `NFrameFpAmplify.or_amplified_error_bound`), it yields circuit error
  `≤ size · p^{-t} · 2^n`.

## What this is and is not

This is the **composition** half.  It takes as input an approximator `A` and a per-gate error bound `B` (the
`ErrAdditive` hypothesis) and produces the circuit-wide bound.  It does **not** yet construct `A` (the correct
weighted AND/OR/MOD_p polynomial forms of `NFrameFpANDOR`/`NFrameFpDegree` with amplification seeds) nor
discharge the per-gate `B` (from `NFrameFpAmplify`).  Assembling those into `ErrAdditive A (p^{-t}·2^n)` is the
remaining repair; this file is the union bound that will consume it.

## Honest scope

The `AC⁰[p]` datatype plus the union-bound composition lemma.  It proves **no** circuit approximation on its own
(no approximator is supplied), **no** ACC⁰ lower bound, and it does not cross the composite-MOD wall.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameAC0pUnionBound

/-! ## The `AC⁰[p]` circuit datatype (MOD gates fixed to modulus `p`) -/

/-- An `AC⁰[p]` circuit over `n` inputs: unbounded fan-in AND/OR, NOT, and MOD gates whose modulus is **fixed to
`p`** (the `mod` constructor carries no modulus). -/
inductive AC0pCircuit (p n : Nat) where
  | input : Fin n → AC0pCircuit p n
  | const : Bool → AC0pCircuit p n
  | not : AC0pCircuit p n → AC0pCircuit p n
  | and : List (AC0pCircuit p n) → AC0pCircuit p n
  | or : List (AC0pCircuit p n) → AC0pCircuit p n
  | mod : List (AC0pCircuit p n) → AC0pCircuit p n

namespace AC0pCircuit

/-- Semantics.  A MOD gate fires iff the number of `true` children is `≡ 0 (mod p)`. -/
def eval {p n : Nat} (x : Fin n → Bool) : AC0pCircuit p n → Bool
  | .input i => x i
  | .const b => b
  | .not c => !(eval x c)
  | .and l => (l.map (eval x)).all id
  | .or l => (l.map (eval x)).any id
  | .mod l => decide (((l.map (eval x)).filter id).length % p = 0)

/-- Number of gates. -/
def gateCount {p n : Nat} : AC0pCircuit p n → Nat
  | .input _ => 1
  | .const _ => 1
  | .not c => gateCount c + 1
  | .and l => (l.map gateCount).sum + 1
  | .or l => (l.map gateCount).sum + 1
  | .mod l => (l.map gateCount).sum + 1

/-- Circuit depth. -/
def depth {p n : Nat} : AC0pCircuit p n → Nat
  | .input _ => 0
  | .const _ => 0
  | .not c => depth c + 1
  | .and l => (l.map depth).foldr max 0 + 1
  | .or l => (l.map depth).foldr max 0 + 1
  | .mod l => (l.map depth).foldr max 0 + 1

end AC0pCircuit

open AC0pCircuit

/-! ## The error count of an approximator -/

/-- The number of inputs on which the approximator `A` disagrees with the circuit at `C`. -/
def errCard {p n : Nat} (A : AC0pCircuit p n → (Fin n → Bool) → Bool) (C : AC0pCircuit p n) : Nat :=
  (Finset.univ.filter (fun x => A C x ≠ eval x C)).card

/-- **The per-gate additive error hypothesis** — the union-bound structure.  Each gate's error is contained in
the union of its children's errors plus a local error set of size `≤ B` (base gates have error `≤ B`). -/
def ErrAdditive {p n : Nat} (A : AC0pCircuit p n → (Fin n → Bool) → Bool) (B : Nat) : Prop :=
  (∀ i, errCard A (.input i) ≤ B) ∧
  (∀ b, errCard A (.const b) ≤ B) ∧
  (∀ c, errCard A (.not c) ≤ errCard A c + B) ∧
  (∀ l, errCard A (.and l) ≤ (l.map (errCard A)).sum + B) ∧
  (∀ l, errCard A (.or l) ≤ (l.map (errCard A)).sum + B) ∧
  (∀ l, errCard A (.mod l) ≤ (l.map (errCard A)).sum + B)

/-- A pointwise circuit-error bound lifts to a sum bound over a list of subcircuits. -/
theorem map_errCard_sum_le {p n : Nat} (A : AC0pCircuit p n → (Fin n → Bool) → Bool) (B : Nat)
    (l : List (AC0pCircuit p n)) (h : ∀ c ∈ l, errCard A c ≤ gateCount c * B) :
    (l.map (errCard A)).sum ≤ (l.map gateCount).sum * B := by
  induction l with
  | nil => simp
  | cons a t iht =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (by simp)
    have ht := iht (fun c hc => h c (by simp [hc]))
    calc errCard A a + (t.map (errCard A)).sum
        ≤ gateCount a * B + (t.map gateCount).sum * B := Nat.add_le_add ha ht
      _ = (gateCount a + (t.map gateCount).sum) * B := by ring

/-! ## The union-bound composition lemma -/

/-- **The union-bound composition lemma.**  If an approximator's error obeys the per-gate additive bound
(`ErrAdditive A B`), then the whole-circuit error is at most `gateCount C · B`: total error `≤` (number of gates)
times the per-gate local error. -/
theorem errCard_le_gateCount_mul {p n : Nat} (A : AC0pCircuit p n → (Fin n → Bool) → Bool) (B : Nat)
    (h : ErrAdditive A B) : ∀ C : AC0pCircuit p n, errCard A C ≤ gateCount C * B
  | .input i => by have := h.1 i; simp only [gateCount]; omega
  | .const b => by have := h.2.1 b; simp only [gateCount]; omega
  | .not c => by
      have ih := errCard_le_gateCount_mul A B h c
      have hg := h.2.2.1 c
      simp only [gateCount]
      calc errCard A (.not c) ≤ errCard A c + B := hg
        _ ≤ gateCount c * B + B := by omega
        _ = (gateCount c + 1) * B := by ring
  | .and l => by
      have ih : ∀ c ∈ l, errCard A c ≤ gateCount c * B := fun c _ => errCard_le_gateCount_mul A B h c
      have hsum := map_errCard_sum_le A B l ih
      simp only [gateCount]
      calc errCard A (.and l) ≤ (l.map (errCard A)).sum + B := h.2.2.2.1 l
        _ ≤ (l.map gateCount).sum * B + B := by omega
        _ = ((l.map gateCount).sum + 1) * B := by ring
  | .or l => by
      have ih : ∀ c ∈ l, errCard A c ≤ gateCount c * B := fun c _ => errCard_le_gateCount_mul A B h c
      have hsum := map_errCard_sum_le A B l ih
      simp only [gateCount]
      calc errCard A (.or l) ≤ (l.map (errCard A)).sum + B := h.2.2.2.2.1 l
        _ ≤ (l.map gateCount).sum * B + B := by omega
        _ = ((l.map gateCount).sum + 1) * B := by ring
  | .mod l => by
      have ih : ∀ c ∈ l, errCard A c ≤ gateCount c * B := fun c _ => errCard_le_gateCount_mul A B h c
      have hsum := map_errCard_sum_le A B l ih
      simp only [gateCount]
      calc errCard A (.mod l) ≤ (l.map (errCard A)).sum + B := h.2.2.2.2.2 l
        _ ≤ (l.map gateCount).sum * B + B := by omega
        _ = ((l.map gateCount).sum + 1) * B := by ring
  termination_by C => sizeOf C
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega | (rename_i hc; have := List.sizeOf_lt_of_mem hc; omega))

/-- **Restated as the RS union bound.**  With a per-gate error `B` and any circuit `C`, the approximator errs on
at most `gateCount C · B` inputs.  (Instantiating `B = ⌈p^{-t}·2^n⌉` from the amplification gives circuit error
`≤ size · p^{-t} · 2^n` — once an approximator `A` with `ErrAdditive A B` is supplied.) -/
theorem union_bound {p n : Nat} (A : AC0pCircuit p n → (Fin n → Bool) → Bool) (B : Nat)
    (h : ErrAdditive A B) (C : AC0pCircuit p n) :
    (Finset.univ.filter (fun x => A C x ≠ eval x C)).card ≤ gateCount C * B :=
  errCard_le_gateCount_mul A B h C

end PallLean.Paper93.DeepMath.PathB.NFrameAC0pUnionBound

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAC0pUnionBound.errCard_le_gateCount_mul
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAC0pUnionBound.union_bound
