import Mathlib.Data.Nat.Basic

/-!
# The KW theorem bridge (`kw ≤ depth`): a formula *is* a communication protocol

`KRWOneStep` needed `kw ≤ depth` — the Karchmer–Wigderson theorem's `CC ≤ depth` direction.  This file
*builds* it for monotone formulas: a formula of depth `d` yields a KW communication protocol of cost `≤ d`
that **correctly** finds a coordinate where the 1-input and the 0-input differ.  The correctness is the
heart of the KW theorem.

The KW game for a monotone `f`: Alice holds `x` with `f(x)=1`, Bob holds `y` with `f(y)=0`; they must find
`i` with `xᵢ = 1`, `yᵢ = 0`.  The **descent** protocol walks the formula top-down — at an `∨` Alice steps
to a child that is `1` on `x`; at an `∧` Bob steps to a child that is `0` on `y` — and the leaf reached is
the answer.

## What is proved

* **`descent_correct`** — the protocol is **correct**: the coordinate it outputs has `x = true` and
  `y = false`.  This is the KW theorem's substance (the descent maintains the invariant "subformula is 1
  on x, 0 on y" and a leaf variable then differs).
* **`descentBits_le_depth`** — the protocol's cost is `≤ depth`: one bit per gate on the path.

Together: a monotone formula of depth `d` gives a correct KW protocol of cost `≤ d`, so the KW
communication complexity satisfies `kw(f) ≤ depth(f)`.  That is the bridge `KRWOneStep` assumes.

## Honest scope

Proved: the `CC ≤ depth` direction (formula → correct protocol, cost ≤ depth) for **monotone** formulas.
The full KW theorem (both directions, general formulas, `kwCC = depth ± 1`) is the repo's KRW / InfoTheory
package.  This is a real, self-contained build of the bridge's load-bearing half — the protocol
correctness — not a socket.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KWBridge

/-- A monotone formula over `n` variables: variables, `∧`, `∨` (no negations). -/
inductive MForm (n : ℕ) where
  | var : Fin n → MForm n
  | and : MForm n → MForm n → MForm n
  | or  : MForm n → MForm n → MForm n

/-- Formula semantics on an input. -/
def eval {n : ℕ} : MForm n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .and a b, x => eval a x && eval b x
  | .or a b, x => eval a x || eval b x

/-- Formula depth (leaves have depth 0). -/
def depth {n : ℕ} : MForm n → ℕ
  | .var _ => 0
  | .and a b => max (depth a) (depth b) + 1
  | .or a b => max (depth a) (depth b) + 1

/-- The **descent protocol**: at `∧`, step to a child false on `y`; at `∨`, step to a child true on `x`;
at a leaf, output the variable.  A total function making the KW moves. -/
def descent {n : ℕ} : MForm n → (Fin n → Bool) → (Fin n → Bool) → Fin n
  | .var i, _, _ => i
  | .and a b, x, y => if eval a y = false then descent a x y else descent b x y
  | .or a b, x, y => if eval a x = true then descent a x y else descent b x y

/-- Number of communication bits of the descent (one per gate on the path). -/
def descentBits {n : ℕ} : MForm n → (Fin n → Bool) → (Fin n → Bool) → ℕ
  | .var _, _, _ => 0
  | .and a b, x, y => (if eval a y = false then descentBits a x y else descentBits b x y) + 1
  | .or a b, x, y => (if eval a x = true then descentBits a x y else descentBits b x y) + 1

/-- **The protocol is correct (proved) — the heart of the KW theorem.**  If `f(x)=1` and `f(y)=0`, the
descent outputs a coordinate `i` with `xᵢ = true` and `yᵢ = false`. -/
theorem descent_correct {n : ℕ} :
    ∀ (F : MForm n) (x y : Fin n → Bool), eval F x = true → eval F y = false →
      x (descent F x y) = true ∧ y (descent F x y) = false := by
  intro F
  induction F with
  | var i => intro x y hx hy; exact ⟨hx, hy⟩
  | and a b iha ihb =>
    intro x y hx hy
    simp only [eval, Bool.and_eq_true] at hx
    simp only [eval] at hy
    by_cases h : eval a y = false
    · have hd : descent (MForm.and a b) x y = descent a x y := by simp only [descent, if_pos h]
      rw [hd]; exact iha x y hx.1 h
    · have h1 : eval a y = true := by
        cases hh : eval a y with
        | false => exact absurd hh h
        | true => rfl
      have h2 : eval b y = false := by rw [h1, Bool.true_and] at hy; exact hy
      have hd : descent (MForm.and a b) x y = descent b x y := by simp only [descent, if_neg h]
      rw [hd]; exact ihb x y hx.2 h2
  | or a b iha ihb =>
    intro x y hx hy
    simp only [eval] at hx
    simp only [eval, Bool.or_eq_false_iff] at hy
    by_cases h : eval a x = true
    · have hd : descent (MForm.or a b) x y = descent a x y := by simp only [descent, if_pos h]
      rw [hd]; exact iha x y h hy.1
    · have h1 : eval a x = false := by
        cases hh : eval a x with
        | false => rfl
        | true => exact absurd hh h
      have h2 : eval b x = true := by rw [h1, Bool.false_or] at hx; exact hx
      have hd : descent (MForm.or a b) x y = descent b x y := by simp only [descent, if_neg h]
      rw [hd]; exact ihb x y h2 hy.2

/-- **The protocol cost is `≤ depth` (proved).**  One bit per gate on the descent path. -/
theorem descentBits_le_depth {n : ℕ} :
    ∀ (F : MForm n) (x y : Fin n → Bool), descentBits F x y ≤ depth F := by
  intro F
  induction F with
  | var i => intro x y; simp [descentBits, depth]
  | and a b iha ihb =>
    intro x y
    simp only [descentBits, depth]
    by_cases h : eval a y = false
    · rw [if_pos h]; have := iha x y; have := le_max_left (depth a) (depth b); omega
    · rw [if_neg h]; have := ihb x y; have := le_max_right (depth a) (depth b); omega
  | or a b iha ihb =>
    intro x y
    simp only [descentBits, depth]
    by_cases h : eval a x = true
    · rw [if_pos h]; have := iha x y; have := le_max_left (depth a) (depth b); omega
    · rw [if_neg h]; have := ihb x y; have := le_max_right (depth a) (depth b); omega

end PallLean.Paper93.DeepMath.PathB.KWBridge

#print axioms PallLean.Paper93.DeepMath.PathB.KWBridge.descent_correct
#print axioms PallLean.Paper93.DeepMath.PathB.KWBridge.descentBits_le_depth
