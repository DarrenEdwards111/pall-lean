import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CarryRefinementCrossing

/-!
# Carry-state complexity — a field-free lower bound for the carry crossing (the new frontier)

The composite wall (`CarryRefinementCrossing`, entry 283) needs a **characteristic-independent** invariant — the field
methods stop because they commit to one characteristic.  This file builds the first such invariant: **carry-state
complexity**, a purely combinatorial (field-free) measure of how much state a sequential observer must carry.

**The model (field-free).**  A *carry observer* is a finite state set `Q` with an initial state `q₀` and an increment
map `δ : Q → Q` (reading one more `1`-bit advances the carry).  After reading an input of Hamming weight `w`, the carry
state is `δ^[w] q₀`.  An accept/output map reads off the answer.  No fields, no polynomials — just states and the
increment map.

**The lower bounds (proved).**

* *Modular.*  A carry observer computing `MOD_m` (accept iff weight `≡ 0 mod m`) needs `≥ m` states
  (`carry_observer_mod_card_ge`): the `m` residues are pairwise distinguishable — if residues `a < b` shared a state,
  appending `m - a` more `1`-bits would make `a` accept (weight `m`) but `b` reject (weight `≡ b - a ≢ 0`).  This is the
  Myhill–Nerode argument on the increment map, entirely field-free.
* *Count.*  A carry observer outputting the exact weight needs `≥ n + 1` states (`carry_observer_count_card_ge`): the
  carry state grows with the count range.

**For `MOD₆`** (`mod6_carry_state_ge_six`): `≥ 6` states.  *Honest caveat:* this bound is the **constant** `6`
(`= 2 · 3`, the CRT product) and is achievable — `MOD₆` is carry-cheap, which is exactly why `MOD₆ ∈ ACC⁰[6]`.  So
carry-state complexity for a *fixed* modulus does not by itself separate composite `ACC⁰`; it has teeth where the carry
**grows** — the exact count (`≥ n+1`), a growing modulus, or a function whose carry-state complexity grows with `n`.
Identifying such a function and proving the growth is the genuinely-open composite step.

## What is proved (clean axioms, no `sorry`)

* **`carry_observer_mod_card_ge`** (PROVED) — a carry observer computing `MOD_m` has `≥ m` states (Myhill–Nerode via
  `Function.iterate_add_apply` + the residue-distinguishing continuation).
* **`carry_observer_count_card_ge`** (PROVED) — a carry observer outputting the exact weight on `n` bits has `≥ n + 1`
  states: carry state grows with the count range.
* **`mod6_carry_state_ge_six`** (PROVED) — `≥ 6` carry states for `MOD₆`.
* **`mod_observer_too_small_fails`** (PROVED) — the trivial bounded case: `< m` states ⇒ cannot compute `MOD_m`.

## Honest scope — a real field-free bound, and where it stops

The carry-state lower bound `≥ m` (and `≥ n+1` for the count) is a genuine, field-free, machine-proved invariant —
exactly the kind the composite wall needs.  But for a *fixed* modulus it is constant (`6` for `MOD₆`) and achievable, so
it does **not** prove `MOD₆ ∉ ACC⁰[6]` (false — `MOD₆ ∈ ACC⁰[6]`); the separation requires a target whose carry-state
complexity *grows* under bounded-observer composition, which is the open `CarryRefinementCrossing` step (entry 283).
This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CarryStateComplexity

/-- **Carry-state lower bound for `MOD_m` (PROVED).**  A carry observer — state set `Q`, initial `q₀`, increment
`δ : Q → Q` (one more `1`-bit), accept `acc` — that computes `MOD_m` (`acc (δ^[w] q₀) = [w ≡ 0 mod m]` for all weights
`w`) must have `≥ m` states.  The `m` residues are pairwise distinguishable: if `a < b < m` shared a state, the
continuation of `m - a` more `1`-bits would accept `a` (total weight `m`) but reject `b` (total `≡ b - a ≢ 0`).  A
field-free Myhill–Nerode bound. -/
theorem carry_observer_mod_card_ge {Q : Type} [Fintype Q] (q₀ : Q) (δ : Q → Q) (acc : Q → Bool)
    (m : ℕ) (hcomp : ∀ w : ℕ, acc (δ^[w] q₀) = decide (w % m = 0)) :
    m ≤ Fintype.card Q := by
  have aux : ∀ a b : ℕ, a < b → b < m → δ^[a] q₀ = δ^[b] q₀ → False := by
    intro a b hab hbm heq
    have e1 : δ^[(m - a) + a] q₀ = δ^[m - a] (δ^[a] q₀) := Function.iterate_add_apply δ (m - a) a q₀
    have e2 : δ^[(m - a) + b] q₀ = δ^[m - a] (δ^[b] q₀) := Function.iterate_add_apply δ (m - a) b q₀
    have estate : δ^[(m - a) + a] q₀ = δ^[(m - a) + b] q₀ := by rw [e1, e2, heq]
    have hi := hcomp ((m - a) + a)
    have hj := hcomp ((m - a) + b)
    rw [estate, hj] at hi
    have hm1 : ((m - a) + a) % m = 0 := by
      have h1 : (m - a) + a = m := by omega
      rw [h1, Nat.mod_self]
    have hm2 : ((m - a) + b) % m = b - a := by
      have h2 : (m - a) + b = m + (b - a) := by omega
      rw [h2, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hm1, hm2] at hi
    rw [decide_eq_decide] at hi
    have hba : b - a = 0 := hi.mpr rfl
    omega
  have hinj : Function.Injective (fun i : Fin m => δ^[i.val] q₀) := by
    intro i j hij
    by_contra hne
    have hvne : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_ge i.val j.val with h | h
    · exact aux i.val j.val h j.isLt hij
    · exact aux j.val i.val (by omega) i.isLt hij.symm
  calc m = Fintype.card (Fin m) := (Fintype.card_fin m).symm
    _ ≤ Fintype.card Q := Fintype.card_le_of_injective _ hinj

/-- **Carry-state lower bound for the exact count (PROVED).**  A carry observer that outputs the exact Hamming weight on
inputs of weight `≤ n` (`out (δ^[w] q₀) = w`) must have `≥ n + 1` states: distinct weights give distinct outputs, so
distinct states.  The carry state *grows* with the count range — the regime where carry-state complexity has teeth. -/
theorem carry_observer_count_card_ge {Q : Type} [Fintype Q] (q₀ : Q) (δ : Q → Q) (out : Q → ℕ)
    (n : ℕ) (hcomp : ∀ w : ℕ, w ≤ n → out (δ^[w] q₀) = w) :
    n + 1 ≤ Fintype.card Q := by
  have hinj : Function.Injective (fun i : Fin (n + 1) => δ^[i.val] q₀) := by
    intro i j hij
    have hval : out (δ^[i.val] q₀) = out (δ^[j.val] q₀) := congrArg out hij
    rw [hcomp i.val (by omega), hcomp j.val (by omega)] at hval
    exact Fin.ext hval
  calc n + 1 = Fintype.card (Fin (n + 1)) := (Fintype.card_fin (n + 1)).symm
    _ ≤ Fintype.card Q := Fintype.card_le_of_injective _ hinj

/-- **`MOD₆` needs `≥ 6` carry states (PROVED).**  Instantiating `carry_observer_mod_card_ge` at `m = 6`.  (Caveat: `6`
is constant and achievable — `MOD₆ ∈ ACC⁰[6]` — so this is a real field-free bound but not a composite separation; the
separation needs a *growing* carry.) -/
theorem mod6_carry_state_ge_six {Q : Type} [Fintype Q] (q₀ : Q) (δ : Q → Q) (acc : Q → Bool)
    (hcomp : ∀ w : ℕ, acc (δ^[w] q₀) = decide (w % 6 = 0)) :
    6 ≤ Fintype.card Q :=
  carry_observer_mod_card_ge q₀ δ acc 6 hcomp

/-- **The trivial bounded case fails (PROVED).**  A carry observer with fewer than `m` states cannot compute `MOD_m`
(contrapositive of `carry_observer_mod_card_ge`). -/
theorem mod_observer_too_small_fails {Q : Type} [Fintype Q] (q₀ : Q) (δ : Q → Q) (acc : Q → Bool)
    (m : ℕ) (hsmall : Fintype.card Q < m) :
    ¬ (∀ w : ℕ, acc (δ^[w] q₀) = decide (w % m = 0)) :=
  fun hcomp => absurd (carry_observer_mod_card_ge q₀ δ acc m hcomp) (by omega)

/-!
**The field-free frontier.**  Carry-state complexity is a genuine, field-free, machine-proved invariant: computing
`MOD_m` needs `≥ m` carry states (`carry_observer_mod_card_ge`), and the exact count needs `≥ n + 1` (growing,
`carry_observer_count_card_ge`).  It is exactly the *characteristic-independent* kind of measure the composite wall
(`CarryRefinementCrossing`, entry 283) calls for.  Honestly, for a *fixed* modulus the bound is constant (`6` for
`MOD₆`) and achievable — `MOD₆ ∈ ACC⁰[6]` — so it is not itself a composite separation; the separation requires a target
whose carry-state complexity *grows* under bounded-observer composition.  Locating such a target and proving the growth
is the open composite step.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CarryStateComplexity

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryStateComplexity.carry_observer_mod_card_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryStateComplexity.carry_observer_count_card_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryStateComplexity.mod6_carry_state_ge_six
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryStateComplexity.mod_observer_too_small_fails
