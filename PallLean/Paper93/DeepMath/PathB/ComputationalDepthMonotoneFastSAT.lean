import Mathlib.Tactic

/-!
# The next fast-SAT rung: monotone-SAT decided by a SINGLE evaluation

The fast-SAT ladder so far: juntas (search `2^d`), DNF (poly consistency scan).  This rung is **monotone**
functions, and it is the cleanest yet — SAT needs *no search at all*, just one evaluation at the
all-true input.  A monotone `f` satisfies `f x ≤ f ⊤` for every `x`, so `f` is satisfiable iff `f ⊤ =
true`.  One evaluation beats `2^n`.

Built through the Mikoshi pipeline: the speedup (`1 < 2^n`) was gated by mikoshilang/SymPy first; the
structural correctness (below) is proved here in Lean.

## What is proved

* **`monotone_sat_iff_top`** — for monotone `f : (Fin n → Bool) → Bool`,
  `(∃ x, f x = true) ↔ f (fun _ => true) = true`.  Forward: any satisfying `x` is `≤ ⊤`, so
  `true = f x ≤ f ⊤`.  Backward: `⊤` is itself an input.
* **`monotone_beats_brute`** — the speedup: one evaluation vs the `2^n` brute-force search (`1 < 2^n`
  for `0 < n`).

## Honest scope

A complete, real fast-SAT — for **monotone** functions (a genuine restricted class).  It fills the
`Attack.decides` socket for this class with a single evaluation.  Pushing "decide by structure" to a
class *past ACC⁰* (e.g. general TC⁰-SAT, which curiosity flagged) is the open direction — the wall.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MonotoneFastSAT

variable {n : ℕ}

/-- **Monotone-SAT is one evaluation (proved).**  A monotone Boolean function is satisfiable iff it is
`true` at the all-true input — no search over the `2^n` assignments. -/
theorem monotone_sat_iff_top (f : (Fin n → Bool) → Bool) (hf : Monotone f) :
    (∃ x, f x = true) ↔ f (fun _ => true) = true := by
  constructor
  · rintro ⟨x, hx⟩
    have hle : x ≤ (fun _ => true) := fun i => Bool.le_true (x i)
    have hmono : f x ≤ f (fun _ => true) := hf hle
    rw [hx] at hmono
    exact le_antisymm (Bool.le_true _) hmono
  · intro h
    exact ⟨fun _ => true, h⟩

/-- **The speedup (proved).**  Monotone-SAT is one evaluation; brute force is `2^n`.  For `0 < n`,
`1 < 2^n` — the single check strictly beats the search. -/
theorem monotone_beats_brute (hn : 0 < n) : 1 < 2 ^ n := by
  calc 1 < 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

end PallLean.Paper93.DeepMath.PathB.MonotoneFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneFastSAT.monotone_sat_iff_top
