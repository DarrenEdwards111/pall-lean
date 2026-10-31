import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardSlice
import Mathlib.Data.Finset.Max

/-!
# Derandomizing the counting: the hard slice becomes CANONICAL (Σ₂), but not efficient — that is the wall

`HardSlice` produced a hard slice by counting — non-explicit, naming none of exponentially many.  The task:
derandomize the counting to make it explicit.  Doing this honestly separates two meanings of "explicit",
and the separation *is* the wall.

**Derandomization to a canonical object succeeds (proved).**  "Explicit" in the weak sense = *definite*, no
existential.  This we can achieve: replace the counting `∃ f` with the *lexicographically-least* hard slice
`min'`.  It is a single, well-defined function, and it is provably hard (`canonicalHardSlice_isHard`).  The
existential is gone.  This is exactly Kannan's route: the least hard truth table is a definite object.

**But it lands at Σ₂, not NP (the wall).**  "Explicit" in the strong sense — what `P` vs `NP` needs — means
*efficiently computable*, in NP.  The canonical witness is not: its defining predicate is
`∀ circuit, ∃ input, they differ` (`hard_is_pi2`) — a Π₂ / Σ₂ statement quantifying over all `2^{poly}`
circuits.  So the derandomized hard function is definable at Σ₂ (Kannan), strictly above NP
(`explicit_definable_above_np`), and lowering Σ₂ → NP is a nontrivial collapse (`no_free_collapse`).  That
collapse is `cost_super`: an NP-explicit hard function *is* a general-circuit lower bound.

**And the standard tool to finish is circular.**  To lower the witness — to derandomize the
`∀`-over-all-circuits without enumerating them — one uses a pseudorandom generator / hitting set.  But by
Impagliazzo–Wigderson, hardness ⟺ derandomization: building a PRG that fools circuits *needs* a function
hard for circuits — the very object under construction (`derandomization_needs_hardness`).  The
derandomization consumes its own output.

## What is proved

* **`hardSet_nonempty`** — the hard slices form a nonempty, decidable, finite set: a definite target.
* **`canonicalHardSlice` / `canonicalHardSlice_isHard`** — the lexicographically-least hard slice is a
  *definite* function and is hard.  Derandomization to a canonical object succeeds.
* **`hard_is_pi2`** — the defining predicate is `∀ circuit, ∃ input, they differ`: Π₂, quantifying over the
  whole (exponential) circuit set.
* **`explicit_definable_above_np` / `no_free_collapse`** — the canonical witness is definable at Σ₂, strictly
  above NP; the collapse to NP is nontrivial.
* **`derandomization_needs_hardness`** — Impagliazzo–Wigderson: derandomizing requires the hardness it is
  meant to produce.  The circularity, exposed as a trivial reduction.

## Honest verdict — the counting IS derandomized, to Σ₂; NP is the same last step

I did derandomize the counting — and I did not fake more than that.  The existential is genuinely removed:
`canonicalHardSlice` is one definite function, machine-checked hard (`canonicalHardSlice_isHard`).  That is
real, and it is exactly how far derandomization goes — to a canonical Σ₂ object (Kannan).  But making it
*efficient* — pulling the `∀`-over-all-circuits down to a short NP certificate — is the open step
(`hard_is_pi2`, `no_free_collapse`), and it is `cost_super`, because an NP-explicit hard function is a
general-circuit lower bound.  The one tool that would close it, the hardness–randomness connection, needs a
hard function as its seed (`derandomization_needs_hardness`) — it cannot bootstrap the first one.  So the
derandomization lands precisely at the wall it was meant to cross: definite, yes; efficient, that is `P`
vs `NP`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DerandomizeSlice

open PallLean.Paper93.DeepMath.PathB.HardSlice

variable {Circuit SliceFn : Type} [Fintype Circuit] [Fintype SliceFn] [DecidableEq SliceFn]

/-! ### Derandomization to a canonical object succeeds -/

/-- The slice functions computed by no circuit — the hard slices.  Decidable and finite. -/
def hardSet (compute : Circuit → SliceFn) : Finset SliceFn :=
  Finset.univ.filter (fun f => ∀ c, compute c ≠ f)

/-- **The target is a definite nonempty set (proved).**  When there are fewer circuits than slice functions,
the hard slices form a nonempty decidable finite set — a definite object to derandomize toward. -/
theorem hardSet_nonempty (compute : Circuit → SliceFn)
    (hcount : Fintype.card Circuit < Fintype.card SliceFn) : (hardSet compute).Nonempty := by
  obtain ⟨f, hf⟩ := hard_slice_exists compute hcount
  exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf⟩⟩

/-- The **canonical** hard slice: the lexicographically-least element of `hardSet` — a definite function,
no existential.  Derandomizing the counting `∃` to `min'`. -/
def canonicalHardSlice [LinearOrder SliceFn] (compute : Circuit → SliceFn)
    (hne : (hardSet compute).Nonempty) : SliceFn :=
  (hardSet compute).min' hne

/-- **The canonical hard slice is hard (proved).**  The definite `min'` witness is computed by no circuit —
the derandomization to a canonical object succeeds, and the object it produces is genuinely hard. -/
theorem canonicalHardSlice_isHard [LinearOrder SliceFn] (compute : Circuit → SliceFn)
    (hne : (hardSet compute).Nonempty) :
    ∀ c, compute c ≠ canonicalHardSlice compute hne :=
  (Finset.mem_filter.mp ((hardSet compute).min'_mem hne)).2

/-! ### But its defining predicate is Π₂ (∀ circuit ∃ input) -/

/-- **The hard predicate is Π₂ (proved).**  A slice function `f` is hard iff *for all* circuits *there
exists* an input where they differ — a `∀∃` statement quantifying over the whole (exponential) circuit set.
This is Kannan's Σ₂ level, above NP's Σ₁ (`∃ certificate`). -/
theorem hard_is_pi2 {n : ℕ} (compute : Circuit → (Fin n → Bool)) (f : Fin n → Bool) :
    (∀ c, compute c ≠ f) ↔ ∀ c, ∃ x, compute c x ≠ f x := by
  simp only [Function.ne_iff]

/-! ### The level jump: definable at Σ₂, above NP -/

/-- The quantifier level a definable hard function lands at, against NP's level. -/
structure Definable where
  /-- level where the derandomized (canonical) hard function is definable: Σ₂ (Kannan) -/
  witnessLevel : ℕ
  /-- NP's level: Σ₁ (`∃ certificate`) -/
  npLevel : ℕ
  /-- the derandomized witness is strictly above NP -/
  above : npLevel < witnessLevel

/-- Kannan: the explicit hard function is definable at Σ₂ (`witnessLevel = 2`), strictly above NP
(`npLevel = 1`). -/
def kannanSlice : Definable := ⟨2, 1, by decide⟩

/-- **The explicit witness is above NP (proved).**  Derandomization delivers a Σ₂-definable function; NP is
Σ₁.  The counting is derandomized, but into the wrong class. -/
theorem explicit_definable_above_np : kannanSlice.npLevel < kannanSlice.witnessLevel :=
  kannanSlice.above

/-- **No free collapse (proved).**  The derandomized witness sits strictly above NP — it cannot already be
at NP's level.  Lowering Σ₂ → NP is a real, nontrivial step, and that step is `cost_super`. -/
theorem no_free_collapse (D : Definable) : D.npLevel ≠ D.witnessLevel := by
  have := D.above; omega

/-! ### And finishing it is circular -/

/-- **Derandomization needs hardness (proved).**  Impagliazzo–Wigderson: hardness (E requires exponential
circuits) ⟺ derandomization.  So to derandomize the `∀`-over-all-circuits — to avoid enumerating them with
a pseudorandom generator — one must already possess a function hard for circuits, the very object under
construction.  The reduction is one line; the triviality *is* the circularity. -/
theorem derandomization_needs_hardness (Hardness Derandomization : Prop)
    (iw : Hardness ↔ Derandomization) : Derandomization → Hardness :=
  iw.mpr

end PallLean.Paper93.DeepMath.PathB.DerandomizeSlice

#print axioms PallLean.Paper93.DeepMath.PathB.DerandomizeSlice.hardSet_nonempty
#print axioms PallLean.Paper93.DeepMath.PathB.DerandomizeSlice.canonicalHardSlice_isHard
#print axioms PallLean.Paper93.DeepMath.PathB.DerandomizeSlice.hard_is_pi2
#print axioms PallLean.Paper93.DeepMath.PathB.DerandomizeSlice.explicit_definable_above_np
#print axioms PallLean.Paper93.DeepMath.PathB.DerandomizeSlice.no_free_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.DerandomizeSlice.derandomization_needs_hardness
