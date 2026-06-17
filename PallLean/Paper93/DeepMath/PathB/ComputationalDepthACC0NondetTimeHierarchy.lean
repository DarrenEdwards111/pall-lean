import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0KarpLiptonCollapse

/-!
# NexpNeqNp / the nondeterministic time hierarchy — the diagonalization kernel (proved)

Entry 199 left **`NexpNeqNp`** (`NEXP ≠ NP`) as one of the three sub-sockets of the Karp–Lipton collapse chain.  Unlike
the other two (the BFL collapse, the derandomisation collapse), this one is classically **unconditional** — it is the
Cook / Seiferas–Fischer–Meyer nondeterministic time hierarchy theorem.  Its genuine heart is **Cantor diagonalization**
against an enumeration of the smaller class, which this file proves outright.

The kernel.  Fix an injective encoding `enc : ℕ → List Bool` of indices as inputs, and an enumeration `enum : ℕ → Lang`
of the smaller class.  The diagonal language `diag enum w := ∀ i, enc i = w → ¬ enum i w` differs from `enum i` at the
input `enc i` (`diag enum (enc i) ↔ ¬ enum i (enc i)`), so `diag enum ∉ range enum`.  Hence if the smaller class is
`range enum` and the diagonal lies in the larger class, the two classes differ.

## What is proved (clean axioms, no `sorry`)

* **`enc`** / **`enc_injective`** — an injective encoding `ℕ → List Bool` (`n ↦ replicate n true`, injective by length).
* **`diag`** / **`diag_eval`** — the diagonal language and its defining property `diag enum (enc i) ↔ ¬ enum i (enc i)`.
* **`diag_ne`** — the Cantor heart: `diag enum ≠ enum i` for every `i` (else `P ↔ ¬P` at `enc i`).
* **`diag_not_mem_range`** — `diag enum ∉ range enum`: the diagonal escapes the whole enumeration.
* **`nexpNeqNp_discharge`** — discharges the **entry-199 `NexpNeqNp` socket** from two model sockets: `NP` is
  machine-enumerable, and the diagonal lies in `NEXP`.

## Honest scope

This proves the **diagonalization kernel** of the nondeterministic time hierarchy — genuine, unconditional Cantor
diagonalization (`diag enum ∉ range enum`) — and the discharge of `NexpNeqNp` from it.  What remain named model sockets
are the two facts that make the kernel *apply to NTMs*: **`NPEnumerable`** (`NP` is the range of a machine enumeration —
the recursive enumeration of clocked poly-time nondeterministic machines) and **`DiagonalInNexp`** (the diagonal language
is decidable in `NEXP`).  The latter hides the genuinely NTM-specific subtlety: nondeterministic classes are not known to
be closed under complement, so the *real* hierarchy theorem uses Cook's **lazy diagonalization** (delaying the flip
across a range of inputs) rather than the direct complement `¬ enum i w` used here at the set level.  This file proves
the set-theoretic diagonalization core, not the lazy-diagonalization simulation.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NondetTimeHierarchy

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (CClass Lang)
open PallLean.Paper93.DeepMath.PathB.ACC0KarpLiptonCollapse (NexpNeqNp)

/-- **An injective encoding of indices as inputs.**  `enc n = replicate n true` (a list of `n` `true`s). -/
def enc (n : ℕ) : List Bool := List.replicate n true

/-- **The encoding is injective (PROVED).**  Distinct indices give distinct-length lists. -/
theorem enc_injective : Function.Injective enc := by
  intro a b h
  have : (enc a).length = (enc b).length := by rw [h]
  simpa [enc, List.length_replicate] using this

/-- **The diagonal language.**  `diag enum` accepts `w` iff every index `i` whose encoding is `w` has `enum i` *reject*
`w` — i.e. it flips machine `i` on its own encoding `enc i`. -/
def diag (enum : ℕ → Lang) : Lang := fun w => ∀ i, enc i = w → ¬ enum i w

/-- **The diagonal's defining property (PROVED).**  On the input `enc i`, `diag enum` is the negation of `enum i`:
`diag enum (enc i) ↔ ¬ enum i (enc i)` (the `∀` collapses to `i` by injectivity of `enc`). -/
theorem diag_eval (enum : ℕ → Lang) (i : ℕ) : diag enum (enc i) ↔ ¬ enum i (enc i) := by
  constructor
  · intro h; exact h i rfl
  · intro h j hj
    have : j = i := enc_injective hj
    rw [this]; exact h

/-- **The Cantor heart (PROVED).**  `diag enum` differs from every `enum i`: if they were equal, then at `enc i` we would
have `enum i (enc i) ↔ ¬ enum i (enc i)`, i.e. `P ↔ ¬P`, impossible. -/
theorem diag_ne (enum : ℕ → Lang) (i : ℕ) : diag enum ≠ enum i := by
  intro h
  have heq : diag enum (enc i) = enum i (enc i) := congrFun h (enc i)
  exact iff_not_self (heq ▸ diag_eval enum i)

/-- **The diagonal escapes the enumeration (PROVED).**  `diag enum ∉ range enum` — no machine in the enumeration decides
the diagonal language. -/
theorem diag_not_mem_range (enum : ℕ → Lang) : diag enum ∉ Set.range enum := by
  rintro ⟨i, hi⟩
  exact diag_ne enum i hi.symm

/-- **The NP-enumerability socket.**  `NP` is the range of a machine enumeration `enum : ℕ → Lang` — the recursive
enumeration of clocked polynomial-time nondeterministic machines.  Stated, not proved. -/
def NPEnumerable (NP : CClass) : Prop := ∃ enum : ℕ → Lang, NP = Set.range enum

/-- **The diagonal-in-`NEXP` socket.**  For any enumeration of `NP`, the diagonal language is decidable in `NEXP`.  This
hides the NTM-specific lazy-diagonalization simulation.  Stated, not proved. -/
def DiagonalInNexp (NEXP NP : CClass) : Prop :=
  ∀ enum : ℕ → Lang, NP = Set.range enum → diag enum ∈ NEXP

/-- **Discharging the entry-199 `NexpNeqNp` socket (PROVED).**  From `NP = range enum` (enumerability) and
`diag enum ∈ NEXP`, the diagonal witnesses `NEXP ≠ NP`: were `NEXP = NP = range enum`, the diagonal would lie in
`range enum`, contradicting `diag_not_mem_range`. -/
theorem nexpNeqNp_discharge (NEXP NP : CClass) (henum : NPEnumerable NP)
    (hdiag : DiagonalInNexp NEXP NP) : NexpNeqNp NEXP NP := by
  obtain ⟨enum, hNP⟩ := henum
  intro hEq
  have hin : diag enum ∈ NEXP := hdiag enum hNP
  rw [hEq, hNP] at hin
  exact diag_not_mem_range enum hin

end PallLean.Paper93.DeepMath.PathB.ACC0NondetTimeHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NondetTimeHierarchy.diag_ne
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NondetTimeHierarchy.diag_not_mem_range
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NondetTimeHierarchy.nexpNeqNp_discharge
