import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Config

/-!
# Entry 457 — universal-TM-table build: the config-region layout `homeConfigTape3` (proved)

The first concrete artifact of the `φ` layout for the universal-machine assembly: the **config region** of the tape — the
home marker followed by the encoded configuration (state field, current-symbol cache, simulated tape).  Its structural
invariants are *exactly* the preconditions every phase consumes (home marker at `0`, the state field of `q` ones at `1`,
its separator at `1+q`, the cache at `1+q+1`), so this pins the `home = 0`, `c = 1` instance the phases run on.

These follow directly from the prefix-parameterised `configEncode3_content` (entry 413) with the prefix `[M]`.

## What is proved (clean axioms, no `sorry`)

* **`homeConfigTape3 q sym rest`** — `Sym3.M :: configEncode3 q sym rest` (home marker then the encoded config).
* **`homeConfigTape3_content`** (PROVED) — the four structural invariants: `getD 0 = M`; `getD (1+i) = I` for `i < q`;
  `getD (1+q) = O`; `getD (1+q+1) = boolToSym3 sym`.

## Honest scope

This is the **config region** of the assembly layout `φ` — the home marker, state field, and cache, with the exact
invariants the phases assume.  It does **not** yet add the rule table or the simulated tape's head marker, nor define the
full `φ` / prove `EmitsEncodedStepEx3`.  Building the rest fragment by fragment is the genuine remaining construction —
large but obstruction-free (entry 456), **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HomeLayout

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config (configEncode3 configEncode3_content)

/-- **The config-region layout.**  Home marker, then the encoded configuration (`home = 0`, config key start `c = 1`). -/
def homeConfigTape3 (q : ℕ) (sym : Bool) (rest : List Sym3) : List Sym3 :=
  Sym3.M :: configEncode3 q sym rest

/-- **The config-region invariants (PROVED).**  Exactly the phase preconditions at `home = 0`, `c = 1`. -/
theorem homeConfigTape3_content (q : ℕ) (sym : Bool) (rest : List Sym3) :
    (homeConfigTape3 q sym rest).getD 0 Sym3.O = Sym3.M
    ∧ (∀ i, i < q → (homeConfigTape3 q sym rest).getD (1 + i) Sym3.O = Sym3.I)
    ∧ (homeConfigTape3 q sym rest).getD (1 + q) Sym3.O = Sym3.O
    ∧ (homeConfigTape3 q sym rest).getD (1 + q + 1) Sym3.O = boolToSym3 sym := by
  have h := configEncode3_content [Sym3.M] rest q sym
  exact ⟨rfl, fun i hi => h.1 i hi, h.2.1, h.2.2⟩

/-!
**The config-region layout, proved.**  `homeConfigTape3` realises the home marker + encoded configuration with the exact
invariants the phases consume.  Next: place the rule table and the simulated tape (with head marker) to complete `φ`, then
assemble `U` and prove `EmitsEncodedStepEx3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HomeLayout

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HomeLayout.homeConfigTape3_content
