import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DepthCompose

/-!
# Exact depth composition, and the irreducible exact-vs-quasipoly wall

The exact symmetric gates (`…ACC0SymmetricExact`: `AND`/`OR`/`MOD` are *exactly* count functions) compose **exactly**
— no approximation — at any depth: a top gate over `k` subcircuits is observed by the subcircuit-output vector, so SAT
searches `≤ 2^k` cells.  This `exact_depth_composes` is the exact side of the composition.

This file makes precise the **irreducible wall** that the whole YBT lane bottoms out at — a genuine tension, not a
missing lemma:

* **Exact** composition (this file, `…ACC0SymmetricExact`): boundary `= 2^k` — the *product* / subcircuit-output
  vector.  Exact, but **exponential** in the width.
* **Quasipolynomial** composition (`…ACC0AdditiveDegree` + `…ACC0ToAgreeDegree`): boundary `= ∑_{i≤D} C(n,i)`
  quasipoly, via the *additive* polynomial degree.  But only **approximate** (`toAgree` agrees `1-ε`).

Having **both at once** — an *exact* `SYM∘AND` of *quasipolynomial* size — is the Beigel–Tarui construction (an exact
integer polynomial of polylog degree, decoded by the symmetric top via CRT).  That is the irreducible structural
theorem, and it is the open wall: the exact gates give exponential boundary; the quasipoly degree needs approximation.

## What is proved (clean axioms, no `sorry`)

* `exact_depth_composes` — a top over `k` subcircuits (e.g. the exact symmetric gates) is SAT-searchable in `< 2^n`
  once `2^k < 2^n`, with the subcircuit-output statistic (boundary `2^k`).  Exact, any depth.

## Honest scope

This is the exact composition with the honest exponential (`2^k`) boundary — composes at any depth, no approximation.
The quasipoly boundary needs the additive-degree polynomial method, which is only *approximate*; the *exact*
quasipoly depth-composition is the irreducible YBT wall (and the separate Williams realization remains untouched per
the plan).  Still the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExactCompose

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0DepthCompose

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-- **Exact depth composition (proved): a top over `k` subcircuits is SAT-searchable in `< 2^n` once `2^k < 2^n`.**  No
approximation — the subcircuits may be the exact symmetric gates; the boundary is the subcircuit-output vector
(`2^k` cells). -/
theorem exact_depth_composes {k : ℕ} (sub : Fin k → (Fin n → Bool) → Bool)
    (top : (Fin k → Bool) → Bool) (hreg : 2 ^ k < 2 ^ n) :
    ∃ g : (Fin k → Bool) → Bool,
      (Satisfiable (fun x => top (fun i => sub i x)) ↔
          ∃ s ∈ Finset.univ.image (fun x => fun i => sub i x), g s = true)
        ∧ (Finset.univ.image (fun x => fun i => sub i x)).card < 2 ^ n := by
  have h := depth_compose_searchable (S := fun _ => Bool) sub sub
    (fun i => ⟨id, fun _ => rfl⟩) top
    (by simpa [Fintype.card_bool, Finset.prod_const] using hreg)
  convert h using 2
  congr!

end PallLean.Paper93.DeepMath.PathB.ACC0ExactCompose

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactCompose.exact_depth_composes
