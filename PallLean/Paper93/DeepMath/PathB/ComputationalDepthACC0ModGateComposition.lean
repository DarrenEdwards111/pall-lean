import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndComposition

/-!
# The MOD case of shared-layer SYM∘AND composition (PROVED)

Completing the `HasSymAndRep` composition closure.  `ACC0SymAndComposition` proves the shared-layer
closure for `NOT`, `AND`, `OR` (and the cross-layer binary / CRT cases); the **`MOD` gate** was the
missing case.  Here it is:

  `hasSymAndRep_modGate_sharedLayer` — a `MOD_m` gate (any modulus `m`, residue `r`) over `k`
  subcircuits that all read the **same** bottom `AND`-layer is again `SYM∘AND` over that layer —
  **exact, no blow-up**.

Reason: each subcircuit `g i x = sym i (satCount supp x)` is a function of the single shared count
`s = satCount supp x`, so the `MOD` gate's count `∑_i (g i x).toNat = ∑_i (sym i s).toNat` is itself a
function of `s`; the gate output `(∑_i (sym i s).toNat) % m = r` is therefore symmetric in the shared
layer.  Combined with the existing `NOT`/`AND`/`OR` shared-layer closures, this gives full
`MOD/AND/OR/NOT` closure for the **shared-bottom-layer** ACC⁰ fragment.

## What is proved (clean axioms, no `sorry`)

* `hasSymAndRep_modGate_sharedLayer` — `MOD_m` of shared-layer SYM∘AND subcircuits is SYM∘AND.
* `hasSymAndRep_modGate_of_reps` — same, packaged from per-subcircuit `HasSymAndRep` hypotheses sharing
  a layer.

## Honest scope — where the wall is

This is the **shared-layer** (single bottom count) case: exact and with no size blow-up.  Real ACC⁰
gates read **different** bottom layers; composing those raises the count dimension (`HasBinarySymRep`,
one extra count per layer) and, iterated to constant depth with *distinct* layers, hits the
exact-vs-quasipoly tension proved in `ACC0ExactCompose` (exact ⇒ `2^k` boundary; quasipoly ⇒ only
approximate).  The simultaneous *exact* `SYM∘AND` of *quasipolynomial* size — the Beigel–Tarui
construction — remains the open wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModGateComposition

open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2 (satCount)

variable {n : ℕ}

/-- **Shared-layer `MOD` closure (proved).**  A `MOD_m` gate at residue `r` over `k` subcircuits that
all read the same bottom `AND`-layer `supp` (each `g i = sym i ∘ satCount supp`) is again `SYM∘AND`
over `supp` — exact, with the *same* bottom layer (no blow-up). -/
theorem hasSymAndRep_modGate_sharedLayer {t k m r : ℕ} {supp : Fin t → Finset (Fin n)}
    {g : Fin k → (Fin n → Bool) → Bool} {sym : Fin k → ℕ → Bool}
    (hg : ∀ i x, g i x = sym i (satCount supp x)) :
    HasSymAndRep (fun x => decide ((∑ i, (g i x).toNat) % m = r)) :=
  ⟨t, supp, fun s => decide ((∑ i, (sym i s).toNat) % m = r),
    fun x => by simp only [hg]⟩

/-- **Shared-layer `MOD` closure from per-subcircuit reps (proved).**  If every subcircuit `g i` has a
`SYM∘AND` representation `sym i` over the *same shared* layer `supp`, then the `MOD_m`-at-`r` gate over
them is `SYM∘AND`. -/
theorem hasSymAndRep_modGate_of_reps {t k m r : ℕ} {supp : Fin t → Finset (Fin n)}
    {g : Fin k → (Fin n → Bool) → Bool} (sym : Fin k → ℕ → Bool)
    (hrep : ∀ i x, g i x = sym i (satCount supp x)) :
    HasSymAndRep (fun x => decide ((∑ i, (g i x).toNat) % m = r)) :=
  hasSymAndRep_modGate_sharedLayer hrep

/-!
**MOD shared-layer closure proved.**  Together with the existing `NOT`/`AND`/`OR` shared-layer
closures, the `MOD/AND/OR/NOT` shared-bottom-layer ACC⁰ fragment is closed under composition into
`SYM∘AND` — exact, no blow-up.  The cross-layer (distinct bottom layers) case raises the count
dimension and meets the exact-vs-quasipoly Beigel–Tarui wall (`ACC0ExactCompose`).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModGateComposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModGateComposition.hasSymAndRep_modGate_sharedLayer
