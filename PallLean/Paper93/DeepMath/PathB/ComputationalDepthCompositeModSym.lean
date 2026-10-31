import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompositeModRing

/-!
# Composite `MOD_m`: the symmetric-gate characterisation

Rungs 1–2 gave the CRT decomposition of `MOD_m` and the ring-level barrier (`ZMod m` is not a field for composite `m`).
This file records the positive structural fact that locates the difficulty precisely: a `MOD_m` gate is a **symmetric
function of the input count**, and that count is a *degree-1 linear form* — so the `MOD_m` gate itself is trivially a
`SYM` of a degree-`1` polynomial, in the `SYM⁺` shape Toda / Beigel–Tarui use.  The obstruction is therefore **not** the
`MOD_m` gate in isolation but the *composition* of `AND`/`OR` above `MOD` gates of incompatible characteristics.

  `boolCount` — the number of `true` inputs (`∑ᵢ [xᵢ]`), the degree-1 linear form the `MOD_m` gate reads.
  `modSym m x` — the `MOD_m` gate on `n` inputs: `modAccept m (boolCount x)`.
  `boolCount_perm` — **PROVED**: the count is invariant under any input permutation.
  `modSym_perm_invariant` — **PROVED**: the `MOD_m` gate is a *symmetric* function (permutation-invariant).
  `modSym_depends_on_count` — **PROVED**: it depends only on the count — a genuine `SYM` gate.
  `modSym_crt` — **PROVED**: for coprime `a, b`, `modSym (a*b) = modSym a ∨ modSym b` (the CRT factoring, at the gate level).

## Honest scope — locating the difficulty, not resolving it

This shows the composite `MOD_m` gate is a symmetric function of a degree-`1` linear form (`boolCount`), so as an isolated
gate it is already in the `SYM⁺` normal form Williams' method targets.  The Razborov–Smolensky wall is therefore not here
— it is in composing `AND`/`OR` gates *above* `MOD` gates of different prime characteristics, where no single field keeps
the whole circuit low-degree (rung 2's ring barrier).  Toda's resolution lifts the composition to a symmetric polynomial
over `ℤ`; that construction (the `NEXP`-strength core of Williams' method) is **not** established here.  This file supplies
only the symmetric-gate characterisation.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CompositeMod

open Finset

variable {n : ℕ}

/-- The number of `true` inputs — the degree-`1` linear form a `MOD` gate reads. -/
def boolCount (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

/-- The `MOD_m` gate on `n` inputs, as the accept-indicator of the input count. -/
def modSym (m : ℕ) (x : Fin n → Bool) : Bool := modAccept m (boolCount x)

/-- **The count is permutation-invariant (proved)**. -/
theorem boolCount_perm (x : Fin n → Bool) (σ : Equiv.Perm (Fin n)) :
    boolCount (x ∘ σ) = boolCount x := by
  simp only [boolCount, Finset.card_filter]
  exact Fintype.sum_equiv σ _ _ (fun i => by simp [Function.comp])

/-- **`MOD_m` is a symmetric function (proved)**: invariant under any permutation of its inputs. -/
theorem modSym_perm_invariant (m : ℕ) (x : Fin n → Bool) (σ : Equiv.Perm (Fin n)) :
    modSym m (x ∘ σ) = modSym m x := by
  simp only [modSym, boolCount_perm]

/-- **`MOD_m` depends only on the count (proved)**: it is a genuine `SYM` gate. -/
theorem modSym_depends_on_count (m : ℕ) (x y : Fin n → Bool) (h : boolCount x = boolCount y) :
    modSym m x = modSym m y := by
  simp only [modSym, h]

/-- **The CRT factoring at the gate level (proved)**: for coprime `a, b`, `MOD_{a·b} = MOD_a ∨ MOD_b`. -/
theorem modSym_crt {a b : ℕ} (h : Nat.Coprime a b) (x : Fin n → Bool) :
    modSym (a * b) x = (modSym a x || modSym b x) := by
  simp only [modSym, modAccept_mul h]

end PallLean.Paper93.DeepMath.PathB.CompositeMod

#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.boolCount_perm
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.modSym_perm_invariant
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.modSym_crt
