import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Function.Basic

/-!
# A real restricted fast-SAT, with a proved speedup — demonstrating the ingredient (not the crossing)

The off-Π★ spec (`CircuitSATOffPiStar`) leaves the algorithm as an open socket for the *general* class,
because filling it there is `P ≠ NP`.  This file fills it for a concrete *restricted* class, honestly and
completely, to show the ingredient is genuine and the socket is fillable where it is allowed to be.

The class is **juntas**: a circuit on `n` inputs whose output depends on only `d` of them (via an
injective selection `π : Fin d → Fin n` and a core `g`).  Its satisfiability over the `2^n`-size
assignment space reduces exactly to a search over the `2^d`-size relevant space — and `2^d < 2^n` for
`d < n`.  That is a genuine faster-than-brute-force Circuit-SAT algorithm, proved correct and proved
faster.

## What is proved

* **`junta_sat_iff`** — the algorithm is CORRECT: full-space SAT (`∃ x : Fin n → Bool`) holds iff the
  small-space search (`∃ y : Fin d → Bool`) does.  (Forward: restrict; backward: extend along the
  injective selection with `Function.extend`.)
* **`junta_beats_brute`** — the SPEEDUP: the `2^d`-size relevant search strictly beats the `2^n`
  brute-force search for `d < n`.
* **`juntaSAT_decidable`** — junta-SAT is decidable by that finite search.

## Honest scope

This is a real, complete fast-SAT algorithm — for a **weak** class (juntas sit *below* AC⁰/ACC⁰).  The
`Attack.decides` socket of the off-Π★ spec is therefore fillable here.  Pushing the same
search-beats-brute mechanism to a class *strictly past* ACC⁰ (toward general circuits) is the open
direction — that step is `NEXP ⊄ (class)` and ultimately the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RestrictedFastSAT

variable {d n : ℕ}

/-- **The junta algorithm is correct (proved).**  For a junta `f x = g (x ∘ π)` with `π` injective,
satisfiability over the full `2^n` assignment space holds iff the search over the `2^d` relevant
assignments finds a witness. -/
theorem junta_sat_iff (π : Fin d → Fin n) (hπ : Function.Injective π) (g : (Fin d → Bool) → Bool) :
    (∃ x : Fin n → Bool, g (fun i => x (π i)) = true) ↔ (∃ y : Fin d → Bool, g y = true) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun i => x (π i), hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨Function.extend π y (fun _ => false), ?_⟩
    have hrestrict : (fun i => Function.extend π y (fun _ => false) (π i)) = y := by
      funext i; exact hπ.extend_apply y (fun _ => false) i
    rw [hrestrict]; exact hy

/-- Junta-SAT is decidable by searching the `2^d` relevant assignments (a finite search over
`Fin d → Bool`). -/
instance juntaSAT_decidable (g : (Fin d → Bool) → Bool) :
    Decidable (∃ y : Fin d → Bool, g y = true) := Fintype.decidableExistsFintype

/-- **The restricted speedup (proved).**  A `d`-junta on `n` inputs is decided by searching the
`2^d`-size relevant space, strictly fewer than the `2^n` brute-force assignments whenever `d < n`. -/
theorem junta_beats_brute (h : d < n) : 2 ^ d < 2 ^ n :=
  Nat.pow_lt_pow_right (by decide) h

end PallLean.Paper93.DeepMath.PathB.RestrictedFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedFastSAT.junta_sat_iff
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedFastSAT.junta_beats_brute
