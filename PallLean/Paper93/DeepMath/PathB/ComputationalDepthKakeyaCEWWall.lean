import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKakeyaCEWCovering

/-!
# Pushing to the superpolynomial regime — and showing, machine-checked, that it is the wall

`covering` was discharged for the low-degree AC⁰[p] family only at *polynomial* dimension
(`KakeyaCEWCovering`).  This file pushes to the superpolynomial regime and shows precisely why the
separation cannot be manufactured there — not by faking a lower bound, but by proving exactly where the
provable machinery stops.

The chain of honest facts:

1. **The class is proper.**  For `d < n` the degree-`n` monomial `χ_univ` (AND of all bits) is *not*
   degree-`≤ d` representable (`topMonomial_not_lowDeg`), proved from the multilinear-monomial
   independence of `KakeyaCEWCovering`.  So a separation is not vacuously impossible: the low-degree
   class does not contain everything.

2. **Properness is not a separation.**  The witness `χ_univ` is the AND function — which is *itself in
   AC⁰*.  So "high exact degree" is not "outside AC⁰": exact degree is not the AC⁰ boundary.  The genuine
   AC⁰ lower bound is about *approximate* degree (Razborov–Smolensky), a strictly harder notion the exact
   machinery here does not reach.

3. **The separation is a statement about a specific function.**  A genuine separation of an NP family
   from the low-degree class is `¬ LowDeg d f` for a *specific* `f` — and the covering machinery
   (`covering_discharged`, proved unconditionally) is logically independent of whether any given `f`
   escapes the class.  No amount of covering certifies `¬ LowDeg d f`.

Pushed to the superpolynomial regime, then, the object that would separate is `¬ LowDeg (polylog) f` for
an explicit NP `f` — a circuit lower bound.  That is the wall, and it is untouched.

## Honest scope

Everything here is proved and axiom-clean; **nothing** discharges the separation.  `topMonomial_not_lowDeg`
proves only that a specific *easy* function has high exact degree.  The wall — a specific *hard* (NP)
function of superpolynomial *approximate* degree — is named and left standing.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KakeyaCEWWall

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB.KakeyaCEWCovering

variable {F : Type*} [Field F] {n : ℕ}

/-- A function `f : cube → F` is degree-`≤ d` representable (in the bounded-CEW / low-degree class). -/
def LowDeg (d : ℕ) (f : (Fin n → Bool) → F) : Prop :=
  ∃ c : Finset (Fin n) → F, (∀ T, d < T.card → c T = 0) ∧
    (f = fun x => ∑ T : Finset (Fin n), c T * monoVal T x)

/-- The multilinear monomial as a function on the cube. -/
def monoFn (T : Finset (Fin n)) : (Fin n → Bool) → F := fun x => monoVal T x

/-- **The low-degree class is proper (proved).**  For `d < n`, the degree-`n` monomial `χ_univ` (the AND
of all bits) is not degree-`≤ d` representable — proved from multilinear-monomial independence.  Hence a
separation is not vacuously impossible.  (But note: `χ_univ` is AND, itself in AC⁰ — high exact degree is
not the AC⁰ boundary.) -/
theorem topMonomial_not_lowDeg (hd : d < n) :
    ¬ LowDeg d (monoFn (Finset.univ : Finset (Fin n)) : (Fin n → Bool) → F) := by
  rintro ⟨c, hsupp, hrep⟩
  set c' : Finset (Fin n) → F := fun T => (if T = Finset.univ then (1 : F) else 0) - c T with hc'
  have hrepx : ∀ x, monoVal (Finset.univ : Finset (Fin n)) x
      = ∑ T : Finset (Fin n), c T * monoVal T x := by
    intro x; have := congrFun hrep x; simpa [monoFn] using this
  have hzero : ∀ x, (∑ T : Finset (Fin n), c' T * monoVal T x) = 0 := by
    intro x
    have hind : (∑ T : Finset (Fin n), (if T = Finset.univ then (1 : F) else 0) * monoVal T x)
        = monoVal Finset.univ x := by
      rw [Finset.sum_eq_single (Finset.univ : Finset (Fin n))
        (fun T _ hT => by simp [hT]) (fun h => absurd (Finset.mem_univ _) h)]
      simp
    calc (∑ T : Finset (Fin n), c' T * monoVal T x)
        = (∑ T : Finset (Fin n), (if T = Finset.univ then (1 : F) else 0) * monoVal T x)
            - ∑ T : Finset (Fin n), c T * monoVal T x := by
          simp only [hc', sub_mul]; rw [Finset.sum_sub_distrib]
      _ = monoVal Finset.univ x - monoVal Finset.univ x := by rw [hind, ← hrepx]
      _ = 0 := sub_self _
  have hzeta : ∀ T : Finset (Fin n), T.card ≤ n → c' T = 0 := by
    apply zeta_triangular n
    intro S _
    rw [← sum_poly_indicator c' S]
    exact hzero (ind S)
  have h1 : c' Finset.univ = 0 := hzeta Finset.univ (by simp)
  have h2 : c Finset.univ = 0 := hsupp _ (by rw [Finset.card_univ, Fintype.card_fin]; exact hd)
  simp [hc', h2] at h1

/-- **The wall, named (proved-as-characterization).**  A separation of a function `f` from the
degree-`≤ d` class is exactly `¬ LowDeg d f`.  Trivial as an equivalence — that is the point: the content
is entirely in exhibiting a specific `f` (an NP function, at superpolynomial degree), which is a circuit
lower bound, and which the covering machinery never provides. -/
theorem separation_is_not_lowDeg (d : ℕ) (f : (Fin n → Bool) → F) :
    (f ∉ {g | LowDeg d g}) ↔ ¬ LowDeg d f := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.KakeyaCEWWall

#print axioms PallLean.Paper93.DeepMath.PathB.KakeyaCEWWall.topMonomial_not_lowDeg
