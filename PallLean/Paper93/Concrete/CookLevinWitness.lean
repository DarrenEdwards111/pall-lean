/-
  PallLean/Paper93/Concrete/CookLevinWitness.lean

  Cook-Levin witness polynomial family indexed by `n`, exposed as a
  concrete polynomial sequence in `MvPolynomial (Fin n) ℚ`.

  U14 stub: the witness is returned as `0` for all `n`. Agent U16 will
  replace this stub with the real Cook-Levin witness (e.g. produced by
  `cookLevinQ`), at which point `cookLevinWitness_zero` will be removed
  or generalised.

  The signature deliberately carries the hypotheses
    * `hn  : n ≥ 2`                (problem-size precondition)
    * `htb : True`                 (placeholder for the T/B budget slot)
    * `hns : True`                 (placeholder for the NS/coupled slot)
  so that downstream call-sites already match the eventual U16 API.
-/

import Mathlib.Algebra.MvPolynomial.Basic

namespace PallLean.Paper93.Concrete

open MvPolynomial

/-- Cook-Levin witness polynomial family indexed by `n`.

    U14 stub: returns `0`. The real witness (U16) will use `cookLevinQ`. -/
noncomputable def cookLevinWitness
    (n : ℕ) (hn : n ≥ 2) (htb : True) (hns : True) :
    MvPolynomial (Fin n) ℚ :=
  0

/-- U14 stub equation: the current stub witness is identically `0`. -/
theorem cookLevinWitness_zero
    (n : ℕ) (hn : n ≥ 2) (htb : True) (hns : True) :
    cookLevinWitness n hn htb hns = 0 := rfl

end PallLean.Paper93.Concrete
