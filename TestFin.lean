import PallLean.MultilinearSPDP

open MvPolynomial

-- Test: what does Finsupp.induction goal look like?
example (s : Fin 3 →₀ ℕ) (h : s.prod (fun j (k : ℕ) => (j : ℕ) + k) = 0) : True := by
  trivial
