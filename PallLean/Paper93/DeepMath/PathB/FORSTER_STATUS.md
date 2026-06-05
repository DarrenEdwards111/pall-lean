# Forster sign-rank lower bound — status (COMPLETE to ceiling)

**Result (unconditional, clean `[propext, Classical.choice, Quot.sound]`, no `sorry`):**

- `ForsterUPP.forster_signRank_lower` — Forster's theorem: for a `±1` matrix `M`,
  `√((m'+1)²)/‖sgnMat M‖ ≤ d` whenever `HasSignRankLE M d`.  **No general-position
  hypothesis** (removed via perturbation in `ForsterUnconditional`).
- `ForsterUPP.walsh_forsterLowerBound` — the explicit `2^{2j} × 2^{2j}`
  Walsh–Hadamard matrix has `ForsterLowerBound … (2^j)`: sign-rank `≥ 2^j = √(dim)`.

**Pipeline (all proved):**
- Isotropic position / tight frame (`ForsterIsotropic.exists_isotropic`): the full
  analytic `∃T` via log-potential minimization — coercivity (spanning + generalized
  Hadamard/AM–GM) ⇒ minimizer (EVT on compact PSD slice) ⇒ first-order optimality
  (Jacobi's formula, **not in Mathlib**) ⇒ tight frame; `T = √S⋆` (`exists_symm_sqrt`).
- Wiring (`ForsterWiring`): matrix tight frame ⇒ Euclidean tight frame (exact, no fudge).
- Bound (`ForsterScaffold.forster_bound_of_tightFrame`, `ForsterUnconditional.
  forster_bound_unconditional`): tight frame + spectral upper bound ⇒ dimension bound.
- Walsh–Hadamard instantiation (`ForsterUPP`): explicit matrix, `‖sgnMat‖ = √dim`.

**Principled ceiling (the remaining wall, fenced, not faked):** connecting the
sign-rank / UPP lower bound to *general circuit* complexity — the margin-free
`O(log s)` UPP protocol from a poly-size circuit.  `ForsterUPP` records the no-go
that the constant-bias (full-rank) route cannot bypass Forster.  This is the known
hard complexity question (UPP/PH ↔ circuits), not a missing Lean lemma.

So: an explicit-matrix sign-rank lower bound is a complete formal artifact; the
circuit-complexity application is the open research wall.
