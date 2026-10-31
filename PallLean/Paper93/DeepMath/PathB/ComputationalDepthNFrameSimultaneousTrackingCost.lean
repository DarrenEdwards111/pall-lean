import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSelectorTrackedContexts

/-!
# N-Frame: simultaneous tracking cost — the vise, closed to a single inequality

The final assembly.  For every tracked selector in a minimal circuit, exactly one of:

  * **duplication or reuse** — paid by the kill engine (`cbudget_fanout_kill`);
  * **mediation** — and then a mediator wire is installed *inside the budget* (`r < cbudget`), owing the
        **entire** `2^(m−2)`-context flip-obligation cube (`sat3_selector_port_tracks_contexts`), with the
        capacity theorem supplying at least half as many distinct such wires as tracked selectors
        (`selector_count_le_two_mul_ports`).

  `simultaneous_tracking_cost` — **PROVED**: the per-coordinate vise, with the obligation cube and the
        budget residence made explicit in the mediation branch.

## Honest scope — the single remaining inequality

What is **not** proved, and is the mountain: that the assembled obligations exceed the connectivity budget.
A tight binary tree at `2·m·D − 1` gates realizes every structural obligation listed here — every variable
read once, every reader a mediator, every flip obligation dischargeable by pass-through — so the closing
inequality `cbudget > 2·m·D − 1 + Ω(K)` cannot follow from structure alone; it must show that budget-priced
wires cannot *semantically* satisfy all obligation cubes at once while the shared top completes SAT.  Both
jaws of the vise are now theorems; the closing force is the one open statement.  A last structural gap worth
filling first: dead-gate elimination (Normal Form IV — every interior wire of a minimal circuit is read),
the remaining surgery, named as the next mechanical rung.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE VISE (proved)**: every tracked selector either pays the kill engine or installs a budget-resident
mediator wire owing the entire context-cube of flip obligations. -/
theorem simultaneous_tracking_cost (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N)) (hjv : sat3M N - 2 ≤ j.val) :
    (∃ p₁ p₂, p₁ ≠ p₂ ∧ c.getD p₁ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      c.getD p₂ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j)) ∨
    (∃ p r₁ r₂, r₁ ≠ r₂ ∧ c.getD p (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      p ∈ childrenOf c r₁ ∧ p ∈ childrenOf c r₂) ∨
    (∃ p r, MediatedAt c (sat3S2Sel N cIdx j) p r ∧
      r < cbudget (sat3Family N) ∧
      ∀ bvec : Fin (sat3M N - 2) → Bool,
        (runFrom (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
            (fun _ => false)) (sat3S2Sel N cIdx j) true) [] c).getD r false
        ≠ (runFrom (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
            (fun _ => false)) (sat3S2Sel N cIdx j) false) [] c).getD r false) := by
  rcases sat3_selector_terminal N hv (by omega) cIdx j c hcomp with hd | hr | ⟨p, r, hmed⟩
  · exact Or.inl hd
  · exact Or.inr (Or.inl hr)
  · refine Or.inr (Or.inr ⟨p, r, hmed, ?_, ?_⟩)
    · have h := hmed.2.2.2.1
      omega
    · exact sat3_selector_port_tracks_contexts N hv hm3 hk cIdx j hjv c hcomp p r hmed

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.simultaneous_tracking_cost
