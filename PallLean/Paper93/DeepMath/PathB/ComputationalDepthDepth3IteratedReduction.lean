import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ReduceChain

/-!
# AC⁰ reduction, foundation 37: the d-fold chaining induction (branch only)

The inductive engine of the multi-round loop.  Given a sequence of towers `C 0, C 1, …` and nested
restrictions `ρ 0, ρ 1, …` (all extended by a common finest `σ`), with each round a subcube-equivalence
`EquivOn (ρ i) (C i) (C (i+1))`, the `d`-fold composition is a single `Reduces` from `C 0` to `C d` on
`σ`'s subcube — proved by induction on `d` using `Reduces.round` (brick 31) and `Reduces.trans` (brick 20).
Wiring that through `tower_not_parity` (brick 21) gives: if the `d`-th tower is a bottom `DNF` whose
canonical tree is shallow relative to the survivors, the original tower does not compute parity.

* `reduces_iterate` — the `d`-fold `Reduces` chain (axiom-free).
* `iterated_not_parity` — the original tower `C 0` does not compute parity on `σ`'s subcube.

The round data `(C, ρ, heq, hext)` is exactly what iterating the concrete one-round step
(`one_round_exists_p_fifth_dim`, brick 36) and the collapse/merge operations produce; this theorem is the
induction that consumes it.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

/-- **The `d`-fold reduction chain.**  Folding `d` nested subcube-equivalence rounds gives a single
reduction `C 0 ⟶ C d` on `σ`'s subcube. -/
theorem reduces_iterate (x : Fin n → Bool) (σ : Fin n → Option Bool)
    (C : ℕ → Layered n) (ρ : ℕ → Fin n → Option Bool)
    (hext : ∀ i, Extends (ρ i) σ) (hag : DTree.agreeRestriction σ x)
    (heq : ∀ i, EquivOn (ρ i) (C i) (C (i + 1))) :
    ∀ d, Reduces x (C 0) (C d) := by
  intro d
  induction d with
  | zero => exact Reduces.refl _
  | succ d ih =>
    exact ih.trans (Reduces.round (hext d) hag (heq d) (Reduces.refl (C (d + 1))))

/-- **The `d`-fold chaining capstone.**  If `d` nested rounds reduce `C 0` to a bottom `DNF` `D` whose
canonical tree is shallow relative to the survivors of `σ`, then `C 0` does not compute parity on `σ`'s
subcube. -/
theorem iterated_not_parity (C : ℕ → Layered n) (ρ : ℕ → Fin n → Option Bool)
    (σ : Fin n → Option Bool) (d : ℕ) (D : List (Clause n)) (w F : ℕ)
    (hext : ∀ i, Extends (ρ i) σ) (heq : ∀ i, EquivOn (ρ i) (C i) (C (i + 1)))
    (hCd : C d = dnf D) (hsf : stars σ < F)
    (hshallow : (canonicalDTree D w F σ).depth < stars σ) :
    ¬ (∀ x, DTree.agreeRestriction σ x → eval (C 0) x = DTree.parity x) :=
  tower_not_parity (C 0) D w F σ hsf hshallow (fun x hx => by
    have h := reduces_iterate x σ C ρ hext hx heq d
    rw [hCd] at h
    exact h)

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.reduces_iterate
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.iterated_not_parity
