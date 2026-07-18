import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEqInP

/-!
# Nondeterministic communication complexity via the cover number

The *nondeterministic* (one-sided, accepting) communication complexity `N¹(f)` is `⌈log₂⌉` of the
**1-cover number** `C¹(f)` — the least number of all-`1` combinatorial rectangles needed to cover
`f⁻¹(1)`.  (A nondeterministic protocol guesses a rectangle and both players verify membership;
the guessed certificate names one of `C¹(f)` rectangles.)

The lower-bound engine is again the **fooling set**, now against covers rather than partitions:
each all-`1` rectangle can contain at most one `true`-valued fooling input (two would force both
off-diagonal crossings to be `1`, which the fooling condition forbids), so a size-`s` fooling set
forces `≥ s` rectangles (`cover_fooling_ge`).

The witness is EQUALITY.  Its `1`-inputs are the diagonal `{(x, x)}`, a size-`2^n` fooling set, so
its 1-cover number is `≥ 2^n` — and exactly `2^n`, since the `2^n` singleton diagonal rectangles
cover it (`eqCover`).  Thus `N¹(EQ) = n`: nondeterminism does **not** help decide equality (its
complement `NEQ` is nondeterministically easy — guess a differing coordinate — but `EQ` is not).
Combined with `eqLang_inP` this is `P ⊄` sublinear nondeterministic communication.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NondetCommLB

open PallLean.Paper93.DeepMath.PathB.ComposableMachine (InP)
open PallLean.Paper93.DeepMath.PathB.TwoWayCommFooling
open PallLean.Paper93.DeepMath.PathB.EqInP

/-- A nondeterministic (1-)protocol as a **1-cover**: `k` combinatorial rectangles, each all-`1`
(monochromatic for value `true`), together covering every `1`-input of `f`.  The nondeterministic
communication complexity of `f` is `⌈log₂⌉` of the least such `k`. -/
structure Cover {α β : Type} (f : α → β → Bool) (k : ℕ) where
  /-- Rectangle `i`'s row set (membership on `α`). -/
  ra : Fin k → α → Bool
  /-- Rectangle `i`'s column set (membership on `β`). -/
  rb : Fin k → β → Bool
  /-- Each rectangle is all-`1`. -/
  mono : ∀ i u v, ra i u = true → rb i v = true → f u v = true
  /-- The rectangles cover every `1`-input. -/
  covers : ∀ u v, f u v = true → ∃ i, ra i u = true ∧ rb i v = true

/-- **The cover-number fooling bound.**  A `true`-valued fooling set lower-bounds the number of
rectangles in any 1-cover: an all-`1` rectangle contains at most one fooling input (two would force
both off-diagonal crossings to be `true`, which the fooling condition forbids), so the covering
index is injective on the fooling set. -/
theorem cover_fooling_ge {α β : Type} (f : α → β → Bool) (k : ℕ)
    (C : Cover f k) (S : Finset (α × β)) (hS : FoolingSet f S true) : S.card ≤ k := by
  classical
  obtain ⟨hval, hfool⟩ := hS
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp
  · obtain ⟨p₀, hp₀⟩ := hSne
    obtain ⟨i₀, _, _⟩ := C.covers p₀.1 p₀.2 (hval p₀ hp₀)
    haveI : Nonempty (Fin k) := ⟨i₀⟩
    have hcov : ∀ p, p ∈ S → ∃ i, C.ra i p.1 = true ∧ C.rb i p.2 = true :=
      fun p hp => C.covers p.1 p.2 (hval p hp)
    choose! g hg using hcov
    have hinj : ∀ p ∈ S, ∀ q ∈ S, g p = g q → p = q := by
      intro p hp q hq hgpq
      by_contra hpq
      obtain ⟨hpa, hpb⟩ := hg p hp
      obtain ⟨hqa, hqb⟩ := hg q hq
      have h1 : f p.1 q.2 = true := C.mono (g p) p.1 q.2 hpa (by rw [hgpq]; exact hqb)
      have h2 : f q.1 p.2 = true := C.mono (g p) q.1 p.2 (by rw [hgpq]; exact hqa) hpb
      exact hfool p hp q hq hpq ⟨h1, h2⟩
    calc S.card
        = (S.image g).card :=
          (Finset.card_image_of_injOn (fun p hp q hq h => hinj p hp q hq h)).symm
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = k := by simp

/-! ## EQUALITY -/

/-- **EQUALITY needs `≥ 2^n` covering rectangles.**  Its diagonal is a size-`2^n` fooling set. -/
theorem eq_cover_ge (n k : ℕ) (C : Cover (EQ n) k) : 2 ^ n ≤ k := by
  have := cover_fooling_ge (EQ n) k C (diagFool n) (diagFool_isFooling n)
  rwa [diagFool_card] at this

/-- **EQUALITY has nondeterministic communication complexity `≥ n`.** -/
theorem eq_nondet_ge (n k : ℕ) (C : Cover (EQ n) k) : n ≤ Nat.log 2 k := by
  have hk : 2 ^ n ≤ k := eq_cover_ge n k C
  calc n = Nat.log 2 (2 ^ n) := (Nat.log_pow Nat.one_lt_two n).symm
    _ ≤ Nat.log 2 k := Nat.log_mono_right hk

/-- The `2^n` singleton diagonal rectangles cover EQUALITY's `1`-inputs — the matching upper
bound, so the 1-cover number is exactly `2^n`. -/
noncomputable def eqCover (n : ℕ) : Cover (EQ n) (2 ^ n) :=
  let e : (Fin n → Bool) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin])
  { ra := fun i u => decide (u = e.symm i)
    rb := fun i v => decide (v = e.symm i)
    mono := by
      intro i u v hu hv
      simp only [decide_eq_true_eq] at hu hv
      simp [EQ, hu, hv]
    covers := by
      intro u v huv
      simp only [EQ, decide_eq_true_eq] at huv
      subst huv
      exact ⟨e u, by simp [Equiv.symm_apply_apply], by simp [Equiv.symm_apply_apply]⟩ }

/-- **EQUALITY's nondeterministic complexity is exactly `2^n` rectangles.**  `2^n` suffice
(`eqCover`) and are necessary (`eq_cover_ge`) — tight. -/
theorem eq_nondet_exact (n : ℕ) :
    Nonempty (Cover (EQ n) (2 ^ n)) ∧ ∀ k, Cover (EQ n) k → 2 ^ n ≤ k :=
  ⟨⟨eqCover n⟩, fun k C => eq_cover_ge n k C⟩

/-- **P ⊄ sublinear nondeterministic communication.**  `eqLang ∈ P`, yet every 1-cover of the
length-`n` equality problem uses `≥ 2^n` rectangles, i.e. `≥ n` nondeterministic bits.  Polynomial
time does not imply sublinear nondeterministic communication — nondeterminism does not shrink the
equality problem below linear. -/
theorem P_not_sublinear_nondet :
    InP eqLang ∧ ∀ (n k : ℕ), Cover (EQ n) k → n ≤ Nat.log 2 k :=
  ⟨eqLang_inP, fun n k C => eq_nondet_ge n k C⟩

end PallLean.Paper93.DeepMath.PathB.NondetCommLB
