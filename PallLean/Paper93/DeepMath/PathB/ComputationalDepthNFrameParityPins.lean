import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityEval

/-!
# N-Frame: the parity pins — discharging `hsol` and `heven`

Rung 26 of the arc (… → parity layout → **parity pins**).  The rung-24/25 detection interface
left two hypotheses open: `hsol` (the all-false predicate has exactly the two solutions of one
last free direction) and `heven` (the non-target count is even).  This file discharges both
from a concrete probe STRUCTURE — kit blocks + pin blocks — and a LINEAR package on the pin
and target functionals, all in kernel form (rank language stays on paper):

  `nonTarget_iff_pins` — **PROVED, the kit/pin collapse**: if every non-target block is kit
        (tautology selected) or pin (singleton literal), the non-target predicate IS the pin
        system.  (The forward direction needs `cstar ∉ PB` — a pin at the target block would
        break the equivalence; caught in the paper pressure-test.)
  `pair_solution_of_span` — **PROVED, the kernel-form rank statement**: if `a₀` solves the
        combined system (pins asserted, target content complemented), `w` lies in its joint
        kernel, and the joint kernel is EXACTLY `{0, w}`, then the combined solution set is
        exactly `{a₀, a₀ + w}` — `hsol` discharged.
  `pins_even` — **PROVED**: `w` in the pin kernel plus a splitting functional make the pin
        count even (the scout's `count_even_of_free_direction`) — `heven` discharged.
  `package_discharge` / `parity_detect_assembled` — **PROVED, the single entry point**:
        structure + linear package ⇒ the full rung-24 interface ⇒ the family flips, for both
        values of the added literal.

## Honest scope

The hypotheses of the linear package are where the remaining work lives: `hspan` (joint
kernel exactly `{0, w}`) is the pins-plus-scaffold spanning condition, and the AVAILABILITY
of pin blocks with live functionals under an adversarial balanced cut is the kill-cost
liveness + independence transversal — both are rung 27 (the adversarial balanced-cut
theorem), followed by the band assembly and the final `cbudget(sat3X⊕) ≥ (2+c)N` conversion.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityPins

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval

variable {v m : ℕ}

/-! ### The kit/pin collapse -/

/-- **The kit/pin collapse (proved)**: with every non-target block kit-or-pin, the non-target
predicate is the pin system. -/
theorem nonTarget_iff_pins (Bk : Fin m → Finset (Lit v)) (cstar : Fin m)
    (pinlit : Fin m → Lit v) (KB PB : Finset (Fin m))
    (hcover : ∀ c, c ≠ cstar → c ∈ KB ∨ c ∈ PB)
    (hkit : ∀ c ∈ KB, tautLit v ∈ Bk c)
    (hpin : ∀ c ∈ PB, Bk c = {pinlit c})
    (hPnc : cstar ∉ PB)
    (a : Fin v → ZMod 2) :
    (∀ c, c ≠ cstar → blockSat a (Bk c)) ↔ (∀ c ∈ PB, litHolds a (pinlit c)) := by
  constructor
  · intro h c hc
    have hcne : c ≠ cstar := fun hcon => hPnc (hcon ▸ hc)
    have hb := h c hcne
    rw [hpin c hc] at hb
    exact (blockSat_singleton _).mp hb
  · intro h c hc
    rcases hcover c hc with hK | hP
    · exact blockSat_of_taut (hkit c hK)
    · rw [hpin c hP]
      exact (blockSat_singleton _).mpr (h c hP)

/-! ### The pair-solution lemma (kernel form) -/

set_option maxHeartbeats 800000 in
/-- **The kernel-form rank statement (proved)**: `a₀` solves the combined system, `w` lies in
its joint kernel, and the joint kernel is exactly `{0, w}` — then the combined solution set
is exactly `{a₀, a₀ + w}`. -/
theorem pair_solution_of_span (Bk : Fin m → Finset (Lit v)) (cstar : Fin m)
    (pinlit : Fin m → Lit v) (PB : Finset (Fin m))
    (w a₀ : Fin v → ZMod 2)
    (hsolP : ∀ c ∈ PB, litHolds a₀ (pinlit c))
    (hsolT : ∀ ℓ ∈ Bk cstar, ¬ litHolds a₀ ℓ)
    (hkerP : ∀ c ∈ PB, dotp (pinlit c).1 w = 0)
    (hkerT : ∀ ℓ ∈ Bk cstar, dotp ℓ.1 w = 0)
    (hspan : ∀ u : Fin v → ZMod 2, (∀ c ∈ PB, dotp (pinlit c).1 u = 0) →
      (∀ ℓ ∈ Bk cstar, dotp ℓ.1 u = 0) → u = 0 ∨ u = w) :
    ∀ a, ((∀ c ∈ PB, litHolds a (pinlit c)) ∧ ∀ ℓ ∈ Bk cstar, ¬ litHolds a ℓ)
      ↔ (a = a₀ ∨ a = a₀ + w) := by
  have hne2 : ∀ x y : ZMod 2, ¬ x = y ↔ x = y + 1 := by decide
  have hxx : ∀ x : ZMod 2, x + x = 0 := by decide
  intro a
  constructor
  · rintro ⟨hp, ht⟩
    have hu1 : ∀ c ∈ PB, dotp (pinlit c).1 (a + a₀) = 0 := by
      intro c hc
      rw [dotp_add_right]
      have h1 : dotp (pinlit c).1 a = (pinlit c).2 := hp c hc
      have h2 : dotp (pinlit c).1 a₀ = (pinlit c).2 := hsolP c hc
      rw [h1, h2]
      exact hxx _
    have hu2 : ∀ ℓ ∈ Bk cstar, dotp ℓ.1 (a + a₀) = 0 := by
      intro ℓ hℓ
      rw [dotp_add_right]
      have h1 : dotp ℓ.1 a = ℓ.2 + 1 := (hne2 _ _).mp (ht ℓ hℓ)
      have h2 : dotp ℓ.1 a₀ = ℓ.2 + 1 := (hne2 _ _).mp (hsolT ℓ hℓ)
      rw [h1, h2]
      exact hxx _
    have hcancel : (a + a₀) + a₀ = a := by
      rw [add_assoc, add_self_cancel, add_zero]
    rcases hspan (a + a₀) hu1 hu2 with h0 | hw
    · left
      have h2 : (a + a₀) + a₀ = 0 + a₀ := by rw [h0]
      rw [zero_add, hcancel] at h2
      exact h2
    · right
      have h2 : (a + a₀) + a₀ = w + a₀ := by rw [hw]
      rw [hcancel] at h2
      rw [h2, add_comm]
  · rintro (rfl | rfl)
    · exact ⟨hsolP, hsolT⟩
    · constructor
      · intro c hc
        show dotp (pinlit c).1 (a₀ + w) = (pinlit c).2
        rw [dotp_add_right, hkerP c hc, add_zero]
        exact hsolP c hc
      · intro ℓ hℓ
        show ¬ dotp ℓ.1 (a₀ + w) = ℓ.2
        rw [dotp_add_right, hkerT ℓ hℓ, add_zero]
        exact hsolT ℓ hℓ

/-! ### The even count -/

/-- **The even-count discharge (proved)**: `w` in the pin kernel plus a splitting functional
make the pin count even. -/
theorem pins_even (pinlit : Fin m → Lit v) (PB : Finset (Fin m))
    (w l : Fin v → ZMod 2)
    (hkerP : ∀ c ∈ PB, dotp (pinlit c).1 w = 0)
    (hlw : dotp l w = 1) :
    (Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      ∀ c ∈ PB, litHolds a (pinlit c))).card % 2 = 0 := by
  classical
  have hshift : ∀ a : Fin v → ZMod 2,
      (∀ c ∈ PB, litHolds a (pinlit c)) ↔ (∀ c ∈ PB, litHolds (a + w) (pinlit c)) := by
    intro a
    constructor
    · intro h c hc
      show dotp (pinlit c).1 (a + w) = (pinlit c).2
      rw [dotp_add_right, hkerP c hc, add_zero]
      exact h c hc
    · intro h c hc
      have h2 : dotp (pinlit c).1 (a + w) = (pinlit c).2 := h c hc
      rw [dotp_add_right, hkerP c hc, add_zero] at h2
      exact h2
  exact count_even_of_free_direction _ w hshift l hlw

/-! ### The composed discharge and the assembled detection -/

set_option maxHeartbeats 800000 in
/-- **The package discharge (proved)**: structure + linear package ⇒ the rung-24 interface
(`hsol` and `heven`). -/
theorem package_discharge (Bk : Fin m → Finset (Lit v)) (cstar : Fin m)
    (pinlit : Fin m → Lit v) (KB PB : Finset (Fin m))
    (w a₀ l : Fin v → ZMod 2)
    (hcover : ∀ c, c ≠ cstar → c ∈ KB ∨ c ∈ PB)
    (hkit : ∀ c ∈ KB, tautLit v ∈ Bk c)
    (hpin : ∀ c ∈ PB, Bk c = {pinlit c})
    (hPnc : cstar ∉ PB)
    (hsolP : ∀ c ∈ PB, litHolds a₀ (pinlit c))
    (hsolT : ∀ ℓ ∈ Bk cstar, ¬ litHolds a₀ ℓ)
    (hkerP : ∀ c ∈ PB, dotp (pinlit c).1 w = 0)
    (hkerT : ∀ ℓ ∈ Bk cstar, dotp ℓ.1 w = 0)
    (hspan : ∀ u : Fin v → ZMod 2, (∀ c ∈ PB, dotp (pinlit c).1 u = 0) →
      (∀ ℓ ∈ Bk cstar, dotp ℓ.1 u = 0) → u = 0 ∨ u = w)
    (hlw : dotp l w = 1) :
    (∀ a : Fin v → ZMod 2,
      ((∀ c, c ≠ cstar → blockSat a (Bk c)) ∧ ∀ ℓ ∈ Bk cstar, ¬ litHolds a ℓ)
        ↔ (a = a₀ ∨ a = a₀ + w))
    ∧ (Finset.univ.filter (fun a : Fin v → ZMod 2 =>
        ∀ c, c ≠ cstar → blockSat a (Bk c))).card % 2 = 0 := by
  classical
  have hA := nonTarget_iff_pins Bk cstar pinlit KB PB hcover hkit hpin hPnc
  have hD := pair_solution_of_span Bk cstar pinlit PB w a₀
    hsolP hsolT hkerP hkerT hspan
  constructor
  · intro a
    constructor
    · rintro ⟨hnt, ht⟩
      exact (hD a).mp ⟨(hA a).mp hnt, ht⟩
    · intro h
      obtain ⟨hp, ht⟩ := (hD a).mpr h
      exact ⟨(hA a).mpr hp, ht⟩
  · have hEq : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
        ∀ c, c ≠ cstar → blockSat a (Bk c))
        = Finset.univ.filter (fun a : Fin v → ZMod 2 =>
        ∀ c ∈ PB, litHolds a (pinlit c)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hA a
    rw [hEq]
    exact pins_even pinlit PB w l hkerP hlw

set_option maxHeartbeats 800000 in
/-- **THE ASSEMBLED DETECTION (proved)**: kit/pin structure + the linear package ⇒ the family
flips when the target literal is added — for BOTH values `b`.  The single entry point for the
adversarial-cut rung: what remains is SUPPLYING pins with live functionals (kill-cost
liveness), the scaffold spanning (hspan), and the transversal placement, under an adversarial
balanced cut. -/
theorem parity_detect_assembled (Bk Bk' : Fin m → Finset (Lit v)) (cstar : Fin m)
    (pinlit : Fin m → Lit v) (KB PB : Finset (Fin m))
    (w a₀ l : Fin v → ZMod 2) (b : ZMod 2)
    (hlw : dotp l w = 1)
    (hBt : Bk' cstar = insert (l, b) (Bk cstar))
    (hBr : ∀ c, c ≠ cstar → Bk' c = Bk c)
    (hcover : ∀ c, c ≠ cstar → c ∈ KB ∨ c ∈ PB)
    (hkit : ∀ c ∈ KB, tautLit v ∈ Bk c)
    (hpin : ∀ c ∈ PB, Bk c = {pinlit c})
    (hPnc : cstar ∉ PB)
    (hsolP : ∀ c ∈ PB, litHolds a₀ (pinlit c))
    (hsolT : ∀ ℓ ∈ Bk cstar, ¬ litHolds a₀ ℓ)
    (hkerP : ∀ c ∈ PB, dotp (pinlit c).1 w = 0)
    (hkerT : ∀ ℓ ∈ Bk cstar, dotp ℓ.1 w = 0)
    (hspan : ∀ u : Fin v → ZMod 2, (∀ c ∈ PB, dotp (pinlit c).1 u = 0) →
      (∀ ℓ ∈ Bk cstar, dotp ℓ.1 u = 0) → u = 0 ∨ u = w) :
    parityFamily Bk = false ∧ parityFamily Bk' = true := by
  obtain ⟨hsol, heven⟩ := package_discharge Bk cstar pinlit KB PB w a₀ l
    hcover hkit hpin hPnc hsolP hsolT hkerP hkerT hspan hlw
  exact parity_detect Bk Bk' cstar w a₀ l b hlw hBt hBr hsol heven

end PallLean.Paper93.DeepMath.PathB.NFrameParityPins

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityPins.nonTarget_iff_pins
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityPins.pair_solution_of_span
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityPins.pins_even
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityPins.package_discharge
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityPins.parity_detect_assembled
