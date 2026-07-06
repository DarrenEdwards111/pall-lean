import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityFlipScout

/-!
# N-Frame: the parity eval layer — `F = Z mod 2` for `sat3X⊕`

Rung 24 of the arc (… → parity-flip scout → **parity eval**).  The SEMANTIC layer of
`sat3X⊕`: instances are block families of affine-literal sets over the hidden witness
`a ∈ F₂^v`; the family value is the PARITY of the number of satisfying witnesses.  This file
proves the reduction announced in the task-3c audit: kit-neutralized blocks plus unit-clause
pins collapse the family's value to exactly the affine counts governed by the scout lemmas —
and composes it with `parity_flip` into the detection theorem.

  `litHolds` / `tautLit` / `blockSat` / `instSat` / `parityFamily` — the semantic family.
        The kit needs NO special mechanism: the tautology selector IS the literal `(0, 0)`,
        true at every witness — the intrinsic-kit design formalizes itself
        (`blockSat_of_taut`).
  `blockSat_singleton` — a singleton block is a unit-clause pin.
  `count_split` — **PROVED, THE `F = Z` REDUCTION**: for any target block,
        `#sat + #(non-target ∧ all-false at target) = #(non-target)` — an ADDITIVE identity,
        so all parity bookkeeping is subtraction-free.
  `parity_detect` / `parity_detect_ne` — **PROVED, THE DETECTION THEOREM**: if the non-target
        count is even and the all-false predicate has exactly the two solutions of one last
        free direction split by the target functional (`parity_flip`'s package), then
        `parityFamily = false` WITHOUT the target literal and `= true` WITH it — for BOTH
        values `b` of the added literal.  Value-independence, now at the family level.

## Honest scope

This is the semantic layer: the family lives on structured block contents, not yet on the
`Fin N → Bool` bit layout — positions, cut geometry, rows/probes as `mixOn` overlays, and the
instantiation of `hsol`/`heven` from pins + scaffold (via the kill-cost liveness and the
independence transversal) are the next rungs.  The chain targeted is
`kill-cost + transversal + parity detection ⇒ j = Θ(N) ⇒ coneExcess = Θ(N) ⇒
cbudget(sat3X⊕) ≥ (2+c)N`, for a ⊕P-shaped family (NP bridge deferred via
Valiant–Vazirani).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityEval

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout

variable {v m : ℕ}

/-- An affine literal: a functional and its demanded value. -/
abbrev Lit (v : ℕ) := (Fin v → ZMod 2) × ZMod 2

/-- The literal holds at witness `a`. -/
def litHolds (a : Fin v → ZMod 2) (ℓ : Lit v) : Prop := dotp ℓ.1 a = ℓ.2

instance (a : Fin v → ZMod 2) (ℓ : Lit v) : Decidable (litHolds a ℓ) :=
  inferInstanceAs (Decidable (dotp ℓ.1 a = ℓ.2))

/-- The tautology literal `(0, 0)` — the intrinsic kit. -/
def tautLit (v : ℕ) : Lit v := (0, 0)

theorem litHolds_taut (a : Fin v → ZMod 2) : litHolds a (tautLit v) := by
  show dotp 0 a = 0
  unfold dotp
  simp

/-- A block is satisfied: some selected literal holds. -/
def blockSat (a : Fin v → ZMod 2) (T : Finset (Lit v)) : Prop :=
  ∃ ℓ ∈ T, litHolds a ℓ

instance (a : Fin v → ZMod 2) (T : Finset (Lit v)) : Decidable (blockSat a T) :=
  inferInstanceAs (Decidable (∃ ℓ ∈ T, litHolds a ℓ))

/-- The instance is satisfied by `a`: every block is. -/
def instSat (a : Fin v → ZMod 2) (Bk : Fin m → Finset (Lit v)) : Prop :=
  ∀ c, blockSat a (Bk c)

instance (a : Fin v → ZMod 2) (Bk : Fin m → Finset (Lit v)) :
    Decidable (instSat a Bk) :=
  inferInstanceAs (Decidable (∀ c, blockSat a (Bk c)))

/-- **THE SEMANTIC FAMILY**: the parity of the number of satisfying witnesses. -/
def parityFamily (Bk : Fin m → Finset (Lit v)) : Bool :=
  decide ((Finset.univ.filter (fun a => instSat a Bk)).card % 2 = 1)

/-! ### Kit and pin readings -/

/-- Kit neutralization: a block containing the tautology literal is always satisfied. -/
theorem blockSat_of_taut {a : Fin v → ZMod 2} {T : Finset (Lit v)}
    (h : tautLit v ∈ T) : blockSat a T :=
  ⟨tautLit v, h, litHolds_taut a⟩

/-- Unit-clause pin: a singleton block is satisfied exactly when its literal holds. -/
theorem blockSat_singleton {a : Fin v → ZMod 2} (ℓ : Lit v) :
    blockSat a {ℓ} ↔ litHolds a ℓ := by
  constructor
  · rintro ⟨ℓ', hℓ', h⟩
    rw [Finset.mem_singleton] at hℓ'
    rwa [hℓ'] at h
  · intro h
    exact ⟨ℓ, Finset.mem_singleton_self ℓ, h⟩

theorem not_blockSat_iff {a : Fin v → ZMod 2} {T : Finset (Lit v)} :
    ¬ blockSat a T ↔ ∀ ℓ ∈ T, ¬ litHolds a ℓ := by
  constructor
  · intro h ℓ hℓ hh
    exact h ⟨ℓ, hℓ, hh⟩
  · rintro h ⟨ℓ, hℓ, hh⟩
    exact h ℓ hℓ hh

/-- The ∀-split at a designated target block. -/
theorem instSat_split (Bk : Fin m → Finset (Lit v)) (cstar : Fin m)
    (a : Fin v → ZMod 2) :
    instSat a Bk ↔ ((∀ c, c ≠ cstar → blockSat a (Bk c)) ∧ blockSat a (Bk cstar)) := by
  constructor
  · intro h
    exact ⟨fun c _ => h c, h cstar⟩
  · rintro ⟨h1, h2⟩ c
    by_cases hc : c = cstar
    · rw [hc]
      exact h2
    · exact h1 c hc

/-! ### The F = Z reduction -/

/-- **THE `F = Z` REDUCTION (proved)**: the satisfying count plus the all-false count equals
the non-target count — additive, so the parity bookkeeping is subtraction-free. -/
theorem count_split (Bk : Fin m → Finset (Lit v)) (cstar : Fin m) :
    (Finset.univ.filter (fun a => instSat a Bk)).card
      + (Finset.univ.filter (fun a =>
          (∀ c, c ≠ cstar → blockSat a (Bk c))
          ∧ ∀ ℓ ∈ Bk cstar, ¬ litHolds a ℓ)).card
    = (Finset.univ.filter (fun a => ∀ c, c ≠ cstar → blockSat a (Bk c))).card := by
  classical
  have hcover := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      ∀ c, c ≠ cstar → blockSat a (Bk c)))
    (p := fun a => blockSat a (Bk cstar))
  rw [Finset.filter_filter, Finset.filter_filter] at hcover
  have h1 : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      (∀ c, c ≠ cstar → blockSat a (Bk c)) ∧ blockSat a (Bk cstar))
      = Finset.univ.filter (fun a => instSat a Bk) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (instSat_split Bk cstar a).symm
  have h2 : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      (∀ c, c ≠ cstar → blockSat a (Bk c)) ∧ ¬ blockSat a (Bk cstar))
      = Finset.univ.filter (fun a =>
      (∀ c, c ≠ cstar → blockSat a (Bk c)) ∧ ∀ ℓ ∈ Bk cstar, ¬ litHolds a ℓ) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_right (fun _ => not_blockSat_iff)
  rw [h1, h2] at hcover
  exact hcover

/-! ### The detection theorem -/

set_option maxHeartbeats 800000 in
/-- **THE PARITY DETECTION (proved)**: if the non-target count is even and the all-false
predicate carries exactly one last free direction split by the target functional, the family
flips from `false` to `true` when the target literal is added — for BOTH values `b`. -/
theorem parity_detect (Bk Bk' : Fin m → Finset (Lit v)) (cstar : Fin m)
    (w a₀ l : Fin v → ZMod 2) (b : ZMod 2)
    (hlw : dotp l w = 1)
    (hBt : Bk' cstar = insert (l, b) (Bk cstar))
    (hBr : ∀ c, c ≠ cstar → Bk' c = Bk c)
    (hsol : ∀ a, ((∀ c, c ≠ cstar → blockSat a (Bk c))
        ∧ ∀ ℓ ∈ Bk cstar, ¬ litHolds a ℓ) ↔ (a = a₀ ∨ a = a₀ + w))
    (heven : (Finset.univ.filter (fun a : Fin v → ZMod 2 =>
        ∀ c, c ≠ cstar → blockSat a (Bk c))).card % 2 = 0) :
    parityFamily Bk = false ∧ parityFamily Bk' = true := by
  classical
  have hflip := parity_flip (fun a : Fin v → ZMod 2 =>
      (∀ c, c ≠ cstar → blockSat a (Bk c)) ∧ ∀ ℓ ∈ Bk cstar, ¬ litHolds a ℓ)
    w a₀ hsol l hlw (b + 1)
  obtain ⟨hP_even, hPl_odd⟩ := hflip
  have hsplit := count_split Bk cstar
  have hsplit' := count_split Bk' cstar
  -- the non-target counts agree
  have hntEq : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      ∀ c, c ≠ cstar → blockSat a (Bk' c))
      = Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      ∀ c, c ≠ cstar → blockSat a (Bk c)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h c hc
      rw [← hBr c hc]
      exact h c hc
    · intro h c hc
      rw [hBr c hc]
      exact h c hc
  -- the primed all-false predicate is P ∧ (target functional at value b+1)
  have hnotlit : ∀ a : Fin v → ZMod 2, (¬ litHolds a (l, b)) ↔ dotp l a = b + 1 := by
    intro a
    show ¬ (dotp l a = b) ↔ dotp l a = b + 1
    have hd : ∀ x y : ZMod 2, ¬ x = y ↔ x = y + 1 := by decide
    exact hd _ _
  have hP'Eq : Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      (∀ c, c ≠ cstar → blockSat a (Bk' c))
      ∧ ∀ ℓ ∈ Bk' cstar, ¬ litHolds a ℓ)
      = Finset.univ.filter (fun a : Fin v → ZMod 2 =>
      ((∀ c, c ≠ cstar → blockSat a (Bk c))
        ∧ ∀ ℓ ∈ Bk cstar, ¬ litHolds a ℓ)
      ∧ dotp l a = b + 1) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hnt, hall⟩
      have hnt2 : ∀ c, c ≠ cstar → blockSat a (Bk c) := by
        intro c hc
        rw [← hBr c hc]
        exact hnt c hc
      have htarget : ¬ litHolds a (l, b) := by
        apply hall
        rw [hBt]
        exact Finset.mem_insert_self _ _
      have hrest : ∀ ℓ ∈ Bk cstar, ¬ litHolds a ℓ := by
        intro ℓ hℓ
        apply hall
        rw [hBt]
        exact Finset.mem_insert_of_mem hℓ
      exact ⟨⟨hnt2, hrest⟩, (hnotlit a).mp htarget⟩
    · rintro ⟨⟨hnt, hrest⟩, hval⟩
      refine ⟨?_, ?_⟩
      · intro c hc
        rw [hBr c hc]
        exact hnt c hc
      · intro ℓ hℓ
        rw [hBt] at hℓ
        rcases Finset.mem_insert.mp hℓ with h | h
        · rw [h]
          exact (hnotlit a).mpr hval
        · exact hrest ℓ h
  rw [hntEq, hP'Eq] at hsplit'
  constructor
  · show decide _ = false
    rw [decide_eq_false_iff_not]
    omega
  · show decide _ = true
    rw [decide_eq_true_eq]
    omega

/-- The detection theorem, distinctness form: the two instances get DIFFERENT family
values. -/
theorem parity_detect_ne (Bk Bk' : Fin m → Finset (Lit v)) (cstar : Fin m)
    (w a₀ l : Fin v → ZMod 2) (b : ZMod 2)
    (hlw : dotp l w = 1)
    (hBt : Bk' cstar = insert (l, b) (Bk cstar))
    (hBr : ∀ c, c ≠ cstar → Bk' c = Bk c)
    (hsol : ∀ a, ((∀ c, c ≠ cstar → blockSat a (Bk c))
        ∧ ∀ ℓ ∈ Bk cstar, ¬ litHolds a ℓ) ↔ (a = a₀ ∨ a = a₀ + w))
    (heven : (Finset.univ.filter (fun a : Fin v → ZMod 2 =>
        ∀ c, c ≠ cstar → blockSat a (Bk c))).card % 2 = 0) :
    parityFamily Bk ≠ parityFamily Bk' := by
  obtain ⟨h1, h2⟩ := parity_detect Bk Bk' cstar w a₀ l b hlw hBt hBr hsol heven
  rw [h1, h2]
  exact Bool.false_ne_true

end PallLean.Paper93.DeepMath.PathB.NFrameParityEval

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityEval.count_split
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityEval.parity_detect
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityEval.parity_detect_ne
