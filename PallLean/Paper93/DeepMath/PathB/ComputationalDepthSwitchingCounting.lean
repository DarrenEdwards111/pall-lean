import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Prod

/-!
# Counting scaffold for the switching lemma (Razborov-style encoding)

**STATUS: REAL COUNTING/INJECTION CORE.  THE DNF-DETERMINED LABEL BOUND IS THE GATE.**

The honest entry point to the probabilistic switching lemma is its
*counting/injection* form (Razborov): bound the number of "bad" restrictions by
encoding each one injectively as a restriction with *more* fixed coordinates
together with a small label, then count.  No probability spaces — everything is
finite and combinatorial.

This file proves the load-bearing, error-prone part of that argument — the
**injectivity** of the encoding `ρ ↦ (fix the chosen free coordinates, the chosen
set)` — for an *arbitrary* coordinate-selection rule `sel` with
`sel ρ ⊆ freeVars ρ`.  It then derives the cardinality bound

  `|Bad| ≤ |Short| · |sel '' Bad|`.

What is **not** here (the gate): the selection rule `sel` must be the *canonical
decision-tree path* of the DNF, and the label set `sel '' Bad` must be bounded by
`(O(w))^s` using the DNF's bottom width `w` and the path length `s`.  That DNF
analysis is the remaining hard content; this file supplies the counting reduction
it plugs into.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

variable {n : ℕ}

/-- A restriction: each coordinate is fixed to a Boolean or left free (`none`). -/
abbrev Restriction (n : ℕ) := Fin n → Option Bool

/-- The free (unset) coordinates of a restriction. -/
def freeVars (ρ : Restriction n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ρ i = none)

theorem mem_freeVars {ρ : Restriction n} {i : Fin n} : i ∈ freeVars ρ ↔ ρ i = none := by
  simp [freeVars]

/-- Number of free coordinates ("stars"). -/
def stars (ρ : Restriction n) : ℕ := (freeVars ρ).card

/-- Fix the coordinates in `S` to the values given by `a`, leaving the rest. -/
def fixOn (ρ : Restriction n) (S : Finset (Fin n)) (a : Fin n → Bool) : Restriction n :=
  fun i => if i ∈ S then some (a i) else ρ i

/-- Re-free the coordinates in `S`. -/
def freeOn (ρ : Restriction n) (S : Finset (Fin n)) : Restriction n :=
  fun i => if i ∈ S then none else ρ i

/-- **Recovery.**  If `S` was free in `ρ`, re-freeing `S` after fixing it returns
`ρ` exactly.  This is the inverse that makes the encoding injective. -/
theorem freeOn_fixOn (ρ : Restriction n) (S : Finset (Fin n)) (a : Fin n → Bool)
    (hS : S ⊆ freeVars ρ) : freeOn (fixOn ρ S a) S = ρ := by
  funext i
  unfold freeOn fixOn
  by_cases hi : i ∈ S
  · simp only [hi, if_true]
    exact (mem_freeVars.mp (hS hi)).symm
  · simp only [hi, if_false]

/-- **Injectivity of the encoding.**  For any selection rule `sel` choosing free
coordinates (`sel ρ ⊆ freeVars ρ`), the map `ρ ↦ (fixOn ρ (sel ρ) (D ρ), sel ρ)`
is injective on `Bad`: `ρ` is recovered as `freeOn (encoded) (sel ρ)`. -/
theorem enc_injOn (sel : Restriction n → Finset (Fin n)) (D : Restriction n → (Fin n → Bool))
    {Bad : Finset (Restriction n)} (hsel : ∀ ρ ∈ Bad, sel ρ ⊆ freeVars ρ) :
    Set.InjOn (fun ρ => (fixOn ρ (sel ρ) (D ρ), sel ρ)) ↑Bad := by
  intro ρ1 h1 ρ2 h2 heq
  have hb1 := Finset.mem_coe.mp h1
  have hb2 := Finset.mem_coe.mp h2
  have hf := congrArg Prod.fst heq
  have hs := congrArg Prod.snd heq
  simp only at hf hs
  calc ρ1 = freeOn (fixOn ρ1 (sel ρ1) (D ρ1)) (sel ρ1) :=
        (freeOn_fixOn ρ1 (sel ρ1) (D ρ1) (hsel ρ1 hb1)).symm
    _ = freeOn (fixOn ρ2 (sel ρ2) (D ρ2)) (sel ρ2) := by rw [hf, hs]
    _ = ρ2 := freeOn_fixOn ρ2 (sel ρ2) (D ρ2) (hsel ρ2 hb2)

/-- **Counting bound from the encoding.**  The number of bad restrictions is at most
the number of (denser) encoded restrictions times the number of distinct labels.
The savings of the switching lemma come from bounding `|Bad.image sel|` via the DNF
width (the open gate); the injection that makes this counting valid is proved here. -/
theorem card_bad_le (sel : Restriction n → Finset (Fin n)) (D : Restriction n → (Fin n → Bool))
    {Bad : Finset (Restriction n)} (Short : Finset (Restriction n))
    (hsel : ∀ ρ ∈ Bad, sel ρ ⊆ freeVars ρ)
    (hmem : ∀ ρ ∈ Bad, fixOn ρ (sel ρ) (D ρ) ∈ Short) :
    Bad.card ≤ Short.card * (Bad.image sel).card := by
  have hsub : ∀ ρ ∈ Bad, (fun ρ => (fixOn ρ (sel ρ) (D ρ), sel ρ)) ρ
      ∈ Short ×ˢ (Bad.image sel) := by
    intro ρ hρ
    exact Finset.mem_product.mpr ⟨hmem ρ hρ, Finset.mem_image_of_mem sel hρ⟩
  calc Bad.card
      ≤ (Short ×ˢ (Bad.image sel)).card :=
        Finset.card_le_card_of_injOn _ hsub (enc_injOn sel D hsel)
    _ = Short.card * (Bad.image sel).card := Finset.card_product _ _

/-- Specialised bound: if the label set has size `≤ ℓ` and the encoded
restrictions lie in `Short`, then `|Bad| ≤ |Short| · ℓ`.  Discharging
`hlabel` with `ℓ = (O(w))^s` from the DNF analysis is the switching lemma. -/
theorem card_bad_le_of_label_bound (sel : Restriction n → Finset (Fin n))
    (D : Restriction n → (Fin n → Bool)) {Bad : Finset (Restriction n)}
    (Short : Finset (Restriction n)) {ℓ : ℕ}
    (hsel : ∀ ρ ∈ Bad, sel ρ ⊆ freeVars ρ)
    (hmem : ∀ ρ ∈ Bad, fixOn ρ (sel ρ) (D ρ) ∈ Short)
    (hlabel : (Bad.image sel).card ≤ ℓ) :
    Bad.card ≤ Short.card * ℓ :=
  le_trans (card_bad_le sel D Short hsel hmem) (Nat.mul_le_mul_left _ hlabel)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_fixOn
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.enc_injOn
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_bad_le
