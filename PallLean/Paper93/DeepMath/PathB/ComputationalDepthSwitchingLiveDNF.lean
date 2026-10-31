import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingActive
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad

/-!
# Håstad switching lemma — live-DNF normalization (the confound-breaking route, first brick)

The genuine path past the confound (per `STAR_ENCODING_SCOPE.md`): reduce a general `ρ` (which may
falsify terms) to its **live sub-DNF** — drop the `ρ`-falsified terms — converting the general case to
the already-proved `ρ`-falsifies-nothing (`hnf`) case.

The core invariance: `ρ`-falsified terms stay falsified along the replay path (falsification is
monotone), so `activeTerm` never selects them, so dropping them **does not change `activeTerm`**.
This brick proves that invariance, with the two reusable list tools it rests on.

## What is proved (clean axioms, no `sorry`)

* `find?_filter_eq` / `any_filter_eq` — dropping non-`p` elements (`p x → q x`) preserves
  `List.find? p` / `List.any p`.
* `liveCs` — the live sub-DNF `cs.filter (¬ termFalsified ρ)`; `liveCs_hnf` — `ρ` falsifies nothing in
  it (the `hnf` precondition, by construction).
* `termFalsified_not_termSat` — a falsified term is not satisfied.
* `activeTerm_liveCs` — **`activeTerm (liveCs ρ cs) σ = activeTerm cs σ`** whenever every
  `ρ`-falsified term of `cs` is still falsified at `σ` (which holds along the replay path).

## Honest scope

The `activeTerm` invariance under live-DNF restriction — the structural heart of reducing general `ρ`
to the `hnf` case.  Lifting it through the whole replay path/selected set, and combining with the
proved `hnf` decoder, is the remaining normalization assembly (next bricks); the probabilistic
switching lemma is separate.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- Dropping non-`p` elements preserves `find? p`. -/
theorem find?_filter_eq {α : Type*} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) → (l.filter q).find? p = l.find? p
  | [], _ => by simp
  | a :: t, h => by
    have ih := find?_filter_eq p q t (fun x hx => h x (List.mem_cons_of_mem a hx))
    by_cases hq : q a = true
    · rw [List.filter_cons_of_pos hq]
      by_cases hp : p a = true
      · rw [List.find?_cons_of_pos hp, List.find?_cons_of_pos hp]
      · rw [List.find?_cons_of_neg hp, List.find?_cons_of_neg hp, ih]
    · have hpa : ¬ p a = true := fun hp => hq (h a (by simp) hp)
      rw [List.filter_cons_of_neg hq, List.find?_cons_of_neg hpa, ih]

/-- Dropping non-`p` elements preserves `any p`. -/
theorem any_filter_eq {α : Type*} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) → (l.filter q).any p = l.any p
  | [], _ => by simp
  | a :: t, h => by
    have ih := any_filter_eq p q t (fun x hx => h x (List.mem_cons_of_mem a hx))
    by_cases hq : q a = true
    · rw [List.filter_cons_of_pos hq, List.any_cons, List.any_cons, ih]
    · have hpa : p a = false := by
        by_contra hp; rw [Bool.not_eq_false] at hp
        exact hq (h a (by simp) hp)
      rw [List.filter_cons_of_neg hq, List.any_cons, hpa, Bool.false_or, ih]

/-- The live sub-DNF: drop the `ρ`-falsified terms. -/
def liveCs (ρ : Restriction n) (cs : List (Clause n)) : List (Clause n) :=
  cs.filter (fun T => !termFalsified ρ T)

/-- **`ρ` falsifies nothing in the live sub-DNF** (the `hnf` precondition, by construction). -/
theorem liveCs_hnf (ρ : Restriction n) (cs : List (Clause n)) :
    ∀ T ∈ liveCs ρ cs, termFalsified ρ T = false := by
  intro T hT
  have := (List.mem_filter.mp hT).2
  simpa using this

/-- A falsified term is not satisfied. -/
theorem termFalsified_not_termSat {σ : Restriction n} {T : Clause n}
    (h : termFalsified σ T = true) : termSat σ T = false := by
  rw [termFalsified, List.any_eq_true] at h
  obtain ⟨ℓ, hℓ, hℓf⟩ := h
  rw [termSat, List.all_eq_false]
  exact ⟨ℓ, hℓ, by rw [litTrue_eq_false_of_litFalse hℓf]; simp⟩

/-- **`activeTerm` is invariant under live-DNF restriction.**  If every `ρ`-falsified term of `cs` is
still falsified at `σ` (true along the replay path), then dropping the `ρ`-falsified terms does not
change the active term. -/
theorem activeTerm_liveCs {ρ : Restriction n} {cs : List (Clause n)} {σ : Restriction n}
    (hmono : ∀ T ∈ cs, termFalsified ρ T = true → termFalsified σ T = true) :
    activeTerm (liveCs ρ cs) σ = activeTerm cs σ := by
  have hmono_contra : ∀ T ∈ cs, termFalsified σ T = false → termFalsified ρ T = false := by
    intro T hT hσ
    by_contra hρ
    rw [Bool.not_eq_false] at hρ
    rw [hmono T hT hρ] at hσ
    exact absurd hσ (by simp)
  have hany : anyTermSat (liveCs ρ cs) σ = anyTermSat cs σ := by
    rw [anyTermSat, anyTermSat, liveCs]
    refine any_filter_eq (termSat σ) (fun T => !termFalsified ρ T) cs (fun T hT hsat => ?_)
    have hσf : termFalsified σ T = false := by
      by_contra hσ; rw [Bool.not_eq_false] at hσ
      rw [termFalsified_not_termSat hσ] at hsat; exact absurd hsat (by simp)
    simp [hmono_contra T hT hσf]
  have hfind : (liveCs ρ cs).find?
        (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length))
      = cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length)) := by
    rw [liveCs]
    refine find?_filter_eq _ (fun T => !termFalsified ρ T) cs (fun T hT hpred => ?_)
    have hσf : termFalsified σ T = false := by
      rw [Bool.and_eq_true] at hpred
      simpa using hpred.1
    simp [hmono_contra T hT hσf]
  rw [activeTerm, activeTerm, hany, hfind]

/-!
**Live-DNF `activeTerm` invariance, proved.**  Dropping the `ρ`-falsified terms leaves `activeTerm`
unchanged (they stay falsified, never selected), and `ρ` falsifies nothing in the live sub-DNF.  This
is the structural heart of reducing general `ρ` to the `hnf` case.  Lifting through the full replay
path + selected set, and combining with the `hnf` decoder, is the remaining assembly; not faked.
AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.activeTerm_liveCs
