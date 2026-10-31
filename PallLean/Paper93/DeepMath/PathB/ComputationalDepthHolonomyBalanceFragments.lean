import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolonomyCorrelationEngine

/-!
# Balance for restricted predictors — the first real test of the correlation engine

The engine (`…HolonomyCorrelationEngine`) proved the **seed**: a class‑constant predictor that is *balanced on
each of its classes* against the target has no correlation advantage (`2 · agreement ≤ #inputs`).  The open input
was **balance‑per‑class**.  This file *discharges balance* for restricted predictors against the genuine
holonomy/parity target, then combines with the seed.

## The mechanism — a missed parity variable

The holonomy observable is an `F₂` linear functional (the cycle's charge parity); we take the target
`fParity D x = ⊕_{i ∈ D} x i`, the parity over a holonomy support `D`.  The decisive structural fact:

> If a predictor `π` **factors through a read set `seen`** (it never inspects variables outside `seen`) and the
> parity support `D` contains a variable `v ∉ seen`, then `fParity D` is **exactly balanced inside every class of
> `π`**.

The proof is a fixed‑point‑free sign‑reversing involution: flipping the *unread* coordinate `v` (`flipAt v`)
preserves every predictor class (`π` cannot see the flip) yet toggles the parity (`v ∈ D`).  An involution on a
finite class that swaps `f = true` with `f = false` forces equal counts — balance.  This is `NP`‑independent,
elementary, and clean.

## What is proved (clean axioms, no `sorry`)

* `balanced_per_class_of_involution` — **the abstract balance engine**: a class‑preserving, target‑flipping
  involution forces per‑class balance.
* `parityCharge_flipAt_mem`, `fParity_flipAt_mem` — flipping a variable in the parity support toggles the target.
* `factorsThrough_flipAt` — a predictor that ignores `v` is invariant under `flipAt v`.
* `parity_balanced_of_missed_var`, `parity_balanced_of_card_gap` — **balance from a missed parity variable** (the
  latter supplying the missed variable by pigeonhole from `#read set < #parity support`).
* `restricted_fragment_low_correlation` — **balance + the seed ⇒ `2 · agreement ≤ #inputs`**: a predictor that
  reads fewer variables than the holonomy parity spans has *no correlation advantage* against it.
* `logGate_predictor_classes_balanced`, `readOnce_predictor_classes_balanced`,
  `boundedOverlap_predictor_classes_balanced` — the three named fragments, each establishing the read‑set bound
  from its own gate structure (gate‑count × fan‑in; disjoint supports; direct read‑set bound).

## The honest finding

At the *rank* level the three fragments were genuinely different (their incidence structure drove distinct
`q^{·}` bounds).  At the *correlation* level they **collapse to one condition**: does the predictor's read set miss
a variable the holonomy parity depends on?  Read‑once and bounded‑overlap give no smaller read set than plain
gate‑count × fan‑in for this purpose — the overlap parameter that mattered for rank is *irrelevant* to balance.
This is a real structural observation, not a gap.

## Scope — what stays open

This bites *restricted* predictors (read set provably smaller than the parity support).  A general poly‑size ACC⁰
circuit reads *all* `n` variables, so no single unread coordinate exists — balance via a fixed coordinate fails,
and one needs an *approximate* low‑dimensional predictor.  That is the named open bridge
`ACC0ApproximatesByLowRankPredictors` (below): ACC⁰ ≈ a coarse holonomy predictor up to small error.  Combined
with `restricted_fragment_low_correlation` and `acc0_williams_cashout` it would give `NP ⊄ ACC⁰` — and is itself
`NP ⊄ ACC⁰`‑strength, under the PRF‑free naturalness ceiling.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments

open PallLean.Paper93.DeepMath.PathB.HolonomyCorrelationEngine

variable {ι : Type*} {n : ℕ}

/-! ## The abstract balance engine: a sign‑reversing involution forces per‑class balance -/

/-- **Per‑class balance from a class‑preserving, target‑flipping involution (proved).**  If `τ` is an involution
on `Inputs` that fixes every predictor class (`π ∘ τ = π`) and toggles the target (`f ∘ τ = !f`), then inside each
class the `f = true` and `f = false` counts are equal: `τ` is a fixed‑point‑free bijection swapping the two
halves. -/
theorem balanced_per_class_of_involution {C : Type*} [DecidableEq C]
    (Inputs : Finset ι) (π : ι → C) (f : ι → Bool) (τ : ι → ι)
    (hmem : ∀ x ∈ Inputs, τ x ∈ Inputs)
    (hinv : ∀ x ∈ Inputs, τ (τ x) = x)
    (hpi : ∀ x ∈ Inputs, π (τ x) = π x)
    (hflip : ∀ x ∈ Inputs, f (τ x) = !(f x)) :
    ∀ c ∈ Inputs.image π,
      ((Inputs.filter (fun x => π x = c)).filter (fun x => f x = true)).card
        = ((Inputs.filter (fun x => π x = c)).filter (fun x => f x = false)).card := by
  intro c _
  refine Finset.card_nbij' τ τ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    obtain ⟨⟨haI, hac⟩, haf⟩ := ha
    refine ⟨⟨hmem a haI, ?_⟩, ?_⟩
    · rw [hpi a haI, hac]
    · rw [hflip a haI, haf]; rfl
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    obtain ⟨⟨haI, hac⟩, haf⟩ := ha
    refine ⟨⟨hmem a haI, ?_⟩, ?_⟩
    · rw [hpi a haI, hac]
    · rw [hflip a haI, haf]; rfl
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha
    exact hinv a ha.1.1
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha
    exact hinv a ha.1.1

/-! ## Flipping an unread coordinate: the involution -/

/-- Flip the value of input coordinate `v`. -/
def flipAt (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := Function.update x v (!(x v))

theorem flipAt_apply (v : Fin n) (x : Fin n → Bool) (i : Fin n) :
    flipAt v x i = if i = v then !(x v) else x i := by
  simp only [flipAt, Function.update_apply]

theorem flipAt_involutive (v : Fin n) (x : Fin n → Bool) : flipAt v (flipAt v x) = x := by
  funext i
  by_cases h : i = v
  · subst h
    rw [flipAt_apply, if_pos rfl, flipAt_apply, if_pos rfl, Bool.not_not]
  · rw [flipAt_apply, if_neg h, flipAt_apply, if_neg h]

/-! ## A predictor that ignores `v` is invariant under `flipAt v` -/

/-- A predictor `π` **factors through its read set `seen`**: it depends on the input only through coordinates in
`seen`. -/
def factorsThrough {C : Type*} (seen : Finset (Fin n)) (π : (Fin n → Bool) → C) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i ∈ seen, x i = y i) → π x = π y

/-- **A predictor that does not read `v` is invariant under flipping `v` (proved).** -/
theorem factorsThrough_flipAt {C : Type*} {seen : Finset (Fin n)} {π : (Fin n → Bool) → C}
    (hf : factorsThrough seen π) {v : Fin n} (hv : v ∉ seen) (x : Fin n → Bool) :
    π (flipAt v x) = π x := by
  apply hf
  intro i hi
  have hiv : i ≠ v := by rintro rfl; exact hv hi
  rw [flipAt_apply, if_neg hiv]

/-! ## The genuine holonomy/parity target, and its toggle under flips -/

/-- The `F₂` holonomy charge of an input over a support `D`: the parity `⊕_{i ∈ D} x i`. -/
def parityCharge (D : Finset (Fin n)) (x : Fin n → Bool) : ZMod 2 :=
  ∑ i ∈ D, (if x i then (1 : ZMod 2) else 0)

/-- The Boolean holonomy/parity target. -/
def fParity (D : Finset (Fin n)) (x : Fin n → Bool) : Bool := decide (parityCharge D x = 1)

/-- **Flipping a variable in the parity support toggles the charge by `1` (proved).** -/
theorem parityCharge_flipAt_mem (D : Finset (Fin n)) {v : Fin n} (hv : v ∈ D) (x : Fin n → Bool) :
    parityCharge D (flipAt v x) = parityCharge D x + 1 := by
  unfold parityCharge
  rw [← Finset.add_sum_erase D (fun i => if flipAt v x i then (1 : ZMod 2) else 0) hv,
      ← Finset.add_sum_erase D (fun i => if x i then (1 : ZMod 2) else 0) hv]
  have herase : ∑ i ∈ D.erase v, (if flipAt v x i then (1 : ZMod 2) else 0)
      = ∑ i ∈ D.erase v, (if x i then (1 : ZMod 2) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiv : i ≠ v := Finset.ne_of_mem_erase hi
    rw [flipAt_apply, if_neg hiv]
  have hval : (if flipAt v x v then (1 : ZMod 2) else 0) = (if x v then (1 : ZMod 2) else 0) + 1 := by
    rw [flipAt_apply, if_pos rfl]
    cases hxv : x v <;> decide
  rw [herase, hval]
  ring

theorem zmod2_toggle : ∀ a : ZMod 2, decide (a + 1 = 1) = !decide (a = 1) := by decide

/-- **Flipping a variable in the parity support toggles the Boolean target (proved).** -/
theorem fParity_flipAt_mem (D : Finset (Fin n)) {v : Fin n} (hv : v ∈ D) (x : Fin n → Bool) :
    fParity D (flipAt v x) = !(fParity D x) := by
  unfold fParity
  rw [parityCharge_flipAt_mem D hv x]
  exact zmod2_toggle (parityCharge D x)

/-! ## Balance for restricted predictors against the holonomy parity -/

/-- **Balance from a missed parity variable (proved).**  If `π` factors through a read set `seen` that omits some
`v ∈ D`, then the holonomy parity `fParity D` is exactly balanced in each class of `π`. -/
theorem parity_balanced_of_missed_var {C : Type*} [DecidableEq C]
    (π : (Fin n → Bool) → C) (D seen : Finset (Fin n))
    (hπ : factorsThrough seen π) {v : Fin n} (hvD : v ∈ D) (hvS : v ∉ seen) :
    ∀ c ∈ (Finset.univ : Finset (Fin n → Bool)).image π,
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => π x = c)).filter
          (fun x => fParity D x = true)).card
        = (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => π x = c)).filter
            (fun x => fParity D x = false)).card :=
  balanced_per_class_of_involution Finset.univ π (fParity D) (flipAt v)
    (fun _ _ => Finset.mem_univ _)
    (fun x _ => flipAt_involutive v x)
    (fun x _ => factorsThrough_flipAt hπ hvS x)
    (fun x _ => fParity_flipAt_mem D hvD x)

/-- A read set strictly smaller than the parity support omits a parity variable (pigeonhole). -/
theorem exists_missed_of_card_lt (D seen : Finset (Fin n)) (h : seen.card < D.card) :
    ∃ v ∈ D, v ∉ seen := by
  by_contra hc
  push_neg at hc
  exact absurd (Finset.card_le_card (fun v hv => hc v hv)) (Nat.not_le.mpr h)

/-- **Balance from a read set smaller than the parity support (proved).** -/
theorem parity_balanced_of_card_gap {C : Type*} [DecidableEq C]
    (π : (Fin n → Bool) → C) (D seen : Finset (Fin n))
    (hπ : factorsThrough seen π) (hcard : seen.card < D.card) :
    ∀ c ∈ (Finset.univ : Finset (Fin n → Bool)).image π,
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => π x = c)).filter
          (fun x => fParity D x = true)).card
        = (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => π x = c)).filter
            (fun x => fParity D x = false)).card := by
  obtain ⟨v, hvD, hvS⟩ := exists_missed_of_card_lt D seen hcard
  exact parity_balanced_of_missed_var π D seen hπ hvD hvS

/-! ## Combine with the seed: restricted predictors have no correlation advantage -/

/-- **The first real test of the engine (proved): a predictor reading fewer variables than the holonomy parity
spans has no correlation advantage against it.**  Balance (`parity_balanced_of_card_gap`) feeds the engine seed
(`low_rank_predictor_low_correlation_with_full_holonomy`): `2 · agreement ≤ #inputs`. -/
theorem restricted_fragment_low_correlation {C : Type*} [DecidableEq C]
    (π : (Fin n → Bool) → C) (g : C → Bool) (D seen : Finset (Fin n))
    (hπ : factorsThrough seen π) (hcard : seen.card < D.card) :
    2 * ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => g (π x) = fParity D x)).card
      ≤ (Finset.univ : Finset (Fin n → Bool)).card :=
  low_rank_predictor_low_correlation_with_full_holonomy
    Finset.univ π g (fParity D) (parity_balanced_of_card_gap π D seen hπ hcard)

/-! ## The three named fragments — each establishing the read‑set bound from its gate structure -/

/-- **Bounded‑overlap fragment (proved): direct read‑set bound.**  A predictor reading only the variables of a
gate set whose total read set is smaller than the holonomy parity is balanced per class.  (At the correlation
level the *overlap* parameter — decisive for the rank ladder — is irrelevant; only the read‑set size matters.) -/
theorem boundedOverlap_predictor_classes_balanced {C G : Type*} [DecidableEq C] [DecidableEq G]
    (π : (Fin n → Bool) → C) (D : Finset (Fin n)) (gates : Finset G) (supp : G → Finset (Fin n))
    (hπ : factorsThrough (gates.biUnion supp) π)
    (hread : (gates.biUnion supp).card < D.card) :
    ∀ c ∈ (Finset.univ : Finset (Fin n → Bool)).image π,
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => π x = c)).filter
          (fun x => fParity D x = true)).card
        = (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => π x = c)).filter
            (fun x => fParity D x = false)).card :=
  parity_balanced_of_card_gap π D (gates.biUnion supp) hπ hread

/-- **Log‑gate fragment (proved): read‑set bound from gate count × fan‑in.**  A predictor built from `≤ L` gates
of fan‑in `≤ F` reads `≤ L · F` variables; when the holonomy parity spans more, it is balanced per class. -/
theorem logGate_predictor_classes_balanced {C G : Type*} [DecidableEq C] [DecidableEq G]
    (π : (Fin n → Bool) → C) (D : Finset (Fin n)) (gates : Finset G) (supp : G → Finset (Fin n))
    (hπ : factorsThrough (gates.biUnion supp) π)
    (L F : ℕ) (hgates : gates.card ≤ L) (hfan : ∀ g ∈ gates, (supp g).card ≤ F)
    (hD : L * F < D.card) :
    ∀ c ∈ (Finset.univ : Finset (Fin n → Bool)).image π,
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => π x = c)).filter
          (fun x => fParity D x = true)).card
        = (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => π x = c)).filter
            (fun x => fParity D x = false)).card := by
  have hseen : (gates.biUnion supp).card < D.card := by
    have h1 : (gates.biUnion supp).card ≤ gates.card * F :=
      calc (gates.biUnion supp).card
          ≤ ∑ g ∈ gates, (supp g).card := Finset.card_biUnion_le
        _ ≤ ∑ _g ∈ gates, F := Finset.sum_le_sum hfan
        _ = gates.card * F := by rw [Finset.sum_const, smul_eq_mul]
    exact lt_of_le_of_lt (le_trans h1 (Nat.mul_le_mul hgates (le_refl F))) hD
  exact parity_balanced_of_card_gap π D (gates.biUnion supp) hπ hseen

/-- **Read‑once fragment (proved): read‑set bound from disjoint gate supports.**  When the gate supports are
pairwise disjoint (each variable read at most once), the read set has size `∑ |supp g|`; when that is smaller than
the holonomy parity support, the predictor is balanced per class. -/
theorem readOnce_predictor_classes_balanced {C G : Type*} [DecidableEq C] [DecidableEq G]
    (π : (Fin n → Bool) → C) (D : Finset (Fin n)) (gates : Finset G) (supp : G → Finset (Fin n))
    (hπ : factorsThrough (gates.biUnion supp) π)
    (hdisj : ∀ x ∈ gates, ∀ y ∈ gates, x ≠ y → Disjoint (supp x) (supp y))
    (hD : ∑ g ∈ gates, (supp g).card < D.card) :
    ∀ c ∈ (Finset.univ : Finset (Fin n → Bool)).image π,
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => π x = c)).filter
          (fun x => fParity D x = true)).card
        = (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => π x = c)).filter
            (fun x => fParity D x = false)).card := by
  have hseen : (gates.biUnion supp).card < D.card := by
    rw [Finset.card_biUnion hdisj]; exact hD
  exact parity_balanced_of_card_gap π D (gates.biUnion supp) hπ hseen

/-! ## The open bridge to general ACC⁰ (step 4), and the Williams cash‑out wiring (step 5) -/

/-- **(Named open bridge — `NP ⊄ ACC⁰`‑strength).**  A poly‑size ACC⁰ family is approximated, up to a `½ − ε`
agreement deficit, by a *low‑rank holonomy predictor* (one factoring through `o(#holonomy support)` read
variables / coarse statistics) on the hard instances.  Plugging such a predictor into
`restricted_fragment_low_correlation` (balance ⇒ no advantage) and `acc0_williams_cashout` would yield
`NP ⊄ ACC⁰`.  General ACC⁰ reads *all* variables, so this needs *approximate* low‑dimensionality, not a single
unread coordinate — exactly the content the elementary fragment route cannot supply. -/
def ACC0ApproximatesByLowRankPredictors
    (acc0Agreement : ℕ → ℕ) (lowRankAgreement : ℕ → ℕ) (deficit : ℕ → ℕ) : Prop :=
  ∀ n, acc0Agreement n ≤ lowRankAgreement n + deficit n

end PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments

#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments.balanced_per_class_of_involution
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments.fParity_flipAt_mem
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments.parity_balanced_of_card_gap
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments.restricted_fragment_low_correlation
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments.logGate_predictor_classes_balanced
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments.readOnce_predictor_classes_balanced
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments.boundedOverlap_predictor_classes_balanced
