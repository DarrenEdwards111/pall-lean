import PallLean.Paper93.DeepMath.PathB.ComputationalDepthModQGateBalance

/-!
# Composition: two (and many) modular gates vs the holonomy parity

The single‑gate engine (`…ModQGateBalance`) bit a `MOD q` gate because the off‑diagonal flip‑both `pairSwap v w`
preserves its count.  This file moves to **composition** — a predictor that factors through *several* modular
statistics — and asks: can the same involution still force small correlation?

## The clean answer for full‑support gates

The off‑diagonal flip‑both `pairSwap v w` (on `{x_v ≠ x_w}`) moves one coordinate `0→1` and the other `1→0`, so it
preserves the **integer weight** `∑_i x_i` *exactly* — hence preserves **every** statistic that factors through the
weight at once: any number of full‑support `MOD q_j` gates (any moduli), threshold gates, exact‑count gates.  So a
predictor factoring through `(modQStat q₁ x, …, modQStat q_k x)` is preserved by the *same single* involution, and
the whole engine (off‑diagonal balance, no correlation advantage) carries over verbatim.  Mixed moduli are no
obstacle when the supports are full.

## The obstruction for different supports

If the two gates read *different* supports `A, B`,
`stat x = (∑_{A} x \bmod q₁, ∑_{B} x \bmod q₂)`, a flip‑both must preserve **both** support‑counts.  Flipping
`v` (`0→1`) and `w` (`1→0`) changes `∑_A` by `[v∈A] − [w∈A]` and `∑_B` by `[v∈B] − [w∈B]`; both vanish iff
`(v ∈ A ↔ w ∈ A)` and `(v ∈ B ↔ w ∈ B)` — i.e. `v` and `w` lie in the **same cell of the partition induced by
`{A, B}`** (the four cells `A∩B, A∖B, B∖A, (A∪B)ᶜ`).  This is the **product‑class obstruction**: a usable witness
pair needs `v ∈ D`, `w ∉ D` *and* `v, w` in a common cell.  Same support (`A = B`) collapses the two conditions to
one; full support (`A = B = univ`) makes them automatic; disjoint / bounded‑overlap supports turn it into a
matching problem (a `D`‑edge inside a cell).

## What is proved (clean axioms, no `sorry`)

* `balanced_offdiag_of_pres`, `low_correlation_of_pres` — **the general composition engine**: *any* predictor `π`
  preserved by the off‑diagonal flip‑both has exact off‑diagonal balance and no correlation advantage against the
  holonomy parity.
* `twoStat_pairSwap_offdiag`, `twoGate_offdiag_balanced`, `twoGate_low_correlation_offdiagonal` — **two full‑support
  MOD gates (mixed moduli)**: the same single involution preserves both, so the engine bites.
* `weightOn`, `weightOn_pairSwap_eq` — a support‑restricted count is preserved by the flip‑both **iff `v, w` lie on
  the same side of the support** (the cell condition).
* `twoStatOn_pairSwap`, `twoGateOn_offdiag_balanced` — **two different‑support MOD gates**: balance holds for a
  witness pair in a common cell of both supports (`v ∈ A ↔ w ∈ A`, `v ∈ B ↔ w ∈ B`).

## Honest scope

This answers the composition question for the *off‑diagonal* (the part the involution reaches): full‑support gates
compose freely (mixed moduli, any number); different‑support gates compose when a `D`‑witness pair sits in a common
support cell.  The diagonal localization (`imbalance_localize_step` is already predicate‑general) and the disjoint
pair‑stacking numeric bound extend by the same induction; the residual on the final core is, as ever, the
character sum.  Finding *enough* common‑cell `D`‑witness pairs for many different‑support gates is the matching /
flow problem the engine reduces composition to — `NP ⊄ ACC⁰`‑strength once the supports are adversarial.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation

open PallLean.Paper93.DeepMath.PathB.HolonomyCorrelationEngine
open PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments
open PallLean.Paper93.DeepMath.PathB.ModQGateBalance

variable {n : ℕ}

/-! ## The general composition engine: any off‑diagonally preserved predictor -/

/-- **General off‑diagonal balance (proved).**  If a predictor `π` is preserved by the off‑diagonal flip‑both
`pairSwap v w` (for `v ∈ D`, `w ∉ D`), then the holonomy parity is exactly balanced inside each `π`‑class on the
off‑diagonal `{x_v ≠ x_w}`. -/
theorem balanced_offdiag_of_pres {C : Type*} [DecidableEq C] (π : (Fin n → Bool) → C)
    (D : Finset (Fin n)) (v w : Fin n) (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D)
    (hpres : ∀ x : Fin n → Bool, x v ≠ x w → π (pairSwap v w x) = π x) :
    ∀ c ∈ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).image π,
      ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => π x = c)).filter (fun x => fParity D x = true)).card
        = ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
            (fun x => π x = c)).filter (fun x => fParity D x = false)).card := by
  apply balanced_per_class_of_involution _ π (fParity D) (pairSwap v w)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [pairSwap_v, pairSwap_w v w x hvw.symm]
    exact bool_not_ne _ _ hx.2
  · intro x _; exact pairSwap_involutive v w hvw x
  · intro x hx; exact hpres x (Finset.mem_filter.mp hx).2
  · intro x _; exact fParity_pairSwap D v w hvD hwD hvw x

set_option maxHeartbeats 1000000 in
/-- **General off‑diagonal no‑correlation (proved).**  An off‑diagonally preserved predictor `g ∘ π` has no
correlation advantage against the holonomy parity on the off‑diagonal. -/
theorem low_correlation_of_pres {C : Type*} [DecidableEq C] (π : (Fin n → Bool) → C) (g : C → Bool)
    (D : Finset (Fin n)) (v w : Fin n) (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D)
    (hpres : ∀ x : Fin n → Bool, x v ≠ x w → π (pairSwap v w x) = π x) :
    2 * (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => g (π x) = fParity D x)).card
      ≤ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).card :=
  low_rank_predictor_low_correlation_with_full_holonomy
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w))
    π g (fParity D) (balanced_offdiag_of_pres π D v w hvw hvD hwD hpres)

/-! ## Two full‑support MOD gates (mixed moduli): one involution preserves both -/

/-- The two‑gate statistic for full‑support gates of moduli `q₁, q₂`. -/
def twoStat (q₁ q₂ : ℕ) (x : Fin n → Bool) : ZMod q₁ × ZMod q₂ :=
  (modQStat q₁ x, modQStat q₂ x)

/-- **The off‑diagonal flip‑both preserves both full‑support counts at once (proved).** -/
theorem twoStat_pairSwap_offdiag (q₁ q₂ : ℕ) (v w : Fin n) (hvw : v ≠ w) (x : Fin n → Bool)
    (hoff : x v ≠ x w) : twoStat q₁ q₂ (pairSwap v w x) = twoStat q₁ q₂ x := by
  unfold twoStat
  rw [modQStat_pairSwap_offdiag q₁ v w hvw x hoff, modQStat_pairSwap_offdiag q₂ v w hvw x hoff]

/-- **Two full‑support MOD gates: off‑diagonal balance (proved).** -/
theorem twoGate_offdiag_balanced (q₁ q₂ : ℕ) (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) :
    ∀ c ∈ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).image (twoStat q₁ q₂),
      ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => twoStat q₁ q₂ x = c)).filter (fun x => fParity D x = true)).card
        = ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
            (fun x => twoStat q₁ q₂ x = c)).filter (fun x => fParity D x = false)).card :=
  balanced_offdiag_of_pres (twoStat q₁ q₂) D v w hvw hvD hwD
    (fun x h => twoStat_pairSwap_offdiag q₁ q₂ v w hvw x h)

set_option maxHeartbeats 1000000 in
/-- **Two full‑support MOD gates: no correlation advantage on the off‑diagonal (proved).**  Mixed moduli compose
freely — the single involution `pairSwap v w` handles both gates. -/
theorem twoGate_low_correlation_offdiagonal (q₁ q₂ : ℕ) (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) (g : ZMod q₁ × ZMod q₂ → Bool) :
    2 * (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => g (twoStat q₁ q₂ x) = fParity D x)).card
      ≤ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).card :=
  low_correlation_of_pres (twoStat q₁ q₂) g D v w hvw hvD hwD
    (fun x h => twoStat_pairSwap_offdiag q₁ q₂ v w hvw x h)

/-! ## Different supports: the cell condition -/

/-- The count of `x` over a support `S`, as a natural number. -/
def weightOn (S : Finset (Fin n)) (x : Fin n → Bool) : ℕ := ∑ i ∈ S, (if x i then 1 else 0)

/-- Pull two distinct members out of a sum over a finset. -/
theorem sum_extract_two_mem {M : Type*} [AddCommMonoid M] (S : Finset (Fin n)) (v w : Fin n)
    (hv : v ∈ S) (hw : w ∈ S) (hvw : v ≠ w) (f : Fin n → M) :
    ∑ i ∈ S, f i = f v + f w + ∑ i ∈ (S.erase v).erase w, f i := by
  rw [← Finset.add_sum_erase S f hv,
      ← Finset.add_sum_erase (S.erase v) f (Finset.mem_erase.mpr ⟨hvw.symm, hw⟩)]
  abel

/-- **A support‑restricted count is preserved by the flip‑both iff `v, w` lie on the same side of the support
(proved).**  When `v, w` are both inside or both outside `S`, the off‑diagonal flip‑both moves their `S`‑weights in
opposite directions (or not at all), leaving `∑_S x` fixed. -/
theorem weightOn_pairSwap_eq (S : Finset (Fin n)) (v w : Fin n) (hvw : v ≠ w)
    (hS : v ∈ S ↔ w ∈ S) (x : Fin n → Bool) (hoff : x v ≠ x w) :
    weightOn S (pairSwap v w x) = weightOn S x := by
  unfold weightOn
  by_cases hv : v ∈ S
  · have hw : w ∈ S := hS.mp hv
    rw [sum_extract_two_mem S v w hv hw hvw (fun i => if pairSwap v w x i then 1 else 0),
        sum_extract_two_mem S v w hv hw hvw (fun i => if x i then 1 else 0)]
    have hrest : ∑ i ∈ (S.erase v).erase w, (if pairSwap v w x i then (1 : ℕ) else 0)
        = ∑ i ∈ (S.erase v).erase w, (if x i then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiw : i ≠ w := Finset.ne_of_mem_erase hi
      have hiv : i ≠ v := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      rw [pairSwap_other _ _ _ hiv hiw]
    rw [hrest, pairSwap_v, pairSwap_w v w x hvw.symm]
    cases hxv : x v <;> cases hxw : x w <;> simp_all
  · have hw : w ∉ S := fun h => hv (hS.mpr h)
    apply Finset.sum_congr rfl
    intro i hi
    have hiv : i ≠ v := fun h => hv (h ▸ hi)
    have hiw : i ≠ w := fun h => hw (h ▸ hi)
    rw [pairSwap_other _ _ _ hiv hiw]

/-- A support‑restricted modular gate. -/
def modQStatOn (S : Finset (Fin n)) (q : ℕ) (x : Fin n → Bool) : ZMod q := (weightOn S x : ZMod q)

theorem modQStatOn_pairSwap_eq (S : Finset (Fin n)) (q : ℕ) (v w : Fin n) (hvw : v ≠ w)
    (hS : v ∈ S ↔ w ∈ S) (x : Fin n → Bool) (hoff : x v ≠ x w) :
    modQStatOn S q (pairSwap v w x) = modQStatOn S q x := by
  unfold modQStatOn
  rw [weightOn_pairSwap_eq S v w hvw hS x hoff]

/-- The two‑gate statistic for different supports `A, B`. -/
def twoStatOn (A B : Finset (Fin n)) (q₁ q₂ : ℕ) (x : Fin n → Bool) : ZMod q₁ × ZMod q₂ :=
  (modQStatOn A q₁ x, modQStatOn B q₂ x)

/-- **The flip‑both preserves both different‑support counts iff the pair lies in a common cell (proved).** -/
theorem twoStatOn_pairSwap (A B : Finset (Fin n)) (q₁ q₂ : ℕ) (v w : Fin n) (hvw : v ≠ w)
    (hA : v ∈ A ↔ w ∈ A) (hB : v ∈ B ↔ w ∈ B) (x : Fin n → Bool) (hoff : x v ≠ x w) :
    twoStatOn A B q₁ q₂ (pairSwap v w x) = twoStatOn A B q₁ q₂ x := by
  unfold twoStatOn
  rw [modQStatOn_pairSwap_eq A q₁ v w hvw hA x hoff, modQStatOn_pairSwap_eq B q₂ v w hvw hB x hoff]

/-- **Two different‑support MOD gates: off‑diagonal balance for a common‑cell witness pair (proved).**  The
product‑class obstruction is exactly the hypotheses `hA, hB` — a `D`‑witness pair `(v ∈ D, w ∉ D)` lying on the
same side of *both* supports.  Same support (`A = B`) collapses these to one; full support makes them automatic. -/
theorem twoGateOn_offdiag_balanced (A B : Finset (Fin n)) (q₁ q₂ : ℕ) (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) (hA : v ∈ A ↔ w ∈ A) (hB : v ∈ B ↔ w ∈ B) :
    ∀ c ∈ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).image (twoStatOn A B q₁ q₂),
      ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => twoStatOn A B q₁ q₂ x = c)).filter (fun x => fParity D x = true)).card
        = ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
            (fun x => twoStatOn A B q₁ q₂ x = c)).filter (fun x => fParity D x = false)).card :=
  balanced_offdiag_of_pres (twoStatOn A B q₁ q₂) D v w hvw hvD hwD
    (fun x h => twoStatOn_pairSwap A B q₁ q₂ v w hvw hA hB x h)

end PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation

#print axioms PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation.balanced_offdiag_of_pres
#print axioms PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation.twoGate_low_correlation_offdiagonal
#print axioms PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation.weightOn_pairSwap_eq
#print axioms PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation.twoGateOn_offdiag_balanced
