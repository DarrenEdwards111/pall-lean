import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Mod6SymAndDepth2

/-!
# The composition lemma for the composite residue / `SYM∘AND` observer — what composes, and the one wall that does not

Route B needs the composite residue observer to **compose**: if subcircuits have `SYM∘AND` (count-symmetric)
representations, does a gate applied to them again have one, with controlled blow-up?  This is the mini–Beigel–Tarui
question.  We answer it honestly by separating the part that genuinely composes from the part that does not.

A function `F : (Fin n → Bool) → Bool` **has a `SYM∘AND` representation** when it is a symmetric function of the count
of satisfied bottom `AND` gates: `F x = sym (satCount supports x)` for some `sym : ℕ → Bool`
(`HasSymAndRep`, grounding object the proved depth-2 `MOD₆∘AND` of `…ACC0Mod6SymAndDepth2`).

## What composes — proved (clean axioms, no `sorry`)

* **`hasSymAndRep_not`** — `NOT` closure: the complement is `SYM∘AND` over the *same* bottom layer (negate `sym`).
* **`hasSymAndRep_and_sharedLayer`** / **`hasSymAndRep_or_sharedLayer`** — over a **shared** bottom layer, `AND`/`OR`
  stay single-count `SYM∘AND` (both are functions of one and the same count `satCount supp x`).
* **`residue_observer_compose_coprime`** — the cross-modulus CRT composition: for coprime `a, b`, the `MODₐ` and
  `MOD_b` residue observers compose to the `MOD_{ab}` observer (`a*b ∣ m ↔ a ∣ m ∧ b ∣ m`).  (`mod6 = mod2 ∧ mod3`
  is the case `a=2, b=3`; this is the general product-residue / mixed-modulus composition of the algebra aspect.)
* **`hasBinarySymRep_and`** / **`hasBinarySymRep_or`** — the general cross-layer case: `AND`/`OR` of two `SYM∘AND`
  functions over *different* layers is a **joint** function of the *pair* of counts (`HasBinarySymRep`): the count
  dimension goes up by one.

## The wall — not proved, socketed precisely

Cross-layer `AND`/`OR` lands in a **two-count joint** representation, not a single-count one.  Collapsing a joint
multi-count representation back to a *single* quasipolynomial `SYM∘AND` is the genuine hard content — the
Beigel–Tarui degree reduction (probabilistic polynomials / Toda).  The naive **exact** collapse is even false in
general (a single count cannot recover an independent pair of counts), which is exactly why `BT` needs quasipolynomial
blow-up and approximation.  We isolate it:

* **`MiniBTCollapse`** — the named open hypothesis: every two-count joint representation collapses to a single
  `SYM∘AND`.  **Not proved** (the exact form is too strong; the real theorem is its quasipolynomial relaxation).
* **`symAndRep_closed_under_and_of_miniBT`** / **`_or_`** — *given* `MiniBTCollapse`, `SYM∘AND` is closed under
  `AND`/`OR`.  This is the precise conditional: closure of the composite observer ⟺ the mini-`BT` collapse.

## Honest scope

The closures that do not raise the count dimension (`NOT`, shared-layer `AND`/`OR`) and the cross-modulus CRT
composition are *proved*; cross-layer `AND`/`OR` is proved to land in a joint two-count representation.  We leave the
collapse of a joint representation to a single `SYM∘AND` as the named socket `MiniBTCollapse`.

**Correction (see `…ACC0MiniBTTwoCount`).**  The remark below that the *exact* collapse is "too strong / false" was
wrong: `MiniBTCollapse` is in fact *provable* exactly, by a mixed-radix encoding (`miniBTCollapse_holds`), and the
conditional closures below then become unconditional.  The genuine wall is not impossibility but the **multiplicative
size blow-up** of the exact encoding, which compounds to a tower over circuit depth — which is why the *global*
quasipolynomial `SYM∘AND` representation of a whole `ACC⁰` circuit (`…ACC0CompositeBTTarget`) still needs probabilistic
polynomials.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2

variable {n : ℕ}

/-! ## The `SYM∘AND` representation predicate -/

/-- **`F` has a `SYM∘AND` representation**: it is a symmetric function `sym` of the count of satisfied bottom `AND`
gates over some layer `supports`. -/
def HasSymAndRep (F : (Fin n → Bool) → Bool) : Prop :=
  ∃ (t : ℕ) (supports : Fin t → Finset (Fin n)) (sym : ℕ → Bool),
    ∀ x, F x = sym (satCount supports x)

/-- **The depth-2 `MOD₆∘AND` circuit has a `SYM∘AND` representation (proved): the grounding object.**  Confirms the
abstraction is inhabited by the real proved base case (`sym := fun s => decide (6 ∣ s)`). -/
theorem mod6AndCircuit_hasSymAndRep {t : ℕ} (supp : Fin t → Finset (Fin n)) :
    HasSymAndRep (fun x => decide (6 ∣ satCount supp x)) :=
  ⟨t, supp, fun s => decide (6 ∣ s), fun _ => rfl⟩

/-! ## 1. Closures that do not raise the count dimension (proved) -/

/-- **`NOT` closure (proved): the complement is `SYM∘AND` over the same layer.** -/
theorem hasSymAndRep_not {F : (Fin n → Bool) → Bool} (h : HasSymAndRep F) :
    HasSymAndRep (fun x => !F x) := by
  obtain ⟨t, supp, sym, hF⟩ := h
  exact ⟨t, supp, fun s => !sym s, fun x => by simp only [hF]⟩

/-- **Shared-layer `AND` closure (proved): over one bottom layer, `AND` stays single-count `SYM∘AND`.** -/
theorem hasSymAndRep_and_sharedLayer {t : ℕ} {supp : Fin t → Finset (Fin n)}
    {F G : (Fin n → Bool) → Bool} {symF symG : ℕ → Bool}
    (hF : ∀ x, F x = symF (satCount supp x)) (hG : ∀ x, G x = symG (satCount supp x)) :
    HasSymAndRep (fun x => F x && G x) :=
  ⟨t, supp, fun s => symF s && symG s, fun x => by simp only [hF, hG]⟩

/-- **Shared-layer `OR` closure (proved).** -/
theorem hasSymAndRep_or_sharedLayer {t : ℕ} {supp : Fin t → Finset (Fin n)}
    {F G : (Fin n → Bool) → Bool} {symF symG : ℕ → Bool}
    (hF : ∀ x, F x = symF (satCount supp x)) (hG : ∀ x, G x = symG (satCount supp x)) :
    HasSymAndRep (fun x => F x || G x) :=
  ⟨t, supp, fun s => symF s || symG s, fun x => by simp only [hF, hG]⟩

/-! ## 2. Cross-modulus CRT composition of residue observers (proved) -/

/-- **Cross-modulus composition (proved): for coprime `a, b`, the `MODₐ` and `MOD_b` observers compose to `MOD_{ab}`.**
`a*b ∣ m ↔ a ∣ m ∧ b ∣ m`.  This is the general product-residue / mixed-modulus composition of the algebra aspect (the
case `a=2, b=3` is `MOD₆ = MOD₂ ∧ MOD₃`); the composite observer for `∏ pᵢ` is the iterated product of the single-prime
observers. -/
theorem residue_observer_compose_coprime {a b : ℕ} (hab : Nat.Coprime a b) (m : ℕ) :
    a * b ∣ m ↔ (a ∣ m ∧ b ∣ m) := by
  constructor
  · intro h
    exact ⟨(dvd_mul_right a b).trans h, (dvd_mul_left b a).trans h⟩
  · rintro ⟨ha, hb⟩
    exact hab.mul_dvd_of_dvd_of_dvd ha hb

/-! ## 3. Cross-layer `AND`/`OR` lands in a joint two-count representation (proved) -/

/-- **`F` has a binary (two-count) joint representation**: it is a joint function `j` of the counts of satisfied
bottom `AND` gates over *two* layers. -/
def HasBinarySymRep (F : (Fin n → Bool) → Bool) : Prop :=
  ∃ (t₁ t₂ : ℕ) (s₁ : Fin t₁ → Finset (Fin n)) (s₂ : Fin t₂ → Finset (Fin n)) (j : ℕ → ℕ → Bool),
    ∀ x, F x = j (satCount s₁ x) (satCount s₂ x)

/-- **Cross-layer `AND` is jointly two-count symmetric (proved): the count dimension rises by one.** -/
theorem hasBinarySymRep_and {F G : (Fin n → Bool) → Bool}
    (hF : HasSymAndRep F) (hG : HasSymAndRep G) :
    HasBinarySymRep (fun x => F x && G x) := by
  obtain ⟨tF, sF, symF, hFx⟩ := hF
  obtain ⟨tG, sG, symG, hGx⟩ := hG
  exact ⟨tF, tG, sF, sG, fun a b => symF a && symG b, fun x => by simp only [hFx, hGx]⟩

/-- **Cross-layer `OR` is jointly two-count symmetric (proved).** -/
theorem hasBinarySymRep_or {F G : (Fin n → Bool) → Bool}
    (hF : HasSymAndRep F) (hG : HasSymAndRep G) :
    HasBinarySymRep (fun x => F x || G x) := by
  obtain ⟨tF, sF, symF, hFx⟩ := hF
  obtain ⟨tG, sG, symG, hGx⟩ := hG
  exact ⟨tF, tG, sF, sG, fun a b => symF a || symG b, fun x => by simp only [hFx, hGx]⟩

/-! ## 4. The wall — collapsing joint to single (the mini-Beigel–Tarui socket) -/

/-- **The mini-Beigel–Tarui collapse.**  Every two-count joint representation collapses to a single `SYM∘AND`
representation.  *Originally stated here as the open socket marking the wall; it is in fact **provable** exactly* —
`…ACC0MiniBTTwoCount.miniBTCollapse_holds` discharges it via a mixed-radix encoding.  (The earlier guess that the
exact form was "too strong" was wrong; the genuine wall is the multiplicative **size** blow-up of the encoding over
circuit depth, not impossibility.)  Kept as a definition because the conditional closures below are stated against
it. -/
def MiniBTCollapse (n : ℕ) : Prop :=
  ∀ F : (Fin n → Bool) → Bool, HasBinarySymRep F → HasSymAndRep F

/-- **Closure under `AND` ⟸ the mini-`BT` collapse (proved conditional).**  *Given* `MiniBTCollapse`, the cross-layer
`AND` (which lands in a joint two-count representation) collapses back to a single `SYM∘AND`.  This pins the closure of
the composite observer exactly to the mini-`BT` collapse. -/
theorem symAndRep_closed_under_and_of_miniBT (hBT : MiniBTCollapse n)
    {F G : (Fin n → Bool) → Bool} (hF : HasSymAndRep F) (hG : HasSymAndRep G) :
    HasSymAndRep (fun x => F x && G x) :=
  hBT _ (hasBinarySymRep_and hF hG)

/-- **Closure under `OR` ⟸ the mini-`BT` collapse (proved conditional).** -/
theorem symAndRep_closed_under_or_of_miniBT (hBT : MiniBTCollapse n)
    {F G : (Fin n → Bool) → Bool} (hF : HasSymAndRep F) (hG : HasSymAndRep G) :
    HasSymAndRep (fun x => F x || G x) :=
  hBT _ (hasBinarySymRep_or hF hG)

end PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition.mod6AndCircuit_hasSymAndRep
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition.hasSymAndRep_not
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition.hasSymAndRep_and_sharedLayer
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition.hasSymAndRep_or_sharedLayer
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition.residue_observer_compose_coprime
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition.hasBinarySymRep_and
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition.hasBinarySymRep_or
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition.symAndRep_closed_under_and_of_miniBT
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition.symAndRep_closed_under_or_of_miniBT
