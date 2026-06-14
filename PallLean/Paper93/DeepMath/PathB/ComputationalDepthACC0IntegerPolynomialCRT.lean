import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymmetricObserver
import Mathlib.Data.Nat.ChineseRemainder

/-!
# The Beigel–Tarui integer-polynomial / CRT decode (the exact *back half*)

The Yao–Beigel–Tarui normal form has two halves:

* **Front half** (`ACC⁰ → exact low-degree integer polynomial across depth`): the *open wall* (Wall 1 in
  `WHAT_IS_PROVED.md`).  Razborov–Smolensky gives only an *approximate* low-degree polynomial over `F_p`; the *exact*
  integer-valued polynomial of polylog degree is the irreducible Beigel–Tarui analytic core.
* **Back half** (this file): given the **exact integer count polynomial**, an exact `MOD_M` (or threshold) decision is
  recovered from the count's residues modulo the prime factors of `M`, recombined by the **Chinese Remainder
  Theorem**.  This half is *exact* and fully provable.

The integer count polynomial is `gateCount g x` (`…ACC0SymmetricObserver`): the number of accepting sub-gates, an
exact integer-valued symmetric polynomial in the gate indicators.  For `M = ∏ q_i` with the `q_i` **pairwise
coprime**, CRT gives

```
gateCount g x ≡ t  (mod M)   ⟺   ∀ i, gateCount g x ≡ t  (mod q_i),
```

so the exact `MOD_M` decision **factors through the residue vector** `i ↦ (gateCount g x  mod q_i) ∈ ∏_i ZMod q_i`,
of cardinality `∏_i q_i = M`.  This is the integer-polynomial/CRT decode at the heart of Beigel–Tarui's
`SYM∘AND`-top, generalising `mod6_eq_mod2_and_mod3` (`…Layer3MixedModulus`) from the fixed modulus `6 = 2·3` to an
arbitrary pairwise-coprime family, and attaching it to the **count polynomial** rather than a single `MOD`-gate's
support count.

## What is proved (clean axioms, no `sorry`)

* `count_crt_iff` — CRT for the count: `gateCount ≡ t [MOD qs.prod] ↔ ∀ i, gateCount ≡ t [MOD qs.get i]`
  (pairwise coprime), via `Nat.modEq_list_prod_iff`.
* `modCount_factors_through_resVec` — the exact `MOD_{qs.prod}` count decision `= G (countResVec …)`: it factors
  through the residue vector `i ↦ (gateCount : ZMod (qs.get i))` (CRT + `ZMod.natCast_eq_natCast_iff`).
* `countResVec_card_le` — `|image(countResVec)| ≤ qs.prod` (lands in `∏_i ZMod q_i`).
* `count_crt_sat_speedup` — `qs.prod < 2^n ⇒` the exact `MOD_{qs.prod}` count-decision SAT is decided by a search over
  `< 2^n` residue cells.
* `mod6_count_crt_speedup` — the concrete `M = 6 = 2·3` instance: a `MOD_6` count gate decoded via residues mod `2`
  and mod `3`, searchable in `≤ 6` cells.

## Honest scope — this is the *exact back half only*

The CRT decode is **exact** and requires the **exact** integer count `gateCount`.  CRT does **not** turn *approximate*
residues into an exact decision: combining Razborov–Smolensky approximants (each correct on a `1-ε` fraction over its
own prime field) by CRT yields a decision correct only where *all* approximants are simultaneously correct — still
approximate.  The exactness here comes from using the exact count, not from CRT.  So this file does **not** close the
exact-vs-approximate gap; that gap is precisely the front half — **Wall 1**, `ACC⁰ → exact low-degree integer
polynomial across depth` (socketed as `MixedACCDepthReductionSocket` / `HasExactSymAndForm`).  And a `< 2^n` cell
count is still not a uniform algorithm (Wall 2, Williams realization).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver

variable {n m : ℕ}

/-- The **exact `MOD_{qs.prod}` decision on the integer count polynomial**: fires iff the accepting-sub-gate count
`gateCount g x` is `≡ t` modulo `M = qs.prod`. -/
def modCountDecision (qs : List ℕ) (t : ℕ) (g : Fin m → (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : Bool :=
  decide (gateCount g x ≡ t [MOD qs.prod])

/-- The **residue vector of the integer count polynomial**: coordinate `i` is `gateCount g x` reduced modulo `qs.get i`
(an element of `ZMod (qs.get i)`).  This is the Beigel–Tarui CRT statistic — the only information the `MOD_{qs.prod}`
decision can use. -/
def countResVec (qs : List ℕ) (g : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (i : Fin qs.length) → ZMod (qs.get i) :=
  fun i => (gateCount g x : ZMod (qs.get i))

/-- **CRT for the integer count (proved).**  For a pairwise-coprime family `qs`, the count is `≡ t` modulo the product
iff it is `≡ t` modulo each factor — the Chinese Remainder Theorem applied to `gateCount`. -/
theorem count_crt_iff (qs : List ℕ) (co : qs.Pairwise Nat.Coprime) (t : ℕ)
    (g : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    gateCount g x ≡ t [MOD qs.prod] ↔ ∀ i : Fin qs.length, gateCount g x ≡ t [MOD qs.get i] :=
  Nat.modEq_list_prod_iff co

/-- **The exact `MOD_{qs.prod}` count decision factors through the residue vector (proved).**  CRT collapses the
modulus, and `ZMod.natCast_eq_natCast_iff` turns each `≡ t [MOD q_i]` into a residue equation, so the decision is a
fixed Boolean function `G` of `countResVec`. -/
theorem modCount_factors_through_resVec (qs : List ℕ) (co : qs.Pairwise Nat.Coprime) (t : ℕ)
    (g : Fin m → (Fin n → Bool) → Bool) :
    ∃ G : ((i : Fin qs.length) → ZMod (qs.get i)) → Bool,
      ∀ x, modCountDecision qs t g x = G (countResVec qs g x) := by
  refine ⟨fun v => decide (∀ i : Fin qs.length, v i = (t : ZMod (qs.get i))), fun x => ?_⟩
  show decide (gateCount g x ≡ t [MOD qs.prod])
      = decide (∀ i : Fin qs.length, (gateCount g x : ZMod (qs.get i)) = (t : ZMod (qs.get i)))
  apply decide_eq_decide.mpr
  rw [count_crt_iff qs co]
  exact forall_congr' (fun i => (ZMod.natCast_eq_natCast_iff _ _ _).symm)

/-- **The exact decision is observed by the count-residue vector (proved).** -/
theorem modCount_observed (qs : List ℕ) (co : qs.Pairwise Nat.Coprime) (t : ℕ)
    (g : Fin m → (Fin n → Bool) → Bool) :
    ObservedBy (modCountDecision qs t g) (countResVec qs g) :=
  modCount_factors_through_resVec qs co t g

/-- **The residue-cell count is `≤ qs.prod` (proved).**  The count-residue vector lands in `∏_i ZMod (qs.get i)`, of
cardinality `∏_i qs.get i = qs.prod`. -/
theorem countResVec_card_le (qs : List ℕ) (hpos : ∀ i : Fin qs.length, 0 < qs.get i)
    (g : Fin m → (Fin n → Bool) → Bool) :
    (Finset.univ.image (countResVec qs g)).card ≤ qs.prod := by
  haveI : ∀ i : Fin qs.length, NeZero (qs.get i) := fun i => ⟨(hpos i).ne'⟩
  calc (Finset.univ.image (countResVec qs g)).card
      ≤ Fintype.card ((i : Fin qs.length) → ZMod (qs.get i)) :=
        le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
    _ = ∏ i, Fintype.card (ZMod (qs.get i)) := Fintype.card_pi
    _ = ∏ i, qs.get i := Finset.prod_congr rfl (fun i _ => ZMod.card (qs.get i))
    _ = qs.prod := by rw [← List.prod_ofFn, List.ofFn_get]

/-- **The CRT SAT speedup (proved): `qs.prod < 2^n ⇒` the exact `MOD_{qs.prod}` count-decision is SAT-decided by a
search over `< 2^n` residue cells.**  The exact back half of Beigel–Tarui, made searchable. -/
theorem count_crt_sat_speedup (qs : List ℕ) (co : qs.Pairwise Nat.Coprime)
    (hpos : ∀ i : Fin qs.length, 0 < qs.get i) (t : ℕ) (g : Fin m → (Fin n → Bool) → Bool)
    (hregime : qs.prod < 2 ^ n) :
    ∃ G : ((i : Fin qs.length) → ZMod (qs.get i)) → Bool,
      (Satisfiable (modCountDecision qs t g) ↔
          ∃ v ∈ Finset.univ.image (countResVec qs g), G v = true)
        ∧ (Finset.univ.image (countResVec qs g)).card < 2 ^ n := by
  obtain ⟨G, hG⟩ := modCount_factors_through_resVec qs co t g
  refine ⟨G, ?_, lt_of_le_of_lt (countResVec_card_le qs hpos g) hregime⟩
  have hsat : Satisfiable (modCountDecision qs t g) ↔ ∃ x, G (countResVec qs g x) = true := by
    unfold Satisfiable
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hG]; exact hx⟩
    · rintro ⟨x, hx⟩; exact ⟨x, by rw [hG]; exact hx⟩
  rw [hsat]
  exact sat_iff_image G (countResVec qs g)

/-- **The concrete `M = 6 = 2·3` instance (proved).**  A `MOD_6` gate on the integer count is decoded via the count's
residues modulo `2` and modulo `3` (the Beigel–Tarui CRT split, `mod6_eq_mod2_and_mod3` lifted to the count
polynomial), SAT-searchable in `≤ 6` residue cells. -/
theorem mod6_count_crt_speedup (t : ℕ) (g : Fin m → (Fin n → Bool) → Bool) (hregime : 6 < 2 ^ n) :
    ∃ G : ((i : Fin ([2, 3] : List ℕ).length) → ZMod (([2, 3] : List ℕ).get i)) → Bool,
      (Satisfiable (modCountDecision [2, 3] t g) ↔
          ∃ v ∈ Finset.univ.image (countResVec [2, 3] g), G v = true)
        ∧ (Finset.univ.image (countResVec [2, 3] g)).card < 2 ^ n := by
  refine count_crt_sat_speedup [2, 3] (by decide) (by decide) t g ?_
  rw [show ([2, 3] : List ℕ).prod = 6 from by decide]
  exact hregime

end PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT.count_crt_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT.modCount_factors_through_resVec
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT.countResVec_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT.count_crt_sat_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT.mod6_count_crt_speedup
