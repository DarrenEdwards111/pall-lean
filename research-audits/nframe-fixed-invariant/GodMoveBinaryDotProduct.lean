import GodMoveRationalWireEncoding
import GodMoveDotLoopPrecision
import GodMoveBinaryRationalMultiply
import GodMoveBinaryRationalAdd

/-!
# Fixed-width dot products through the emitted rational circuits

Each executed iteration multiplies the next pair of represented rationals,
normalizes and resizes that product, adds it to the cached accumulator, then
normalizes and resizes the next accumulator. Resizing uses canonical precision
bounds for the actual products and partial sums; no discarded bit is assumed
to vanish without that proof.

The bound counts emitted Boolean gates. Retained product and accumulator
reference words have the chosen width after resizing; internal arithmetic
words may be wider and the wire store retains earlier gates. Code generation,
reference-list allocation and a
complete host-machine execution bound are separate obligations. No rank or
SAT runtime assumption is introduced here.
-/

namespace GodMoveBinaryDotProduct

open GodMoveRationalWireEncoding GodMoveRationalPrecisionArithmetic
open GodMoveTrackedOrthogonalizationCost GodMoveDotLoopPrecision
open GodMoveBinaryAdder GodMoveBinaryRationalMultiply GodMoveBinaryRationalAdd
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The numerical recurrence is the multiply-then-add order of `sumProductsOn`. -/
def dotValue : ℚ → List (ℚ × ℚ) → ℚ
  | acc, [] => acc
  | acc, p :: ps => dotValue (acc + p.1 * p.2) ps

theorem dotValue_eq_sum (acc : ℚ) (pairs : List (ℚ × ℚ)) :
    dotValue acc pairs = acc + (pairs.map fun p => p.1 * p.2).sum := by
  induction pairs generalizing acc with
  | nil => simp [dotValue]
  | cons p ps ih => simp [dotValue, ih, add_assoc]

theorem dotValue_sumProductsOn {ι : Type*} (v u : ι → ℚ) (is : List ι) (acc : ℚ) :
    dotValue acc (is.map fun i => (v i, u i)) =
      (sumProductsOn v u is ⟨acc, 0⟩).value := by
  rw [dotValue_eq_sum, sumProductsOn_value]
  simp only [List.map_map, Function.comp_def]

/-- Every input, executed product, and prefix accumulator fits the fixed width.
The recursive state uses the actual next sum, not an independent size field. -/
inductive DotFits (w : ℕ) : ℚ → List (ℚ × ℚ) → Prop
  | nil {acc : ℚ} : Fits acc w → DotFits w acc []
  | cons {acc x y : ℚ} {ps : List (ℚ × ℚ)} :
      Fits acc w → Fits x w → Fits y w → Fits (x * y) w →
      DotFits w (acc + x * y) ps → DotFits w acc ((x, y) :: ps)

theorem DotFits.acc {w : ℕ} {acc : ℚ} {ps : List (ℚ × ℚ)} (h : DotFits w acc ps) :
    Fits acc w := by cases h with | nil ha => exact ha | cons ha _ _ _ _ => exact ha

theorem dotFits_of_prefixes {ι : Type*} (is : List ι) (v u : ι → ℚ) (acc : ℚ) (b : ℕ)
    (hv : ∀ i ∈ is, BitBound (v i) b) (hu : ∀ i ∈ is, BitBound (u i) b)
    (hp : ∀ i ∈ is, BitBound (v i * u i) b)
    (hs : ∀ k, BitBound (acc + ((is.take k).map fun i => v i * u i).sum) b) :
    DotFits (b + 1) acc (is.map fun i => (v i, u i)) := by
  induction is generalizing acc with
  | nil =>
      apply DotFits.nil
      exact fits_of_bitBound (by simpa using hs 0)
  | cons i is ih =>
      apply DotFits.cons
      · exact fits_of_bitBound (by simpa using hs 0)
      · exact fits_of_bitBound (hv i (by simp))
      · exact fits_of_bitBound (hu i (by simp))
      · exact fits_of_bitBound (hp i (by simp))
      · apply ih (acc + v i * u i)
          (fun j hj => hv j (by simp [hj]))
          (fun j hj => hu j (by simp [hj]))
          (fun j hj => hp j (by simp [hj]))
        intro k
        simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, ← add_assoc] using hs (k + 1)

/-- Existing precision certificates supply the entire fixed-width loop premise
at width `b+1`, including the zero-seeded empty case. -/
theorem dotFits_of_dotPrecision {n : ℕ} {v u : Fin n → ℚ} {b : ℕ}
    (h : DotPrecision v u b) :
    DotFits (b + 1) 0 ((List.finRange n).map fun i => (v i, u i)) := by
  apply dotFits_of_prefixes _ _ _ _ b
    (fun i _ => h.left i) (fun i _ => h.right i) (fun i _ => h.products i)
  intro k
  simpa only [sumProductsOn_value] using h.prefixes k

def dotStep {n : ℕ} (start w zeroRef : ℕ) (acc x y : FractionRefs) :
    List (CGate n) × FractionRefs :=
  let prod := multiplyFractions start x y
  let smallProd := resize prod.2 w zeroRef
  let total := addFractions (start + prod.1.length) acc smallProd
  (prod.1 ++ total.1, resize total.2 w zeroRef)

theorem dotStep_width {n : ℕ} (start w zeroRef : ℕ) (acc x y : FractionRefs) :
    Width (dotStep (n := n) start w zeroRef acc x y).2 w := by
  exact resize_width _ _ _

theorem dotStep_gate_count {n : ℕ} (start w zeroRef : ℕ) (acc x y : FractionRefs)
    (ha : Width acc w) (hx : Width x w) (hy : Width y w) :
    (dotStep (n := n) start w zeroRef acc x y).1.length ≤ 2048 * (w + 1) ^ 3 := by
  have hm := multiplyFractions_gate_count (n := n) start x y w hx hy
  have hs := addFractions_gate_count (n := n)
    (start + (multiplyFractions (n := n) start x y).1.length) acc
    (resize (multiplyFractions (n := n) start x y).2 w zeroRef) w ha (resize_width _ _ _)
  simp only [dotStep, List.length_append]
  omega

theorem dotStep_valid {n : ℕ} (start w zeroRef : ℕ) (acc x y : FractionRefs)
    (ha : Width acc w) (hz : zeroRef < start) :
    Valid (dotStep (n := n) start w zeroRef acc x y).2
      (start + (dotStep (n := n) start w zeroRef acc x y).1.length) := by
  have hs := addFractions_valid (n := n)
    (start + (multiplyFractions (n := n) start x y).1.length) acc
    (resize (multiplyFractions (n := n) start x y).2 w zeroRef) w ha (resize_width _ _ _)
  have hr := resize_valid _ w zeroRef _ hs (by omega)
  simpa only [dotStep, List.length_append, Nat.add_assoc] using hr

theorem dotStep_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (w zeroRef : ℕ) (acc x y : FractionRefs) (q r s : ℚ)
    (haw : Width acc w) (hxw : Width x w) (hyw : Width y w)
    (hav : Valid acc vals.length) (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hz : zeroRef < vals.length) (hzv : vals.getD zeroRef false = false)
    (ha : Represents vals acc q) (hx : Represents vals x r) (hy : Represents vals y s)
    (hp : Fits (r * s) w) (hs : Fits (q + r * s) w) :
    Represents (runFrom a vals (dotStep vals.length w zeroRef acc x y).1)
      (dotStep (n := n) vals.length w zeroRef acc x y).2 (q + r * s) := by
  let prod := multiplyFractions (n := n) vals.length x y
  let v₁ := runFrom a vals prod.1
  have hv₁ : v₁.length = vals.length + prod.1.length := runFrom_length _ _ _
  have hz₁ : v₁.getD zeroRef false = false :=
    (read_runFrom_old a vals prod.1 zeroRef hz).trans hzv
  have hp₁ : Represents v₁ prod.2 (r * s) :=
    multiplyFractions_represents a vals x y r s w hxw hyw hxv hyv hx hy
  have hpv : Valid prod.2 v₁.length := by
    rw [hv₁]
    exact multiplyFractions_valid vals.length x y w hxw hyw
  have hpr := resize_represents v₁ prod.2 (r * s) w zeroRef hp₁ hz₁ hp
  have hprv := resize_valid prod.2 w zeroRef v₁.length hpv (by omega)
  have hav₁ : Valid acc v₁.length := hav.mono (by omega)
  have ha₁ : Represents v₁ acc q := ha.runFrom_old a prod.1 hav
  let total := addFractions (n := n) v₁.length acc (resize prod.2 w zeroRef)
  have ht : Represents (runFrom a v₁ total.1) total.2 (q + r * s) :=
    addFractions_represents a v₁ acc (resize prod.2 w zeroRef) q (r * s) w
      haw (resize_width _ _ _) hav₁ hprv ha₁ hpr
  have hz₂ : (runFrom a v₁ total.1).getD zeroRef false = false :=
    (read_runFrom_old a v₁ total.1 zeroRef (by omega)).trans hz₁
  have hr := resize_represents (runFrom a v₁ total.1) total.2 (q + r * s)
    w zeroRef ht hz₂ hs
  simpa only [dotStep, runFrom_append, prod, v₁, total, runFrom_length] using hr

/-- The builder materializes each scalar program once and retains its output
references at width `w` before generating the next iteration. -/
def dotFrom {n : ℕ} (start w zeroRef : ℕ) (acc : FractionRefs) :
    List (FractionRefs × FractionRefs) → List (CGate n) × FractionRefs
  | [] => ([], acc)
  | p :: ps =>
      let step := dotStep start w zeroRef acc p.1 p.2
      let rest := dotFrom (start + step.1.length) w zeroRef step.2 ps
      (step.1 ++ rest.1, rest.2)

theorem dotFrom_width {n : ℕ} (start w zeroRef : ℕ) (acc : FractionRefs)
    (pairs : List (FractionRefs × FractionRefs)) (ha : Width acc w) :
    Width (dotFrom (n := n) start w zeroRef acc pairs).2 w := by
  induction pairs generalizing start acc with
  | nil => exact ha
  | cons p ps ih => exact ih _ _ (dotStep_width _ _ _ _ _ _)

theorem dotFrom_gate_count {n : ℕ} (start w zeroRef : ℕ) (acc : FractionRefs)
    (pairs : List (FractionRefs × FractionRefs)) (ha : Width acc w)
    (hw : ∀ p ∈ pairs, Width p.1 w ∧ Width p.2 w) :
    (dotFrom (n := n) start w zeroRef acc pairs).1.length ≤
      2048 * pairs.length * (w + 1) ^ 3 := by
  induction pairs generalizing start acc with
  | nil => simp [dotFrom]
  | cons p ps ih =>
      have hp := hw p (by simp)
      have hs := dotStep_gate_count (n := n) start w zeroRef acc p.1 p.2 ha hp.1 hp.2
      have hr := ih (start + (dotStep (n := n) start w zeroRef acc p.1 p.2).1.length)
        (dotStep (n := n) start w zeroRef acc p.1 p.2).2
        (dotStep_width _ _ _ _ _ _) (fun q hq => hw q (by simp [hq]))
      simp only [dotFrom, List.length_append, List.length_cons]
      nlinarith

theorem dotFrom_valid {n : ℕ} (start w zeroRef : ℕ) (acc : FractionRefs)
    (pairs : List (FractionRefs × FractionRefs)) (haw : Width acc w)
    (hav : Valid acc start) (hz : zeroRef < start) :
    Valid (dotFrom (n := n) start w zeroRef acc pairs).2
      (start + (dotFrom (n := n) start w zeroRef acc pairs).1.length) := by
  induction pairs generalizing start acc with
  | nil => simpa [dotFrom] using hav
  | cons p ps ih =>
      have hv := dotStep_valid (n := n) start w zeroRef acc p.1 p.2 haw hz
      have hr := ih (start + (dotStep (n := n) start w zeroRef acc p.1 p.2).1.length)
        (dotStep (n := n) start w zeroRef acc p.1 p.2).2
        (dotStep_width _ _ _ _ _ _) hv (by omega)
      simpa only [dotFrom, List.length_append, Nat.add_assoc] using hr

/-- Stored input references, widths and their exact canonical rational values. -/
def PairsRepresent (vals : List Bool) (w : ℕ)
    (pairs : List (FractionRefs × FractionRefs)) (values : List (ℚ × ℚ)) : Prop :=
  List.Forall₂ (fun p q => Width p.1 w ∧ Width p.2 w ∧
    Valid p.1 vals.length ∧ Valid p.2 vals.length ∧
    Represents vals p.1 q.1 ∧ Represents vals p.2 q.2) pairs values

theorem PairsRepresent.runFrom_old {n : ℕ} {vals : List Bool} {w : ℕ}
    {pairs : List (FractionRefs × FractionRefs)} {values : List (ℚ × ℚ)}
    (h : PairsRepresent vals w pairs values) (a : Fin n → Bool) (code : List (CGate n)) :
    PairsRepresent (runFrom a vals code) w pairs values := by
  apply List.Forall₂.imp (fun p q hp => ?_) h
  have hl : vals.length ≤ (runFrom a vals code).length := by
    rw [runFrom_length]
    omega
  exact ⟨hp.1, hp.2.1, hp.2.2.1.mono hl, hp.2.2.2.1.mono hl,
    hp.2.2.2.2.1.runFrom_old a code hp.2.2.1,
    hp.2.2.2.2.2.runFrom_old a code hp.2.2.2.1⟩

theorem PairsRepresent.widths {vals : List Bool} {w : ℕ}
    {pairs : List (FractionRefs × FractionRefs)} {values : List (ℚ × ℚ)}
    (h : PairsRepresent vals w pairs values) :
    ∀ p ∈ pairs, Width p.1 w ∧ Width p.2 w := by
  induction h with
  | nil => simp
  | cons h hd ih =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨h.1, h.2.1⟩
      · exact ih p hp

theorem PairsRepresent.length_eq {vals : List Bool} {w : ℕ}
    {pairs : List (FractionRefs × FractionRefs)} {values : List (ℚ × ℚ)}
    (h : PairsRepresent vals w pairs values) : pairs.length = values.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem dotFrom_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (w zeroRef : ℕ) (acc : FractionRefs) (q : ℚ)
    (pairs : List (FractionRefs × FractionRefs)) (values : List (ℚ × ℚ))
    (haw : Width acc w) (hav : Valid acc vals.length) (ha : Represents vals acc q)
    (hz : zeroRef < vals.length) (hzv : vals.getD zeroRef false = false)
    (hr : PairsRepresent vals w pairs values) (hf : DotFits w q values) :
    Represents (runFrom a vals (dotFrom vals.length w zeroRef acc pairs).1)
      (dotFrom (n := n) vals.length w zeroRef acc pairs).2 (dotValue q values) := by
  induction pairs generalizing vals acc q values with
  | nil =>
      cases hr
      exact ha
  | cons p ps ih =>
      obtain ⟨⟨x, y⟩, qs, hp, hrs, rfl⟩ := List.forall₂_cons_left_iff.mp hr
      cases hf with
      | cons _ _ _ hprod htail =>
          let step := dotStep (n := n) vals.length w zeroRef acc p.1 p.2
          let v₁ := runFrom a vals step.1
          have hv₁ : v₁.length = vals.length + step.1.length := runFrom_length _ _ _
          have hs : Represents v₁ step.2 (q + x * y) :=
            dotStep_represents a vals w zeroRef acc p.1 p.2 q x y
              haw hp.1 hp.2.1 hav hp.2.2.1 hp.2.2.2.1 hz hzv
              ha hp.2.2.2.2.1 hp.2.2.2.2.2 hprod htail.acc
          have hsv : Valid step.2 v₁.length := by
            rw [hv₁]
            exact dotStep_valid vals.length w zeroRef acc p.1 p.2 haw hz
          have hz₁ : v₁.getD zeroRef false = false :=
            (read_runFrom_old a vals step.1 zeroRef hz).trans hzv
          have hrs₁ : PairsRepresent v₁ w ps qs :=
            PairsRepresent.runFrom_old hrs a step.1
          have ht := ih v₁ step.2 (q + x * y) qs (dotStep_width _ _ _ _ _ _)
            hsv hs (by omega) hz₁ hrs₁ htail
          simpa only [dotFrom, dotValue, runFrom_append, step, v₁, runFrom_length] using ht

/-- Exact specialization to an already certified zero-seeded dot call. The
returned fraction represents the old counted arithmetic loop's value. -/
theorem dotFrom_sumProductsOn {n s : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (b zeroRef : ℕ) (acc : FractionRefs) (v u : Fin s → ℚ)
    (pairs : List (FractionRefs × FractionRefs))
    (haw : Width acc (b + 1)) (hav : Valid acc vals.length)
    (ha : Represents vals acc 0) (hz : zeroRef < vals.length)
    (hzv : vals.getD zeroRef false = false)
    (hr : PairsRepresent vals (b + 1) pairs ((List.finRange s).map fun i => (v i, u i)))
    (hp : DotPrecision v u b) :
    Represents (runFrom a vals (dotFrom vals.length (b + 1) zeroRef acc pairs).1)
      (dotFrom (n := n) vals.length (b + 1) zeroRef acc pairs).2
      (sumProductsOn v u (List.finRange s) ⟨0, 0⟩).value := by
  rw [← dotValue_sumProductsOn]
  exact dotFrom_represents a vals (b + 1) zeroRef acc 0 pairs _
    haw hav ha hz hzv hr (dotFits_of_dotPrecision hp)

theorem dotFrom_sumProductsOn_gate_count {n s : ℕ} (start b zeroRef : ℕ)
    (acc : FractionRefs) (vals : List Bool) (v u : Fin s → ℚ)
    (pairs : List (FractionRefs × FractionRefs)) (haw : Width acc (b + 1))
    (hr : PairsRepresent vals (b + 1) pairs ((List.finRange s).map fun i => (v i, u i))) :
    (dotFrom (n := n) start (b + 1) zeroRef acc pairs).1.length ≤
      2048 * s * (b + 2) ^ 3 := by
  have hl : pairs.length = s := by simpa using hr.length_eq
  simpa only [hl, Nat.add_assoc] using
    dotFrom_gate_count (n := n) start (b + 1) zeroRef acc pairs haw hr.widths

end GodMoveBinaryDotProduct

#print axioms GodMoveBinaryDotProduct.dotValue_sumProductsOn
#print axioms GodMoveBinaryDotProduct.dotFits_of_prefixes
#print axioms GodMoveBinaryDotProduct.dotFits_of_dotPrecision
#print axioms GodMoveBinaryDotProduct.dotStep_represents
#print axioms GodMoveBinaryDotProduct.dotFrom_gate_count
#print axioms GodMoveBinaryDotProduct.dotFrom_valid
#print axioms GodMoveBinaryDotProduct.dotFrom_represents
#print axioms GodMoveBinaryDotProduct.dotFrom_sumProductsOn
#print axioms GodMoveBinaryDotProduct.dotFrom_sumProductsOn_gate_count
