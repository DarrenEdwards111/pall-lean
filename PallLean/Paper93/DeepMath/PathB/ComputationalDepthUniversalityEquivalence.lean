import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSeparatingMeasure
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9PpolyLowerBound

/-!
# Universality and the sharp equivalence `SeparatingMeasure ↔ ¬ Ppoly`

Every Boolean function has a circuit (universality, via a DNF construction), so the **minimum circuit
size** is a total measure.  It is a `SeparatingMeasure` exactly when the target is hard — which upgrades
the "no shortcut" bridge to a genuine **equivalence**:

* **`universality`** — `∀ f, ∃ s, f ∈ SIZE n s` (DNF).
* **`separatingMeasure_iff_not_ppoly`** — `Nonempty (SeparatingMeasure L) ↔ ¬ Ppoly L`.

So *building a separating measure is exactly as hard as proving the separation* — the target object
exists **iff** `L ∉ P/poly`.  No measure can be a shortcut, and the trivial (min-size) measure witnesses
the easy direction.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalityEquivalence

open PallLean.Paper93.DeepMath.PathB
open Layer8

variable {n : ℕ}

/-- The literal circuit selecting the target bit-value `a i`. -/
def literal (a : Fin n → Bool) (i : Fin n) : Circuit n :=
  if a i then Circuit.input i else Circuit.not (Circuit.input i)

theorem eval_literal (a x : Fin n → Bool) (i : Fin n) :
    (literal a i).eval x = (x i == a i) := by
  unfold literal
  cases hai : a i <;> cases hxi : x i <;> simp [Circuit.eval, hai, hxi]

/-- The minterm circuit: `AND` of the `n` literals for `a`. -/
def minterm (a : Fin n → Bool) : Circuit n :=
  (List.finRange n).foldr (fun i acc => Circuit.and (literal a i) acc) (Circuit.const true)

theorem eval_minterm_aux (a x : Fin n → Bool) (l : List (Fin n)) :
    (l.foldr (fun i acc => Circuit.and (literal a i) acc) (Circuit.const true)).eval x
      = l.all (fun i => x i == a i) := by
  induction l with
  | nil => simp [Circuit.eval]
  | cons i l ih => simp [Circuit.eval, eval_literal, ih, List.all_cons]

theorem eval_minterm (a x : Fin n → Bool) : (minterm a).eval x = true ↔ x = a := by
  rw [minterm, eval_minterm_aux, List.all_eq_true]
  constructor
  · intro h
    funext i
    have := h i (List.mem_finRange i)
    simpa [beq_iff_eq] using this
  · intro h i _
    rw [h]
    simp

/-- All inputs on which `f` is true. -/
noncomputable def enumTrue (f : (Fin n → Bool) → Bool) : List (Fin n → Bool) :=
  (Finset.univ.filter (fun a => f a = true)).toList

/-- The DNF circuit for `f`: `OR` of the minterms of its true points. -/
noncomputable def dnf (f : (Fin n → Bool) → Bool) : Circuit n :=
  (enumTrue f).foldr (fun a acc => Circuit.or (minterm a) acc) (Circuit.const false)

theorem eval_dnf_aux (x : Fin n → Bool) (l : List (Fin n → Bool)) :
    (l.foldr (fun a acc => Circuit.or (minterm a) acc) (Circuit.const false)).eval x
      = l.any (fun a => (minterm a).eval x) := by
  induction l with
  | nil => simp [Circuit.eval]
  | cons a l ih => simp [Circuit.eval, ih, List.any_cons]

/-- **The DNF circuit computes `f` (proved).** -/
theorem eval_dnf_computes (f : (Fin n → Bool) → Bool) : Computes (dnf f) f := by
  intro x
  have hmem_iff : ∀ a, a ∈ enumTrue f ↔ f a = true := by
    intro a
    rw [enumTrue, Finset.mem_toList, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ a, h⟩⟩
  have h : (dnf f).eval x = true ↔ f x = true := by
    rw [dnf, eval_dnf_aux, List.any_eq_true]
    constructor
    · rintro ⟨a, ha, hax⟩
      rw [eval_minterm] at hax
      rw [hax]
      exact (hmem_iff a).1 ha
    · intro hfx
      refine ⟨x, (hmem_iff x).2 hfx, ?_⟩
      rw [eval_minterm]
  by_cases hf : f x = true
  · rw [h.mpr hf, hf]
  · have hf' : f x = false := by simpa using hf
    have hd' : (dnf f).eval x = false := by
      simpa using (fun hh => hf (h.mp hh) : ¬ (dnf f).eval x = true)
    rw [hd', hf']

/-- **UNIVERSALITY (proved).**  Every Boolean function is computed by a circuit, so lands in some
`SIZE n s`. -/
theorem universality (f : (Fin n → Bool) → Bool) : ∃ s, f ∈ Layer8.SIZE n s :=
  ⟨(dnf f).size, dnf f, le_refl _, eval_dnf_computes f⟩

/-- **Minimum circuit size** — a total measure, thanks to universality. -/
noncomputable def minSize (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf { s | f ∈ Layer8.SIZE n s }

theorem minSize_le {n s : ℕ} {f : (Fin n → Bool) → Bool} (hmem : f ∈ Layer8.SIZE n s) :
    minSize n f ≤ s := Nat.sInf_le hmem

theorem mem_SIZE_minSize (n : ℕ) (f : (Fin n → Bool) → Bool) :
    f ∈ Layer8.SIZE n (minSize n f) :=
  Nat.sInf_mem (by obtain ⟨s, hs⟩ := universality f; exact ⟨s, hs⟩)

/-- **The trivial (min-size) separating measure (proved).**  When `L ∉ P/poly`, minimum circuit size is
a `SeparatingMeasure` for `L`. -/
noncomputable def trivialMeasure (L : Layer7.BoolLang) (hnp : ¬ Layer9.Ppoly L) :
    SeparatingMeasure.SeparatingMeasure L where
  I := minSize
  h := fun m => m
  hpoly := ⟨2, 1, 2, fun m => by show m ≤ 2 * m ^ 1 + 2; rw [pow_one]; omega⟩
  circuitBounded := fun _ _ _ hmem => minSize_le hmem
  hardOnTarget := by
    rintro ⟨p, hp, hle⟩
    exact hnp ⟨p, hp, fun m => Layer9.SIZE_mono (hle m) (mem_SIZE_minSize m (L m))⟩

/-- **THE SHARP EQUIVALENCE (proved).**  A separating measure for `L` exists **iff** `L ∉ P/poly`.
Building the target object is exactly as hard as proving the separation — no shortcut, and no obstacle
beyond the separation itself. -/
theorem separatingMeasure_iff_not_ppoly (L : Layer7.BoolLang) :
    Nonempty (SeparatingMeasure.SeparatingMeasure L) ↔ ¬ Layer9.Ppoly L := by
  constructor
  · rintro ⟨sm⟩
    exact SeparatingMeasure.separatingMeasure_not_ppoly sm
  · intro hnp
    exact ⟨trivialMeasure L hnp⟩

end PallLean.Paper93.DeepMath.PathB.UniversalityEquivalence

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalityEquivalence.universality
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalityEquivalence.separatingMeasure_iff_not_ppoly
