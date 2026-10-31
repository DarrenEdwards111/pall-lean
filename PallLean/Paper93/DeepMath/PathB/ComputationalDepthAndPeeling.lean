import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDegreeCertificateAnd

/-!
# Closing the general AND-family log bound via the peeling

The concrete instances of `DegreeCertificateAnd` are here made uniform in `n`.  The engine is the
**peeling lemma**: differencing the `AND-except-T` function in a fresh unit direction `i` deletes one
more coordinate, `Δ_{eᵢ}(andExcept T) = andExcept (insert i T)`.  Iterating over a nodup list of
directions builds up `andExcept` of that whole coordinate set, which is `1` at the all-true point.

* **`andExcept`** — `∏_{j ∉ T} x_j`, i.e. the AND of the coordinates outside `T`.
* **`peeling` (proved)** — `Δ_{eᵢ}(andExcept T) = andExcept (insert i T)` for `i ∉ T`.
* **`iterDelta_map_unitVec` (proved)** — iterating the peeling over a nodup, `T`-disjoint list `L`
  gives `andExcept (T ∪ L.toFinset)`.
* **`andN_needs_nonlinear` (proved)** — **the general family bound**: for every `n` and `m` with
  `2^m + 1 ≤ n`, any circuit computing the `n`-bit AND has more than `m` nonlinear gates.

So the log lower bound `nlCount > m` for `2^m < n` holds **uniformly in `n`**, unconditionally.

**Honest scope.**  A real, uniform, unconditional `log₂`-lower bound on the nonlinear-gate count of AND
circuits.  Still only logarithmic (the AND actually needs `n-1`), and still the nonlinear-gate count,
not total size.  `cost_super`'s full Uhlig bound remains the open wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AndPeeling

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.DegreeCalculus
open PallLean.Paper93.DeepMath.PathB.WireDegreeBound
open PallLean.Paper93.DeepMath.PathB.DegreeCertificate
open PallLean.Paper93.DeepMath.PathB.DegreeCertificateAnd

variable {n : ℕ}

/-- The AND of the coordinates *outside* `T`. -/
def andExcept (T : Finset (Fin n)) : (Fin n → Bool) → Bool :=
  fun x => decide (∀ j, j ∉ T → x j = true)

/-- `andN` is `andExcept ∅`. -/
theorem andN_eq_andExcept_empty : (andN : (Fin n → Bool) → Bool) = andExcept ∅ := by
  funext x; simp [andN, andExcept]

/-- Splitting the `AND-except-T` condition off a fresh coordinate `i ∉ T`. -/
theorem forall_notMem_split {T : Finset (Fin n)} {i : Fin n} (hi : i ∉ T) (y : Fin n → Bool) :
    (∀ j, j ∉ T → y j = true) ↔ (y i = true ∧ ∀ j, j ∉ insert i T → y j = true) := by
  constructor
  · intro h
    exact ⟨h i hi, fun j hj => h j (fun hjT => hj (Finset.mem_insert_of_mem hjT))⟩
  · rintro ⟨hyi, h⟩ j hjT
    by_cases hji : j = i
    · subst hji; exact hyi
    · exact h j (fun hjins => (Finset.mem_insert.mp hjins).elim hji hjT)

/-- **The peeling lemma (proved):** differencing `andExcept T` in a fresh direction `i` deletes one
more coordinate. -/
theorem peeling {T : Finset (Fin n)} {i : Fin n} (hi : i ∉ T) :
    Delta (unitVec i) (andExcept T) = andExcept (insert i T) := by
  have hconj : ∀ (a : Bool) (Q : Prop) [Decidable Q], decide (a = true ∧ Q) = (a && decide Q) := by
    intro a Q _; cases a <;> simp
  funext x
  have hui : unitVec i i = true := by simp [unitVec]
  have hflip : (∀ j, j ∉ insert i T → Bool.xor (x j) (unitVec i j) = true)
             ↔ (∀ j, j ∉ insert i T → x j = true) := by
    have haux : ∀ j, j ∉ insert i T → unitVec i j = false := by
      intro j hj
      have hji : j ≠ i := fun e => hj (e ▸ Finset.mem_insert_self i T)
      simp only [unitVec]; exact decide_eq_false hji
    constructor
    · intro h j hj; have hh := h j hj; rw [haux j hj, Bool.xor_false] at hh; exact hh
    · intro h j hj; rw [haux j hj, Bool.xor_false]; exact h j hj
  simp only [Delta, andExcept, forall_notMem_split hi, hui, Bool.xor_true, hflip, hconj]
  cases x i <;> simp

/-- Iterating the peeling over a nodup, `T`-disjoint list builds up `andExcept`. -/
theorem iterDelta_map_unitVec :
    ∀ (L : List (Fin n)) (T : Finset (Fin n)), L.Nodup → (∀ i ∈ L, i ∉ T) →
      iterDelta (L.map unitVec) (andExcept T) = andExcept (T ∪ L.toFinset) := by
  intro L
  induction L with
  | nil => intro T _ _; simp [iterDelta]
  | cons a L ih =>
    intro T hnodup hdisj
    rw [List.map_cons, iterDelta, peeling (hdisj a (by simp))]
    have haL : a ∉ L := (List.nodup_cons.mp hnodup).1
    have hLnodup : L.Nodup := (List.nodup_cons.mp hnodup).2
    have hdisj' : ∀ i ∈ L, i ∉ insert a T := by
      intro i hi
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun e => haL (e ▸ hi), hdisj i (List.mem_cons_of_mem _ hi)⟩
    rw [ih (insert a T) hLnodup hdisj']
    congr 1
    ext j
    simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons, Finset.mem_insert]
    tauto

/-- **The general AND-family log bound (proved).**  For every `n` and `m` with `2^m + 1 ≤ n`, any
circuit computing the `n`-bit AND has more than `m` nonlinear gates. -/
theorem andN_needs_nonlinear (m : ℕ) (hnm : 2 ^ m + 1 ≤ n) (c : List (CGate n))
    (hc : output c = andN) : m < nlCount c := by
  set L : List (Fin n) := (List.finRange n).take (2 ^ m + 1) with hL
  have hlen : (L.map unitVec).length = 2 ^ m + 1 := by
    rw [List.length_map, hL, List.length_take, List.length_finRange]
    omega
  have hnodup : L.Nodup := (List.nodup_finRange n).sublist (List.take_sublist _ _)
  have hdisj : ∀ i ∈ L, i ∉ (∅ : Finset (Fin n)) := by intro i _; simp
  have hcert : iterDelta (L.map unitVec) (output c) (fun _ => true) = true := by
    rw [hc, andN_eq_andExcept_empty, iterDelta_map_unitVec L ∅ hnodup hdisj]
    simp [andExcept]
  exact highDegree_needs_nonlinear c m (L.map unitVec) (fun _ => true) hlen hcert

end PallLean.Paper93.DeepMath.PathB.AndPeeling

#print axioms PallLean.Paper93.DeepMath.PathB.AndPeeling.peeling
#print axioms PallLean.Paper93.DeepMath.PathB.AndPeeling.andN_needs_nonlinear
