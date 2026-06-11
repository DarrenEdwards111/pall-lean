import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8Shannon

/-!
# Layer 8 (general circuits, R1b) — the circuit count, and the unconditional Shannon bound

Discharges the counting hypothesis of `exists_hard_function` (R1) by a **single-exponential** bound on the
number of size-`≤ s` circuits, via preorder serialization + unique readability (no Catalan recursion):

* `toTokens` — preorder tokenization `Circuit n → List (Tok n)`, `Tok n := Fin n ⊕ Bool ⊕ Fin 3`.
* `toTokens_inj` — **unique readability**: the serialization is injective (structural induction with the
  strengthened append statement).
* `card_circuits_size_le_pow` — `card {c // c.size ≤ s} ≤ (n+6)^s`, by the padded-array injection
  `c ↦ (i ↦ (toTokens c)[i]?) : Fin s → Option (Tok n)`.
* `shannon_counting_bound` — **unconditional given the threshold**: if `(n+6)^s < 2^{2ⁿ}` then some
  Boolean function needs circuit size `> s` (`∉ SIZE n s`).  Combined with `exists_hard_function`.

Still **nonconstructive** (names no explicit hard function); the explicit super-polynomial frontier remains
open and fenced (`SCOPE_LAYER8_GENERAL_CIRCUITS.md`).  At `s ≈ 2ⁿ/(n+6)` the hypothesis `(n+6)^s < 2^{2ⁿ}`
holds, giving the classical exponential Shannon bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer8

open Finset

/-- Preorder token alphabet: input index / constant bit / one of `¬,∧,∨`. -/
abbrev Tok (n : ℕ) := Fin n ⊕ Bool ⊕ Fin 3

/-- Preorder serialization of a circuit. -/
def toTokens {n : ℕ} : Circuit n → List (Tok n)
  | .input i => [Sum.inl i]
  | .const b => [Sum.inr (Sum.inl b)]
  | .not c => Sum.inr (Sum.inr 0) :: toTokens c
  | .and c d => Sum.inr (Sum.inr 1) :: (toTokens c ++ toTokens d)
  | .or c d => Sum.inr (Sum.inr 2) :: (toTokens c ++ toTokens d)

theorem toTokens_length {n : ℕ} (c : Circuit n) : (toTokens c).length = c.size := by
  induction c with
  | input i => rfl
  | const b => rfl
  | not c ih => simp [toTokens, Circuit.size, ih]
  | and c d ihc ihd => simp [toTokens, Circuit.size, ihc, ihd]
  | or c d ihc ihd => simp [toTokens, Circuit.size, ihc, ihd]

set_option maxHeartbeats 800000 in
/-- **Unique readability (append form).**  `toTokens c₁ ++ r₁ = toTokens c₂ ++ r₂ → c₁ = c₂ ∧ r₁ = r₂`. -/
theorem toTokens_append_inj {n : ℕ} (c₁ : Circuit n) :
    ∀ (c₂ : Circuit n) (r₁ r₂ : List (Tok n)),
      toTokens c₁ ++ r₁ = toTokens c₂ ++ r₂ → c₁ = c₂ ∧ r₁ = r₂ := by
  induction c₁ with
  | input i =>
      intro c₂ r₁ r₂ h
      cases c₂ with
      | input j =>
          simp only [toTokens, List.singleton_append, List.cons.injEq, Sum.inl.injEq] at h
          obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
      | _ => simp only [toTokens, List.singleton_append, List.cons_append, List.cons.injEq,
          Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.reduceEq, false_and, and_false] at h
  | const b =>
      intro c₂ r₁ r₂ h
      cases c₂ with
      | const b' =>
          simp only [toTokens, List.singleton_append, List.cons.injEq, Sum.inr.injEq,
            Sum.inl.injEq] at h
          obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
      | _ => simp only [toTokens, List.singleton_append, List.cons_append, List.cons.injEq,
          Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.reduceEq, false_and, and_false] at h
  | not c ih =>
      intro c₂ r₁ r₂ h
      cases c₂ with
      | not c' =>
          simp only [toTokens, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨rfl, hr⟩ := ih c' r₁ r₂ h; exact ⟨rfl, hr⟩
      | _ => simp only [toTokens, List.singleton_append, List.cons_append, List.cons.injEq,
          Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.reduceEq, false_and, and_false] at h
  | and c d ihc ihd =>
      intro c₂ r₁ r₂ h
      cases c₂ with
      | and c' d' =>
          simp only [toTokens, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
          obtain ⟨rfl, hr⟩ := ihc c' (toTokens d ++ r₁) (toTokens d' ++ r₂) h
          obtain ⟨rfl, hr2⟩ := ihd d' r₁ r₂ hr; exact ⟨rfl, hr2⟩
      | _ => simp only [toTokens, List.singleton_append, List.cons_append, List.cons.injEq,
          Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.reduceEq, false_and, and_false] at h
  | or c d ihc ihd =>
      intro c₂ r₁ r₂ h
      cases c₂ with
      | or c' d' =>
          simp only [toTokens, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
          obtain ⟨rfl, hr⟩ := ihc c' (toTokens d ++ r₁) (toTokens d' ++ r₂) h
          obtain ⟨rfl, hr2⟩ := ihd d' r₁ r₂ hr; exact ⟨rfl, hr2⟩
      | _ => simp only [toTokens, List.singleton_append, List.cons_append, List.cons.injEq,
          Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.reduceEq, false_and, and_false] at h

theorem toTokens_inj {n : ℕ} : Function.Injective (toTokens : Circuit n → List (Tok n)) := fun c₁ c₂ h =>
  (toTokens_append_inj c₁ c₂ [] [] (by simpa using h)).1

/-- Padded-array encoding of a size-`≤ s` circuit into `Fin s → Option (Tok n)`. -/
def enc {n s : ℕ} (c : {c : Circuit n // c.size ≤ s}) : Fin s → Option (Tok n) :=
  fun i => (toTokens c.1)[i.val]?

theorem enc_inj {n s : ℕ} : Function.Injective (enc (n := n) (s := s)) := by
  rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
  have hlist : toTokens c = toTokens c' := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < s
    · simpa [enc] using congrFun h ⟨k, hk⟩
    · rw [List.getElem?_eq_none (by rw [toTokens_length]; omega),
        List.getElem?_eq_none (by rw [toTokens_length]; omega)]
  exact Subtype.ext (toTokens_inj hlist)

theorem card_circuits_size_le_pow (n s : ℕ) [Fintype {c : Circuit n // c.size ≤ s}] :
    Fintype.card {c : Circuit n // c.size ≤ s} ≤ (n + 6) ^ s := by
  refine le_trans (Fintype.card_le_of_injective enc enc_inj) (le_of_eq ?_)
  have hbase : Fintype.card (Option (Tok n)) = n + 6 := by
    simp [Fintype.card_option, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
  rw [Fintype.card_fun, Fintype.card_fin, hbase]

/-- **Shannon counting lower bound (unconditional given the threshold).**  If `(n+6)^s < 2^{2ⁿ}` then some
Boolean function on `n` bits requires circuit size `> s` (it is not in `SIZE n s`).  Nonconstructive. -/
theorem shannon_counting_bound {n s : ℕ} (hthresh : (n + 6) ^ s < 2 ^ (2 ^ n)) :
    ∃ f : (Fin n → Bool) → Bool, f ∉ SIZE n s := by
  haveI : Fintype {c : Circuit n // c.size ≤ s} := Fintype.ofInjective enc enc_inj
  refine exists_hard_function (Finset.univ.image (Subtype.val : {c : Circuit n // c.size ≤ s} → Circuit n))
    (fun c hc => Finset.mem_image.mpr ⟨⟨c, hc⟩, Finset.mem_univ _, rfl⟩) ?_
  calc (Finset.univ.image (Subtype.val : {c : Circuit n // c.size ≤ s} → Circuit n)).card
      ≤ (Finset.univ : Finset {c : Circuit n // c.size ≤ s}).card := Finset.card_image_le
    _ = Fintype.card {c : Circuit n // c.size ≤ s} := Finset.card_univ
    _ ≤ (n + 6) ^ s := card_circuits_size_le_pow n s
    _ < 2 ^ (2 ^ n) := hthresh

end PallLean.Paper93.DeepMath.PathB.Layer8

#print axioms PallLean.Paper93.DeepMath.PathB.Layer8.toTokens_inj
#print axioms PallLean.Paper93.DeepMath.PathB.Layer8.shannon_counting_bound
