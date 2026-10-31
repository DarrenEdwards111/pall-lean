import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA6a

/-!
# Shrinkage brick A6b: THE COUNTING LOWER BOUND

Pigeonhole: there are `2^(2^k)` Boolean functions on `k` bits but only
`≤ (2B+1)·|Tok|^(2B)` formulas of size `< B`, so some function is hard:

* `Tok_card` — the alphabet has `2k + 4` symbols;
* `encList` — pad a bounded list into `Fin (L+1) × (Fin L → Tok)` (injective
  on lists of length `≤ L`);
* **`exists_hard` (proved)** — if
  `(2B+1)·|Tok k|^(2B) < 2^(2^k)` then `∃ f, B ≤ dmsizeC f`;
* **`exists_hard_card` (proved)** — the same with `|Tok k|` spelled `2k+4`.

The witness formula of every function is canonical (constant-free after
`simpC`), so its serialization has length `≤ 2·L₀ + 1`; injectivity of `ser`
plus the padding gives the count.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Alphabet cardinality -/

theorem Tok_card (k : ℕ) : Fintype.card (Tok k) = 2 * k + 4 := by
  simp only [Tok, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  ring

/-! ### List padding -/

/-- Pad a list into a fixed finite product; injective on lists of length ≤ L. -/
def encList {k : ℕ} (L : ℕ) (l : List (Tok k)) :
    Fin (L + 1) × (Fin L → Tok k) :=
  (⟨min l.length L, by omega⟩, fun i => l.getD i.val (Sum.inl false))

theorem list_eq_of_getD {α : Type*} (l1 l2 : List α) (d : α) (L : ℕ)
    (h1 : l1.length ≤ L) (h2 : l2.length ≤ L) (hlen : l1.length = l2.length)
    (hget : ∀ i, i < L → l1.getD i d = l2.getD i d) : l1 = l2 := by
  apply List.ext_getElem hlen
  intro i hi1 hi2
  have e1 : l1.getD i d = l1[i] := List.getD_eq_getElem l1 d hi1
  have e2 : l2.getD i d = l2[i] := List.getD_eq_getElem l2 d hi2
  have := hget i (by omega)
  rw [e1, e2] at this
  exact this

theorem encList_inj {k : ℕ} (L : ℕ) {l1 l2 : List (Tok k)}
    (h1 : l1.length ≤ L) (h2 : l2.length ≤ L)
    (he : encList L l1 = encList L l2) : l1 = l2 := by
  have hfst : min l1.length L = min l2.length L := by
    have := congrArg Prod.fst he
    exact congrArg Fin.val this
  have hlen : l1.length = l2.length := by
    rw [Nat.min_eq_left h1, Nat.min_eq_left h2] at hfst
    exact hfst
  have hsnd : (fun i : Fin L => l1.getD i.val (Sum.inl false))
      = (fun i : Fin L => l2.getD i.val (Sum.inl false)) :=
    congrArg Prod.snd he
  refine list_eq_of_getD l1 l2 (Sum.inl false) L h1 h2 hlen ?_
  intro i hi
  have := congrFun hsnd ⟨i, hi⟩
  exact this

/-! ### The pigeonhole -/

theorem card_functions (k : ℕ) :
    Fintype.card ((Fin k → Bool) → Bool) = 2 ^ (2 ^ k) := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]

theorem card_target (k L : ℕ) :
    Fintype.card (Fin (L + 1) × (Fin L → Tok k)) = (L + 1) * (2 * k + 4) ^ L := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
    Tok_card]

/-- **THE COUNTING LOWER BOUND (proved)**: too few small formulas force a hard
function. -/
theorem exists_hard (k B : ℕ)
    (hnum : (2 * B + 1) * Fintype.card (Tok k) ^ (2 * B) < 2 ^ (2 ^ k)) :
    ∃ f : (Fin k → Bool) → Bool, B ≤ dmsizeC f := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every function has a small canonical witness; encode injectively
  set enc : ((Fin k → Bool) → Bool) → Fin (2 * B + 1) × (Fin (2 * B) → Tok k) :=
    fun f => encList (2 * B) (ser (wit f)) with henc
  have hlen : ∀ f : (Fin k → Bool) → Bool, (ser (wit f)).length ≤ 2 * B := by
    intro f
    have hlt : dmsizeC f < B := hcon f
    have hcan := canonical_ser_len (wit f) (wit_canonical f)
    have hle := wit_lsize0_le f
    omega
  have hinj : Function.Injective enc := by
    intro f₁ f₂ he
    have hser : ser (wit f₁) = ser (wit f₂) :=
      encList_inj (2 * B) (hlen f₁) (hlen f₂) he
    have hwit : wit f₁ = wit f₂ := ser_injective hser
    funext x
    rw [← wit_eval f₁ x, ← wit_eval f₂ x, hwit]
  have hcard := Fintype.card_le_of_injective enc hinj
  rw [card_functions, card_target] at hcard
  have hlt : (2 * B + 1) * (2 * k + 4) ^ (2 * B) < 2 ^ (2 ^ k) := by
    rw [Tok_card] at hnum
    exact hnum
  omega

/-- **The counting lower bound, alphabet size spelled out (proved).** -/
theorem exists_hard_card (k B : ℕ)
    (hnum : (2 * B + 1) * (2 * k + 4) ^ (2 * B) < 2 ^ (2 ^ k)) :
    ∃ f : (Fin k → Bool) → Bool, B ≤ dmsizeC f := by
  apply exists_hard k B
  rw [Tok_card]
  exact hnum

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.exists_hard
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.exists_hard_card
