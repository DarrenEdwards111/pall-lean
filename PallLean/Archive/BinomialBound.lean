/-
  BinomialBound.lean — Combinatorial lower bound on binomial coefficients.
  
  Key lemma: Nat.choose (k * m) k ≥ m ^ k
  Proof by injection: each f : Fin k → Fin m maps to a k-element subset
  {i * m + f(i) : i ∈ Fin k} ⊆ Fin (k * m). Different f give different subsets.
-/
import Mathlib

namespace BinomialBound

open Finset

/-- The injection: a function f : Fin k → Fin m gives a k-element subset of Fin (k*m).
    Element i maps to i*m + f(i), which lies in the block [i*m, (i+1)*m). -/
def functionToSubset (k m : ℕ) (hm : 0 < m) (f : Fin k → Fin m) :
    Finset (Fin (k * m)) :=
  Finset.univ.image (fun i : Fin k =>
    ⟨i.val * m + (f i).val, by
      have hi := i.isLt
      have hfi := (f i).isLt
      calc i.val * m + (f i).val
          < i.val * m + m := by omega
        _ = (i.val + 1) * m := by ring
        _ ≤ k * m := by exact Nat.mul_le_mul_right m (by omega)⟩)

/-- Elements in different blocks are distinct. -/
private theorem block_injective (k m : ℕ) (hm : 0 < m) (f : Fin k → Fin m)
    (i j : Fin k) (h : i.val * m + (f i).val = j.val * m + (f j).val) :
    i = j := by
  have hfi := (f i).isLt  -- f(i) < m
  have hfj := (f j).isLt  -- f(j) < m
  -- (i*m + fi) / m = i (since fi < m)
  -- From h: i*m + fi = j*m + fj, with fi < m and fj < m
  -- Therefore i*m ≤ i*m + fi = j*m + fj < j*m + m = (j+1)*m
  -- And j*m ≤ j*m + fj = i*m + fi < i*m + m = (i+1)*m
  -- So i*m < (j+1)*m and j*m < (i+1)*m, i.e. i < j+1 and j < i+1, i.e. i = j
  exact Fin.ext (by nlinarith)

/-- The subset has exactly k elements. -/
theorem functionToSubset_card (k m : ℕ) (hm : 0 < m) (f : Fin k → Fin m) :
    (functionToSubset k m hm f).card = k := by
  unfold functionToSubset
  rw [Finset.card_image_of_injective _ (fun i j h => by
    simp only [Fin.mk.injEq] at h
    exact block_injective k m hm f i j h)]
  exact Finset.card_fin k

/-- The map from functions to subsets is injective. -/
theorem functionToSubset_injective (k m : ℕ) (hm : 0 < m) :
    Function.Injective (functionToSubset k m hm) := by
  intro f g hfg
  funext i
  -- The i-th element of f's subset is ⟨i*m + f(i), _⟩
  -- Since the subsets are equal, this element must also be in g's subset
  -- Element ⟨i*m + f(i), _⟩ is in f's subset, hence in g's subset
  have hbound : i.val * m + (f i).val < k * m := by
    calc i.val * m + (f i).val < i.val * m + m := by omega
      _ = (i.val + 1) * m := by ring
      _ ≤ k * m := Nat.mul_le_mul_right m (by omega)
  have hmem : (⟨i.val * m + (f i).val, hbound⟩ : Fin (k * m)) ∈ functionToSubset k m hm g := by
    rw [← hfg]
    simp only [functionToSubset, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  simp only [functionToSubset, Finset.mem_image, Finset.mem_univ, true_and] at hmem
  obtain ⟨j, hj⟩ := hmem
  simp only [Fin.mk.injEq] at hj
  -- hj : j.val * m + (g j).val = i.val * m + (f i).val
  -- Both g(j) < m and f(i) < m, so j = i and g(j) = f(i)
  have hgj := (g j).isLt
  have hfi := (f i).isLt
  have hij : j.val = i.val := by nlinarith
  have hjf : (g j).val = (f i).val := by nlinarith
  have hje : j = i := Fin.ext hij
  subst hje
  exact (Fin.ext hjf).symm

/-- **Key lemma**: Nat.choose (k * m) k ≥ m ^ k.
    Each of the m^k functions Fin k → Fin m gives a distinct k-element subset of Fin(k*m). -/
theorem choose_mul_ge_pow (k m : ℕ) (hm : 0 < m) :
    Nat.choose (k * m) k ≥ m ^ k := by
  -- Number of k-element subsets of Fin(k*m) = choose(k*m, k)
  -- Number of functions Fin k → Fin m = m^k
  -- Injection → m^k ≤ choose(k*m, k)
  -- The k-element subsets of {0,...,k*m-1} biject with Finset.powersetCard k (Finset.univ : Finset (Fin (k*m)))
  have hinj := functionToSubset_injective k m hm
  have hcard := functionToSubset_card k m hm
  -- Each image is a member of powersetCard k univ
  have hmem : ∀ f, functionToSubset k m hm f ∈ Finset.powersetCard k (Finset.univ : Finset (Fin (k * m))) := by
    intro f
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hcard f⟩
  -- The image of the injection has card = m^k
  -- And it's a subset of powersetCard k univ which has card = choose(k*m, k)
  have himage_card : (Finset.univ.image (functionToSubset k m hm)).card = Fintype.card (Fin k → Fin m) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at himage_card
  have hle : (Finset.univ.image (functionToSubset k m hm)).card ≤
      (Finset.powersetCard k (Finset.univ : Finset (Fin (k * m)))).card := by
    apply Finset.card_le_card
    intro s hs
    simp at hs
    obtain ⟨f, _, rfl⟩ := hs
    exact hmem f
  rw [Finset.card_powersetCard, Finset.card_fin] at hle
  omega

/-- Corollary: choose L k ≥ (L / k) ^ k when 0 < k. -/
theorem choose_ge_div_pow (L k : ℕ) (hk : 0 < k) :
    Nat.choose L k ≥ (L / k) ^ k := by
  by_cases hm : L / k = 0
  · simp [hm, Nat.zero_pow hk]
  · have hm_pos : 0 < L / k := Nat.pos_of_ne_zero hm
    have hle : k * (L / k) ≤ L := Nat.mul_div_le L k
    calc Nat.choose L k
        ≥ Nat.choose (k * (L / k)) k := Nat.choose_mono k hle
      _ ≥ (L / k) ^ k := choose_mul_ge_pow k (L / k) hm_pos

end BinomialBound
