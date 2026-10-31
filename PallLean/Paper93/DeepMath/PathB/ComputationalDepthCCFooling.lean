import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProtocolModel5

/-!
# Deterministic communication complexity: the fooling-set lower bound

A complete, unconditional classical lower bound built on the protocol tree.  A
protocol computing a function partitions the inputs into transcript-rectangles on
which the function is constant; a *fooling set* is a set no two of whose elements
can share such a rectangle, so it forces at least that many distinct transcripts,
hence that many leaves, hence cost `≥ log₂` of its size.

* **`Computes`** — a protocol computes a Boolean function;
* **`transcripts` / `numLeaves`** — the achieved transcripts and the leaf count;
* **`numLeaves_le_pow_cost` (proved)** — `#leaves ≤ 2^cost`;
* **`transcripts_card_le_numLeaves` (proved)** — `#transcripts ≤ #leaves`;
* **`IsFooling` / `fooling_card_le_transcripts` (proved)** — a fooling set injects
  into the transcripts (the rectangle property does the work);
* **`eq_cost_lower_bound` / `eq_log_lower_bound` (proved)** — `D(EQ) ≥ log₂|ι|`
  via the diagonal fooling set.

This is deterministic communication complexity — a real, classical theorem — not
`P ≠ NP`.  The ceiling of the whole KW arc remains `P ≠ NC¹`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CommProtocol

variable {α β τ : Type*}

/-- The number of leaves of a protocol tree (its size). -/
def numLeaves : Protocol α β τ → ℕ
  | .leaf _ => 1
  | .alice _ l r => numLeaves l + numLeaves r
  | .bob _ l r => numLeaves l + numLeaves r

/-- **Leaf count is at most `2^cost` (proved)**. -/
theorem numLeaves_le_pow_cost (P : Protocol α β τ) : numLeaves P ≤ 2 ^ cost P := by
  induction P with
  | leaf t => simp [numLeaves, cost]
  | alice f l r ihl ihr =>
    simp only [numLeaves, cost]
    have h1 : numLeaves l ≤ 2 ^ (max (cost l) (cost r)) :=
      le_trans ihl (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
    have h2 : numLeaves r ≤ 2 ^ (max (cost l) (cost r)) :=
      le_trans ihr (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
    calc numLeaves l + numLeaves r
        ≤ 2 ^ (max (cost l) (cost r)) + 2 ^ (max (cost l) (cost r)) := Nat.add_le_add h1 h2
      _ = 2 ^ (1 + max (cost l) (cost r)) := by rw [pow_add, pow_one, two_mul]
  | bob g l r ihl ihr =>
    simp only [numLeaves, cost]
    have h1 : numLeaves l ≤ 2 ^ (max (cost l) (cost r)) :=
      le_trans ihl (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
    have h2 : numLeaves r ≤ 2 ^ (max (cost l) (cost r)) :=
      le_trans ihr (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
    calc numLeaves l + numLeaves r
        ≤ 2 ^ (max (cost l) (cost r)) + 2 ^ (max (cost l) (cost r)) := Nat.add_le_add h1 h2
      _ = 2 ^ (1 + max (cost l) (cost r)) := by rw [pow_add, pow_one, two_mul]

/-- A protocol computes a Boolean function `F`. -/
def Computes (P : Protocol α β Bool) (F : α → β → Bool) : Prop := ∀ x y, run P x y = F x y

/-- A **fooling set** for `F` with value `b`: every element evaluates to `b`, and no
two distinct elements can lie in a common `F`-monochromatic rectangle. -/
def IsFooling (F : α → β → Bool) (S : Finset (α × β)) (b : Bool) : Prop :=
  (∀ p ∈ S, F p.1 p.2 = b) ∧
  (∀ p ∈ S, ∀ q ∈ S, p ≠ q → F p.1 q.2 ≠ b ∨ F q.1 p.2 ≠ b)

variable [Fintype α] [Fintype β]

/-- The set of transcripts a protocol produces on some input. -/
def transcripts (P : Protocol α β τ) : Finset (List Bool) :=
  Finset.univ.image (fun p : α × β => trans P p.1 p.2)

/-- **Distinct transcripts are at most the leaf count (proved)**. -/
theorem transcripts_card_le_numLeaves (P : Protocol α β τ) :
    (transcripts P).card ≤ numLeaves P := by
  induction P with
  | leaf t =>
    have hsub : transcripts (Protocol.leaf t : Protocol α β τ) ⊆ {[]} := by
      intro s hs
      simp only [transcripts, Finset.mem_image] at hs
      obtain ⟨p, _, hp⟩ := hs
      simp only [trans] at hp
      exact Finset.mem_singleton.mpr hp.symm
    calc (transcripts (Protocol.leaf t : Protocol α β τ)).card
        ≤ ({[]} : Finset (List Bool)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
      _ = numLeaves (Protocol.leaf t) := by simp [numLeaves]
  | alice f l r ihl ihr =>
    have hsub : transcripts (Protocol.alice f l r) ⊆
        (transcripts r).image (List.cons true) ∪ (transcripts l).image (List.cons false) := by
      intro s hs
      simp only [transcripts, Finset.mem_image] at hs
      obtain ⟨p, _, hp⟩ := hs
      simp only [trans] at hp
      cases hfx : f p.1 with
      | true =>
        rw [hfx] at hp; simp only [cond_true] at hp
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨trans r p.1 p.2, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, hp⟩)
      | false =>
        rw [hfx] at hp; simp only [cond_false] at hp
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨trans l p.1 p.2, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, hp⟩)
    calc (transcripts (Protocol.alice f l r)).card
        ≤ ((transcripts r).image (List.cons true) ∪ (transcripts l).image (List.cons false)).card :=
          Finset.card_le_card hsub
      _ ≤ ((transcripts r).image (List.cons true)).card
            + ((transcripts l).image (List.cons false)).card := Finset.card_union_le _ _
      _ ≤ (transcripts r).card + (transcripts l).card :=
          Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ ≤ numLeaves r + numLeaves l := Nat.add_le_add ihr ihl
      _ = numLeaves (Protocol.alice f l r) := by simp only [numLeaves]; omega
  | bob g l r ihl ihr =>
    have hsub : transcripts (Protocol.bob g l r) ⊆
        (transcripts r).image (List.cons true) ∪ (transcripts l).image (List.cons false) := by
      intro s hs
      simp only [transcripts, Finset.mem_image] at hs
      obtain ⟨p, _, hp⟩ := hs
      simp only [trans] at hp
      cases hgy : g p.2 with
      | true =>
        rw [hgy] at hp; simp only [cond_true] at hp
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨trans r p.1 p.2, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, hp⟩)
      | false =>
        rw [hgy] at hp; simp only [cond_false] at hp
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨trans l p.1 p.2, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, hp⟩)
    calc (transcripts (Protocol.bob g l r)).card
        ≤ ((transcripts r).image (List.cons true) ∪ (transcripts l).image (List.cons false)).card :=
          Finset.card_le_card hsub
      _ ≤ ((transcripts r).image (List.cons true)).card
            + ((transcripts l).image (List.cons false)).card := Finset.card_union_le _ _
      _ ≤ (transcripts r).card + (transcripts l).card :=
          Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ ≤ numLeaves r + numLeaves l := Nat.add_le_add ihr ihl
      _ = numLeaves (Protocol.bob g l r) := by simp only [numLeaves]; omega

/-- **The fooling-set lemma (proved)**: a fooling set injects into the transcripts,
so it forces at least that many distinct communication patterns. -/
theorem fooling_card_le_transcripts {P : Protocol α β Bool} {F : α → β → Bool}
    {S : Finset (α × β)} {b : Bool} (hP : Computes P F) (hS : IsFooling F S b) :
    S.card ≤ (transcripts P).card := by
  apply Finset.card_le_card_of_injOn (fun p => trans P p.1 p.2)
  · intro p _
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
  · intro p hp q hq hfeq
    by_contra hne
    obtain ⟨hval, hfool⟩ := hS
    have hpS : p ∈ S := hp
    have hqS : q ∈ S := hq
    have e1 : trans P p.1 q.2 = trans P q.1 q.2 := trans_cutPaste P p.1 p.2 q.1 q.2 hfeq
    have e2 : trans P q.1 p.2 = trans P p.1 p.2 := trans_cutPaste P q.1 q.2 p.1 p.2 hfeq.symm
    have r1 : run P p.1 q.2 = run P q.1 q.2 := run_eq_of_trans_eq P p.1 q.2 q.1 q.2 e1
    have r2 : run P q.1 p.2 = run P p.1 p.2 := run_eq_of_trans_eq P q.1 p.2 p.1 p.2 e2
    have f1 : F p.1 q.2 = b := by rw [← hP p.1 q.2, r1, hP q.1 q.2, hval q hqS]
    have f2 : F q.1 p.2 = b := by rw [← hP q.1 p.2, r2, hP p.1 p.2, hval p hpS]
    rcases hfool p hpS q hqS hne with h | h
    · exact h f1
    · exact h f2

/-! ## The classic lower bound: `D(EQ) ≥ log₂ |domain|` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Computing `EQ` needs at least `|ι|` transcripts (proved)**, via the diagonal
fooling set. -/
theorem eq_needs_transcripts {P : Protocol ι ι Bool}
    (hP : Computes P (fun a b => decide (a = b))) :
    Fintype.card ι ≤ (transcripts P).card := by
  have hfool : IsFooling (fun a b => decide (a = b))
      (Finset.univ.image (fun a : ι => (a, a))) true := by
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [Finset.mem_image] at hp
      obtain ⟨a, -, rfl⟩ := hp
      simp
    · intro p hp q hq hne
      simp only [Finset.mem_image] at hp hq
      obtain ⟨a, -, rfl⟩ := hp
      obtain ⟨a', -, rfl⟩ := hq
      have haa : a ≠ a' := fun h => hne (by rw [h])
      left
      simpa using haa
  have hinj : Function.Injective (fun a : ι => (a, a)) := fun a a' h => (Prod.ext_iff.mp h).1
  have hcard : (Finset.univ.image (fun a : ι => (a, a))).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  calc Fintype.card ι = (Finset.univ.image (fun a : ι => (a, a))).card := hcard.symm
    _ ≤ (transcripts P).card := fooling_card_le_transcripts hP hfool

/-- **`D(EQ) ≥ log₂ |ι|` in size form (proved)**: `|ι| ≤ 2^cost`. -/
theorem eq_cost_lower_bound {P : Protocol ι ι Bool}
    (hP : Computes P (fun a b => decide (a = b))) :
    Fintype.card ι ≤ 2 ^ cost P :=
  le_trans (eq_needs_transcripts hP)
    (le_trans (transcripts_card_le_numLeaves P) (numLeaves_le_pow_cost P))

/-- **`D(EQ) ≥ log₂ |ι|` in log form (proved)**. -/
theorem eq_log_lower_bound {P : Protocol ι ι Bool}
    (hP : Computes P (fun a b => decide (a = b))) :
    Nat.log 2 (Fintype.card ι) ≤ cost P := by
  calc Nat.log 2 (Fintype.card ι)
      ≤ Nat.log 2 (2 ^ cost P) := Nat.log_mono_right (eq_cost_lower_bound hP)
    _ = cost P := Nat.log_pow (by norm_num : (1 : ℕ) < 2) (cost P)

end PallLean.Paper93.DeepMath.PathB.CommProtocol

#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.fooling_card_le_transcripts
#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.eq_cost_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.eq_log_lower_bound
