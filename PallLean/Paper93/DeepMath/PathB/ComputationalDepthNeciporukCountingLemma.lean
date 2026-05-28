import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFormulaNormalForm

/-!
# Nečiporuk counting lemma — Stage 1: counting normal-form trees

**STATUS: combinatorial core of the counting lemma (Stage 1 of 2).**

We bound the number of distinct normal-form trees (`NF`) with at most `k` leaves.
A tree is serialized by a pre-order token list `encode`, shown injective by a
structural *prefix* lemma (no well-founded parser needed).  Since `encode t` has
length `2 * leaves t - 1 < 2k`, the map `t ↦ (i ↦ (encode t)[i]?)` injects
`{t // leaves t ≤ k}` into `Fin (2k) → Option (Tok n)`, giving

  `#{t : NF n // leaves t ≤ k} ≤ (|Tok n| + 1) ^ (2k)`  with `|Tok n| = 16 + 2n`,

i.e. `2^{O(k log n)}` — the bound that makes Nečiporuk single-exponential.
Stage 2 (separate) bridges this to the block subfunction count and assembles the
formula lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace NF

variable {n : Nat}

/-! ## Pre-order token serialization -/

/-- Serialization alphabet: a binary gate, or a variable literal. -/
inductive Tok (n : Nat) where
  | gate : (Bool -> Bool -> Bool) -> Tok n
  | lit  : Fin n -> Bool -> Tok n
deriving DecidableEq, Fintype

/-- Pre-order serialization of a normal-form tree. -/
def encode : NF n -> List (Tok n)
  | NF.leaf i b => [Tok.lit i b]
  | NF.node g l r => Tok.gate g :: (encode l ++ encode r)

/-- **Prefix lemma** (structural): a serialization determines its tree and the
remaining suffix.  This is the parser-free route to injectivity. -/
theorem encode_prefix_inj :
    ∀ (s₁ s₂ : NF n) (r₁ r₂ : List (Tok n)),
      encode s₁ ++ r₁ = encode s₂ ++ r₂ -> s₁ = s₂ ∧ r₁ = r₂ := by
  intro s₁
  induction s₁ with
  | leaf i b =>
      intro s₂ r₁ r₂ h
      cases s₂ with
      | leaf i' b' =>
          simp only [encode, List.cons_append, List.nil_append, List.cons.injEq,
            Tok.lit.injEq] at h
          exact ⟨by rw [h.1.1, h.1.2], h.2⟩
      | node g l r =>
          simp only [encode, List.cons_append, List.nil_append, List.cons.injEq,
            reduceCtorEq, false_and] at h
  | node g₁ l₁ r₁' ihl ihr =>
      intro s₂ R₁ R₂ h
      cases s₂ with
      | leaf i' b' =>
          simp only [encode, List.cons_append, List.nil_append, List.cons.injEq,
            reduceCtorEq, false_and] at h
      | node g₂ l₂ r₂' =>
          simp only [encode, List.cons_append, List.cons.injEq, Tok.gate.injEq] at h
          obtain ⟨hg, htail⟩ := h
          rw [List.append_assoc, List.append_assoc] at htail
          obtain ⟨hl, hrest⟩ := ihl l₂ (encode r₁' ++ R₁) (encode r₂' ++ R₂) htail
          obtain ⟨hr, hR⟩ := ihr r₂' R₁ R₂ hrest
          exact ⟨by rw [hg, hl, hr], hR⟩

theorem encode_injective : Function.Injective (encode : NF n -> List (Tok n)) := by
  intro s₁ s₂ h
  exact (encode_prefix_inj s₁ s₂ [] [] (by rw [List.append_nil, List.append_nil]; exact h)).1

/-- `encode t` has length `2 * leaves t - 1` (stated without subtraction). -/
theorem encode_length (t : NF n) : (encode t).length + 1 = 2 * NF.leaves t := by
  induction t with
  | leaf i b => simp [encode, NF.leaves]
  | node g l r ihl ihr =>
      simp only [encode, NF.leaves, List.length_cons, List.length_append]
      omega

theorem encode_length_lt (t : NF n) {k : Nat} (hk : NF.leaves t ≤ k) :
    (encode t).length < 2 * k := by
  have h := encode_length t
  omega

/-! ## Padded code and injection -/

/-- Pad a tree's serialization into a fixed-width code. -/
def enc2 (k : Nat) (t : NF n) : Fin (2 * k) -> Option (Tok n) :=
  fun i => (encode t)[(i : Nat)]?

theorem enc2_injOn (k : Nat) {t₁ t₂ : NF n}
    (h1 : NF.leaves t₁ ≤ k) (h2 : NF.leaves t₂ ≤ k)
    (h : enc2 k t₁ = enc2 k t₂) : t₁ = t₂ := by
  apply encode_injective
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 2 * k
  · have := congrFun h ⟨j, hj⟩
    simpa [enc2] using this
  · have e1 := encode_length_lt t₁ h1
    have e2 := encode_length_lt t₂ h2
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ## Cardinality bound on bounded-leaf trees -/

noncomputable instance fintypeNFle (k : Nat) :
    Fintype {t : NF n // NF.leaves t ≤ k} :=
  Fintype.ofInjective (fun st => enc2 k st.1)
    (fun a b hab => Subtype.ext (enc2_injOn k a.2 b.2 hab))

/-- **Tree-count bound.**  At most `(|Tok n|+1)^(2k)` normal-form trees have `≤ k`
leaves, i.e. `2^{O(k log n)}` since `|Tok n| = 16 + 2n`. -/
theorem nf_card_le (k : Nat) :
    Fintype.card {t : NF n // NF.leaves t ≤ k}
      ≤ (Fintype.card (Tok n) + 1) ^ (2 * k) := by
  calc
    Fintype.card {t : NF n // NF.leaves t ≤ k}
        ≤ Fintype.card (Fin (2 * k) -> Option (Tok n)) :=
          Fintype.card_le_of_injective (fun st => enc2 k st.1)
            (fun a b hab => Subtype.ext (enc2_injOn k a.2 b.2 hab))
    _ = (Fintype.card (Tok n) + 1) ^ (2 * k) := by
          rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]

/-! ## Kernel-only trace -/

#print axioms encode_injective
#print axioms nf_card_le

end NF

end PallLean.Paper93.DeepMath.PathB
