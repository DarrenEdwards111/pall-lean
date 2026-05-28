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

/-!
## Stage 2: bridge to the block subfunction count and the formula lower bound
-/

open NF

/-- The distinct residual functions of `F` on a block `S` (fix the outside vars to
each `α`).  Its cardinality is the block subfunction count. -/
noncomputable def blockResiduals (S : Finset (Fin n)) (F : BFormula n) :
    Finset ((Fin n -> Bool) -> Bool) := by
  classical
  exact Finset.univ.image
    (fun α : Fin n -> Bool => fun x => BFormula.eval F (fun i => if i ∈ S then x i else α i))

/-- Decode a constant tag / normal-form tree to the function it computes. -/
def evalRepr (k : Nat) :
    (Bool ⊕ {t : NF n // NF.leaves t ≤ k}) -> ((Fin n -> Bool) -> Bool)
  | Sum.inl c => fun _ => c
  | Sum.inr t => NF.eval t.1

/-- **Bridge + count.**  The block subfunction count is at most
`2 ^ (2 · clog₂(|Tok|+1) · leavesIn S F + 2)` — the genuine Nečiporuk per-block
capacity bound from real formula semantics. -/
theorem blockResiduals_card_le (S : Finset (Fin n)) (F : BFormula n) :
    (blockResiduals S F).card
      ≤ 2 ^ (2 * Nat.clog 2 (Fintype.card (NF.Tok n) + 1) * BFormula.leavesIn S F + 2) := by
  classical
  set k := BFormula.leavesIn S F with hk
  set T := Fintype.card (NF.Tok n) with hT
  set Cn := Nat.clog 2 (T + 1) with hCn
  -- every residual is decoded from a constant tag or a small tree
  have hsub : blockResiduals S F ⊆ Finset.univ.image (evalRepr k) := by
    intro φ hφ
    simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and] at hφ
    obtain ⟨α, hα⟩ := hφ
    obtain ⟨G, hGleaf, hGeval⟩ := BFormula.block_realization S α F
    have hφG : φ = BFormula.eval G := by
      funext x
      have h1 := congrFun hα x
      have h2 := hGeval x
      simp only [] at h1
      exact (h2.trans h1).symm
    rw [Finset.mem_image]
    cases hnG : norm G with
    | inl c =>
        refine ⟨Sum.inl c, Finset.mem_univ _, ?_⟩
        funext x
        have hs := seval_norm G x
        rw [hnG] at hs
        simp only [NF.seval] at hs
        simp only [evalRepr]
        rw [hφG]; exact hs
    | inr t =>
        have hleaf : NF.leaves t ≤ k :=
          Nat.le_trans (leaves_norm_le G hnG) hGleaf
        refine ⟨Sum.inr ⟨t, hleaf⟩, Finset.mem_univ _, ?_⟩
        funext x
        have hs := seval_norm G x
        rw [hnG] at hs
        simp only [NF.seval] at hs
        simp only [evalRepr]
        rw [hφG]; exact hs
  -- card ≤ |Bool ⊕ {trees}| = 2 + #trees ≤ 2 + (T+1)^(2k)
  have hcard1 : (blockResiduals S F).card
      ≤ 2 + Fintype.card {t : NF n // NF.leaves t ≤ k} := by
    calc
      (blockResiduals S F).card
          ≤ (Finset.univ.image (evalRepr k)).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Bool ⊕ {t : NF n // NF.leaves t ≤ k})).card :=
            Finset.card_image_le
      _ = Fintype.card (Bool ⊕ {t : NF n // NF.leaves t ≤ k}) := Finset.card_univ
      _ = 2 + Fintype.card {t : NF n // NF.leaves t ≤ k} := by
            rw [Fintype.card_sum, Fintype.card_bool]
  have hnf : Fintype.card {t : NF n // NF.leaves t ≤ k} ≤ (T + 1) ^ (2 * k) :=
    NF.nf_card_le k
  -- arithmetic: 2 + (T+1)^(2k) ≤ 2^(2 Cn k + 2)
  have hTpow : (T + 1) ^ (2 * k) ≤ 2 ^ (Cn * (2 * k)) := by
    calc (T + 1) ^ (2 * k)
        ≤ (2 ^ Cn) ^ (2 * k) := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) (T + 1)) (2 * k)
      _ = 2 ^ (Cn * (2 * k)) := by rw [← pow_mul]
  have hfin : (2 : Nat) + 2 ^ (Cn * (2 * k)) ≤ 2 ^ (Cn * (2 * k) + 2) := by
    have hp : 1 ≤ 2 ^ (Cn * (2 * k)) := Nat.one_le_two_pow
    have he : 2 ^ (Cn * (2 * k) + 2) = 4 * 2 ^ (Cn * (2 * k)) := by rw [pow_add]; ring
    omega
  have hexp : Cn * (2 * k) + 2 = 2 * Cn * k + 2 := by ring
  calc
    (blockResiduals S F).card
        ≤ 2 + Fintype.card {t : NF n // NF.leaves t ≤ k} := hcard1
    _ ≤ 2 + (T + 1) ^ (2 * k) := by omega
    _ ≤ 2 + 2 ^ (Cn * (2 * k)) := by omega
    _ ≤ 2 ^ (Cn * (2 * k) + 2) := hfin
    _ = 2 ^ (2 * Cn * k + 2) := by rw [hexp]

/-- **Concrete Nečiporuk formula lower bound.**  For any `B₂` formula `F` and any
partition of the variables into disjoint blocks covering everything, the number of
variable leaves satisfies

  `Σ_i log₂(blockSubfunctionCount_i) ≤ 2·clog₂(|Tok|+1)·litCount F + 2·#blocks`,

i.e. `litCount F ≥ (Σ_i log₂ c_i − 2·#blocks) / (2·clog₂(16+2n+1))` — a genuine,
fully proved formula-size lower bound of the Nečiporuk shape (`n²/log n` when the
`c_i` are large on `Θ(n/log n)` blocks).  No carried hypotheses. -/
theorem neciporuk_formula_lower_bound {ι : Type*}
    (blocks : Finset ι) (S : ι -> Finset (Fin n)) (F : BFormula n)
    (hdisj : (blocks : Set ι).PairwiseDisjoint S)
    (hcover : blocks.biUnion S = Finset.univ) :
    ∑ i ∈ blocks, Nat.log 2 ((blockResiduals (S i) F).card)
      ≤ 2 * Nat.clog 2 (Fintype.card (NF.Tok n) + 1) * BFormula.litCount F
        + 2 * blocks.card := by
  set Cn := Nat.clog 2 (Fintype.card (NF.Tok n) + 1) with hCn
  have key := neciporuk_sum_lower_bound blocks
    (fun i => (blockResiduals (S i) F).card)
    (fun i => 2 * Cn * BFormula.leavesIn (S i) F + 2)
    (∑ i ∈ blocks, (2 * Cn * BFormula.leavesIn (S i) F + 2))
    rfl
    (fun i _ => blockResiduals_card_le (S i) F)
  have hsum : ∑ i ∈ blocks, (2 * Cn * BFormula.leavesIn (S i) F + 2)
      = 2 * Cn * BFormula.litCount F + 2 * blocks.card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        BFormula.sum_leavesIn_of_partition blocks S F hdisj hcover,
        Finset.sum_const, smul_eq_mul, Nat.mul_comm blocks.card 2]
  rw [hsum] at key
  exact key

/-! ## Kernel-only trace -/

#print axioms blockResiduals_card_le
#print axioms neciporuk_formula_lower_bound

end PallLean.Paper93.DeepMath.PathB
