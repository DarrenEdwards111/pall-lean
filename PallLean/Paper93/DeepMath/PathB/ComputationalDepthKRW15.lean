import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW14

/-!
# KRW brick 15: a universal-relation protocol exists, and the CC bracket

Non-vacuity for KRW14: a `U_n` protocol of cost `2n` exists (reveal every
coordinate of both players; a fully-revealed rectangle is a single pair, trivially
solved).  Combined with the lower bound this brackets the universal-relation
communication complexity.

* **`revealAll` (proved)** — revealing a list `cs` of coordinates gives a protocol
  of cost `2·|cs|`, provided every distinct pair in the rectangle differs somewhere
  in `cs`;
* **`uprotocol_exists` (proved)** — `HasUProtocol univ univ (2n)`;
* **`ucc`** and **`ucc_pow2_bracket` (proved)** — for `k ≥ 4`,
  `2^{k-1} - 2 ≤ ucc (2^k) ≤ 2·2^k`: the universal relation has communication
  complexity `Θ(n)` (for `n = 2^k`).

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- **Reveal a list of coordinates (proved)**: cost `2·|cs|`, when every distinct
pair in `A×B` differs somewhere in `cs`. -/
theorem revealAll {n : ℕ} (hn : 0 < n) :
    ∀ (cs : List (Fin n)) (A B : Finset (Fin n → Bool)),
      (∀ x ∈ A, ∀ y ∈ B, x ≠ y → ∃ i ∈ cs, x i ≠ y i) →
      HasUProtocol A B (2 * cs.length) := by
  intro cs
  induction cs with
  | nil =>
    intro A B hyp
    exact HasUProtocol.leaf 0 ⟨0, hn⟩ (fun x hx y hy hxy => absurd (hyp x hx y hy hxy) (by simp))
  | cons c cs' ih =>
    intro A B hyp
    have hlen : 2 * (c :: cs').length = 2 * cs'.length + 1 + 1 := by
      rw [List.length_cons]; ring
    rw [hlen]
    have leafd : ∀ (AA BB : Finset (Fin n → Bool)), (∀ x ∈ AA, x c = true) →
        (∀ y ∈ BB, y c = false) → HasUProtocol AA BB (2 * cs'.length) :=
      fun AA BB hAA hBB => HasUProtocol.leaf _ c (fun x hx y hy _ => by
        rw [hAA x hx, hBB y hy]; decide)
    have leafd' : ∀ (AA BB : Finset (Fin n → Bool)), (∀ x ∈ AA, x c = false) →
        (∀ y ∈ BB, y c = true) → HasUProtocol AA BB (2 * cs'.length) :=
      fun AA BB hAA hBB => HasUProtocol.leaf _ c (fun x hx y hy _ => by
        rw [hAA x hx, hBB y hy]; decide)
    have recEq : ∀ (v : Bool) (AA BB : Finset (Fin n → Bool)),
        (∀ x ∈ AA, x c = v) → (∀ y ∈ BB, y c = v) → AA ⊆ A → BB ⊆ B →
        HasUProtocol AA BB (2 * cs'.length) := by
      intro v AA BB hAA hBB hsubA hsubB
      apply ih
      intro x hx y hy hxy
      obtain ⟨i, hi_mem, hi_ne⟩ := hyp x (hsubA hx) y (hsubB hy) hxy
      refine ⟨i, ?_, hi_ne⟩
      rcases List.mem_cons.mp hi_mem with hic | hic'
      · exfalso; subst hic; rw [hAA x hx, hBB y hy] at hi_ne; exact hi_ne rfl
      · exact hic'
    refine HasUProtocol.alice (fun z => z c) ?_ ?_
    · refine HasUProtocol.bob (fun z => z c) ?_ ?_
      · exact recEq false _ _ (fun x hx => (Finset.mem_filter.mp hx).2)
          (fun y hy => (Finset.mem_filter.mp hy).2) (Finset.filter_subset _ _)
          (Finset.filter_subset _ _)
      · exact leafd' _ _ (fun x hx => (Finset.mem_filter.mp hx).2)
          (fun y hy => (Finset.mem_filter.mp hy).2)
    · refine HasUProtocol.bob (fun z => z c) ?_ ?_
      · exact leafd _ _ (fun x hx => (Finset.mem_filter.mp hx).2)
          (fun y hy => (Finset.mem_filter.mp hy).2)
      · exact recEq true _ _ (fun x hx => (Finset.mem_filter.mp hx).2)
          (fun y hy => (Finset.mem_filter.mp hy).2) (Finset.filter_subset _ _)
          (Finset.filter_subset _ _)

/-- **A universal-relation protocol of cost `2n` exists (proved)**. -/
theorem uprotocol_exists {n : ℕ} (hn : 0 < n) :
    HasUProtocol (Finset.univ : Finset (Fin n → Bool)) Finset.univ (2 * n) := by
  have h := revealAll hn (List.finRange n) Finset.univ Finset.univ (fun x _ y _ hxy => by
    by_contra hc
    push_neg at hc
    exact hxy (funext (fun i => hc i (List.mem_finRange i))))
  rwa [List.length_finRange] at h

/-- Universal-relation communication complexity: least protocol cost on `Fin n`. -/
noncomputable def ucc (n : ℕ) : ℕ :=
  sInf {d | HasUProtocol (Finset.univ : Finset (Fin n → Bool)) Finset.univ d}

/-- **THE UNIVERSAL RELATION IS `Θ(n)` (proved)**: `2^{k-1} - 2 ≤ ucc (2^k) ≤ 2·2^k`. -/
theorem ucc_pow2_bracket (k : ℕ) (hk : 4 ≤ k) :
    2 ^ (k - 1) - 2 ≤ ucc (2 ^ k) ∧ ucc (2 ^ k) ≤ 2 * 2 ^ k := by
  have hn : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hne : {d | HasUProtocol (Finset.univ : Finset (Fin (2 ^ k) → Bool)) Finset.univ d}.Nonempty :=
    ⟨2 * 2 ^ k, uprotocol_exists hn⟩
  refine ⟨uprotocol_lower_bound k hk (Nat.sInf_mem hne), ?_⟩
  exact Nat.sInf_le (uprotocol_exists hn)

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.uprotocol_exists
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.ucc_pow2_bracket
