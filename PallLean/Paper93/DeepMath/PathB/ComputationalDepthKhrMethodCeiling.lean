import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKhrK3b

/-!
# The method's own ceiling: Khrapchenko never exceeds `n²`

The honesty theorem for the engine: the Khrapchenko value is capped at `n²`
for EVERY witness pair — parity attains the cap, and no choice of `A`, `B`
can push the measure past quadratic.  This is the classical limitation of the
method, machine-checked so the engine is not mistaken for more than it is:

* **`khr_value_le` (proved)** — `|E(A,B)|² ≤ n² · (|A|·|B|)` unconditionally
  (each vertex has at most `n` Hamming neighbours, on both sides).

Going beyond `n²` formula bounds requires genuinely different mathematics
(shrinkage for `n³`, KRW beyond).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- **THE METHOD CEILING (proved)**: the Khrapchenko value is at most `n²`. -/
theorem khr_value_le (n : ℕ) (A B : Finset (Fin n → Bool)) :
    (hamEdges n A B).card ^ 2 ≤ n ^ 2 * (A.card * B.card) := by
  classical
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    have hE : ∀ p, p ∉ hamEdges 0 A B := by
      intro p hp
      obtain ⟨-, -, i, -⟩ := mem_hamEdges.mp hp
      exact i.elim0
    have hcard : (hamEdges 0 A B).card = 0 := by
      rcases Finset.eq_empty_or_nonempty (hamEdges 0 A B) with he | ⟨p, hp⟩
      · rw [he]
        rfl
      · exact absurd hp (hE p)
    rw [hcard]
    simp
  · -- each left vertex has at most n neighbours
    have h1 : (hamEdges n A B).card ≤ A.card * n := by
      have hle := Finset.card_le_card_of_injOn
        (fun p : (Fin n → Bool) × (Fin n → Bool) =>
          ((p.1 : Fin n → Bool),
           (if h : ∃ i : Fin n, p.2 = Function.update p.1 i (!(p.1 i))
            then h.choose else (⟨0, hn⟩ : Fin n))))
        (s := hamEdges n A B) (t := A ×ˢ (Finset.univ : Finset (Fin n)))
        (fun p hp => Finset.mem_product.mpr
          ⟨(mem_hamEdges.mp hp).1, Finset.mem_univ _⟩)
        (by
          intro p hp q hq he
          have hexp := (mem_hamEdges.mp (Finset.mem_coe.mp hp)).2.2
          have hexq := (mem_hamEdges.mp (Finset.mem_coe.mp hq)).2.2
          have he' : ((p.1 : Fin n → Bool),
              (if h : ∃ i : Fin n, p.2 = Function.update p.1 i (!(p.1 i))
               then h.choose else (⟨0, hn⟩ : Fin n)))
              = ((q.1 : Fin n → Bool),
              (if h : ∃ i : Fin n, q.2 = Function.update q.1 i (!(q.1 i))
               then h.choose else (⟨0, hn⟩ : Fin n))) := he
          have hf0 := congrArg Prod.fst he'
          have hs0 := congrArg Prod.snd he'
          have hf : p.1 = q.1 := hf0
          have hs : (if h : ∃ i : Fin n, p.2 = Function.update p.1 i (!(p.1 i))
               then h.choose else (⟨0, hn⟩ : Fin n))
              = (if h : ∃ i : Fin n, q.2 = Function.update q.1 i (!(q.1 i))
               then h.choose else (⟨0, hn⟩ : Fin n)) := hs0
          rw [dif_pos hexp, dif_pos hexq] at hs
          have hp2 : p.2 = Function.update p.1 hexp.choose
              (!(p.1 hexp.choose)) := hexp.choose_spec
          have hq2 : q.2 = Function.update q.1 hexq.choose
              (!(q.1 hexq.choose)) := hexq.choose_spec
          set ip := hexp.choose with hipdef
          set iq := hexq.choose with hiqdef
          refine Prod.ext_iff.mpr ⟨hf, ?_⟩
          rw [hp2, hq2, hf, hs])
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hle
      exact hle
    -- each right vertex has at most n neighbours (via the flip involution)
    have h2 : (hamEdges n A B).card ≤ B.card * n := by
      have hle := Finset.card_le_card_of_injOn
        (fun p : (Fin n → Bool) × (Fin n → Bool) =>
          ((p.2 : Fin n → Bool),
           (if h : ∃ i : Fin n, p.2 = Function.update p.1 i (!(p.1 i))
            then h.choose else (⟨0, hn⟩ : Fin n))))
        (s := hamEdges n A B) (t := B ×ˢ (Finset.univ : Finset (Fin n)))
        (fun p hp => Finset.mem_product.mpr
          ⟨(mem_hamEdges.mp hp).2.1, Finset.mem_univ _⟩)
        (by
          intro p hp q hq he
          have hexp := (mem_hamEdges.mp (Finset.mem_coe.mp hp)).2.2
          have hexq := (mem_hamEdges.mp (Finset.mem_coe.mp hq)).2.2
          have he' : ((p.2 : Fin n → Bool),
              (if h : ∃ i : Fin n, p.2 = Function.update p.1 i (!(p.1 i))
               then h.choose else (⟨0, hn⟩ : Fin n)))
              = ((q.2 : Fin n → Bool),
              (if h : ∃ i : Fin n, q.2 = Function.update q.1 i (!(q.1 i))
               then h.choose else (⟨0, hn⟩ : Fin n))) := he
          have hf0 := congrArg Prod.fst he'
          have hs0 := congrArg Prod.snd he'
          have hf : p.2 = q.2 := hf0
          have hs : (if h : ∃ i : Fin n, p.2 = Function.update p.1 i (!(p.1 i))
               then h.choose else (⟨0, hn⟩ : Fin n))
              = (if h : ∃ i : Fin n, q.2 = Function.update q.1 i (!(q.1 i))
               then h.choose else (⟨0, hn⟩ : Fin n)) := hs0
          rw [dif_pos hexp, dif_pos hexq] at hs
          have hp1 : p.1 = Function.update p.2 hexp.choose
              (!(p.2 hexp.choose)) := update_flip_symm hexp.choose_spec
          have hq1 : q.1 = Function.update q.2 hexq.choose
              (!(q.2 hexq.choose)) := update_flip_symm hexq.choose_spec
          set ip := hexp.choose with hipdef
          set iq := hexq.choose with hiqdef
          refine Prod.ext_iff.mpr ⟨?_, hf⟩
          rw [hp1, hq1, hf, hs])
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hle
      exact hle
    have hmul : (hamEdges n A B).card * (hamEdges n A B).card
        ≤ (A.card * n) * (B.card * n) := Nat.mul_le_mul h1 h2
    have e1 : (hamEdges n A B).card ^ 2
        = (hamEdges n A B).card * (hamEdges n A B).card := by ring
    have e2 : (A.card * n) * (B.card * n) = n ^ 2 * (A.card * B.card) := by
      ring
    rw [e1, ← e2]
    exact hmul

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.khr_value_le
