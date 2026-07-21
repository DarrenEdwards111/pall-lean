import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKhrK1

/-!
# K2 of the multiplicative-recurrence engine: the parity witness

Khrapchenko's calibration point — parity has the extremal witness pair:

* `oddF` — the parity function; `oddSet`/`evenSet` — its level sets;
* **`oddF_flip` (proved)** — flipping one coordinate flips parity, so EVERY
  Hamming edge from `oddSet` crosses to `evenSet`;
* **`oddSet_card`/`evenSet_card` (proved)** — the level sets halve the cube:
  `2^(n−1)` each (flip-at-0 bijection);
* **`parity_edges_card` (proved)** — `|E| = |oddSet| · n`: the edges biject
  with (odd vector, flipped coordinate) pairs;
* **`parity_formula_lb` (proved, K2)** — `n² ≤ lsize(t)` for every DeMorgan
  tree computing parity: THE FIRST SUPERLINEAR BOUND of the project.

Restricted model (DeMorgan formulas).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- The parity (odd-weight) function. -/
def oddF (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter (fun j => x j = true)).card % 2 = 1)

/-- The odd-weight vectors. -/
def oddSet (n : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => oddF n x = true)

/-- The even-weight vectors. -/
def evenSet (n : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => oddF n x = false)

/-- Flip-flip cancellation. -/
theorem flip_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    Function.update (Function.update x i (!(x i))) i
      (!(Function.update x i (!(x i)) i)) = x := by
  rw [Function.update_self, Bool.not_not, Function.update_idem,
    Function.update_eq_self]

/-- **Flipping one coordinate flips parity (proved).** -/
theorem oddF_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    oddF n (Function.update x i (!(x i))) = !(oddF n x) := by
  classical
  have hset : Finset.univ.filter
        (fun j => Function.update x i (!(x i)) j = true)
      = if x i = true
        then (Finset.univ.filter (fun j => x j = true)).erase i
        else insert i (Finset.univ.filter (fun j => x j = true)) := by
    by_cases hxi : x i = true
    · rw [if_pos hxi]
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, hxi]
        simp
      · rw [Function.update_of_ne hj]
        simp [hj]
    · have hxif : x i = false := by
        cases h : x i
        · rfl
        · exact absurd h hxi
      rw [if_neg hxi]
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, hxif]
        simp
      · rw [Function.update_of_ne hj]
        simp [hj]
  by_cases hxi : x i = true
  · have hiT : i ∈ Finset.univ.filter (fun j => x j = true) := by
      simp [hxi]
    have hpos : 0 < (Finset.univ.filter (fun j => x j = true)).card :=
      Finset.card_pos.mpr ⟨i, hiT⟩
    have hc : (Finset.univ.filter
          (fun j => Function.update x i (!(x i)) j = true)).card
        = (Finset.univ.filter (fun j => x j = true)).card - 1 := by
      rw [hset, if_pos hxi, Finset.card_erase_of_mem hiT]
    show decide ((Finset.univ.filter
        (fun j => Function.update x i (!(x i)) j = true)).card % 2 = 1)
      = !(decide ((Finset.univ.filter (fun j => x j = true)).card % 2 = 1))
    rw [hc]
    by_cases h : (Finset.univ.filter (fun j => x j = true)).card % 2 = 1
    · have h' : ¬(((Finset.univ.filter (fun j => x j = true)).card - 1) % 2
          = 1) := by omega
      simp [h, h']
    · have h' : ((Finset.univ.filter (fun j => x j = true)).card - 1) % 2
          = 1 := by omega
      simp [h, h']
  · have hiT : i ∉ Finset.univ.filter (fun j => x j = true) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hxi
    have hc : (Finset.univ.filter
          (fun j => Function.update x i (!(x i)) j = true)).card
        = (Finset.univ.filter (fun j => x j = true)).card + 1 := by
      rw [hset, if_neg hxi, Finset.card_insert_of_notMem hiT]
    show decide ((Finset.univ.filter
        (fun j => Function.update x i (!(x i)) j = true)).card % 2 = 1)
      = !(decide ((Finset.univ.filter (fun j => x j = true)).card % 2 = 1))
    rw [hc]
    by_cases h : (Finset.univ.filter (fun j => x j = true)).card % 2 = 1
    · have h' : ¬(((Finset.univ.filter (fun j => x j = true)).card + 1) % 2
          = 1) := by omega
      simp [h, h']
    · have h' : ((Finset.univ.filter (fun j => x j = true)).card + 1) % 2
          = 1 := by omega
      simp [h, h']

/-- The level sets halve each other (flip-at-a-coordinate bijection). -/
theorem oddSet_card_eq_evenSet (n : ℕ) (hn : 1 ≤ n) :
    (oddSet n).card = (evenSet n).card := by
  classical
  have h0 : (0 : ℕ) < n := hn
  refine Finset.card_bij
    (fun x _ => Function.update x ⟨0, h0⟩ (!(x ⟨0, h0⟩))) ?_ ?_ ?_
  · intro x hx
    have h1 : oddF n x = true := (Finset.mem_filter.mp hx).2
    have h2 := oddF_flip x ⟨0, h0⟩
    rw [h1] at h2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
  · intro x hx y hy he
    have hx' := congrArg (fun z => Function.update z ⟨0, h0⟩
      (!(z ⟨0, h0⟩))) he
    simpa [flip_flip] using hx'
  · intro y hy
    refine ⟨Function.update y ⟨0, h0⟩ (!(y ⟨0, h0⟩)), ?_, flip_flip y ⟨0, h0⟩⟩
    have h1 : oddF n y = false := (Finset.mem_filter.mp hy).2
    have h2 := oddF_flip y ⟨0, h0⟩
    rw [h1] at h2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩

theorem odd_add_even (n : ℕ) :
    (oddSet n).card + (evenSet n).card = 2 ^ n := by
  classical
  have hcong : evenSet n
      = Finset.univ.filter (fun x => ¬ oddF n x = true) := by
    ext x
    simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and]
    cases h : oddF n x <;> simp
  rw [oddSet, hcong, Finset.card_filter_add_card_filter_not
    (fun x => oddF n x = true)]
  rw [Finset.card_univ]
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem oddSet_card (n : ℕ) (hn : 1 ≤ n) :
    (oddSet n).card = 2 ^ (n - 1) := by
  have h1 := oddSet_card_eq_evenSet n hn
  have h2 := odd_add_even n
  have h3 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  omega

theorem evenSet_card (n : ℕ) (hn : 1 ≤ n) :
    (evenSet n).card = 2 ^ (n - 1) := by
  have h1 := oddSet_card_eq_evenSet n hn
  have h2 := oddSet_card n hn
  omega

/-- **Every Hamming edge crosses; the edges are (vector, coordinate) pairs.** -/
theorem parity_edges_card (n : ℕ) :
    (hamEdges n (oddSet n) (evenSet n)).card = (oddSet n).card * n := by
  classical
  have hb : ((oddSet n) ×ˢ (Finset.univ : Finset (Fin n))).card
      = (hamEdges n (oddSet n) (evenSet n)).card := by
    refine Finset.card_bij
      (fun p _ => (p.1, Function.update p.1 p.2 (!(p.1 p.2)))) ?_ ?_ ?_
    · intro p hp
      obtain ⟨hp1, -⟩ := Finset.mem_product.mp hp
      refine mem_hamEdges.mpr ⟨hp1, ?_, p.2, rfl⟩
      have h1 : oddF n p.1 = true := (Finset.mem_filter.mp hp1).2
      have h2 := oddF_flip p.1 p.2
      rw [h1] at h2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
    · intro p hp q hq he
      have he' : (p.1, Function.update p.1 p.2 (!(p.1 p.2)))
          = (q.1, Function.update q.1 q.2 (!(q.1 q.2))) := he
      have hfst0 := congrArg Prod.fst he'
      have hsnd0 := congrArg Prod.snd he'
      have hfst : p.1 = q.1 := hfst0
      have hsnd : Function.update p.1 p.2 (!(p.1 p.2))
          = Function.update q.1 q.2 (!(q.1 q.2)) := hsnd0
      rw [← hfst] at hsnd
      by_cases hij : p.2 = q.2
      · exact Prod.ext_iff.mpr ⟨hfst, hij⟩
      · exfalso
        have h1 := congrFun hsnd p.2
        rw [Function.update_self, Function.update_of_ne hij] at h1
        cases hpb : p.1 p.2 <;> rw [hpb] at h1 <;> simp at h1
    · intro b hb
      obtain ⟨hb1, hb2, i, hbi⟩ := mem_hamEdges.mp hb
      exact ⟨(b.1, i), Finset.mem_product.mpr ⟨hb1, Finset.mem_univ _⟩,
        Prod.ext_iff.mpr ⟨rfl, hbi.symm⟩⟩
  rw [← hb, Finset.card_product, Finset.card_univ, Fintype.card_fin]

/-- **K2 (proved): `n² ≤ lsize` for every DeMorgan formula computing parity —
the first superlinear lower bound of the project.** -/
theorem parity_formula_lb (n : ℕ) (hn : 1 ≤ n) (t : DMTree n)
    (ht : ∀ x, t.eval x = oddF n x) : n ^ 2 ≤ t.lsize := by
  have hA : ∀ x ∈ oddSet n, t.eval x = true := by
    intro x hx
    rw [ht]
    exact (Finset.mem_filter.mp hx).2
  have hB : ∀ x ∈ evenSet n, t.eval x = false := by
    intro x hx
    rw [ht]
    exact (Finset.mem_filter.mp hx).2
  have hk := khrapchenko t (oddSet n) (evenSet n) hA hB
  rw [parity_edges_card, oddSet_card n hn, evenSet_card n hn] at hk
  have e1 : (2 ^ (n - 1) * n) ^ 2 = n ^ 2 * (2 ^ (n - 1) * 2 ^ (n - 1)) := by
    ring
  have e2 : t.lsize * 2 ^ (n - 1) * 2 ^ (n - 1)
      = t.lsize * (2 ^ (n - 1) * 2 ^ (n - 1)) := by ring
  rw [e1, e2] at hk
  exact Nat.le_of_mul_le_mul_right hk
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.parity_formula_lb
