import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW13

/-!
# KRW brick 14: the universal relation communication lower bound

The universal relation `U_n`: Alice holds `x`, Bob holds `y`, `x ≠ y`, and they
must agree on a coordinate `i` with `x i ≠ y i`.  It DOMINATES every KW game
(`KW_f ⊆ U_n` since `onesOf f × zerosOf f` are all distinct), so a `U_n` protocol
solves `KW_f` for every `f`.  With a counting-hard `f` this forces linear
communication.

* **`HasUProtocol A B d`** — a depth-`d` `U_n` protocol on the rectangle `A×B`
  (leaf distinguishes DISTINCT pairs only);
* **`uprotocol_restricts` (proved)** — restricting a `U`-protocol to an
  all-distinct subrectangle gives a KW `HasProtocol`;
* **`uprotocol_cost_lower` (proved)** — any `U`-protocol on `2^n` inputs of cost
  `d` gives `dmdepth f ≤ d + 1` for every `f`;
* **`uprotocol_lower_bound` (proved)** — every `U`-protocol on `2^k` bits costs
  `≥ 2^{k-1} - 2` (linear: `≈ n/2` for `n = 2^k`).

The hard `f` comes from `exists_deep_pow2` (counting), and the KW theorem
(`dmdepth_le_kwCC_succ`) transfers it.  Non-vacuity (a `U`-protocol exists) is
KRW15.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- A depth-`d` universal-relation protocol on the rectangle `A×B` (a leaf need
only distinguish DISTINCT pairs). -/
inductive HasUProtocol {n : ℕ} : Finset (Fin n → Bool) → Finset (Fin n → Bool) → ℕ → Prop
  | leaf {A B : Finset (Fin n → Bool)} (d : ℕ) (i : Fin n)
      (h : ∀ x ∈ A, ∀ y ∈ B, x ≠ y → x i ≠ y i) : HasUProtocol A B d
  | bob {A B : Finset (Fin n → Bool)} {d : ℕ} (p : (Fin n → Bool) → Bool)
      (h0 : HasUProtocol A (B.filter (fun y => p y = false)) d)
      (h1 : HasUProtocol A (B.filter (fun y => p y = true)) d) :
      HasUProtocol A B (d + 1)
  | alice {A B : Finset (Fin n → Bool)} {d : ℕ} (p : (Fin n → Bool) → Bool)
      (h0 : HasUProtocol (A.filter (fun x => p x = false)) B d)
      (h1 : HasUProtocol (A.filter (fun x => p x = true)) B d) :
      HasUProtocol A B (d + 1)

/-- **Restriction to an all-distinct subrectangle gives a KW protocol (proved)**. -/
theorem uprotocol_restricts {n : ℕ} {A B : Finset (Fin n → Bool)} {d : ℕ}
    (h : HasUProtocol A B d) :
    ∀ (A' B' : Finset (Fin n → Bool)), A' ⊆ A → B' ⊆ B →
      (∀ x ∈ A', ∀ y ∈ B', x ≠ y) → HasProtocol A' B' d := by
  induction h with
  | leaf d i hi =>
    intro A' B' hA' hB' hdist
    exact HasProtocol.leaf d i (fun x hx y hy => hi x (hA' hx) y (hB' hy) (hdist x hx y hy))
  | bob p h0 h1 ih0 ih1 =>
    intro A' B' hA' hB' hdist
    refine HasProtocol.bob p (ih0 A' (B'.filter (fun y => p y = false)) hA' ?_ ?_)
                            (ih1 A' (B'.filter (fun y => p y = true)) hA' ?_ ?_)
    · intro y hy
      exact Finset.mem_filter.mpr ⟨hB' (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩
    · intro x hx y hy; exact hdist x hx y (Finset.mem_filter.mp hy).1
    · intro y hy
      exact Finset.mem_filter.mpr ⟨hB' (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩
    · intro x hx y hy; exact hdist x hx y (Finset.mem_filter.mp hy).1
  | alice p h0 h1 ih0 ih1 =>
    intro A' B' hA' hB' hdist
    refine HasProtocol.alice p (ih0 (A'.filter (fun x => p x = false)) B' ?_ hB' ?_)
                             (ih1 (A'.filter (fun x => p x = true)) B' ?_ hB' ?_)
    · intro x hx
      exact Finset.mem_filter.mpr ⟨hA' (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    · intro x hx y hy; exact hdist x (Finset.mem_filter.mp hx).1 y hy
    · intro x hx
      exact Finset.mem_filter.mpr ⟨hA' (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    · intro x hx y hy; exact hdist x (Finset.mem_filter.mp hx).1 y hy

/-- **Any `U`-protocol of cost `d` bounds every function's depth (proved)**. -/
theorem uprotocol_cost_lower {n : ℕ} (hn : 0 < n) {d : ℕ}
    (h : HasUProtocol (Finset.univ : Finset (Fin n → Bool)) Finset.univ d)
    (f : (Fin n → Bool) → Bool) : dmdepth f ≤ d + 1 := by
  have hkw : HasProtocol (onesOf f) (zerosOf f) d :=
    uprotocol_restricts h (onesOf f) (zerosOf f) (Finset.subset_univ _) (Finset.subset_univ _)
      (fun x hx y hy => by
        have hfx : f x = true := (Finset.mem_filter.mp hx).2
        have hfy : f y = false := (Finset.mem_filter.mp hy).2
        intro hxy; rw [hxy] at hfx; rw [hfx] at hfy; exact Bool.noConfusion hfy)
  have h1 : kwCC f ≤ d := Nat.sInf_le hkw
  have h2 := dmdepth_le_kwCC_succ hn f
  omega

/-- **THE UNIVERSAL RELATION LOWER BOUND (proved)**: every `U`-protocol on `2^k`
bits costs `≥ 2^{k-1} - 2` (linear communication, `≈ n/2` for `n = 2^k`). -/
theorem uprotocol_lower_bound (k : ℕ) (hk : 4 ≤ k) {d : ℕ}
    (h : HasUProtocol (Finset.univ : Finset (Fin (2 ^ k) → Bool)) Finset.univ d) :
    2 ^ (k - 1) - 2 ≤ d := by
  obtain ⟨f, hf⟩ := exists_deep_pow2 k hk
  have hn : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hle := uprotocol_cost_lower hn h f
  omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.uprotocol_restricts
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.uprotocol_lower_bound
