import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW17

/-!
# KRW brick 18: the KW composition theorem via the universal relation

The universal relation is the *universal* KW game (`kwCC f ≤ ucc n`, since a
`U`-protocol solves every KW game), so it bounds every composed KW game.  This
brick gives the composition UPPER bound and, with KRW13, the two-sided picture.

* **`kwCC_le_ucc` (proved)** — `kwCC f ≤ ucc n`: the universal relation dominates
  every function's KW game;
* **`kwCC_comp_le` (proved)** — `kwCC (f ⋄ g) ≤ kwCC f + kwCC g + 2`: the KW
  composition UPPER bound (protocols/formulas compose);
* **`kwCC_comp_le_ucc` (proved)** — `kwCC (f ⋄ g) ≤ ucc m + ucc b + 2`: the same,
  bounded by the universal relation at both scales;
* **`kwCC_comp_two_sided` (from the conjecture)** — under `KRWConjectureDepth`,
  `kwCC f + kwCC g ≤ kwCC (f ⋄ g) + 1 ≤ kwCC f + kwCC g + 3`: composition is
  additive up to `O(1)`.

HONEST SCOPE.  The composition UPPER bound is unconditional.  The matching LOWER
bound — that composition is genuinely additive — is `KRWConjectureDepth` in
general.  For the universal relation SPECIFICALLY it is proved UNCONDITIONALLY by
Gavinsky–Meir–Weinstein–Wigderson / Håstad–Wigderson (`CC(U_m ⋄ U_n) ≥ m + n − o`),
a research-level argument NOT formalized here; my lower bound stays conditional on
`KRWConjectureDepth`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- **The universal relation dominates every KW game (proved)**: `kwCC f ≤ ucc n`. -/
theorem kwCC_le_ucc {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    kwCC f ≤ ucc n := by
  have hne : {d | HasUProtocol (Finset.univ : Finset (Fin n → Bool)) Finset.univ d}.Nonempty :=
    ⟨2 * n, uprotocol_exists hn⟩
  have hu : HasUProtocol (Finset.univ : Finset (Fin n → Bool)) Finset.univ (ucc n) :=
    Nat.sInf_mem hne
  have hkw : HasProtocol (onesOf f) (zerosOf f) (ucc n) :=
    uprotocol_restricts hu (onesOf f) (zerosOf f) (Finset.subset_univ _) (Finset.subset_univ _)
      (fun x hx y hy => by
        have hfx : f x = true := (Finset.mem_filter.mp hx).2
        have hfy : f y = false := (Finset.mem_filter.mp hy).2
        intro hxy; rw [hxy] at hfx; rw [hfx] at hfy; exact Bool.noConfusion hfy)
  exact Nat.sInf_le hkw

/-- **The KW composition upper bound (proved)**: `kwCC (f ⋄ g) ≤ kwCC f + kwCC g + 2`. -/
theorem kwCC_comp_le {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool) :
    kwCC (comp hb f g) ≤ kwCC f + kwCC g + 2 := by
  have h1 : kwCC (comp hb f g) ≤ dmdepth (comp hb f g) :=
    kwCC_le_dmdepth (Nat.mul_pos hm hb) _
  have h2 : dmdepth (comp hb f g) ≤ dmdepth f + dmdepth g := dmdepth_comp_le' hm hb f g
  have h3 : dmdepth f ≤ kwCC f + 1 := dmdepth_le_kwCC_succ hm f
  have h4 : dmdepth g ≤ kwCC g + 1 := dmdepth_le_kwCC_succ hb g
  omega

/-- **Composition bounded by the universal relation (proved)**:
`kwCC (f ⋄ g) ≤ ucc m + ucc b + 2`. -/
theorem kwCC_comp_le_ucc {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool) :
    kwCC (comp hb f g) ≤ ucc m + ucc b + 2 := by
  have h1 := kwCC_comp_le hm hb f g
  have h2 := kwCC_le_ucc hm f
  have h3 := kwCC_le_ucc hb g
  omega

/-- **The two-sided KW composition theorem (upper proved, lower from the
conjecture)**: `kwCC f + kwCC g ≤ kwCC (f ⋄ g) + 1` and
`kwCC (f ⋄ g) ≤ kwCC f + kwCC g + 2`. -/
theorem kwCC_comp_two_sided (H : KRWConjectureDepth) {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (hfc : ∃ y y', f y ≠ f y') (hgc : ∃ u u', g u ≠ g u') :
    kwCC f + kwCC g ≤ kwCC (comp hb f g) + 1
      ∧ kwCC (comp hb f g) ≤ kwCC f + kwCC g + 2 :=
  ⟨krw_conjecture_in_kw_terms H hm hb f g hfc hgc, kwCC_comp_le hm hb f g⟩

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.kwCC_comp_le_ucc
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.kwCC_comp_two_sided
