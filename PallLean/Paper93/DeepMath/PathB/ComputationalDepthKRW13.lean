import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW12

/-!
# KRW brick 13: the conjecture in communication-complexity terms

Via the Karchmer–Wigderson theorem (`kw_theorem`, KRW12), the depth-form
`KRWConjectureDepth` translates into the communication-complexity statement that
KRW is classically stated in: the KW communication of a composition is (nearly)
the sum of the KW communications.

* **`krw_conjecture_in_kw_terms` (from the conjecture)** — `KRWConjectureDepth`
  implies `kwCC f + kwCC g ≤ kwCC (f ⋄ g) + 1` for nonconstant `f`, `g`;
* **`kw_superadditive_of_krw`** — the same, packaged as super-additivity of
  `kwCC` under composition (up to `+1`).

This is the bridge: our depth conjecture IS the classical Karchmer–Raz–Wigderson
communication conjecture, up to the `+1` slack from `DMTree` constants.  It does
NOT prove the conjecture — `KRWConjectureDepth` stays a hypothesis.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- **The KRW conjecture in KW-communication terms (proved from the conjecture)**:
`kwCC f + kwCC g ≤ kwCC (f ⋄ g) + 1`. -/
theorem krw_conjecture_in_kw_terms (H : KRWConjectureDepth) {m b : ℕ}
    (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (hfc : ∃ y y', f y ≠ f y') (hgc : ∃ u u', g u ≠ g u') :
    kwCC f + kwCC g ≤ kwCC (comp hb f g) + 1 := by
  have h1 := kwCC_le_dmdepth hm f
  have h2 := kwCC_le_dmdepth hb g
  have h3 := H m b hb f g hfc hgc
  have h4 := dmdepth_le_kwCC_succ (Nat.mul_pos hm hb) (comp hb f g)
  omega

/-- Super-additivity of KW communication under composition, under the conjecture. -/
theorem kw_superadditive_of_krw (H : KRWConjectureDepth) {m b : ℕ}
    (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (hfc : ∃ y y', f y ≠ f y') (hgc : ∃ u u', g u ≠ g u') :
    kwCC f + kwCC g ≤ kwCC (comp hb f g) + 1 :=
  krw_conjecture_in_kw_terms H hm hb f g hfc hgc

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.krw_conjecture_in_kw_terms
