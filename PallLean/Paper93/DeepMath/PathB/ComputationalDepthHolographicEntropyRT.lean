import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsObstruction

/-!
# The AdS/CFT holographic entropy face: Ryu–Takayanagi against the wall

The Ryu–Takayanagi formula: the entanglement entropy of a boundary region `A` equals the area of the
minimal bulk surface homologous to `A`, `S(A) = Area(γ_A)/4G`.  It is the most refined AdS/CFT
information observable, with a genuine minimization structure (like `cbudget`) and real proved
inequalities (subadditivity, strong subadditivity).  This file formalises it and shows where it
lands: it is an entropy (information, not cost), its area law is a COMPRESSION statement (it
certifies EASINESS, the wrong side of the wall), and its inequalities are SUB-additive (the wrong
DIRECTION versus `cost_super`'s super-additivity).  Even so, its efficient-detector form is the same
natural-proofs barrier.  It renames the wall — and, uniquely among the physics faces, it renames the
*easy* side.

## The structure and its two real properties

`RTWorld` carries the entanglement entropy `S`, the boundary area, and a `join` of regions, with the
two RT facts as fields:

* **area law** `S(A) ≤ area(A)` — entanglement is bounded ABOVE by the boundary area (the RT
  minimal surface is at most the trivial one).
* **subadditivity** `S(A ∪ B) ≤ S(A) + S(B)` — a real theorem for RT entropy.

## What is proved

* **`rt_bounds_entanglement_above`** — RT gives an UPPER bound on entanglement.  `cost_super` needs a
  LOWER bound on cost; an upper bound on information is the wrong quantity and the wrong direction.
* **`rt_area_law_certifies_easiness`** — small boundary area ⟹ low entanglement ⟹ the compressible
  (MERA/tensor-network) regime.  RT identifies the EASY states; it is a `P/poly`-side witness, not a
  SAT-hardness one — the wrong side of the wall.
* **`entropy_subadditive_caps`** — RT entropy of a doubled region is `≤ 2·S` (an upper cap), the
  reverse of `cost_super`'s `2·cost ≤ cost'` (a lower floor).
* **`subadditive_opposes_cost_super`** — the two constraints are opposite: a quantity that is both
  RT-subadditive and `cost_super`-super-additive is pinned to exact equality, so subadditivity
  forbids the strict growth `cost_super` needs.  The holographic entropy cone points the wrong way.
* **`entanglement_detector_breaks_crypto`** — an efficient test for "low entanglement" that separated
  SAT would be a `ColossusRuler`, hence — via the reused Razborov–Rudich barrier — force
  `¬ PRFExists`.

## Verdict

Ryu–Takayanagi is the sharpest AdS/CFT information observable, and it lands furthest from
`cost_super` of all the physics faces: wrong quantity (entropy), wrong direction (upper bound /
sub-additive), wrong side (certifies compressibility/easiness), with the efficient form still
natural-proofs-barriered.  The minimization structure that makes RT look like `cbudget` is genuine,
but it minimizes AREA to bound ENTANGLEMENT, not gates to bound COMPUTATION.  A faithful
re-description of the easy side of the wall — not a way across it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolographicEntropyRT

open PallLean.Paper93.DeepMath.PathB.NaturalProofsObstruction

/-- An RT / holographic-entropy world: entanglement entropy `S`, boundary `area`, region `join`,
with the area law and subadditivity as the two RT facts. -/
structure RTWorld where
  /-- boundary regions -/
  Region : Type
  /-- holographic entanglement entropy `S(A) = Area(γ_A)/4G` -/
  S : Region → ℕ
  /-- boundary area `|∂A|` -/
  area : Region → ℕ
  /-- union of regions -/
  join : Region → Region → Region
  /-- the area law: entanglement is bounded above by the boundary area -/
  area_law : ∀ A, S A ≤ area A
  /-- RT entropy is subadditive -/
  subadditive : ∀ A B, S (join A B) ≤ S A + S B
  /-- the SAT region/state -/
  sat : Region
  /-- pseudorandom functions exist (the barrier's crypto hypothesis) -/
  PRFExists : Prop

/-- **RT bounds entanglement from ABOVE (proved).**  `S(A) ≤ area(A)`: an upper bound on
information.  `cost_super` needs a LOWER bound on cost — wrong quantity, wrong direction. -/
theorem rt_bounds_entanglement_above (W : RTWorld) (A : W.Region) : W.S A ≤ W.area A :=
  W.area_law A

/-- **The area law certifies EASINESS (proved).**  A small boundary (`area A ≤ k`) forces low
entanglement (`S A ≤ k`) — the compressible, efficiently-describable (MERA) regime.  RT identifies
the EASY states: it is a witness for the low-complexity side, not a SAT-hardness certificate. -/
theorem rt_area_law_certifies_easiness (W : RTWorld) (A : W.Region) (k : ℕ)
    (hsmall : W.area A ≤ k) : W.S A ≤ k :=
  le_trans (W.area_law A) hsmall

/-- **RT entropy sub-adds — the doubled region is capped (proved).**  `S(A ∪ A) ≤ 2·S(A)`: an upper
cap on combined entropy, the reverse of `cost_super`'s lower floor. -/
theorem entropy_subadditive_caps (W : RTWorld) (A : W.Region) :
    W.S (W.join A A) ≤ 2 * W.S A := by
  have h := W.subadditive A A; omega

/-- **Subadditivity opposes `cost_super` (proved).**  A quantity that is BOTH RT-subadditive
(`y ≤ 2x`) and `cost_super`-super-additive (`2x ≤ y`) is pinned to exact equality — so
subadditivity forbids the strict growth `cost_super` requires.  The entropy inequalities point the
opposite way from the cost tower. -/
theorem subadditive_opposes_cost_super (x y : ℕ) (hsub : y ≤ 2 * x) (hsuper : 2 * x ≤ y) :
    y = 2 * x := by omega

/-! ### The efficient-detector barrier -/

/-- The `ComplexityWorld` at entanglement threshold `k`: `P/poly` = "low entanglement `S ≤ k`". -/
def toComplexityWorld (W : RTWorld) (k : ℕ) (Eff : (W.Region → Bool) → Prop) : ComplexityWorld where
  Fn := W.Region
  InPpoly := fun A => W.S A ≤ k
  PolyTimeComputable := Eff
  sat := W.sat
  PRFExists := W.PRFExists

/-- **The low-entanglement test is a `ColossusRuler` (proved).**  `A ↦ (S A ≤ k)` is poly-checkable
(if `S` is efficient), true on every low-entanglement region, and false on a high-entanglement SAT. -/
def entanglementRuler (W : RTWorld) (k : ℕ) (hsat : k < W.S W.sat)
    (Eff : (W.Region → Bool) → Prop) (hEff : Eff (fun A => decide (W.S A ≤ k))) :
    ColossusRuler (toComplexityWorld W k Eff) where
  E := fun A => decide (W.S A ≤ k)
  poly := hEff
  closedOnPpoly := fun A hA => by
    have hSA : W.S A ≤ k := hA
    simp [hSA]
  failsSAT := by
    show decide (W.S W.sat ≤ k) = false
    have hn : ¬ (W.S W.sat ≤ k) := by omega
    simp [hn]

/-- **An efficient entanglement detector breaks crypto (proved).**  If low-entanglement is
efficiently testable and SAT is high-entanglement, the detector is a natural distinguisher and,
via the Razborov–Rudich barrier, forces `¬ PRFExists`. -/
theorem entanglement_detector_breaks_crypto (W : RTWorld) (k : ℕ) (hsat : k < W.S W.sat)
    (Eff : (W.Region → Bool) → Prop) (hEff : Eff (fun A => decide (W.S A ≤ k)))
    (barrier : RazborovRudichBarrier (toComplexityWorld W k Eff)) :
    ¬ W.PRFExists :=
  ruler_needs_broken_crypto (toComplexityWorld W k Eff)
    (entanglementRuler W k hsat Eff hEff) barrier

end PallLean.Paper93.DeepMath.PathB.HolographicEntropyRT

#print axioms PallLean.Paper93.DeepMath.PathB.HolographicEntropyRT.rt_bounds_entanglement_above
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicEntropyRT.rt_area_law_certifies_easiness
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicEntropyRT.entropy_subadditive_caps
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicEntropyRT.subadditive_opposes_cost_super
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicEntropyRT.entanglement_detector_breaks_crypto
