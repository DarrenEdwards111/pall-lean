import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsObstruction

/-!
# The tensor-network / MERA compression face

MERA (multiscale entanglement renormalization) and tensor networks are the *constructive* companion
to Ryu–Takayanagi: RT says area-law states have low entanglement; MERA says low-entanglement states
have **small descriptions** — a tensor network of small bond dimension.  A tensor network IS a
circuit, so this is a genuine COMPRESSION scheme, and it is the algorithmic engine of the *easy* side
of the wall.  This file formalises it and shows: tensor-network size UPPER-bounds circuit complexity
(compression ⟹ easiness, the wrong direction for `cost_super`); the area-law chain (RT → MERA) lands
entirely on the `P/poly` side; and the incompressibility question ("does SAT have a small tensor
network?") — which is exactly `cost_super` in this language — is the MCSP/natural-proofs barrier.

## The structure

`TNWorld` carries the true `cbudget`, the minimal tensor-network size `tnSize`, the `entanglement`,
and a MERA cost function `meraCost`, with the two physics facts as fields:

* **compression** `cbudget f ≤ tnSize f` — a tensor network is a description, so it bounds circuit
  complexity from above.
* **MERA efficiency** `tnSize f ≤ meraCost (entanglement f)` with `meraCost` monotone — low
  entanglement ⟹ small tensor network (the area-law representation theorem).

## What is proved

* **`tn_upper_bounds_cbudget`** — compression is an UPPER bound on cost.  `cost_super` needs a LOWER
  bound; an upper bound cannot supply it.
* **`small_tn_certifies_easiness`** — `tnSize f ≤ k ⟹ cbudget f ≤ k`: a small tensor network is a
  `P/poly` membership witness.  MERA certifies EASINESS.
* **`mera_area_law_chain`** — bounded entanglement ⟹ bounded `tnSize` ⟹ bounded `cbudget`: the full
  RT→MERA chain lands on the easy side.
* **`tn_size_is_not_a_lower_bound`** — a large `tnSize` does NOT force a large `cbudget` (since
  `cbudget ≤ tnSize`, the cost can be anything below): tensor-network size proves easiness, never
  hardness.
* **`incompressibility_detector_breaks_crypto`** — the MCSP question "does `f` have a size-`k` tensor
  network?" made an efficient detector separating SAT is a `ColossusRuler`, hence forces
  `¬ PRFExists`.  Detecting incompressibility is the natural-proofs wall.

## Verdict

MERA/tensor networks are the constructive compressor — the algorithm of the easy side.  They give
UPPER bounds on `cbudget` (proving membership, never non-membership), the area-law chain confirms
easiness, and `cost_super` in this language is precisely tensor-network INCOMPRESSIBILITY of SAT —
whose typical form is counting and whose efficient-detector form is MCSP, both barriered.  The
constructive companion to `HolographicEntropyRT`; a faithful re-description of the easy side and its
compression algorithm, not a way across.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TensorNetworkMERA

open PallLean.Paper93.DeepMath.PathB.NaturalProofsObstruction

/-- A tensor-network world: true `cbudget`, minimal tensor-network size `tnSize`, `entanglement`,
and a monotone MERA cost, with compression and MERA-efficiency as fields. -/
structure TNWorld where
  /-- the universe of functions -/
  Fn : Type
  /-- true minimal circuit size -/
  cbudget : Fn → ℕ
  /-- minimal tensor-network (MERA) size (bond dimension × sites) -/
  tnSize : Fn → ℕ
  /-- entanglement of `f` (from the RT face) -/
  entanglement : Fn → ℕ
  /-- MERA cost as a function of entanglement -/
  meraCost : ℕ → ℕ
  /-- MERA cost is monotone in entanglement -/
  meraCost_mono : ∀ a b, a ≤ b → meraCost a ≤ meraCost b
  /-- **compression**: a tensor network is a circuit, so it upper-bounds `cbudget` -/
  tn_compresses : ∀ f, cbudget f ≤ tnSize f
  /-- **MERA efficiency**: low entanglement ⟹ small tensor network -/
  mera_efficient : ∀ f, tnSize f ≤ meraCost (entanglement f)
  /-- the SAT function -/
  sat : Fn
  /-- pseudorandom functions exist (the barrier's crypto hypothesis) -/
  PRFExists : Prop

/-- **Compression is an UPPER bound on cost (proved).**  `cbudget f ≤ tnSize f`.  `cost_super` needs
a LOWER bound on cost; an upper-bounding tool cannot supply it. -/
theorem tn_upper_bounds_cbudget (W : TNWorld) (f : W.Fn) : W.cbudget f ≤ W.tnSize f :=
  W.tn_compresses f

/-- **A small tensor network certifies EASINESS (proved).**  `tnSize f ≤ k ⟹ cbudget f ≤ k`: MERA
compressibility is a `P/poly`-membership witness, not a hardness certificate. -/
theorem small_tn_certifies_easiness (W : TNWorld) (f : W.Fn) (k : ℕ)
    (hsmall : W.tnSize f ≤ k) : W.cbudget f ≤ k :=
  le_trans (W.tn_compresses f) hsmall

/-- **The RT→MERA chain lands on the easy side (proved).**  Bounded entanglement ⟹ bounded tensor
network ⟹ bounded circuit size: `entanglement f ≤ e ⟹ cbudget f ≤ meraCost e`. -/
theorem mera_area_law_chain (W : TNWorld) (f : W.Fn) (e : ℕ)
    (hent : W.entanglement f ≤ e) : W.cbudget f ≤ W.meraCost e :=
  le_trans (W.tn_compresses f)
    (le_trans (W.mera_efficient f) (W.meraCost_mono _ _ hent))

/-- **Tensor-network size is NOT a cost lower bound (proved).**  Since `cbudget ≤ tnSize`, a large
`tnSize` is consistent with a small `cbudget` — so `tnSize` cannot certify hardness.  Witnessed:
`cbudget = 0`, `tnSize = k`, with `cbudget ≤ tnSize` and `cbudget < k`. -/
theorem tn_size_is_not_a_lower_bound (k : ℕ) (hk : 0 < k) :
    ∃ cb tn : ℕ, cb ≤ tn ∧ cb < k ∧ k ≤ tn :=
  ⟨0, k, Nat.zero_le _, hk, le_refl _⟩

/-! ### The incompressibility (MCSP) detector barrier -/

/-- The `ComplexityWorld` at tensor-network threshold `k`: `P/poly` = "compressible, `tnSize ≤ k`". -/
def toComplexityWorld (W : TNWorld) (k : ℕ) (Eff : (W.Fn → Bool) → Prop) : ComplexityWorld where
  Fn := W.Fn
  InPpoly := fun f => W.tnSize f ≤ k
  PolyTimeComputable := Eff
  sat := W.sat
  PRFExists := W.PRFExists

/-- **The compressibility test is a `ColossusRuler` (proved).**  `f ↦ (tnSize f ≤ k)` — the MCSP
question "does `f` have a size-`k` tensor network?" — is poly-checkable (if `tnSize` is efficiently
testable), true on every compressible function, and false on an incompressible SAT. -/
def compressibilityRuler (W : TNWorld) (k : ℕ) (hsat : k < W.tnSize W.sat)
    (Eff : (W.Fn → Bool) → Prop) (hEff : Eff (fun f => decide (W.tnSize f ≤ k))) :
    ColossusRuler (toComplexityWorld W k Eff) where
  E := fun f => decide (W.tnSize f ≤ k)
  poly := hEff
  closedOnPpoly := fun f hf => by
    have htn : W.tnSize f ≤ k := hf
    simp [htn]
  failsSAT := by
    show decide (W.tnSize W.sat ≤ k) = false
    have hn : ¬ (W.tnSize W.sat ≤ k) := by omega
    simp [hn]

/-- **Detecting incompressibility breaks crypto (proved).**  If tensor-network compressibility is
efficiently testable and SAT is incompressible, the detector is a natural distinguisher and, via the
Razborov–Rudich barrier, forces `¬ PRFExists`.  `cost_super` as tensor-network incompressibility is
the MCSP/natural-proofs wall. -/
theorem incompressibility_detector_breaks_crypto (W : TNWorld) (k : ℕ) (hsat : k < W.tnSize W.sat)
    (Eff : (W.Fn → Bool) → Prop) (hEff : Eff (fun f => decide (W.tnSize f ≤ k)))
    (barrier : RazborovRudichBarrier (toComplexityWorld W k Eff)) :
    ¬ W.PRFExists :=
  ruler_needs_broken_crypto (toComplexityWorld W k Eff)
    (compressibilityRuler W k hsat Eff hEff) barrier

end PallLean.Paper93.DeepMath.PathB.TensorNetworkMERA

#print axioms PallLean.Paper93.DeepMath.PathB.TensorNetworkMERA.tn_upper_bounds_cbudget
#print axioms PallLean.Paper93.DeepMath.PathB.TensorNetworkMERA.small_tn_certifies_easiness
#print axioms PallLean.Paper93.DeepMath.PathB.TensorNetworkMERA.mera_area_law_chain
#print axioms PallLean.Paper93.DeepMath.PathB.TensorNetworkMERA.tn_size_is_not_a_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.TensorNetworkMERA.incompressibility_detector_breaks_crypto
