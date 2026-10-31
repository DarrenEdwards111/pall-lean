import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATKillB23

/-!
# THE `+2`: `2·deps + 1 ≤ cbudget (SATFamily N)` at every two-gadget length

The capstone of the `+2` campaign.  Suppose the budget were `≤ 2·deps`.  The
above-floor theorem already excludes `2·deps − 1`, so an optimal circuit sits at
exactly one unit above the floor — and the spare-structure theorem hands us its
unique reconvergence wire `u`.  Casing on which of the six sign gates lie below
`u`, every configuration is a proved kill:

* a gadget fully avoiding `u` — `killA_g0/g1`;
* a gadget fully below `u` — `killB1_g0/g1` (the prefix split);
* two below + one free — `killB2_*` (three values demanded of one bit);
* one below in each gadget — `killB3_*` (the polarity-flip pins).

* **`SATFamily_plus_two` (proved)** — `2·deps + 1 ≤ cbudget (SATFamily N)` for all
  `N ≥ 46`;
* **`cbudget_SATFamily_two_n_plus2` (proved)** — readable form
  `2N ≤ cbudget (SATFamily N) + 43`, two past the dense floor's `45`.

## Honest scope

This is `+2` over the cone floor on the exact target family — each embedded codec
gadget now provably costs one unit of slack on SAT's own circuits.  It is NOT
superlinear: growing the excess to `+m` (m gadgets ⟹ m spare units ⟹ the
multi-wire collision analysis) is the open continuation, and superlinearity
remains the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-- **THE `+2` (proved)**: two above the cone floor on the exact target family, at
every two-gadget length. -/
theorem SATFamily_plus_two (N : ℕ) (hN : 46 ≤ N) :
    2 * (depSet (SATFamily N)).card + 1 ≤ cbudget (SATFamily N) := by
  have h12 : (12 : ℕ) < N := by omega
  have h18 : (18 : ℕ) < N := by omega
  have h24 : (24 : ℕ) < N := by omega
  have h31 : (31 : ℕ) < N := by omega
  have h38 : (38 : ℕ) < N := by omega
  have h45 : (45 : ℕ) < N := by omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hcomp, hclen⟩ := Nat.sInf_mem (cbudget_set_nonempty (SATFamily N))
  have hclen' : c.length = cbudget (SATFamily N) := hclen
  have hfl := SATFamily_above_floor N (by omega)
  have hlen : c.length ≤ 2 * (depSet (SATFamily N)).card := by omega
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd31 := sign31_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd38 := sign38_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd45 := sign45_dep6 N hN h12 h18 h24 h31 h38 h45
  have hdcard : 1 ≤ (depSet (SATFamily N)).card := Finset.card_pos.mpr ⟨_, hd12⟩
  have hs : 0 < c.length := by omega
  have hone := SATFamily_spare_structure N (by omega) c hcomp hs hlen
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hone
  obtain ⟨q12, hq12c, hq12g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd12
  obtain ⟨q18, hq18c, hq18g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd18
  obtain ⟨q24, hq24c, hq24g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd24
  obtain ⟨q31, hq31c, hq31g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd31
  obtain ⟨q38, hq38c, hq38g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd38
  obtain ⟨q45, hq45c, hq45g⟩ := dep_var_gate (SATFamily N) c hcomp hs _ hd45
  by_cases hb12 : Reach c u q12 <;> by_cases hb18 : Reach c u q18 <;>
    by_cases hb24 : Reach c u q24 <;> by_cases hb31 : Reach c u q31 <;>
    by_cases hb38 : Reach c u q38 <;> by_cases hb45 : Reach c u q45 <;>
    first
      | exact killA_g0 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24
      | exact killA_g1 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq31c hq31g hb31 hq38c hq38g hb38 hq45c hq45g hb45
      | exact killB1_g0 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24
      | exact killB1_g1 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq31c hq31g hb31 hq38c hq38g hb38 hq45c hq45g hb45
      | exact killB2_g0_free1 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24
      | exact killB2_g0_free2 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24
      | exact killB2_g0_free3 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24
      | exact killB2_g1_free4 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq31c hq31g hb31 hq38c hq38g hb38 hq45c hq45g hb45
      | exact killB2_g1_free5 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq31c hq31g hb31 hq38c hq38g hb38 hq45c hq45g hb45
      | exact killB2_g1_free6 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq31c hq31g hb31 hq38c hq38g hb38 hq45c hq45g hb45
      | exact killB3_14 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24 hq31c hq31g hb31
      | exact killB3_15 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24 hq38c hq38g hb38
      | exact killB3_16 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24 hq45c hq45g hb45
      | exact killB3_24 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24 hq31c hq31g hb31
      | exact killB3_25 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24 hq38c hq38g hb38
      | exact killB3_26 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24 hq45c hq45g hb45
      | exact killB3_34 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24 hq31c hq31g hb31
      | exact killB3_35 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24 hq38c hq38g hb38
      | exact killB3_36 N hN h12 h18 h24 h31 h38 h45 c hcomp hs hlen hu
          hq12c hq12g hb12 hq18c hq18g hb18 hq24c hq24g hb24 hq45c hq45g hb45

/-- **Readable form (proved)**: `2N ≤ cbudget (SATFamily N) + 43` — two past the
dense floor's `45`. -/
theorem cbudget_SATFamily_two_n_plus2 (N : ℕ) (hN : 46 ≤ N) :
    2 * N ≤ cbudget (SATFamily N) + 43 := by
  have h1 := depSet_card_ge_dense N
  have h2 := SATFamily_plus_two N hN
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.SATFamily_plus_two
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_SATFamily_two_n_plus2
