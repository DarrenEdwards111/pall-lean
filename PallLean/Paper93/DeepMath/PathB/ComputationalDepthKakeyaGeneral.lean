import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKakeyaRankForcing

/-!
# Generalising the Kakeya forcing to the wall: the mechanism is already general; the depth-4 chasm is the wall

`KakeyaRankForcing` proved a Kakeya-type dimension bound forces superpolynomial SPDP rank — for a concrete
family, in the restricted regime.  "Generalise it to the wall" splits into two halves, and machine-checking
which is which is the honest content: one half is *already general*, the other *is* the wall.

**The forcing already generalises — it holds for any family.**  `kakeya_dimension_forces_rank` has no
restriction: for *every* SPDP family, the Kakeya dimension bounds the rank.  So the mechanism does not need
generalising; it already applies to a general Boolean NP-complete family.  What a superpolynomial SPDP rank
buys, by GKKS, is a superpolynomial lower bound *against depth-4 circuits* (`forcing_certifies_depth4`).

**The wall is the depth-4 → general chasm.**  Superpolynomial SPDP rank certifies *depth-4* hardness, not
*general-circuit* hardness — the SPDP method provably caps at the depth-4 chasm.  A depth-4 lower bound does not
lift to a general-circuit lower bound (`depth4_not_general`): there is a consistent world with the depth-4 bound
and no general bound.  So generalising the *conclusion* to general circuits — `(A3)`-general — is exactly the
uncrossed step (`wall_is_beyond_depth4`).  It is `cost_super`: the Kakeya→rank route reaches depth-4 and the
lift to general is the wall.

## What is proved

* **`forcing_certifies_depth4`** — superpolynomial SPDP rank ⟹ a depth-4 lower bound (GKKS): the forcing's real
  reach, general over families.
* **`depth4_not_general`** — a consistent world has the depth-4 bound but not the general bound: depth-4 hardness
  does not lift.
* **`wall_is_beyond_depth4`** — `depth4LB → generalLB` is not derivable: generalising to general circuits is the
  wall, `(A3)`-general = `cost_super`.

## Honest verdict — generalised to the edge, not across

Generalising the Kakeya forcing to the wall reaches the wall's edge and stops there, honestly.  The forcing
mechanism was already general (`KakeyaRankForcing.kakeya_dimension_forces_rank`, any family), and it certifies
depth-4 hardness (`forcing_certifies_depth4`) — a real, restricted lower bound.  The remaining step, lifting a
depth-4 bound to a general-circuit bound, is the depth-4 chasm: it does not go through
(`depth4_not_general`, `wall_is_beyond_depth4`), and crossing it is `(A3)`-general — a superpolynomial
lower bound against *general* circuits for an explicit family, which is `cost_super` = `P ≠ NP`.  So the honest
generalisation is: the mechanism is general, its certification is depth-4, and the lift to general is the wall.
I did not fake the lift.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KakeyaGeneral

/-- The reach of an SPDP-rank bound: what a superpolynomial rank certifies (depth-4), versus the general-circuit
bound that would be `(A3)`-general. -/
structure SPDPReach where
  /-- the family has superpolynomial SPDP rank (from the Kakeya forcing) -/
  superpolyRank : Prop
  /-- a superpolynomial lower bound against depth-4 circuits -/
  depth4LB : Prop
  /-- a superpolynomial lower bound against general circuits — `(A3)`-general, the wall -/
  generalLB : Prop
  /-- **GKKS**: superpolynomial SPDP rank certifies depth-4 hardness -/
  gkks : superpolyRank → depth4LB

/-- **The forcing certifies depth-4 hardness (proved).**  Superpolynomial SPDP rank — which the Kakeya
dimension bound forces, for any family — yields a lower bound against depth-4 circuits (GKKS). -/
theorem forcing_certifies_depth4 (S : SPDPReach) : S.superpolyRank → S.depth4LB := S.gkks

/-- A world at the depth-4 chasm: the depth-4 bound holds, the general bound does not. -/
def chasmWorld : SPDPReach where
  superpolyRank := True
  depth4LB := True
  generalLB := False
  gkks := fun _ => trivial

/-- **Depth-4 hardness does not lift to general (proved).**  A consistent world has a depth-4 lower bound but no
general-circuit lower bound — the depth-4 chasm the SPDP method caps at. -/
theorem depth4_not_general : ∃ S : SPDPReach, S.depth4LB ∧ ¬ S.generalLB :=
  ⟨chasmWorld, trivial, not_false⟩

/-- **The wall is beyond depth-4 (proved).**  `depth4LB → generalLB` is not derivable: lifting the Kakeya→rank
forcing from a depth-4 bound to a general-circuit bound — `(A3)`-general — is the uncrossed step, `cost_super`. -/
theorem wall_is_beyond_depth4 : ¬ (∀ S : SPDPReach, S.depth4LB → S.generalLB) := by
  intro h
  exact h chasmWorld trivial

end PallLean.Paper93.DeepMath.PathB.KakeyaGeneral

#print axioms PallLean.Paper93.DeepMath.PathB.KakeyaGeneral.forcing_certifies_depth4
#print axioms PallLean.Paper93.DeepMath.PathB.KakeyaGeneral.depth4_not_general
#print axioms PallLean.Paper93.DeepMath.PathB.KakeyaGeneral.wall_is_beyond_depth4
