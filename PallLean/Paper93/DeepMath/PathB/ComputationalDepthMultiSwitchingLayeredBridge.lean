import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingCommonShallow
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingFuelSafeTerminal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBounded
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AltReduce
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafTowerCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundCount2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwitchingNormalize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TotalClauseCount

/-!
# Bridge from a common switching trunk to one layered collapse round

`CommonShallowAt` controls a finite family of canonical gate trees at every reached leaf of one
shared trunk.  The layered collapse API instead asks for `Shallows`, which covers both the direct
and De Morgan-dual canonical trees of every bottom gate.  This file isolates the exact missing
compatibility condition: the common family must enumerate both polarities of every bottom gate.

Under that coverage condition, each reached leaf supports the existing collapse round.  The result
explicitly retains the common-trunk depth charge, preserves the fuel bound at the leaf, bounds the
new bottom width by `residualDepth + 1`, and drops one alternating layer.  Thus no new semantic
collapse construction is required; the remaining iteration obligation is to instantiate the common
switching count with the two-polarity bottom-gate family of the current layered circuit.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.Depth3.Layered
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration

/-- The finite common-switching family contains canonical trees equal to both trees needed by
`leafCollapse` for every bottom gate of `C`.  Tree equality, rather than syntactic list equality,
allows order-preserving duplicate normalization without changing the collapse interface. -/
def CoversLayeredBottoms {n G : ℕ} (gates : Fin G → List (Clause n))
    (C : Layered n) : Prop :=
  ∀ cs ∈ bottomGates C,
    (∃ g, ∀ fuel σ, canonicalDT (gates g) fuel σ = canonicalDT cs fuel σ) ∧
    (∃ g, ∀ fuel σ, canonicalDT (gates g) fuel σ = canonicalDT (negDNF cs) fuel σ)

/-- The exact list used to index one round's common-switching family.  It deliberately retains
duplicates: the counting theorem charges indexed gates, so quotienting here would obscure the exact
relation to the circuit's syntactic bottom-gate count. -/
def layeredBottomFamilyList {n : ℕ} (C : Layered n) : List (List (Clause n)) :=
  bottomGates C ++ (bottomGates C).map negDNF

/-- Canonical finite indexing of both polarities of every syntactic bottom gate. -/
def layeredBottomFamily {n : ℕ} (C : Layered n) :
    Fin (layeredBottomFamilyList C).length → List (Clause n) :=
  fun g => (layeredBottomFamilyList C).get g

/-- The indexed family has exactly twice the syntactic bottom-gate count. -/
theorem layeredBottomFamilyList_length {n : ℕ} (C : Layered n) :
    (layeredBottomFamilyList C).length = 2 * (bottomGates C).length := by
  simp [layeredBottomFamilyList, Nat.two_mul]

/-- The canonical indexing discharges the abstract coverage premise of the layered bridge. -/
theorem layeredBottomFamily_covers {n : ℕ} (C : Layered n) :
    CoversLayeredBottoms (layeredBottomFamily C) C := by
  intro cs hcs
  constructor
  · obtain ⟨g, hg⟩ := List.get_of_mem
      (show cs ∈ layeredBottomFamilyList C by
        exact List.mem_append_left _ hcs)
    exact ⟨g, fun fuel σ => by
      change canonicalDT ((layeredBottomFamilyList C).get g) fuel σ = _
      rw [hg]⟩
  · obtain ⟨g, hg⟩ := List.get_of_mem
      (show negDNF cs ∈ layeredBottomFamilyList C by
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨cs, hcs, rfl⟩)
    exact ⟨g, fun fuel σ => by
      change canonicalDT ((layeredBottomFamilyList C).get g) fuel σ = _
      rw [hg]⟩

/-- The exact two-polarity family with duplicate clauses removed inside each indexed gate.  The
index type and hence the exact gate charge are unchanged. -/
def normalizedLayeredBottomFamily {n : ℕ} (C : Layered n) :
    Fin (layeredBottomFamilyList C).length → List (Clause n) :=
  fun g => (layeredBottomFamily C g).eraseDups

/-- Normalization preserves both canonical trees required by the layered collapse. -/
theorem normalizedLayeredBottomFamily_covers {n : ℕ} (C : Layered n) :
    CoversLayeredBottoms (normalizedLayeredBottomFamily C) C := by
  intro cs hcs
  obtain ⟨⟨g, hg⟩, ⟨gneg, hgneg⟩⟩ := layeredBottomFamily_covers C cs hcs
  constructor
  · exact ⟨g, fun fuel σ => (canonicalDT_eraseDups _ fuel σ).trans (hg fuel σ)⟩
  · exact ⟨gneg, fun fuel σ => (canonicalDT_eraseDups _ fuel σ).trans (hgneg fuel σ)⟩

/-- A common-shallow certificate is unchanged by pointwise duplicate normalization. -/
theorem commonShallowAt_normalizedLayeredBottomFamily_iff {n : ℕ} (C : Layered n)
    (fuel : ℕ) (σ : Restriction n) (trunkDepth residualDepth : ℕ) :
    CommonShallowAt (normalizedLayeredBottomFamily C) fuel σ trunkDepth residualDepth ↔
      CommonShallowAt (layeredBottomFamily C) fuel σ trunkDepth residualDepth := by
  constructor <;> rintro ⟨trunk, hdepth, hleaf⟩
  · refine ⟨trunk, hdepth, fun x hx => ?_⟩
    obtain ⟨hext, hagree, hshallow⟩ := hleaf x hx
    refine ⟨hext, hagree, fun g => ?_⟩
    have hg := hshallow g
    change (canonicalDT (layeredBottomFamily C g).eraseDups fuel
      (CommonTree.run trunk x)).depth ≤ residualDepth at hg
    rw [canonicalDT_eraseDups] at hg
    exact hg
  · refine ⟨trunk, hdepth, fun x hx => ?_⟩
    obtain ⟨hext, hagree, hshallow⟩ := hleaf x hx
    refine ⟨hext, hagree, fun g => ?_⟩
    change (canonicalDT (layeredBottomFamily C g).eraseDups fuel
      (CommonTree.run trunk x)).depth ≤ residualDepth
    rw [canonicalDT_eraseDups]
    exact hshallow g

/-- A circuit-level clause-count bound transfers without loss to the exact two-polarity indexing. -/
theorem layeredBottomFamily_length_le {n m : ℕ} {C : Layered n}
    (hcount : BottomCount m C) :
    ∀ g, (layeredBottomFamily C g).length ≤ m := by
  intro g
  have hg : layeredBottomFamily C g ∈ layeredBottomFamilyList C := List.get_mem _ _
  rw [layeredBottomFamilyList, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hcount _ hg
  · rw [List.mem_map] at hg
    obtain ⟨cs, hcs, hg⟩ := hg
    rw [← hg]
    simpa [negDNF] using hcount cs hcs

/-- A circuit-level bottom-width bound also transfers without loss through De Morgan polarity. -/
theorem layeredBottomFamily_width_le {n w : ℕ} {C : Layered n}
    (hw : BottomWidth w C) :
    ∀ g T, T ∈ layeredBottomFamily C g → T.lits.length ≤ w := by
  intro g T hT
  have hg : layeredBottomFamily C g ∈ layeredBottomFamilyList C := List.get_mem _ _
  rw [layeredBottomFamilyList, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hw _ hg T hT
  · rw [List.mem_map] at hg
    obtain ⟨cs, hcs, hg⟩ := hg
    rw [← hg, negDNF, List.mem_map] at hT
    obtain ⟨S, hS, rfl⟩ := hT
    simpa using hw cs hcs S hS

/-- Width bounds survive duplicate normalization. -/
theorem normalizedLayeredBottomFamily_width_le {n w : ℕ} {C : Layered n}
    (hw : BottomWidth w C) :
    ∀ g T, T ∈ normalizedLayeredBottomFamily C g → T.lits.length ≤ w := by
  intro g T hT
  apply layeredBottomFamily_width_le hw g T
  exact (mem_eraseDups_iff T _).mp hT

/-- Clause-count bounds survive duplicate normalization. -/
theorem normalizedLayeredBottomFamily_length_le {n m : ℕ} {C : Layered n}
    (hcount : BottomCount m C) :
    ∀ g, (normalizedLayeredBottomFamily C g).length ≤ m := by
  intro g
  exact (eraseDups_length_le _).trans (layeredBottomFamily_length_le hcount g)

/-- Every normalized indexed gate is duplicate-free, without an extra circuit invariant. -/
theorem normalizedLayeredBottomFamily_nodup {n : ℕ} (C : Layered n) :
    ∀ g, (normalizedLayeredBottomFamily C g).Nodup := by
  intro g
  exact eraseDups_nodup _

/-- The exact ragged alphabet of the raw two-polarity family has twice the circuit's total
bottom-clause occurrence count. -/
theorem layeredBottomFamily_total_length {n : ℕ} (C : Layered n) :
    (∑ g, (layeredBottomFamily C g).length) = 2 * bottomClauseCount C := by
  rw [← List.sum_ofFn]
  have hofn : List.ofFn (layeredBottomFamily C) = layeredBottomFamilyList C := by
    simpa only [layeredBottomFamily] using
      (List.ofFn_get (l := layeredBottomFamilyList C))
  have hlen : List.ofFn (fun g => (layeredBottomFamily C g).length) =
      (List.ofFn (layeredBottomFamily C)).map List.length := by
    rw [List.map_ofFn]
    have hfun : (fun g => (layeredBottomFamily C g).length) =
        List.length ∘ layeredBottomFamily C := by
      funext g
      rfl
    rw [hfun]
  rw [hlen, hofn]
  rw [layeredBottomFamilyList, List.map_append, List.sum_append]
  change ((bottomGates C).map List.length).sum +
      (((bottomGates C).map negDNF).map List.length).sum =
    2 * bottomClauseCount C
  have hneg : (((bottomGates C).map negDNF).map List.length).sum =
      ((bottomGates C).map List.length).sum := by
    apply congrArg List.sum
    rw [List.map_map]
    apply List.map_congr_left
    intro cs _
    simp [negDNF]
  rw [hneg]
  simp [bottomClauseCount, Nat.two_mul]

/-- Pointwise duplicate normalization can only shrink the exact ragged alphabet. -/
theorem normalizedLayeredBottomFamily_total_length_le {n : ℕ} (C : Layered n) :
    (∑ g, (normalizedLayeredBottomFamily C g).length) ≤ 2 * bottomClauseCount C := by
  calc
    (∑ g, (normalizedLayeredBottomFamily C g).length) ≤
        ∑ g, (layeredBottomFamily C g).length := by
      apply Finset.sum_le_sum
      intro g _
      exact eraseDups_length_le _
    _ = 2 * bottomClauseCount C := layeredBottomFamily_total_length C

/-- The switching encoder's list-`Nodup` premise transfers from the two circuit polarities.  This
assumption is intentionally explicit: the existing `BottomClean` invariant controls literals inside
each clause, not duplicate clauses inside a bottom gate. -/
theorem layeredBottomFamily_nodup {n : ℕ} {C : Layered n}
    (hnd : ∀ cs ∈ bottomGates C, cs.Nodup ∧ (negDNF cs).Nodup) :
    ∀ g, (layeredBottomFamily C g).Nodup := by
  intro g
  have hg : layeredBottomFamily C g ∈ layeredBottomFamilyList C := List.get_mem _ _
  rw [layeredBottomFamilyList, List.mem_append] at hg
  rcases hg with hg | hg
  · exact (hnd _ hg).1
  · rw [List.mem_map] at hg
    obtain ⟨cs, hcs, hg⟩ := hg
    rw [← hg]
    exact (hnd cs hcs).2

/-- The realized-prefix shell contraction specialized to the exact current circuit family.  Its
density charge now exposes the precise indexed gate count; by `layeredBottomFamilyList_length` this
is `2 * (bottomGates C).length`. -/
theorem layered_commonShallowBad_scaled_le_of_realized_density
    {n w d m fuel K residualDepth savingNum savingDen : ℕ} {C : Layered n}
    (hnd : ∀ cs ∈ bottomGates C, cs.Nodup ∧ (negDNF cs).Nodup)
    (hw : BottomWidth w C) (hcount : BottomCount m C)
    (hKfuel : K ≤ fuel) (hdpos : 0 < d) (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity :
      (4 * ((w + 1) * ((layeredBottomFamilyList C).length * m + 1))) * K + K ≤ n + 1) :
    (commonShallowBad (layeredBottomFamily C) fuel K d residualDepth).card *
        2 ^ ((savingNum * K) / savingDen) ≤
      (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
  exact commonShallowBad_scaled_le_of_realized_density
    (layeredBottomFamily_nodup hnd)
    (layeredBottomFamily_width_le hw)
    (layeredBottomFamily_length_le hcount)
    hKfuel hdpos hdK hKn hsave hdensity

/-- Circuit-specialized shell contraction after order-preserving normalization.  Unlike the raw
family theorem, this requires no duplicate-clause hypothesis; the exact family size remains twice
the syntactic bottom-gate count and the original width and term bounds still transfer. -/
theorem normalizedLayered_commonShallowBad_scaled_le_of_realized_density
    {n w d m fuel K residualDepth savingNum savingDen : ℕ} {C : Layered n}
    (hw : BottomWidth w C) (hcount : BottomCount m C)
    (hKfuel : K ≤ fuel) (hdpos : 0 < d) (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity :
      (4 * ((w + 1) * ((layeredBottomFamilyList C).length * m + 1))) * K + K ≤ n + 1) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel K d residualDepth).card *
        2 ^ ((savingNum * K) / savingDen) ≤
      (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
  exact commonShallowBad_scaled_le_of_realized_density
    (normalizedLayeredBottomFamily_nodup C)
    (normalizedLayeredBottomFamily_width_le hw)
    (normalizedLayeredBottomFamily_length_le hcount)
    hKfuel hdpos hdK hKn hsave hdensity

/-- Circuit-specialized contraction charging the normalized family's exact total number of clause
occurrences.  This is the ragged counterpart of the rectangular `G*m` theorem above. -/
theorem normalizedLayered_commonShallowBad_scaled_le_of_actual_density
    {n w d fuel K residualDepth savingNum savingDen : ℕ} {C : Layered n}
    (hw : BottomWidth w C)
    (hKfuel : K ≤ fuel) (hdpos : 0 < d) (hdK : d ≤ K) (hKn : K ≤ n)
    (hsave : (savingNum * K) / savingDen ≤ d)
    (hdensity :
      (4 * ((w + 1) *
        ((∑ g, (normalizedLayeredBottomFamily C g).length) + 1))) * K + K ≤ n + 1) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel K d residualDepth).card *
        2 ^ ((savingNum * K) / savingDen) ≤
      (Finset.univ.filter fun σ : Restriction n => stars σ = K).card := by
  exact commonShallowBad_scaled_le_of_actual_density
    (normalizedLayeredBottomFamily_nodup C)
    (normalizedLayeredBottomFamily_width_le hw)
    hKfuel hdpos hdK hKn hsave hdensity

/-! ### Linear ragged-alphabet survivor schedule

The exact total-clause recurrence replaces the old quadratic rectangular cap by a linear one.
The schedule below repeats the half-shell audit with that smaller cap. -/

/-- Worst-case exact alphabet after a collapse round with at most `M` input bottom gates. -/
def layeredRoundActualKeyCap (M s : ℕ) : ℕ :=
  2 * M * 2 ^ (s + 1)

/-- Backward gap scale for the exact-alphabet recurrence. -/
def layeredRoundActualScale (M s : ℕ) : ℕ :=
  100 * (s + 2) * (layeredRoundActualKeyCap M s + 1)

def layeredRoundActualLive (M s r j : ℕ) : ℕ :=
  2000 * (s + 2) * (layeredRoundActualKeyCap M s + 1) *
    (r * layeredRoundActualScale M s ^ j)

def layeredRoundActualShell (M s r j : ℕ) : ℕ :=
  20 * (r * layeredRoundActualScale M s ^ j)

theorem layeredRoundActualShell_succ_eq_live (M s r j : ℕ) :
    layeredRoundActualShell M s r (j + 1) = layeredRoundActualLive M s r j := by
  simp only [layeredRoundActualShell, layeredRoundActualLive, layeredRoundActualScale, pow_succ]
  ring

/-- Every exact normalized alphabet below the linear recurrence cap satisfies the schedule's
density premise. -/
theorem layeredRoundActual_density {A M s r j : ℕ}
    (hA : A ≤ layeredRoundActualKeyCap M s) :
    (4 * (((s + 1) + 1) * (A + 1))) * layeredRoundActualShell M s r j +
        layeredRoundActualShell M s r j ≤ layeredRoundActualLive M s r j + 1 := by
  let R := r * layeredRoundActualScale M s ^ j
  have hplus : A + 1 ≤ layeredRoundActualKeyCap M s + 1 := Nat.add_le_add_right hA 1
  have hs : s + 1 + 1 = s + 2 := by omega
  rw [hs]
  simp only [layeredRoundActualShell, layeredRoundActualLive]
  change 4 * ((s + 2) * (A + 1)) * (20 * R) + 20 * R ≤
    2000 * (s + 2) * (layeredRoundActualKeyCap M s + 1) * R + 1
  calc
    4 * ((s + 2) * (A + 1)) * (20 * R) + 20 * R ≤
        4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * (20 * R) + 20 * R := by
          gcongr
    _ ≤ 2000 * (s + 2) * (layeredRoundActualKeyCap M s + 1) * R + 1 := by
      have hspos : 1 ≤ s + 2 := by omega
      have hcap : 1 ≤ layeredRoundActualKeyCap M s + 1 := by omega
      have hprod : 1 ≤ (s + 2) * (layeredRoundActualKeyCap M s + 1) :=
        Nat.mul_pos hspos hcap
      calc
        4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * (20 * R) + 20 * R ≤
            4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * (20 * R) +
              20 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * R := by
                gcongr
                exact Nat.mul_le_mul_left 20 hprod
        _ = 100 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * R := by ring
        _ ≤ 2000 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * R := by
          gcongr
          norm_num
        _ ≤ 2000 * (s + 2) * (layeredRoundActualKeyCap M s + 1) * R + 1 := by
          rw [show 2000 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * R =
            2000 * (s + 2) * (layeredRoundActualKeyCap M s + 1) * R by ring]
          omega

/-- Half-shell contraction at every level of the linear exact-alphabet schedule. -/
theorem normalizedLayered_commonShallowBad_scaled_le_actual_schedule
    {M s r j fuel : ℕ}
    {C : Layered (layeredRoundActualLive M s r j)}
    (hr : 0 < r)
    (hw : BottomWidth (s + 1) C)
    (hactual : (∑ g, (normalizedLayeredBottomFamily C g).length) ≤
      layeredRoundActualKeyCap M s)
    (hKfuel : layeredRoundActualShell M s r j ≤ fuel) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel
        (layeredRoundActualShell M s r j)
        (10 * (r * layeredRoundActualScale M s ^ j)) s).card *
        2 ^ (10 * (r * layeredRoundActualScale M s ^ j)) ≤
      (Finset.univ.filter fun σ : Restriction (layeredRoundActualLive M s r j) =>
        stars σ = layeredRoundActualShell M s r j).card := by
  let R := r * layeredRoundActualScale M s ^ j
  have hscale : 0 < layeredRoundActualScale M s := by
    simp [layeredRoundActualScale]
  have hR : 0 < R := Nat.mul_pos hr (pow_pos hscale _)
  have hdpos : 0 < 10 * R := by omega
  have hdK : 10 * R ≤ layeredRoundActualShell M s r j := by
    simp only [layeredRoundActualShell]
    change 10 * R ≤ 20 * R
    omega
  have hKn : layeredRoundActualShell M s r j ≤ layeredRoundActualLive M s r j := by
    simp only [layeredRoundActualShell, layeredRoundActualLive]
    change 20 * R ≤ 2000 * (s + 2) * (layeredRoundActualKeyCap M s + 1) * R
    have hcoef : 20 ≤ 2000 * (s + 2) * (layeredRoundActualKeyCap M s + 1) := by
      nlinarith
    exact Nat.mul_le_mul_right R hcoef
  have hsave : 1 * layeredRoundActualShell M s r j / 2 ≤ 10 * R := by
    simp only [layeredRoundActualShell]
    change 1 * (20 * R) / 2 ≤ 10 * R
    omega
  have hbound := normalizedLayered_commonShallowBad_scaled_le_of_actual_density
    (residualDepth := s) (d := 10 * R) (savingNum := 1) (savingDen := 2)
    hw hKfuel hdpos hdK hKn hsave (layeredRoundActual_density hactual)
  have hhalf : 1 * layeredRoundActualShell M s r j / 2 = 10 * R := by
    simp only [layeredRoundActualShell]
    change 1 * (20 * R) / 2 = 10 * R
    omega
  rw [hhalf] at hbound
  simpa [R] using hbound

/-- The linear recurrence improves the schedule by one factor of `M`, but does not close the
worst-case self-reference when the gate bound can already dominate the ambient live dimension. -/
theorem not_layeredRoundActual_worstCase_density_of_live_le_gateBound
    {N M s K : ℕ} (hN : 0 < N) (hNM : N ≤ M) (hK : 0 < K) :
    ¬(4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * K + K ≤ N + 1) := by
  intro hdensity
  have hM : 1 ≤ M := hN.trans_le hNM
  have hpow : 1 ≤ 2 ^ (s + 1) := one_le_pow₀ (by omega)
  have hcap : M ≤ layeredRoundActualKeyCap M s := by
    rw [layeredRoundActualKeyCap]
    have htwo : M ≤ 2 * M := by omega
    exact htwo.trans (Nat.le_mul_of_pos_right _ hpow)
  have hbase : N + 1 < 4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) := by
    have hs : 2 ≤ s + 2 := by omega
    have hcap' : M + 1 ≤ layeredRoundActualKeyCap M s + 1 := Nat.add_le_add_right hcap 1
    nlinarith
  have hmul :
      4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) ≤
        4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * K := by
    simpa using Nat.le_mul_of_pos_right
      (4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1))) hK
  omega

/-- Any nonempty round satisfying the linear-cap density premise must have a genuinely sublinear
bottom-gate cap.  This is a necessary condition on the *external cap* `M`, not merely on the exact
alphabet of one unusually sparse circuit. -/
theorem layeredRoundActual_gateBound_lt_live_of_density
    {N M s K : ℕ} (hN : 0 < N) (hK : 0 < K)
    (hdensity :
      4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * K + K ≤ N + 1) :
    M < N := by
  apply Nat.lt_of_not_ge
  intro hNM
  exact not_layeredRoundActual_worstCase_density_of_live_le_gateBound hN hNM hK hdensity

/-- The density premise forces substantially more than the qualitative condition `M < N`.
After exposing the exact linear alphabet cap and using only `K ≥ 1`, the live dimension must
contain the full residual-width-adjusted base.  This is the quantitative target that any
structural sparsification theorem must meet. -/
theorem layeredRoundActual_gateBound_margin_of_density
    {N M s K : ℕ} (hK : 0 < K)
    (hdensity :
      4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * K + K ≤ N + 1) :
    8 * (s + 2) * M * 2 ^ (s + 1) + 4 * (s + 2) ≤ N := by
  have hbase :
      8 * (s + 2) * M * 2 ^ (s + 1) + 4 * (s + 2) =
        4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) := by
    simp only [layeredRoundActualKeyCap]
    ring
  have hmul :
      4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) ≤
        4 * ((s + 2) * (layeredRoundActualKeyCap M s + 1)) * K := by
    exact Nat.le_mul_of_pos_right _ hK
  rw [hbase]
  omega

/-- A standard positive-degree polynomial size cap cannot serve as the uniform gate cap for the
linear ragged-alphabet schedule.  For `M = N^c`, `c > 0`, the cap already dominates `N`, so the
density premise fails on every nonempty shell.  This does not say every polynomial-size circuit
has that many bottom gates; it says the class-level upper bound alone is too weak. -/
theorem not_layeredRoundActual_worstCase_density_of_polynomial_gateCap
    {N c s K : ℕ} (hN : 0 < N) (hc : 0 < c) (hK : 0 < K) :
    ¬(4 * ((s + 2) * (layeredRoundActualKeyCap (N ^ c) s + 1)) * K + K ≤ N + 1) := by
  apply not_layeredRoundActual_worstCase_density_of_live_le_gateBound hN _ hK
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : c ≠ 0)
  rw [pow_succ]
  exact Nat.le_mul_of_pos_left N (pow_pos hN c)

/-- Specialization of the necessary density condition to the circuit-owned active-occurrence
measure.  Even after eliminating the external gate-cap interface, every nonempty round still
requires the current slot count to be strictly below the live dimension. -/
theorem layeredRoundActual_bottomSlotCount_lt_live_of_density
    {N s K : ℕ} {C : Layered N} (hN : 0 < N) (hK : 0 < K)
    (hdensity :
      4 * ((s + 2) * (layeredRoundActualKeyCap (bottomSlotCount C) s + 1)) * K + K ≤
        N + 1) :
    bottomSlotCount C < N := by
  exact layeredRoundActual_gateBound_lt_live_of_density hN hK hdensity

/-- Circuit-owned form of the exact density margin: occurrence accounting removes the external
gate cap, but a valid nonempty round still needs the complete residual-width-adjusted density base
for every charged bottom slot. -/
theorem layeredRoundActual_bottomSlotCount_margin_of_density
    {N s K : ℕ} {C : Layered N} (hK : 0 < K)
    (hdensity :
      4 * ((s + 2) * (layeredRoundActualKeyCap (bottomSlotCount C) s + 1)) * K + K ≤
        N + 1) :
    8 * (s + 2) * bottomSlotCount C * 2 ^ (s + 1) + 4 * (s + 2) ≤ N := by
  exact layeredRoundActual_gateBound_margin_of_density hK hdensity

/-! ### A round-dependent survivor schedule

After one collapse with residual depth `s`, the next normalized family has width `s+1`, at most
`2*M` indexed gates, and at most `M*2^(s+1)` clauses per gate.  The following schedule charges the
resulting product by `2*M^2*2^(s+1)` and chooses consecutive live dimensions so that the current
round's `20*r` survivor shell is exactly the next round's ambient cube. -/

/-- Uniform upper bound for the next normalized family's gate/term key product. -/
def layeredRoundKeyCap (M s : ℕ) : ℕ :=
  2 * M ^ 2 * 2 ^ (s + 1)

/-- Backward scale between the gap parameters of two consecutive survivor rounds. -/
def layeredRoundScale (M s : ℕ) : ℕ :=
  100 * (s + 2) * (layeredRoundKeyCap M s + 1)

/-- Full live-variable budget at schedule level `j`. -/
def layeredRoundLive (M s r j : ℕ) : ℕ :=
  2000 * (s + 2) * (layeredRoundKeyCap M s + 1) *
    (r * layeredRoundScale M s ^ j)

/-- Survivor shell retained by schedule level `j`. -/
def layeredRoundShell (M s r j : ℕ) : ℕ :=
  20 * (r * layeredRoundScale M s ^ j)

/-- The survivor shell of level `j+1` is exactly the full cube required at level `j`.  Thus the
density budget composes for every prescribed finite number of rounds, rather than merely holding
independently on unrelated ambient cubes. -/
theorem layeredRoundShell_succ_eq_live (M s r j : ℕ) :
    layeredRoundShell M s r (j + 1) = layeredRoundLive M s r j := by
  simp only [layeredRoundShell, layeredRoundLive, layeredRoundScale, pow_succ]
  ring

/-- The audited next-family recurrence fits the key cap used by the schedule. -/
theorem layeredRound_keyProduct_le {G m M s : ℕ}
    (hG : G ≤ 2 * M) (hm : m ≤ M * 2 ^ (s + 1)) :
    G * m ≤ layeredRoundKeyCap M s := by
  calc
    G * m ≤ (2 * M) * (M * 2 ^ (s + 1)) := Nat.mul_le_mul hG hm
    _ = layeredRoundKeyCap M s := by simp [layeredRoundKeyCap, pow_two]; ring

/-- Every level of the schedule absorbs any gate/term product below the recurrence cap. -/
theorem layeredRound_density {G m M s r j : ℕ} (hkey : G * m ≤ layeredRoundKeyCap M s) :
    (4 * (((s + 1) + 1) * (G * m + 1))) * layeredRoundShell M s r j +
        layeredRoundShell M s r j ≤ layeredRoundLive M s r j + 1 := by
  let R := r * layeredRoundScale M s ^ j
  have hplus : G * m + 1 ≤ layeredRoundKeyCap M s + 1 := Nat.add_le_add_right hkey 1
  have hs : s + 1 + 1 = s + 2 := by omega
  rw [hs]
  simp only [layeredRoundShell, layeredRoundLive]
  change 4 * ((s + 2) * (G * m + 1)) * (20 * R) + 20 * R ≤
    2000 * (s + 2) * (layeredRoundKeyCap M s + 1) * R + 1
  calc
    4 * ((s + 2) * (G * m + 1)) * (20 * R) + 20 * R ≤
        4 * ((s + 2) * (layeredRoundKeyCap M s + 1)) * (20 * R) + 20 * R := by
          gcongr
    _ ≤ 2000 * (s + 2) * (layeredRoundKeyCap M s + 1) * R + 1 := by
      have hspos : 1 ≤ s + 2 := by omega
      have hcap : 1 ≤ layeredRoundKeyCap M s + 1 := by omega
      have hA : 1 ≤ (s + 2) * (layeredRoundKeyCap M s + 1) :=
        Nat.mul_pos hspos hcap
      calc
        4 * ((s + 2) * (layeredRoundKeyCap M s + 1)) * (20 * R) + 20 * R ≤
            4 * ((s + 2) * (layeredRoundKeyCap M s + 1)) * (20 * R) +
              20 * ((s + 2) * (layeredRoundKeyCap M s + 1)) * R := by
                gcongr
                exact Nat.mul_le_mul_left 20 hA
        _ = 100 * ((s + 2) * (layeredRoundKeyCap M s + 1)) * R := by ring
        _ ≤ 2000 * ((s + 2) * (layeredRoundKeyCap M s + 1)) * R := by
          gcongr
          norm_num
        _ ≤ 2000 * (s + 2) * (layeredRoundKeyCap M s + 1) * R + 1 := by
          rw [show 2000 * ((s + 2) * (layeredRoundKeyCap M s + 1)) * R =
            2000 * (s + 2) * (layeredRoundKeyCap M s + 1) * R by ring]
          omega

/-- The worst-case cap does not close self-referentially when the gate bound is already at least
the ambient live dimension.  For every nonempty survivor shell its density premise is then false.
This records the quantitative limitation of the geometric schedule: it composes for an externally
fixed `M`, but cannot by itself handle a worst-case `M` growing linearly (or faster) with `N`. -/
theorem not_layeredRound_worstCase_density_of_live_le_gateBound
    {N M s K : ℕ} (hN : 0 < N) (hNM : N ≤ M) (hK : 0 < K) :
    ¬(4 * ((s + 2) * (layeredRoundKeyCap M s + 1)) * K + K ≤ N + 1) := by
  intro hdensity
  have hM : 1 ≤ M := hN.trans_le hNM
  have hpow : 1 ≤ 2 ^ (s + 1) := one_le_pow₀ (by omega)
  have hsq : M ≤ M ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_left M hM
  have hcap : M ≤ layeredRoundKeyCap M s := by
    rw [layeredRoundKeyCap]
    calc
      M ≤ M ^ 2 := hsq
      _ ≤ 2 * M ^ 2 * 2 ^ (s + 1) := by
        have : M ^ 2 ≤ 2 * M ^ 2 := by omega
        exact this.trans (Nat.le_mul_of_pos_right _ hpow)
  have hbase : N + 1 < 4 * ((s + 2) * (layeredRoundKeyCap M s + 1)) := by
    have hs : 2 ≤ s + 2 := by omega
    have hcap' : M + 1 ≤ layeredRoundKeyCap M s + 1 := Nat.add_le_add_right hcap 1
    nlinarith
  have hmul :
      4 * ((s + 2) * (layeredRoundKeyCap M s + 1)) ≤
        4 * ((s + 2) * (layeredRoundKeyCap M s + 1)) * K := by
    simpa using Nat.le_mul_of_pos_right
      (4 * ((s + 2) * (layeredRoundKeyCap M s + 1))) hK
  omega

/-- Circuit-specialized half-shell contraction at every level of the composable schedule.  It
uses the normalized two-polarity family, so no duplicate-clause premise is required. -/
theorem normalizedLayered_commonShallowBad_scaled_le_schedule
    {M s r j fuel : ℕ}
    {C : Layered (layeredRoundLive M s r j)}
    (hr : 0 < r)
    (hw : BottomWidth (s + 1) C)
    (hcnt : (bottomGates C).length ≤ M)
    (hcount : BottomCount (M * 2 ^ (s + 1)) C)
    (hKfuel : layeredRoundShell M s r j ≤ fuel) :
    (commonShallowBad (normalizedLayeredBottomFamily C) fuel
        (layeredRoundShell M s r j) (10 * (r * layeredRoundScale M s ^ j)) s).card *
        2 ^ (10 * (r * layeredRoundScale M s ^ j)) ≤
      (Finset.univ.filter fun σ : Restriction (layeredRoundLive M s r j) =>
        stars σ = layeredRoundShell M s r j).card := by
  let R := r * layeredRoundScale M s ^ j
  have hscale : 0 < layeredRoundScale M s := by
    simp [layeredRoundScale]
  have hR : 0 < R := Nat.mul_pos hr (pow_pos hscale _)
  have hG : (layeredBottomFamilyList C).length ≤ 2 * M := by
    rw [layeredBottomFamilyList_length]
    exact Nat.mul_le_mul_left 2 hcnt
  have hkey : (layeredBottomFamilyList C).length * (M * 2 ^ (s + 1)) ≤
      layeredRoundKeyCap M s :=
    layeredRound_keyProduct_le hG le_rfl
  have hdpos : 0 < 10 * R := by omega
  have hdK : 10 * R ≤ layeredRoundShell M s r j := by
    simp only [layeredRoundShell]
    change 10 * R ≤ 20 * R
    omega
  have hKn : layeredRoundShell M s r j ≤ layeredRoundLive M s r j := by
    simp only [layeredRoundShell, layeredRoundLive]
    change 20 * R ≤ 2000 * (s + 2) * (layeredRoundKeyCap M s + 1) * R
    have hspos : 1 ≤ s + 2 := by omega
    have hcap : 1 ≤ layeredRoundKeyCap M s + 1 := by omega
    have hcoef : 20 ≤ 2000 * (s + 2) * (layeredRoundKeyCap M s + 1) := by
      nlinarith
    exact Nat.mul_le_mul_right R hcoef
  have hsave : 1 * layeredRoundShell M s r j / 2 ≤ 10 * R := by
    simp only [layeredRoundShell]
    change 1 * (20 * R) / 2 ≤ 10 * R
    omega
  have hbound := normalizedLayered_commonShallowBad_scaled_le_of_realized_density
    (residualDepth := s) (d := 10 * R) (savingNum := 1) (savingDen := 2)
    hw hcount hKfuel hdpos hdK hKn hsave (layeredRound_density hkey)
  have hhalf : 1 * layeredRoundShell M s r j / 2 = 10 * R := by
    simp only [layeredRoundShell]
    change 1 * (20 * R) / 2 = 10 * R
    omega
  rw [hhalf] at hbound
  simpa [R] using hbound

/-- Residual common shallowness at a reached trunk leaf is precisely the root-level `Shallows`
hypothesis needed by the existing layered collapse round, with `+ 1` converting `≤` to `<`. -/
theorem CommonShallowAt.leaf_shallows {n G : ℕ} {gates : Fin G → List (Clause n)}
    {fuel : ℕ} {σ : Restriction n} {trunkDepth residualDepth : ℕ} {C : Layered n}
    (h : CommonShallowAt gates fuel σ trunkDepth residualDepth)
    (hcover : CoversLayeredBottoms gates C)
    (x : Fin n → Bool) (hx : Rung4Restriction.Extends σ x) :
    ∃ trunk : CommonTree n (Restriction n),
      CommonTree.depth trunk ≤ trunkDepth ∧
      stars (CommonTree.run trunk x) ≤ stars σ ∧
      Shallows fuel (CommonTree.run trunk x) (residualDepth + 1) C := by
  obtain ⟨trunk, hdepth, hleaf⟩ := h
  obtain ⟨hext, _hagree, hshallow⟩ := hleaf x hx
  have hstars : stars (CommonTree.run trunk x) ≤ stars σ := by
    apply Finset.card_le_card
    intro v hv
    rw [mem_freeVars] at hv ⊢
    cases hσv : σ v with
    | none => rfl
    | some b => rw [hext v b hσv] at hv; simp at hv
  refine ⟨trunk, hdepth, hstars, ?_⟩
  intro cs hcs
  obtain ⟨⟨g, hg⟩, ⟨gneg, hgneg⟩⟩ := hcover cs hcs
  constructor
  · rw [← hg fuel (CommonTree.run trunk x)]
    exact Nat.lt_succ_of_le (hshallow g)
  · rw [← hgneg fuel (CommonTree.run trunk x)]
    exact Nat.lt_succ_of_le (hshallow gneg)

/-- A common-shallow trunk can be followed by the existing collapse round at every reached leaf.
The conclusion records all interfaces needed for iteration: trunk cost, leaf fuel, semantic
equivalence, output bottom width, and the one-level alternation reduction. -/
theorem CommonShallowAt.leaf_collapseRound_altO {n G k : ℕ}
    {gates : Fin G → List (Clause n)} {fuel : ℕ} {σ : Restriction n}
    {trunkDepth residualDepth : ℕ} {C : Layered n}
    (h : CommonShallowAt gates fuel σ trunkDepth residualDepth)
    (hfuel : stars σ ≤ fuel) (hcover : CoversLayeredBottoms gates C)
    (halt : AltO (k + 3) C)
    (x : Fin n → Bool) (hx : Rung4Restriction.Extends σ x) :
    ∃ trunk : CommonTree n (Restriction n),
      CommonTree.depth trunk ≤ trunkDepth ∧
      let τ := CommonTree.run trunk x
      stars τ ≤ fuel ∧
      EquivOn τ C (collapseRound fuel τ C) ∧
      BottomWidth (residualDepth + 1) (collapseRound fuel τ C) ∧
      AltO (k + 2) (collapseRound fuel τ C) := by
  obtain ⟨trunk, hdepth, hstars, hshallow⟩ := h.leaf_shallows hcover x hx
  refine ⟨trunk, hdepth, ?_⟩
  dsimp only
  have hstarsFuel : stars (CommonTree.run trunk x) ≤ fuel := hstars.trans hfuel
  exact ⟨hstarsFuel,
    collapseRound_EquivOn fuel hstarsFuel C,
    collapseRound_BottomWidth fuel (CommonTree.run trunk x) hshallow,
    collapseRound_AltO fuel (CommonTree.run trunk x) halt⟩

/-- Exact family-size and term-count recurrence at a common-trunk leaf.  If the current circuit has
at most `M` syntactic bottom gates, the next circuit still has at most `M`; if the residual switching
depth is `s`, every next-round indexed gate has at most `M * 2^(s+1)` clauses. -/
theorem CommonShallowAt.leaf_collapseRound_family_bounds {n G M : ℕ}
    {gates : Fin G → List (Clause n)} {fuel : ℕ} {σ : Restriction n}
    {trunkDepth residualDepth : ℕ} {C : Layered n}
    (h : CommonShallowAt gates fuel σ trunkDepth residualDepth)
    (hfuel : stars σ ≤ fuel) (hcover : CoversLayeredBottoms gates C)
    (hM1 : 1 ≤ M) (hC : NonEmptyGates C) (hcnt : (bottomGates C).length ≤ M)
    (x : Fin n → Bool) (hx : Rung4Restriction.Extends σ x) :
    ∃ trunk : CommonTree n (Restriction n),
      CommonTree.depth trunk ≤ trunkDepth ∧
      let τ := CommonTree.run trunk x
      stars τ ≤ fuel ∧
      (bottomGates (collapseRound fuel τ C)).length ≤ M ∧
      BottomCount (M * 2 ^ (residualDepth + 1)) (collapseRound fuel τ C) := by
  obtain ⟨trunk, hdepth, hstars, hshallow⟩ := h.leaf_shallows hcover x hx
  refine ⟨trunk, hdepth, ?_⟩
  dsimp only
  have hstarsFuel : stars (CommonTree.run trunk x) ≤ fuel := hstars.trans hfuel
  exact ⟨hstarsFuel,
    (collapseRound_count_le fuel (CommonTree.run trunk x) hC).trans hcnt,
    collapseRound_BottomCount fuel (CommonTree.run trunk x) hM1 hC hshallow hcnt⟩

/-- The next round's exact ragged encoder alphabet is only linear in the current bottom-gate
bound.  The old rectangular recurrence paid `2*M^2*2^(s+1)`; total-clause conservation through
the merge gives `2*M*2^(s+1)` for the normalized two-polarity family. -/
theorem CommonShallowAt.leaf_collapseRound_actualAlphabet_bound {n G M : ℕ}
    {gates : Fin G → List (Clause n)} {fuel : ℕ} {σ : Restriction n}
    {trunkDepth residualDepth : ℕ} {C : Layered n}
    (h : CommonShallowAt gates fuel σ trunkDepth residualDepth)
    (hfuel : stars σ ≤ fuel) (hcover : CoversLayeredBottoms gates C)
    (hcnt : (bottomGates C).length ≤ M)
    (x : Fin n → Bool) (hx : Rung4Restriction.Extends σ x) :
    ∃ trunk : CommonTree n (Restriction n),
      CommonTree.depth trunk ≤ trunkDepth ∧
      let τ := CommonTree.run trunk x
      stars τ ≤ fuel ∧
      (∑ g, (normalizedLayeredBottomFamily
        (collapseRound fuel τ C) g).length) ≤
          layeredRoundActualKeyCap M residualDepth := by
  obtain ⟨trunk, hdepth, hstars, hshallow⟩ := h.leaf_shallows hcover x hx
  refine ⟨trunk, hdepth, ?_⟩
  dsimp only
  have hstarsFuel : stars (CommonTree.run trunk x) ≤ fuel := hstars.trans hfuel
  refine ⟨hstarsFuel, ?_⟩
  have hbound := (normalizedLayeredBottomFamily_total_length_le
    (collapseRound fuel (CommonTree.run trunk x) C)).trans
      (Nat.mul_le_mul_left 2
        (collapseRound_bottomClauseCount_le hcnt hshallow))
  simpa [layeredRoundActualKeyCap, Nat.mul_assoc] using hbound

/-- Fully occurrence-sensitive recurrence.  The current circuit supplies its own cap through
`bottomSlotCount`; no externally chosen bottom-gate bound is needed.  The unit charge in
`bottomSlotCount` is necessary for legal empty `dnf`/`cnf` gates. -/
theorem CommonShallowAt.leaf_collapseRound_slotAlphabet_bound {n G : ℕ}
    {gates : Fin G → List (Clause n)} {fuel : ℕ} {σ : Restriction n}
    {trunkDepth residualDepth : ℕ} {C : Layered n}
    (h : CommonShallowAt gates fuel σ trunkDepth residualDepth)
    (hfuel : stars σ ≤ fuel) (hcover : CoversLayeredBottoms gates C)
    (x : Fin n → Bool) (hx : Rung4Restriction.Extends σ x) :
    ∃ trunk : CommonTree n (Restriction n),
      CommonTree.depth trunk ≤ trunkDepth ∧
      let τ := CommonTree.run trunk x
      stars τ ≤ fuel ∧
      (∑ g, (normalizedLayeredBottomFamily
        (collapseRound fuel τ C) g).length) ≤
          layeredRoundActualKeyCap (bottomSlotCount C) residualDepth := by
  obtain ⟨trunk, hdepth, hstars, hshallow⟩ := h.leaf_shallows hcover x hx
  refine ⟨trunk, hdepth, ?_⟩
  dsimp only
  have hstarsFuel : stars (CommonTree.run trunk x) ≤ fuel := hstars.trans hfuel
  refine ⟨hstarsFuel, ?_⟩
  have hbound := (normalizedLayeredBottomFamily_total_length_le
    (collapseRound fuel (CommonTree.run trunk x) C)).trans
      (Nat.mul_le_mul_left 2
        (collapseRound_bottomClauseCount_le_bottomSlotCount hshallow))
  simpa [layeredRoundActualKeyCap, Nat.mul_assoc] using hbound

/-- Actual slot recurrence at a reached common-trunk leaf.  Unlike the normalized encoder-alphabet
bound above, this is the invariant consumed by the following round's circuit-owned density premise.
The verified restriction/collapse pipeline controls it by `M * (2^(s+1) + 1)`; in particular the
available structural estimate is not a roundwise sparsification theorem. -/
theorem CommonShallowAt.leaf_collapseRound_bottomSlotCount_bound {n G : ℕ}
    {gates : Fin G → List (Clause n)} {fuel : ℕ} {σ : Restriction n}
    {trunkDepth residualDepth : ℕ} {C : Layered n}
    (h : CommonShallowAt gates fuel σ trunkDepth residualDepth)
    (hfuel : stars σ ≤ fuel) (hcover : CoversLayeredBottoms gates C)
    (hne : NonEmptyGates C)
    (x : Fin n → Bool) (hx : Rung4Restriction.Extends σ x) :
    ∃ trunk : CommonTree n (Restriction n),
      CommonTree.depth trunk ≤ trunkDepth ∧
      let τ := CommonTree.run trunk x
      stars τ ≤ fuel ∧
      bottomSlotCount (collapseRound fuel τ C) ≤
        bottomSlotCount C * (2 ^ (residualDepth + 1) + 1) := by
  obtain ⟨trunk, hdepth, hstars, hshallow⟩ := h.leaf_shallows hcover x hx
  refine ⟨trunk, hdepth, ?_⟩
  dsimp only
  have hstarsFuel : stars (CommonTree.run trunk x) ≤ fuel := hstars.trans hfuel
  exact ⟨hstarsFuel, collapseRound_bottomSlotCount_le hne hshallow⟩

/-! ## Baseline mass at canonical trunk leaves -/

/-- A support-aware baseline: the number of distinct designated essential coordinates that remain
live on the current subcube.  Unlike component count, this charges replicated literals sharing one
coordinate only once. -/
def distinctEssentialCoordinateBaseline {n : ℕ}
    (ρ : Restriction n) (support : Finset (Fin n)) : ℕ :=
  (support ∩ freeVars ρ).card

/-- The independent one-literal components carried by the designated coordinates that are still
live.  The finite-set conversion makes distinctness explicit. -/
noncomputable def independentLiveLiteralFamily {n : ℕ}
    (ρ : Restriction n) (support : Finset (Fin n)) : List (Layered n) :=
  (support ∩ freeVars ρ).toList.map
    (fun i => Layered.dnf [⟨[Rung4Literal.pos i]⟩])

/-- On independent literals, the support-aware baseline is exactly the semantic
baseline-plus-excess mass, rather than merely a proxy for it. -/
theorem aggregateSemanticBaselineExcess_independentLiveLiteralFamily {n : ℕ}
    (ρ : Restriction n) (support : Finset (Fin n)) :
    aggregateSemanticBaselineExcess ρ (independentLiveLiteralFamily ρ support) =
      distinctEssentialCoordinateBaseline ρ support := by
  rw [aggregateSemanticBaselineExcess_eq]
  unfold independentLiveLiteralFamily distinctEssentialCoordinateBaseline
  simp only [List.map_map]
  change
    (((support ∩ freeVars ρ).toList.map fun i =>
      semanticBottomSlotCount ρ (Layered.dnf [⟨[Rung4Literal.pos i]⟩])).sum = _)
  have hmap :
      ((support ∩ freeVars ρ).toList.map fun i =>
        semanticBottomSlotCount ρ (Layered.dnf [⟨[Rung4Literal.pos i]⟩])) =
      (support ∩ freeVars ρ).toList.map (fun _ => 1) := by
    apply List.map_congr_left
    intro i hi
    apply semanticBottomSlotCount_singleLiteral_of_free
    exact mem_freeVars.mp (Finset.mem_inter.mp (Finset.mem_toList.mp hi)).2
  calc
    _ = ((support ∩ freeVars ρ).toList.map (fun _ => 1)).sum :=
      congrArg List.sum hmap
    _ = (support ∩ freeVars ρ).card := by simp

/-- When all designated coordinates are initially live, a canonical prefix removes exactly the
designated coordinates that occur among its fresh queries. -/
theorem distinctEssentialCoordinateBaseline_prefixEndpoint {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool)
    (support : Finset (Fin n)) (hsupport : support ⊆ freeVars σ) :
    distinctEssentialCoordinateBaseline (CommonTree.prefixEndpoint σ t budget x) support =
      (support \ CommonTree.prefixVars σ t budget x).card := by
  rw [distinctEssentialCoordinateBaseline, CommonTree.freeVars_prefixEndpoint]
  congr 1
  ext i
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hi, _, hnot⟩
    exact ⟨hi, hnot⟩
  · rintro ⟨hi, hnot⟩
    exact ⟨hi, hsupport hi, hnot⟩

/-- Sharp pathwise survivor bound for independent essential coordinates: a prefix of budget `d`
can discharge at most `d` of them. -/
theorem distinctEssentialCoordinateBaseline_prefixEndpoint_ge_sub {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool)
    (support : Finset (Fin n)) (hsupport : support ⊆ freeVars σ) :
    support.card - budget ≤
      distinctEssentialCoordinateBaseline (CommonTree.prefixEndpoint σ t budget x) support := by
  rw [distinctEssentialCoordinateBaseline_prefixEndpoint σ t budget x support hsupport]
  rw [Finset.card_sdiff]
  have hinter : (support ∩ CommonTree.prefixVars σ t budget x).card ≤ budget := by
    calc
      (support ∩ CommonTree.prefixVars σ t budget x).card ≤
          (CommonTree.prefixVars σ t budget x).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ ≤ budget := by
        rw [CommonTree.prefixVars]
        exact (List.toFinset_card_le _).trans
          (by
            rw [CommonTree.queryVars_prefixEndpoints]
            exact List.length_take_le _ _)
  have hinter' : (CommonTree.prefixVars σ t budget x ∩ support).card ≤ budget := by
    simpa [Finset.inter_comm] using hinter
  omega

/-- Consequently a factor-`factor` pathwise contraction is impossible whenever the unavoidable
`q - budget` survivors already exceed the permitted `q / factor` mass. -/
theorem distinctEssentialCoordinateBaseline_no_scaled_contraction {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget factor : ℕ)
    (x : Fin n → Bool) (support : Finset (Fin n))
    (hsupport : support ⊆ freeVars σ)
    (hgap : support.card < factor * (support.card - budget)) :
    ¬ factor *
        distinctEssentialCoordinateBaseline (CommonTree.prefixEndpoint σ t budget x) support ≤
      support.card := by
  intro hcontract
  have hsurvive := distinctEssentialCoordinateBaseline_prefixEndpoint_ge_sub
    σ t budget x support hsupport
  have := Nat.mul_le_mul_left factor hsurvive
  omega

/-- The exact switching-round factor can therefore contract this baseline only outside the
explicit linear survivor-gap obstruction. -/
theorem distinctEssentialCoordinateBaseline_no_switchingFactor_contraction {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget s : ℕ)
    (x : Fin n → Bool) (support : Finset (Fin n))
    (hsupport : support ⊆ freeVars σ)
    (hgap : support.card <
      (8 * (s + 2) * 2 ^ (s + 1)) * (support.card - budget)) :
    ¬ (8 * (s + 2) * 2 ^ (s + 1)) *
        distinctEssentialCoordinateBaseline (CommonTree.prefixEndpoint σ t budget x) support ≤
      support.card :=
  distinctEssentialCoordinateBaseline_no_scaled_contraction
    σ t budget (8 * (s + 2) * 2 ^ (s + 1)) x support hsupport hgap

/-- A simple regime exposing the obstruction: if the independent support is more than twice the
trunk budget, the required switching factor cannot contract it on any canonical prefix leaf. -/
theorem distinctEssentialCoordinateBaseline_no_switchingFactor_contraction_of_twice_budget_lt
    {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget s : ℕ)
    (x : Fin n → Bool) (support : Finset (Fin n))
    (hsupport : support ⊆ freeVars σ) (hwide : 2 * budget < support.card) :
    ¬ (8 * (s + 2) * 2 ^ (s + 1)) *
        distinctEssentialCoordinateBaseline (CommonTree.prefixEndpoint σ t budget x) support ≤
      support.card := by
  apply distinctEssentialCoordinateBaseline_no_switchingFactor_contraction
    σ t budget s x support hsupport
  have hfactor : 2 ≤ 8 * (s + 2) * 2 ^ (s + 1) := by
    have hs : 2 ≤ s + 2 := by omega
    have hp0 : 0 < 2 ^ (s + 1) := pow_pos (by omega) _
    have hp : 1 ≤ 2 ^ (s + 1) := by omega
    nlinarith
  have hlinear : support.card < 2 * (support.card - budget) := by omega
  exact hlinear.trans_le (Nat.mul_le_mul_right (support.card - budget) hfactor)

/-! ### Failure of a support-plus-semantic-excess alphabet bound -/

/-- Six clean indexed gates obtained by permuting the same three positive literals.  Pointwise
clause deduplication does nothing: each indexed gate contains exactly one clause, while all six
clauses have the same semantics. -/
def permutedThreeLiteralGates : List (List (Clause 3)) :=
  [ [⟨[Rung4Literal.pos 0, Rung4Literal.pos 1, Rung4Literal.pos 2]⟩]
  , [⟨[Rung4Literal.pos 0, Rung4Literal.pos 2, Rung4Literal.pos 1]⟩]
  , [⟨[Rung4Literal.pos 1, Rung4Literal.pos 0, Rung4Literal.pos 2]⟩]
  , [⟨[Rung4Literal.pos 1, Rung4Literal.pos 2, Rung4Literal.pos 0]⟩]
  , [⟨[Rung4Literal.pos 2, Rung4Literal.pos 0, Rung4Literal.pos 1]⟩]
  , [⟨[Rung4Literal.pos 2, Rung4Literal.pos 1, Rung4Literal.pos 0]⟩] ]

/-- The corresponding survivor components, one bottom gate per indexed encoder gate. -/
def permutedThreeLiteralSurvivors : List (Layered 3) :=
  permutedThreeLiteralGates.map Layered.dnf

/-- The example meets both duplicate-free hypotheses used by the switching encoder: gate lists
are `Nodup`, and no clause repeats a variable. -/
theorem permutedThreeLiteralGates_clean :
    ∀ gate ∈ permutedThreeLiteralGates,
      gate.Nodup ∧ ∀ T ∈ gate, (T.lits.map litVarOf).Nodup := by
  simp [permutedThreeLiteralGates, litVarOf]

/-- The realized ragged key alphabet has six entries. -/
theorem permutedThreeLiteralGates_alphabet_mass :
    (permutedThreeLiteralGates.map List.length).sum = 6 := by
  rfl

/-- Two representatives isolated from the permutation family.  They have the same conjunction
semantics, but put different live variables first in the canonical walk. -/
def orderedThreeLiteralGate012 : List (Clause 3) :=
  [⟨[Rung4Literal.pos 0, Rung4Literal.pos 1, Rung4Literal.pos 2]⟩]

def orderedThreeLiteralGate102 : List (Clause 3) :=
  [⟨[Rung4Literal.pos 1, Rung4Literal.pos 0, Rung4Literal.pos 2]⟩]

/-- The two representatives compute the same Boolean function. -/
theorem orderedThreeLiteral_dnfEval_eq (x : Fin 3 → Bool) :
    dnfEval orderedThreeLiteralGate012 x = dnfEval orderedThreeLiteralGate102 x := by
  simp [orderedThreeLiteralGate012, orderedThreeLiteralGate102, dnfEval,
    Rung4DNFTerm.evalLits, Rung4Literal.eval]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> decide

/-- Literal-order canonicalization is not coverage-preserving for the bridge's current exact-tree
interface: already at fuel one on the fully live cube, the two semantically identical singleton
gates query different roots. -/
theorem orderedThreeLiteral_canonicalDT_ne :
    canonicalDT orderedThreeLiteralGate012 1 (fun _ => none) ≠
      canonicalDT orderedThreeLiteralGate102 1 (fun _ => none) := by
  intro h
  simp [orderedThreeLiteralGate012, orderedThreeLiteralGate102, canonicalDT,
    anyTermSat, termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue,
    Depth3.litFree, Depth3.litFixedVal, litFalse, litVar] at h

/-- Consequently no single quotient representative can retain exact canonical-tree coverage of
both literal orders.  Whole-family deduplication by conjunction semantics therefore does not plug
directly into `CoversLayeredBottoms`. -/
theorem orderedThreeLiteral_no_common_exactTree_representative :
    ¬ ∃ gate : List (Clause 3),
      (∀ fuel σ, canonicalDT gate fuel σ = canonicalDT orderedThreeLiteralGate012 fuel σ) ∧
      (∀ fuel σ, canonicalDT gate fuel σ = canonicalDT orderedThreeLiteralGate102 fuel σ) := by
  rintro ⟨gate, h012, h102⟩
  apply orderedThreeLiteral_canonicalDT_ne
  exact (h012 1 (fun _ => none)).symm.trans (h102 1 (fun _ => none))

/-- A semantics-invariant replacement for the encoder's `(gate,term)` key cannot recover the
queried coordinate from the literal-position stream.  Both reordered singleton gates select
position zero first, but that position denotes coordinate zero in one gate and coordinate one in
the other.  Thus any semantic prefix code must separately retain queried-variable identity (or
equivalent order information); quotienting only the raw key is not injective. -/
theorem orderedThreeLiteral_no_semanticKey_position_decoder
    {α : Type} (key : List (Clause 3) → α)
    (hsemantic : ∀ gate₁ gate₂,
      (∀ x, dnfEval gate₁ x = dnfEval gate₂ x) → key gate₁ = key gate₂) :
    ¬ ∃ decode : α → Fin 3 → Fin 3,
      decode (key orderedThreeLiteralGate012) 0 = 0 ∧
      decode (key orderedThreeLiteralGate102) 0 = 1 := by
  rintro ⟨decode, hdecode0, hdecode1⟩
  have hkey : key orderedThreeLiteralGate012 = key orderedThreeLiteralGate102 :=
    hsemantic _ _ orderedThreeLiteral_dnfEval_eq
  rw [hkey] at hdecode0
  have : (0 : Fin 3) = 1 := hdecode0.symm.trans hdecode1
  omega

/-! ### Coordinate-augmented semantic labels -/

/-- The smallest direct repair of the failed semantic-key decoder: retain one optional queried
coordinate per prefix slot, together with the symmetric multiset of abstract semantic keys.
`Option` makes both components total on paths shorter than `d`, exactly as in the realized-prefix
encoder. -/
abbrev CoordinateSemanticPrefixLabel (n d S : ℕ) :=
  (Fin d → Option (Fin n)) × Option (Sym (Fin S) d)

/-- Exact cardinality of the direct coordinate-augmented semantic label.  Even if semantic
quotienting makes `S` tiny, the selected-coordinate word contributes the unavoidable
`(n + 1)^d` factor. -/
theorem card_coordinateSemanticPrefixLabel (n d S : ℕ) :
    Fintype.card (CoordinateSemanticPrefixLabel n d S) =
      (n + 1) ^ d * ((S + d - 1).choose d + 1) := by
  simp [CoordinateSemanticPrefixLabel, Fintype.card_prod, Sym.card_sym_eq_choose]

/-- The coordinate repair is incompatible with the current proportional half-shell balance,
independently of the semantic-key alphabet size.  At `K = 2*r`, `d = r`, and saving exponent
`r`, its coordinate word already contains at least as many labels as the symmetric code over all
`n` coordinates.  The previously proved exact stars-and-bars obstruction therefore applies even
when `S = 0`. -/
theorem not_coordinateSemantic_exact_balance_half
    {n S r : ℕ} (hr : 0 < r) (h2rn : 2 * r ≤ n) :
    ¬(Nat.choose n (2 * r - r) * 2 ^ (n - (2 * r - r)) *
          ((n + 1) ^ r * ((S + r - 1).choose r + 1)) * 2 ^ r ≤
        Nat.choose n (2 * r) * 2 ^ (n - 2 * r)) := by
  intro hbalance
  apply not_realizedPrefix_exact_balance_half_of_live_le_keys
    (n := n) (A := n) (w := 0) hr h2rn (le_refl n)
  have hcoordinates : (n + r - 1).choose r + 1 ≤ (n + 1) ^ r :=
    prefixSymCode_le_pow n r hr
  have hsemantic : 1 ≤ (S + r - 1).choose r + 1 := by omega
  have haugment : (n + r - 1).choose r + 1 ≤
      (n + 1) ^ r * ((S + r - 1).choose r + 1) := by
    exact hcoordinates.trans (by
      simpa only [mul_one] using Nat.mul_le_mul_left ((n + 1) ^ r) hsemantic)
  have haugment' : 1 * ((n + r - 1).choose r + 1) ≤
      (n + 1) ^ r * ((S + r - 1).choose r + 1) := by
    simpa only [one_mul] using haugment
  calc
    Nat.choose n (2 * r - r) * 2 ^ (n - (2 * r - r)) *
          ((0 + 1) ^ r * ((n + r - 1).choose r + 1)) * 2 ^ r ≤
        Nat.choose n (2 * r - r) * 2 ^ (n - (2 * r - r)) *
          ((n + 1) ^ r * ((S + r - 1).choose r + 1)) * 2 ^ r := by
            simp only [zero_add, one_pow]
            exact Nat.mul_le_mul_right (2 ^ r)
              (Nat.mul_le_mul_left
                (Nat.choose n (2 * r - r) * 2 ^ (n - (2 * r - r))) haugment')
    _ ≤ Nat.choose n (2 * r) * 2 ^ (n - 2 * r) := hbalance

/-! ### Endpoint-fiber audit for unordered coordinate labels -/

/-- Charging the selected coordinates only among those fixed at the endpoint does shrink each
individual label fiber.  Across the whole endpoint shell, however, that shrinkage cancels exactly:
the compatible endpoint/coordinate-set pairs outnumber the root shell by
`choose K d * 2^d`. -/
theorem endpointFiber_coordinateSet_exact_count
    {n K d : ℕ} (hdK : d ≤ K) (hKn : K ≤ n) :
    Nat.choose n (K - d) * 2 ^ (n - (K - d)) *
          Nat.choose (n - (K - d)) d =
      Nat.choose n K * 2 ^ (n - K) * Nat.choose K d * 2 ^ d := by
  have hchoose :
      Nat.choose n (K - d) * Nat.choose (n - (K - d)) d =
        Nat.choose n K * Nat.choose K d := by
    have hmul := Nat.choose_mul (n := n) (k := K) (s := K - d)
      (Nat.sub_le K d)
    have hsub : K - (K - d) = d := by omega
    have hsymm : Nat.choose K (K - d) = Nat.choose K d := by
      simpa using Nat.choose_symm hdK
    rw [hsub, hsymm] at hmul
    omega
  have hexponent : n - (K - d) = (n - K) + d := by omega
  have hpowSplit : 2 ^ (n - (K - d)) = 2 ^ (n - K) * 2 ^ d := by
    rw [hexponent, pow_add]
  calc
    Nat.choose n (K - d) * 2 ^ (n - (K - d)) *
          Nat.choose (n - (K - d)) d =
        Nat.choose n (K - d) * (2 ^ (n - K) * 2 ^ d) *
          Nat.choose (n - (K - d)) d := by rw [hpowSplit]
    _ = (Nat.choose n (K - d) * Nat.choose (n - (K - d)) d) *
          2 ^ (n - K) * 2 ^ d := by ring
    _ = (Nat.choose n K * Nat.choose K d) * 2 ^ (n - K) * 2 ^ d := by
      rw [hchoose]
    _ = Nat.choose n K * 2 ^ (n - K) * Nat.choose K d * 2 ^ d := by ring

/-- Thus the proposed endpoint-fiber restriction does not merely miss the requested exponential
saving: for every nonempty selected prefix it gives a strictly larger compatible-pair space than
the original shell.  Consequently, merely replacing the ambient label count by the full
endpoint-compatible fiber cannot prove contraction, including when auditing independent-literal
families.  A successful refinement would have to bound the actually realized canonical image. -/
theorem endpointFiber_coordinateSet_strictly_larger
    {n K d : ℕ} (hd : 0 < d) (hdK : d ≤ K) (hKn : K ≤ n) :
    Nat.choose n K * 2 ^ (n - K) <
      Nat.choose n (K - d) * 2 ^ (n - (K - d)) *
        Nat.choose (n - (K - d)) d := by
  rw [endpointFiber_coordinateSet_exact_count hdK hKn]
  have hroot : 0 < Nat.choose n K * 2 ^ (n - K) :=
    Nat.mul_pos (Nat.choose_pos hKn) (pow_pos (by omega) _)
  have hchoose : 0 < Nat.choose K d := Nat.choose_pos hdK
  have hpow : 1 < 2 ^ d := by
    exact Nat.one_lt_pow (by omega) (by omega)
  have hchooseOne : 1 ≤ Nat.choose K d := by omega
  have hfactor : 1 < Nat.choose K d * 2 ^ d :=
    hpow.trans_le (by
      have hmul := Nat.mul_le_mul_right (2 ^ d) hchooseOne
      simpa using hmul)
  have hgrow := Nat.mul_lt_mul_of_pos_left hfactor hroot
  simpa only [mul_one, Nat.mul_assoc] using hgrow

/-! ### Realized endpoint multiplicity on independent literals -/

/-- The generic independent-literal family contains one positive singleton gate per coordinate. -/
def independentLiteralGates (n : ℕ) : Fin n → List (Clause n) :=
  fun i => [⟨[Rung4Literal.pos i]⟩]

/-- Free exactly `S`, fixing every other coordinate to false. -/
def independentRoot {n : ℕ} (S : Finset (Fin n)) : Restriction n :=
  fun i => if i ∈ S then none else some false

def independentAllFalse (n : ℕ) : Restriction n := fun _ => some false

def independentAssignment (n : ℕ) : Fin n → Bool := fun _ => false

/-- A path in a common tree contains no more queries than the tree's maximum depth. -/
theorem CommonTree.queryVars_length_le_depth {n : ℕ} {α : Type}
    (t : CommonTree n α) (x : Fin n → Bool) :
    (CommonTree.queryVars t x).length ≤ CommonTree.depth t := by
  induction t with
  | leaf a => simp [CommonTree.queryVars, CommonTree.depth]
  | query i lo hi ihlo ihhi =>
      by_cases hxi : x i
      · simp only [CommonTree.queryVars, hxi, if_true, List.length_cons,
          CommonTree.depth]
        omega
      · simp only [CommonTree.queryVars, hxi, Bool.false_eq_true, if_false,
          List.length_cons, CommonTree.depth]
        omega

/-- Changing a coordinate absent from the followed query path does not change the reached leaf. -/
theorem CommonTree.run_update_of_not_mem_queryVars {n : ℕ} {α : Type}
    (t : CommonTree n α) (x : Fin n → Bool) (i : Fin n)
    (hi : i ∉ CommonTree.queryVars t x) :
    CommonTree.run t (Function.update x i (!x i)) = CommonTree.run t x := by
  induction t with
  | leaf a => rfl
  | query j lo hiTree ihlo ihhi =>
      by_cases hxj : x j
      · simp only [CommonTree.queryVars, hxj, if_true, List.mem_cons, not_or] at hi
        have hji : j ≠ i := Ne.symm hi.1
        have hupdate : Function.update x i (!x i) j = x j :=
          Function.update_of_ne hji _ _
        rw [CommonTree.run, hupdate]
        simp [hxj, ihhi hi.2]
      · simp only [CommonTree.queryVars, hxj, Bool.false_eq_true, if_false,
          List.mem_cons, not_or] at hi
        have hji : j ≠ i := Ne.symm hi.1
        have hupdate : Function.update x i (!x i) j = x j :=
          Function.update_of_ne hji _ _
        rw [CommonTree.run, hupdate]
        simp [hxj, ihlo hi.2]

theorem independentRoot_extends {n : ℕ} (S : Finset (Fin n)) :
    Rung4Restriction.Extends (independentRoot S) (independentAssignment n) := by
  intro i b hi
  simp only [independentRoot] at hi
  split at hi
  · contradiction
  · simpa [independentAssignment] using hi.symm

/-- Flipping any live coordinate of an independent root still extends that root. -/
theorem independentRoot_extends_update {n : ℕ} (S : Finset (Fin n))
    (i : Fin n) (hiS : i ∈ S) :
    Rung4Restriction.Extends (independentRoot S)
      (Function.update (independentAssignment n) i true) := by
  intro j b hj
  by_cases hjS : j ∈ S
  · simp [independentRoot, hjS] at hj
  · have hb : b = false := by
      simpa [independentRoot, hjS] using hj.symm
    subst b
    have hji : j ≠ i := by
      intro h
      subst j
      exact hjS hiS
    simp [Function.update_of_ne hji, independentAssignment]

/-- A live independent singleton gate has canonical depth one at fuel one. -/
theorem independentLiteral_canonicalDT_depth_of_free {n : ℕ}
    (ρ : Restriction n) (i : Fin n) (hi : ρ i = none) :
    (canonicalDT (independentLiteralGates n i) 1 ρ).depth = 1 := by
  simp [independentLiteralGates, canonicalDT, anyTermSat, termSat, activeTerm,
    termFalsified, freeLits, Depth3.litTrue, litVar, litFixedVal, litFalse,
    litFree, fixVar, BoolDecisionTree.depth, hi]

/-- Independent singleton gates saturate the semantic bad event at residual depth zero: a trunk
of depth `d` cannot make all `K>d` live coordinates constant on every reached subcube. -/
theorem independentRoot_not_commonShallowAt_zero {n d : ℕ}
    (S : Finset (Fin n)) (hd : d < S.card) :
    ¬ CommonShallowAt (independentLiteralGates n) 1 (independentRoot S) d 0 := by
  rintro ⟨trunk, hdepth, hleaf⟩
  let x := independentAssignment n
  have hpathCard : (CommonTree.queryVars trunk x).toFinset.card ≤ d := by
    calc
      (CommonTree.queryVars trunk x).toFinset.card ≤
          (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ d := hdepth
  have hnotSubset : ¬ S ⊆ (CommonTree.queryVars trunk x).toFinset := by
    intro hsubset
    have := Finset.card_le_card hsubset
    omega
  obtain ⟨i, hiS, hiPath⟩ := Finset.not_subset.mp hnotSubset
  let y : Fin n → Bool := Function.update x i true
  have hx : Rung4Restriction.Extends (independentRoot S) x := independentRoot_extends S
  have hy : Rung4Restriction.Extends (independentRoot S) y := by
    exact independentRoot_extends_update S i hiS
  obtain ⟨_, hτx, hshallowx⟩ := hleaf x hx
  obtain ⟨_, hτy, _⟩ := hleaf y hy
  have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
    exact CommonTree.run_update_of_not_mem_queryVars trunk x i
      (by simpa using hiPath)
  have hfree : CommonTree.run trunk x i = none := by
    cases hτ : CommonTree.run trunk x i with
    | none => rfl
    | some b =>
        have hbx : b = false := by
          simpa [x, independentAssignment] using hτx i b hτ
        have hby : b = true := by
          have : CommonTree.run trunk y i = some b := by simpa [hrun] using hτ
          simpa [y, x] using hτy i b this
        exact False.elim (Bool.false_ne_true (hbx.symm.trans hby))
  have hdeep := independentLiteral_canonicalDT_depth_of_free
    (CommonTree.run trunk x) i hfree
  have hzero := hshallowx i
  omega

/-- Hence every independent root on the `K`-live shell is semantically bad whenever `d<K` and
the residual threshold is zero. -/
theorem independentRoot_mem_commonShallowBad_zero {n K d : ℕ}
    (S : Finset (Fin n)) (hcard : S.card = K) (hd : d < K) :
    independentRoot S ∈ commonShallowBad (independentLiteralGates n) 1 K d 0 := by
  rw [mem_commonShallowBad]
  constructor
  · rw [stars]
    have hfree : freeVars (independentRoot S) = S := by
      ext i
      simp [mem_freeVars, independentRoot]
    rw [hfree, hcard]
  · exact independentRoot_not_commonShallowAt_zero S (by omega)

/-! ### A positive-residual disjoint-block obstruction -/

/-- General semantic core of the disjoint-block obstruction.  If every set of at most
`trunkDepth` queried coordinates misses the whole support of some indexed gate, and that gate's
canonical tree remains deeper than `residualDepth` whenever its support is free, then no common
trunk of the prescribed depth can shallow the family on the fully live cube.

The statement deliberately separates the finite block-packing argument (`hmiss`) from the
gate-specific canonical-depth computation (`hdeep`).  It therefore applies uniformly at arbitrary
positive residual depth and does not depend on a particular contiguous-block encoding. -/
theorem supportedGates_not_commonShallowAt_allFree
    {n G fuel trunkDepth residualDepth : ℕ}
    (gates : Fin G → List (Clause n)) (support : Fin G → Finset (Fin n))
    (hmiss : ∀ path : Finset (Fin n), path.card ≤ trunkDepth →
      ∃ g, Disjoint (support g) path)
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i = none) →
        residualDepth < (canonicalDT (gates g) fuel rho).depth) :
    ¬ CommonShallowAt gates fuel (fun _ : Fin n ↦ none) trunkDepth residualDepth := by
  rintro ⟨trunk, hdepth, hleaf⟩
  let x : Fin n → Bool := fun _ ↦ false
  let path : Finset (Fin n) := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ trunkDepth := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ trunkDepth := hdepth
  obtain ⟨g, hgdisj⟩ := hmiss path hpathCard
  have hx : Rung4Restriction.Extends (fun _ : Fin n ↦ none) x := by
    intro i b hi
    simp at hi
  have hfree (i : Fin n) (hi : i ∉ path) : CommonTree.run trunk x i = none := by
    let y : Fin n → Bool := Function.update x i true
    have hy : Rung4Restriction.Extends (fun _ : Fin n ↦ none) y := by
      intro j b hj
      simp at hj
    obtain ⟨_, htx, _⟩ := hleaf x hx
    obtain ⟨_, hty, _⟩ := hleaf y hy
    have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
      exact CommonTree.run_update_of_not_mem_queryVars trunk x i (by simpa [path] using hi)
    cases ht : CommonTree.run trunk x i with
    | none => rfl
    | some b =>
        have hbx : b = false := by
          simpa [x] using htx i b ht
        have hby : b = true := by
          have : CommonTree.run trunk y i = some b := by simpa [hrun] using ht
          simpa [y, x] using hty i b this
        exact False.elim (Bool.false_ne_true (hbx.symm.trans hby))
  obtain ⟨_, _, hshallow⟩ := hleaf x hx
  have hgateDeep : residualDepth <
      (canonicalDT (gates g) fuel (CommonTree.run trunk x)).depth := by
    apply hdeep (CommonTree.run trunk x) g
    intro i hiSupport
    apply hfree i
    exact (Finset.disjoint_left.mp hgdisj hiSupport)
  exact (Nat.not_lt_of_ge (hshallow g)) hgateDeep

/-- The obstruction schema places the fully live root in the actual fixed-shell bad event. -/
theorem allFree_mem_commonShallowBad_of_supportedGates
    {n G fuel trunkDepth residualDepth : ℕ}
    (gates : Fin G → List (Clause n)) (support : Fin G → Finset (Fin n))
    (hmiss : ∀ path : Finset (Fin n), path.card ≤ trunkDepth →
      ∃ g, Disjoint (support g) path)
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i = none) →
        residualDepth < (canonicalDT (gates g) fuel rho).depth) :
    (fun _ : Fin n ↦ none) ∈
      commonShallowBad gates fuel n trunkDepth residualDepth := by
  rw [mem_commonShallowBad]
  constructor
  · simp [stars, freeVars]
  · exact supportedGates_not_commonShallowAt_allFree gates support hmiss hdeep

/-- Two disjoint ordered conjunction blocks.  This is the smallest positive-residual analogue of
the independent-singleton family: each gate has canonical depth two while the target residual
depth is one. -/
def independentPairGates : Fin 2 → List (Clause 4) := fun g =>
  if g = 0 then
    [⟨[Rung4Literal.pos 0, Rung4Literal.pos 1]⟩]
  else
    [⟨[Rung4Literal.pos 2, Rung4Literal.pos 3]⟩]

/-- If both coordinates of either pair remain free, its gate has exact canonical depth two. -/
theorem independentPairGates_depth_two {ρ : Restriction 4} (g : Fin 2) :
    (if g = 0 then ρ 0 = none ∧ ρ 1 = none else ρ 2 = none ∧ ρ 3 = none) →
      (canonicalDT (independentPairGates g) 2 ρ).depth = 2 := by
  fin_cases g
  · rintro ⟨h0, h1⟩
    simp [independentPairGates, canonicalDT, anyTermSat, termSat, activeTerm,
      termFalsified, freeLits, Depth3.litTrue, litVar, litFixedVal, litFalse,
      litFree, fixVar, h0, h1]
    rfl
  · rintro ⟨h2, h3⟩
    simp [independentPairGates, canonicalDT, anyTermSat, termSat, activeTerm,
      termFalsified, freeLits, Depth3.litTrue, litVar, litFixedVal, litFalse,
      litFree, fixVar, h2, h3]
    rfl

/-- Positive residual depth does not by itself force an endpoint/label saving.  On the fully live
four-variable cube, a depth-one common trunk cannot make both disjoint width-two conjunctions
residual-depth at most one: along the all-false branch it queries at most one coordinate, leaving
one complete pair free and hence one residual canonical tree of depth two. -/
theorem independentPairs_not_commonShallowAt_one :
    ¬ CommonShallowAt independentPairGates 2 (fun _ : Fin 4 => none) 1 1 := by
  rintro ⟨trunk, hdepth, hleaf⟩
  let x : Fin 4 → Bool := fun _ => false
  let path : Finset (Fin 4) := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ 1 := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ 1 := hdepth
  have hx : Rung4Restriction.Extends (fun _ : Fin 4 => none) x := by
    intro i b hi
    simp at hi
  have hfree (i : Fin 4) (hi : i ∉ path) : CommonTree.run trunk x i = none := by
    let y : Fin 4 → Bool := Function.update x i true
    have hy : Rung4Restriction.Extends (fun _ : Fin 4 => none) y := by
      intro j b hj
      simp at hj
    obtain ⟨_, hτx, _⟩ := hleaf x hx
    obtain ⟨_, hτy, _⟩ := hleaf y hy
    have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
      exact CommonTree.run_update_of_not_mem_queryVars trunk x i (by simpa [path] using hi)
    cases hτ : CommonTree.run trunk x i with
    | none => rfl
    | some b =>
        have hbx : b = false := by
          simpa [x] using hτx i b hτ
        have hby : b = true := by
          have : CommonTree.run trunk y i = some b := by simpa [hrun] using hτ
          simpa [y, x] using hτy i b this
        exact False.elim (Bool.false_ne_true (hbx.symm.trans hby))
  obtain ⟨_, _, hshallow⟩ := hleaf x hx
  by_cases h0 : (0 : Fin 4) ∈ path
  · have h2 : (2 : Fin 4) ∉ path := by
      intro h2
      have hsub : ({0, 2} : Finset (Fin 4)) ⊆ path := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      have hcard : ({0, 2} : Finset (Fin 4)).card = 2 := by decide
      rw [hcard] at this
      omega
    have h3 : (3 : Fin 4) ∉ path := by
      intro h3
      have hsub : ({0, 3} : Finset (Fin 4)) ⊆ path := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      have hcard : ({0, 3} : Finset (Fin 4)).card = 2 := by decide
      rw [hcard] at this
      omega
    have hdeep := independentPairGates_depth_two
      (ρ := CommonTree.run trunk x) (1 : Fin 2)
      (by simp [hfree 2 h2, hfree 3 h3])
    have := hshallow (1 : Fin 2)
    omega
  · by_cases h1 : (1 : Fin 4) ∈ path
    · have h2 : (2 : Fin 4) ∉ path := by
        intro h2
        have hsub : ({1, 2} : Finset (Fin 4)) ⊆ path := by
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl <;> assumption
        have := Finset.card_le_card hsub
        have hcard : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
        rw [hcard] at this
        omega
      have h3 : (3 : Fin 4) ∉ path := by
        intro h3
        have hsub : ({1, 3} : Finset (Fin 4)) ⊆ path := by
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl <;> assumption
        have := Finset.card_le_card hsub
        have hcard : ({1, 3} : Finset (Fin 4)).card = 2 := by decide
        rw [hcard] at this
        omega
      have hdeep := independentPairGates_depth_two
        (ρ := CommonTree.run trunk x) (1 : Fin 2)
        (by simp [hfree 2 h2, hfree 3 h3])
      have := hshallow (1 : Fin 2)
      omega
    · have hdeep := independentPairGates_depth_two
        (ρ := CommonTree.run trunk x) (0 : Fin 2)
        (by simp [hfree 0 h0, hfree 1 h1])
      have := hshallow (0 : Fin 2)
      omega

/-- The fully live root is therefore in the actual semantic bad event at positive residual depth. -/
theorem allFreeFour_mem_commonShallowBad_one :
    (fun _ : Fin 4 => none) ∈ commonShallowBad independentPairGates 2 4 1 1 := by
  rw [mem_commonShallowBad]
  constructor
  · decide
  · exact independentPairs_not_commonShallowAt_one

/-- A singleton gate contributes its coordinate to the raw canonical path exactly when that
coordinate belongs to the chosen free set. -/
theorem independentLiteral_queryVars {n : ℕ} (S : Finset (Fin n)) (a : Fin n) :
    CommonTree.queryVars
        (CommonTree.ofBool
          (canonicalDT (independentLiteralGates n a) 1 (independentRoot S)))
        (independentAssignment n) = if a ∈ S then [a] else [] := by
  by_cases ha : a ∈ S <;>
    simp [independentLiteralGates, independentRoot, independentAssignment, canonicalDT,
      anyTermSat, termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue,
      litVar, litFixedVal, litFalse, litFree, fixVar, ha, CommonTree.ofBool,
      CommonTree.queryVars]

/-- On the independent singleton family, the assignment-followed witness for gate `a` is the
single canonical key exactly when `a` is live.  This list-level form exposes gate order, which the
set-level path theorem intentionally forgets. -/
theorem independentLiteral_runWitSeq {n : ℕ} (S : Finset (Fin n)) (a : Fin n) :
    runWitSeq (independentLiteralGates n a) 1 (independentRoot S)
      (independentAssignment n) = if a ∈ S then [(0, 0)] else [] := by
  by_cases ha : a ∈ S <;>
    simp [independentLiteralGates, independentRoot, independentAssignment, runWitSeq,
      anyTermSat, termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue,
      litFixedVal, litFalse, litFree, termActivePred, freeLitPos, activeTermIdx, ha]

/-- The live coordinates in the same `Fin` order used by `taggedRawWitSeq`. -/
def independentLiveOrder {n : ℕ} (S : Finset (Fin n)) : List (Fin n) :=
  (List.ofFn fun i : Fin n => if i ∈ S then [i] else []).flatten

/-- Decoding the raw tagged stream gives precisely the live coordinates in gate order. -/
theorem independentLiteral_taggedRawVars {n : ℕ} (S : Finset (Fin n)) :
    (taggedRawWitSeq (independentLiteralGates n) 1 (independentRoot S)
      (independentAssignment n)).filterMap (taggedWitVar? (independentLiteralGates n)) =
        independentLiveOrder S := by
  simp only [taggedRawWitSeq, independentLiveOrder, List.filterMap_flatten, List.map_ofFn]
  apply congrArg List.flatten
  rw [List.ofFn_inj]
  funext g
  simp only [Function.comp_apply]
  rw [independentLiteral_runWitSeq]
  by_cases hg : g ∈ S <;> simp [hg, taggedWitVar?, independentLiteralGates, litVar]

/-- The gate-ordered live-coordinate list has no repetitions. -/
theorem independentLiveOrder_nodup {n : ℕ} (S : Finset (Fin n)) :
    (independentLiveOrder S).Nodup := by
  simp only [independentLiveOrder, List.nodup_flatten, List.mem_ofFn]
  constructor
  · rintro l ⟨i, rfl⟩
    by_cases h : i ∈ S <;> simp [h]
  · rw [List.pairwise_ofFn]
    intro i j hij
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [hi, hj, List.disjoint_singleton, ne_of_gt hij]

/-- On singleton gates the raw decoded stream is already globally fresh, so stable freshness
leaves its exact order unchanged. -/
theorem independentLiteral_freshTaggedVars {n : ℕ} (S : Finset (Fin n)) :
    (freshTaggedWitSeq (independentLiteralGates n) 1 (independentRoot S)
      (independentAssignment n)).filterMap (taggedWitVar? (independentLiteralGates n)) =
        independentLiveOrder S := by
  have hsub := (freshTaggedWitSeq_sublist (independentLiteralGates n) 1
    (independentRoot S) (independentAssignment n)).filterMap
      (taggedWitVar? (independentLiteralGates n))
  rw [independentLiteral_taggedRawVars S] at hsub
  apply hsub.eq_of_length
  have hfresh := freshTaggedWitSeq_vars_nodup (independentLiteralGates n) 1
    (independentRoot S) (independentAssignment n)
  have hsets := freshTaggedWitSeq_vars_toFinset (independentLiteralGates n) 1
    (independentRoot S) (independentAssignment n)
  rw [independentLiteral_taggedRawVars S] at hsets
  rw [← List.toFinset_card_of_nodup hfresh,
    hsets, List.toFinset_card_of_nodup (independentLiveOrder_nodup S)]

private theorem filterMap_take_eq_take_filterMap_of_isSome {α β : Type}
    (f : α → Option β) : ∀ (l : List α),
    (∀ e ∈ l, (f e).isSome = true) → ∀ d,
      (l.take d).filterMap f = (l.filterMap f).take d := by
  intro l h d
  induction l generalizing d with
  | nil => simp
  | cons e es ih =>
      cases d with
      | zero => simp
      | succ d =>
          have he := h e (by simp)
          cases hef : f e with
          | none => simp [hef] at he
          | some b =>
              simp only [List.take_succ_cons, List.filterMap_cons, hef,
                List.take_succ_cons, List.cons.injEq, true_and]
              apply ih (fun a ha => h a (by simp [ha]))

/-- The budgeted singleton prefix is exactly the first `d` live coordinates in `Fin` gate order. -/
theorem independentLiteral_freshTaggedPrefixVars_eq_take {n d : ℕ}
    (S : Finset (Fin n)) :
    freshTaggedPrefixVars (independentLiteralGates n) 1 (independentRoot S)
      (independentAssignment n) d = ((independentLiveOrder S).take d).toFinset := by
  have hall : ∀ e ∈ freshTaggedWitSeq (independentLiteralGates n) 1
      (independentRoot S) (independentAssignment n),
      (taggedWitVar? (independentLiteralGates n) e).isSome = true := by
    intro e he
    exact freshTaggedAux_var_isSome (independentLiteralGates n) ∅ _ e he
  have htake := filterMap_take_eq_take_filterMap_of_isSome
    (taggedWitVar? (independentLiteralGates n))
    (freshTaggedWitSeq (independentLiteralGates n) 1
      (independentRoot S) (independentAssignment n)) hall d
  rw [freshTaggedPrefixVars, htake, independentLiteral_freshTaggedVars]

/-- The ordered prefix fixes precisely those first `d` live coordinates to false and leaves the
remaining live set untouched. -/
theorem independentLiteral_freshTaggedPrefixEndpoint_eq_sdiff {n d : ℕ}
    (S : Finset (Fin n)) :
    freshTaggedPrefixEndpoint (independentLiteralGates n) 1 (independentRoot S)
      (independentAssignment n) d =
        independentRoot (S \ ((independentLiveOrder S).take d).toFinset) := by
  have hsubset : ((independentLiveOrder S).take d).toFinset ⊆ S := by
    rw [← independentLiteral_freshTaggedPrefixVars_eq_take S,
      Finset.subset_iff]
    intro i hi
    have hfree := (freshTaggedPrefixVars_subset_freeVars
      (independentLiteralGates n) 1 (independentRoot S)
      (independentAssignment n) d (independentRoot_extends S)) hi
    simpa [mem_freeVars, independentRoot] using hfree
  funext i
  rw [freshTaggedPrefixEndpoint,
    independentLiteral_freshTaggedPrefixVars_eq_take]
  by_cases hip : i ∈ ((independentLiveOrder S).take d).toFinset
  · have his : i ∈ S := hsubset hip
    simp [fixOn, independentRoot, independentAssignment, hip, his]
  · by_cases his : i ∈ S <;>
      simp [fixOn, independentRoot, hip, his]

/-- The live-coordinate order really is increasing `Fin` order.  This ordered form is what makes
the partially free endpoint fibers computable rather than merely bounded by an ambient label
space. -/
theorem independentLiveOrder_pairwise {n : ℕ} (S : Finset (Fin n)) :
    (independentLiveOrder S).Pairwise (· ≤ ·) := by
  simp only [independentLiveOrder, List.pairwise_flatten, List.mem_ofFn]
  constructor
  · rintro l ⟨i, rfl⟩
    by_cases hi : i ∈ S <;> simp [hi]
  · rw [List.pairwise_ofFn]
    intro i j hij
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [hi, hj, Fin.le_of_lt hij]

/-- Equivalently, the explicit gate-ordered list is the sorted list of the live finset. -/
theorem independentLiveOrder_eq_sort {n : ℕ} (S : Finset (Fin n)) :
    independentLiveOrder S = S.sort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba)
  · exact independentLiveOrder_pairwise S
  · exact Finset.sort_sorted _ _
  · apply List.perm_of_nodup_nodup_toFinset_eq
    · exact independentLiveOrder_nodup S
    · exact Finset.sort_nodup _ _
    ext i
    simp [independentLiveOrder]

theorem independentLiveOrder_length {n : ℕ} (S : Finset (Fin n)) :
    (independentLiveOrder S).length = S.card := by
  rw [← List.toFinset_card_of_nodup (independentLiveOrder_nodup S)]
  congr 1
  ext i
  simp [independentLiveOrder]

/-- If every member of `D` precedes every member of `E`, the canonical live order of their union
is exactly the concatenation `D` then `E`. -/
theorem independentLiveOrder_union_of_lt {n : ℕ} (D E : Finset (Fin n))
    (hcross : ∀ i ∈ D, ∀ j ∈ E, i < j) :
    independentLiveOrder (D ∪ E) =
      independentLiveOrder D ++ independentLiveOrder E := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba)
  · exact independentLiveOrder_pairwise (D ∪ E)
  · rw [List.pairwise_append]
    exact ⟨independentLiveOrder_pairwise D, independentLiveOrder_pairwise E,
      fun i hi j hj =>
        (hcross i (by simpa [independentLiveOrder] using hi) j
          (by simpa [independentLiveOrder] using hj)).le⟩
  · apply List.perm_of_nodup_nodup_toFinset_eq
    · exact independentLiveOrder_nodup _
    · rw [List.nodup_append]
      exact ⟨independentLiveOrder_nodup D, independentLiveOrder_nodup E, by
        intro i hi j hj hij
        subst j
        exact (hcross i (by simpa [independentLiveOrder] using hi) i
          (by simpa [independentLiveOrder] using hj)).false⟩
    · ext i
      simp [independentLiveOrder]

/-- A `d`-set strictly below a residual set `E` is precisely consumed before `E`; its root reaches
the residual independent root after the budget-`d` prefix. -/
theorem independentLiteral_prefixEndpoint_union_of_lt {n d : ℕ}
    (D E : Finset (Fin n)) (hD : D.card = d)
    (hcross : ∀ i ∈ D, ∀ j ∈ E, i < j) :
    freshTaggedPrefixEndpoint (independentLiteralGates n) 1 (independentRoot (D ∪ E))
      (independentAssignment n) d = independentRoot E := by
  rw [independentLiteral_freshTaggedPrefixEndpoint_eq_sdiff,
    independentLiveOrder_union_of_lt D E hcross,
    ← hD, ← independentLiveOrder_length D, List.take_left]
  congr 1
  have hto : (independentLiveOrder D).toFinset = D := by
    ext i
    simp [independentLiveOrder]
  rw [hto]
  ext i
  constructor
  · simp only [Finset.mem_sdiff, Finset.mem_union]
    rintro ⟨hiD | hiE, hniD⟩
    · contradiction
    · exact hiE
  · intro hiE
    simp only [Finset.mem_sdiff, Finset.mem_union]
    refine ⟨Or.inr hiE, ?_⟩
    intro hiD
    exact (hcross i hiD i hiE).false

/-- Coordinates strictly below every coordinate of the residual endpoint.  For nonempty `E` this
is the initial segment below `min(E)`; the definition also handles `E = ∅` without a choice. -/
def independentStrictBelow {n : ℕ} (E : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ j ∈ E, i < j

/-- The realized ordered subfiber obtained by adjoining any `d`-set below `E`. -/
def independentOrderedFiber {n : ℕ} (E : Finset (Fin n)) (d : ℕ) :
    Finset (Restriction n) :=
  ((independentStrictBelow E).powersetCard d).image
    fun D => independentRoot (D ∪ E)

/-- The ordered subfiber has the exact binomial size suggested by the gate order, and every one of
its roots reaches the same residual endpoint.  This is an actual-image count, not an ambient
compatible-label bound. -/
theorem independentOrderedFiber_card_and_endpoint {n d : ℕ} (E : Finset (Fin n)) :
    (independentOrderedFiber E d).card =
        Nat.choose (independentStrictBelow E).card d ∧
      ∀ ρ ∈ independentOrderedFiber E d,
        freshTaggedPrefixEndpoint (independentLiteralGates n) 1 ρ
          (independentAssignment n) d = independentRoot E := by
  constructor
  · rw [independentOrderedFiber, Finset.card_image_of_injOn]
    · exact Finset.card_powersetCard d (independentStrictBelow E)
    · intro D₁ hD₁ D₂ hD₂ hroot
      have hD₁' : D₁ ∈ (independentStrictBelow E).powersetCard d := hD₁
      have hD₂' : D₂ ∈ (independentStrictBelow E).powersetCard d := hD₂
      have hunion : D₁ ∪ E = D₂ ∪ E := by
        ext i
        have hi := congrFun hroot i
        by_cases hi₁ : i ∈ D₁ ∪ E <;> by_cases hi₂ : i ∈ D₂ ∪ E <;>
          simp [independentRoot, hi₁, hi₂] at hi ⊢
      have hsub₁ := (Finset.mem_powersetCard.mp hD₁').1
      have hsub₂ := (Finset.mem_powersetCard.mp hD₂').1
      ext i
      have hdis₁ : i ∈ D₁ → i ∉ E := by
        intro hiD hiE
        have hlt : i < i :=
          (Finset.mem_filter.mp (hsub₁ hiD)).2 i hiE
        exact hlt.false
      have hdis₂ : i ∈ D₂ → i ∉ E := by
        intro hiD hiE
        have hlt : i < i :=
          (Finset.mem_filter.mp (hsub₂ hiD)).2 i hiE
        exact hlt.false
      constructor
      · intro hi₁
        have hiu : i ∈ D₂ ∪ E := by rw [← hunion]; simp [hi₁]
        rcases Finset.mem_union.mp hiu with hi₂ | hiE
        · exact hi₂
        · exact (hdis₁ hi₁ hiE).elim
      · intro hi₂
        have hiu : i ∈ D₁ ∪ E := by rw [hunion]; simp [hi₂]
        rcases Finset.mem_union.mp hiu with hi₁ | hiE
        · exact hi₁
        · exact (hdis₂ hi₂ hiE).elim
  · intro ρ hρ
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hρ
    apply independentLiteral_prefixEndpoint_union_of_lt D E
      (Finset.mem_powersetCard.mp hD).2
    intro i hiD j hjE
    exact (Finset.mem_filter.mp
      ((Finset.mem_powersetCard.mp hD).1 hiD)).2 j hjE

/-- The normalized canonical-family path has exactly the selected free-coordinate set.  This is
the set-level generic singleton trace lemma needed by the endpoint-fiber audit. -/
theorem independentLiteral_pathVars {n : ℕ} (S : Finset (Fin n)) :
    CommonTree.pathVars (independentRoot S)
        (canonicalFamilyTree (independentLiteralGates n) 1 (independentRoot S))
        (independentAssignment n) = S := by
  rw [pathVars_canonicalFamily_eq_raw _ _ _ _ (independentRoot_extends S)]
  ext v
  simp [canonicalFamilyTree, CommonTree.queryVars_commonRefineFin,
    independentLiteral_queryVars]

/-- The globally fresh singleton trace has one entry for every live coordinate. -/
theorem independentLiteral_freshTaggedWitSeq_length {n : ℕ} (S : Finset (Fin n)) :
    (freshTaggedWitSeq (independentLiteralGates n) 1 (independentRoot S)
      (independentAssignment n)).length = S.card := by
  calc
    _ = ((freshTaggedWitSeq (independentLiteralGates n) 1 (independentRoot S)
          (independentAssignment n)).filterMap
        (taggedWitVar? (independentLiteralGates n))).length :=
      (freshTaggedAux_filterMap_length (independentLiteralGates n) ∅ _).symm
    _ = ((freshTaggedWitSeq (independentLiteralGates n) 1 (independentRoot S)
          (independentAssignment n)).filterMap
        (taggedWitVar? (independentLiteralGates n))).toFinset.card :=
      (List.toFinset_card_of_nodup
        (freshTaggedWitSeq_vars_nodup (independentLiteralGates n) 1
          (independentRoot S) (independentAssignment n))).symm
    _ = S.card := by
      rw [freshTaggedWitSeq_vars_eq_pathVars _ _ _ _ (independentRoot_extends S),
        independentLiteral_pathVars]

/-- A budget-`d` prefix from a `K`-live independent root leaves exactly `K-d` coordinates live.
This holds independently of the later endpoint-fiber count. -/
theorem independentLiteral_prefixEndpoint_stars {n d : ℕ} (S : Finset (Fin n))
    (hd : d ≤ S.card) :
    stars (freshTaggedPrefixEndpoint (independentLiteralGates n) 1 (independentRoot S)
      (independentAssignment n) d) = S.card - d := by
  have hstars : stars (independentRoot S) = S.card := by
    rw [stars]
    congr 1
    ext i
    simp [mem_freeVars, independentRoot]
  have hprefix :
      (freshTaggedPrefixVars (independentLiteralGates n) 1 (independentRoot S)
        (independentAssignment n) d).card = d := by
    apply freshTaggedPrefixVars_card_eq_of_le_trace _ _ _ _ _
      (independentRoot_extends S)
    rwa [← freshTaggedWitSeq_length_eq_trace_readOnce _ _ _ _ (independentRoot_extends S),
      independentLiteral_freshTaggedWitSeq_length]
  rw [stars_freshTaggedPrefixEndpoint _ _ _ _ _ (independentRoot_extends S),
    hstars, hprefix]

/-- Taking exactly `|S|` globally fresh tagged witnesses recovers all and only the coordinates in
`S`.  Hence canonical gate order loses none of the compatible independent-literal labels. -/
theorem independentLiteral_freshTaggedPrefixVars {n : ℕ} (S : Finset (Fin n)) :
    freshTaggedPrefixVars (independentLiteralGates n) 1 (independentRoot S)
      (independentAssignment n) S.card = S := by
  have hext := independentRoot_extends S
  have hdecode :
      ((freshTaggedWitSeq (independentLiteralGates n) 1 (independentRoot S)
          (independentAssignment n)).filterMap
        (taggedWitVar? (independentLiteralGates n))).toFinset = S := by
    rw [freshTaggedWitSeq_vars_eq_pathVars _ _ _ _ hext]
    exact independentLiteral_pathVars S
  have hlen :
      (freshTaggedWitSeq (independentLiteralGates n) 1 (independentRoot S)
        (independentAssignment n)).length = S.card := by
    calc
      _ = ((freshTaggedWitSeq (independentLiteralGates n) 1 (independentRoot S)
            (independentAssignment n)).filterMap
          (taggedWitVar? (independentLiteralGates n))).length :=
        (freshTaggedAux_filterMap_length (independentLiteralGates n) ∅ _).symm
      _ = ((freshTaggedWitSeq (independentLiteralGates n) 1 (independentRoot S)
            (independentAssignment n)).filterMap
          (taggedWitVar? (independentLiteralGates n))).toFinset.card :=
        (List.toFinset_card_of_nodup
          (freshTaggedWitSeq_vars_nodup (independentLiteralGates n) 1
            (independentRoot S) (independentAssignment n))).symm
      _ = S.card := by rw [hdecode]
  rw [freshTaggedPrefixVars, ← hlen, List.take_length]
  exact hdecode

theorem freeVars_independentRoot {n : ℕ} (S : Finset (Fin n)) :
    freeVars (independentRoot S) = S := by
  ext i
  simp [mem_freeVars, independentRoot]

theorem independentRoot_injective {n : ℕ} :
    Function.Injective (independentRoot : Finset (Fin n) → Restriction n) := by
  intro S T h
  rw [← freeVars_independentRoot S, h, freeVars_independentRoot T]

/-- Converse to the ordered-subfiber construction at the level of the consumed prefix.  If a
budget-`d` singleton prefix from `S` reaches exactly `E`, then the actually consumed coordinates
form a `d`-set strictly below `E`, and `S` is their disjoint ordered union with `E`. -/
theorem independentLiteral_prefixEndpoint_converse {n d : ℕ}
    (S E : Finset (Fin n)) (hd : d ≤ S.card)
    (hendpoint :
      freshTaggedPrefixEndpoint (independentLiteralGates n) 1 (independentRoot S)
        (independentAssignment n) d = independentRoot E) :
    let D := ((independentLiveOrder S).take d).toFinset
    D.card = d ∧ D ⊆ independentStrictBelow E ∧ S = D ∪ E := by
  let D : Finset (Fin n) := ((independentLiveOrder S).take d).toFinset
  change D.card = d ∧ D ⊆ independentStrictBelow E ∧ S = D ∪ E
  have hresidual : S \ D = E := by
    apply independentRoot_injective
    rw [← hendpoint,
      independentLiteral_freshTaggedPrefixEndpoint_eq_sdiff]
  have hDcard : D.card = d := by
    change ((independentLiveOrder S).take d).toFinset.card = d
    rw [List.toFinset_card_of_nodup
      (independentLiveOrder_nodup S).take, List.length_take,
      independentLiveOrder_length, Nat.min_eq_left hd]
  have hDsubS : D ⊆ S := by
    intro i hi
    have hi' : i ∈ independentLiveOrder S :=
      List.mem_of_mem_take (by simpa only [D, List.mem_toFinset] using hi)
    simpa [independentLiveOrder] using hi'
  have hDbelow : D ⊆ independentStrictBelow E := by
    intro i hiD
    rw [independentStrictBelow, Finset.mem_filter]
    refine ⟨Finset.mem_univ i, fun j hjE => ?_⟩
    have hiTake : i ∈ (independentLiveOrder S).take d := by
      simpa only [D, List.mem_toFinset] using hiD
    have hjResidualMem : j ∈ S \ D := by
      rw [hresidual]
      exact hjE
    have hjResidual := Finset.mem_sdiff.mp hjResidualMem
    have hjOrder : j ∈ independentLiveOrder S := by
      simpa [independentLiveOrder] using hjResidual.1
    have hjDrop : j ∈ (independentLiveOrder S).drop d := by
      have hjAppend :
          j ∈ (independentLiveOrder S).take d ++
            (independentLiveOrder S).drop d := by
        rw [List.take_append_drop]
        exact hjOrder
      have hjEither := List.mem_append.mp hjAppend
      exact hjEither.resolve_left (by
        simpa only [D, List.mem_toFinset] using hjResidual.2)
    have hordered :
        ((independentLiveOrder S).take d ++
          (independentLiveOrder S).drop d).Pairwise (· ≤ ·) := by
      rw [List.take_append_drop]
      exact independentLiveOrder_pairwise S
    have hijLe := (List.pairwise_append.mp hordered).2.2 i hiTake j hjDrop
    exact lt_of_le_of_ne hijLe (fun hij => hjResidual.2 (by
      simpa only [D, List.mem_toFinset, hij] using hiD))
  refine ⟨hDcard, hDbelow, ?_⟩
  ext i
  constructor
  · intro hiS
    by_cases hiD : i ∈ D
    · exact Finset.mem_union_left E hiD
    · exact Finset.mem_union_right D ((by
        rw [← hresidual]
        exact Finset.mem_sdiff.mpr ⟨hiS, hiD⟩) : i ∈ E)
  · intro hiUnion
    rcases Finset.mem_union.mp hiUnion with hiD | hiE
    · exact hDsubS hiD
    · have : i ∈ S \ D := by rwa [hresidual]
      exact (Finset.mem_sdiff.mp this).1

/-- Exact converse characterization, including uniqueness of the consumed `d`-set.  The statement
is uniform at `E = ∅`, where `independentStrictBelow E` is all coordinates. -/
theorem independentLiteral_prefixEndpoint_iff_existsUnique {n d : ℕ}
    (S E : Finset (Fin n)) (hd : d ≤ S.card) :
    freshTaggedPrefixEndpoint (independentLiteralGates n) 1 (independentRoot S)
        (independentAssignment n) d = independentRoot E ↔
      ∃! D : Finset (Fin n),
        D.card = d ∧ D ⊆ independentStrictBelow E ∧ S = D ∪ E := by
  constructor
  · intro hendpoint
    let D : Finset (Fin n) := ((independentLiveOrder S).take d).toFinset
    have hD := independentLiteral_prefixEndpoint_converse S E hd hendpoint
    change D.card = d ∧ D ⊆ independentStrictBelow E ∧ S = D ∪ E at hD
    refine ⟨D, hD, fun D' hD' => ?_⟩
    apply Finset.Subset.antisymm
    · intro i hiD'
      have hiS : i ∈ S := by
        rw [hD'.2.2]
        exact Finset.mem_union_left E hiD'
      rw [hD.2.2] at hiS
      rcases Finset.mem_union.mp hiS with hiD | hiE
      · exact hiD
      · have hii := (Finset.mem_filter.mp (hD'.2.1 hiD')).2 i hiE
        exact hii.false.elim
    · intro i hiD
      have hiS : i ∈ S := by
        rw [hD.2.2]
        exact Finset.mem_union_left E hiD
      rw [hD'.2.2] at hiS
      rcases Finset.mem_union.mp hiS with hiD' | hiE
      · exact hiD'
      · have hii := (Finset.mem_filter.mp (hD.2.1 hiD)).2 i hiE
        exact hii.false.elim
  · rintro ⟨D, hD, _⟩
    rw [hD.2.2]
    apply independentLiteral_prefixEndpoint_union_of_lt D E hD.1
    intro i hiD j hjE
    exact (Finset.mem_filter.mp (hD.2.1 hiD)).2 j hjE

/-- The roots in the exact `K`-live independent shell whose budget-`d` prefix reaches `E`. -/
def independentFixedShellEndpointFiber {n : ℕ} (K d : ℕ) (E : Finset (Fin n)) :
    Finset (Restriction n) :=
  (((Finset.univ : Finset (Fin n)).powersetCard K).filter fun S =>
      freshTaggedPrefixEndpoint (independentLiteralGates n) 1 (independentRoot S)
        (independentAssignment n) d = independentRoot E).image independentRoot

/-- The same fixed-shell fiber before applying the injective `independentRoot` encoding.  This
coordinate-set form exposes the partition needed for aggregate incidence counting. -/
def independentFixedShellCoordinateFiber {n : ℕ} (K d : ℕ) (E : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard K).filter fun S =>
    S \ ((independentLiveOrder S).take d).toFinset = E

/-- Passing from live-coordinate sets to independent restrictions loses no elements of a fixed
endpoint fiber. -/
theorem independentFixedShellEndpointFiber_card_eq_coordinateFiber {n K d : ℕ}
    (E : Finset (Fin n)) :
    (independentFixedShellEndpointFiber K d E).card =
      (independentFixedShellCoordinateFiber K d E).card := by
  rw [independentFixedShellEndpointFiber, independentFixedShellCoordinateFiber,
    Finset.card_image_of_injective _ independentRoot_injective]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hS, hendpoint⟩
    refine ⟨hS, independentRoot_injective ?_⟩
    rw [← hendpoint, independentLiteral_freshTaggedPrefixEndpoint_eq_sdiff]
  · rintro ⟨hS, hresidual⟩
    refine ⟨hS, ?_⟩
    rw [independentLiteral_freshTaggedPrefixEndpoint_eq_sdiff, hresidual]

/-- Aggregate incidence is exactly conserved on the independent singleton family.  Summing the
actual canonical endpoint fibers over every residual `d`-set counts each `2d`-live root exactly
once, so the total is the original coordinate-shell count `choose(n,2d)`.  In particular, the
attained pointwise maximum cannot be multiplied across the whole residual shell. -/
theorem independentFixedShellEndpointFiber_aggregate_exact (n d : ℕ) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        (independentFixedShellEndpointFiber (2 * d) d E).card) = Nat.choose n (2 * d) := by
  simp_rw [independentFixedShellEndpointFiber_card_eq_coordinateFiber]
  let source : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (2 * d)
  let residual : Finset (Fin n) → Finset (Fin n) := fun S =>
    S \ ((independentLiveOrder S).take d).toFinset
  have hmaps : (source : Set (Finset (Fin n))).MapsTo residual
      ((Finset.univ : Finset (Fin n)).powersetCard d) := by
    intro S hS
    have hScard : S.card = 2 * d :=
      (Finset.mem_powersetCard.mp (show S ∈ source from hS)).2
    have hdScard : d ≤ S.card := by rw [hScard]; omega
    have hstars := independentLiteral_prefixEndpoint_stars S hdScard
    rw [independentLiteral_freshTaggedPrefixEndpoint_eq_sdiff, stars,
      freeVars_independentRoot, hScard] at hstars
    unfold residual
    have hrescard : (S \ ((independentLiveOrder S).take d).toFinset).card = d := by
      omega
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hrescard⟩
  calc
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        (independentFixedShellCoordinateFiber (2 * d) d E).card) = source.card := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      rfl
    _ = Nat.choose n (2 * d) := by
      simp [source, Finset.card_powersetCard]

/-- The pointwise ordered-prefix converse exhausts the fixed-shell endpoint fiber.  The endpoint
shell condition `|E| = K-d` and `d ≤ K` are exactly what makes every ordered union `D ∪ E`
return to the `K`-live source shell. -/
theorem independentFixedShellEndpointFiber_eq_ordered {n K d : ℕ}
    (E : Finset (Fin n)) (hd : d ≤ K) (hE : E.card = K - d) :
    independentFixedShellEndpointFiber K d E = independentOrderedFiber E d := by
  ext ρ
  constructor
  · intro hρ
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hρ
    have hSfilter := Finset.mem_filter.mp hS
    have hScard : S.card = K := (Finset.mem_powersetCard.mp hSfilter.1).2
    have hdS : d ≤ S.card := by simpa [hScard] using hd
    obtain ⟨D, hD, _⟩ :=
      (independentLiteral_prefixEndpoint_iff_existsUnique S E hdS).mp hSfilter.2
    apply Finset.mem_image.mpr
    refine ⟨D, Finset.mem_powersetCard.mpr ⟨hD.2.1, hD.1⟩, ?_⟩
    rw [hD.2.2]
  · intro hρ
    obtain ⟨D, hDmem, rfl⟩ := Finset.mem_image.mp hρ
    have hD := Finset.mem_powersetCard.mp hDmem
    have hdisj : Disjoint D E := by
      refine Finset.disjoint_left.mpr fun i hiD hiE => ?_
      exact ((Finset.mem_filter.mp (hD.1 hiD)).2 i hiE).false
    apply Finset.mem_image.mpr
    refine ⟨D ∪ E, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_union_of_disjoint hdisj, hD.2, hE,
        Nat.add_sub_of_le hd]
    · apply independentLiteral_prefixEndpoint_union_of_lt D E hD.2
      intro i hiD j hjE
      exact (Finset.mem_filter.mp (hD.1 hiD)).2 j hjE

/-- Consequently the exact fixed-shell endpoint multiplicity is the ordered binomial. -/
theorem independentFixedShellEndpointFiber_card {n K d : ℕ}
    (E : Finset (Fin n)) (hd : d ≤ K) (hE : E.card = K - d) :
    (independentFixedShellEndpointFiber K d E).card =
      Nat.choose (independentStrictBelow E).card d := by
  rw [independentFixedShellEndpointFiber_eq_ordered E hd hE]
  exact (independentOrderedFiber_card_and_endpoint E).1

/-- Semantic residual depth zero excludes none of the realized ordered fiber when the trunk is
strictly shorter than the live shell.  Every root in the explicit canonical endpoint fiber is an
actual member of `commonShallowBad`, not merely a combinatorially compatible restriction. -/
theorem independentFixedShellEndpointFiber_subset_commonShallowBad_zero
    {n K d : ℕ} (E : Finset (Fin n)) (hdK : d < K) :
    independentFixedShellEndpointFiber K d E ⊆
      commonShallowBad (independentLiteralGates n) 1 K d 0 := by
  intro ρ hρ
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hρ
  have hsource := (Finset.mem_filter.mp hS).1
  exact independentRoot_mem_commonShallowBad_zero S
    (Finset.mem_powersetCard.mp hsource).2 hdK

/-- In the proportional shell `K = 2d`, every realized ordered endpoint fiber is semantically
bad at threshold zero, and their aggregate cardinality is the full coordinate shell.  Hence the
independent singleton family genuinely saturates the endpoint incidence on a bad event; semantic
badness alone supplies no further endpoint/label exclusion in this regime. -/
theorem independentBadEndpointFibers_aggregate_exact (n d : ℕ) (hd : 0 < d) :
    (∀ E : Finset (Fin n),
      independentFixedShellEndpointFiber (2 * d) d E ⊆
        commonShallowBad (independentLiteralGates n) 1 (2 * d) d 0) ∧
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        (independentFixedShellEndpointFiber (2 * d) d E).card) = Nat.choose n (2 * d) := by
  constructor
  · intro E
    exact independentFixedShellEndpointFiber_subset_commonShallowBad_zero E (by omega)
  · exact independentFixedShellEndpointFiber_aggregate_exact n d

/-- For a nonempty residual endpoint, the coordinates strictly below all of `E` are exactly the
finite initial segment below its least member. -/
theorem independentStrictBelow_eq_Iio_min' {n : ℕ} (E : Finset (Fin n))
    (hE : E.Nonempty) :
    independentStrictBelow E = Finset.Iio (E.min' hE) := by
  ext i
  simp only [independentStrictBelow, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_Iio]
  constructor
  · intro hi
    exact hi (E.min' hE) (Finset.min'_mem E hE)
  · intro hi j hj
    exact lt_of_lt_of_le hi (Finset.min'_le E j hj)

/-- Hence the ordered endpoint-fiber binomial is based on the numeric value of the least residual
coordinate, rather than on an opaque filtered-finset cardinality. -/
theorem independentFixedShellEndpointFiber_card_eq_choose_min' {n K d : ℕ}
    (E : Finset (Fin n)) (hd : d ≤ K) (hcard : E.card = K - d)
    (hE : E.Nonempty) :
    (independentFixedShellEndpointFiber K d E).card = Nat.choose (E.min' hE).val d := by
  rw [independentFixedShellEndpointFiber_card E hd hcard,
    independentStrictBelow_eq_Iio_min' E hE, Fin.card_Iio]

/-- A nonempty `d`-set of coordinates cannot start later than coordinate `n-d`.  This is the
finite pigeonhole step behind the extremal ordered endpoint fiber. -/
theorem min'_val_le_card_complement {n d : ℕ} (E : Finset (Fin n))
    (hcard : E.card = d) (hE : E.Nonempty) :
    (E.min' hE).val ≤ n - d := by
  have hsubset : E ⊆ Finset.Ici (E.min' hE) := by
    intro i hi
    exact Finset.mem_Ici.mpr (Finset.min'_le E i hi)
  have hcardle : d ≤ n - (E.min' hE).val := by
    rw [← hcard, ← Fin.card_Ici]
    exact Finset.card_le_card hsubset
  omega

/-- The bound on the least member is sharp: the final `d` coordinates form a `d`-set whose
least coordinate is exactly `n-d`. -/
theorem exists_card_min'_val_eq_card_complement {n d : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) :
    ∃ (E : Finset (Fin n)) (hE : E.Nonempty),
      E.card = d ∧ (E.min' hE).val = n - d := by
  let a : Fin n := ⟨n - d, by omega⟩
  refine ⟨Finset.Ici a, ⟨a, Finset.mem_Ici.mpr le_rfl⟩, ?_, ?_⟩
  · rw [Fin.card_Ici]
    dsimp [a]
    omega
  · have hmin : (Finset.Ici a).min' ⟨a, Finset.mem_Ici.mpr le_rfl⟩ = a := by
      apply le_antisymm
      · exact Finset.min'_le _ a (Finset.mem_Ici.mpr le_rfl)
      · exact Finset.mem_Ici.mp (Finset.min'_mem _ _)
    rw [hmin]

/-- Therefore every nonempty residual `d`-endpoint fiber in the proportional shell `K = 2d`
has multiplicity at most `choose(n-d,d)`. -/
theorem independentFixedShellEndpointFiber_card_le_choose_card_complement
    {n d : ℕ} (E : Finset (Fin n)) (hcard : E.card = d) (hE : E.Nonempty) :
    (independentFixedShellEndpointFiber (2 * d) d E).card ≤ Nat.choose (n - d) d := by
  rw [independentFixedShellEndpointFiber_card_eq_choose_min' E (by omega) (by omega) hE]
  exact Nat.choose_le_choose d (min'_val_le_card_complement E hcard hE)

/-- The extremal value is attained by the terminal segment.  Hence `choose(n-d,d)` is the exact
maximum endpoint multiplicity among residual `d`-sets in the `2d`-live shell. -/
theorem exists_independentFixedShellEndpointFiber_card_eq_choose_card_complement
    {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    ∃ (E : Finset (Fin n)) (hE : E.Nonempty),
      E.card = d ∧
        (independentFixedShellEndpointFiber (2 * d) d E).card = Nat.choose (n - d) d := by
  obtain ⟨E, hE, hcard, hmin⟩ :=
    exists_card_min'_val_eq_card_complement hd hdn
  refine ⟨E, hE, hcard, ?_⟩
  rw [independentFixedShellEndpointFiber_card_eq_choose_min' E (by omega) (by omega) hE,
    hmin]

/-- Inserting the attained maximum into the proportional shell count gives an exact identity.
The residual `d`-shell, the maximum ordered endpoint fiber, and the requested `2^d` saving
together exceed the original `2d`-shell by the factor `choose(2d,d) * 2^(2d)`. -/
theorem independentOrderedFiberMaximum_exact_shell_count {n d : ℕ} (h2dn : 2 * d ≤ n) :
    Nat.choose n d * 2 ^ (n - d) * Nat.choose (n - d) d * 2 ^ d =
      Nat.choose n (2 * d) * 2 ^ (n - 2 * d) *
        Nat.choose (2 * d) d * 2 ^ (2 * d) := by
  have hcount := endpointFiber_coordinateSet_exact_count
    (n := n) (K := 2 * d) (d := d) (by omega) h2dn
  have hsub : 2 * d - d = d := by omega
  rw [hsub] at hcount
  calc
    Nat.choose n d * 2 ^ (n - d) * Nat.choose (n - d) d * 2 ^ d =
        (Nat.choose n d * 2 ^ (n - d) * Nat.choose (n - d) d) * 2 ^ d := by
          ring
    _ = (Nat.choose n (2 * d) * 2 ^ (n - 2 * d) *
          Nat.choose (2 * d) d * 2 ^ d) * 2 ^ d := by rw [hcount]
    _ = Nat.choose n (2 * d) * 2 ^ (n - 2 * d) *
          Nat.choose (2 * d) d * 2 ^ (2 * d) := by
      rw [show 2 * d = d + d by omega, pow_add]
      ring

/-- Therefore no nonempty proportional shell can absorb the attained maximum together with the
requested saving.  This is independent of how large the ambient dimension is once `2d ≤ n`. -/
theorem not_independentOrderedFiberMaximum_exact_balance_half
    {n d : ℕ} (hd : 0 < d) (h2dn : 2 * d ≤ n) :
    ¬(Nat.choose n d * 2 ^ (n - d) * Nat.choose (n - d) d * 2 ^ d ≤
        Nat.choose n (2 * d) * 2 ^ (n - 2 * d)) := by
  intro hbalance
  rw [independentOrderedFiberMaximum_exact_shell_count h2dn] at hbalance
  have hroot : 0 < Nat.choose n (2 * d) * 2 ^ (n - 2 * d) :=
    Nat.mul_pos (Nat.choose_pos h2dn) (pow_pos (by omega) _)
  have hchoose : 0 < Nat.choose (2 * d) d := Nat.choose_pos (by omega)
  have hpow : 1 < 2 ^ (2 * d) := Nat.one_lt_pow (by omega) (by omega)
  have hfactor : 1 < Nat.choose (2 * d) d * 2 ^ (2 * d) :=
    lt_of_lt_of_le hpow (Nat.le_mul_of_pos_left _ hchoose)
  have hgrow := Nat.mul_lt_mul_of_pos_left hfactor hroot
  apply (Nat.not_lt_of_ge hbalance)
  simpa only [mul_one, Nat.mul_assoc] using hgrow

/-- Every selected-set root returns to the same all-false endpoint after its full fresh prefix. -/
theorem independentLiteral_freshTaggedPrefixEndpoint {n : ℕ} (S : Finset (Fin n)) :
    freshTaggedPrefixEndpoint (independentLiteralGates n) 1 (independentRoot S)
      (independentAssignment n) S.card = independentAllFalse n := by
  funext i
  simp [freshTaggedPrefixEndpoint, independentLiteral_freshTaggedPrefixVars,
    fixOn, independentRoot, independentAssignment, independentAllFalse]

/-- All roots obtained by freeing a `d`-set from the common all-false endpoint. -/
def independentRealizedRoots (n d : ℕ) : Finset (Restriction n) :=
  ((Finset.univ : Finset (Fin n)).powersetCard d).image independentRoot

/-- For every `n,d`, the actually realized canonical common-endpoint fiber has exact size
`choose(n,d)`.  In particular, canonical gate order gives no asymptotic multiplicity saving on the
independent singleton family. -/
theorem independentLiteral_realized_endpoint_fiber_card (n d : ℕ) :
    (independentRealizedRoots n d).card = Nat.choose n d ∧
      ∀ ρ ∈ independentRealizedRoots n d,
        freshTaggedPrefixEndpoint (independentLiteralGates n) 1 ρ
          (independentAssignment n) d = independentAllFalse n := by
  constructor
  · rw [independentRealizedRoots,
      Finset.card_image_of_injective _ independentRoot_injective,
      Finset.card_powersetCard]
    simp
  · intro ρ hρ
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hρ
    rw [(Finset.mem_powersetCard.mp hS).2.symm]
    exact independentLiteral_freshTaggedPrefixEndpoint S

/-- The smallest independent-literal family in which a one-query canonical prefix can originate
from either coordinate. -/
def independentTwoLiteralGates : Fin 2 → List (Clause 2) :=
  fun i => [⟨[Rung4Literal.pos i]⟩]

/-- The two roots obtained by freeing one coordinate of the same all-false endpoint. -/
def independentTwoRoot0 : Restriction 2 :=
  fun i => if i = 0 then none else some false

def independentTwoRoot1 : Restriction 2 :=
  fun i => if i = 1 then none else some false

def independentTwoAllFalse : Restriction 2 := fun _ => some false

def independentTwoAssignment : Fin 2 → Bool := fun _ => false

/-- The first root realizes coordinate zero and returns to the common all-false endpoint. -/
theorem independentTwoRoot0_realized_endpoint :
    freshTaggedPrefixEndpoint independentTwoLiteralGates 1 independentTwoRoot0
      independentTwoAssignment 1 = independentTwoAllFalse := by
  decide

/-- The second root realizes coordinate one and returns to the same endpoint. -/
theorem independentTwoRoot1_realized_endpoint :
    freshTaggedPrefixEndpoint independentTwoLiteralGates 1 independentTwoRoot1
      independentTwoAssignment 1 = independentTwoAllFalse := by
  decide

/-- The two realized roots are genuinely distinct. -/
theorem independentTwoRoots_ne : independentTwoRoot0 ≠ independentTwoRoot1 := by
  decide

/-- The realized coordinate labels are the two distinct singleton sets. -/
theorem independentTwoRoot0_realized_label :
    freshTaggedPrefixVars independentTwoLiteralGates 1 independentTwoRoot0
      independentTwoAssignment 1 = {0} := by
  decide

theorem independentTwoRoot1_realized_label :
    freshTaggedPrefixVars independentTwoLiteralGates 1 independentTwoRoot1
      independentTwoAssignment 1 = {1} := by
  decide

/-- The complete two-root witness set for the common endpoint. -/
def independentTwoRealizedRoots : Finset (Restriction 2) :=
  {independentTwoRoot0, independentTwoRoot1}

/-- The actually realized canonical fiber reaches the full compatible size in this independent
example: both one-element coordinate sets occur over one fixed endpoint.  Thus no universal
per-endpoint multiplicity-one refinement of the coordinate-set count is available. -/
theorem independentTwo_realized_endpoint_fiber_card :
    independentTwoRealizedRoots.card = Nat.choose 2 1 ∧
      ∀ ρ ∈ independentTwoRealizedRoots,
        freshTaggedPrefixEndpoint independentTwoLiteralGates 1 ρ
          independentTwoAssignment 1 = independentTwoAllFalse := by
  constructor
  · decide
  · intro ρ hρ
    simp only [independentTwoRealizedRoots, Finset.mem_insert, Finset.mem_singleton] at hρ
    rcases hρ with rfl | rfl
    · exact independentTwoRoot0_realized_endpoint
    · exact independentTwoRoot1_realized_endpoint

/-- The next independent-literal case tests the first genuinely multi-query fiber. -/
def independentThreeLiteralGates : Fin 3 → List (Clause 3) :=
  fun i => [⟨[Rung4Literal.pos i]⟩]

/-- The three roots obtained by freeing a two-element coordinate set from one all-false
assignment. -/
def independentThreeRoot01 : Restriction 3 :=
  fun i => if i = 0 ∨ i = 1 then none else some false

def independentThreeRoot02 : Restriction 3 :=
  fun i => if i = 0 ∨ i = 2 then none else some false

def independentThreeRoot12 : Restriction 3 :=
  fun i => if i = 1 ∨ i = 2 then none else some false

def independentThreeAllFalse : Restriction 3 := fun _ => some false

def independentThreeAssignment : Fin 3 → Bool := fun _ => false

/-- The partially free endpoint retaining only coordinate two. -/
def independentThreeResidual2 : Restriction 3 :=
  fun i => if i = 2 then none else some false

/-- At the first proportional case `K = 2*d` (`K = 2`, `d = 1`), two distinct independent roots
already reach the same partially free endpoint.  Gate order therefore does not make conditional
endpoint fibers universally multiplicity one. -/
theorem independentThree_partial_endpoint_fiber_two :
    independentThreeRoot02 ≠ independentThreeRoot12 ∧
      freshTaggedPrefixEndpoint independentThreeLiteralGates 1 independentThreeRoot02
          independentThreeAssignment 1 = independentThreeResidual2 ∧
      freshTaggedPrefixEndpoint independentThreeLiteralGates 1 independentThreeRoot12
          independentThreeAssignment 1 = independentThreeResidual2 := by
  decide

/-- All three two-element coordinate labels are actually realized.  In particular, the canonical
gate order does not collapse the fiber when the prefix contains more than one query. -/
theorem independentThree_realized_labels :
    freshTaggedPrefixVars independentThreeLiteralGates 1 independentThreeRoot01
        independentThreeAssignment 2 = {0, 1} ∧
      freshTaggedPrefixVars independentThreeLiteralGates 1 independentThreeRoot02
        independentThreeAssignment 2 = {0, 2} ∧
      freshTaggedPrefixVars independentThreeLiteralGates 1 independentThreeRoot12
        independentThreeAssignment 2 = {1, 2} := by
  decide

/-- The complete three-root witness set for the common endpoint. -/
def independentThreeRealizedRoots : Finset (Restriction 3) :=
  {independentThreeRoot01, independentThreeRoot02, independentThreeRoot12}

/-- At `n = 3, d = 2`, the realized common-endpoint fiber again fills the entire compatible
coordinate-set fiber, now of exact size `choose(3,2) = 3`.  This rules out the possibility that
canonical gate order forces multiplicity one as soon as the prefix has multiple queries. -/
theorem independentThree_realized_endpoint_fiber_card :
    independentThreeRealizedRoots.card = Nat.choose 3 2 ∧
      ∀ ρ ∈ independentThreeRealizedRoots,
        freshTaggedPrefixEndpoint independentThreeLiteralGates 1 ρ
          independentThreeAssignment 2 = independentThreeAllFalse := by
  decide

/-- The exact unordered coordinate-set repair is sufficient for injectivity, but it still cannot
satisfy the current proportional half-shell balance.  At `K = 2*r` and `d = r`, the endpoint
shell and the label each contribute `choose n r`; the requested `2^r` saving then makes the left
side strictly larger than the original shell. -/
theorem not_coordinateSet_exact_balance_half
    {n r : ℕ} (hr : 0 < r) (h2rn : 2 * r ≤ n) :
    ¬(Nat.choose n (2 * r - r) * 2 ^ (n - (2 * r - r)) *
          Nat.choose n r * 2 ^ r ≤
        Nat.choose n (2 * r) * 2 ^ (n - 2 * r)) := by
  intro hbalance
  have hsub : 2 * r - r = r := by omega
  rw [hsub] at hbalance
  have hchoose : n.choose (2 * r) ≤ n.choose r * n.choose r := by
    have hmul := Nat.choose_mul (n := n) (k := 2 * r) (s := r) (by omega)
    have hcentral : 0 < (2 * r).choose r := Nat.choose_pos (by omega)
    have hstep : n.choose (2 * r) ≤ n.choose r * (n - r).choose r := by
      apply Nat.le_of_mul_le_mul_left _ hcentral
      calc
        (2 * r).choose r * n.choose (2 * r) =
            n.choose (2 * r) * (2 * r).choose r := by ring
        _ = n.choose r * (n - r).choose r := by simpa [hsub] using hmul
        _ ≤ (2 * r).choose r * (n.choose r * (n - r).choose r) := by
          exact Nat.le_mul_of_pos_left _ hcentral
    exact hstep.trans (Nat.mul_le_mul_left _
      (Nat.choose_le_choose r (Nat.sub_le n r)))
  have hnr : 0 < n.choose r := Nat.choose_pos (by omega)
  have hsquare : 0 < n.choose r * n.choose r := Nat.mul_pos hnr hnr
  have hexponent : n - 2 * r < n := by omega
  have hpow : 2 ^ (n - 2 * r) < 2 ^ n :=
    Nat.pow_lt_pow_right (by norm_num) hexponent
  have hrhs : n.choose (2 * r) * 2 ^ (n - 2 * r) <
      (n.choose r * n.choose r) * 2 ^ n :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hchoose)
      (Nat.mul_lt_mul_of_pos_left hpow hsquare)
  have hpowprod : 2 ^ (n - r) * 2 ^ r = 2 ^ n := by
    rw [← pow_add]
    congr 1
    omega
  have hlhs : n.choose r * 2 ^ (n - r) * n.choose r * 2 ^ r =
      (n.choose r * n.choose r) * 2 ^ n := by
    calc
      n.choose r * 2 ^ (n - r) * n.choose r * 2 ^ r =
          (n.choose r * n.choose r) * (2 ^ (n - r) * 2 ^ r) := by ring
      _ = (n.choose r * n.choose r) * 2 ^ n := by rw [hpowprod]
  rw [← hlhs] at hrhs
  exact (Nat.not_lt_of_ge hbalance) hrhs

/-- A two-clause example showing that weakening exact-tree coverage merely to depth coverage does
not make unrestricted literal sorting sound.  The second clause is absorbed semantically by the
first gate's conjunction, but its position in the canonical walk makes query order observable. -/
def depthSensitiveGate01 : List (Clause 2) :=
  [⟨[Rung4Literal.pos 0, Rung4Literal.pos 1]⟩, ⟨[Rung4Literal.pos 0]⟩]

def depthSensitiveGate10 : List (Clause 2) :=
  [⟨[Rung4Literal.pos 1, Rung4Literal.pos 0]⟩, ⟨[Rung4Literal.pos 0]⟩]

/-- Reordering the first clause preserves the DNF function. -/
theorem depthSensitive_dnfEval_eq (x : Fin 2 → Bool) :
    dnfEval depthSensitiveGate01 x = dnfEval depthSensitiveGate10 x := by
  simp [depthSensitiveGate01, depthSensitiveGate10, dnfEval,
    Rung4DNFTerm.evalLits, Rung4Literal.eval]
  cases x 0 <;> cases x 1 <;> decide

/-- Nevertheless, at fuel two on the fully live cube the two canonical trees have different
depths (one versus two).  A depth-only coverage bridge therefore cannot justify general
within-clause sorting either. -/
theorem depthSensitive_canonicalDT_depth_ne :
    (canonicalDT depthSensitiveGate01 2 (fun _ => none)).depth ≠
      (canonicalDT depthSensitiveGate10 2 (fun _ => none)).depth := by
  decide

/-- Every component is a single-clause circuit, so ideal semantic cleanup assigns zero excess to
the whole family even though its encoder keys remain distinct. -/
theorem permutedThreeLiteralSurvivors_semanticExcess :
    aggregateSemanticSlotExcess (fun _ => none) permutedThreeLiteralSurvivors = 0 := by
  simp [permutedThreeLiteralSurvivors, permutedThreeLiteralGates,
    aggregateSemanticSlotExcess]

/-- Even charging every ambient coordinate as support cannot bound the encoder alphabet by
distinct support plus semantic excess: the clean family has mass six against `3 + 0`.  Thus the
proposed bridge is false before any question of extracting a sharper circuit-owned essential set;
one must also quotient semantic replicas across indexed gates (including literal order), or retain
a separate component/key charge. -/
theorem permutedThreeLiteral_no_alphabet_le_support_add_semanticExcess :
    (Finset.univ : Finset (Fin 3)).card +
        aggregateSemanticSlotExcess (fun _ => none) permutedThreeLiteralSurvivors <
      (permutedThreeLiteralGates.map List.length).sum := by
  rw [permutedThreeLiteralSurvivors_semanticExcess,
    permutedThreeLiteralGates_alphabet_mass]
  simp

/-- A canonical prefix trunk cannot reduce the baseline charge of a live literal unless its
coordinate occurs on the followed query path.  In particular, arbitrarily many copies retain
their full combined baseline-plus-excess mass at every leaf that does not query that coordinate. -/
theorem prefixEndpoint_replicate_singleLiteral_baseline_mass_of_not_mem
    {n : ℕ} {α : Type} (σ : Restriction n) (t : CommonTree n α) (budget q : ℕ)
    (x : Fin n → Bool) (i : Fin n) (hi : σ i = none)
    (hnot : i ∉ CommonTree.queryVars (CommonTree.prefixEndpoints σ t budget) x) :
    aggregateSemanticBaselineExcess
        (CommonTree.run (CommonTree.prefixEndpoints σ t budget) x)
        (List.replicate q (Layered.dnf [⟨[Rung4Literal.pos i]⟩])) = q := by
  apply aggregateSemanticBaselineExcess_replicate_singleLiteral_of_free
  rw [CommonTree.run_prefixEndpoints]
  simp [fixOn, hi, hnot]

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonShallowAt.leaf_collapseRound_altO
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonShallowAt.leaf_collapseRound_bottomSlotCount_bound
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.layered_commonShallowBad_scaled_le_of_realized_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.normalizedLayered_commonShallowBad_scaled_le_of_realized_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.normalizedLayered_commonShallowBad_scaled_le_of_actual_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowAt_normalizedLayeredBottomFamily_iff
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonShallowAt.leaf_collapseRound_family_bounds
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonShallowAt.leaf_collapseRound_actualAlphabet_bound
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonShallowAt.leaf_collapseRound_slotAlphabet_bound
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.layeredRoundShell_succ_eq_live
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.normalizedLayered_commonShallowBad_scaled_le_schedule
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_layeredRound_worstCase_density_of_live_le_gateBound
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.layeredRoundActualShell_succ_eq_live
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.normalizedLayered_commonShallowBad_scaled_le_actual_schedule
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_layeredRoundActual_worstCase_density_of_live_le_gateBound
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.layeredRoundActual_gateBound_lt_live_of_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.layeredRoundActual_gateBound_margin_of_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_layeredRoundActual_worstCase_density_of_polynomial_gateCap
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.layeredRoundActual_bottomSlotCount_lt_live_of_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.layeredRoundActual_bottomSlotCount_margin_of_density
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.aggregateSemanticBaselineExcess_independentLiveLiteralFamily
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.permutedThreeLiteral_no_alphabet_le_support_add_semanticExcess
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.orderedThreeLiteral_canonicalDT_ne
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.orderedThreeLiteral_no_common_exactTree_representative
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.orderedThreeLiteral_no_semanticKey_position_decoder
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.card_coordinateSemanticPrefixLabel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_coordinateSemantic_exact_balance_half
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.endpointFiber_coordinateSet_exact_count
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.endpointFiber_coordinateSet_strictly_larger
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_pathVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentRoot_not_commonShallowAt_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentBadEndpointFibers_aggregate_exact
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.supportedGates_not_commonShallowAt_allFree
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.allFree_mem_commonShallowBad_of_supportedGates
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentPairGates_depth_two
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentPairs_not_commonShallowAt_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.allFreeFour_mem_commonShallowBad_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_taggedRawVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_freshTaggedVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_freshTaggedPrefixVars_eq_take
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_freshTaggedPrefixEndpoint_eq_sdiff
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_prefixEndpoint_stars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_freshTaggedPrefixVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_realized_endpoint_fiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentTwo_realized_endpoint_fiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentThree_realized_labels
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentThree_realized_endpoint_fiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentThree_partial_endpoint_fiber_two
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiveOrder_eq_sort
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_prefixEndpoint_union_of_lt
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentOrderedFiber_card_and_endpoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_prefixEndpoint_converse
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_prefixEndpoint_iff_existsUnique
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentFixedShellEndpointFiber_eq_ordered
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentFixedShellEndpointFiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentStrictBelow_eq_Iio_min'
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentFixedShellEndpointFiber_card_eq_choose_min'
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.min'_val_le_card_complement
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_card_min'_val_eq_card_complement
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentFixedShellEndpointFiber_card_le_choose_card_complement
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_independentFixedShellEndpointFiber_card_eq_choose_card_complement
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentOrderedFiberMaximum_exact_shell_count
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentFixedShellEndpointFiber_aggregate_exact
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_independentOrderedFiberMaximum_exact_balance_half
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_coordinateSet_exact_balance_half
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.depthSensitive_canonicalDT_depth_ne
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.distinctEssentialCoordinateBaseline_prefixEndpoint_ge_sub
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.distinctEssentialCoordinateBaseline_no_switchingFactor_contraction
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.distinctEssentialCoordinateBaseline_no_switchingFactor_contraction_of_twice_budget_lt
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.prefixEndpoint_replicate_singleLiteral_baseline_mass_of_not_mem
