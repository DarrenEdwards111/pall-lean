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

/-- More pairwise-disjoint support blocks than queried coordinates force one whole block to be
missed.  This is the exact finite packing premise needed by the semantic obstruction below.

The proof chooses one queried coordinate from every allegedly hit block.  Pairwise disjointness
makes those choices injective into `path`, contradicting `path.card < G`. -/
theorem exists_disjoint_support_of_pairwiseDisjoint
    {n G : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (path : Finset (Fin n)) (hpath : path.card < G) :
    ∃ g, Disjoint (support g) path := by
  by_contra hmiss
  push_neg at hmiss
  have hmeet (g : Fin G) : ∃ i, i ∈ support g ∧ i ∈ path :=
    Finset.not_disjoint_iff.mp (hmiss g)
  let hit : Fin G → {i // i ∈ path} := fun g ↦
    ⟨Classical.choose (hmeet g), (Classical.choose_spec (hmeet g)).2⟩
  have hit_mem (g : Fin G) : (hit g).1 ∈ support g :=
    (Classical.choose_spec (hmeet g)).1
  have hinj : Function.Injective hit := by
    intro g h heq
    by_contra hne
    have hdisj := hpair g h hne
    apply (Finset.not_disjoint_iff.mpr ⟨(hit g).1, hit_mem g, ?_⟩) hdisj
    simpa [heq] using hit_mem h
  have hcard : G ≤ path.card := by
    simpa using Fintype.card_le_of_injective hit hinj
  omega

/-- A pairwise-disjoint family with more blocks than the trunk depth automatically satisfies the
support-missing premise used by `supportedGates_not_commonShallowAt_allFree`. -/
theorem pairwiseDisjoint_support_miss
    {n G trunkDepth : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hblocks : trunkDepth < G) :
    ∀ path : Finset (Fin n), path.card ≤ trunkDepth →
      ∃ g, Disjoint (support g) path := by
  intro path hpath
  exact exists_disjoint_support_of_pairwiseDisjoint support hpair path
    (lt_of_le_of_lt hpath hblocks)

/-- The indices of support blocks that remain completely live under a restriction. -/
def intactSupportBlocks {n G : ℕ} (support : Fin G → Finset (Fin n))
    (σ : Restriction n) : Finset (Fin G) :=
  Finset.univ.filter fun g => support g ⊆ freeVars σ

/-- The explicit fixed-shell event whose roots retain more whole support blocks than a trunk of
depth `trunkDepth` can query. -/
def manyIntactShell {n G : ℕ} (support : Fin G → Finset (Fin n))
    (K trunkDepth : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter fun σ =>
    stars σ = K ∧ trunkDepth < (intactSupportBlocks support σ).card

/-- The free-set occupancy event underlying `manyIntactShell`.  Separating it from restrictions
removes the irrelevant Boolean values on fixed coordinates. -/
def manyIntactFreeSets {n G : ℕ} (support : Fin G → Finset (Fin n))
    (K trunkDepth : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard K |>.filter fun S =>
    trunkDepth < (Finset.univ.filter fun g => support g ⊆ S).card

/-- All coordinates belonging to at least one support block. -/
def supportUnion {n G : ℕ} (support : Fin G → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion support

/-- The lossless occupancy record of a free set: its selected coordinates inside every support
block, together with its selected coordinates outside the union of all blocks.  Retaining the
actual intersections (rather than only their cardinalities) makes the no-double-counting step
independent of any ordering convention. -/
def freeSetOccupancyCode {n G : ℕ} (support : Fin G → Finset (Fin n))
    (S : Finset (Fin n)) : (Fin G → Finset (Fin n)) × Finset (Fin n) :=
  (fun g => S ∩ support g, S \ supportUnion support)

/-- Reconstruction identity underlying the occupancy code. -/
theorem freeSetOccupancyCode_reconstruct {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (S : Finset (Fin n)) :
    S = (Finset.univ.biUnion fun g => (freeSetOccupancyCode support S).1 g) ∪
      (freeSetOccupancyCode support S).2 := by
  classical
  ext i
  simp only [freeSetOccupancyCode, supportUnion, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · intro hiS
    by_cases hblock : ∃ g, i ∈ support g
    · left
      obtain ⟨g, hig⟩ := hblock
      exact ⟨g, hiS, hig⟩
    · exact Or.inr ⟨hiS, hblock⟩
  · rintro (⟨_, hiS, _⟩ | ⟨hiS, _⟩) <;> exact hiS

/-- The full block-intersection profile plus the outside reservoir reconstructs the free set.
This is the exact no-double-counting interface needed before assigning binomial weights to
partial occupancies.  Pairwise disjointness is not needed for injectivity; it enters only when
the cardinality of a profile is factored across blocks. -/
theorem freeSetOccupancyCode_injective {n G : ℕ} (support : Fin G → Finset (Fin n)) :
    Function.Injective (freeSetOccupancyCode support) := by
  classical
  intro S T hcode
  have hblocks : (fun g => S ∩ support g) = (fun g => T ∩ support g) :=
    congrArg Prod.fst hcode
  have houtside : S \ supportUnion support = T \ supportUnion support :=
    congrArg Prod.snd hcode
  ext i
  by_cases hi : i ∈ supportUnion support
  · rw [supportUnion, Finset.mem_biUnion] at hi
    obtain ⟨g, _, hig⟩ := hi
    have hg := congrFun hblocks g
    have hmem := congrArg (fun U : Finset (Fin n) => i ∈ U) hg
    simpa [hig] using hmem
  · have hmem := congrArg (fun U : Finset (Fin n) => i ∈ U) houtside
    simpa [hi] using hmem

/-- For pairwise-disjoint supports, the shell size is exactly the sum of all block occupancies
and the outside occupancy.  This is the additive constraint in the eventual hypergeometric
coefficient; in particular partial blocks and outside coordinates are not silently discarded. -/
theorem freeSetOccupancyCode_card {n G : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (S : Finset (Fin n)) :
    S.card = (∑ g, ((freeSetOccupancyCode support S).1 g).card) +
      (freeSetOccupancyCode support S).2.card := by
  classical
  let inside := Finset.univ.biUnion fun g => (freeSetOccupancyCode support S).1 g
  let outside := (freeSetOccupancyCode support S).2
  have hinsidePair : ((Finset.univ : Finset (Fin G)) : Set (Fin G)).PairwiseDisjoint
      (fun g => (freeSetOccupancyCode support S).1 g) := by
    intro g _ h _ hne
    exact (hpair g h hne).mono Finset.inter_subset_right Finset.inter_subset_right
  have hio : Disjoint inside outside := by
    rw [Finset.disjoint_left]
    intro i hiInside hiOutside
    change i ∈ Finset.univ.biUnion
      (fun g => (freeSetOccupancyCode support S).1 g) at hiInside
    rw [Finset.mem_biUnion] at hiInside
    obtain ⟨g, _, hig⟩ := hiInside
    have hiSupport : i ∈ supportUnion support := by
      rw [supportUnion, Finset.mem_biUnion]
      exact ⟨g, Finset.mem_univ g, (Finset.mem_inter.mp hig).2⟩
    exact (Finset.mem_sdiff.mp hiOutside).2 hiSupport
  calc
    S.card = (inside ∪ outside).card :=
      congrArg Finset.card (freeSetOccupancyCode_reconstruct support S)
    _ = inside.card + outside.card := Finset.card_union_of_disjoint hio
    _ = (∑ g, ((freeSetOccupancyCode support S).1 g).card) + outside.card := by
      congr 1
      change (Finset.univ.biUnion
        (fun g => (freeSetOccupancyCode support S).1 g)).card = _
      exact Finset.card_biUnion hinsidePair

/-- A support is wholly intact exactly when its occupancy-code component is the full support.
Thus the threshold in `manyIntactFreeSets` can be read directly from the lossless profile. -/
theorem support_subset_iff_occupancy_eq {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (S : Finset (Fin n)) (g : Fin G) :
    support g ⊆ S ↔ (freeSetOccupancyCode support S).1 g = support g := by
  simp [freeSetOccupancyCode, Finset.inter_eq_right]

/-- Exact profile-level membership description of the many-intact event.  It records both the
fixed shell size and the number of full block components, while leaving partial components and
outside coordinates explicit rather than merging them into overlapping cases. -/
theorem mem_manyIntactFreeSets_iff_occupancy {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (K trunkDepth : ℕ) (S : Finset (Fin n)) :
    S ∈ manyIntactFreeSets support K trunkDepth ↔
      S.card = K ∧ trunkDepth <
        (Finset.univ.filter fun g =>
          (freeSetOccupancyCode support S).1 g = support g).card := by
  rw [manyIntactFreeSets, Finset.mem_filter, Finset.mem_powersetCard]
  simp only [Finset.subset_univ, true_and]
  simp_rw [support_subset_iff_occupancy_eq support S]

/-- The fiber of free sets having prescribed cardinality in every support block and in the
outside-coordinate reservoir. -/
def occupancySizeFiber {n G : ℕ} (support : Fin G → Finset (Fin n))
    (a : Fin G → ℕ) (r : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S =>
    (∀ g, (S ∩ support g).card = a g) ∧
      (S \ supportUnion support).card = r

/-- Independent choices of an `a g`-element subset from each support block and an `r`-element
subset from outside all blocks. -/
def occupancySlotChoices {n G : ℕ} (support : Fin G → Finset (Fin n))
    (a : Fin G → ℕ) (r : ℕ) :
    Finset ((Fin G → Finset (Fin n)) × Finset (Fin n)) :=
  (Fintype.piFinset fun g => (support g).powersetCard (a g)).product
    ((Finset.univ \ supportUnion support).powersetCard r)

/-- The raw slot choices have the expected product-of-binomial-coefficients cardinality. -/
theorem occupancySlotChoices_card {n G : ℕ} (support : Fin G → Finset (Fin n))
    (a : Fin G → ℕ) (r : ℕ) :
    (occupancySlotChoices support a r).card =
      (∏ g, (support g).card.choose (a g)) *
        ((Finset.univ \ supportUnion support).card.choose r) := by
  classical
  simp [occupancySlotChoices, Finset.card_powersetCard]

theorem mem_occupancySizeFiber {n G : ℕ} (support : Fin G → Finset (Fin n))
    (a : Fin G → ℕ) (r : ℕ) (S : Finset (Fin n)) :
    S ∈ occupancySizeFiber support a r ↔
      (∀ g, (S ∩ support g).card = a g) ∧
        (S \ supportUnion support).card = r := by
  simp [occupancySizeFiber]

theorem mem_occupancySlotChoices {n G : ℕ} (support : Fin G → Finset (Fin n))
    (a : Fin G → ℕ) (r : ℕ)
    (c : (Fin G → Finset (Fin n)) × Finset (Fin n)) :
    c ∈ occupancySlotChoices support a r ↔
      (∀ g, c.1 g ⊆ support g ∧ (c.1 g).card = a g) ∧
        c.2 ⊆ Finset.univ \ supportUnion support ∧ c.2.card = r := by
  classical
  simp [occupancySlotChoices, Finset.mem_powersetCard]

/-- Reassemble a free set from independently selected block and outside slots. -/
def reconstructOccupancyChoice {n G : ℕ}
    (c : (Fin G → Finset (Fin n)) × Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion c.1 ∪ c.2

/-- Pairwise disjointness makes slot reconstruction a right inverse to the lossless occupancy
code.  This is the point at which independent binomial factors become legitimate. -/
theorem freeSetOccupancyCode_reconstructChoice {n G : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (a : Fin G → ℕ) (r : ℕ)
    (c : (Fin G → Finset (Fin n)) × Finset (Fin n))
    (hc : c ∈ occupancySlotChoices support a r) :
    freeSetOccupancyCode support (reconstructOccupancyChoice c) = c := by
  classical
  rw [mem_occupancySlotChoices] at hc
  apply Prod.ext
  · funext g
    ext i
    simp only [freeSetOccupancyCode, reconstructOccupancyChoice, Finset.mem_inter,
      Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨(⟨h, hih⟩ | hiout), hig⟩
      · by_cases heq : h = g
        · simpa [heq] using hih
        · exact False.elim <| Finset.disjoint_left.mp (hpair h g heq)
            ((hc.1 h).1 hih) hig
      · exact False.elim <| (Finset.mem_sdiff.mp (hc.2.1 hiout)).2 <| by
          rw [supportUnion, Finset.mem_biUnion]
          exact ⟨g, Finset.mem_univ g, hig⟩
    · intro hig
      exact ⟨Or.inl ⟨g, hig⟩, (hc.1 g).1 hig⟩
  · ext i
    simp only [freeSetOccupancyCode, reconstructOccupancyChoice, supportUnion, Finset.mem_sdiff,
      Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hin, hout⟩
      rcases hin with ⟨g, hig⟩ | hiout
      · exact False.elim <| hout ⟨g, (hc.1 g).1 hig⟩
      · exact hiout
    · intro hiout
      refine ⟨Or.inr hiout, ?_⟩
      simpa only [supportUnion, Finset.mem_biUnion, Finset.mem_univ, true_and] using
        (Finset.mem_sdiff.mp (hc.2.1 hiout)).2

/-- Exact cardinality of every occupancy-size fiber.  Each block contributes one binomial factor,
and the coordinates outside all supports contribute the final factor. -/
theorem occupancySizeFiber_card {n G : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (a : Fin G → ℕ) (r : ℕ) :
    (occupancySizeFiber support a r).card =
      (∏ g, (support g).card.choose (a g)) *
        ((Finset.univ \ supportUnion support).card.choose r) := by
  classical
  rw [← occupancySlotChoices_card support a r]
  apply Finset.card_nbij' (freeSetOccupancyCode support) reconstructOccupancyChoice
  · intro S hS
    change S ∈ occupancySizeFiber support a r at hS
    change freeSetOccupancyCode support S ∈ occupancySlotChoices support a r
    rw [mem_occupancySizeFiber] at hS
    rw [mem_occupancySlotChoices]
    refine ⟨fun g => ⟨Finset.inter_subset_right, hS.1 g⟩, ?_, hS.2⟩
    exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (by rfl)
  · intro c hc
    change c ∈ occupancySlotChoices support a r at hc
    change reconstructOccupancyChoice c ∈ occupancySizeFiber support a r
    rw [mem_occupancySizeFiber]
    have hcode := freeSetOccupancyCode_reconstructChoice support hpair a r c hc
    rw [mem_occupancySlotChoices] at hc
    constructor
    · intro g
      calc
        (reconstructOccupancyChoice c ∩ support g).card
            = (c.1 g).card := congrArg (fun x => (x.1 g).card) hcode
        _ = a g := (hc.1 g).2
    · calc
        (reconstructOccupancyChoice c \ supportUnion support).card
            = c.2.card := congrArg (fun x => x.2.card) hcode
        _ = r := hc.2.2
  · intro S hS
    exact (freeSetOccupancyCode_reconstruct support S).symm
  · intro c hc
    exact freeSetOccupancyCode_reconstructChoice support hpair a r c hc

/-- Equal pairwise-disjoint width-`w` blocks occupy exactly `G*w` ambient coordinates. -/
theorem supportUnion_card_of_pairwiseDisjoint_uniform {n G w : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = w) :
    (supportUnion support).card = G * w := by
  classical
  have hpair' : ((Finset.univ : Finset (Fin G)) : Set (Fin G)).PairwiseDisjoint support := by
    intro g _ h _ hne
    exact hpair g h hne
  rw [supportUnion, Finset.card_biUnion hpair']
  simp_rw [hcard]
  simp

/-- Uniform-width specialization of the exact occupancy fiber formula.  This is the advertised
hypergeometric summand: one `choose w (a g)` factor per block and an outside reservoir of size
`n-G*w`. -/
theorem occupancySizeFiber_card_uniform {n G w : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = w)
    (a : Fin G → ℕ) (r : ℕ) :
    (occupancySizeFiber support a r).card =
      (∏ g, w.choose (a g)) * (n - G * w).choose r := by
  rw [occupancySizeFiber_card support hpair a r]
  congr 1
  · apply Finset.prod_congr rfl
    intro g _
    rw [hcard]
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, supportUnion_card_of_pairwiseDisjoint_uniform support hpair hcard]

/-- The bounded size profile used to index the exact occupancy partition.  The ambient `n+1`
bound is deliberately independent of the block widths, so the definition also handles ragged
families without choosing width-dependent finite types. -/
def occupancySizeIndex {n G : ℕ} (support : Fin G → Finset (Fin n))
    (S : Finset (Fin n)) : (Fin G → Fin (n + 1)) × Fin (n + 1) :=
  (fun g => ⟨(S ∩ support g).card, Nat.lt_succ_of_le <|
      (Finset.card_le_card (Finset.inter_subset_left)).trans <| by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card (Finset.subset_univ S)⟩,
    ⟨(S \ supportUnion support).card, Nat.lt_succ_of_le <|
      (Finset.card_le_card (Finset.sdiff_subset)).trans <| by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card (Finset.subset_univ S)⟩)

/-- The finite stars-and-bars index set for a ragged family: every block occupancy fits in its
block, the block and outside occupancies add to `K`, and more than `trunkDepth` blocks are full. -/
def admissibleOccupancyIndices {n G : ℕ} (support : Fin G → Finset (Fin n))
    (K trunkDepth : ℕ) : Finset ((Fin G → Fin (n + 1)) × Fin (n + 1)) :=
  Finset.univ.filter fun p =>
    (∀ g, (p.1 g).val ≤ (support g).card) ∧
      (∑ g, (p.1 g).val) + p.2.val = K ∧
      trunkDepth < (Finset.univ.filter fun g => (p.1 g).val = (support g).card).card

theorem mem_admissibleOccupancyIndices {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (K trunkDepth : ℕ)
    (p : (Fin G → Fin (n + 1)) × Fin (n + 1)) :
    p ∈ admissibleOccupancyIndices support K trunkDepth ↔
      (∀ g, (p.1 g).val ≤ (support g).card) ∧
        (∑ g, (p.1 g).val) + p.2.val = K ∧
        trunkDepth <
          (Finset.univ.filter fun g => (p.1 g).val = (support g).card).card := by
  simp [admissibleOccupancyIndices]

/-- A free set belongs to the many-intact event exactly when its bounded size profile is an
admissible index.  Pairwise disjointness is used only for the additive size constraint. -/
theorem occupancySizeIndex_mem_admissible_iff {n G : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (K trunkDepth : ℕ) (S : Finset (Fin n)) :
    occupancySizeIndex support S ∈ admissibleOccupancyIndices support K trunkDepth ↔
      S ∈ manyIntactFreeSets support K trunkDepth := by
  classical
  rw [mem_admissibleOccupancyIndices, mem_manyIntactFreeSets_iff_occupancy]
  change
    (∀ g, (S ∩ support g).card ≤ (support g).card) ∧
        (∑ g, (S ∩ support g).card) + (S \ supportUnion support).card = K ∧
        trunkDepth <
          (Finset.univ.filter fun g => (S ∩ support g).card = (support g).card).card ↔
      S.card = K ∧ trunkDepth <
        (Finset.univ.filter fun g => S ∩ support g = support g).card
  have hbound : ∀ g, (S ∩ support g).card ≤ (support g).card :=
    fun g => Finset.card_le_card Finset.inter_subset_right
  have hsize := freeSetOccupancyCode_card support hpair S
  change S.card = (∑ g, (S ∩ support g).card) +
    (S \ supportUnion support).card at hsize
  have hfull : (Finset.univ.filter fun g => (S ∩ support g).card = (support g).card) =
      Finset.univ.filter fun g => S ∩ support g = support g := by
    apply Finset.filter_congr
    intro g _
    constructor
    · intro hcard
      exact Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    · intro heq
      exact congrArg Finset.card heq
  rw [hfull, ← hsize]
  simp [hbound]

/-- An admissible profile fiber inside the event is exactly the unrestricted occupancy-size
fiber.  This is the disjoint-partition statement at the level of individual parts. -/
theorem manyIntactFreeSets_filter_sizeIndex_eq {n G : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (K trunkDepth : ℕ) (p : (Fin G → Fin (n + 1)) × Fin (n + 1))
    (hp : p ∈ admissibleOccupancyIndices support K trunkDepth) :
    (manyIntactFreeSets support K trunkDepth).filter
        (fun S => occupancySizeIndex support S = p) =
      occupancySizeFiber support (fun g => (p.1 g).val) p.2.val := by
  classical
  ext S
  simp only [Finset.mem_filter, mem_occupancySizeFiber]
  constructor
  · rintro ⟨_, hindex⟩
    have hfirst := congrArg Prod.fst hindex
    have hsecond := congrArg Prod.snd hindex
    constructor
    · intro g
      exact congrArg Fin.val (congrFun hfirst g)
    · exact congrArg Fin.val hsecond
  · rintro ⟨hblocks, houtside⟩
    have hindex : occupancySizeIndex support S = p := by
      apply Prod.ext
      · funext g
        apply Fin.ext
        exact hblocks g
      · apply Fin.ext
        exact houtside
    refine ⟨?_, hindex⟩
    rw [← occupancySizeIndex_mem_admissible_iff support hpair K trunkDepth]
    exact hindex.symm ▸ hp

/-- Exact finite-sum enumeration of the many-intact free-set event.  The admissible profiles are
disjoint because `occupancySizeIndex` is a function, and every summand has its independent
product-of-binomial weight. -/
theorem manyIntactFreeSets_card_eq_sum_occupancy {n G : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (K trunkDepth : ℕ) :
    (manyIntactFreeSets support K trunkDepth).card =
      ∑ p ∈ admissibleOccupancyIndices support K trunkDepth,
        (∏ g, (support g).card.choose (p.1 g).val) *
          ((Finset.univ \ supportUnion support).card.choose p.2.val) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := occupancySizeIndex support)
    (t := admissibleOccupancyIndices support K trunkDepth)]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [manyIntactFreeSets_filter_sizeIndex_eq support hpair K trunkDepth p hp,
      occupancySizeFiber_card support hpair]
  · intro S hS
    exact (occupancySizeIndex_mem_admissible_iff support hpair K trunkDepth S).2 hS

/-- Uniform disjoint blocks cannot contribute to the many-intact event when the requested number
of complete blocks already needs more than the entire live-coordinate budget.  This is the sharp
support-volume cutoff: more than `trunkDepth` intact width-`width` blocks require at least
`(trunkDepth + 1) * width` live coordinates. -/
theorem manyIntactFreeSets_eq_empty_of_uniform_volume
    {n G K trunkDepth width : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = width)
    (hvolume : K < (trunkDepth + 1) * width) :
    manyIntactFreeSets support K trunkDepth = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro S hS
  simp only [manyIntactFreeSets, Finset.mem_filter, Finset.mem_powersetCard] at hS
  let intact : Finset (Fin G) :=
    Finset.univ.filter fun g => support g ⊆ S
  have hintact : trunkDepth < intact.card := hS.2
  have hdisj : ((intact : Finset (Fin G)) : Set (Fin G)).PairwiseDisjoint support := by
    intro g _ h _ hne
    exact hpair g h hne
  have hunionCard : (intact.biUnion support).card = intact.card * width := by
    rw [Finset.card_biUnion hdisj]
    simp [hcard]
  have hunionSubset : intact.biUnion support ⊆ S := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨g, hg, hig⟩ := hi
    exact (Finset.mem_filter.mp hg).2 hig
  have hcapacity : intact.card * width ≤ K := by
    rw [← hS.1.2, ← hunionCard]
    exact Finset.card_le_card hunionSubset
  have hcount : trunkDepth + 1 ≤ intact.card := by omega
  have hrequired : (trunkDepth + 1) * width ≤ intact.card * width :=
    Nat.mul_le_mul_right width hcount
  exact (Nat.not_lt_of_ge (hrequired.trans hcapacity)) hvolume

/-- At the intended half-shell schedule with width two, the many-intact-block obstruction is
empty: `10*r + 1` complete blocks would consume `20*r + 2` coordinates in a `20*r` shell. -/
theorem manyIntactFreeSets_eq_empty_width_two_half_shell
    {n G r : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 2) :
    manyIntactFreeSets support (20 * r) (10 * r) = ∅ := by
  apply manyIntactFreeSets_eq_empty_of_uniform_volume support hpair hcard
  omega

/-- Exact shell factorization for the many-intact-block event.  Every qualifying `K`-element
free set has exactly `2^(n-K)` restrictions above it, independently of its block occupancy.
Thus the remaining equal-block calculation is purely a hypergeometric count of free sets. -/
theorem manyIntactShell_card {n G : ℕ} (support : Fin G → Finset (Fin n))
    (K trunkDepth : ℕ) :
    (manyIntactShell support K trunkDepth).card =
      (manyIntactFreeSets support K trunkDepth).card * 2 ^ (n - K) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Restriction n => freeVars σ)
    (t := manyIntactFreeSets support K trunkDepth)]
  · have hterm : ∀ S ∈ manyIntactFreeSets support K trunkDepth,
        ((manyIntactShell support K trunkDepth).filter
          (fun σ => freeVars σ = S)).card = 2 ^ (n - K) := by
      intro S hS
      have hSparts := Finset.mem_filter.mp hS
      have hScard : S.card = K := (Finset.mem_powersetCard.mp hSparts.1).2
      have heq :
          (manyIntactShell support K trunkDepth).filter
              (fun σ => freeVars σ = S) =
            Finset.univ.filter (fun σ : Restriction n => freeVars σ = S) := by
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro hfree
          refine ⟨?_, hfree⟩
          rw [manyIntactShell, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · rw [stars, hfree, hScard]
          · simpa [intactSupportBlocks, hfree] using hSparts.2
      rw [heq, card_freeVars_eq, hScard]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  · intro σ hσ
    have hσ' : σ ∈ manyIntactShell support K trunkDepth := hσ
    rw [manyIntactShell, Finset.mem_filter] at hσ'
    change freeVars σ ∈ manyIntactFreeSets support K trunkDepth
    rw [manyIntactFreeSets, Finset.mem_filter]
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · simpa [stars] using hσ'.2.1
    · simpa [intactSupportBlocks] using hσ'.2.2

/-- The restriction-valued obstruction is also empty at the intended width-two half-shell
schedule; fixed Boolean values cannot revive an impossible free-coordinate occupancy profile. -/
theorem manyIntactShell_eq_empty_width_two_half_shell
    {n G r : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 2) :
    manyIntactShell support (20 * r) (10 * r) = ∅ := by
  rw [← Finset.card_eq_zero, manyIntactShell_card,
    manyIntactFreeSets_eq_empty_width_two_half_shell support hpair hcard]
  simp

/-- If more pairwise-disjoint blocks remain intact than there are queried coordinates, one intact
block is missed completely.  This is the shell-level version of the fully-live packing lemma. -/
theorem exists_intact_support_disjoint_of_pairwiseDisjoint
    {n G : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (σ : Restriction n) (path : Finset (Fin n))
    (hpath : path.card < (intactSupportBlocks support σ).card) :
    ∃ g ∈ intactSupportBlocks support σ, Disjoint (support g) path := by
  by_contra hmiss
  push_neg at hmiss
  have hmeet (g : {g // g ∈ intactSupportBlocks support σ}) :
      ∃ i, i ∈ support g.1 ∧ i ∈ path :=
    Finset.not_disjoint_iff.mp (hmiss g.1 g.2)
  let hit : {g // g ∈ intactSupportBlocks support σ} → {i // i ∈ path} := fun g ↦
    ⟨Classical.choose (hmeet g), (Classical.choose_spec (hmeet g)).2⟩
  have hit_mem (g : {g // g ∈ intactSupportBlocks support σ}) :
      (hit g).1 ∈ support g.1 :=
    (Classical.choose_spec (hmeet g)).1
  have hinj : Function.Injective hit := by
    intro g h heq
    apply Subtype.ext
    by_contra hne
    have hdisj := hpair g.1 h.1 hne
    apply (Finset.not_disjoint_iff.mpr ⟨(hit g).1, hit_mem g, ?_⟩) hdisj
    simpa [heq] using hit_mem h
  have hcard : (intactSupportBlocks support σ).card ≤ path.card := by
    simpa using Fintype.card_le_of_injective hit hinj
  omega

/-- General semantic core at an arbitrary restriction.  It is enough that every shallow path
misses one block which was wholly free at the root; toggling an unqueried free coordinate shows
that the reached restriction must leave that coordinate free as well. -/
theorem supportedGates_not_commonShallowAt_of_intact_miss
    {n G fuel trunkDepth residualDepth : ℕ}
    (gates : Fin G → List (Clause n)) (support : Fin G → Finset (Fin n))
    (σ : Restriction n)
    (hmiss : ∀ path : Finset (Fin n), path.card ≤ trunkDepth →
      ∃ g, support g ⊆ freeVars σ ∧ Disjoint (support g) path)
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i = none) →
        residualDepth < (canonicalDT (gates g) fuel rho).depth) :
    ¬ CommonShallowAt gates fuel σ trunkDepth residualDepth := by
  rintro ⟨trunk, hdepth, hleaf⟩
  let x : Fin n → Bool := fun i => (σ i).getD false
  have hx : Rung4Restriction.Extends σ x := by
    intro i b hi
    simp [x, hi]
  let path : Finset (Fin n) := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ trunkDepth := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ trunkDepth := hdepth
  obtain ⟨g, hgfree, hgdisj⟩ := hmiss path hpathCard
  have hfree (i : Fin n) (hiσ : σ i = none) (hi : i ∉ path) :
      CommonTree.run trunk x i = none := by
    let y : Fin n → Bool := Function.update x i (!x i)
    have hy : Rung4Restriction.Extends σ y := by
      intro j b hj
      have hji : j ≠ i := by
        intro h
        subst j
        rw [hiσ] at hj
        simp at hj
      simpa [y, Function.update_of_ne hji] using hx j b hj
    obtain ⟨_, htx, _⟩ := hleaf x hx
    obtain ⟨_, hty, _⟩ := hleaf y hy
    have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
      exact CommonTree.run_update_of_not_mem_queryVars trunk x i
        (by simpa [path] using hi)
    cases ht : CommonTree.run trunk x i with
    | none => rfl
    | some b =>
        have hbx : x i = b := htx i b ht
        have hby : y i = b := by
          apply hty i b
          simpa [hrun] using ht
        cases hxi : x i with
        | false =>
            have hbfalse : b = false := by simpa [hxi] using hbx.symm
            have hbtrue : b = true := by simpa [y, hxi] using hby.symm
            exact False.elim (Bool.false_ne_true (hbfalse.symm.trans hbtrue))
        | true =>
            have hbtrue : b = true := by simpa [hxi] using hbx.symm
            have hbfalse : b = false := by simpa [y, hxi] using hby.symm
            exact False.elim (Bool.false_ne_true (hbfalse.symm.trans hbtrue))
  obtain ⟨_, _, hshallow⟩ := hleaf x hx
  have hgateDeep : residualDepth <
      (canonicalDT (gates g) fuel (CommonTree.run trunk x)).depth := by
    apply hdeep (CommonTree.run trunk x) g
    intro i hiSupport
    apply hfree i (mem_freeVars.mp (hgfree hiSupport))
    exact Finset.disjoint_left.mp hgdisj hiSupport
  exact (Nat.not_lt_of_ge (hshallow g)) hgateDeep

/-- Pairwise-disjoint supports lift the arbitrary-root semantic obstruction exactly when the
number of intact blocks exceeds the common-trunk depth. -/
theorem pairwiseDisjoint_supportedGates_not_commonShallowAt_of_intact
    {n G fuel trunkDepth residualDepth : ℕ}
    (gates : Fin G → List (Clause n)) (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (σ : Restriction n)
    (hintact : trunkDepth < (intactSupportBlocks support σ).card)
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i = none) →
        residualDepth < (canonicalDT (gates g) fuel rho).depth) :
    ¬ CommonShallowAt gates fuel σ trunkDepth residualDepth := by
  apply supportedGates_not_commonShallowAt_of_intact_miss gates support σ
  · intro path hpath
    obtain ⟨g, hgintact, hgdisj⟩ :=
      exists_intact_support_disjoint_of_pairwiseDisjoint support hpair σ path
        (lt_of_le_of_lt hpath hintact)
    exact ⟨g, (Finset.mem_filter.mp hgintact).2, hgdisj⟩
  · exact hdeep

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

/-- Pairwise-disjoint deep blocks instantiate the complete semantic obstruction: if the family
contains more blocks than a common trunk can query, the fully live root is bad.  The only
gate-specific premise left is the canonical depth of a block whose entire support remains free. -/
theorem allFree_mem_commonShallowBad_of_pairwiseDisjoint
    {n G fuel trunkDepth residualDepth : ℕ}
    (gates : Fin G → List (Clause n)) (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hblocks : trunkDepth < G)
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i = none) →
        residualDepth < (canonicalDT (gates g) fuel rho).depth) :
    (fun _ : Fin n ↦ none) ∈
      commonShallowBad gates fuel n trunkDepth residualDepth := by
  exact allFree_mem_commonShallowBad_of_supportedGates gates support
    (pairwiseDisjoint_support_miss support hpair hblocks) hdeep

/-- A single ordered positive conjunction block. -/
def orderedConjunctionBlock {n : ℕ} (xs : List (Fin n)) : List (Clause n) :=
  [⟨xs.map Rung4Literal.pos⟩]

/-- Structural form used to compute the exact depth of an ordered conjunction:
`done` records the distinct coordinates already fixed to true and `todo` the still-free suffix. -/
theorem orderedConjunctionBlock_depth_aux {n : ℕ} (done todo : List (Fin n))
    (hdup : (done ++ todo).Nodup)
    (rho : Restriction n)
    (hdone : ∀ i ∈ done, rho i = some true)
    (htodo : ∀ i ∈ todo, rho i = none) :
    (canonicalDT (orderedConjunctionBlock (done ++ todo)) todo.length rho).depth =
      todo.length := by
  induction todo generalizing done rho with
  | nil =>
      simp only [List.append_nil, List.length_nil]
      rw [canonicalDT]
      split <;> rfl
  | cons i todo ih =>
      have hiFree : rho i = none := htodo i (by simp)
      have hiDone : i ∉ done := by
        intro hi
        have hparts := List.nodup_append.mp hdup
        exact (hparts.2.2 i hi i (by simp)) rfl
      have hiTodo : i ∉ todo := by
        have hparts := List.nodup_append.mp hdup
        exact (List.nodup_cons.mp hparts.2.1).1
      let T : Clause n := ⟨(done ++ i :: todo).map Rung4Literal.pos⟩
      have hany : anyTermSat [T] rho = false := by
        simp [T, anyTermSat, termSat, List.all_append, Depth3.litTrue,
          litFixedVal, hiFree]
      have hnotFalse : termFalsified rho T = false := by
        rw [termFalsified, List.any_eq_false]
        intro l hl
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
        rcases List.mem_append.mp hj with hj | hj
        · simp [litFalse, litFixedVal, hdone j hj]
        · rcases List.mem_cons.mp hj with rfl | hj
          · simp [litFalse, litFixedVal, hiFree]
          · simp [litFalse, litFixedVal, htodo j (by simp [hj])]
      have hfreeExact : freeLits rho T =
          Rung4Literal.pos i :: todo.map Rung4Literal.pos := by
        have hdoneFilter : (done.map Rung4Literal.pos).filter (litFree rho) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro l hl
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
          simp [litFree, litFixedVal, hdone j hj]
        have htodoFilter : (todo.map Rung4Literal.pos).filter (litFree rho) =
            todo.map Rung4Literal.pos := by
          apply List.filter_eq_self.mpr
          intro l hl
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
          simp [litFree, litFixedVal, htodo j (by simp [hj])]
        simp [freeLits, T, List.filter_append, hdoneFilter, htodoFilter,
          litFree, litFixedVal, hiFree]
      have hactive : activeTerm [T] rho = some T := by
        rw [activeTerm_eq_find hany]
        simp [hnotFalse, hfreeExact]
      have hhead : (freeLits rho T).head? = some (Rung4Literal.pos i) := by
        rw [hfreeExact]
        rfl
      rw [show orderedConjunctionBlock (done ++ i :: todo) = [T] by rfl]
      change (canonicalDT [T] (todo.length + 1) rho).depth = todo.length + 1
      rw [canonicalDT]
      simp only [hany, Bool.false_eq_true, if_false, hactive, hhead]
      simp only [litVar, BoolDecisionTree.depth]
      have hfalse : (canonicalDT [T] todo.length (fixVar rho i false)).depth ≤
          todo.length := canonicalDT_depth_le [T] todo.length _
      have hdup' : ((done ++ [i]) ++ todo).Nodup := by
        simpa [List.append_assoc] using hdup
      have hdone' : ∀ j ∈ done ++ [i], fixVar rho i true j = some true := by
        intro j hj
        rcases List.mem_append.mp hj with hj | hj
        · have hji : j ≠ i := by
            intro h
            subst j
            exact hiDone hj
          rw [fixVar, Function.update_of_ne hji]
          exact hdone j hj
        · simp only [List.mem_singleton] at hj
          subst j
          simp [fixVar]
      have htodo' : ∀ j ∈ todo, fixVar rho i true j = none := by
        intro j hj
        have hji : j ≠ i := fun h => hiTodo (h ▸ hj)
        simp [fixVar, Function.update_of_ne hji, htodo j (by simp [hj])]
      have htrue :
          (canonicalDT [T] todo.length (fixVar rho i true)).depth = todo.length := by
        simpa [orderedConjunctionBlock, List.append_assoc, T] using
          ih (done ++ [i]) hdup' (fixVar rho i true) hdone' htodo'
      omega

/-- A duplicate-free ordered conjunction whose coordinates are all free has canonical depth
exactly its length when given that much fuel.  Coordinates outside the block may be arbitrary. -/
theorem orderedConjunctionBlock_depth {n : ℕ} (xs : List (Fin n)) (hdup : xs.Nodup)
    (rho : Restriction n) (hfree : ∀ i ∈ xs, rho i = none) :
    (canonicalDT (orderedConjunctionBlock xs) xs.length rho).depth = xs.length := by
  simpa using orderedConjunctionBlock_depth_aux ([] : List (Fin n)) xs
    (by simpa using hdup) rho (by simp) hfree

/-- With enough fuel for the ambient restriction, an ordered positive conjunction has depth at
least the number of its distinct coordinates that remain free, provided none of its coordinates
is fixed false.  Unlike `orderedConjunctionBlock_depth`, fixed-true coordinates may occur anywhere
in the ordered clause.

The proof is semantic and therefore does not need `Nodup`: on the all-true extension, every free
support coordinate must occur on the decision-tree path, since flipping any missing coordinate
makes the conjunction false while off-path invariance would keep the tree's value unchanged. -/
theorem orderedConjunctionBlock_freeSupport_card_le_depth {n fuel : ℕ}
    (xs : List (Fin n)) (rho : Restriction n) (hfuel : stars rho ≤ fuel)
    (hnotFalse : ∀ i ∈ xs, rho i ≠ some false) :
    (xs.toFinset ∩ freeVars rho).card ≤
      (canonicalDT (orderedConjunctionBlock xs) fuel rho).depth := by
  classical
  let tree := canonicalDT (orderedConjunctionBlock xs) fuel rho
  let x : Fin n → Bool := fun i => (rho i).getD true
  have hxext : Rung4Restriction.Extends rho x := by
    intro i b hi
    simp [x, hi]
  have hxtrue (i : Fin n) (hi : i ∈ xs) : x i = true := by
    cases hri : rho i with
    | none => simp [x, hri]
    | some b =>
        cases b with
        | false => exact False.elim (hnotFalse i hi hri)
        | true => simp [x, hri]
  let path := DTree.pathVars (toDTree tree) x
  have hpathCard : path.card ≤ tree.depth := by
    rw [← toDTree_depth]
    exact DTree.pathVars_card_le_depth (toDTree tree) x
  by_contra hdepth
  have hdepth' : ¬(xs.toFinset ∩ freeVars rho).card ≤ tree.depth := by
    simpa [tree] using hdepth
  have hlt : path.card < (xs.toFinset ∩ freeVars rho).card := by omega
  have hnsub : ¬ xs.toFinset ∩ freeVars rho ⊆ path := fun hsub => by
    have := Finset.card_le_card hsub
    omega
  obtain ⟨j, hjSupport, hjPath⟩ := Finset.not_subset.mp hnsub
  have hjxs : j ∈ xs := List.mem_toFinset.mp (Finset.mem_inter.mp hjSupport).1
  have hjrho : rho j = none := mem_freeVars.mp (Finset.mem_inter.mp hjSupport).2
  let y : Fin n → Bool := Function.update x j false
  have hyext : Rung4Restriction.Extends rho y := by
    intro i b hi
    have hij : i ≠ j := by
      intro h
      subst i
      rw [hjrho] at hi
      simp at hi
    simpa [y, Function.update_of_ne hij] using hxext i b hi
  have hinvariant : tree.eval y = tree.eval x := by
    rw [← toDTree_eval, ← toDTree_eval]
    exact DTree.eval_invariant_off_path (toDTree tree) x j false hjPath
  have hxeval : tree.eval x = dnfEval (orderedConjunctionBlock xs) x := by
    exact canonicalDT_eval fuel rho x hfuel hxext
  have hyeval : tree.eval y = dnfEval (orderedConjunctionBlock xs) y := by
    exact canonicalDT_eval fuel rho y hfuel hyext
  have hdnfx : dnfEval (orderedConjunctionBlock xs) x = true := by
    have hall : Rung4DNFTerm.evalLits (xs.map Rung4Literal.pos) x = true :=
      evalLits_eq_true_of_all _ <| by
        intro l hl
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
        simpa [Rung4Literal.eval] using hxtrue i hi
    simpa [orderedConjunctionBlock, dnfEval] using hall
  have hdnfy : dnfEval (orderedConjunctionBlock xs) y = false := by
    have hjmem : Rung4Literal.pos j ∈ xs.map Rung4Literal.pos :=
      List.mem_map.mpr ⟨j, hjxs, rfl⟩
    have hfalse : Rung4DNFTerm.evalLits (xs.map Rung4Literal.pos) y = false :=
      evalLits_eq_false_of_mem _ _ hjmem (by simp [Rung4Literal.eval, y])
    simpa [orderedConjunctionBlock, dnfEval] using hfalse
  rw [hyeval, hdnfy, hxeval, hdnfx] at hinvariant
  exact Bool.false_ne_true hinvariant

/-- The parameterized disjoint-block obstruction with its gate-specific premise discharged.
For `G` pairwise-disjoint, duplicate-free ordered conjunctions of common length `width`, every
trunk shallower than `G` leaves one entire block untouched; if `residualDepth < width`, the fully
live root is therefore in the actual semantic bad event. -/
theorem allFree_mem_commonShallowBad_of_orderedConjunctionBlocks
    {n G width trunkDepth residualDepth : ℕ}
    (blocks : Fin G → List (Fin n))
    (hdup : ∀ g, (blocks g).Nodup)
    (hwidth : ∀ g, (blocks g).length = width)
    (hpair : ∀ g h, g ≠ h → Disjoint (blocks g).toFinset (blocks h).toFinset)
    (hblocks : trunkDepth < G) (hresidual : residualDepth < width) :
    (fun _ : Fin n ↦ none) ∈
      commonShallowBad (fun g ↦ orderedConjunctionBlock (blocks g)) width n
        trunkDepth residualDepth := by
  apply allFree_mem_commonShallowBad_of_pairwiseDisjoint
    (fun g ↦ orderedConjunctionBlock (blocks g)) (fun g ↦ (blocks g).toFinset)
    hpair hblocks
  intro rho g hfree
  have hdepth := orderedConjunctionBlock_depth (blocks g) (hdup g) rho
    (fun i hi ↦ hfree i (List.mem_toFinset.mpr hi))
  rw [hwidth g] at hdepth
  omega

/-- Exact shell-level semantic lift for ordered conjunction blocks.  Every fixed-`K` restriction
retaining more intact blocks than the trunk can query belongs to the actual common-shallow bad
event.  The remaining problem is purely to count this explicitly defined intact-block event. -/
theorem mem_commonShallowBad_of_orderedConjunctionBlocks_of_many_intact
    {n G width K trunkDepth residualDepth : ℕ}
    (blocks : Fin G → List (Fin n))
    (hdup : ∀ g, (blocks g).Nodup)
    (hwidth : ∀ g, (blocks g).length = width)
    (hpair : ∀ g h, g ≠ h → Disjoint (blocks g).toFinset (blocks h).toFinset)
    (σ : Restriction n) (hstars : stars σ = K)
    (hintact : trunkDepth <
      (intactSupportBlocks (fun g => (blocks g).toFinset) σ).card)
    (hresidual : residualDepth < width) :
    σ ∈ commonShallowBad (fun g ↦ orderedConjunctionBlock (blocks g)) width K
      trunkDepth residualDepth := by
  rw [mem_commonShallowBad]
  refine ⟨hstars, ?_⟩
  apply pairwiseDisjoint_supportedGates_not_commonShallowAt_of_intact
    (fun g ↦ orderedConjunctionBlock (blocks g))
    (fun g ↦ (blocks g).toFinset) hpair σ hintact
  intro rho g hfree
  have hdepth := orderedConjunctionBlock_depth (blocks g) (hdup g) rho
    (fun i hi ↦ hfree i (List.mem_toFinset.mpr hi))
  rw [hwidth g] at hdepth
  omega

/-- The entire explicit many-intact shell event embeds into the semantic bad event for disjoint
ordered conjunction blocks. -/
theorem manyIntactShell_subset_commonShallowBad_of_orderedConjunctionBlocks
    {n G width K trunkDepth residualDepth : ℕ}
    (blocks : Fin G → List (Fin n))
    (hdup : ∀ g, (blocks g).Nodup)
    (hwidth : ∀ g, (blocks g).length = width)
    (hpair : ∀ g h, g ≠ h → Disjoint (blocks g).toFinset (blocks h).toFinset)
    (hresidual : residualDepth < width) :
    manyIntactShell (fun g ↦ (blocks g).toFinset) K trunkDepth ⊆
      commonShallowBad (fun g ↦ orderedConjunctionBlock (blocks g)) width K
        trunkDepth residualDepth := by
  intro σ hσ
  rw [manyIntactShell, Finset.mem_filter] at hσ
  exact mem_commonShallowBad_of_orderedConjunctionBlocks_of_many_intact
    blocks hdup hwidth hpair σ hσ.2.1 hσ.2.2 hresidual

/-- Exact occupancy-to-semantics lower bound.  The number of bad restrictions is at least the
number of qualifying `K`-element free sets times the common fixed-value multiplicity
`2^(n-K)`. -/
theorem manyIntactFreeSets_mul_pow_le_commonShallowBad_card
    {n G width K trunkDepth residualDepth : ℕ}
    (blocks : Fin G → List (Fin n))
    (hdup : ∀ g, (blocks g).Nodup)
    (hwidth : ∀ g, (blocks g).length = width)
    (hpair : ∀ g h, g ≠ h → Disjoint (blocks g).toFinset (blocks h).toFinset)
    (hresidual : residualDepth < width) :
    (manyIntactFreeSets (fun g ↦ (blocks g).toFinset) K trunkDepth).card *
        2 ^ (n - K) ≤
      (commonShallowBad (fun g ↦ orderedConjunctionBlock (blocks g)) width K
        trunkDepth residualDepth).card := by
  rw [← manyIntactShell_card]
  exact Finset.card_le_card
    (manyIntactShell_subset_commonShallowBad_of_orderedConjunctionBlocks
      blocks hdup hwidth hpair hresidual)

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

/-- Querying one coordinate from each live pair is the exact boundary certificate.  This
two-query trunk fixes coordinates `0` and `2`, leaving at most one free coordinate in each
ordered conjunction block. -/
def independentPairBoundaryTrunk : CommonTree 4 (Restriction 4) :=
  .query 0
    (.query 2
      (.leaf (fixVar (fixVar (fun _ => none) 0 false) 2 false))
      (.leaf (fixVar (fixVar (fun _ => none) 0 false) 2 true)))
    (.query 2
      (.leaf (fixVar (fixVar (fun _ => none) 0 true) 2 false))
      (.leaf (fixVar (fixVar (fun _ => none) 0 true) 2 true)))

/-- The smallest disjoint width-two example is shallow exactly at the block-count boundary:
although no depth-one trunk works, a depth-two trunk makes both gates residual-depth one. -/
theorem independentPairs_commonShallowAt_two :
    CommonShallowAt independentPairGates 2 (fun _ : Fin 4 => none) 2 1 := by
  refine ⟨independentPairBoundaryTrunk, by decide, ?_⟩
  intro x hx
  constructor
  · intro i b hi
    simp at hi
  constructor
  · cases h0 : x 0 <;> cases h2 : x 2 <;>
      simpa [independentPairBoundaryTrunk, CommonTree.run, h0, h2] using
        (extends_fixVar (extends_fixVar hx h0) h2)
  · intro g
    fin_cases g <;> cases h0 : x 0 <;> cases h2 : x 2 <;>
      simp [independentPairBoundaryTrunk, CommonTree.run, independentPairGates,
        canonicalDT, anyTermSat, termSat, activeTerm, termFalsified, freeLits,
        Depth3.litTrue, litVar, litFixedVal, litFalse, litFree, fixVar,
        BoolDecisionTree.depth, h0, h2]

/-- Consequently the exact two-intact-block boundary is not in the semantic bad event when the
trunk is allowed two queries. -/
theorem allFreeFour_not_mem_commonShallowBad_two :
    (fun _ : Fin 4 => none) ∉ commonShallowBad independentPairGates 2 4 2 1 := by
  rw [mem_commonShallowBad]
  intro hbad
  exact hbad.2 independentPairs_commonShallowAt_two

/-! ### Width-three boundary obstruction -/

/-! ### Weighted live-support deficit -/

/-- The coordinates of a support block that are live at the root restriction. -/
def liveSupport {n G : ℕ} (support : Fin G → Finset (Fin n))
    (σ : Restriction n) (g : Fin G) : Finset (Fin n) :=
  support g ∩ freeVars σ

/-- The minimum number of distinct true-path queries that block `g` needs before at most
`residualDepth` of its root-live coordinates remain unqueried. -/
def residualQueryDeficit {n G : ℕ} (support : Fin G → Finset (Fin n))
    (σ : Restriction n) (residualDepth : ℕ) (g : Fin G) : ℕ :=
  (liveSupport support σ g).card - residualDepth

/-- A positive-conjunction support is compatible with the all-true branch when none of its
coordinates is already fixed false at the root. -/
def supportTrueCompatible {n G : ℕ} (support : Fin G → Finset (Fin n))
    (σ : Restriction n) (g : Fin G) : Prop :=
  ∀ i ∈ support g, σ i ≠ some false

/-- The sound weighted deficit for positive conjunctions.  Blocks already killed by a fixed
false coordinate contribute zero, even if several other coordinates remain live. -/
noncomputable def compatibleResidualQueryDeficit {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (σ : Restriction n)
    (residualDepth : ℕ) (g : Fin G) : ℕ :=
  by
    classical
    exact if supportTrueCompatible support σ g then
      residualQueryDeficit support σ residualDepth g
    else 0

/-- The fixed-shell event whose total truth-compatible residual query demand exceeds the common
trunk budget.  Unlike `manyIntactShell`, its membership depends on fixed Boolean values as well as
the free set: a partially live positive block contributes only when all its other coordinates are
fixed true. -/
noncomputable def compatibleDeficitShell {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (K trunkDepth residualDepth : ℕ) :
    Finset (Restriction n) :=
  Finset.univ.filter fun σ =>
    stars σ = K ∧ trunkDepth <
      ∑ g, compatibleResidualQueryDeficit support σ residualDepth g

/-! ### Exact local width-three state enumerator -/

/-- Number of live coordinates in one abstract width-three block.  Isolating the block as
`Fin 3 → Option Bool` makes the local coefficient calculation independent of an ambient support
embedding; the later product count only has to transport restrictions along three-element support
bijections. -/
def tripleLocalStars (rho : Fin 3 → Option Bool) : ℕ :=
  (Finset.univ.filter fun i => rho i = none).card

/-- Truth-compatible residual query deficit of one width-three positive conjunction at residual
depth one.  A fixed false coordinate kills the block; otherwise its contribution is the number of
live coordinates minus one. -/
def tripleLocalDeficit (rho : Fin 3 → Option Bool) : ℕ :=
  if (∀ i, rho i ≠ some false) then tripleLocalStars rho - 1 else 0

/-- The local fiber with prescribed star count and compatible deficit. -/
def tripleLocalFiber (starCount deficit : ℕ) : Finset (Fin 3 → Option Bool) :=
  Finset.univ.filter fun rho =>
    tripleLocalStars rho = starCount ∧ tripleLocalDeficit rho = deficit

/-- Exact constant term of the local bivariate enumerator: all eight fully fixed assignments have
zero compatible deficit. -/
theorem tripleLocalFiber_card_zero_zero : (tripleLocalFiber 0 0).card = 8 := by
  decide

/-- Exact one-star coefficient: choose the live coordinate and freely fix the other two. -/
theorem tripleLocalFiber_card_one_zero : (tripleLocalFiber 1 0).card = 12 := by
  decide

/-- Of the six two-star restrictions, three fix their remaining coordinate false and therefore
contribute no compatible deficit. -/
theorem tripleLocalFiber_card_two_zero : (tripleLocalFiber 2 0).card = 3 := by
  decide

/-- The other three two-star restrictions fix their remaining coordinate true and contribute one
unit of compatible deficit. -/
theorem tripleLocalFiber_card_two_one : (tripleLocalFiber 2 1).card = 3 := by
  decide

/-- The unique fully live restriction contributes two compatible-deficit units. -/
theorem tripleLocalFiber_card_three_two : (tripleLocalFiber 3 2).card = 1 := by
  decide

/-- The five displayed fibers exhaust all local restrictions.  Together with the five exact
cardinalities above, this is the machine-checked coefficient table
`8 + 12*z + 3*z^2 + 3*z^2*y + z^3*y^2`. -/
theorem tripleLocalFibers_exhaustive :
    (Finset.univ : Finset (Fin 3 → Option Bool)) =
      tripleLocalFiber 0 0 ∪ tripleLocalFiber 1 0 ∪
        tripleLocalFiber 2 0 ∪ tripleLocalFiber 2 1 ∪ tripleLocalFiber 3 2 := by
  decide

/-! ### Product decomposition of ambient restrictions -/

/-- The independent restriction data carried by every support block, together with the
coordinates outside all support blocks.  This is the semantic product whose local factors will
be transported to `Fin 3 → Option Bool` in the width-three coefficient calculation. -/
def restrictionProductSpace {n G : ℕ}
    (support : Fin G → Finset (Fin n)) : Type :=
  ((g : Fin G) → ({i : Fin n // i ∈ support g} → Option Bool)) ×
    ({i : Fin n // i ∈ Finset.univ \ supportUnion support} → Option Bool)

/-- Restrict an ambient assignment independently to each support block and to the outside
reservoir. -/
def restrictionProductCode {n G : ℕ} (support : Fin G → Finset (Fin n))
    (rho : Restriction n) : restrictionProductSpace support :=
  (⟨fun _g i ↦ rho i.1, fun i ↦ rho i.1⟩)

/-- The block restrictions and outside restriction determine the ambient restriction.  Pairwise
disjointness is not needed for injectivity; it is needed below to show that the displayed target
contains no inconsistent duplicate block data. -/
theorem restrictionProductCode_injective {n G : ℕ}
    (support : Fin G → Finset (Fin n)) :
    Function.Injective (restrictionProductCode support) := by
  intro rho tau hcode
  funext i
  by_cases hi : i ∈ supportUnion support
  · rw [supportUnion, Finset.mem_biUnion] at hi
    obtain ⟨g, _, hig⟩ := hi
    have hg := congrFun (congrArg Prod.fst hcode) g
    exact congrFun hg ⟨i, hig⟩
  · have hout := congrArg Prod.snd hcode
    exact congrFun hout ⟨i, by simp [hi]⟩

/-- For disjoint uniform triples, the product code has exactly the same finite cardinality as
the ambient restriction space.  Thus every independently chosen collection of local triple
states and outside states is globally realizable. -/
theorem restrictionProductCode_bijective_triples {n G : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) :
    Function.Bijective (restrictionProductCode support) := by
  classical
  letI : Fintype (restrictionProductSpace support) := by
    unfold restrictionProductSpace
    infer_instance
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨restrictionProductCode_injective support, ?_⟩
  have hunion := supportUnion_card_of_pairwiseDisjoint_uniform support hpair hcard
  have hvolume : G * 3 ≤ n := by
    rw [← hunion]
    simpa [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card (Finset.subset_univ (supportUnion support)))
  simp only [restrictionProductSpace, Fintype.card_prod, Fintype.card_pi,
    Fintype.card_option, Fintype.card_bool]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe]
  simp_rw [hcard]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, hunion]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-- The resulting actual equivalence is the lossless block/outside factorization needed for the
generating-function count. -/
noncomputable def restrictionProductEquiv_triples {n G : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) :
    Restriction n ≃ restrictionProductSpace support :=
  Equiv.ofBijective (restrictionProductCode support)
    (restrictionProductCode_bijective_triples support hpair hcard)

/-- A chosen three-coordinate numbering of one uniform support block.  The downstream local
statistics are permutation-invariant, so the coefficient count does not depend on which
equivalence `equivOfCardEq` chooses. -/
noncomputable def tripleSupportEquiv {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (hcard : ∀ g, (support g).card = 3)
    (g : Fin G) : {i : Fin n // i ∈ support g} ≃ Fin 3 :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, hcard g, Fintype.card_fin])

/-- Reindex all block-local restrictions by `Fin 3`, leaving the outside reservoir unchanged. -/
noncomputable def restrictionProductToTripleEquiv {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (hcard : ∀ g, (support g).card = 3) :
    restrictionProductSpace support ≃
      ((Fin G → Fin 3 → Option Bool) ×
        ({i : Fin n // i ∈ Finset.univ \ supportUnion support} → Option Bool)) :=
  Equiv.prodCongr
    (Equiv.piCongr (Equiv.refl (Fin G)) fun g =>
      Equiv.arrowCongr (tripleSupportEquiv support hcard g) (Equiv.refl (Option Bool)))
    (Equiv.refl _)

/-- Full ambient product decomposition used by the target generating function: one abstract
27-state restriction per disjoint triple and one independent three-state choice per outside
coordinate. -/
noncomputable def ambientRestrictionTripleProductEquiv {n G : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) :
    Restriction n ≃
      ((Fin G → Fin 3 → Option Bool) ×
        ({i : Fin n // i ∈ Finset.univ \ supportUnion support} → Option Bool)) :=
  (restrictionProductEquiv_triples support hpair hcard).trans
    (restrictionProductToTripleEquiv support hcard)

/-- The abstract `Fin 3` state obtained by restricting an ambient assignment to one support
triple and transporting along the chosen support numbering. -/
noncomputable def ambientTripleState {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (hcard : ∀ g, (support g).card = 3)
    (σ : Restriction n) (g : Fin G) : Fin 3 → Option Bool :=
  (Equiv.arrowCongr (tripleSupportEquiv support hcard g) (Equiv.refl (Option Bool)))
    (fun i => σ i.1)

/-- Reindexing a three-element type preserves its number of free coordinates. -/
theorem tripleLocalStars_arrowCongr {α : Type} [Fintype α] [DecidableEq α]
    (e : α ≃ Fin 3) (rho : α → Option Bool) :
    tripleLocalStars ((Equiv.arrowCongr e (Equiv.refl (Option Bool))) rho) =
      (Finset.univ.filter fun i => rho i = none).card := by
  classical
  unfold tripleLocalStars
  apply Finset.card_bij (fun i _ => e.symm i)
  · intro i hi
    simpa [Equiv.arrowCongr_apply] using hi
  · intro i hi j hj hij
    exact e.symm.injective hij
  · intro i hi
    refine ⟨e i, ?_, ?_⟩
    · simpa [Equiv.arrowCongr_apply] using (Finset.mem_filter.mp hi).2
    · exact e.symm_apply_apply i

/-- Counting free coordinates on a support subtype agrees with intersecting the ambient free set
with that support. -/
theorem restrictedStars_eq_liveSupport_card {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (σ : Restriction n) (g : Fin G) :
    (Finset.univ.filter fun i : {i : Fin n // i ∈ support g} => σ i.1 = none).card =
      (liveSupport support σ g).card := by
  classical
  apply Finset.card_bij (fun i _ => i.1)
  · intro i hi
    rw [Finset.mem_filter] at hi
    rw [liveSupport, Finset.mem_inter]
    exact ⟨i.2, mem_freeVars.mpr hi.2⟩
  · intro i hi j hj hij
    exact Subtype.ext hij
  · intro i hi
    rw [liveSupport, Finset.mem_inter] at hi
    refine ⟨⟨i, hi.1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, mem_freeVars.mp hi.2⟩

/-- Each transported local star statistic is exactly the root-live cardinality of its ambient
support block. -/
theorem ambientTripleState_stars {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (hcard : ∀ g, (support g).card = 3)
    (σ : Restriction n) (g : Fin G) :
    tripleLocalStars (ambientTripleState support hcard σ g) =
      (liveSupport support σ g).card := by
  rw [ambientTripleState, tripleLocalStars_arrowCongr]
  exact restrictedStars_eq_liveSupport_card support σ g

/-- The transported local deficit is exactly the ambient truth-compatible residual query
deficit at residual depth one. -/
theorem ambientTripleState_deficit {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (hcard : ∀ g, (support g).card = 3)
    (σ : Restriction n) (g : Fin G) :
    tripleLocalDeficit (ambientTripleState support hcard σ g) =
      compatibleResidualQueryDeficit support σ 1 g := by
  classical
  have hcompat :
      (∀ i, ambientTripleState support hcard σ g i ≠ some false) ↔
        supportTrueCompatible support σ g := by
    constructor
    · intro h i hi
      let x : {i : Fin n // i ∈ support g} := ⟨i, hi⟩
      have hx := h ((tripleSupportEquiv support hcard g) x)
      simpa [ambientTripleState, Equiv.arrowCongr_apply] using hx
    · intro h i
      have hx := h ((tripleSupportEquiv support hcard g).symm i).1
        ((tripleSupportEquiv support hcard g).symm i).2
      simpa [ambientTripleState, Equiv.arrowCongr_apply] using hx
  by_cases hambient : supportTrueCompatible support σ g
  · have hlocal := hcompat.mpr hambient
    simp [tripleLocalDeficit, compatibleResidualQueryDeficit, hambient, hlocal,
      residualQueryDeficit, ambientTripleState_stars]
  · have hlocal : ¬(∀ i, ambientTripleState support hcard σ g i ≠ some false) :=
      fun h => hambient (hcompat.mp h)
    simp [tripleLocalDeficit, compatibleResidualQueryDeficit, hambient, hlocal]

/-- The ambient star count is the sum of the transported local triple star counts and the free
outside-coordinate count.  This is the `z`-weight preservation law for the product encoding. -/
theorem ambient_stars_eq_triple_sum_add_outside {n G : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) (σ : Restriction n) :
    stars σ = (∑ g, tripleLocalStars (ambientTripleState support hcard σ g)) +
      (Finset.univ.filter fun i : ↥(Finset.univ \ supportUnion support) =>
        σ i.1 = none).card := by
  rw [stars, freeSetOccupancyCode_card support hpair (freeVars σ)]
  congr 1
  · apply Finset.sum_congr rfl
    intro g _
    rw [ambientTripleState_stars]
    simp only [freeSetOccupancyCode, liveSupport, Finset.inter_comm]
  · change (freeVars σ \ supportUnion support).card = _
    apply Finset.card_bij (fun (i : Fin n) hi =>
        (⟨i, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩⟩ :
            {i : Fin n // i ∈ Finset.univ \ supportUnion support}))
    · intro i hi
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        mem_freeVars.mp (Finset.mem_sdiff.mp hi).1
    · intro i hi j hj hij
      exact congrArg Subtype.val hij
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨i.1, ?_, Subtype.ext rfl⟩
      exact Finset.mem_sdiff.mpr ⟨mem_freeVars.mpr hi, (Finset.mem_sdiff.mp i.2).2⟩

/-- The total compatible residual deficit is exactly the sum of the transported local deficit
weights.  This is the `y`-weight preservation law for the product encoding. -/
theorem compatible_deficit_eq_triple_sum {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (hcard : ∀ g, (support g).card = 3)
    (σ : Restriction n) :
    (∑ g, compatibleResidualQueryDeficit support σ 1 g) =
      ∑ g, tripleLocalDeficit (ambientTripleState support hcard σ g) := by
  apply Finset.sum_congr rfl
  intro g _
  exact (ambientTripleState_deficit support hcard σ g).symm

/-- The concrete product equivalence exposes exactly the transported triple states and the
unchanged outside restriction used in the weight laws above. -/
theorem ambientRestrictionTripleProductEquiv_apply {n G : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) (σ : Restriction n) :
    ambientRestrictionTripleProductEquiv support hpair hcard σ =
      (fun g => ambientTripleState support hcard σ g, fun i => σ i.1) := by
  rfl

/-- Combined weight preservation stated directly on the output of the ambient product
equivalence.  The first component is the generating function's total `z`-degree and the second is
its total `y`-degree. -/
theorem ambientRestrictionTripleProductEquiv_preserves_weights {n G : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) (σ : Restriction n) :
    let data := ambientRestrictionTripleProductEquiv support hpair hcard σ
    stars σ = (∑ g, tripleLocalStars (data.1 g)) +
        (Finset.univ.filter fun i => data.2 i = none).card ∧
      (∑ g, compatibleResidualQueryDeficit support σ 1 g) =
        ∑ g, tripleLocalDeficit (data.1 g) := by
  rw [ambientRestrictionTripleProductEquiv_apply]
  exact ⟨ambient_stars_eq_triple_sum_add_outside support hpair hcard σ,
    compatible_deficit_eq_triple_sum support hcard σ⟩

/-! ### Exact bivariate fibers on the product space -/

/-- Ambient restrictions with exactly `K` live coordinates and exactly `D` units of compatible
residual deficit.  These are the individual coefficients whose union over `D > trunkDepth` is
`compatibleDeficitShell` at residual depth one. -/
noncomputable def compatibleDeficitFiber {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (K D : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter fun σ =>
    stars σ = K ∧ (∑ g, compatibleResidualQueryDeficit support σ 1 g) = D

/-- The corresponding `(K,D)` fiber after splitting an ambient restriction into independent
width-three block states and its outside-coordinate state. -/
noncomputable def tripleProductWeightFiber {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (K D : ℕ) :
    Finset ((Fin G → (Fin 3 → Option Bool)) ×
      ({i : Fin n // i ∈ Finset.univ \ supportUnion support} → Option Bool)) :=
  Finset.univ.filter fun data =>
    (∑ g, tripleLocalStars (data.1 g)) +
        (Finset.univ.filter fun i => data.2 i = none).card = K ∧
      (∑ g, tripleLocalDeficit (data.1 g)) = D

theorem mem_compatibleDeficitFiber {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (K D : ℕ) (σ : Restriction n) :
    σ ∈ compatibleDeficitFiber support K D ↔
      stars σ = K ∧ (∑ g, compatibleResidualQueryDeficit support σ 1 g) = D := by
  simp [compatibleDeficitFiber]

theorem mem_tripleProductWeightFiber {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (K D : ℕ)
    (data : (Fin G → (Fin 3 → Option Bool)) ×
      ({i : Fin n // i ∈ Finset.univ \ supportUnion support} → Option Bool)) :
    data ∈ tripleProductWeightFiber support K D ↔
      (∑ g, tripleLocalStars (data.1 g)) +
          (Finset.univ.filter fun i => data.2 i = none).card = K ∧
        (∑ g, tripleLocalDeficit (data.1 g)) = D := by
  simp [tripleProductWeightFiber]

/-- The weight-preserving ambient product equivalence identifies every exact bivariate fiber.
This is the semantic coefficient theorem: no restrictions are lost or duplicated when the
`(K,D)` coefficient is computed on the product state space. -/
theorem compatibleDeficitFiber_card_eq_tripleProductWeightFiber_card {n G K D : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) :
    (compatibleDeficitFiber support K D).card =
      (tripleProductWeightFiber support K D).card := by
  classical
  let e := ambientRestrictionTripleProductEquiv support hpair hcard
  apply Finset.card_bij (fun σ _ => e σ)
  · intro σ hσ
    rw [mem_compatibleDeficitFiber] at hσ
    rw [mem_tripleProductWeightFiber]
    have hw := ambientRestrictionTripleProductEquiv_preserves_weights
      support hpair hcard σ
    change stars σ =
        (∑ g, tripleLocalStars ((e σ).1 g)) +
          (Finset.univ.filter fun i => (e σ).2 i = none).card ∧
      (∑ g, compatibleResidualQueryDeficit support σ 1 g) =
        ∑ g, tripleLocalDeficit ((e σ).1 g) at hw
    exact ⟨hw.1.symm.trans hσ.1, hw.2.symm.trans hσ.2⟩
  · intro σ hσ τ hτ heq
    exact e.injective heq
  · intro data hdata
    rw [mem_tripleProductWeightFiber] at hdata
    refine ⟨e.symm data, ?_, e.apply_symm_apply data⟩
    rw [mem_compatibleDeficitFiber]
    have hw := ambientRestrictionTripleProductEquiv_preserves_weights
      support hpair hcard (e.symm data)
    change stars (e.symm data) =
        (∑ g, tripleLocalStars ((e (e.symm data)).1 g)) +
          (Finset.univ.filter fun i => (e (e.symm data)).2 i = none).card ∧
      (∑ g, compatibleResidualQueryDeficit support (e.symm data) 1 g) =
        ∑ g, tripleLocalDeficit ((e (e.symm data)).1 g) at hw
    rw [e.apply_symm_apply] at hw
    exact ⟨hw.1.trans hdata.1, hw.2.trans hdata.2⟩

/-! ### Algebraic factorization of the product enumerator -/

/-- Bivariate polynomials with natural-number coefficients.  Coordinate `0` records the live
count (`z`) and coordinate `1` records the compatible deficit (`y`). -/
abbrev BivariateEnumerator := MvPolynomial (Fin 2) ℕ

/-- The monomial `z^K y^D` used to record one weighted state. -/
noncomputable def bivariateWeightMonomial (K D : ℕ) : BivariateEnumerator :=
  MvPolynomial.monomial (Finsupp.single 0 K + Finsupp.single 1 D) 1

theorem bivariateWeightMonomial_eq (K D : ℕ) :
    bivariateWeightMonomial K D = MvPolynomial.X 0 ^ K * MvPolynomial.X 1 ^ D := by
  rw [bivariateWeightMonomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]
  simp

theorem bivariateWeightMonomial_mul (K₁ D₁ K₂ D₂ : ℕ) :
    bivariateWeightMonomial K₁ D₁ * bivariateWeightMonomial K₂ D₂ =
      bivariateWeightMonomial (K₁ + K₂) (D₁ + D₂) := by
  simp only [bivariateWeightMonomial, MvPolynomial.monomial_mul, one_mul]
  apply congrArg (fun s : Fin 2 →₀ ℕ => MvPolynomial.monomial s 1)
  ext i
  fin_cases i <;> simp [add_assoc, add_comm, add_left_comm]

theorem prod_bivariateWeightMonomial {α : Type} [DecidableEq α]
    (s : Finset α) (K D : α → ℕ) :
    ∏ i ∈ s, bivariateWeightMonomial (K i) (D i) =
      bivariateWeightMonomial (∑ i ∈ s, K i) (∑ i ∈ s, D i) := by
  induction s using Finset.induction_on with
  | empty => simp [bivariateWeightMonomial]
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      exact bivariateWeightMonomial_mul _ _ _ _

theorem bivariateWeightExponent_eq_iff (K₁ D₁ K₂ D₂ : ℕ) :
    Finsupp.single (0 : Fin 2) K₁ + Finsupp.single (1 : Fin 2) D₁ =
        Finsupp.single 0 K₂ + Finsupp.single 1 D₂ ↔
      K₁ = K₂ ∧ D₁ = D₂ := by
  constructor
  · intro h
    constructor
    · simpa using congrArg (fun s : Fin 2 →₀ ℕ => s 0) h
    · simpa using congrArg (fun s : Fin 2 →₀ ℕ => s 1) h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem bivariateSplitWeightExponent_eq_iff (K₁ K₂ D₁ K D : ℕ) :
    (Finsupp.single (0 : Fin 2) K₁ + Finsupp.single 0 K₂) +
        Finsupp.single (1 : Fin 2) D₁ =
        Finsupp.single 0 K + Finsupp.single 1 D ↔
      K₁ + K₂ = K ∧ D₁ = D := by
  constructor
  · intro h
    constructor
    · simpa using congrArg (fun s : Fin 2 →₀ ℕ => s 0) h
    · simpa using congrArg (fun s : Fin 2 →₀ ℕ => s 1) h
  · rintro ⟨hK, hD⟩
    ext i
    fin_cases i <;> simp [hK, hD]

/-- The polynomial inventory of all 27 abstract states of one support triple. -/
noncomputable def tripleLocalEnumerator : BivariateEnumerator :=
  ∑ rho : Fin 3 → Option Bool,
    bivariateWeightMonomial (tripleLocalStars rho) (tripleLocalDeficit rho)

/-- The five checked local fibers give the advertised width-three bivariate factor exactly. -/
theorem tripleLocalEnumerator_eq :
    tripleLocalEnumerator =
      8 + 12 * MvPolynomial.X 0 + 3 * MvPolynomial.X 0 ^ 2 +
        3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 +
          MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 2 := by
  classical
  unfold tripleLocalEnumerator
  rw [show (Finset.univ : Finset (Fin 3 → Option Bool)) =
      tripleLocalFiber 0 0 ∪ tripleLocalFiber 1 0 ∪ tripleLocalFiber 2 0 ∪
        tripleLocalFiber 2 1 ∪ tripleLocalFiber 3 2 from tripleLocalFibers_exhaustive]
  have hf (K D : ℕ) :
      ∑ rho ∈ tripleLocalFiber K D,
          bivariateWeightMonomial (tripleLocalStars rho) (tripleLocalDeficit rho) =
        (tripleLocalFiber K D).card • bivariateWeightMonomial K D := by
    apply Finset.sum_eq_card_nsmul
    intro rho hrho
    simp only [tripleLocalFiber, Finset.mem_filter] at hrho
    rw [hrho.2.1, hrho.2.2]
  rw [Finset.sum_union (by decide), Finset.sum_union (by decide),
    Finset.sum_union (by decide), Finset.sum_union (by decide)]
  simp only [hf, tripleLocalFiber_card_zero_zero, tripleLocalFiber_card_one_zero,
    tripleLocalFiber_card_two_zero, tripleLocalFiber_card_two_one,
    tripleLocalFiber_card_three_two, nsmul_eq_mul]
  simp [bivariateWeightMonomial_eq]
  ring

/-- The multiplicative weight enumerator of `G` independent triple states and a canonically
reindexed reservoir of `outsideCount` outside states.  Writing each state's weight as a product
makes independence explicit; coefficient extraction will next identify its `z^K y^D` coefficient
with `tripleProductWeightFiber` after reindexing the outside subtype by its cardinality. -/
noncomputable def tripleProductEnumerator (G outsideCount : ℕ) : BivariateEnumerator :=
  ∑ data : (Fin G → (Fin 3 → Option Bool)) × (Fin outsideCount → Option Bool),
    (∏ g, bivariateWeightMonomial
      (tripleLocalStars (data.1 g)) (tripleLocalDeficit (data.1 g))) *
      ∏ i, bivariateWeightMonomial (if data.2 i = none then 1 else 0) 0

/-- The exact `(K,D)` fiber on the canonically indexed product space used by
`tripleProductEnumerator`. -/
noncomputable def tripleProductIndexWeightFiber (G outsideCount K D : ℕ) :
    Finset ((Fin G → (Fin 3 → Option Bool)) × (Fin outsideCount → Option Bool)) :=
  Finset.univ.filter fun data =>
    (∑ g, tripleLocalStars (data.1 g)) +
        (Finset.univ.filter fun i => data.2 i = none).card = K ∧
      (∑ g, tripleLocalDeficit (data.1 g)) = D

theorem tripleProductEnumerator_summand_eq {G outsideCount : ℕ}
    (data : (Fin G → (Fin 3 → Option Bool)) × (Fin outsideCount → Option Bool)) :
    (∏ g, bivariateWeightMonomial
        (tripleLocalStars (data.1 g)) (tripleLocalDeficit (data.1 g))) *
      ∏ i, bivariateWeightMonomial (if data.2 i = none then 1 else 0) 0 =
    bivariateWeightMonomial
      ((∑ g, tripleLocalStars (data.1 g)) +
        (Finset.univ.filter fun i => data.2 i = none).card)
      (∑ g, tripleLocalDeficit (data.1 g)) := by
  classical
  rw [show (∏ g, bivariateWeightMonomial
        (tripleLocalStars (data.1 g)) (tripleLocalDeficit (data.1 g))) =
      bivariateWeightMonomial (∑ g, tripleLocalStars (data.1 g))
        (∑ g, tripleLocalDeficit (data.1 g)) by
        simpa using prod_bivariateWeightMonomial Finset.univ
          (fun g => tripleLocalStars (data.1 g))
          (fun g => tripleLocalDeficit (data.1 g))]
  rw [show (∏ i, bivariateWeightMonomial (if data.2 i = none then 1 else 0) 0) =
      bivariateWeightMonomial
        (Finset.univ.filter fun i => data.2 i = none).card 0 by
        rw [prod_bivariateWeightMonomial Finset.univ]
        congr 2
        · simp
        · simp]
  simpa using bivariateWeightMonomial_mul
    (∑ g, tripleLocalStars (data.1 g))
    (∑ g, tripleLocalDeficit (data.1 g))
    (Finset.univ.filter fun i => data.2 i = none).card 0

/-- Coefficient extraction on the canonically indexed product space counts exactly the states
with the requested live and deficit weights. -/
theorem tripleProductEnumerator_coeff (G outsideCount K D : ℕ) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 2) K + Finsupp.single (1 : Fin 2) D)
        (tripleProductEnumerator G outsideCount) =
      (tripleProductIndexWeightFiber G outsideCount K D).card := by
  classical
  unfold tripleProductEnumerator tripleProductIndexWeightFiber
  simp_rw [tripleProductEnumerator_summand_eq]
  simp only [MvPolynomial.coeff_sum, bivariateWeightMonomial,
    MvPolynomial.coeff_monomial]
  simp [bivariateSplitWeightExponent_eq_iff]

theorem filter_card_comp_equiv {α β γ : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → γ) (p : γ → Prop) [DecidablePred p] :
    (Finset.univ.filter fun a => p (f a)).card =
      (Finset.univ.filter fun b => p (f (e.symm b))).card := by
  classical
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    simpa using ha
  · intro a ha b hb hab
    exact e.injective hab
  · intro b hb
    exact ⟨e.symm b, by simpa using hb, e.apply_symm_apply b⟩

/-- Reindexing the ambient outside subtype by its exact cardinality identifies its weight fiber
with the canonical `Fin (n-3*G)` fiber used in the algebraic enumerator. -/
theorem tripleProductWeightFiber_card_eq_indexWeightFiber_card {n G K D : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) :
    (tripleProductWeightFiber support K D).card =
      (tripleProductIndexWeightFiber G (n - 3 * G) K D).card := by
  classical
  have houtside : (Finset.univ \ supportUnion support).card = n - 3 * G := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, supportUnion_card_of_pairwiseDisjoint_uniform support hpair hcard]
    omega
  let e : {i : Fin n // i ∈ Finset.univ \ supportUnion support} ≃
      Fin (n - 3 * G) := (Finset.orderIsoOfFin _ houtside).symm.toEquiv
  apply Finset.card_bij (fun data _ => (data.1, fun i => data.2 (e.symm i)))
  · intro data hdata
    rw [mem_tripleProductWeightFiber] at hdata
    simp only [tripleProductIndexWeightFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    have hout := filter_card_comp_equiv e data.2 (fun x => x = none)
    exact ⟨by simpa only using (congrArg
        (fun q => (∑ g, tripleLocalStars (data.1 g)) + q) hout).symm.trans hdata.1,
      hdata.2⟩
  · intro data hdata data' hdata' heq
    cases data with
    | mk x y =>
      cases data' with
      | mk x' y' =>
        simp only [Prod.mk.injEq] at heq ⊢
        refine ⟨heq.1, ?_⟩
        funext i
        simpa using congrFun heq.2 (e i)
  · intro data hdata
    refine ⟨(data.1, fun i => data.2 (e i)), ?_, ?_⟩
    · rw [mem_tripleProductWeightFiber]
      simp only [tripleProductIndexWeightFiber, Finset.mem_filter, Finset.mem_univ, true_and]
        at hdata
      have hout := filter_card_comp_equiv e (fun i => data.2 (e i)) (fun x => x = none)
      simp only [e.apply_symm_apply] at hout
      exact ⟨by simpa only using (congrArg
          (fun q => (∑ g, tripleLocalStars (data.1 g)) + q) hout).trans hdata.1,
        hdata.2⟩
    · apply Prod.ext
      · rfl
      · funext i
        simp

/-- The advertised coefficient theorem: the `z^K y^D` coefficient of the factored canonical
enumerator is exactly the cardinality of the semantic product fiber for any disjoint family of
three-element supports. -/
theorem tripleProductEnumerator_coeff_eq_weightFiber_card {n G K D : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 2) K + Finsupp.single (1 : Fin 2) D)
        (tripleProductEnumerator G (n - 3 * G)) =
      (tripleProductWeightFiber support K D).card := by
  rw [tripleProductEnumerator_coeff,
    tripleProductWeightFiber_card_eq_indexWeightFiber_card support hpair hcard]

/-- End-to-end exact coefficient extraction back on ambient restrictions. -/
theorem tripleProductEnumerator_coeff_eq_compatibleDeficitFiber_card {n G K D : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 2) K + Finsupp.single (1 : Fin 2) D)
        (tripleProductEnumerator G (n - 3 * G)) =
      (compatibleDeficitFiber support K D).card := by
  rw [tripleProductEnumerator_coeff_eq_weightFiber_card support hpair hcard,
    compatibleDeficitFiber_card_eq_tripleProductWeightFiber_card support hpair hcard]

/-! ### Finite coefficient tails -/

/-- A width-three block contributes at most two units in the deficit grading. -/
theorem tripleLocalDeficit_le_two (rho : Fin 3 → Option Bool) :
    tripleLocalDeficit rho ≤ 2 := by
  classical
  unfold tripleLocalDeficit
  split
  · have hstars : tripleLocalStars rho ≤ 3 := by
      unfold tripleLocalStars
      calc
        (Finset.univ.filter fun i => rho i = none).card ≤ Finset.univ.card :=
          Finset.card_filter_le _ _
        _ = 3 := by simp
    omega
  · omega

/-- The finite set of deficit degrees strictly above the trunk budget.  The upper endpoint `2*G`
is exact for `G` independent width-three blocks and makes the coefficient tail manifestly finite. -/
def compatibleDeficitTailIndices (G trunkDepth : ℕ) : Finset ℕ :=
  (Finset.range (2 * G + 1)).filter fun D => trunkDepth < D

theorem mem_compatibleDeficitTailIndices {G trunkDepth D : ℕ} :
    D ∈ compatibleDeficitTailIndices G trunkDepth ↔ trunkDepth < D ∧ D ≤ 2 * G := by
  simp [compatibleDeficitTailIndices]
  omega

/-- On disjoint width-three supports, the total compatible deficit has no mass above degree
`2*G`. -/
theorem compatible_deficit_sum_le_two_mul {n G : ℕ}
    (support : Fin G → Finset (Fin n)) (σ : Restriction n)
    (hcard : ∀ g, (support g).card = 3) :
    (∑ g, compatibleResidualQueryDeficit support σ 1 g) ≤ 2 * G := by
  rw [compatible_deficit_eq_triple_sum support hcard σ]
  calc
    (∑ g, tripleLocalDeficit (ambientTripleState support hcard σ g)) ≤
        ∑ _g : Fin G, 2 :=
      Finset.sum_le_sum fun g _ => tripleLocalDeficit_le_two _
    _ = 2 * G := by simp [Nat.mul_comm]

/-- Exact finite deficit-tail extraction on the semantic restriction shell.  Fiberwise counting
partitions the shell by its unique deficit degree, and the width-three local bound cuts the sum off
at `2*G`. -/
theorem compatibleDeficitShell_card_eq_sum_fibers {n G K trunkDepth : ℕ}
    (support : Fin G → Finset (Fin n))
    (hcard : ∀ g, (support g).card = 3) :
    (compatibleDeficitShell support K trunkDepth 1).card =
      ∑ D ∈ compatibleDeficitTailIndices G trunkDepth,
        (compatibleDeficitFiber support K D).card := by
  classical
  let deficit : Restriction n → ℕ := fun σ =>
    ∑ g, compatibleResidualQueryDeficit support σ 1 g
  rw [Finset.card_eq_sum_card_fiberwise
    (f := deficit) (t := compatibleDeficitTailIndices G trunkDepth)]
  · apply Finset.sum_congr rfl
    intro D hD
    congr 1
    ext σ
    rw [Finset.mem_filter, mem_compatibleDeficitFiber]
    simp only [compatibleDeficitShell, Finset.mem_filter, Finset.mem_univ, true_and]
    have htail := (mem_compatibleDeficitTailIndices.mp hD).1
    change (stars σ = K ∧ trunkDepth < deficit σ) ∧ deficit σ = D ↔
      stars σ = K ∧ deficit σ = D
    omega
  · intro σ hσ
    change deficit σ ∈ compatibleDeficitTailIndices G trunkDepth
    rw [mem_compatibleDeficitTailIndices]
    have hshell := (Finset.mem_filter.mp hσ).2
    exact ⟨hshell.2, compatible_deficit_sum_le_two_mul support σ hcard⟩

/-- The exact shell mass is the finite coefficient tail of the factored bivariate enumerator. -/
theorem compatibleDeficitShell_card_eq_coefficient_tail {n G K trunkDepth : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) :
    (compatibleDeficitShell support K trunkDepth 1).card =
      ∑ D ∈ compatibleDeficitTailIndices G trunkDepth,
        MvPolynomial.coeff
          (Finsupp.single (0 : Fin 2) K + Finsupp.single (1 : Fin 2) D)
          (tripleProductEnumerator G (n - 3 * G)) := by
  rw [compatibleDeficitShell_card_eq_sum_fibers support hcard]
  apply Finset.sum_congr rfl
  intro D _hD
  exact (tripleProductEnumerator_coeff_eq_compatibleDeficitFiber_card
    support hpair hcard).symm

/-- The first parameter specialization requested by the frontier audit: at `K = 20*r`, the
semantic event with deficit above `10*r` is exactly the corresponding finite coefficient tail. -/
theorem compatibleDeficitShell_twenty_card_eq_coefficient_tail {n G r : ℕ}
    (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) :
    (compatibleDeficitShell support (20 * r) (10 * r) 1).card =
      ∑ D ∈ compatibleDeficitTailIndices G (10 * r),
        MvPolynomial.coeff
          (Finsupp.single (0 : Fin 2) (20 * r) + Finsupp.single (1 : Fin 2) D)
          (tripleProductEnumerator G (n - 3 * G)) :=
  compatibleDeficitShell_card_eq_coefficient_tail support hpair hcard

/-- A finite reservoir of independent outside coordinates contributes one `2 + z` factor per
coordinate.  Keeping this lemma polymorphic avoids exposing a large support-subtype expression to
the finite-product elaborator in the main factorization proof. -/
theorem outsideStateEnumerator_eq (α : Type) [Fintype α] [DecidableEq α] :
    (∑ y : α → Option Bool,
      ∏ i, bivariateWeightMonomial (if y i = none then 1 else 0) 0) =
        (2 + MvPolynomial.X 0) ^ Fintype.card α := by
  classical
  have hlocal :
      (∑ x : Option Bool,
        bivariateWeightMonomial (if x = none then 1 else 0) 0) =
          2 + MvPolynomial.X 0 := by
    simp [bivariateWeightMonomial_eq]
    ring
  calc
    (∑ y : α → Option Bool,
        ∏ i, bivariateWeightMonomial (if y i = none then 1 else 0) 0) =
        ∏ _i : α, ∑ x : Option Bool,
          bivariateWeightMonomial (if x = none then 1 else 0) 0 :=
      (Fintype.prod_sum (fun (_i : α) (x : Option Bool) =>
        bivariateWeightMonomial (if x = none then 1 else 0) 0)).symm
    _ = _ := by
      rw [show (∑ x : Option Bool,
          bivariateWeightMonomial (if x = none then 1 else 0) 0) =
            2 + MvPolynomial.X 0 from hlocal]
      simp only [Finset.prod_const, Finset.card_univ]

/-- Exact algebraic factorization of the product-space enumerator for the outside cardinality
forced by `G` disjoint triples in `n` coordinates.  Every triple contributes the verified
five-term local polynomial, and every outside coordinate contributes `2 + z` (two fixed values or
one live value). -/
theorem tripleProductEnumerator_factorization (n G : ℕ) :
    tripleProductEnumerator G (n - 3 * G) =
      (8 + 12 * MvPolynomial.X 0 + 3 * MvPolynomial.X 0 ^ 2 +
        3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 +
          MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 2) ^ G *
        (2 + MvPolynomial.X 0) ^ (n - 3 * G) := by
  classical
  unfold tripleProductEnumerator
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  have hfactor :
      (∑ x : Fin G → (Fin 3 → Option Bool),
        (∏ g, bivariateWeightMonomial
          (tripleLocalStars (x g)) (tripleLocalDeficit (x g))) *
          (∑ y : Fin (n - 3 * G) → Option Bool,
            ∏ i, bivariateWeightMonomial (if y i = none then 1 else 0) 0)) =
        (∑ x : Fin G → (Fin 3 → Option Bool),
          ∏ g, bivariateWeightMonomial
            (tripleLocalStars (x g)) (tripleLocalDeficit (x g))) *
          (∑ y : Fin (n - 3 * G) → Option Bool,
            ∏ i, bivariateWeightMonomial (if y i = none then 1 else 0) 0) := by
    exact (Finset.sum_mul Finset.univ _ _).symm
  rw [hfactor]
  congr 1
  · calc
      (∑ x : Fin G → (Fin 3 → Option Bool),
          ∏ g, bivariateWeightMonomial
            (tripleLocalStars (x g)) (tripleLocalDeficit (x g))) =
          ∏ _g : Fin G, tripleLocalEnumerator := by
        rw [tripleLocalEnumerator]
        exact (Fintype.prod_sum (fun (_g : Fin G) (rho : Fin 3 → Option Bool) =>
          bivariateWeightMonomial
            (tripleLocalStars rho) (tripleLocalDeficit rho))).symm
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          tripleLocalEnumerator_eq]
  · calc
      (∑ y : Fin (n - 3 * G) → Option Bool,
          ∏ i, bivariateWeightMonomial (if y i = none then 1 else 0) 0) =
          (2 + MvPolynomial.X 0) ^ Fintype.card (Fin (n - 3 * G)) :=
        outsideStateEnumerator_eq (Fin (n - 3 * G))
      _ = _ := by
        simp only [Fintype.card_fin]

/-- A completely live width-three support contributes exactly two units to the compatible
residual query deficit at residual depth one.  In particular, fixed-value compatibility costs
nothing on this subevent: every support coordinate is free. -/
theorem compatibleResidualQueryDeficit_eq_two_of_intact_triple
    {n G : ℕ} (support : Fin G → Finset (Fin n)) (σ : Restriction n) (g : Fin G)
    (hcard : (support g).card = 3) (hintact : g ∈ intactSupportBlocks support σ) :
    compatibleResidualQueryDeficit support σ 1 g = 2 := by
  have hsub : support g ⊆ freeVars σ := (Finset.mem_filter.mp hintact).2
  have hcompat : supportTrueCompatible support σ g := by
    intro i hi hfalse
    have hfree : σ i = none := mem_freeVars.mp (hsub hi)
    rw [hfree] at hfalse
    simp at hfalse
  simp [compatibleResidualQueryDeficit, hcompat, residualQueryDeficit, liveSupport,
    Finset.inter_eq_left.mpr hsub, hcard]

/-- The older whole-block event gives a rigorous lower-bound subevent for the weighted width-three
shell.  More than `5*r` intact triples contribute more than `10*r` total compatible deficit.
Partially live truth-compatible triples may enlarge the target event, but are not needed for this
inclusion. -/
theorem manyIntactShell_subset_compatibleDeficitShell_triples
    {n G r : ℕ} (support : Fin G → Finset (Fin n))
    (hcard : ∀ g, (support g).card = 3) :
    manyIntactShell support (20 * r) (5 * r) ⊆
      compatibleDeficitShell support (20 * r) (10 * r) 1 := by
  intro σ hσ
  have hmem := (Finset.mem_filter.mp hσ).2
  rw [compatibleDeficitShell, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hmem.1, ?_⟩
  have hpartial :
      (∑ g ∈ intactSupportBlocks support σ,
          compatibleResidualQueryDeficit support σ 1 g) ≤
        ∑ g, compatibleResidualQueryDeficit support σ 1 g :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)
  have heq :
      (∑ g ∈ intactSupportBlocks support σ,
          compatibleResidualQueryDeficit support σ 1 g) =
        2 * (intactSupportBlocks support σ).card := by
    calc
      _ = ∑ _g ∈ intactSupportBlocks support σ, 2 := by
        apply Finset.sum_congr rfl
        intro g hg
        exact compatibleResidualQueryDeficit_eq_two_of_intact_triple
          support σ g (hcard g) hg
      _ = 2 * (intactSupportBlocks support σ).card := by simp [Nat.mul_comm]
  rw [heq] at hpartial
  omega

/-- Cardinal form of the intact-triple lower bound.  The left side already has the exact
occupancy-sum enumeration and the uniform fixed-value factor proved above. -/
theorem manyIntactShell_card_le_compatibleDeficitShell_triples
    {n G r : ℕ} (support : Fin G → Finset (Fin n))
    (hcard : ∀ g, (support g).card = 3) :
    (manyIntactShell support (20 * r) (5 * r)).card ≤
      (compatibleDeficitShell support (20 * r) (10 * r) 1).card :=
  Finset.card_le_card
    (manyIntactShell_subset_compatibleDeficitShell_triples support hcard)

/-- Explicit stars-and-bars lower bound for the weighted triple event.  It is the exact occupancy
sum for more than `5*r` fully live triples, including the common `2^(n-20*r)` fixed-value factor.
The full compatible event can additionally contain deficit-one partially live triples. -/
theorem compatibleDeficitShell_triples_occupancy_lower_bound
    {n G r : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hcard : ∀ g, (support g).card = 3) :
    (∑ p ∈ admissibleOccupancyIndices support (20 * r) (5 * r),
        (∏ g, (support g).card.choose (p.1 g).val) *
          ((Finset.univ \ supportUnion support).card.choose p.2.val)) *
        2 ^ (n - 20 * r) ≤
      (compatibleDeficitShell support (20 * r) (10 * r) 1).card := by
  rw [← manyIntactFreeSets_card_eq_sum_occupancy support hpair,
    ← manyIntactShell_card]
  exact manyIntactShell_card_le_compatibleDeficitShell_triples support hcard

/-- If the sum of the blockwise live-coordinate deficits exceeds the number of distinct queried
coordinates, some block retains more than `residualDepth` root-live coordinates outside the
query path.  Pairwise disjointness is exactly what prevents one query from paying two deficits.

This is the weighted replacement for the earlier whole-block pigeonhole argument.  It is purely
combinatorial: the semantic use for conjunction gates must additionally exclude a root-fixed
false literal, since such a literal makes the gate constant regardless of its live deficit. -/
theorem exists_liveSupport_sdiff_card_gt_of_sum_deficit
    {n G residualDepth : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (σ : Restriction n) (path : Finset (Fin n))
    (hdeficit : path.card < ∑ g, residualQueryDeficit support σ residualDepth g) :
    ∃ g, residualDepth < ((liveSupport support σ g) \ path).card := by
  by_contra hnone
  push_neg at hnone
  have hpoint (g : Fin G) :
      residualQueryDeficit support σ residualDepth g ≤
        ((liveSupport support σ g) ∩ path).card := by
    have hsplit := Finset.card_sdiff_add_card_inter
      (liveSupport support σ g) path
    have hremain := hnone g
    simp only [residualQueryDeficit]
    apply Nat.sub_le_iff_le_add.mpr
    omega
  have hhits :
      (∑ g, ((liveSupport support σ g) ∩ path).card) ≤ path.card := by
    have hdisj : ((Finset.univ : Finset (Fin G)) : Set (Fin G)).PairwiseDisjoint
        (fun g => (liveSupport support σ g) ∩ path) := by
      intro g _ h _ hne
      apply (hpair g h hne).mono
      · intro i hi
        exact (Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1
      · intro i hi
        exact (Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1
    calc
      (∑ g, ((liveSupport support σ g) ∩ path).card) =
          (Finset.univ.biUnion fun g => (liveSupport support σ g) ∩ path).card :=
        (Finset.card_biUnion hdisj).symm
      _ ≤ path.card := Finset.card_le_card <| by
        intro i hi
        rw [Finset.mem_biUnion] at hi
        obtain ⟨g, _, hig⟩ := hi
        exact (Finset.mem_inter.mp hig).2
  have hsum :
      (∑ g, residualQueryDeficit support σ residualDepth g) ≤
        ∑ g, ((liveSupport support σ g) ∩ path).card :=
    Finset.sum_le_sum fun g _ => hpoint g
  exact (Nat.not_lt_of_ge (hsum.trans hhits)) hdeficit

/-- Sound weighted pigeonhole principle for positive conjunctions: if compatible deficits exceed
the path budget, one compatible block retains too many live unqueried coordinates. -/
theorem exists_compatible_liveSupport_sdiff_card_gt_of_sum_deficit
    {n G residualDepth : ℕ} (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (σ : Restriction n) (path : Finset (Fin n))
    (hdeficit : path.card <
      ∑ g, compatibleResidualQueryDeficit support σ residualDepth g) :
    ∃ g, supportTrueCompatible support σ g ∧
      residualDepth < ((liveSupport support σ g) \ path).card := by
  classical
  let eligible : Fin G → Finset (Fin n) := fun g =>
    if supportTrueCompatible support σ g then support g else ∅
  have heligiblePair : ∀ g h, g ≠ h → Disjoint (eligible g) (eligible h) := by
    intro g h hne
    by_cases hg : supportTrueCompatible support σ g <;>
      by_cases hh : supportTrueCompatible support σ h <;>
      simp [eligible, hg, hh, hpair g h hne]
  have hsum :
      (∑ g, residualQueryDeficit eligible σ residualDepth g) =
        ∑ g, compatibleResidualQueryDeficit support σ residualDepth g := by
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : supportTrueCompatible support σ g <;>
      simp [eligible, compatibleResidualQueryDeficit, residualQueryDeficit, liveSupport, hg]
  obtain ⟨g, hg⟩ := exists_liveSupport_sdiff_card_gt_of_sum_deficit
    eligible heligiblePair σ path (by rw [hsum]; exact hdeficit)
  have hcompat : supportTrueCompatible support σ g := by
    by_contra hnot
    simp [eligible, liveSupport, hnot] at hg
  refine ⟨g, hcompat, ?_⟩
  simpa [eligible, liveSupport, hcompat] using hg

/-- Semantic lift of the compatible weighted deficit.  Follow the assignment which sets every
root-live coordinate to true.  A depth-`trunkDepth` common trunk has at most that many distinct
queries on this path, so an excess compatible deficit leaves more than `residualDepth` live
coordinates of one block unqueried.  Toggling each such coordinate shows that it remains free at
the reached leaf; truth compatibility and leaf agreement show that no coordinate of the selected
support is fixed false there.

The final premise is deliberately local and gate-specific.  For ordered positive conjunctions it
is exactly the remaining canonical-depth lemma: more than `residualDepth` free support
coordinates, with no support coordinate false, force depth greater than `residualDepth`. -/
theorem supportedGates_not_commonShallowAt_of_compatible_sum_deficit
    {n G fuel trunkDepth residualDepth : ℕ}
    (gates : Fin G → List (Clause n)) (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (σ : Restriction n)
    (hdeficit : trunkDepth <
      ∑ g, compatibleResidualQueryDeficit support σ residualDepth g)
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i ≠ some false) →
      residualDepth < (support g ∩ freeVars rho).card →
      residualDepth < (canonicalDT (gates g) fuel rho).depth) :
    ¬ CommonShallowAt gates fuel σ trunkDepth residualDepth := by
  rintro ⟨trunk, htrunkDepth, hleaf⟩
  let x : Fin n → Bool := fun i => (σ i).getD true
  have hx : Rung4Restriction.Extends σ x := by
    intro i b hi
    simp [x, hi]
  let path : Finset (Fin n) := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ trunkDepth := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ trunkDepth := htrunkDepth
  obtain ⟨g, hcompat, hremain⟩ :=
    exists_compatible_liveSupport_sdiff_card_gt_of_sum_deficit
      support hpair σ path (lt_of_le_of_lt hpathCard hdeficit)
  have hfree (i : Fin n) (hiσ : σ i = none) (hi : i ∉ path) :
      CommonTree.run trunk x i = none := by
    let y : Fin n → Bool := Function.update x i (!x i)
    have hy : Rung4Restriction.Extends σ y := by
      intro j b hj
      have hji : j ≠ i := by
        intro h
        subst j
        rw [hiσ] at hj
        simp at hj
      simpa [y, Function.update_of_ne hji] using hx j b hj
    obtain ⟨_, htx, _⟩ := hleaf x hx
    obtain ⟨_, hty, _⟩ := hleaf y hy
    have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
      exact CommonTree.run_update_of_not_mem_queryVars trunk x i
        (by simpa [path] using hi)
    cases ht : CommonTree.run trunk x i with
    | none => rfl
    | some b =>
        have hbx : x i = b := htx i b ht
        have hby : y i = b := by
          apply hty i b
          simpa [hrun] using ht
        cases hxi : x i with
        | false =>
            have hbfalse : b = false := by simpa [hxi] using hbx.symm
            have hbtrue : b = true := by simpa [y, hxi] using hby.symm
            exact False.elim (Bool.false_ne_true (hbfalse.symm.trans hbtrue))
        | true =>
            have hbtrue : b = true := by simpa [hxi] using hbx.symm
            have hbfalse : b = false := by simpa [y, hxi] using hby.symm
            exact False.elim (Bool.false_ne_true (hbfalse.symm.trans hbtrue))
  obtain ⟨_, hagree, hshallow⟩ := hleaf x hx
  have hsupportNotFalse (i : Fin n) (hi : i ∈ support g) :
      CommonTree.run trunk x i ≠ some false := by
    intro hfalse
    have hxi : x i = false := hagree i false hfalse
    cases hσi : σ i with
    | none => simp [x, hσi] at hxi
    | some b =>
        cases b
        · exact hcompat i hi hσi
        · simp [x, hσi] at hxi
  have hremainingSubset : (liveSupport support σ g \ path) ⊆
      support g ∩ freeVars (CommonTree.run trunk x) := by
    intro i hi
    have hilive := (Finset.mem_sdiff.mp hi).1
    have hipath := (Finset.mem_sdiff.mp hi).2
    have hisupport := (Finset.mem_inter.mp hilive).1
    have hiσ := mem_freeVars.mp (Finset.mem_inter.mp hilive).2
    exact Finset.mem_inter.mpr ⟨hisupport, mem_freeVars.mpr (hfree i hiσ hipath)⟩
  have hfreeCard : residualDepth <
      (support g ∩ freeVars (CommonTree.run trunk x)).card :=
    lt_of_lt_of_le hremain (Finset.card_le_card hremainingSubset)
  have hgateDeep : residualDepth <
      (canonicalDT (gates g) fuel (CommonTree.run trunk x)).depth :=
    hdeep (CommonTree.run trunk x) g hsupportNotFalse hfreeCard
  exact (Nat.not_lt_of_ge (hshallow g)) hgateDeep

/-- Fixed-shell form of the weighted semantic lift. -/
theorem mem_commonShallowBad_of_compatible_sum_deficit
    {n G fuel K trunkDepth residualDepth : ℕ}
    (gates : Fin G → List (Clause n)) (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (σ : Restriction n) (hstars : stars σ = K)
    (hdeficit : trunkDepth <
      ∑ g, compatibleResidualQueryDeficit support σ residualDepth g)
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i ≠ some false) →
      residualDepth < (support g ∩ freeVars rho).card →
      residualDepth < (canonicalDT (gates g) fuel rho).depth) :
    σ ∈ commonShallowBad gates fuel K trunkDepth residualDepth := by
  rw [mem_commonShallowBad]
  exact ⟨hstars,
    supportedGates_not_commonShallowAt_of_compatible_sum_deficit
      gates support hpair σ hdeficit hdeep⟩

/-- Once the local canonical-depth premise is available, the entire compatible weighted shell
event embeds in semantic common-shallow badness.  This is the set-level interface needed by the
remaining width-three counting problem. -/
theorem compatibleDeficitShell_subset_commonShallowBad
    {n G fuel K trunkDepth residualDepth : ℕ}
    (gates : Fin G → List (Clause n)) (support : Fin G → Finset (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (support g) (support h))
    (hdeep : ∀ (rho : Restriction n) (g : Fin G),
      (∀ i ∈ support g, rho i ≠ some false) →
      residualDepth < (support g ∩ freeVars rho).card →
      residualDepth < (canonicalDT (gates g) fuel rho).depth) :
    compatibleDeficitShell support K trunkDepth residualDepth ⊆
      commonShallowBad gates fuel K trunkDepth residualDepth := by
  intro σ hσ
  have hmem := (Finset.mem_filter.mp hσ).2
  exact mem_commonShallowBad_of_compatible_sum_deficit
    gates support hpair σ hmem.1 hmem.2 hdeep

/-- The compatible weighted shell has unconditional semantic badness for pairwise-disjoint
ordered positive conjunctions when the canonical tree receives ambient fuel `n`.  The ambient
fuel bound is sufficient for every restriction, and
`orderedConjunctionBlock_freeSupport_card_le_depth` discharges the gate-local premise of the
generic weighted lift. -/
theorem compatibleDeficitShell_subset_commonShallowBad_of_orderedConjunctionBlocks
    {n G K trunkDepth residualDepth : ℕ}
    (blocks : Fin G → List (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (blocks g).toFinset (blocks h).toFinset) :
    compatibleDeficitShell (fun g => (blocks g).toFinset) K trunkDepth residualDepth ⊆
      commonShallowBad (fun g => orderedConjunctionBlock (blocks g)) n K
        trunkDepth residualDepth := by
  apply compatibleDeficitShell_subset_commonShallowBad
    (fun g => orderedConjunctionBlock (blocks g)) (fun g => (blocks g).toFinset) hpair
  intro rho g hnotFalse hfree
  have hfuel : stars rho ≤ n := by
    exact le_trans (Finset.card_le_univ (freeVars rho)) (by simp)
  exact lt_of_lt_of_le hfree
    (orderedConjunctionBlock_freeSupport_card_le_depth (blocks g) rho hfuel <| by
      intro i hi
      exact hnotFalse i (List.mem_toFinset.mpr hi))

/-- The exact intact-triple occupancy subevent is already semantic common-shallow badness for
disjoint ordered conjunctions.  This composes the quantitative lower-bound interface with the
assumption-free ordered-conjunction depth theorem. -/
theorem manyIntactShell_card_le_commonShallowBad_of_orderedTriples
    {n G r : ℕ} (blocks : Fin G → List (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (blocks g).toFinset (blocks h).toFinset)
    (hcard : ∀ g, (blocks g).toFinset.card = 3) :
    (manyIntactShell (fun g => (blocks g).toFinset) (20 * r) (5 * r)).card ≤
      (commonShallowBad (fun g => orderedConjunctionBlock (blocks g)) n
        (20 * r) (10 * r) 1).card := by
  calc
    _ ≤ (compatibleDeficitShell (fun g => (blocks g).toFinset)
        (20 * r) (10 * r) 1).card :=
      manyIntactShell_card_le_compatibleDeficitShell_triples
        (fun g => (blocks g).toFinset) hcard
    _ ≤ _ := Finset.card_le_card
      (compatibleDeficitShell_subset_commonShallowBad_of_orderedConjunctionBlocks
        blocks hpair)

/-- In the verified linear-gap regime, the newly extracted exact width-three coefficient tail
inherits the common-shallow `2^(10*r)` contraction.  This is the first direct quantitative
comparison between the factored polynomial mass and the switching upper bound. -/
theorem orderedTriples_coefficient_tail_scaled_le_linearGap
    {G r : ℕ}
    (blocks : Fin G → List (Fin (1000 * (G * 3) * r)))
    (hG : 0 < G) (hr : 0 < r)
    (hnd : ∀ g, (blocks g).Nodup)
    (hlen : ∀ g, (blocks g).length = 3)
    (hpair : ∀ g h, g ≠ h → Disjoint (blocks g).toFinset (blocks h).toFinset) :
    (∑ D ∈ compatibleDeficitTailIndices G (10 * r),
        MvPolynomial.coeff
          (Finsupp.single (0 : Fin 2) (20 * r) + Finsupp.single (1 : Fin 2) D)
          (tripleProductEnumerator G (1000 * (G * 3) * r - 3 * G))) *
        2 ^ (10 * r) ≤
      (Finset.univ.filter fun σ : Restriction (1000 * (G * 3) * r) =>
        stars σ = 20 * r).card := by
  let support : Fin G → Finset (Fin (1000 * (G * 3) * r)) :=
    fun g => (blocks g).toFinset
  have hcard : ∀ g, (support g).card = 3 := by
    intro g
    simp only [support, List.toFinset_card_of_nodup (hnd g), hlen g]
  have htail := compatibleDeficitShell_twenty_card_eq_coefficient_tail
    (r := r) support hpair hcard
  have hsubset := compatibleDeficitShell_subset_commonShallowBad_of_orderedConjunctionBlocks
    blocks hpair (K := 20 * r) (trunkDepth := 10 * r) (residualDepth := 1)
  have hupper := commonShallowBad_scaled_le_of_realized_density
    (gates := fun g => orderedConjunctionBlock (blocks g))
    (G := G) (w := 3) (d := 10 * r) (m := 1)
    (fuel := 1000 * (G * 3) * r) (K := 20 * r)
    (residualDepth := 1) (savingNum := 1) (savingDen := 2)
    (fun g => by simp [orderedConjunctionBlock])
    (fun g T hT => by
      simp only [orderedConjunctionBlock, List.mem_singleton] at hT
      subst T
      simpa using Nat.le_of_eq (hlen g))
    (fun g => by simp [orderedConjunctionBlock])
    (by
      have : 20 ≤ 1000 * (G * 3) := by nlinarith
      exact Nat.mul_le_mul_right r this)
    (by omega)
    (by omega)
    (by
      have : 20 ≤ 1000 * (G * 3) := by nlinarith
      exact Nat.mul_le_mul_right r this)
    (by omega)
    (by
      have hrG : r ≤ G * r := by
        calc
          r = 1 * r := by simp
          _ ≤ G * r := Nat.mul_le_mul_right r hG
      nlinarith)
  have hsaveEq : 20 * r / 2 = 10 * r := by omega
  calc
    (∑ D ∈ compatibleDeficitTailIndices G (10 * r),
        MvPolynomial.coeff
          (Finsupp.single (0 : Fin 2) (20 * r) + Finsupp.single (1 : Fin 2) D)
          (tripleProductEnumerator G (1000 * (G * 3) * r - 3 * G))) *
        2 ^ (10 * r) =
        (compatibleDeficitShell support (20 * r) (10 * r) 1).card *
          2 ^ (10 * r) := by rw [htail]
    _ ≤ (commonShallowBad (fun g => orderedConjunctionBlock (blocks g))
          (1000 * (G * 3) * r) (20 * r) (10 * r) 1).card * 2 ^ (10 * r) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hsubset)
    _ ≤ _ := by simpa [hsaveEq] using hupper

/-! ### Exact subfamily transfer and the clause-packing obstruction -/

/-- A common trunk for a larger indexed family is also a common trunk for every exactly reindexed
subfamily.  Injectivity of the index map is deliberately unnecessary: the semantic certificate
only needs every small gate to occur among the large gates. -/
theorem CommonShallowAt.of_reindex
    {n G H fuel trunkDepth residualDepth : ℕ}
    {small : Fin G → List (Clause n)} {large : Fin H → List (Clause n)}
    (e : Fin G → Fin H) (hgate : ∀ g, small g = large (e g))
    {sigma : Restriction n}
    (h : CommonShallowAt large fuel sigma trunkDepth residualDepth) :
    CommonShallowAt small fuel sigma trunkDepth residualDepth := by
  obtain ⟨trunk, hdepth, hleaf⟩ := h
  refine ⟨trunk, hdepth, ?_⟩
  intro x hx
  obtain ⟨hroot, hext, hshallow⟩ := hleaf x hx
  exact ⟨hroot, hext, fun g => by simpa [hgate g] using hshallow (e g)⟩

/-- A duplicate-free gate whose target term is live and whose every other term is already
falsified has exactly that target as its root-live sublist.  This packages the precise condition
missing from bare clause inclusion: competing terms must be killed, not merely ignored. -/
theorem liveTermFilter_eq_singleton {n : ℕ} (sigma : Restriction n) :
    ∀ (cs : List (Clause n)) (T : Clause n), cs.Nodup → T ∈ cs →
      termFalsified sigma T = false →
      (∀ U ∈ cs, U ≠ T → termFalsified sigma U = true) →
      cs.filter (fun U => !termFalsified sigma U) = [T] := by
  intro cs
  induction cs with
  | nil => simp
  | cons U cs ih =>
      intro T hnodup hTmem hTlive hcompetitors
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hTmem
      by_cases hUT : U = T
      · subst U
        rw [List.filter_cons_of_pos (by simp [hTlive])]
        have htail : cs.filter (fun V => !termFalsified sigma V) = [] := by
          rw [List.filter_eq_nil_iff]
          intro V hV
          have hVT : V ≠ T := by
            intro h
            subst V
            exact hnodup.1 hV
          have hfalse := hcompetitors V (by simp [hV]) hVT
          simp [hfalse]
        rw [htail]
      · have hUfalse := hcompetitors U (by simp) hUT
        rw [List.filter_cons_of_neg (by simp [hUfalse])]
        apply ih T hnodup.2
        · rcases hTmem with h | h
          · exact False.elim (hUT h.symm)
          · exact h
        · exact hTlive
        · intro V hV hVT
          exact hcompetitors V (by simp [hV]) hVT

/-- Restriction-dependent isolation is enough for exact subfamily transfer.  At every reached
leaf, root-falsified competitors remain falsified, so the full gate's canonical tree equals the
canonical tree of its root-live filter.  Unlike `of_reindex`, this permits the packed gate to
appear only after restricting the larger gate. -/
theorem CommonShallowAt.of_reindex_liveFilter
    {n G H fuel trunkDepth residualDepth : ℕ}
    {small : Fin G → List (Clause n)} {large : Fin H → List (Clause n)}
    (e : Fin G → Fin H) {sigma : Restriction n}
    (hgate : ∀ g, small g = (large (e g)).filter
      (fun T => !termFalsified sigma T))
    (h : CommonShallowAt large fuel sigma trunkDepth residualDepth) :
    CommonShallowAt small fuel sigma trunkDepth residualDepth := by
  obtain ⟨trunk, hdepth, hleaf⟩ := h
  refine ⟨trunk, hdepth, ?_⟩
  intro x hx
  obtain ⟨hroot, hext, hshallow⟩ := hleaf x hx
  refine ⟨hroot, hext, fun g => ?_⟩
  have htree := canonicalDT_eq_filter (large (e g)) sigma fuel
    (CommonTree.run trunk x)
    (fun T hT => termFalsified_mono (by exact hroot) hT)
  rw [← hgate g] at htree
  rw [← htree]
  exact hshallow (e g)

/-- Pointwise semantic transfer for restriction-isolated singleton gates.  This is the positive
replacement for the false clause-sublist shortcut: a bad root for the packed singleton family is
bad for the full family whenever each selected target survives and every competing term in its
selected full gate is falsified at that root. -/
theorem mem_commonShallowBad_of_isolatedSingleton_reindex
    {n G H fuel K trunkDepth residualDepth : ℕ}
    (large : Fin H → List (Clause n)) (target : Fin G → Clause n)
    (e : Fin G → Fin H) {sigma : Restriction n}
    (hnodup : ∀ g, (large (e g)).Nodup)
    (hmem : ∀ g, target g ∈ large (e g))
    (hlive : ∀ g, termFalsified sigma (target g) = false)
    (hcompetitors : ∀ g U, U ∈ large (e g) → U ≠ target g →
      termFalsified sigma U = true)
    (hsigma : sigma ∈ commonShallowBad (fun g => [target g]) fuel K
      trunkDepth residualDepth) :
    sigma ∈ commonShallowBad large fuel K trunkDepth residualDepth := by
  rw [mem_commonShallowBad] at hsigma ⊢
  refine ⟨hsigma.1, ?_⟩
  intro hlarge
  apply hsigma.2
  apply hlarge.of_reindex_liveFilter e
  intro g
  exact (liveTermFilter_eq_singleton sigma (large (e g)) (target g)
    (hnodup g) (hmem g) (hlive g) (hcompetitors g)).symm

/-! ### A necessary antichain condition for restriction isolation -/

/-- Falsification is monotone with respect to literal-list inclusion: if every literal of `U`
also occurs in `T`, then falsifying the weaker conjunction `U` also falsifies `T`.  No
consistency or duplicate-variable premise is needed for this one-way implication. -/
theorem termFalsified_true_of_lits_subset {n : ℕ} {sigma : Restriction n}
    {U T : Clause n} (hsub : ∀ ell ∈ U.lits, ell ∈ T.lits)
    (hU : termFalsified sigma U = true) :
    termFalsified sigma T = true := by
  rw [termFalsified, List.any_eq_true] at hU ⊢
  obtain ⟨ell, hellU, hfalse⟩ := hU
  exact ⟨ell, hsub ell hellU, hfalse⟩

/-- Contrapositively, a target conjunction that survives a restriction forces every conjunction
whose literals are contained in the target's literals to survive as well. -/
theorem termFalsified_false_of_lits_subset {n : ℕ} {sigma : Restriction n}
    {U T : Clause n} (hsub : ∀ ell ∈ U.lits, ell ∈ T.lits)
    (hT : termFalsified sigma T = false) :
    termFalsified sigma U = false := by
  cases hU : termFalsified sigma U with
  | false => rfl
  | true =>
      have hTtrue := termFalsified_true_of_lits_subset hsub hU
      rw [hT] at hTtrue
      simp at hTtrue

/-- Any target isolated as the unique live term must be inclusion-minimal among the other terms
of its gate.  In particular, `eraseDups` alone is insufficient: it removes equal competitors but
does not remove a distinct weaker term whose literals are contained in the target. -/
theorem not_lits_subset_of_isolatedSingleton {n : ℕ} {sigma : Restriction n}
    {cs : List (Clause n)} {T U : Clause n}
    (hlive : termFalsified sigma T = false)
    (hcompetitors : ∀ V ∈ cs, V ≠ T → termFalsified sigma V = true)
    (hUmem : U ∈ cs) (hUne : U ≠ T) :
    ¬ (∀ ell ∈ U.lits, ell ∈ T.lits) := by
  intro hsub
  have hUfalse := termFalsified_false_of_lits_subset hsub hlive
  have hUtrue := hcompetitors U hUmem hUne
  rw [hUfalse] at hUtrue
  simp at hUtrue

/-- A term is inclusion-minimal inside its original ordered gate when every gate term whose
literal list is contained in it is equal to it.  This definition deliberately does not reorder
or delete any term, so it is compatible with the canonical-tree interface. -/
def InclusionMinimalIn {n : ℕ} (cs : List (Clause n)) (T : Clause n) : Prop :=
  T ∈ cs ∧ ∀ U ∈ cs, (∀ ell ∈ U.lits, ell ∈ T.lits) → U = T

/-- Every competitor of an inclusion-minimal target contains a literal outside the target.  This
is the exact local resource needed by a future isolation construction: making that literal false
can kill the competitor without making an identical target literal false. -/
theorem exists_outside_literal_of_inclusionMinimal {n : ℕ} {cs : List (Clause n)}
    {T U : Clause n} (hmin : InclusionMinimalIn cs T) (hUmem : U ∈ cs) (hUne : U ≠ T) :
    ∃ ell ∈ U.lits, ell ∉ T.lits := by
  by_contra hout
  push_neg at hout
  exact hUne (hmin.2 U hUmem hout)

/-- Unique liveness implies inclusion-minimality in the unchanged ordered gate.  Thus the
outside-literal conclusion above is not merely sufficient bookkeeping: every target accepted by
the existing exact isolation interface necessarily has it. -/
theorem inclusionMinimal_of_isolatedSingleton {n : ℕ} {sigma : Restriction n}
    {cs : List (Clause n)} {T : Clause n} (hTmem : T ∈ cs)
    (hlive : termFalsified sigma T = false)
    (hcompetitors : ∀ U ∈ cs, U ≠ T → termFalsified sigma U = true) :
    InclusionMinimalIn cs T := by
  refine ⟨hTmem, ?_⟩
  intro U hUmem hsub
  by_contra hUne
  exact not_lits_subset_of_isolatedSingleton hlive hcompetitors hUmem hUne hsub

/-! ### Globally compatible outside-literal selections -/

/-- A finite literal selection simultaneously isolates the chosen targets when selected
literals agree on every shared variable, no selected variable occurs in any target, and every
competitor contains a selected literal.  The variable-disjointness premise is deliberately
stronger than literal non-membership: selecting `x` to be false would also kill a target
containing `¬x`. -/
def GloballyCompatibleIsolationSelection {n G H : ℕ}
    (large : Fin H → List (Clause n)) (target : Fin G → Clause n)
    (e : Fin G → Fin H) (selected : List (Rung4Literal n)) : Prop :=
  (∀ ell₁ ∈ selected, ∀ ell₂ ∈ selected,
      litVar ell₁ = litVar ell₂ → falValue ell₁ = falValue ell₂) ∧
    (∀ ell ∈ selected, ∀ g, ∀ t ∈ (target g).lits, litVar ell ≠ litVar t) ∧
    (∀ g U, U ∈ large (e g) → U ≠ target g →
      ∃ ell ∈ selected, ell ∈ U.lits)

/-- The restriction induced by a compatible selection fixes exactly the variables represented
in the selection, using the falsifying value of an arbitrary representative.  Compatibility
makes that arbitrary choice harmless. -/
noncomputable def compatibleIsolationRestriction {n : ℕ}
    (selected : List (Rung4Literal n)) : Restriction n := fun i =>
  if h : ∃ ell ∈ selected, litVar ell = i then
    some (falValue (Classical.choose h))
  else none

/-- The coordinate set fixed by a compatible isolation selection.  Polarity and repeated
occurrences are deliberately forgotten here: shell accounting pays once per selected variable. -/
def compatibleIsolationSelectedVars {n : ℕ}
    (selected : List (Rung4Literal n)) : Finset (Fin n) :=
  (selected.map litVar).toFinset

/-- The induced isolation restriction leaves exactly the coordinates absent from the selected
variable set free.  This fact does not require consistency: consistency controls which value is
chosen, whereas the free/fixed pattern depends only on existence of a selected representative. -/
theorem freeVars_compatibleIsolationRestriction {n : ℕ}
    (selected : List (Rung4Literal n)) :
    freeVars (compatibleIsolationRestriction selected) =
      Finset.univ \ compatibleIsolationSelectedVars selected := by
  ext i
  simp [mem_freeVars, compatibleIsolationRestriction,
    compatibleIsolationSelectedVars]

/-- Exact shell location of the restriction constructed from a literal selection. -/
theorem stars_compatibleIsolationRestriction {n : ℕ}
    (selected : List (Rung4Literal n)) :
    stars (compatibleIsolationRestriction selected) =
      n - (compatibleIsolationSelectedVars selected).card := by
  rw [stars, freeVars_compatibleIsolationRestriction,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  simp

/-- A selection fixes no more variables than it has literal occurrences. -/
theorem compatibleIsolationSelectedVars_card_le {n : ℕ}
    (selected : List (Rung4Literal n)) :
    (compatibleIsolationSelectedVars selected).card ≤ selected.length := by
  simpa [compatibleIsolationSelectedVars] using
    (List.toFinset_card_le (selected.map litVar))

/-- Consequently a compatible isolation selection of length at most `q` lands at or above the
`(n-q)`-star shell.  This is the fixed-shell expenditure bound needed by the positive branch. -/
theorem sub_le_stars_compatibleIsolationRestriction {n q : ℕ}
    {selected : List (Rung4Literal n)} (hlen : selected.length ≤ q) :
    n - q ≤ stars (compatibleIsolationRestriction selected) := by
  rw [stars_compatibleIsolationRestriction]
  exact Nat.sub_le_sub_left
    ((compatibleIsolationSelectedVars_card_le selected).trans hlen) n

/-- With no repeated selected variable, literal count is the exact number of fixed coordinates. -/
theorem stars_compatibleIsolationRestriction_eq_sub_length {n : ℕ}
    {selected : List (Rung4Literal n)} (hvars : (selected.map litVar).Nodup) :
    stars (compatibleIsolationRestriction selected) = n - selected.length := by
  rw [stars_compatibleIsolationRestriction, compatibleIsolationSelectedVars,
    List.toFinset_card_of_nodup hvars, List.length_map]

/-! ### Target-preserving extension to a prescribed shell -/

/-- The distinct variables used by the complete packed target family. -/
def compatibleIsolationTargetVars {n G : ℕ} (target : Fin G → Clause n) :
    Finset (Fin n) :=
  Finset.univ.biUnion fun g => ((target g).lits.map litVar).toFinset

theorem mem_compatibleIsolationTargetVars {n G : ℕ} (target : Fin G → Clause n)
    (i : Fin n) :
    i ∈ compatibleIsolationTargetVars target ↔
      ∃ g t, t ∈ (target g).lits ∧ litVar t = i := by
  simp [compatibleIsolationTargetVars]

/-! ### Competitor--target-support conflict edges -/

/-- The variables of one competitor that remain available after excluding the support of every
preserved target.  These are the vertices of the simplest competitor conflict edge.  Polarity is
retained later by the literal selection; at this stage an empty edge is already a decisive
obstruction, since global compatibility forbids fixing any target variable in either polarity. -/
def competitorOutsideTargetVars {n G : ℕ} (target : Fin G → Clause n)
    (U : Clause n) : Finset (Fin n) :=
  (U.lits.map litVar).toFinset \ compatibleIsolationTargetVars target

/-- The literal-level vertex pool underlying all nonempty competitor edges.  Unlike
`competitorOutsideTargetVars`, this retains polarity: every literal in every full-family gate
whose variable avoids the complete preserved-target support occurs in the pool.  Keeping all
such literals (rather than choosing representatives yet) cleanly separates edge nonemptiness
from the remaining polarity-consistency constraint. -/
def outsideTargetLiteralPool {n G H : ℕ} (large : Fin H → List (Clause n))
    (target : Fin G → Clause n) : List (Rung4Literal n) :=
  (List.ofFn large).flatten.flatMap fun U =>
    U.lits.filter fun ell => litVar ell ∉ compatibleIsolationTargetVars target

theorem mem_outsideTargetLiteralPool {n G H : ℕ} (large : Fin H → List (Clause n))
    (target : Fin G → Clause n) (ell : Rung4Literal n) :
    ell ∈ outsideTargetLiteralPool large target ↔
      (∃ h, ∃ U ∈ large h, ell ∈ U.lits) ∧
        litVar ell ∉ compatibleIsolationTargetVars target := by
  simp [outsideTargetLiteralPool] <;> aesop

theorem mem_competitorOutsideTargetVars {n G : ℕ} (target : Fin G → Clause n)
    (U : Clause n) (i : Fin n) :
    i ∈ competitorOutsideTargetVars target U ↔
      (∃ ell ∈ U.lits, litVar ell = i) ∧
        i ∉ compatibleIsolationTargetVars target := by
  simp [competitorOutsideTargetVars]

/-- Nonempty variable edges plus polarity consistency of the complete available-literal pool
are sufficient for global isolation.  Selecting the whole pool is deliberately nonminimal: the
theorem identifies the exact remaining obstruction without hiding a choice principle or a
transversal-size estimate. -/
theorem exists_globallyCompatibleIsolationSelection_of_nonempty_edges_of_pool_consistent
    {n G H : ℕ} {large : Fin H → List (Clause n)}
    {target : Fin G → Clause n} {e : Fin G → Fin H}
    (hedge : ∀ g U, U ∈ large (e g) → U ≠ target g →
      (competitorOutsideTargetVars target U).Nonempty)
    (hconsistent : ∀ ell₁ ∈ outsideTargetLiteralPool large target,
      ∀ ell₂ ∈ outsideTargetLiteralPool large target,
        litVar ell₁ = litVar ell₂ → falValue ell₁ = falValue ell₂) :
    ∃ selected, GloballyCompatibleIsolationSelection large target e selected := by
  refine ⟨outsideTargetLiteralPool large target, hconsistent, ?_, ?_⟩
  · intro ell hell g t ht heq
    have hout := (mem_outsideTargetLiteralPool large target ell).mp hell
    apply hout.2
    rw [mem_compatibleIsolationTargetVars]
    exact ⟨g, t, ht, heq.symm⟩
  · intro g U hUmem hUne
    obtain ⟨i, hi⟩ := hedge g U hUmem hUne
    rw [mem_competitorOutsideTargetVars] at hi
    obtain ⟨⟨ell, hellU, rfl⟩, hout⟩ := hi
    refine ⟨ell, ?_, hellU⟩
    rw [mem_outsideTargetLiteralPool]
    exact ⟨⟨e g, U, hUmem, hellU⟩, hout⟩

/-- Two singleton competitor edges that demand opposite falsifying values on one variable form a
complete polarity-conflict certificate.  In particular, nonempty variable edges alone do not
imply the existence of a globally compatible isolation selection. -/
theorem not_exists_globallyCompatibleIsolationSelection_of_singleton_polarity_conflict
    {n G H : ℕ} {large : Fin H → List (Clause n)}
    {target : Fin G → Clause n} {e : Fin G → Fin H}
    {g₁ g₂ : Fin G} {U₁ U₂ : Clause n} {ell₁ ell₂ : Rung4Literal n}
    (hU₁mem : U₁ ∈ large (e g₁)) (hU₁ne : U₁ ≠ target g₁)
    (hU₁lits : U₁.lits = [ell₁])
    (hU₂mem : U₂ ∈ large (e g₂)) (hU₂ne : U₂ ≠ target g₂)
    (hU₂lits : U₂.lits = [ell₂])
    (hvar : litVar ell₁ = litVar ell₂)
    (hpol : falValue ell₁ ≠ falValue ell₂) :
    ¬ ∃ selected, GloballyCompatibleIsolationSelection large target e selected := by
  rintro ⟨selected, hselection⟩
  obtain ⟨a, haSelected, haU₁⟩ := hselection.2.2 g₁ U₁ hU₁mem hU₁ne
  obtain ⟨b, hbSelected, hbU₂⟩ := hselection.2.2 g₂ U₂ hU₂mem hU₂ne
  rw [hU₁lits] at haU₁
  rw [hU₂lits] at hbU₂
  simp only [List.mem_singleton] at haU₁ hbU₂
  subst a
  subst b
  exact hpol (hselection.1 ell₁ haSelected ell₂ hbSelected hvar)

/-- A total Boolean orientation assignment hits the competitor family when every competitor
contains an available literal whose falsifying value is the value assigned to its variable.
This is the ordinary clause-satisfaction formulation of the polarity-aware transversal problem:
target variables have first been deleted, and the remaining literal orientations are the clause
literals. -/
def HitsOutsideCompetitors {n G H : ℕ} (large : Fin H → List (Clause n))
    (target : Fin G → Clause n) (e : Fin G → Fin H)
    (assignment : Fin n → Bool) : Prop :=
  ∀ g U, U ∈ large (e g) → U ≠ target g →
    ∃ ell ∈ U.lits, litVar ell ∉ compatibleIsolationTargetVars target ∧
      assignment (litVar ell) = falValue ell

/-- Compatible isolation selection is exactly satisfiability of the outside-literal competitor
clauses.  The forward direction extends the consistent partial orientation represented by a
selection to an arbitrary total Boolean assignment.  The reverse direction selects every
available occurrence matched by a satisfying assignment.  Thus no extra combinatorial
tractability follows merely from calling the problem an oriented transversal. -/
theorem exists_globallyCompatibleIsolationSelection_iff_exists_hitsOutsideCompetitors
    {n G H : ℕ} {large : Fin H → List (Clause n)}
    {target : Fin G → Clause n} {e : Fin G → Fin H} :
    (∃ selected, GloballyCompatibleIsolationSelection large target e selected) ↔
      ∃ assignment, HitsOutsideCompetitors large target e assignment := by
  constructor
  · rintro ⟨selected, hconsistent, htarget, hhit⟩
    let assignment : Fin n → Bool := fun i =>
      if h : ∃ ell ∈ selected, litVar ell = i then
        falValue (Classical.choose h)
      else false
    refine ⟨assignment, ?_⟩
    intro g U hUmem hUne
    obtain ⟨ell, hellSelected, hellU⟩ := hhit g U hUmem hUne
    refine ⟨ell, hellU, ?_, ?_⟩
    · intro hellTarget
      rw [mem_compatibleIsolationTargetVars] at hellTarget
      obtain ⟨g', t, ht, heq⟩ := hellTarget
      exact htarget ell hellSelected g' t ht heq.symm
    · have hexists : ∃ ell' ∈ selected, litVar ell' = litVar ell :=
        ⟨ell, hellSelected, rfl⟩
      rw [show assignment (litVar ell) =
        falValue (Classical.choose hexists) by simp [assignment, hexists]]
      exact hconsistent (Classical.choose hexists)
        (Classical.choose_spec hexists).1 ell hellSelected
        (Classical.choose_spec hexists).2
  · rintro ⟨assignment, hhit⟩
    let selected := (outsideTargetLiteralPool large target).filter fun ell =>
      assignment (litVar ell) = falValue ell
    refine ⟨selected, ?_, ?_, ?_⟩
    · intro ell₁ hell₁ ell₂ hell₂ hvar
      rw [List.mem_filter] at hell₁ hell₂
      have hvalue₁ := of_decide_eq_true hell₁.2
      have hvalue₂ := of_decide_eq_true hell₂.2
      rw [← hvalue₁, ← hvalue₂, hvar]
    · intro ell hellSelected g t ht heq
      rw [List.mem_filter] at hellSelected
      have hout := (mem_outsideTargetLiteralPool large target ell).mp hellSelected.1
      apply hout.2
      rw [mem_compatibleIsolationTargetVars]
      exact ⟨g, t, ht, heq.symm⟩
    · intro g U hUmem hUne
      obtain ⟨ell, hellU, hout, hvalue⟩ := hhit g U hUmem hUne
      refine ⟨ell, ?_, hellU⟩
      rw [List.mem_filter]
      refine ⟨?_, decide_eq_true hvalue⟩
      rw [mem_outsideTargetLiteralPool]
      exact ⟨⟨e g, U, hUmem, hellU⟩, hout⟩

/-! ### Unsatisfiable polarity cores -/

/-- A Boolean orientation hits a finite competitor core when it falsifies an available
outside-target literal in every indexed competitor retained by the core.  Unlike
`HitsOutsideCompetitors`, this predicate ranges only over the explicitly retained clauses. -/
def HitsOutsideCompetitorCore {n G : ℕ} (target : Fin G → Clause n)
    (core : Finset (Fin G × Clause n)) (assignment : Fin n → Bool) : Prop :=
  ∀ p ∈ core,
    ∃ ell ∈ p.2.lits,
      litVar ell ∉ compatibleIsolationTargetVars target ∧
        assignment (litVar ell) = falValue ell

/-- The full finite outside-competitor clause system.  A pair `(g, U)` occurs exactly when `U`
is a proper competitor of the preserved target `target g` in the gate selected by `e g`.
Converting each gate list to a finset deliberately forgets duplicate occurrences: duplicates do
not change satisfiability, while the target index remains part of the clause identity. -/
def fullOutsideCompetitorCore {n G H : ℕ} (large : Fin H → List (Clause n))
    (target : Fin G → Clause n) (e : Fin G → Fin H) : Finset (Fin G × Clause n) :=
  Finset.univ.biUnion fun g =>
    ((large (e g)).toFinset.erase (target g)).image fun U => (g, U)

theorem mem_fullOutsideCompetitorCore {n G H : ℕ}
    (large : Fin H → List (Clause n)) (target : Fin G → Clause n)
    (e : Fin G → Fin H) (g : Fin G) (U : Clause n) :
    (g, U) ∈ fullOutsideCompetitorCore large target e ↔
      U ∈ large (e g) ∧ U ≠ target g := by
  simpa [fullOutsideCompetitorCore, and_comm]

/-- Hitting the explicit full finite core is exactly the earlier quantified condition that hits
every proper competitor.  This is the finite clause-system bridge needed before asking for a
small unsatisfiable subcore. -/
theorem hitsOutsideCompetitorCore_full_iff_hitsOutsideCompetitors
    {n G H : ℕ} (large : Fin H → List (Clause n))
    (target : Fin G → Clause n) (e : Fin G → Fin H)
    (assignment : Fin n → Bool) :
    HitsOutsideCompetitorCore target (fullOutsideCompetitorCore large target e) assignment ↔
      HitsOutsideCompetitors large target e assignment := by
  constructor
  · intro hhit g U hUmem hUne
    exact hhit (g, U) ((mem_fullOutsideCompetitorCore large target e g U).2 ⟨hUmem, hUne⟩)
  · intro hhit p hp
    have hmem := (mem_fullOutsideCompetitorCore large target e p.1 p.2).1 hp
    exact hhit p.1 p.2 hmem.1 hmem.2

/-- An unsatisfiable competitor core is inclusion-minimal when deleting any retained indexed
competitor makes it satisfiable.  For a finite core this one-element deletion formulation is
equivalent to having no proper unsatisfiable subcore, and exposes the witnesses needed for the
sharp generic cardinality bound below. -/
def InclusionMinimalUnsatisfiableCore {n G : ℕ} (target : Fin G → Clause n)
    (core : Finset (Fin G × Clause n)) : Prop :=
  (¬ ∃ assignment, HitsOutsideCompetitorCore target core assignment) ∧
    ∀ p ∈ core, ∃ assignment,
      HitsOutsideCompetitorCore target (core.erase p) assignment

/-- Every finite unsatisfiable competitor system contains an inclusion-minimal unsatisfiable
subcore.  This is purely a finite descent statement and makes no quantitative small-core claim. -/
theorem exists_inclusionMinimalUnsatisfiableCore_subset {n G : ℕ}
    (target : Fin G → Clause n) (full : Finset (Fin G × Clause n))
    (hunsat : ¬ ∃ assignment, HitsOutsideCompetitorCore target full assignment) :
    ∃ core ⊆ full, InclusionMinimalUnsatisfiableCore target core := by
  classical
  induction full using Finset.strongInductionOn with
  | _ full ih =>
      by_cases hminimal : ∀ p ∈ full, ∃ assignment,
          HitsOutsideCompetitorCore target (full.erase p) assignment
      · exact ⟨full, Finset.Subset.rfl, hunsat, hminimal⟩
      · push_neg at hminimal
        obtain ⟨p, hp, heraseUnsat⟩ := hminimal
        have heraseUnsat' : ¬ ∃ assignment,
            HitsOutsideCompetitorCore target (full.erase p) assignment := by
          rintro ⟨assignment, hhit⟩
          exact heraseUnsat assignment hhit
        obtain ⟨core, hcoreErase, hcoreMinimal⟩ :=
          ih (full.erase p) (Finset.erase_ssubset hp) heraseUnsat'
        exact ⟨core, hcoreErase.trans (Finset.erase_subset _ _), hcoreMinimal⟩

/-- The best generic bound supplied by inclusion-minimality alone is exponential in the ambient
Boolean support.  Each retained competitor has a satisfying assignment for the core with that
competitor deleted.  Two different competitors cannot share such a witness, since the witness for
either deletion would then also hit the missing competitor and satisfy the whole core. -/
theorem InclusionMinimalUnsatisfiableCore.card_le_two_pow {n G : ℕ}
    {target : Fin G → Clause n} {core : Finset (Fin G × Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core) :
    core.card ≤ 2 ^ n := by
  classical
  let witness : ↥core → (Fin n → Bool) := fun p =>
    Classical.choose (hminimal.2 p p.property)
  have hwitness (p : ↥core) :
      HitsOutsideCompetitorCore target (core.erase p.1) (witness p) :=
    Classical.choose_spec (hminimal.2 p p.property)
  have hinjective : Function.Injective witness := by
    intro p q hw
    apply Subtype.ext
    by_contra hpq
    apply hminimal.1
    refine ⟨witness p, ?_⟩
    intro r hr
    by_cases hrp : r = p.1
    · subst r
      have hpneqq : p.1 ≠ q.1 := by
        intro heq
        exact hpq heq
      have hhit := hwitness q p.1 (Finset.mem_erase.mpr ⟨hpneqq, p.property⟩)
      simpa [hw] using hhit
    · exact hwitness p r (Finset.mem_erase.mpr ⟨hrp, hr⟩)
  calc
    core.card = Fintype.card ↥core := by simp
    _ ≤ Fintype.card (Fin n → Bool) :=
      Fintype.card_le_of_injective witness hinjective
    _ = 2 ^ n := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- When every outside edge is carried by the recorded canonical-query support, the same witness
injection compresses to assignments on that support.  Thus the unconditional core bound is
`2 ^ queried.card`, not `2 ^ n`; it is nevertheless exponential, so minimality alone does not
provide the desired linear canonical-path charge. -/
theorem InclusionMinimalUnsatisfiableCore.card_le_two_pow_queried {n G : ℕ}
    {target : Fin G → Clause n} {queried : Finset (Fin n)}
    {core : Finset (Fin G × Clause n)}
    (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hsupport : ∀ p ∈ core,
      competitorOutsideTargetVars target p.2 ⊆ queried) :
    core.card ≤ 2 ^ queried.card := by
  classical
  let fullWitness : ↥core → (Fin n → Bool) := fun p =>
    Classical.choose (hminimal.2 p p.property)
  have hfullWitness (p : ↥core) :
      HitsOutsideCompetitorCore target (core.erase p.1) (fullWitness p) :=
    Classical.choose_spec (hminimal.2 p p.property)
  let witness : ↥core → (↥queried → Bool) := fun p i => fullWitness p i.1
  have hinjective : Function.Injective witness := by
    intro p q hw
    apply Subtype.ext
    by_contra hpq
    apply hminimal.1
    refine ⟨fullWitness p, ?_⟩
    intro r hr
    by_cases hrp : r = p.1
    · subst r
      have hpneqq : p.1 ≠ q.1 := by
        intro heq
        exact hpq heq
      obtain ⟨ell, hell, hout, hvalue⟩ :=
        hfullWitness q p.1 (Finset.mem_erase.mpr ⟨hpneqq, p.property⟩)
      have hedge : litVar ell ∈ competitorOutsideTargetVars target p.1.2 :=
        (mem_competitorOutsideTargetVars target p.1.2 (litVar ell)).2
          ⟨⟨ell, hell, rfl⟩, hout⟩
      have hqueried : litVar ell ∈ queried := hsupport p.1 p.property hedge
      refine ⟨ell, hell, hout, ?_⟩
      have hcoordinate := congrFun hw ⟨litVar ell, hqueried⟩
      exact hcoordinate.trans hvalue
    · exact hfullWitness p r (Finset.mem_erase.mpr ⟨hrp, hr⟩)
  calc
    core.card = Fintype.card ↥core := by simp
    _ ≤ Fintype.card (↥queried → Bool) :=
      Fintype.card_le_of_injective witness hinjective
    _ = 2 ^ queried.card := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- Compatible isolation exists exactly when the full finite outside-competitor clause system is
satisfiable.  Consequently isolation failure is literally unsatisfiability of this full core;
the equivalence itself does not need the additional hypothesis that every outside edge is
nonempty (an empty edge is simply a one-clause unsatisfiable core). -/
theorem exists_globallyCompatibleIsolationSelection_iff_fullCore_satisfiable
    {n G H : ℕ} {large : Fin H → List (Clause n)}
    {target : Fin G → Clause n} {e : Fin G → Fin H} :
    (∃ selected, GloballyCompatibleIsolationSelection large target e selected) ↔
      ∃ assignment,
        HitsOutsideCompetitorCore target
          (fullOutsideCompetitorCore large target e) assignment := by
  rw [exists_globallyCompatibleIsolationSelection_iff_exists_hitsOutsideCompetitors]
  constructor
  · rintro ⟨assignment, hhit⟩
    exact ⟨assignment,
      (hitsOutsideCompetitorCore_full_iff_hitsOutsideCompetitors
        large target e assignment).2 hhit⟩
  · rintro ⟨assignment, hhit⟩
    exact ⟨assignment,
      (hitsOutsideCompetitorCore_full_iff_hitsOutsideCompetitors
        large target e assignment).1 hhit⟩

theorem not_exists_globallyCompatibleIsolationSelection_iff_fullCore_unsatisfiable
    {n G H : ℕ} {large : Fin H → List (Clause n)}
    {target : Fin G → Clause n} {e : Fin G → Fin H} :
    (¬ ∃ selected, GloballyCompatibleIsolationSelection large target e selected) ↔
      ¬ ∃ assignment,
        HitsOutsideCompetitorCore target
          (fullOutsideCompetitorCore large target e) assignment := by
  rw [exists_globallyCompatibleIsolationSelection_iff_fullCore_satisfiable]

/-- A polarity-cycle certificate is a finite unsatisfiable core of genuine competitors whose
outside-target variable edges are nonempty and lie on the recorded canonical-query support.

The name "cycle" describes the intended small certificates (such as two clauses forcing opposite
orientations), while the definition deliberately permits an arbitrary finite unsatisfiable core.
This keeps soundness separate from the still-open quantitative claim that a core can always be
chosen linearly small. -/
def PolarityCycleValid {n G H : ℕ} (large : Fin H → List (Clause n))
    (target : Fin G → Clause n) (e : Fin G → Fin H)
    (queried : Finset (Fin n)) (core : Finset (Fin G × Clause n)) : Prop :=
  core.Nonempty ∧
    (∀ p ∈ core,
      p.2 ∈ large (e p.1) ∧
        p.2 ≠ target p.1 ∧
        (competitorOutsideTargetVars target p.2).Nonempty ∧
        competitorOutsideTargetVars target p.2 ⊆ queried) ∧
    ¬ ∃ assignment, HitsOutsideCompetitorCore target core assignment

/-- Every valid polarity cycle blocks a globally compatible isolation selection.  The proof uses
the exact selection--orientation equivalence: a selection would induce a total assignment hitting
all competitors and therefore the retained core, contradicting its unsatisfiability. -/
theorem PolarityCycleValid.not_exists_globallyCompatibleIsolationSelection
    {n G H : ℕ} {large : Fin H → List (Clause n)}
    {target : Fin G → Clause n} {e : Fin G → Fin H}
    {queried : Finset (Fin n)} {core : Finset (Fin G × Clause n)}
    (hvalid : PolarityCycleValid large target e queried core) :
    ¬ ∃ selected, GloballyCompatibleIsolationSelection large target e selected := by
  intro hselection
  obtain ⟨assignment, hhit⟩ :=
    exists_globallyCompatibleIsolationSelection_iff_exists_hitsOutsideCompetitors.mp hselection
  apply hvalid.2.2
  refine ⟨assignment, ?_⟩
  intro p hp
  exact hhit p.1 p.2 (hvalid.2.1 p hp).1 (hvalid.2.1 p hp).2.1

/-- If every proper competitor has a nonempty outside edge, all of those edges lie in the
recorded query support, and compatible isolation fails, then the full finite competitor system
is itself a valid polarity-cycle core.  This is a completeness theorem for the certificate
interface.  It deliberately makes no small-core claim: the full core may retain every indexed
proper competitor. -/
theorem fullOutsideCompetitorCore_polarityCycleValid_of_failure
    {n G H : ℕ} {large : Fin H → List (Clause n)}
    {target : Fin G → Clause n} {e : Fin G → Fin H}
    {queried : Finset (Fin n)}
    (hedge : ∀ g U, U ∈ large (e g) → U ≠ target g →
      (competitorOutsideTargetVars target U).Nonempty)
    (hqueried : ∀ g U, U ∈ large (e g) → U ≠ target g →
      competitorOutsideTargetVars target U ⊆ queried)
    (hfailure : ¬ ∃ selected,
      GloballyCompatibleIsolationSelection large target e selected) :
    PolarityCycleValid large target e queried
      (fullOutsideCompetitorCore large target e) := by
  have hunsat : ¬ ∃ assignment,
      HitsOutsideCompetitorCore target
        (fullOutsideCompetitorCore large target e) assignment :=
    not_exists_globallyCompatibleIsolationSelection_iff_fullCore_unsatisfiable.mp hfailure
  refine ⟨?_, ?_, hunsat⟩
  · by_contra hnonempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty] at hunsat
    apply hunsat
    exact ⟨fun _ => false, by simp [HitsOutsideCompetitorCore]⟩
  · intro p hp
    have hmem :=
      (mem_fullOutsideCompetitorCore large target e p.1 p.2).1 hp
    exact ⟨hmem.1, hmem.2,
      hedge p.1 p.2 hmem.1 hmem.2,
      hqueried p.1 p.2 hmem.1 hmem.2⟩

/-- Isolation failure admits an inclusion-minimal valid polarity core whose size is bounded by
the full Boolean assignment space on the recorded query support.  This is the strongest generic
consequence of finite minimality established here: the bound is exponential in query support and
therefore does not by itself yield the linear charge needed by the switching recurrence. -/
theorem exists_minimalPolarityCycleValid_card_le_two_pow_queried
    {n G H : ℕ} {large : Fin H → List (Clause n)}
    {target : Fin G → Clause n} {e : Fin G → Fin H}
    {queried : Finset (Fin n)}
    (hedge : ∀ g U, U ∈ large (e g) → U ≠ target g →
      (competitorOutsideTargetVars target U).Nonempty)
    (hqueried : ∀ g U, U ∈ large (e g) → U ≠ target g →
      competitorOutsideTargetVars target U ⊆ queried)
    (hfailure : ¬ ∃ selected,
      GloballyCompatibleIsolationSelection large target e selected) :
    ∃ core,
      core ⊆ fullOutsideCompetitorCore large target e ∧
      InclusionMinimalUnsatisfiableCore target core ∧
      PolarityCycleValid large target e queried core ∧
      core.card ≤ 2 ^ queried.card := by
  classical
  have hfullUnsat : ¬ ∃ assignment,
      HitsOutsideCompetitorCore target
        (fullOutsideCompetitorCore large target e) assignment :=
    not_exists_globallyCompatibleIsolationSelection_iff_fullCore_unsatisfiable.mp hfailure
  obtain ⟨core, hcoreFull, hminimal⟩ :=
    exists_inclusionMinimalUnsatisfiableCore_subset target
      (fullOutsideCompetitorCore large target e) hfullUnsat
  have hcoreNonempty : core.Nonempty := by
    by_contra hnonempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty] at hminimal
    apply hminimal.1
    exact ⟨fun _ => false, by simp [HitsOutsideCompetitorCore]⟩
  have hproperties : ∀ p ∈ core,
      p.2 ∈ large (e p.1) ∧
        p.2 ≠ target p.1 ∧
        (competitorOutsideTargetVars target p.2).Nonempty ∧
        competitorOutsideTargetVars target p.2 ⊆ queried := by
    intro p hp
    have hmem := (mem_fullOutsideCompetitorCore large target e p.1 p.2).1
      (hcoreFull hp)
    exact ⟨hmem.1, hmem.2,
      hedge p.1 p.2 hmem.1 hmem.2,
      hqueried p.1 p.2 hmem.1 hmem.2⟩
  have hcard : core.card ≤ 2 ^ queried.card :=
    hminimal.card_le_two_pow_queried fun p hp => (hproperties p hp).2.2.2
  exact ⟨core, hcoreFull, hminimal,
    ⟨hcoreNonempty, hproperties, hminimal.1⟩, hcard⟩

/-! ### Query incidence of a reduced polarity core -/

/-- The exact clause--coordinate incidence relation of a retained polarity core, restricted to
the recorded canonical-query support.  Unlike the earlier complete target--competitor relation,
this relation keeps only coordinates that actually occur in the retained outside edge. -/
def polarityCoreQueryIncidences {n G : ℕ} (target : Fin G → Clause n)
    (core : Finset (Fin G × Clause n)) (queried : Finset (Fin n)) :
    Finset ((Fin G × Clause n) × Fin n) :=
  (core ×ˢ queried).filter fun p =>
    p.2 ∈ competitorOutsideTargetVars target p.1.2

/-- The incidence relation is contained in the evident core-by-query rectangle. -/
theorem polarityCoreQueryIncidences_subset_product {n G : ℕ}
    (target : Fin G → Clause n) (core : Finset (Fin G × Clause n))
    (queried : Finset (Fin n)) :
    polarityCoreQueryIncidences target core queried ⊆ core ×ˢ queried := by
  exact Finset.filter_subset _ _

/-- Consequently its aggregate size is at most `core.card * queried.card`. -/
theorem polarityCoreQueryIncidences_card_le_mul {n G : ℕ}
    (target : Fin G → Clause n) (core : Finset (Fin G × Clause n))
    (queried : Finset (Fin n)) :
    (polarityCoreQueryIncidences target core queried).card ≤
      core.card * queried.card := by
  exact (Finset.card_le_card
    (polarityCoreQueryIncidences_subset_product target core queried)).trans_eq
      (Finset.card_product _ _)

/-- Every single queried coordinate receives at most one incidence from each retained clause. -/
theorem polarityCoreQueryIncidences_coordinate_fiber_card_le {n G : ℕ}
    (target : Fin G → Clause n) (core : Finset (Fin G × Clause n))
    (queried : Finset (Fin n)) (v : Fin n) :
    ((polarityCoreQueryIncidences target core queried).filter fun p => p.2 = v).card ≤
      core.card := by
  have hsubset :
      (polarityCoreQueryIncidences target core queried).filter (fun p => p.2 = v) ⊆
        core ×ˢ {v} := by
    intro p hp
    have hproduct := polarityCoreQueryIncidences_subset_product target core queried
      (Finset.mem_filter.mp hp).1
    have hv : p.2 = v := (Finset.mem_filter.mp hp).2
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hproduct).1,
      Finset.mem_singleton.mpr hv⟩
  exact (Finset.card_le_card hsubset).trans_eq (by simp)

/-- Minimal-core reduction plus query support gives only an exponential-times-support aggregate
incidence bound.  This is the precise unconditional output of the current incidence audit; it is
not the sought linear canonical-path charge. -/
theorem InclusionMinimalUnsatisfiableCore.polarityCoreQueryIncidences_card_le
    {n G : ℕ} {target : Fin G → Clause n} {core : Finset (Fin G × Clause n)}
    {queried : Finset (Fin n)} (hminimal : InclusionMinimalUnsatisfiableCore target core)
    (hedges : ∀ p ∈ core, competitorOutsideTargetVars target p.2 ⊆ queried) :
    (polarityCoreQueryIncidences target core queried).card ≤
      2 ^ queried.card * queried.card := by
  exact (polarityCoreQueryIncidences_card_le_mul target core queried).trans
    (Nat.mul_le_mul_right queried.card
      (hminimal.card_le_two_pow_queried hedges))

/-! ### Joint target choice is not generically sufficient -/

/-- Once a DNF already contains a satisfied term, its canonical tree is the true leaf for every
fuel budget.  This local helper keeps the complementary-singleton calculation below independent
of the remaining fuel after its only possible query. -/
private theorem canonicalDT_eq_leaf_true_of_anyTermSat {n : ℕ}
    (cs : List (Clause n)) (fuel : ℕ) (sigma : Restriction n)
    (hsat : SwitchingCounting.anyTermSat cs sigma = true) :
    canonicalDT cs fuel sigma = BoolDecisionTree.leaf true := by
  cases fuel <;> simp [canonicalDT, hsat]

/-- A complementary pair of singleton terms is always canonically shallow.  If its variable is
fixed, one singleton is already satisfied.  If it is live, the canonical procedure queries it
once and both children immediately satisfy one of the two terms. -/
theorem complementarySingleton_canonicalDT_depth_le {n : ℕ} (i : Fin n)
    (fuel : ℕ) (sigma : Restriction n) :
    (canonicalDT [⟨[Rung4Literal.pos i]⟩, ⟨[Rung4Literal.neg i]⟩]
      fuel sigma).depth ≤ 1 := by
  cases h : sigma i with
  | none =>
      cases fuel with
      | zero => exact (canonicalDT_depth_le _ 0 _).trans (by omega)
      | succ fuel =>
          have hfalse : SwitchingCounting.anyTermSat
              [⟨[Rung4Literal.pos i]⟩, ⟨[Rung4Literal.neg i]⟩]
              (fixVar sigma i false) = true := by
            simp [SwitchingCounting.anyTermSat, SwitchingCounting.termSat,
              Depth3.litTrue, Depth3.litFixedVal, fixVar]
          have htrue : SwitchingCounting.anyTermSat
              [⟨[Rung4Literal.pos i]⟩, ⟨[Rung4Literal.neg i]⟩]
              (fixVar sigma i true) = true := by
            simp [SwitchingCounting.anyTermSat, SwitchingCounting.termSat,
              Depth3.litTrue, Depth3.litFixedVal, fixVar]
          have hleafFalse := canonicalDT_eq_leaf_true_of_anyTermSat
            [⟨[Rung4Literal.pos i]⟩, ⟨[Rung4Literal.neg i]⟩] fuel _ hfalse
          have hleafTrue := canonicalDT_eq_leaf_true_of_anyTermSat
            [⟨[Rung4Literal.pos i]⟩, ⟨[Rung4Literal.neg i]⟩] fuel _ htrue
          simp [canonicalDT, SwitchingCounting.anyTermSat,
            SwitchingCounting.termSat, SwitchingCounting.activeTerm,
            SwitchingCounting.termFalsified, SwitchingCounting.freeLits,
            Depth3.litFree, Depth3.litTrue, Depth3.litFixedVal,
            SwitchingCounting.litFalse, litVar, fixVar, h]
          simp only [BoolDecisionTree.depth]
          change max
            (canonicalDT [⟨[Rung4Literal.pos i]⟩, ⟨[Rung4Literal.neg i]⟩]
              fuel (fixVar sigma i false)).depth
            (canonicalDT [⟨[Rung4Literal.pos i]⟩, ⟨[Rung4Literal.neg i]⟩]
              fuel (fixVar sigma i true)).depth + 1 ≤ 1
          rw [hleafFalse, hleafTrue]
          simp
  | some b =>
      apply (congrArg BoolDecisionTree.depth
        (canonicalDT_eq_leaf_true_of_anyTermSat
          [⟨[Rung4Literal.pos i]⟩, ⟨[Rung4Literal.neg i]⟩] fuel _ (by
            cases b <;> simp [SwitchingCounting.anyTermSat,
              SwitchingCounting.termSat, Depth3.litTrue, Depth3.litFixedVal, h]))).le.trans
      simp

/-- The smallest clean gate exhibiting an unavoidable target-support conflict: whichever
singleton is preserved, the opposite-polarity singleton competitor uses the same variable. -/
def oppositeSingletonGate : List (Clause 1) :=
  [⟨[Rung4Literal.pos 0]⟩, ⟨[Rung4Literal.neg 0]⟩]

def oppositeSingletonFamily : Fin 1 → List (Clause 1) :=
  fun _ => oppositeSingletonGate

/-- The obstruction already satisfies the local syntactic conditions available at this frontier. -/
theorem oppositeSingletonGate_nodup_width_one :
    oppositeSingletonGate.Nodup ∧
      ∀ T ∈ oppositeSingletonGate, T.lits.Nodup ∧ T.lits.length = 1 := by
  decide

/-- Even choosing the target jointly with the orientation assignment does not guarantee an
isolation selection under the current hypotheses.  This width-one, duplicate-free one-gate
family has no admissible target: preserving either singleton protects its only variable, while
the other singleton can be falsified only by fixing that protected variable. -/
theorem oppositeSingleton_no_joint_target_isolation :
    ¬ ∃ target : Fin 1 → Clause 1,
      (∀ g, target g ∈ oppositeSingletonFamily g) ∧
        ∃ selected, GloballyCompatibleIsolationSelection
          oppositeSingletonFamily target (fun g => g) selected := by
  rintro ⟨target, hmem, selected, hselection⟩
  have ht : target 0 = ⟨[Rung4Literal.pos 0]⟩ ∨
      target 0 = ⟨[Rung4Literal.neg 0]⟩ := by
    simpa [oppositeSingletonFamily, oppositeSingletonGate] using hmem 0
  rcases ht with ht | ht
  · have hbad := hselection.2.2 (0 : Fin 1) ⟨[Rung4Literal.neg 0]⟩
      (by simp [oppositeSingletonFamily, oppositeSingletonGate]) (by simp [ht])
    obtain ⟨ell, hellSelected, hellMem⟩ := hbad
    simp only [List.mem_singleton] at hellMem
    subst ell
    exact hselection.2.1 (Rung4Literal.neg 0) hellSelected 0
      (Rung4Literal.pos 0) (by simpa [ht]) rfl
  · have hbad := hselection.2.2 (0 : Fin 1) ⟨[Rung4Literal.pos 0]⟩
      (by simp [oppositeSingletonFamily, oppositeSingletonGate]) (by simp [ht])
    obtain ⟨ell, hellSelected, hellMem⟩ := hbad
    simp only [List.mem_singleton] at hellMem
    subst ell
    exact hselection.2.1 (Rung4Literal.pos 0) hellSelected 0
      (Rung4Literal.neg 0) (by simpa [ht]) rfl

/-- The isolation counterexample is nevertheless not a bad multi-switching instance at residual
depth one.  The root restriction itself is a zero-query common trunk, and the sole gate is already
shallow by `complementarySingleton_canonicalDT_depth_le`.  Thus isolation failure must be
stratified by residual canonical depth before it can obstruct the switching conclusion. -/
theorem oppositeSingletonFamily_commonShallowAt_one (fuel trunkDepth : ℕ)
    (sigma : Restriction 1) :
    CommonShallowAt oppositeSingletonFamily fuel sigma trunkDepth 1 := by
  refine ⟨CommonTree.leaf sigma, by simp [CommonTree.depth], ?_⟩
  intro x hx
  refine ⟨?_, hx, ?_⟩
  · intro v b hv
    exact hv
  · intro g
    fin_cases g
    change (canonicalDT oppositeSingletonGate fuel sigma).depth ≤ 1
    simpa [oppositeSingletonGate] using
      (show (canonicalDT
        [⟨[Rung4Literal.pos (0 : Fin 1)]⟩, ⟨[Rung4Literal.neg 0]⟩]
        fuel sigma).depth ≤ 1 from by
          exact complementarySingleton_canonicalDT_depth_le 0 fuel sigma)

/-! ### A genuinely deep nonempty-edge polarity obstruction -/

/-- A three-term normalized gate in which the first term protects coordinate zero, while the
two remaining terms expose opposite singleton outside edges on coordinate one.  Semantically it
is the expansion `x₀ ∨ (¬x₀ ∧ x₁) ∨ (¬x₀ ∧ ¬x₁)`. -/
def deepPolarityCycleGate : List (Clause 2) :=
  [⟨[Rung4Literal.pos 0]⟩,
   ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1]⟩,
   ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1]⟩]

def deepPolarityCycleFamily : Fin 1 → List (Clause 2) :=
  fun _ => deepPolarityCycleGate

def deepPolarityCycleTarget : Fin 1 → Clause 2 :=
  fun _ => ⟨[Rung4Literal.pos 0]⟩

/-- The example is duplicate-free, has no repeated variable inside a term, and has width at most
two. -/
theorem deepPolarityCycleGate_normalized :
    deepPolarityCycleGate.Nodup ∧
      ∀ T ∈ deepPolarityCycleGate,
        (T.lits.map litVar).Nodup ∧ T.lits.length ≤ 2 := by
  decide

/-- No term is removed by inclusion-minimal normalization. -/
theorem deepPolarityCycleGate_inclusionMinimal :
    ∀ T ∈ deepPolarityCycleGate, InclusionMinimalIn deepPolarityCycleGate T := by
  simp [deepPolarityCycleGate, InclusionMinimalIn]

/-- The two proper competitors have exact nonempty outside-support edges.  Thus this example
cannot be charged to the empty-edge selector used by the exhaustive square. -/
theorem deepPolarityCycle_exact_outside_edges :
    competitorOutsideTargetVars deepPolarityCycleTarget
        ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1]⟩ = {1} ∧
      competitorOutsideTargetVars deepPolarityCycleTarget
        ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1]⟩ = {1} := by
  decide

/-- Every proper competitor edge is nonempty for the displayed preserved target. -/
theorem deepPolarityCycle_all_competitor_edges_nonempty :
    ∀ U ∈ deepPolarityCycleGate, U ≠ deepPolarityCycleTarget 0 →
      (competitorOutsideTargetVars deepPolarityCycleTarget U).Nonempty := by
  intro U hU hne
  simp [deepPolarityCycleGate] at hU
  rcases hU with hU | hU | hU
  · exact (hne hU).elim
  · subst U
    rw [deepPolarityCycle_exact_outside_edges.1]
    simp
  · subst U
    rw [deepPolarityCycle_exact_outside_edges.2]
    simp

/-- Despite having no empty competitor edge, the family has no compatible isolation selection
for the displayed target: the two outside singleton edges force opposite falsifying values on
coordinate one. -/
theorem deepPolarityCycle_no_target_isolation :
    ¬ ∃ selected, GloballyCompatibleIsolationSelection deepPolarityCycleFamily
      deepPolarityCycleTarget (fun g => g) selected := by
  rintro ⟨selected, hselection⟩
  have hpos := hselection.2.2 (0 : Fin 1)
    ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1]⟩
    (by simp [deepPolarityCycleFamily, deepPolarityCycleGate])
    (by simp [deepPolarityCycleTarget])
  have hneg := hselection.2.2 (0 : Fin 1)
    ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1]⟩
    (by simp [deepPolarityCycleFamily, deepPolarityCycleGate])
    (by simp [deepPolarityCycleTarget])
  obtain ⟨ellPos, hellPosSelected, hellPosMem⟩ := hpos
  obtain ⟨ellNeg, hellNegSelected, hellNegMem⟩ := hneg
  have hposOne : Rung4Literal.pos (1 : Fin 2) ∈ selected := by
    have hell : ellPos = Rung4Literal.neg 0 ∨ ellPos = Rung4Literal.pos 1 := by
      simpa using hellPosMem
    rcases hell with rfl | rfl
    · exact (hselection.2.1 (Rung4Literal.neg 0) hellPosSelected 0
        (Rung4Literal.pos 0) (by simp [deepPolarityCycleTarget]) rfl).elim
    · exact hellPosSelected
  have hnegOne : Rung4Literal.neg (1 : Fin 2) ∈ selected := by
    have hell : ellNeg = Rung4Literal.neg 0 ∨ ellNeg = Rung4Literal.neg 1 := by
      simpa using hellNegMem
    rcases hell with rfl | rfl
    · exact (hselection.2.1 (Rung4Literal.neg 0) hellNegSelected 0
        (Rung4Literal.pos 0) (by simp [deepPolarityCycleTarget]) rfl).elim
    · exact hellNegSelected
  have hpol := hselection.1 (Rung4Literal.pos 1) hposOne
    (Rung4Literal.neg 1) hnegOne rfl
  simpa [falValue] using hpol

/-- The canonical procedure queries both coordinates at the all-free root.  Hence the polarity
obstruction is genuinely beyond residual depth one rather than another shallow singleton pair. -/
theorem deepPolarityCycleGate_canonicalDT_depth_eq_two :
    (canonicalDT deepPolarityCycleGate 2 (fun _ => none)).depth = 2 := by
  decide

theorem deepPolarityCycleGate_queriedVars_eq_univ :
    queriedVars (canonicalDT deepPolarityCycleGate 2 (fun _ => none)) = Finset.univ := by
  decide

/-- The two proper terms, indexed by the sole preserved target, form the polarity core of the
depth-two example. -/
def deepPolarityCycleCore : Finset (Fin 1 × Clause 2) :=
  {(0, ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1]⟩),
   (0, ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1]⟩)}

theorem deepPolarityCycleCore_card : deepPolarityCycleCore.card = 2 := by
  decide

theorem deepPolarityCycleCore_card_le_gate_length :
    deepPolarityCycleCore.card ≤ deepPolarityCycleGate.length := by
  decide

/-- The concrete two-clause obstruction satisfies the general polarity-cycle interface.  Both
outside edges are the nonempty singleton `{1}`, that coordinate is canonically queried, and no
Boolean orientation can hit both clauses because they demand opposite values there. -/
theorem deepPolarityCycle_polarityCycleValid :
    PolarityCycleValid deepPolarityCycleFamily deepPolarityCycleTarget (fun g => g)
      (queriedVars (canonicalDT deepPolarityCycleGate 2 (fun _ => none)))
      deepPolarityCycleCore := by
  rw [deepPolarityCycleGate_queriedVars_eq_univ]
  refine ⟨by decide, by decide, ?_⟩
  simp [HitsOutsideCompetitorCore, deepPolarityCycleCore,
    deepPolarityCycleTarget, compatibleIsolationTargetVars, falValue, litVar]

/-- The reusable soundness theorem recovers the concrete isolation obstruction from its finite
unsatisfiable polarity core. -/
theorem deepPolarityCycle_no_target_isolation_via_cycle :
    ¬ ∃ selected, GloballyCompatibleIsolationSelection deepPolarityCycleFamily
      deepPolarityCycleTarget (fun g => g) selected :=
  deepPolarityCycle_polarityCycleValid.not_exists_globallyCompatibleIsolationSelection

/-- The compressed cycle certificate records the two conflicting competitors at their shared
queried coordinate. -/
def deepPolarityCycleIncidences : Finset (Fin 3 × Fin 2) :=
  {(1, 1), (2, 1)}

/-- The polarity-cycle certificate has exactly two incidences, hence is already linear in the
three-term gate size. -/
theorem deepPolarityCycleIncidences_card : deepPolarityCycleIncidences.card = 2 := by
  decide

theorem deepPolarityCycleIncidences_card_le_gate_length :
    deepPolarityCycleIncidences.card ≤ deepPolarityCycleGate.length := by
  decide

/-- Every retained incidence uses an actually queried coordinate, and the two retained outside
literals demand opposite falsifying values there.  This is the semantic validity check missing
from the bare cardinality bound. -/
theorem deepPolarityCycleIncidences_valid :
    (∀ p ∈ deepPolarityCycleIncidences,
        p.2 ∈ queriedVars (canonicalDT deepPolarityCycleGate 2 (fun _ => none))) ∧
      falValue (Rung4Literal.pos (1 : Fin 2)) ≠
        falValue (Rung4Literal.neg (1 : Fin 2)) := by
  decide

/-! ### Isolation failure persists for a genuinely deep gate -/

/-- The exhaustive two-bit DNF, in canonical lexicographic term order.  Every target term uses
both variables, while the four terms collectively realize every polarity pattern. -/
def exhaustiveTwoBitGate : List (Clause 2) :=
  [⟨[Rung4Literal.pos 0, Rung4Literal.pos 1]⟩,
   ⟨[Rung4Literal.pos 0, Rung4Literal.neg 1]⟩,
   ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1]⟩,
   ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1]⟩]

def exhaustiveTwoBitFamily : Fin 1 → List (Clause 2) :=
  fun _ => exhaustiveTwoBitGate

/-- The deep conflict example has no duplicate terms, and every term uses two distinct
variables. -/
theorem exhaustiveTwoBitGate_nodup_width_two :
    exhaustiveTwoBitGate.Nodup ∧
      ∀ T ∈ exhaustiveTwoBitGate,
        (T.lits.map litVar).Nodup ∧ T.lits.length = 2 := by
  decide

/-- On the fully live square with enough fuel, the exhaustive gate's canonical tree really has
depth two.  Thus it lies beyond the residual-depth-one cutoff at the root. -/
theorem exhaustiveTwoBitGate_canonicalDT_depth_eq_two :
    (canonicalDT exhaustiveTwoBitGate 2 (fun _ => none)).depth = 2 := by
  decide

/-- With no common-trunk query available, the fully live square is genuinely bad at residual
depth one.  This connects the depth computation to the exact `CommonShallowAt` interface. -/
theorem exhaustiveTwoBitFamily_not_commonShallowAt_one :
    ¬ CommonShallowAt exhaustiveTwoBitFamily 2 (fun _ => none) 0 1 := by
  rintro ⟨trunk, hdepth, hleaf⟩
  cases trunk with
  | query i lo hi => simp [CommonTree.depth] at hdepth
  | leaf tau =>
      have htau : tau = fun _ => none := by
        funext i
        cases htaui : tau i with
        | none => rfl
        | some b =>
            let x : Fin 2 → Bool := Function.update (fun _ => false) i (!b)
            have hx : Rung4Restriction.Extends (fun _ => none) x := by
              intro j v hj
              simp at hj
            obtain ⟨_, hagree, _⟩ := hleaf x hx
            have hib := hagree i b htaui
            simp [x] at hib
      let x : Fin 2 → Bool := fun _ => false
      have hx : Rung4Restriction.Extends (fun _ => none) x := by
        intro i b hi
        simp at hi
      obtain ⟨_, _, hshallow⟩ := hleaf x hx
      have hgate := hshallow 0
      rw [htau] at hgate
      change (canonicalDT exhaustiveTwoBitGate 2 (fun _ => none)).depth ≤ 1 at hgate
      rw [exhaustiveTwoBitGate_canonicalDT_depth_eq_two] at hgate
      omega

/-- Fixed-shell form: the fully live two-variable restriction belongs to the exact bad event with
zero trunk budget and residual depth one. -/
theorem allFreeTwo_mem_exhaustiveTwoBit_commonShallowBad_one :
    (fun _ => none) ∈ commonShallowBad exhaustiveTwoBitFamily 2 2 0 1 := by
  rw [mem_commonShallowBad]
  refine ⟨?_, exhaustiveTwoBitFamily_not_commonShallowAt_one⟩
  decide

/-- Removing gates already shallow at depth one does not rescue generic target isolation.  Every
possible target in the exhaustive square protects both coordinates, whereas isolating it would
have to falsify a distinct competitor using one of those same coordinates. -/
theorem exhaustiveTwoBit_no_joint_target_isolation :
    ¬ ∃ target : Fin 1 → Clause 2,
      (∀ g, target g ∈ exhaustiveTwoBitFamily g) ∧
        ∃ selected, GloballyCompatibleIsolationSelection
          exhaustiveTwoBitFamily target (fun g => g) selected := by
  rintro ⟨target, hmem, selected, hselection⟩
  have ht : target 0 = ⟨[Rung4Literal.pos 0, Rung4Literal.pos 1]⟩ ∨
      target 0 = ⟨[Rung4Literal.pos 0, Rung4Literal.neg 1]⟩ ∨
      target 0 = ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1]⟩ ∨
      target 0 = ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1]⟩ := by
    simpa [exhaustiveTwoBitFamily, exhaustiveTwoBitGate] using hmem 0
  rcases ht with ht | ht | ht | ht
  · have hbad := hselection.2.2 (0 : Fin 1)
      ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1]⟩
      (by simp [exhaustiveTwoBitFamily, exhaustiveTwoBitGate]) (by simp [ht])
    obtain ⟨ell, hellSelected, hellMem⟩ := hbad
    simp at hellMem
    rcases hellMem with rfl | rfl
    · exact hselection.2.1 (Rung4Literal.neg 0) hellSelected 0
        (Rung4Literal.pos 0) (by simp [ht]) rfl
    · exact hselection.2.1 (Rung4Literal.neg 1) hellSelected 0
        (Rung4Literal.pos 1) (by simp [ht]) rfl
  · have hbad := hselection.2.2 (0 : Fin 1)
      ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1]⟩
      (by simp [exhaustiveTwoBitFamily, exhaustiveTwoBitGate]) (by simp [ht])
    obtain ⟨ell, hellSelected, hellMem⟩ := hbad
    simp at hellMem
    rcases hellMem with rfl | rfl
    · exact hselection.2.1 (Rung4Literal.neg 0) hellSelected 0
        (Rung4Literal.pos 0) (by simp [ht]) rfl
    · exact hselection.2.1 (Rung4Literal.pos 1) hellSelected 0
        (Rung4Literal.neg 1) (by simp [ht]) rfl
  · have hbad := hselection.2.2 (0 : Fin 1)
      ⟨[Rung4Literal.pos 0, Rung4Literal.neg 1]⟩
      (by simp [exhaustiveTwoBitFamily, exhaustiveTwoBitGate]) (by simp [ht])
    obtain ⟨ell, hellSelected, hellMem⟩ := hbad
    simp at hellMem
    rcases hellMem with rfl | rfl
    · exact hselection.2.1 (Rung4Literal.pos 0) hellSelected 0
        (Rung4Literal.neg 0) (by simp [ht]) rfl
    · exact hselection.2.1 (Rung4Literal.neg 1) hellSelected 0
        (Rung4Literal.pos 1) (by simp [ht]) rfl
  · have hbad := hselection.2.2 (0 : Fin 1)
      ⟨[Rung4Literal.pos 0, Rung4Literal.pos 1]⟩
      (by simp [exhaustiveTwoBitFamily, exhaustiveTwoBitGate]) (by simp [ht])
    obtain ⟨ell, hellSelected, hellMem⟩ := hbad
    simp at hellMem
    rcases hellMem with rfl | rfl
    · exact hselection.2.1 (Rung4Literal.pos 0) hellSelected 0
        (Rung4Literal.neg 0) (by simp [ht]) rfl
    · exact hselection.2.1 (Rung4Literal.pos 1) hellSelected 0
        (Rung4Literal.neg 1) (by simp [ht]) rfl

/-! ### Exact local incidence count for the deep isolation obstruction -/

/-- Canonical indexing of the four exhaustive-square terms. -/
def exhaustiveTwoBitTerm (j : Fin 4) : Clause 2 :=
  exhaustiveTwoBitGate.get (Fin.cast (by decide) j)

/-- Target--competitor--query incidences in the exhaustive square.  An incidence records a
distinct ordered pair of terms and a variable that occurs in both terms and in the canonical
tree's queried-variable set. -/
def exhaustiveTwoBitConflictIncidences : Finset ((Fin 4 × Fin 4) × Fin 2) :=
  Finset.univ.filter fun p =>
    p.1.1 ≠ p.1.2 ∧
      p.2 ∈ SwitchingCounting.clauseVars (exhaustiveTwoBitTerm p.1.1) ∧
      p.2 ∈ SwitchingCounting.clauseVars (exhaustiveTwoBitTerm p.1.2) ∧
      p.2 ∈ queriedVars (canonicalDT exhaustiveTwoBitGate 2 (fun _ => none))

/-- The canonical tree queries exactly the two coordinates appearing in every exhaustive
minterm. -/
theorem exhaustiveTwoBitGate_queriedVars_eq_univ :
    queriedVars (canonicalDT exhaustiveTwoBitGate 2 (fun _ => none)) = Finset.univ := by
  decide

/-- The local conflict-to-query incidence relation has exactly twenty-four elements: twelve
ordered target--competitor pairs, each incident to both queried coordinates. -/
theorem exhaustiveTwoBitConflictIncidences_card :
    exhaustiveTwoBitConflictIncidences.card = 24 := by
  decide

/-- Each queried coordinate receives exactly twelve conflict incidences.  This is the first exact
fiber audit for the proposed canonical-path charge: the charge exists locally, but it has already
lost the full ordered-pair multiplicity rather than a constant independent of the gate's term
count. -/
theorem exhaustiveTwoBitConflictIncidences_coordinate_fiber_card (v : Fin 2) :
    (exhaustiveTwoBitConflictIncidences.filter fun p => p.2 = v).card = 12 := by
  fin_cases v <;> decide

/-! ### Dimension-free complete-incidence multiplicity -/

/-- The off-diagonal ordered pairs from an `M`-element term index. -/
def offDiagonalTermPairs (M : ℕ) : Finset (Fin M × Fin M) :=
  Finset.univ.filter fun p => p.1 ≠ p.2

/-- There are exactly `M * (M - 1)` ordered target--competitor pairs. -/
theorem offDiagonalTermPairs_card (M : ℕ) :
    (offDiagonalTermPairs M).card = M * (M - 1) := by
  have hdiag : (Finset.univ.filter fun p : Fin M × Fin M => ¬p.1 ≠ p.2) =
      Finset.univ.image fun i : Fin M => (i, i) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_ne_iff,
      Finset.mem_image]
    constructor
    · intro h
      exact ⟨p.1, Prod.ext rfl h⟩
    · rintro ⟨i, rfl⟩
      rfl
  have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin M × Fin M))) (fun p => p.1 ≠ p.2)
  rw [hdiag] at hsplit
  have hinj : Function.Injective (fun i : Fin M => (i, i)) := fun _ _ h =>
    congrArg Prod.fst h
  rw [Finset.card_image_of_injective _ hinj] at hsplit
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hsplit
  have hcard : (offDiagonalTermPairs M).card = M * M - M := by
    unfold offDiagonalTermPairs
    omega
  rw [hcard, Nat.mul_sub_left_distrib]
  simp

/-- The complete conflict-to-query relation on `M` terms and `d` queried coordinates.  This is
the combinatorial core realized by an exhaustive-minterm gate once every term contains every
queried coordinate: it deliberately retains every distinct ordered target--competitor pair. -/
def completeConflictQueryIncidences (M d : ℕ) :
    Finset ((Fin M × Fin M) × Fin d) :=
  Finset.univ.filter fun p => p.1.1 ≠ p.1.2

theorem completeConflictQueryIncidences_eq_product (M d : ℕ) :
    completeConflictQueryIncidences M d =
      (offDiagonalTermPairs M) ×ˢ Finset.univ := by
  ext p
  simp [completeConflictQueryIncidences, offDiagonalTermPairs]

/-- The complete relation has `d` copies of the full ordered-pair multiplicity. -/
theorem completeConflictQueryIncidences_card (M d : ℕ) :
    (completeConflictQueryIncidences M d).card = M * (M - 1) * d := by
  rw [completeConflictQueryIncidences_eq_product, Finset.card_product,
    offDiagonalTermPairs_card]
  simp

/-- Projecting the complete relation to any one queried coordinate has the exact quadratic fiber
`M * (M - 1)`.  The multiplicity is therefore caused by retaining all ordered competitors, not
by the special choice `M = 4` in the exhaustive square. -/
theorem completeConflictQueryIncidences_coordinate_fiber_card
    (M d : ℕ) (v : Fin d) :
    ((completeConflictQueryIncidences M d).filter fun p => p.2 = v).card =
      M * (M - 1) := by
  have hfiber : (completeConflictQueryIncidences M d).filter (fun p => p.2 = v) =
      (offDiagonalTermPairs M) ×ˢ {v} := by
    ext p
    simp only [completeConflictQueryIncidences, offDiagonalTermPairs, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_product, Finset.mem_singleton]
  rw [hfiber, Finset.card_product, offDiagonalTermPairs_card]
  simp

/-- At the `2^d` term count of a `d`-variable exhaustive-minterm gate, every coordinate fiber of
the complete incidence relation has the expected size `2^d * (2^d - 1)`. -/
theorem exhaustiveMinterm_completeConflict_coordinate_fiber_card
    (d : ℕ) (v : Fin d) :
    ((completeConflictQueryIncidences (2 ^ d) d).filter fun p => p.2 = v).card =
      2 ^ d * (2 ^ d - 1) := by
  exact completeConflictQueryIncidences_coordinate_fiber_card (2 ^ d) d v

/-! ### One-witness-per-target certificate compression -/

/-- A selective conflict certificate retains exactly one chosen competitor and one chosen queried
coordinate for each target.  Semantic validity is deliberately kept separate: the two functions
below are the payload of a selector, while later hypotheses must prove that the chosen competitor
and coordinate really witness the relevant conflict. -/
def selectiveConflictQueryIncidences (M d : ℕ)
    (competitor : Fin M → Fin M) (coordinate : Fin M → Fin d) :
    Finset ((Fin M × Fin M) × Fin d) :=
  Finset.univ.image fun i => ((i, competitor i), coordinate i)

/-- Retaining one certificate per target has exactly `M` incidences.  Injectivity is free because
the target remains the first component of every certificate. -/
theorem selectiveConflictQueryIncidences_card (M d : ℕ)
    (competitor : Fin M → Fin M) (coordinate : Fin M → Fin d) :
    (selectiveConflictQueryIncidences M d competitor coordinate).card = M := by
  rw [selectiveConflictQueryIncidences, Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact congrArg (fun p => p.1.1) h

/-- Consequently every coordinate fiber of a one-witness-per-target certificate is at most
linear in the term count, independently of the number of queried coordinates. -/
theorem selectiveConflictQueryIncidences_coordinate_fiber_card_le
    (M d : ℕ) (competitor : Fin M → Fin M) (coordinate : Fin M → Fin d)
    (v : Fin d) :
    ((selectiveConflictQueryIncidences M d competitor coordinate).filter
      fun p => p.2 = v).card ≤ M := by
  exact (Finset.card_filter_le _ _).trans_eq
    (selectiveConflictQueryIncidences_card M d competitor coordinate)

/-- If every selected competitor is distinct from its target, the selective certificate is a
subrelation of the complete conflict-query relation.  Thus the linear count is genuine
compression of the previously audited quadratic relation; what remains is to justify semantic
conflict validity for a selector arising from a gate. -/
theorem selectiveConflictQueryIncidences_subset_complete
    (M d : ℕ) (competitor : Fin M → Fin M) (coordinate : Fin M → Fin d)
    (hne : ∀ i, competitor i ≠ i) :
    selectiveConflictQueryIncidences M d competitor coordinate ⊆
      completeConflictQueryIncidences M d := by
  intro p hp
  rw [selectiveConflictQueryIncidences, Finset.mem_image] at hp
  obtain ⟨i, -, rfl⟩ := hp
  rw [completeConflictQueryIncidences, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (hne i).symm⟩

/-- Semantic validity for a one-witness-per-target conflict selector.  Besides membership and
index distinctness, the chosen competitor must be a genuinely different clause whose entire
support is protected by the target.  The chosen coordinate records an actual shared support
coordinate queried by the canonical tree.  The empty outside-support edge is phrased using the
same definition as `GloballyCompatibleIsolationSelection`, so it gives an exact isolation
obstruction rather than merely a syntactic overlap. -/
def SelectiveConflictSelectorValid {n M : ℕ} (gate : List (Clause n))
    (term : Fin M → Clause n) (fuel : ℕ) (sigma : Restriction n)
    (competitor : Fin M → Fin M) (coordinate : Fin M → Fin n) : Prop :=
  (∀ i, term i ∈ gate) ∧
    ∀ i,
      competitor i ≠ i ∧
      term (competitor i) ≠ term i ∧
      competitorOutsideTargetVars (fun _ : Fin 1 => term i)
        (term (competitor i)) = ∅ ∧
      coordinate i ∈ SwitchingCounting.clauseVars (term i) ∧
      coordinate i ∈ SwitchingCounting.clauseVars (term (competitor i)) ∧
      coordinate i ∈ queriedVars (canonicalDT gate fuel sigma)

/-- On the exhaustive square, choose the bitwise-opposite minterm as competitor. -/
def exhaustiveTwoBitSelectiveCompetitor (i : Fin 4) : Fin 4 :=
  ⟨3 - i.val, by omega⟩

/-- One shared queried coordinate suffices for every target in the exhaustive square. -/
def exhaustiveTwoBitSelectiveCoordinate (_ : Fin 4) : Fin 2 := 0

/-- The exhaustive deep obstruction admits the desired sound linear certificate.  Hence the
semantic predicate is inhabited in the first genuinely deep model, not only countable in the
abstract. -/
theorem exhaustiveTwoBit_selectiveConflictSelectorValid :
    SelectiveConflictSelectorValid exhaustiveTwoBitGate exhaustiveTwoBitTerm 2
      (fun _ => none) exhaustiveTwoBitSelectiveCompetitor
      exhaustiveTwoBitSelectiveCoordinate := by
  constructor
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide

/-- The selected exhaustive-square incidences retain exactly four witnesses. -/
theorem exhaustiveTwoBit_selectiveConflictQueryIncidences_card :
    (selectiveConflictQueryIncidences 4 2 exhaustiveTwoBitSelectiveCompetitor
      exhaustiveTwoBitSelectiveCoordinate).card = 4 := by
  exact selectiveConflictQueryIncidences_card 4 2 _ _

/-- An empty competitor edge is a complete failure certificate for the compatible-selection
branch: hitting that competitor would require selecting a variable used by a preserved target. -/
theorem not_exists_globallyCompatibleIsolationSelection_of_outsideTargetVars_eq_empty
    {n G H : ℕ} {large : Fin H → List (Clause n)}
    {target : Fin G → Clause n} {e : Fin G → Fin H}
    {g : Fin G} {U : Clause n} (hUmem : U ∈ large (e g))
    (hUne : U ≠ target g) (hempty : competitorOutsideTargetVars target U = ∅) :
    ¬ ∃ selected, GloballyCompatibleIsolationSelection large target e selected := by
  rintro ⟨selected, hselection⟩
  obtain ⟨ell, hellSelected, hellU⟩ := hselection.2.2 g U hUmem hUne
  have hvarTarget : litVar ell ∈ compatibleIsolationTargetVars target := by
    by_contra hnot
    have houtside : litVar ell ∈ competitorOutsideTargetVars target U := by
      rw [mem_competitorOutsideTargetVars]
      exact ⟨⟨ell, hellU, rfl⟩, hnot⟩
    rw [hempty] at houtside
    simp at houtside
  rw [mem_compatibleIsolationTargetVars] at hvarTarget
  obtain ⟨g', t, ht, heq⟩ := hvarTarget
  exact hselection.2.1 ell hellSelected g' t ht heq.symm

/-- A valid selector certifies failure of the existing compatible-isolation interface separately
for every possible target.  This is the semantic bridge missing from the bare linear incidence
count: its empty outside-support edge is consumed directly by the established obstruction lemma. -/
theorem SelectiveConflictSelectorValid.no_singleton_target_isolation
    {n M : ℕ} {gate : List (Clause n)} {term : Fin M → Clause n}
    {fuel : ℕ} {sigma : Restriction n} {competitor : Fin M → Fin M}
    {coordinate : Fin M → Fin n}
    (hvalid : SelectiveConflictSelectorValid gate term fuel sigma competitor coordinate)
    (i : Fin M) :
    ¬ ∃ selected, GloballyCompatibleIsolationSelection
      (fun _ : Fin 1 => gate) (fun _ : Fin 1 => term i) (fun g => g) selected := by
  apply not_exists_globallyCompatibleIsolationSelection_of_outsideTargetVars_eq_empty
    (g := (0 : Fin 1)) (U := term (competitor i))
  · exact hvalid.1 (competitor i)
  · exact hvalid.2 i |>.2.1
  · exact hvalid.2 i |>.2.2.1

/-- Local inclusion-minimality does not prevent the empty-edge obstruction.  When it occurs,
some literal outside the chosen target is forced to share its variable with (possibly another)
preserved target.  This is the first explicit target-support hitting certificate in the negative
branch of the proposed dichotomy. -/
theorem exists_targetSupport_conflict_of_inclusionMinimal_of_outsideTargetVars_eq_empty
    {n G H : ℕ} {large : Fin H → List (Clause n)}
    {target : Fin G → Clause n} {e : Fin G → Fin H}
    {g : Fin G} {U : Clause n} (hmin : InclusionMinimalIn (large (e g)) (target g))
    (hUmem : U ∈ large (e g)) (hUne : U ≠ target g)
    (hempty : competitorOutsideTargetVars target U = ∅) :
    ∃ ell ∈ U.lits, ell ∉ (target g).lits ∧
      ∃ g' t, t ∈ (target g').lits ∧ litVar t = litVar ell := by
  obtain ⟨ell, hellU, hellOutside⟩ :=
    exists_outside_literal_of_inclusionMinimal hmin hUmem hUne
  refine ⟨ell, hellU, hellOutside, ?_⟩
  have hvarTarget : litVar ell ∈ compatibleIsolationTargetVars target := by
    by_contra hnot
    have houtside : litVar ell ∈ competitorOutsideTargetVars target U := by
      rw [mem_competitorOutsideTargetVars]
      exact ⟨⟨ell, hellU, rfl⟩, hnot⟩
    rw [hempty] at houtside
    simp at houtside
  rwa [mem_compatibleIsolationTargetVars] at hvarTarget

/-- Global compatibility makes the complete target support live in the isolation base. -/
theorem compatibleIsolationTargetVars_subset_freeVars {n G H : ℕ}
    {large : Fin H → List (Clause n)} {target : Fin G → Clause n}
    {e : Fin G → Fin H} {selected : List (Rung4Literal n)}
    (hselection : GloballyCompatibleIsolationSelection large target e selected) :
    compatibleIsolationTargetVars target ⊆
      freeVars (compatibleIsolationRestriction selected) := by
  intro i hi
  rw [mem_compatibleIsolationTargetVars] at hi
  obtain ⟨g, t, ht, rfl⟩ := hi
  rw [mem_freeVars, compatibleIsolationRestriction]
  split
  · next h =>
      obtain ⟨ell, hell, heq⟩ := h
      exact False.elim (hselection.2.1 ell hell g t ht heq)
  · rfl

/-- Extend a base restriction by leaving exactly `keep` live and assigning every other formerly
live coordinate `false`.  Existing fixed values are retained.  This deterministic representative
is enough to separate shell feasibility from the later counting problem. -/
def keepFreeExtension {n : ℕ} (base : Restriction n) (keep : Finset (Fin n)) :
    Restriction n := fun i =>
  if i ∈ keep then none else
    match base i with
    | some b => some b
    | none => some false

/-- The deterministic extension has precisely the requested live-coordinate set. -/
theorem freeVars_keepFreeExtension {n : ℕ} (base : Restriction n)
    (keep : Finset (Fin n)) :
    freeVars (keepFreeExtension base keep) = keep := by
  ext i
  rw [mem_freeVars]
  by_cases hi : i ∈ keep
  · simp [keepFreeExtension, hi]
  · simp only [keepFreeExtension, hi, if_false]
    cases base i <;> simp

/-- Hence its shell is exactly the cardinality of the requested live set. -/
theorem stars_keepFreeExtension {n : ℕ} (base : Restriction n)
    (keep : Finset (Fin n)) :
    stars (keepFreeExtension base keep) = keep.card := by
  rw [stars, freeVars_keepFreeExtension]

/-- Choosing `keep` among the base-live coordinates makes the construction a genuine restriction
extension. -/
theorem restrictionExtends_keepFreeExtension {n : ℕ} (base : Restriction n)
    {keep : Finset (Fin n)} (hkeep : keep ⊆ freeVars base) :
    RestrictionExtends base (keepFreeExtension base keep) := by
  intro i b hib
  have hnot : i ∉ keep := by
    intro hi
    have hfree := hkeep hi
    rw [mem_freeVars, hib] at hfree
    simp at hfree
  simp [keepFreeExtension, hnot, hib]

/-- If every target coordinate is retained in `keep`, all targets remain live after extension. -/
theorem keepFreeExtension_target_live {n G : ℕ} (base : Restriction n)
    (target : Fin G → Clause n) {keep : Finset (Fin n)}
    (htarget : ∀ g, ∀ t ∈ (target g).lits, litVar t ∈ keep) (g : Fin G) :
    termFalsified (keepFreeExtension base keep) (target g) = false := by
  rw [termFalsified, List.any_eq_false]
  intro t ht
  have hnone : keepFreeExtension base keep (litVar t) = none := by
    simp [keepFreeExtension, htarget g t ht]
  cases t <;> simp [litFalse, Depth3.litFixedVal, litVar] at hnone ⊢ <;> simp_all

/-- Every selected literal is false under the induced restriction. -/
theorem compatibleIsolationRestriction_litFalse {n : ℕ}
    {selected : List (Rung4Literal n)}
    (hconsistent : ∀ ell₁ ∈ selected, ∀ ell₂ ∈ selected,
      litVar ell₁ = litVar ell₂ → falValue ell₁ = falValue ell₂)
    {ell : Rung4Literal n} (hell : ell ∈ selected) :
    litFalse (compatibleIsolationRestriction selected) ell = true := by
  have hex : ∃ ell' ∈ selected, litVar ell' = litVar ell := ⟨ell, hell, rfl⟩
  have hwmem : Classical.choose hex ∈ selected := (Classical.choose_spec hex).1
  have hwvar : litVar (Classical.choose hex) = litVar ell :=
    (Classical.choose_spec hex).2
  have hvalue : falValue (Classical.choose hex) = falValue ell :=
    hconsistent (Classical.choose hex) hwmem ell hell hwvar
  have hfixed : compatibleIsolationRestriction selected (litVar ell) =
      some (falValue ell) := by
    rw [compatibleIsolationRestriction, dif_pos hex, hvalue]
  cases ell <;> simp [litFalse, Depth3.litFixedVal, falValue, litVar] at hfixed ⊢ <;>
    simp_all

/-- Target variables remain free because compatibility excludes every selected variable from
every target. -/
theorem compatibleIsolationRestriction_target_none {n G : ℕ}
    {target : Fin G → Clause n} {selected : List (Rung4Literal n)}
    (havoid : ∀ ell ∈ selected, ∀ g, ∀ t ∈ (target g).lits,
      litVar ell ≠ litVar t)
    (g : Fin G) {t : Rung4Literal n} (ht : t ∈ (target g).lits) :
    compatibleIsolationRestriction selected (litVar t) = none := by
  rw [compatibleIsolationRestriction]
  split
  · next h =>
      obtain ⟨ell, hell, heq⟩ := h
      exact False.elim (havoid ell hell g t ht heq)
  · rfl

/-- Every target survives the compatible-selection restriction. -/
theorem compatibleIsolationRestriction_target_live {n G : ℕ}
    {target : Fin G → Clause n} {selected : List (Rung4Literal n)}
    (havoid : ∀ ell ∈ selected, ∀ g, ∀ t ∈ (target g).lits,
      litVar ell ≠ litVar t) (g : Fin G) :
    termFalsified (compatibleIsolationRestriction selected) (target g) = false := by
  rw [termFalsified, List.any_eq_false]
  intro t ht
  have hnone := compatibleIsolationRestriction_target_none havoid g ht
  cases t <;> simp [litFalse, Depth3.litFixedVal, litVar] at hnone ⊢ <;> simp_all

/-- Every competitor is falsified when it contains a selected literal. -/
theorem compatibleIsolationRestriction_competitor_falsified {n : ℕ}
    {selected : List (Rung4Literal n)}
    (hconsistent : ∀ ell₁ ∈ selected, ∀ ell₂ ∈ selected,
      litVar ell₁ = litVar ell₂ → falValue ell₁ = falValue ell₂)
    {U : Clause n} (hhit : ∃ ell ∈ selected, ell ∈ U.lits) :
    termFalsified (compatibleIsolationRestriction selected) U = true := by
  obtain ⟨ell, hell, hellU⟩ := hhit
  rw [termFalsified, List.any_eq_true]
  exact ⟨ell, hellU, compatibleIsolationRestriction_litFalse hconsistent hell⟩

/-- A compatible isolation base can be extended to every shell between the total target support
and its current star count.  This proves feasibility of a target-preserving intended shell; it
deliberately gives one canonical extension, while the exact number of such extensions remains the
next counting obligation. -/
theorem exists_shell_extension_of_globallyCompatibleIsolationSelection
    {n G H K : ℕ} (large : Fin H → List (Clause n))
    (target : Fin G → Clause n) (e : Fin G → Fin H)
    (selected : List (Rung4Literal n))
    (hselection : GloballyCompatibleIsolationSelection large target e selected)
    (targetSupport : Finset (Fin n))
    (htarget : ∀ g, ∀ t ∈ (target g).lits, litVar t ∈ targetSupport)
    (hsupport : targetSupport ⊆
      freeVars (compatibleIsolationRestriction selected))
    (hsupportK : targetSupport.card ≤ K)
    (hKstars : K ≤ stars (compatibleIsolationRestriction selected)) :
    ∃ rho : Restriction n,
      stars rho = K ∧
      RestrictionExtends (compatibleIsolationRestriction selected) rho ∧
      (∀ g, termFalsified rho (target g) = false) ∧
      (∀ g U, U ∈ large (e g) → U ≠ target g →
        termFalsified rho U = true) := by
  obtain ⟨keep, htargetKeep, hkeep, hkeepCard⟩ :=
    Finset.exists_subsuperset_card_eq hsupport hsupportK (by
      simpa [stars] using hKstars)
  let base := compatibleIsolationRestriction selected
  let rho := keepFreeExtension base keep
  have hext : RestrictionExtends base rho :=
    restrictionExtends_keepFreeExtension base hkeep
  refine ⟨rho, ?_, hext, ?_, ?_⟩
  · simpa [rho, hkeepCard] using stars_keepFreeExtension base keep
  · intro g
    apply keepFreeExtension_target_live base target
    intro g' t ht
    exact htargetKeep (htarget g' t ht)
  · intro g U hU hUne
    have hbase : termFalsified base U = true :=
      compatibleIsolationRestriction_competitor_falsified hselection.1
        (hselection.2.2 g U hU hUne)
    exact termFalsified_mono hext hbase

/-- Usable specialization with the target support computed internally.  The only shell-side
premises are the sharp interval bounds: the intended live count must contain every distinct target
variable and cannot exceed the compatible base's live count. -/
theorem exists_shell_extension_of_globallyCompatibleIsolationSelection'
    {n G H K : ℕ} (large : Fin H → List (Clause n))
    (target : Fin G → Clause n) (e : Fin G → Fin H)
    (selected : List (Rung4Literal n))
    (hselection : GloballyCompatibleIsolationSelection large target e selected)
    (htargetK : (compatibleIsolationTargetVars target).card ≤ K)
    (hKstars : K ≤ stars (compatibleIsolationRestriction selected)) :
    ∃ rho : Restriction n,
      stars rho = K ∧
      RestrictionExtends (compatibleIsolationRestriction selected) rho ∧
      (∀ g, termFalsified rho (target g) = false) ∧
      (∀ g U, U ∈ large (e g) → U ≠ target g →
        termFalsified rho U = true) := by
  apply exists_shell_extension_of_globallyCompatibleIsolationSelection
    large target e selected hselection (compatibleIsolationTargetVars target)
  · intro g t ht
    rw [mem_compatibleIsolationTargetVars]
    exact ⟨g, t, ht, rfl⟩
  · exact compatibleIsolationTargetVars_subset_freeVars hselection
  · exact htargetK
  · exact hKstars

/-! ### Exact target-preserving extension fibers -/

/-- The complete finite fiber of `K`-star extensions of `base` that keep every coordinate in
`required` live.  For the compatible-isolation application, `required` is the union of all target
supports. -/
noncomputable def targetPreservingShellExtensions {n : ℕ} (base : Restriction n)
    (required : Finset (Fin n)) (K : ℕ) : Finset (Restriction n) :=
  by
    classical
    exact Finset.univ.filter fun rho =>
      RestrictionExtends base rho ∧ stars rho = K ∧ required ⊆ freeVars rho

/-- The fixed-free-set fiber among extensions of `base`. -/
noncomputable def restrictionExtensionFreeSetFiber {n : ℕ} (base : Restriction n)
    (S : Finset (Fin n)) : Finset (Restriction n) := by
  classical
  exact Finset.univ.filter fun rho => RestrictionExtends base rho ∧ freeVars rho = S

/-- Once the final free set is prescribed inside the base-live coordinates, every consumed live
coordinate has two Boolean choices and every other coordinate is forced. -/
theorem card_restrictionExtends_freeVars_eq {n : ℕ} (base : Restriction n)
    (S : Finset (Fin n)) (hS : S ⊆ freeVars base) :
    (restrictionExtensionFreeSetFiber base S).card =
      2 ^ ((freeVars base).card - S.card) := by
  classical
  let choices : Fin n → Finset (Option Bool) := fun i =>
    match base i with
    | some b => {some b}
    | none => if i ∈ S then {none} else {some true, some false}
  have hpi : restrictionExtensionFreeSetFiber base S = Fintype.piFinset choices := by
    ext rho
    rw [restrictionExtensionFreeSetFiber, Finset.mem_filter, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hext, hfree⟩ i
      cases hbase : base i with
      | none =>
          by_cases hi : i ∈ S
          · have hrho : rho i = none := mem_freeVars.mp (hfree.symm ▸ hi)
            simp [choices, hbase, hi, hrho]
          · have hrho : rho i ≠ none := fun hrho => hi (hfree ▸ mem_freeVars.mpr hrho)
            cases hri : rho i with
            | none => exact False.elim (hrho hri)
            | some b => cases b <;> simp [choices, hbase, hi, hri]
      | some b => simp [choices, hbase, hext i b hbase]
    · intro hchoices
      constructor
      · intro i b hbase
        have hi := hchoices i
        simp [choices, hbase] at hi
        exact hi
      · ext i
        rw [mem_freeVars]
        cases hbase : base i with
        | none =>
            by_cases hi : i ∈ S
            · have hri := hchoices i
              simp [choices, hbase, hi] at hri
              simp [hi, hri]
            · have hri := hchoices i
              simp only [choices, hbase, hi, if_false, Finset.mem_insert,
                Finset.mem_singleton] at hri
              rcases hri with hri | hri <;> simp [hi, hri]
        | some b =>
            have hiS : i ∉ S := by
              intro hi
              have hnone := mem_freeVars.mp (hS hi)
              rw [hbase] at hnone
              simp at hnone
            have hri := hchoices i
            simp [choices, hbase] at hri
            simp [hiS, hri]
  rw [hpi, Fintype.card_piFinset]
  have hcard : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (choices i).card = if i ∈ freeVars base \ S then 2 else 1 := by
    intro i _
    cases hbase : base i with
    | none =>
        have hfree : i ∈ freeVars base := mem_freeVars.mpr hbase
        by_cases hi : i ∈ S <;> simp [choices, hbase, hi, hfree]
    | some b =>
        have hnot : i ∉ freeVars base := by simp [mem_freeVars, hbase]
        simp [choices, hbase, hnot]
  rw [Finset.prod_congr rfl hcard, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one]
  have hfilter : (Finset.univ.filter fun i : Fin n => i ∈ freeVars base \ S) =
      freeVars base \ S := by
    ext i
    simp
  rw [hfilter, Finset.card_sdiff_of_subset hS]

/-- The admissible free sets are obtained uniquely by adjoining `K - |required|` coordinates
from the base-live coordinates outside `required`. -/
theorem card_targetSuperset_freeSets {n K : ℕ} (base : Restriction n)
    (required : Finset (Fin n)) (hrequired : required ⊆ freeVars base)
    (hrequiredK : required.card ≤ K) :
    (((freeVars base).powersetCard K).filter (fun S => required ⊆ S)).card =
      Nat.choose ((freeVars base).card - required.card) (K - required.card) := by
  classical
  let extras := (freeVars base \ required).powersetCard (K - required.card)
  let addRequired : Finset (Fin n) → Finset (Fin n) := fun U => required ∪ U
  have himage : extras.image addRequired =
      ((freeVars base).powersetCard K).filter (fun S => required ⊆ S) := by
    ext S
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨U, hU, rfl⟩
      have hU' := Finset.mem_powersetCard.mp hU
      constructor
      · constructor
        · exact Finset.union_subset hrequired (hU'.1.trans Finset.sdiff_subset)
        · rw [Finset.card_union_of_disjoint]
          · omega
          · exact Finset.disjoint_left.mpr fun i hi hUi =>
              (Finset.mem_sdiff.mp (hU'.1 hUi)).2 hi
      · exact Finset.subset_union_left
    · rintro ⟨⟨hSbase, hScard⟩, hrequiredS⟩
      refine ⟨S \ required, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        constructor
        · intro i hi
          exact Finset.mem_sdiff.mpr ⟨hSbase (Finset.mem_sdiff.mp hi).1,
            (Finset.mem_sdiff.mp hi).2⟩
        · rw [Finset.card_sdiff_of_subset hrequiredS]
          omega
      · exact Finset.union_sdiff_of_subset hrequiredS
  rw [← himage]
  have hinj : Set.InjOn addRequired extras := by
    intro U hU V hV hEq
    change required ∪ U = required ∪ V at hEq
    ext i
    have hUsub := (Finset.mem_powersetCard.mp hU).1
    have hVsub := (Finset.mem_powersetCard.mp hV).1
    constructor
    · intro hiU
      have hiNot : i ∉ required := (Finset.mem_sdiff.mp (hUsub hiU)).2
      have hiUnion : i ∈ required ∪ V := by
        rw [← hEq]
        exact Finset.mem_union_right required hiU
      exact (Finset.mem_union.mp hiUnion).resolve_left hiNot
    · intro hiV
      have hiNot : i ∉ required := (Finset.mem_sdiff.mp (hVsub hiV)).2
      have hiUnion : i ∈ required ∪ U := by
        rw [hEq]
        exact Finset.mem_union_right required hiV
      exact (Finset.mem_union.mp hiUnion).resolve_left hiNot
  rw [Finset.card_image_iff.mpr hinj, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset hrequired]

/-- Exact stars-and-bars balance for the full extension fiber.  Choose the additional live
coordinates beyond `required`, then assign a Boolean to every remaining base-live coordinate. -/
theorem targetPreservingShellExtensions_card {n K : ℕ} (base : Restriction n)
    (required : Finset (Fin n)) (hrequired : required ⊆ freeVars base)
    (hrequiredK : required.card ≤ K) (hKbase : K ≤ stars base) :
    (targetPreservingShellExtensions base required K).card =
      Nat.choose ((freeVars base).card - required.card) (K - required.card) *
        2 ^ ((freeVars base).card - K) := by
  classical
  let freeSets := ((freeVars base).powersetCard K).filter fun S => required ⊆ S
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun rho : Restriction n => freeVars rho) (t := freeSets)]
  · have hfiber : ∀ S ∈ freeSets,
        ((targetPreservingShellExtensions base required K).filter
          (fun rho => freeVars rho = S)).card =
          2 ^ ((freeVars base).card - K) := by
      intro S hS
      have hSdata := Finset.mem_filter.mp hS
      have hSbase := (Finset.mem_powersetCard.mp hSdata.1).1
      have hScard := (Finset.mem_powersetCard.mp hSdata.1).2
      have heq : (targetPreservingShellExtensions base required K).filter
          (fun rho => freeVars rho = S) =
          restrictionExtensionFreeSetFiber base S := by
        ext rho
        simp only [targetPreservingShellExtensions, restrictionExtensionFreeSetFiber,
          Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · rintro ⟨hext, hfree⟩
          refine ⟨⟨hext, ?_, ?_⟩, hfree⟩
          · simpa [stars, hfree] using hScard
          · simpa [hfree] using hSdata.2
      rw [heq, card_restrictionExtends_freeVars_eq base S hSbase, hScard]
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, nsmul_eq_mul,
      card_targetSuperset_freeSets base required hrequired hrequiredK]
    simp
  · intro rho hrho
    simp only [targetPreservingShellExtensions, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hrho
    change freeVars rho ∈ freeSets
    simp only [freeSets, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, hrho.2.2⟩
    · intro i hi
      rw [mem_freeVars] at hi ⊢
      cases hbase : base i with
      | none => rfl
      | some b => rw [hrho.1 i b hbase] at hi; simp at hi
    · simpa [stars] using hrho.2.1

/-- Sharp balance against the unrestricted extension shell.  If `B` coordinates are live in the
base and a prescribed `R`-set must remain live, then summing the corresponding fiber size over all
`R`-subsets counts each `K`-live extension exactly `choose K R` times.  Equivalently, the exact
target-preservation density inside the base-extension shell is `choose K R / choose B R`; the
identity is kept division-free over `ℕ`. -/
theorem targetPreservingShellExtensions_exact_balance {n K : ℕ}
    (base : Restriction n) (required : Finset (Fin n))
    (hrequired : required ⊆ freeVars base) (hrequiredK : required.card ≤ K)
    (hKbase : K ≤ stars base) :
    Nat.choose (stars base) required.card *
        (targetPreservingShellExtensions base required K).card =
      Nat.choose (stars base) K * Nat.choose K required.card *
        2 ^ (stars base - K) := by
  rw [targetPreservingShellExtensions_card base required hrequired hrequiredK hKbase]
  simp only [stars]
  rw [← Nat.mul_assoc]
  rw [← Nat.choose_mul hrequiredK]

/-- A globally compatible outside-literal selection discharges the entire semantic isolation
interface in one step.  The remaining frontier is purely combinatorial: find a large selection
satisfying this predicate, or charge its failure to a small support/component hitting set. -/
theorem mem_commonShallowBad_of_globallyCompatibleIsolationSelection
    {n G H fuel K trunkDepth residualDepth : ℕ}
    (large : Fin H → List (Clause n)) (target : Fin G → Clause n)
    (e : Fin G → Fin H) (selected : List (Rung4Literal n))
    (hselection : GloballyCompatibleIsolationSelection large target e selected)
    (hnodup : ∀ g, (large (e g)).Nodup)
    (hmem : ∀ g, target g ∈ large (e g))
    (hbad : compatibleIsolationRestriction selected ∈
      commonShallowBad (fun g => [target g]) fuel K
      trunkDepth residualDepth) :
    compatibleIsolationRestriction selected ∈
      commonShallowBad large fuel K trunkDepth residualDepth := by
  apply mem_commonShallowBad_of_isolatedSingleton_reindex large target e hnodup hmem
  · exact compatibleIsolationRestriction_target_live hselection.2.1
  · intro g U hU hUne
    exact compatibleIsolationRestriction_competitor_falsified hselection.1
      (hselection.2.2 g U hU hUne)
  · exact hbad

/-! ### Subsumption deletion does not preserve the canonical tree -/

/-- The inclusion-minimal gate consisting only of the weaker positive literal. -/
def subsumptionMinimalGate : List (Clause 2) :=
  [⟨[Rung4Literal.pos 0]⟩]

/-- A semantically redundant stronger term is deliberately placed first.  Its literals are
ordered so that the canonical procedure queries the irrelevant second coordinate before reaching
the weaker absorbing term. -/
def subsumptionRedundantGate : List (Clause 2) :=
  [⟨[Rung4Literal.pos 1, Rung4Literal.pos 0]⟩, ⟨[Rung4Literal.pos 0]⟩]

/-- The second term literally subsumes the first: all of the weaker term's literals occur in the
stronger term. -/
theorem subsumptionMinimal_lits_subset_redundant :
    ∀ ell ∈ (subsumptionMinimalGate.get ⟨0, by decide⟩).lits,
      ell ∈ (subsumptionRedundantGate.get ⟨0, by decide⟩).lits := by
  simp [subsumptionMinimalGate, subsumptionRedundantGate]

/-- Despite the extra term, both lists have exactly the same DNF truth value under every partial
restriction.  Thus the counterexample below is about the canonical procedure, not semantics. -/
theorem subsumptionRedundantGate_anyTermSat (sigma : Restriction 2) :
    anyTermSat subsumptionRedundantGate sigma = anyTermSat subsumptionMinimalGate sigma := by
  simp [subsumptionRedundantGate, subsumptionMinimalGate, anyTermSat, termSat,
    Depth3.litTrue, litFixedVal]

/-- The inclusion-minimal gate needs only its essential coordinate on the all-live root. -/
theorem subsumptionMinimalGate_depth_one :
    (canonicalDT subsumptionMinimalGate 2 (fun _ => none)).depth = 1 := by
  simp [subsumptionMinimalGate, canonicalDT, anyTermSat, termSat, activeTerm,
    termFalsified, freeLits, Depth3.litTrue, litVar, litFixedVal, litFalse, litFree,
    fixVar, BoolDecisionTree.depth]

/-- The redundant first term forces the canonical procedure to query both coordinates. -/
theorem subsumptionRedundantGate_depth_two :
    (canonicalDT subsumptionRedundantGate 2 (fun _ => none)).depth = 2 := by
  simp [subsumptionRedundantGate, canonicalDT, anyTermSat, termSat, activeTerm,
    termFalsified, freeLits, Depth3.litTrue, litVar, litFixedVal, litFalse, litFree,
    fixVar, BoolDecisionTree.depth]

/-- Therefore deleting a term absorbed by an inclusion-minimal witness can preserve DNF semantics
while changing canonical depth.  Subsumption normalization cannot replace the isolation argument
at the current canonical-tree interface. -/
theorem canonicalDT_depth_not_preserved_by_subsumption_deletion :
    (∀ sigma, anyTermSat subsumptionRedundantGate sigma =
        anyTermSat subsumptionMinimalGate sigma) ∧
      (canonicalDT subsumptionMinimalGate 2 (fun _ => none)).depth <
        (canonicalDT subsumptionRedundantGate 2 (fun _ => none)).depth := by
  refine ⟨subsumptionRedundantGate_anyTermSat, ?_⟩
  rw [subsumptionMinimalGate_depth_one, subsumptionRedundantGate_depth_two]
  omega

/-- Exact gate reindexing transfers semantic badness in the useful direction: every root bad for
the packed family is bad for the full family. -/
theorem commonShallowBad_subset_of_reindex
    {n G H fuel K trunkDepth residualDepth : ℕ}
    {small : Fin G → List (Clause n)} {large : Fin H → List (Clause n)}
    (e : Fin G → Fin H) (hgate : ∀ g, small g = large (e g)) :
    commonShallowBad small fuel K trunkDepth residualDepth ⊆
      commonShallowBad large fuel K trunkDepth residualDepth := by
  intro sigma hsigma
  rw [mem_commonShallowBad] at hsigma ⊢
  refine ⟨hsigma.1, ?_⟩
  intro hlarge
  exact hsigma.2 (hlarge.of_reindex e hgate)

/-- The exact width-three semantic tail transfers to any larger family containing those ordered
singleton gates verbatim.  This is the positive packing interface that a circuit extraction lemma
would have to discharge. -/
theorem compatibleDeficitShell_subset_commonShallowBad_of_orderedConjunctionBlocks_reindex
    {n G H K trunkDepth residualDepth : ℕ}
    (large : Fin H → List (Clause n)) (blocks : Fin G → List (Fin n))
    (hpair : ∀ g h, g ≠ h → Disjoint (blocks g).toFinset (blocks h).toFinset)
    (e : Fin G → Fin H)
    (hgate : ∀ g, orderedConjunctionBlock (blocks g) = large (e g)) :
    compatibleDeficitShell (fun g => (blocks g).toFinset) K trunkDepth residualDepth ⊆
      commonShallowBad large n K trunkDepth residualDepth := by
  exact Finset.Subset.trans
    (compatibleDeficitShell_subset_commonShallowBad_of_orderedConjunctionBlocks blocks hpair)
    (commonShallowBad_subset_of_reindex e hgate)

/-- A one-literal conjunction used to audit whether merely finding a clause inside a bottom gate
is sufficient for exact subfamily transfer. -/
def packedPositiveSingleton : List (Clause 1) :=
  [⟨[Rung4Literal.pos 0]⟩]

/-- Adding an always-true empty term preserves the packed clause as a list member but makes the
whole DNF constant. -/
def packedPositiveWithTrueTerm : List (Clause 1) :=
  [⟨[]⟩, ⟨[Rung4Literal.pos 0]⟩]

theorem packedPositiveSingleton_sublist_withTrueTerm :
    packedPositiveSingleton.Sublist packedPositiveWithTrueTerm := by
  simp [packedPositiveSingleton, packedPositiveWithTrueTerm]

/-- On the all-live one-variable root, the packed singleton really needs one query. -/
theorem packedPositiveSingleton_depth_one :
    (canonicalDT packedPositiveSingleton 1 (fun _ => none)).depth = 1 := by
  simp [packedPositiveSingleton, canonicalDT, anyTermSat, termSat, activeTerm,
    termFalsified, freeLits, Depth3.litTrue, litVar, litFixedVal, litFalse, litFree,
    fixVar, BoolDecisionTree.depth]

/-- The containing gate has depth zero because its first empty term is already satisfied.  Hence
clause-list inclusion does not provide the depth monotonicity needed to embed the exact triple
tail into a general normalized bottom family. -/
theorem packedPositiveWithTrueTerm_depth_zero :
    (canonicalDT packedPositiveWithTrueTerm 1 (fun _ => none)).depth = 0 := by
  simp [packedPositiveWithTrueTerm, canonicalDT, anyTermSat, termSat]

theorem canonicalDT_depth_not_monotone_of_sublist :
    packedPositiveSingleton.Sublist packedPositiveWithTrueTerm ∧
      (canonicalDT packedPositiveWithTrueTerm 1 (fun _ => none)).depth <
        (canonicalDT packedPositiveSingleton 1 (fun _ => none)).depth := by
  exact ⟨packedPositiveSingleton_sublist_withTrueTerm, by
    rw [packedPositiveWithTrueTerm_depth_zero, packedPositiveSingleton_depth_one]
    omega⟩

private def triple3 : Fin 6 := ⟨3, by omega⟩
private def triple4 : Fin 6 := ⟨4, by omega⟩
private def triple5 : Fin 6 := ⟨5, by omega⟩

/-- Two disjoint width-three ordered conjunctions.  Their six live coordinates exactly fill the
proportional shell `K = 2d` at `d = 3`, while reducing both gates to residual depth one requires
two true-path queries in each block. -/
def independentTripleGates : Fin 2 → List (Clause 6) := fun g ↦
  if g = 0 then
    orderedConjunctionBlock [0, 1, 2]
  else
    orderedConjunctionBlock [triple3, triple4, triple5]

/-- If no coordinate is fixed false and at least two coordinates of the selected triple remain
free, its canonical tree still has depth strictly greater than one. -/
theorem independentTripleGates_depth_gt_one {rho : Restriction 6} (g : Fin 2)
    (hnotFalse : ∀ i, rho i ≠ some false)
    (hfree : if g = 0 then
        (rho 0 = none ∧ rho 1 = none) ∨ (rho 0 = none ∧ rho 2 = none) ∨
          (rho 1 = none ∧ rho 2 = none)
      else
        (rho triple3 = none ∧ rho triple4 = none) ∨
          (rho triple3 = none ∧ rho triple5 = none) ∨
          (rho triple4 = none ∧ rho triple5 = none)) :
    1 < (canonicalDT (independentTripleGates g) 3 rho).depth := by
  fin_cases g
  · simp only [Fin.isValue, Fin.zero_eta, if_pos] at hfree
    rcases hfree with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
    · cases h2' : rho 2 with
      | none =>
          simp [independentTripleGates, triple3, triple4, triple5,
            orderedConjunctionBlock, canonicalDT, anyTermSat,
            termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
            litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h0, h1, h2']
      | some b =>
          cases b
          · exact False.elim (hnotFalse 2 h2')
          · simp [independentTripleGates, triple3, triple4, triple5,
              orderedConjunctionBlock, canonicalDT, anyTermSat,
              termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
              litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h0, h1, h2']
    · cases h1' : rho 1 with
      | none =>
          simp [independentTripleGates, triple3, triple4, triple5,
            orderedConjunctionBlock, canonicalDT, anyTermSat,
            termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
            litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h0, h1', h2]
      | some b =>
          cases b
          · exact False.elim (hnotFalse 1 h1')
          · simp [independentTripleGates, triple3, triple4, triple5,
              orderedConjunctionBlock, canonicalDT, anyTermSat,
              termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
              litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h0, h1', h2]
    · cases h0' : rho 0 with
      | none =>
          simp [independentTripleGates, triple3, triple4, triple5,
            orderedConjunctionBlock, canonicalDT, anyTermSat,
            termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
            litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h0', h1, h2]
      | some b =>
          cases b
          · exact False.elim (hnotFalse 0 h0')
          · simp [independentTripleGates, triple3, triple4, triple5,
              orderedConjunctionBlock, canonicalDT, anyTermSat,
              termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
              litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h0', h1, h2]
  · simp only [Fin.isValue, Fin.reduceFinMk, OfNat.ofNat, if_false] at hfree
    change 1 < (canonicalDT
      (orderedConjunctionBlock [triple3, triple4, triple5]) 3 rho).depth
    rcases hfree with ⟨h3, h4⟩ | ⟨h3, h5⟩ | ⟨h4, h5⟩
    · cases h5' : rho triple5 with
      | none =>
          simp [triple3, triple4, triple5] at h3 h4 h5'
          simp [independentTripleGates, triple3, triple4, triple5,
            orderedConjunctionBlock, canonicalDT, anyTermSat,
            termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
            litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h3, h4, h5']
      | some b =>
          cases b
          · exact False.elim (hnotFalse triple5 h5')
          · simp [triple3, triple4, triple5] at h3 h4 h5'
            simp [independentTripleGates, triple3, triple4, triple5,
              orderedConjunctionBlock, canonicalDT, anyTermSat,
              termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
              litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h3, h4, h5']
    · cases h4' : rho triple4 with
      | none =>
          simp [triple3, triple4, triple5] at h3 h4' h5
          simp [independentTripleGates, triple3, triple4, triple5,
            orderedConjunctionBlock, canonicalDT, anyTermSat,
            termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
            litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h3, h4', h5]
      | some b =>
          cases b
          · exact False.elim (hnotFalse triple4 h4')
          · simp [triple3, triple4, triple5] at h3 h4' h5
            simp [independentTripleGates, triple3, triple4, triple5,
              orderedConjunctionBlock, canonicalDT, anyTermSat,
              termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
              litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h3, h4', h5]
    · cases h3' : rho triple3 with
      | none =>
          simp [triple3, triple4, triple5] at h3' h4 h5
          simp [independentTripleGates, triple3, triple4, triple5,
            orderedConjunctionBlock, canonicalDT, anyTermSat,
            termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
            litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h3', h4, h5]
      | some b =>
          cases b
          · exact False.elim (hnotFalse triple3 h3')
          · simp [triple3, triple4, triple5] at h3' h4 h5
            simp [independentTripleGates, triple3, triple4, triple5,
              orderedConjunctionBlock, canonicalDT, anyTermSat,
              termSat, activeTerm, termFalsified, freeLits, Depth3.litTrue, litVar,
              litFixedVal, litFalse, litFree, fixVar, BoolDecisionTree.depth, h3', h4, h5]

/-- At the exact proportional boundary `K = 6 = 2d`, a depth-three common trunk cannot reduce
both disjoint width-three conjunctions to residual depth one.  The all-true path contains at most
three queried coordinates, so one triple retains at least two free coordinates. -/
theorem independentTriples_not_commonShallowAt_three :
    ¬ CommonShallowAt independentTripleGates 3 (fun _ : Fin 6 ↦ none) 3 1 := by
  rintro ⟨trunk, hdepth, hleaf⟩
  let x : Fin 6 → Bool := fun _ ↦ true
  let path : Finset (Fin 6) := (CommonTree.queryVars trunk x).toFinset
  have hpathCard : path.card ≤ 3 := by
    calc
      path.card ≤ (CommonTree.queryVars trunk x).length := List.toFinset_card_le _
      _ ≤ CommonTree.depth trunk := CommonTree.queryVars_length_le_depth trunk x
      _ ≤ 3 := hdepth
  let A : Finset (Fin 6) := {0, 1, 2}
  let B : Finset (Fin 6) := {triple3, triple4, triple5}
  have hdisj : Disjoint (A ∩ path) (B ∩ path) := by
    simp [A, B, Finset.disjoint_left, triple3, triple4, triple5]
  have hunionSubset : (A ∩ path) ∪ (B ∩ path) ⊆ path := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_inter] at hi
    exact hi.elim And.right And.right
  have hsum : (A ∩ path).card + (B ∩ path).card ≤ 3 := by
    calc
      (A ∩ path).card + (B ∩ path).card =
          ((A ∩ path) ∪ (B ∩ path)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ path.card := Finset.card_le_card hunionSubset
      _ ≤ 3 := hpathCard
  have hside : (A ∩ path).card ≤ 1 ∨ (B ∩ path).card ≤ 1 := by omega
  obtain ⟨g, hgfree⟩ : ∃ g : Fin 2, if g = 0 then
        (0 ∉ path ∧ 1 ∉ path) ∨ (0 ∉ path ∧ 2 ∉ path) ∨
          (1 ∉ path ∧ 2 ∉ path)
      else
        (triple3 ∉ path ∧ triple4 ∉ path) ∨
          (triple3 ∉ path ∧ triple5 ∉ path) ∨
          (triple4 ∉ path ∧ triple5 ∉ path) := by
    rcases hside with hA | hB
    · refine ⟨0, ?_⟩
      simp only [Fin.isValue, Fin.zero_eta, if_pos]
      by_cases h0 : (0 : Fin 6) ∈ path <;>
        by_cases h1 : (1 : Fin 6) ∈ path <;>
        by_cases h2 : (2 : Fin 6) ∈ path <;>
        simp_all [A]
    · refine ⟨1, ?_⟩
      simp only [Fin.isValue, Fin.reduceFinMk, OfNat.ofNat, if_false]
      by_cases h3 : triple3 ∈ path <;>
        by_cases h4 : triple4 ∈ path <;>
        by_cases h5 : triple5 ∈ path <;>
        simp_all [B, triple3, triple4, triple5]
  have hx : Rung4Restriction.Extends (fun _ : Fin 6 ↦ none) x := by
    intro i b hi
    simp at hi
  have hfree (i : Fin 6) (hi : i ∉ path) : CommonTree.run trunk x i = none := by
    let y : Fin 6 → Bool := Function.update x i false
    have hy : Rung4Restriction.Extends (fun _ : Fin 6 ↦ none) y := by
      intro j b hj
      simp at hj
    obtain ⟨_, htx, _⟩ := hleaf x hx
    obtain ⟨_, hty, _⟩ := hleaf y hy
    have hrun : CommonTree.run trunk y = CommonTree.run trunk x := by
      exact CommonTree.run_update_of_not_mem_queryVars trunk x i (by simpa [path] using hi)
    cases ht : CommonTree.run trunk x i with
    | none => rfl
    | some b =>
        have hbx : b = true := by simpa [x] using htx i b ht
        have hby : b = false := by
          have : CommonTree.run trunk y i = some b := by simpa [hrun] using ht
          simpa [y, x] using hty i b this
        exact False.elim (Bool.false_ne_true (hby.symm.trans hbx))
  obtain ⟨_, hagree, hshallow⟩ := hleaf x hx
  have hnotFalse (i : Fin 6) : CommonTree.run trunk x i ≠ some false := by
    intro hi
    have := hagree i false hi
    simpa [x] using this
  have hgdepth := independentTripleGates_depth_gt_one
    (rho := CommonTree.run trunk x) g hnotFalse
    (by
      by_cases hg : g = 0
      · simp only [hg, if_pos] at hgfree ⊢
        rcases hgfree with h | h | h <;> simp_all [hfree]
      · simp only [hg, if_false] at hgfree ⊢
        rcases hgfree with h | h | h <;> simp_all [hfree])
  exact (Nat.not_lt_of_ge (hshallow g)) hgdepth

/-- Hence the fully live six-variable restriction is an actual member of the semantic bad event
on the exact half-shell boundary. -/
theorem allFreeSix_mem_commonShallowBad_three :
    (fun _ : Fin 6 ↦ none) ∈ commonShallowBad independentTripleGates 3 6 3 1 := by
  rw [mem_commonShallowBad]
  constructor
  · decide
  · exact independentTriples_not_commonShallowAt_three

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
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.manyIntactShell_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.freeSetOccupancyCode_injective
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.freeSetOccupancyCode_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.mem_manyIntactFreeSets_iff_occupancy
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.occupancySizeFiber_card_uniform
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.manyIntactFreeSets_card_eq_sum_occupancy
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.manyIntactFreeSets_eq_empty_of_uniform_volume
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.manyIntactFreeSets_eq_empty_width_two_half_shell
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.manyIntactShell_eq_empty_width_two_half_shell
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.manyIntactFreeSets_mul_pow_le_commonShallowBad_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentPairs_commonShallowAt_two
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.allFreeFour_not_mem_commonShallowBad_two
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentTripleGates_depth_gt_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentTriples_not_commonShallowAt_three
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.allFreeSix_mem_commonShallowBad_three
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
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_shell_extension_of_globallyCompatibleIsolationSelection'
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.card_restrictionExtends_freeVars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.card_targetSuperset_freeSets
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.targetPreservingShellExtensions_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.targetPreservingShellExtensions_exact_balance
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
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_disjoint_support_of_pairwiseDisjoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.pairwiseDisjoint_support_miss
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_intact_support_disjoint_of_pairwiseDisjoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.supportedGates_not_commonShallowAt_of_intact_miss
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.pairwiseDisjoint_supportedGates_not_commonShallowAt_of_intact
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.supportedGates_not_commonShallowAt_allFree
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.allFree_mem_commonShallowBad_of_supportedGates
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.allFree_mem_commonShallowBad_of_pairwiseDisjoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.orderedConjunctionBlock_depth
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.orderedConjunctionBlock_freeSupport_card_le_depth
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.allFree_mem_commonShallowBad_of_orderedConjunctionBlocks
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.mem_commonShallowBad_of_orderedConjunctionBlocks_of_many_intact
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentPairGates_depth_two
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentPairs_not_commonShallowAt_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.allFreeFour_mem_commonShallowBad_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_liveSupport_sdiff_card_gt_of_sum_deficit
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_compatible_liveSupport_sdiff_card_gt_of_sum_deficit
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.supportedGates_not_commonShallowAt_of_compatible_sum_deficit
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.mem_commonShallowBad_of_compatible_sum_deficit
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleDeficitShell_subset_commonShallowBad
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleDeficitShell_subset_commonShallowBad_of_orderedConjunctionBlocks
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleResidualQueryDeficit_eq_two_of_intact_triple
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleLocalFiber_card_zero_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleLocalFiber_card_one_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleLocalFiber_card_two_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleLocalFiber_card_two_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleLocalFiber_card_three_two
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleLocalFibers_exhaustive
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.restrictionProductCode_injective
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.restrictionProductCode_bijective_triples
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleDeficitFiber_card_eq_tripleProductWeightFiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleLocalEnumerator_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.outsideStateEnumerator_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleProductEnumerator_factorization
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleProductEnumerator_coeff
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleProductWeightFiber_card_eq_indexWeightFiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleProductEnumerator_coeff_eq_weightFiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.tripleProductEnumerator_coeff_eq_compatibleDeficitFiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleDeficitShell_card_eq_coefficient_tail
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleDeficitShell_twenty_card_eq_coefficient_tail
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.manyIntactShell_subset_compatibleDeficitShell_triples
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleDeficitShell_triples_occupancy_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.manyIntactShell_card_le_commonShallowBad_of_orderedTriples
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.orderedTriples_coefficient_tail_scaled_le_linearGap
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonShallowAt.of_reindex
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.liveTermFilter_eq_singleton
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonShallowAt.of_reindex_liveFilter
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.mem_commonShallowBad_of_isolatedSingleton_reindex
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.termFalsified_true_of_lits_subset
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.termFalsified_false_of_lits_subset
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_lits_subset_of_isolatedSingleton
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_outside_literal_of_inclusionMinimal
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.inclusionMinimal_of_isolatedSingleton
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleIsolationRestriction_litFalse
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleIsolationRestriction_target_live
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleIsolationRestriction_competitor_falsified
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.freeVars_compatibleIsolationRestriction
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.stars_compatibleIsolationRestriction
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.sub_le_stars_compatibleIsolationRestriction
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.stars_compatibleIsolationRestriction_eq_sub_length
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_exists_globallyCompatibleIsolationSelection_of_outsideTargetVars_eq_empty
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_targetSupport_conflict_of_inclusionMinimal_of_outsideTargetVars_eq_empty
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_globallyCompatibleIsolationSelection_of_nonempty_edges_of_pool_consistent
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_exists_globallyCompatibleIsolationSelection_of_singleton_polarity_conflict
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_globallyCompatibleIsolationSelection_iff_exists_hitsOutsideCompetitors
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.mem_fullOutsideCompetitorCore
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.hitsOutsideCompetitorCore_full_iff_hitsOutsideCompetitors
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_inclusionMinimalUnsatisfiableCore_subset
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.InclusionMinimalUnsatisfiableCore.card_le_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.InclusionMinimalUnsatisfiableCore.card_le_two_pow_queried
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_globallyCompatibleIsolationSelection_iff_fullCore_satisfiable
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.not_exists_globallyCompatibleIsolationSelection_iff_fullCore_unsatisfiable
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.PolarityCycleValid.not_exists_globallyCompatibleIsolationSelection
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.fullOutsideCompetitorCore_polarityCycleValid_of_failure
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exists_minimalPolarityCycleValid_card_le_two_pow_queried
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.polarityCoreQueryIncidences_card_le_mul
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.polarityCoreQueryIncidences_coordinate_fiber_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.InclusionMinimalUnsatisfiableCore.polarityCoreQueryIncidences_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.oppositeSingleton_no_joint_target_isolation
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycleGate_normalized
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycleGate_inclusionMinimal
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycle_exact_outside_edges
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycle_all_competitor_edges_nonempty
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycle_no_target_isolation
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycleGate_canonicalDT_depth_eq_two
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycleGate_queriedVars_eq_univ
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycleCore_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycleCore_card_le_gate_length
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycle_polarityCycleValid
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycle_no_target_isolation_via_cycle
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycleIncidences_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycleIncidences_card_le_gate_length
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.deepPolarityCycleIncidences_valid
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.complementarySingleton_canonicalDT_depth_le
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.oppositeSingletonFamily_commonShallowAt_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveTwoBitGate_canonicalDT_depth_eq_two
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveTwoBitFamily_not_commonShallowAt_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.allFreeTwo_mem_exhaustiveTwoBit_commonShallowBad_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveTwoBit_no_joint_target_isolation
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveTwoBitGate_queriedVars_eq_univ
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveTwoBitConflictIncidences_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveTwoBitConflictIncidences_coordinate_fiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.offDiagonalTermPairs_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.completeConflictQueryIncidences_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.completeConflictQueryIncidences_coordinate_fiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveMinterm_completeConflict_coordinate_fiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.selectiveConflictQueryIncidences_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.selectiveConflictQueryIncidences_coordinate_fiber_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.selectiveConflictQueryIncidences_subset_complete
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.SelectiveConflictSelectorValid.no_singleton_target_isolation
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveTwoBit_selectiveConflictSelectorValid
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveTwoBit_selectiveConflictQueryIncidences_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.mem_commonShallowBad_of_globallyCompatibleIsolationSelection
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.subsumptionMinimal_lits_subset_redundant
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.subsumptionRedundantGate_anyTermSat
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.subsumptionMinimalGate_depth_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.subsumptionRedundantGate_depth_two
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_not_preserved_by_subsumption_deletion
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.commonShallowBad_subset_of_reindex
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.compatibleDeficitShell_subset_commonShallowBad_of_orderedConjunctionBlocks_reindex
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.packedPositiveSingleton_sublist_withTrueTerm
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.packedPositiveSingleton_depth_one
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.packedPositiveWithTrueTerm_depth_zero
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalDT_depth_not_monotone_of_sublist
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_taggedRawVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_freshTaggedVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.independentLiteral_freshTaggedPrefixVars_eq_take
/-! ### A normalized core saturating the support-exponential bound -/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- A protected target on a fourth coordinate, kept separate from the three coordinates used by
the exhaustive competitor clauses below. -/
def exhaustiveThreeTarget : Fin 1 → Clause 4 :=
  fun _ => ⟨[Rung4Literal.pos 3]⟩

/-- All eight polarity patterns on coordinates `0,1,2`, followed by the protected target.  The
competitors are ordered as an ordinary exhaustive three-variable DNF, so its canonical tree
really queries all three outside coordinates before the final target can matter. -/
def exhaustiveThreeProtectedGate : List (Clause 4) :=
  [⟨[Rung4Literal.pos 0, Rung4Literal.pos 1, Rung4Literal.pos 2]⟩,
   ⟨[Rung4Literal.pos 0, Rung4Literal.pos 1, Rung4Literal.neg 2]⟩,
   ⟨[Rung4Literal.pos 0, Rung4Literal.neg 1, Rung4Literal.pos 2]⟩,
   ⟨[Rung4Literal.pos 0, Rung4Literal.neg 1, Rung4Literal.neg 2]⟩,
   ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1, Rung4Literal.pos 2]⟩,
   ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1, Rung4Literal.neg 2]⟩,
   ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1, Rung4Literal.pos 2]⟩,
   ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1, Rung4Literal.neg 2]⟩,
   exhaustiveThreeTarget 0]

def exhaustiveThreeProtectedFamily : Fin 1 → List (Clause 4) :=
  fun _ => exhaustiveThreeProtectedGate

/-- The eight indexed proper competitors of the protected target. -/
def exhaustiveThreeProtectedCore : Finset (Fin 1 × Clause 4) :=
  {(0, ⟨[Rung4Literal.pos 0, Rung4Literal.pos 1, Rung4Literal.pos 2]⟩),
   (0, ⟨[Rung4Literal.pos 0, Rung4Literal.pos 1, Rung4Literal.neg 2]⟩),
   (0, ⟨[Rung4Literal.pos 0, Rung4Literal.neg 1, Rung4Literal.pos 2]⟩),
   (0, ⟨[Rung4Literal.pos 0, Rung4Literal.neg 1, Rung4Literal.neg 2]⟩),
   (0, ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1, Rung4Literal.pos 2]⟩),
   (0, ⟨[Rung4Literal.neg 0, Rung4Literal.pos 1, Rung4Literal.neg 2]⟩),
   (0, ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1, Rung4Literal.pos 2]⟩),
   (0, ⟨[Rung4Literal.neg 0, Rung4Literal.neg 1, Rung4Literal.neg 2]⟩)}

/-- The example meets the normalization hypotheses used by the circuit bridge: no repeated
clauses, and no repeated coordinate inside any clause. -/
theorem exhaustiveThreeProtectedGate_normalized :
    exhaustiveThreeProtectedGate.Nodup ∧
      ∀ T ∈ exhaustiveThreeProtectedGate,
        (T.lits.map litVar).Nodup ∧ T.lits.length ≤ 3 := by
  decide

/-- The canonical walk records exactly the three outside coordinates. -/
theorem exhaustiveThreeProtectedGate_queriedVars :
    queriedVars (canonicalDT exhaustiveThreeProtectedGate 3 (fun _ => none)) =
      ({0, 1, 2} : Finset (Fin 4)) := by
  decide

/-- The displayed core is exactly the full proper-competitor core of the normalized gate. -/
theorem exhaustiveThreeProtectedCore_eq_full :
    exhaustiveThreeProtectedCore =
      fullOutsideCompetitorCore exhaustiveThreeProtectedFamily
        exhaustiveThreeTarget (fun g => g) := by
  decide

theorem exhaustiveThreeProtectedCore_card :
    exhaustiveThreeProtectedCore.card = 2 ^ 3 := by
  decide

/-- No Boolean orientation hits all eight exhaustive competitors.  For any assignment on the
three outside coordinates, the competitor carrying exactly its satisfying polarity has no
falsified literal.  The proof exposes the eight Boolean cases directly instead of asking a
decision procedure to solve the higher-order satisfiability proposition. -/
theorem exhaustiveThreeProtectedCore_unsatisfiable :
    ¬ ∃ assignment,
      HitsOutsideCompetitorCore exhaustiveThreeTarget
        exhaustiveThreeProtectedCore assignment := by
  rintro ⟨assignment, hhit⟩
  simp [HitsOutsideCompetitorCore, exhaustiveThreeProtectedCore,
    exhaustiveThreeTarget, compatibleIsolationTargetVars, litVar, falValue] at hhit
  cases h₀ : assignment 0 <;>
    cases h₁ : assignment 1 <;>
      cases h₂ : assignment 2 <;> simp_all

/-- The exhaustive core is inclusion-minimal: after deleting one polarity pattern, assigning the
three outside coordinates to satisfy precisely that pattern hits every remaining competitor.
The eight witnesses are given explicitly, so this semantic minimality result does not rely on
`decide`. -/
theorem exhaustiveThreeProtectedCore_inclusionMinimal :
    InclusionMinimalUnsatisfiableCore exhaustiveThreeTarget
      exhaustiveThreeProtectedCore := by
  refine ⟨exhaustiveThreeProtectedCore_unsatisfiable, ?_⟩
  intro p hp
  simp only [exhaustiveThreeProtectedCore, Finset.mem_insert,
    Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨![true, true, true, false], ?_⟩
    simp [HitsOutsideCompetitorCore, exhaustiveThreeProtectedCore,
      exhaustiveThreeTarget, compatibleIsolationTargetVars, litVar, falValue] <;> aesop
  · refine ⟨![true, true, false, false], ?_⟩
    simp [HitsOutsideCompetitorCore, exhaustiveThreeProtectedCore,
      exhaustiveThreeTarget, compatibleIsolationTargetVars, litVar, falValue] <;> aesop
  · refine ⟨![true, false, true, false], ?_⟩
    simp [HitsOutsideCompetitorCore, exhaustiveThreeProtectedCore,
      exhaustiveThreeTarget, compatibleIsolationTargetVars, litVar, falValue] <;> aesop
  · refine ⟨![true, false, false, false], ?_⟩
    simp [HitsOutsideCompetitorCore, exhaustiveThreeProtectedCore,
      exhaustiveThreeTarget, compatibleIsolationTargetVars, litVar, falValue] <;> aesop
  · refine ⟨![false, true, true, false], ?_⟩
    simp [HitsOutsideCompetitorCore, exhaustiveThreeProtectedCore,
      exhaustiveThreeTarget, compatibleIsolationTargetVars, litVar, falValue] <;> aesop
  · refine ⟨![false, true, false, false], ?_⟩
    simp [HitsOutsideCompetitorCore, exhaustiveThreeProtectedCore,
      exhaustiveThreeTarget, compatibleIsolationTargetVars, litVar, falValue] <;> aesop
  · refine ⟨![false, false, true, false], ?_⟩
    simp [HitsOutsideCompetitorCore, exhaustiveThreeProtectedCore,
      exhaustiveThreeTarget, compatibleIsolationTargetVars, litVar, falValue] <;> aesop
  · refine ⟨![false, false, false, false], ?_⟩
    simp [HitsOutsideCompetitorCore, exhaustiveThreeProtectedCore,
      exhaustiveThreeTarget, compatibleIsolationTargetVars, litVar, falValue] <;> aesop

/-- The now source-checked minimal core is a valid polarity certificate for the normalized gate.
Its outside edges are nonempty and contained in the three coordinates queried by the canonical
tree. -/
theorem exhaustiveThreeProtectedCore_polarityCycleValid :
    PolarityCycleValid exhaustiveThreeProtectedFamily exhaustiveThreeTarget (fun g => g)
      (queriedVars (canonicalDT exhaustiveThreeProtectedGate 3 (fun _ => none)))
      exhaustiveThreeProtectedCore := by
  refine ⟨by decide, ?_, exhaustiveThreeProtectedCore_unsatisfiable⟩
  rw [exhaustiveThreeProtectedGate_queriedVars]
  decide

/-- At support size three, the concrete inclusion-minimal core attains the generic
support-exponential cardinality bound exactly. -/
theorem exhaustiveThreeProtectedCore_card_eq_two_pow_queried :
    exhaustiveThreeProtectedCore.card =
      2 ^ (queriedVars
        (canonicalDT exhaustiveThreeProtectedGate 3 (fun _ => none))).card := by
  rw [exhaustiveThreeProtectedGate_queriedVars]
  decide

/-- Every retained clause is incident to all three actually queried outside coordinates, so the
minimal-core incidence rectangle is also attained exactly. -/
theorem exhaustiveThreeProtectedCore_queryIncidences_card :
    (polarityCoreQueryIncidences exhaustiveThreeTarget exhaustiveThreeProtectedCore
      (queriedVars (canonicalDT exhaustiveThreeProtectedGate 3 (fun _ => none)))).card =
        2 ^ 3 * 3 := by
  decide

/-- Every queried coordinate is owned by all eight retained competitors.  In particular, even
inside the normalized canonical validity class, no ownership rule that charges every incidence
to its coordinate can have coordinate multiplicity one (or any bound below eight) on this
example. -/
theorem exhaustiveThreeProtectedCore_queryIncidences_coordinate_fiber_card
    (v : Fin 4)
    (hv : v ∈ queriedVars
      (canonicalDT exhaustiveThreeProtectedGate 3 (fun _ => none))) :
    ((polarityCoreQueryIncidences exhaustiveThreeTarget exhaustiveThreeProtectedCore
      (queriedVars (canonicalDT exhaustiveThreeProtectedGate 3 (fun _ => none)))).filter
        fun p => p.2 = v).card = 2 ^ 3 := by
  rw [exhaustiveThreeProtectedGate_queriedVars] at hv ⊢
  fin_cases v <;> simp at hv <;> decide

/-! ### Arbitrary-support exhaustive minimal cores -/

/-- The literal on outside coordinate `i` whose falsifying value is the Boolean-vector entry
`a i`.  The coordinate is embedded below the final protected-target coordinate. -/
def exhaustiveVectorLiteral {Q : ℕ} (a : Fin Q → Bool) (i : Fin Q) :
    Rung4Literal (Q + 1) :=
  if a i then Rung4Literal.neg i.castSucc else Rung4Literal.pos i.castSucc

/-- The exhaustive competitor indexed by a Boolean vector on `Q` outside coordinates. -/
def exhaustiveVectorClause {Q : ℕ} (a : Fin Q → Bool) : Clause (Q + 1) :=
  ⟨List.ofFn fun i => exhaustiveVectorLiteral a i⟩

theorem falValue_exhaustiveVectorLiteral {Q : ℕ} (a : Fin Q → Bool) (i : Fin Q) :
    falValue (exhaustiveVectorLiteral a i) = a i := by
  by_cases h : a i <;> simp [exhaustiveVectorLiteral, h, falValue]

theorem litVar_exhaustiveVectorLiteral {Q : ℕ} (a : Fin Q → Bool) (i : Fin Q) :
    litVar (exhaustiveVectorLiteral a i) = i.castSucc := by
  by_cases h : a i <;> simp [exhaustiveVectorLiteral, h, litVar]

/-- Different Boolean vectors give different ordered clauses. -/
theorem exhaustiveVectorClause_injective {Q : ℕ} :
    Function.Injective (exhaustiveVectorClause (Q := Q)) := by
  intro a b hab
  funext i
  have hlits := congrArg Clause.lits hab
  simp only [exhaustiveVectorClause] at hlits
  rw [List.ofFn_inj] at hlits
  have hget := congrFun hlits i
  simp [exhaustiveVectorLiteral] at hget
  by_cases hai : a i <;> by_cases hbi : b i <;> simp_all

/-- An embedding retains the Boolean-vector index while fixing the unique target index. -/
def exhaustiveVectorCoreEmbedding (Q : ℕ) :
    (Fin Q → Bool) ↪ (Fin 1 × Clause (Q + 1)) where
  toFun a := (0, exhaustiveVectorClause a)
  inj' := fun _ _ h => exhaustiveVectorClause_injective (congrArg Prod.snd h)

/-- The competitor core containing one clause for every Boolean vector on `Fin Q`. -/
def exhaustiveVectorCore (Q : ℕ) : Finset (Fin 1 × Clause (Q + 1)) :=
  Finset.univ.map (exhaustiveVectorCoreEmbedding Q)

/-- A singleton target on the final coordinate, disjoint from all exhaustive competitors. -/
def exhaustiveVectorTarget (Q : ℕ) : Fin 1 → Clause (Q + 1) :=
  fun _ => ⟨[Rung4Literal.pos (Fin.last Q)]⟩

/-- A concrete gate realizing the arbitrary-support core.  The exhaustive competitors are
listed without duplication, followed by the protected target.  The eventual canonical-query
argument is deliberately separated from this representation theorem: the semantic core and its
incidence counts do not depend on the implementation order of `Finset.toList`. -/
def exhaustiveVectorGate (Q : ℕ) : List (Clause (Q + 1)) :=
  ((Finset.univ : Finset (Fin Q → Bool)).toList.map exhaustiveVectorClause) ++
    [exhaustiveVectorTarget Q 0]

def exhaustiveVectorFamily (Q : ℕ) : Fin 1 → List (Clause (Q + 1)) :=
  fun _ => exhaustiveVectorGate Q

theorem mem_exhaustiveVectorGate (Q : ℕ) (U : Clause (Q + 1)) :
    U ∈ exhaustiveVectorGate Q ↔
      (∃ a : Fin Q → Bool, exhaustiveVectorClause a = U) ∨
        U = exhaustiveVectorTarget Q 0 := by
  simp [exhaustiveVectorGate]

/-- The abstract Boolean-vector core is exactly the full proper-competitor core of its concrete
protected gate. -/
theorem exhaustiveVectorCore_eq_full (Q : ℕ) :
    exhaustiveVectorCore Q =
      fullOutsideCompetitorCore (exhaustiveVectorFamily Q)
        (exhaustiveVectorTarget Q) (fun g => g) := by
  ext p
  rcases p with ⟨g, U⟩
  have hg : g = 0 := Subsingleton.elim _ _
  subst g
  simp only [mem_fullOutsideCompetitorCore, exhaustiveVectorFamily,
    mem_exhaustiveVectorGate]
  constructor
  · intro hp
    rw [exhaustiveVectorCore, Finset.mem_map] at hp
    obtain ⟨a, -, hpa⟩ := hp
    simp only [exhaustiveVectorCoreEmbedding] at hpa
    have hU : exhaustiveVectorClause a = U := congrArg Prod.snd hpa
    refine ⟨Or.inl ⟨a, hU⟩, ?_⟩
    intro hut
    have hlits := congrArg Clause.lits (hU.trans hut)
    simp [exhaustiveVectorClause, exhaustiveVectorTarget] at hlits
  · rintro ⟨hmem, hne⟩
    rcases hmem with ⟨a, rfl⟩ | htarget
    · simp [exhaustiveVectorCore, exhaustiveVectorCoreEmbedding]
    · exact False.elim (hne htarget)

/-- The arbitrary-support exhaustive core has exactly `2^Q` clauses. -/
theorem exhaustiveVectorCore_card (Q : ℕ) :
    (exhaustiveVectorCore Q).card = 2 ^ Q := by
  simp [exhaustiveVectorCore]

theorem compatibleIsolationTargetVars_exhaustiveVectorTarget (Q : ℕ) :
    compatibleIsolationTargetVars (exhaustiveVectorTarget Q) = {Fin.last Q} := by
  ext i
  simp [compatibleIsolationTargetVars, exhaustiveVectorTarget, litVar]

theorem mem_exhaustiveVectorClause {Q : ℕ} (a : Fin Q → Bool)
    (ell : Rung4Literal (Q + 1)) :
    ell ∈ (exhaustiveVectorClause a).lits ↔
      ∃ i, exhaustiveVectorLiteral a i = ell := by
  simp [exhaustiveVectorClause]

/-- Every exhaustive competitor uses every outside coordinate and avoids the protected final
coordinate.  Thus its available outside edge is the complete embedded `Fin Q` support. -/
theorem competitorOutsideTargetVars_exhaustiveVectorClause {Q : ℕ}
    (a : Fin Q → Bool) :
    competitorOutsideTargetVars (exhaustiveVectorTarget Q)
        (exhaustiveVectorClause a) =
      Finset.univ.map Fin.castSuccEmb := by
  ext j
  rw [mem_competitorOutsideTargetVars,
    compatibleIsolationTargetVars_exhaustiveVectorTarget]
  simp only [Finset.mem_singleton, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨ell, hell, rfl⟩, hlast⟩
    rw [mem_exhaustiveVectorClause] at hell
    obtain ⟨i, rfl⟩ := hell
    rw [litVar_exhaustiveVectorLiteral]
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨⟨exhaustiveVectorLiteral a i,
      (mem_exhaustiveVectorClause a _).2 ⟨i, rfl⟩,
      litVar_exhaustiveVectorLiteral a i⟩, Fin.castSucc_ne_last i⟩

/-- As long as one outside coordinate and the protected final coordinate are both free, no term
of the exhaustive protected gate is already satisfied.  This is the first order-independent
canonical-walk invariant: it uses only membership in the exhaustive family, not the ordering
chosen by `Finset.toList`. -/
theorem anyTermSat_exhaustiveVectorGate_eq_false_of_free
    {Q : ℕ} (sigma : Restriction (Q + 1))
    (hlast : sigma (Fin.last Q) = none)
    (hfree : ∃ i : Fin Q, sigma i.castSucc = none) :
    anyTermSat (exhaustiveVectorGate Q) sigma = false := by
  by_contra hsat
  rw [Bool.not_eq_false, anyTermSat, List.any_eq_true] at hsat
  obtain ⟨T, hT, hTsat⟩ := hsat
  rw [mem_exhaustiveVectorGate] at hT
  rcases hT with ⟨a, rfl⟩ | rfl
  · obtain ⟨i, hi⟩ := hfree
    rw [termSat, List.all_eq_true] at hTsat
    have hlit := hTsat (exhaustiveVectorLiteral a i)
      ((mem_exhaustiveVectorClause a _).2 ⟨i, rfl⟩)
    exact (litTrue_litVar_fixed hlit) (by
      rw [litVar_exhaustiveVectorLiteral, hi])
  · rw [termSat, List.all_eq_true] at hTsat
    have hlit := hTsat (Rung4Literal.pos (Fin.last Q)) (by
      simp [exhaustiveVectorTarget])
    exact (litTrue_litVar_fixed hlit) hlast

/-- Under the same partial-assignment invariant there is a live exhaustive competitor with a
free literal.  Its Boolean vector is chosen pointwise opposite every already fixed outside bit,
so no one of its literals is forced false; the assumed free coordinate supplies progress. -/
theorem exists_exhaustiveVectorClause_live_of_free
    {Q : ℕ} (sigma : Restriction (Q + 1))
    (hfree : ∃ i : Fin Q, sigma i.castSucc = none) :
    ∃ a : Fin Q → Bool,
      exhaustiveVectorClause a ∈ exhaustiveVectorGate Q ∧
      termFalsified sigma (exhaustiveVectorClause a) = false ∧
      0 < (freeLits sigma (exhaustiveVectorClause a)).length := by
  let a : Fin Q → Bool := fun i => !(sigma i.castSucc).getD false
  refine ⟨a, ?_, ?_, ?_⟩
  · exact (mem_exhaustiveVectorGate Q _).2 (Or.inl ⟨a, rfl⟩)
  · rw [termFalsified]
    apply List.any_eq_false.mpr
    intro ell hell
    obtain ⟨i, rfl⟩ := (mem_exhaustiveVectorClause a ell).mp hell
    simp only [litFalse, a, exhaustiveVectorLiteral]
    cases hs : sigma i.castSucc with
    | none => simp [hs, Depth3.litFixedVal]
    | some b => cases b <;> simp [hs, Depth3.litFixedVal]
  · obtain ⟨i, hi⟩ := hfree
    apply List.length_pos.mpr
    refine ⟨exhaustiveVectorLiteral a i, ?_⟩
    rw [freeLits, List.mem_filter]
    refine ⟨(mem_exhaustiveVectorClause a _).2 ⟨i, rfl⟩, ?_⟩
    rw [Depth3.litFree, litVar_exhaustiveVectorLiteral]
    cases exhaustiveVectorLiteral a i <;> simp_all [Depth3.litFixedVal, litVar]

/-- No assignment hits all Boolean-vector competitors: the pointwise opposite vector indexes a
clause with no falsified literal.  This proof works uniformly, including the empty-support case. -/
theorem exhaustiveVectorCore_unsatisfiable (Q : ℕ) :
    ¬ ∃ assignment,
      HitsOutsideCompetitorCore (exhaustiveVectorTarget Q)
        (exhaustiveVectorCore Q) assignment := by
  rintro ⟨assignment, hhit⟩
  let opposite : Fin Q → Bool := fun i => !(assignment i.castSucc)
  have hmem : ((0 : Fin 1), exhaustiveVectorClause opposite) ∈ exhaustiveVectorCore Q := by
    simp [exhaustiveVectorCore, exhaustiveVectorCoreEmbedding]
  obtain ⟨ell, hell, -, hvalue⟩ := hhit _ hmem
  obtain ⟨i, rfl⟩ := (mem_exhaustiveVectorClause opposite ell).mp hell
  rw [falValue_exhaustiveVectorLiteral, litVar_exhaustiveVectorLiteral] at hvalue
  simp [opposite] at hvalue

/-- The exponential core is inclusion-minimal for every support size.  After deleting the clause
indexed by `a`, use the pointwise complement of `a`; every other vector differs somewhere, and
at that coordinate its literal is falsified. -/
theorem exhaustiveVectorCore_inclusionMinimal (Q : ℕ) :
    InclusionMinimalUnsatisfiableCore (exhaustiveVectorTarget Q)
      (exhaustiveVectorCore Q) := by
  refine ⟨exhaustiveVectorCore_unsatisfiable Q, ?_⟩
  rintro ⟨g, U⟩ hp
  rw [exhaustiveVectorCore, Finset.mem_map] at hp
  obtain ⟨a, -, hpa⟩ := hp
  simp only [exhaustiveVectorCoreEmbedding] at hpa
  have hg : g = 0 := Subsingleton.elim _ _
  have hU : exhaustiveVectorClause a = U := congrArg Prod.snd hpa
  subst g
  subst U
  let witness : Fin (Q + 1) → Bool := fun j =>
    if h : j.val < Q then !(a ⟨j.val, h⟩) else false
  refine ⟨witness, ?_⟩
  intro p hpErase
  have hpCore := (Finset.mem_erase.mp hpErase).2
  rw [exhaustiveVectorCore, Finset.mem_map] at hpCore
  obtain ⟨b, -, hpb⟩ := hpCore
  simp only [exhaustiveVectorCoreEmbedding] at hpb
  subst p
  have hba : b ≠ a := by
    intro hba
    subst b
    exact (Finset.mem_erase.mp hpErase).1 rfl
  have hex : ∃ i, b i ≠ a i := by
    simpa only [Function.ne_iff] using hba
  obtain ⟨i, hi⟩ := hex
  refine ⟨exhaustiveVectorLiteral b i, ?_, ?_, ?_⟩
  · exact (mem_exhaustiveVectorClause b _).2 ⟨i, rfl⟩
  · rw [compatibleIsolationTargetVars_exhaustiveVectorTarget]
    simp [litVar_exhaustiveVectorLiteral, Fin.castSucc_ne_last]
  · rw [falValue_exhaustiveVectorLiteral, litVar_exhaustiveVectorLiteral]
    simp only [witness, Fin.val_castSucc, i.isLt, dite_true]
    cases hai : a i <;> cases hbi : b i <;> simp_all

/-- On the full embedded outside support, the core incidence relation is the complete rectangle:
every Boolean-vector clause contains every outside coordinate. -/
theorem exhaustiveVectorCore_queryIncidences_eq_product (Q : ℕ) :
    polarityCoreQueryIncidences (exhaustiveVectorTarget Q)
        (exhaustiveVectorCore Q) (Finset.univ.map Fin.castSuccEmb) =
      exhaustiveVectorCore Q ×ˢ (Finset.univ.map Fin.castSuccEmb) := by
  apply Finset.filter_eq_self.2
  rintro ⟨p, v⟩ hp
  have hpCore := (Finset.mem_product.mp hp).1
  have hv := (Finset.mem_product.mp hp).2
  rw [exhaustiveVectorCore, Finset.mem_map] at hpCore
  obtain ⟨a, -, hpa⟩ := hpCore
  simp only [exhaustiveVectorCoreEmbedding] at hpa
  have hclause : exhaustiveVectorClause a = p.2 := congrArg Prod.snd hpa
  rw [← hclause, competitorOutsideTargetVars_exhaustiveVectorClause]
  exact hv

/-- The aggregate arbitrary-support incidence count is exactly `2^Q * Q`. -/
theorem exhaustiveVectorCore_queryIncidences_card (Q : ℕ) :
    (polarityCoreQueryIncidences (exhaustiveVectorTarget Q)
      (exhaustiveVectorCore Q) (Finset.univ.map Fin.castSuccEmb)).card =
        2 ^ Q * Q := by
  rw [exhaustiveVectorCore_queryIncidences_eq_product, Finset.card_product,
    exhaustiveVectorCore_card, Finset.card_map]
  simp

/-- Every outside coordinate is incident to all `2^Q` clauses. -/
theorem exhaustiveVectorCore_queryIncidences_coordinate_fiber_card
    {Q : ℕ} (i : Fin Q) :
    ((polarityCoreQueryIncidences (exhaustiveVectorTarget Q)
      (exhaustiveVectorCore Q) (Finset.univ.map Fin.castSuccEmb)).filter
        fun p => p.2 = i.castSucc).card = 2 ^ Q := by
  rw [exhaustiveVectorCore_queryIncidences_eq_product]
  have heq :
      ((exhaustiveVectorCore Q ×ˢ (Finset.univ.map Fin.castSuccEmb)).filter
          fun p => p.2 = i.castSucc) =
        exhaustiveVectorCore Q ×ˢ {i.castSucc} := by
    ext p
    simp
  rw [heq, Finset.card_product, exhaustiveVectorCore_card]
  simp

/-- For positive support, the concrete protected gate and its exponential minimal core already
form a valid polarity certificate relative to the complete outside support.  The only remaining
canonical-gate obligation is to identify this support with the gate's actual `queriedVars`. -/
theorem exhaustiveVectorCore_polarityCycleValid (Q : ℕ) (hQ : 0 < Q) :
    PolarityCycleValid (exhaustiveVectorFamily Q) (exhaustiveVectorTarget Q) (fun g => g)
      (Finset.univ.map Fin.castSuccEmb) (exhaustiveVectorCore Q) := by
  refine ⟨?_, ?_, exhaustiveVectorCore_unsatisfiable Q⟩
  · rw [Finset.nonempty_iff_ne_empty, ← Finset.card_ne_zero]
    rw [exhaustiveVectorCore_card]
    exact pow_ne_zero _ (by omega)
  · intro p hp
    rw [exhaustiveVectorCore, Finset.mem_map] at hp
    obtain ⟨a, -, hpa⟩ := hp
    simp only [exhaustiveVectorCoreEmbedding] at hpa
    subst p
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [exhaustiveVectorFamily, exhaustiveVectorGate]
    · intro hut
      have hlits := congrArg Clause.lits hut
      simp [exhaustiveVectorClause, exhaustiveVectorTarget] at hlits
    · rw [competitorOutsideTargetVars_exhaustiveVectorClause]
      simpa using (Finset.univ_nonempty.mpr ⟨⟨0, hQ⟩⟩)
    · rw [competitorOutsideTargetVars_exhaustiveVectorClause]

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveThreeProtectedGate_normalized
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveThreeProtectedGate_queriedVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveThreeProtectedCore_eq_full
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveThreeProtectedCore_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveThreeProtectedCore_unsatisfiable
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveThreeProtectedCore_inclusionMinimal
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveThreeProtectedCore_polarityCycleValid
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveThreeProtectedCore_card_eq_two_pow_queried
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveThreeProtectedCore_queryIncidences_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveThreeProtectedCore_queryIncidences_coordinate_fiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveVectorCore_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveVectorCore_unsatisfiable
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveVectorCore_inclusionMinimal
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveVectorCore_eq_full
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveVectorCore_queryIncidences_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveVectorCore_queryIncidences_coordinate_fiber_card
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.exhaustiveVectorCore_polarityCycleValid

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

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
