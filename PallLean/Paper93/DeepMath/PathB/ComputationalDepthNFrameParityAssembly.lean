import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityThread
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityMass

/-!
# N-Frame: the parity assembly — the drag over the constructed row family

Rung 28g of the arc (… → parity thread/mass → **parity assembly**).  The final wiring of the
drag: ONE explicit row family (`rowOf` — tuple characteristic on the priced positions, kit
constants at all non-reserve blocks, row-side scaffold), its four read lemmas, and the
assembled theorem discharging `parity_tuple_drag`'s interfaces:

  `rowOf` / `rowOf_read_V` / `rowOf_read_kit` / `rowOf_read_reserve` / `rowOf_read_target`
        — the row family and its reads (all `xbit_inj` geometry).
  `parity_assembled_pair` — **PROVED**: for tuples `E, E' ⊆ V` differing at a target
        `q₀ ∈ E' ∖ E`, the constructed probe distinguishes the two rows' mixes — the full
        composition through `parity_pair_dist_singleton`.
  `parity_assembled_drag` — **PROVED, THE ASSEMBLED DRAG**: under a cut factorization of the
        parity family, `V.card ≤ j` — with the per-target supply given as flat
        function-hypotheses.

The two NAMED expander-conditional hypothesis classes (kept hypothetical per the
skeleton-first plan):
  `hlive`      — per-target pin selectors at the reserve are probe-side;
  `hTautProbe` — the data blocks' tautology selectors are probe-side.
Everything else is layout (codebook enumeration), row design (discharged here by
construction), or side-placement bookkeeping.

## Honest scope

The remaining distance to the `(2+c)N` headline: the counting instantiation (the two
liveness classes + the scaffold-availability from the kill/capacity accounting at ratio
`1 + c_d·d` — the expander long-pole), the per-block transversal choice of `V` inside the
Markov-selected data mass (rung 28f supplies the mass), and rung 29 (root-shape,
essential variables, the `cbudget` conversion).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityAssembly

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityProbe
open PallLean.Paper93.DeepMath.PathB.NFrameParitySupply
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityThread
open PallLean.Paper93.DeepMath.PathB.NFrameParityDrag
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

/-! ### The row family -/

/-- The row family: tuple characteristic on the priced positions, kit constants at all
non-reserve blocks, row-side scaffold. -/
def rowOf (hfit : m * L ≤ N) (tautIdx : Fin L) (RS : Finset (Fin m))
    (SCR : Finset (Fin m × Fin L)) (E : Finset (Fin m × Fin L))
    (p : Fin N) : Bool :=
  decide ((∃ q ∈ E, p = xbit hfit q.1 q.2)
    ∨ (∃ c ∈ (Finset.univ : Finset (Fin m)) \ RS, p = xbit hfit c tautIdx)
    ∨ (∃ q ∈ SCR, p = xbit hfit q.1 q.2))

theorem rowOf_read_V (hfit : m * L ≤ N) (tautIdx : Fin L) (RS : Finset (Fin m))
    (SCR : Finset (Fin m × Fin L)) (V : Finset (Fin m × Fin L))
    (hVt : ∀ q ∈ V, q.2 ≠ tautIdx)
    (hVSCR : ∀ q ∈ V, q ∉ SCR)
    (E : Finset (Fin m × Fin L)) (hE : E ⊆ V)
    {q : Fin m × Fin L} (hq : q ∈ V) :
    rowOf hfit tautIdx RS SCR E (xbit hfit q.1 q.2) = decide (q ∈ E) := by
  unfold rowOf
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨q', hq', heq⟩ | ⟨c', hc', heq⟩ | ⟨q', hq', heq⟩)
    · obtain ⟨h1, h2⟩ := xbit_inj hfit heq
      have hqq : q = q' := Prod.ext h1 h2
      rw [hqq]
      exact hq'
    · obtain ⟨-, h2⟩ := xbit_inj hfit heq
      exact absurd h2 (hVt q hq)
    · obtain ⟨h1, h2⟩ := xbit_inj hfit heq
      have hqq : q = q' := Prod.ext h1 h2
      exact absurd (hqq ▸ hq') (hVSCR q hq)
  · intro hqE
    exact Or.inl ⟨q, hqE, rfl⟩

theorem rowOf_read_kit (hfit : m * L ≤ N) (tautIdx : Fin L) (RS : Finset (Fin m))
    (SCR : Finset (Fin m × Fin L)) (E : Finset (Fin m × Fin L))
    {c : Fin m} (hc : c ∉ RS) :
    rowOf hfit tautIdx RS SCR E (xbit hfit c tautIdx) = true := by
  unfold rowOf
  exact decide_eq_true (Or.inr (Or.inl
    ⟨c, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩))

theorem rowOf_read_reserve (hfit : m * L ≤ N) (tautIdx : Fin L) (RS : Finset (Fin m))
    (SCR : Finset (Fin m × Fin L)) (V : Finset (Fin m × Fin L))
    (hVRS : ∀ q ∈ V, q.1 ∉ RS)
    (hSCRRS : ∀ q ∈ SCR, q.1 ∉ RS)
    (E : Finset (Fin m × Fin L)) (hE : E ⊆ V)
    {c : Fin m} (hc : c ∈ RS) (i : Fin L) :
    rowOf hfit tautIdx RS SCR E (xbit hfit c i) = false := by
  unfold rowOf
  apply decide_eq_false
  rintro (⟨q', hq', heq⟩ | ⟨c', hc', heq⟩ | ⟨q', hq', heq⟩)
  · obtain ⟨h1, -⟩ := xbit_inj hfit heq
    apply hVRS q' (hE hq')
    rw [← h1]
    exact hc
  · obtain ⟨h1, -⟩ := xbit_inj hfit heq
    have hc'RS : c' ∉ RS := (Finset.mem_sdiff.mp hc').2
    apply hc'RS
    rw [← h1]
    exact hc
  · obtain ⟨h1, -⟩ := xbit_inj hfit heq
    apply hSCRRS q' hq'
    rw [← h1]
    exact hc

theorem rowOf_read_target (hfit : m * L ≤ N) (tautIdx : Fin L) (RS : Finset (Fin m))
    (SCR : Finset (Fin m × Fin L)) (V : Finset (Fin m × Fin L))
    (S : Finset (Fin N))
    (hVt : ∀ q ∈ V, q.2 ≠ tautIdx)
    (E : Finset (Fin m × Fin L)) (hE : E ⊆ V)
    {cstar : Fin m} (htp : xbit hfit cstar tautIdx ∈ Sᶜ)
    (i : Fin L) (hi : xbit hfit cstar i ∉ Sᶜ) :
    rowOf hfit tautIdx RS SCR E (xbit hfit cstar i) = true
      ↔ ((cstar, i) ∈ E ∨ i ∈ (SCR.filter (fun r => r.1 = cstar)).image Prod.snd) := by
  unfold rowOf
  rw [decide_eq_true_eq]
  constructor
  · rintro (⟨q', hq', heq⟩ | ⟨c', hc', heq⟩ | ⟨q', hq', heq⟩)
    · obtain ⟨h1, h2⟩ := xbit_inj hfit heq
      left
      have hqq : ((cstar, i) : Fin m × Fin L) = q' := Prod.ext h1 h2
      rw [hqq]
      exact hq'
    · obtain ⟨-, h2⟩ := xbit_inj hfit heq
      exfalso
      apply hi
      rw [h2]
      exact htp
    · obtain ⟨h1, h2⟩ := xbit_inj hfit heq
      right
      exact Finset.mem_image.mpr ⟨q', Finset.mem_filter.mpr ⟨hq', h1.symm⟩, h2.symm⟩
  · rintro (hEmem | hscr)
    · exact Or.inl ⟨(cstar, i), hEmem, rfl⟩
    · obtain ⟨q', hq', hsnd⟩ := Finset.mem_image.mp hscr
      rw [Finset.mem_filter] at hq'
      refine Or.inr (Or.inr ⟨q', hq'.1, ?_⟩)
      rw [hq'.2, hsnd]

/-! ### The assembled pair -/

set_option maxHeartbeats 3200000 in
/-- **The assembled pair (proved)**: tuples differing at a target are distinguished by the
constructed probe — the full composition through the threaded discharge. -/
theorem parity_assembled_pair (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (RS : Finset (Fin m)) (SCR : Finset (Fin m × Fin L))
    (V : Finset (Fin m × Fin L)) (S : Finset (Fin N))
    -- per-target supply data (functions over targets)
    (pinIdxF : Fin m × Fin L → Fin m → Fin L)
    (SCF : Fin m × Fin L → Finset (Fin L))
    (jstarF : Fin m × Fin L → Fin v) (bstarF : Fin m × Fin L → ZMod 2)
    (KF : Fin m × Fin L → Finset (Fin v)) (bvalF : Fin m × Fin L → Fin v → ZMod 2)
    -- positional discipline
    (hVt : ∀ q ∈ V, q.2 ≠ tautIdx)
    (hVSCR : ∀ q ∈ V, q ∉ SCR)
    (hVRS : ∀ q ∈ V, q.1 ∉ RS)
    (hSCRRS : ∀ q ∈ SCR, q.1 ∉ RS)
    (hVS : ∀ q ∈ V, xbit hfit q.1 q.2 ∉ Sᶜ)
    (hSCRS : ∀ q ∈ SCR, xbit hfit q.1 q.2 ∉ Sᶜ)
    (hTautProbe : ∀ q ∈ V, xbit hfit q.1 tautIdx ∈ Sᶜ)
    -- codebook layout
    (hcodeTaut : code tautIdx = tautLit v)
    (hcodeStar : ∀ q ∈ V, code q.2 = (single v (jstarF q), bstarF q))
    (hKstar : ∀ q ∈ V, jstarF q ∉ KF q)
    (hcodeV : ∀ q ∈ V, ∀ i : Fin L, (q.1, i) ∈ V → i ≠ q.2 →
      ∃ j ∈ KF q, code i = (single v j, bvalF q j))
    (hpinCode : ∀ q ∈ V, ∀ c ∈ RS,
      ∃ j ∈ KF q, code (pinIdxF q c) = (single v j, bvalF q j + 1))
    (hpinCover : ∀ q ∈ V, ∀ j ∈ KF q,
      ∃ c ∈ RS, code (pinIdxF q c) = (single v j, bvalF q j + 1))
    (hscaffold : ∀ q ∈ V,
      (((SCF q).filter (fun i => xbit hfit q.1 i ∈ Sᶜ))
        ∪ (SCR.filter (fun r => r.1 = q.1)).image Prod.snd).image code
      = ((Finset.univ : Finset (Fin v)) \ insert (jstarF q) (KF q)).image
          (fun j => ((single v j, (1 : ZMod 2)) : Lit v)))
    -- THE EXPANDER-CONDITIONAL LIVENESS
    (hlive : ∀ q ∈ V, ∀ c ∈ RS, xbit hfit c (pinIdxF q c) ∈ Sᶜ)
    -- the pair
    (E E' : Finset (Fin m × Fin L)) (hE : E ⊆ V) (hE' : E' ⊆ V)
    (q₀ : Fin m × Fin L) (hq₀V : q₀ ∈ V) (hq₀E' : q₀ ∈ E') (hq₀E : q₀ ∉ E) :
    parityFamilyBits code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx (pinIdxF q₀) (SCF q₀)
        ((Finset.univ \ RS).erase q₀.1) RS q₀.1)
        (rowOf hfit tautIdx RS SCR E))
    ≠ parityFamilyBits code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx (pinIdxF q₀) (SCF q₀)
        ((Finset.univ \ RS).erase q₀.1) RS q₀.1)
        (rowOf hfit tautIdx RS SCR E')) := by
  classical
  set KB : Finset (Fin m) := (Finset.univ \ RS).erase q₀.1 with hKB
  have hq₀RS : q₀.1 ∉ RS := hVRS q₀ hq₀V
  apply parity_pair_dist_singleton code hfit tautIdx (pinIdxF q₀) (SCF q₀)
    KB RS q₀.1 q₀.2 S
    (rowOf hfit tautIdx RS SCR E) (rowOf hfit tautIdx RS SCR E')
    E E' ((SCR.filter (fun r => r.1 = q₀.1)).image Prod.snd)
    (jstarF q₀) (bstarF q₀) (KF q₀) (bvalF q₀)
    hcodeTaut
    (by
      have h := hcodeStar q₀ hq₀V
      exact h)
    (hKstar q₀ hq₀V)
    (by
      intro i hi
      have hne : i ≠ q₀.2 := by
        intro hcon
        apply hq₀E
        have : ((q₀.1, i) : Fin m × Fin L) = q₀ := by
          rw [hcon]
        rw [← this]
        exact hi
      exact hcodeV q₀ hq₀V i (hE hi) hne)
    (by
      intro i hi hne
      exact hcodeV q₀ hq₀V i (hE' hi) hne)
    (hpinCode q₀ hq₀V)
    (hpinCover q₀ hq₀V)
    (hscaffold q₀ hq₀V)
    (by
      intro c hc
      by_cases hcRS : c ∈ RS
      · exact Or.inr hcRS
      · exact Or.inl (Finset.mem_erase.mpr ⟨hc,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcRS⟩⟩))
    (by
      intro c hc
      intro hcKB
      have := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hcKB)).2
      exact this hc)
    (by
      intro hcon
      exact (Finset.ne_of_mem_erase hcon) rfl)
    hq₀RS
    (hlive q₀ hq₀V)
    (by
      intro c hc
      have hcRS : c ∉ RS := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hc)).2
      exact rowOf_read_kit hfit tautIdx RS SCR E hcRS)
    (by
      intro c hc
      have hcRS : c ∉ RS := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hc)).2
      exact rowOf_read_kit hfit tautIdx RS SCR E' hcRS)
    (by
      intro c hc i
      exact rowOf_read_reserve hfit tautIdx RS SCR V hVRS hSCRRS E hE hc i)
    (by
      intro c hc i
      exact rowOf_read_reserve hfit tautIdx RS SCR V hVRS hSCRRS E' hE' hc i)
    (by
      intro i hi
      exact hVS (q₀.1, i) (hE hi))
    (by
      intro i hi
      exact hVS (q₀.1, i) (hE' hi))
    (by
      intro i hi
      obtain ⟨q', hq', hsnd⟩ := Finset.mem_image.mp hi
      rw [Finset.mem_filter] at hq'
      have := hSCRS q' hq'.1
      rw [hq'.2, hsnd] at this
      exact this)
    (by
      intro i hi
      exact rowOf_read_target hfit tautIdx RS SCR V S hVt E hE
        (hTautProbe q₀ hq₀V) i hi)
    (by
      intro i hi
      exact rowOf_read_target hfit tautIdx RS SCR V S hVt E' hE'
        (hTautProbe q₀ hq₀V) i hi)
    (by
      show ((q₀.1, q₀.2) : Fin m × Fin L) ∈ E'
      rw [show ((q₀.1, q₀.2) : Fin m × Fin L) = q₀ from rfl]
      exact hq₀E')

/-! ### The assembled drag -/

set_option maxHeartbeats 3200000 in
/-- **THE ASSEMBLED DRAG (proved)**: under a cut factorization of the parity family, the
priced position set obeys `V.card ≤ j` — with the per-target supply as flat hypotheses and
the two liveness classes named expander-conditional. -/
theorem parity_assembled_drag (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (RS : Finset (Fin m)) (SCR : Finset (Fin m × Fin L))
    (V : Finset (Fin m × Fin L))
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (parityFamilyBits code hfit) S j)
    (pinIdxF : Fin m × Fin L → Fin m → Fin L)
    (SCF : Fin m × Fin L → Finset (Fin L))
    (jstarF : Fin m × Fin L → Fin v) (bstarF : Fin m × Fin L → ZMod 2)
    (KF : Fin m × Fin L → Finset (Fin v)) (bvalF : Fin m × Fin L → Fin v → ZMod 2)
    (hVt : ∀ q ∈ V, q.2 ≠ tautIdx)
    (hVSCR : ∀ q ∈ V, q ∉ SCR)
    (hVRS : ∀ q ∈ V, q.1 ∉ RS)
    (hSCRRS : ∀ q ∈ SCR, q.1 ∉ RS)
    (hVS : ∀ q ∈ V, xbit hfit q.1 q.2 ∉ Sᶜ)
    (hSCRS : ∀ q ∈ SCR, xbit hfit q.1 q.2 ∉ Sᶜ)
    (hTautProbe : ∀ q ∈ V, xbit hfit q.1 tautIdx ∈ Sᶜ)
    (hcodeTaut : code tautIdx = tautLit v)
    (hcodeStar : ∀ q ∈ V, code q.2 = (single v (jstarF q), bstarF q))
    (hKstar : ∀ q ∈ V, jstarF q ∉ KF q)
    (hcodeV : ∀ q ∈ V, ∀ i : Fin L, (q.1, i) ∈ V → i ≠ q.2 →
      ∃ j' ∈ KF q, code i = (single v j', bvalF q j'))
    (hpinCode : ∀ q ∈ V, ∀ c ∈ RS,
      ∃ j' ∈ KF q, code (pinIdxF q c) = (single v j', bvalF q j' + 1))
    (hpinCover : ∀ q ∈ V, ∀ j' ∈ KF q,
      ∃ c ∈ RS, code (pinIdxF q c) = (single v j', bvalF q j' + 1))
    (hscaffold : ∀ q ∈ V,
      (((SCF q).filter (fun i => xbit hfit q.1 i ∈ Sᶜ))
        ∪ (SCR.filter (fun r => r.1 = q.1)).image Prod.snd).image code
      = ((Finset.univ : Finset (Fin v)) \ insert (jstarF q) (KF q)).image
          (fun j' => ((single v j', (1 : ZMod 2)) : Lit v)))
    (hlive : ∀ q ∈ V, ∀ c ∈ RS, xbit hfit c (pinIdxF q c) ∈ Sᶜ) :
    V.card ≤ j := by
  classical
  apply parity_tuple_drag code hfit hcut V (rowOf hfit tautIdx RS SCR)
  · intro E hE q hq
    exact rowOf_read_V hfit tautIdx RS SCR V hVt hVSCR E
      (Finset.mem_powerset.mp hE) hq
  · intro E hE E' hE' hne
    have hEsub := Finset.mem_powerset.mp hE
    have hE'sub := Finset.mem_powerset.mp hE'
    -- a differing position exists
    have hdiff : ∃ q, (q ∈ E' ∧ q ∉ E) ∨ (q ∈ E ∧ q ∉ E') := by
      by_contra hcon
      push_neg at hcon
      apply hne
      ext q
      have h := hcon q
      constructor
      · intro hq
        exact h.2 hq
      · intro hq
        exact h.1 hq
    obtain ⟨q₀, hcase⟩ := hdiff
    rcases hcase with ⟨hq₀E', hq₀E⟩ | ⟨hq₀E, hq₀E'⟩
    · have hq₀V : q₀ ∈ V := hE'sub hq₀E'
      exact ⟨probeOn hfit tautIdx (pinIdxF q₀) (SCF q₀)
        ((Finset.univ \ RS).erase q₀.1) RS q₀.1,
        parity_assembled_pair code hfit tautIdx RS SCR V S
          pinIdxF SCF jstarF bstarF KF bvalF
          hVt hVSCR hVRS hSCRRS hVS hSCRS hTautProbe
          hcodeTaut hcodeStar hKstar hcodeV hpinCode hpinCover hscaffold hlive
          E E' hEsub hE'sub q₀ hq₀V hq₀E' hq₀E⟩
    · have hq₀V : q₀ ∈ V := hEsub hq₀E
      refine ⟨probeOn hfit tautIdx (pinIdxF q₀) (SCF q₀)
        ((Finset.univ \ RS).erase q₀.1) RS q₀.1, ?_⟩
      exact (parity_assembled_pair code hfit tautIdx RS SCR V S
        pinIdxF SCF jstarF bstarF KF bvalF
        hVt hVSCR hVRS hSCRRS hVS hSCRS hTautProbe
        hcodeTaut hcodeStar hKstar hcodeV hpinCode hpinCover hscaffold hlive
        E' E hE'sub hEsub q₀ hq₀V hq₀E hq₀E').symm

end PallLean.Paper93.DeepMath.PathB.NFrameParityAssembly

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityAssembly.parity_assembled_pair
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityAssembly.parity_assembled_drag
