import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameThicknessCharge

/-!
# N-Frame: slot-multiplicity connectivity — every doubly-read wire is priced

The refinement of the connectivity bound named in the thickness charge.  The original count let a wire with
many readers fill many parent slots for free (`card_biUnion_le` collapses multiplicity); here the incidence
set is counted fiberwise, so every reader beyond the first adds one to the bound.

  `coneExcess` — the total excess fanout of the output cone: `Σ_{w ∈ cone, w ≠ root} (#readers(w) − 1)`.
  `connectivity_fanout` — **PROVED, the refined bound (any circuit)**: for every circuit computing `f` with
        `K` essential variables, `2·K + coneExcess ≤ length + 1`.  Sharing is no longer free: each extra
        read of any cone wire forces one more gate beyond the tree minimum.
  `sat3_connectivity_fanout` / `sat3_excess_priced` — **PROVED, the SAT ledger**: every circuit computing
        `sat3Family` obeys `2·m·D + coneExcess ≤ length + 1`; for the minimal circuit the excess is priced
        directly against the budget: `2·m·D + coneExcess ≤ cbudget + 1`.

## Honest scope

The refinement is unconditional and per-circuit, and it converts the open mountain into a pure excess
question: the record improves beyond `2·m·D − 1` by exactly what excess fanout can be **forced**.  Nothing
here forces excess yet.  The excess-zero corner is a circuit where every cone wire has one reader — with
read-uniqueness that is a read-once formula — so the first `+1` is exactly SAT-is-not-read-once, and the
`Ω(m)` charge is the mountain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Total excess fanout of the cone: readers beyond the first, summed over non-root cone wires. -/
def coneExcess {n : ℕ} (c : List (CGate n)) (root : ℕ) : ℕ :=
  ∑ w ∈ (coneOf c root).erase root,
    (((coneOf c root).filter (fun q => w ∈ childrenOf c q)).card - 1)

/-- **THE REFINED CONNECTIVITY BOUND (proved)**: `2·K + coneExcess ≤ length + 1` — every reader beyond the
first, on any cone wire, forces one more gate beyond the tree minimum. -/
theorem connectivity_fanout {n : ℕ} (f : (Fin n → Bool) → Bool) (V : Finset (Fin n))
    (hess : ∀ i ∈ V, ∃ x₁ x₀ : Fin n → Bool,
      (∀ b : Fin n, x₁ b ≠ x₀ b → b = i) ∧ f x₁ ≠ f x₀)
    (c : List (CGate n)) (hcomp : computes c f) :
    2 * V.card + coneExcess c (c.length - 1) ≤ c.length + 1 := by
  classical
  by_cases hc : c = []
  · subst hc
    have hV0 : V = ∅ := by
      by_contra hVne
      obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hVne
      obtain ⟨x₁, x₀, -, hnev⟩ := hess i₀ hi₀
      apply hnev
      rw [← hcomp x₁, ← hcomp x₀]
      rfl
    have hEX : coneExcess ([] : List (CGate n)) 0 = 0 := by
      unfold coneExcess
      rw [coneOf_eq_cst ([] : List (CGate n)) 0 false
        (List.getD_eq_default _ _ (by simp))]
      rw [Finset.erase_insert (Finset.notMem_empty 0)]
      rfl
    have hEX' : coneExcess ([] : List (CGate n))
        (List.length ([] : List (CGate n)) - 1) = 0 := hEX
    rw [hV0, Finset.card_empty]
    omega
  have hcpos : 0 < c.length :=
    Nat.pos_of_ne_zero (fun h => hc (List.eq_nil_of_length_eq_zero h))
  set root : ℕ := c.length - 1 with hroot
  set R : Finset ℕ := coneOf c root with hRdef
  -- every essential variable owns a var gate in the cone
  have hvarin : ∀ i ∈ V, ∃ p ∈ R, c.getD p (CGate.cst false) = CGate.var i := by
    intro i hi
    obtain ⟨x₁, x₀, hd, hnev⟩ := hess i hi
    by_contra hno
    push_neg at hno
    apply hnev
    rw [← hcomp x₁, ← hcomp x₀]
    show (runFrom x₁ [] c).getD (c.length - 1) false
        = (runFrom x₀ [] c).getD (c.length - 1) false
    apply cone_val_agree c root x₁ x₀ ?_ (c.length - 1) ?_
    · intro p hp i' hgate
      by_cases hii : i' = i
      · exact absurd (hii ▸ hgate) (hno p hp)
      · by_contra hne
        exact hii (hd i' hne)
    · exact cone_self c root
  set pos : Fin n → ℕ := fun i =>
    if h : ∃ p ∈ R, c.getD p (CGate.cst false) = CGate.var i then h.choose else 0
    with hposdef
  have hposmem : ∀ i ∈ V, pos i ∈ R ∧ c.getD (pos i) (CGate.cst false) = CGate.var i := by
    intro i hi
    have h := hvarin i hi
    have hp : pos i = h.choose := by
      rw [hposdef]
      exact dif_pos h
    rw [hp]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  set A : Finset ℕ := R.filter (fun p => isVarGate (c.getD p (CGate.cst false)) = true)
    with hA
  set B : Finset ℕ := R.filter (fun p => isUnGate (c.getD p (CGate.cst false)) = true)
    with hB
  set C : Finset ℕ := R.filter (fun p => isBinGate (c.getD p (CGate.cst false)) = true)
    with hC
  have hVcard : V.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn pos
    · intro i hi
      obtain ⟨hmem, hgate⟩ := hposmem i (Finset.mem_coe.mp hi)
      rw [hA]
      show pos i ∈ Finset.filter _ R
      rw [Finset.mem_filter]
      refine ⟨hmem, ?_⟩
      rw [hgate]
      rfl
    · intro i hi i' hi' heq
      obtain ⟨-, hg⟩ := hposmem i (Finset.mem_coe.mp hi)
      obtain ⟨-, hg'⟩ := hposmem i' (Finset.mem_coe.mp hi')
      rw [heq] at hg
      exact CGate.var.inj (hg.symm.trans hg')
  have hABdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    rw [hA, Finset.mem_filter] at hpA
    rw [hB, Finset.mem_filter] at hpB
    cases hg : c.getD p (CGate.cst false) with
    | var i => rw [hg] at hpB; exact Bool.noConfusion hpB.2
    | cst b => rw [hg] at hpA; exact Bool.noConfusion hpA.2
    | un op j => rw [hg] at hpA; exact Bool.noConfusion hpA.2
    | bin op j k => rw [hg] at hpA; exact Bool.noConfusion hpA.2
  have hABCdis : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro p hpAB hpC
    rw [hC, Finset.mem_filter] at hpC
    rcases Finset.mem_union.mp hpAB with hpA | hpB
    · rw [hA, Finset.mem_filter] at hpA
      cases hg : c.getD p (CGate.cst false) with
      | var i => rw [hg] at hpC; exact Bool.noConfusion hpC.2
      | cst b => rw [hg] at hpA; exact Bool.noConfusion hpA.2
      | un op j => rw [hg] at hpA; exact Bool.noConfusion hpA.2
      | bin op j k => rw [hg] at hpA; exact Bool.noConfusion hpA.2
    · rw [hB, Finset.mem_filter] at hpB
      cases hg : c.getD p (CGate.cst false) with
      | var i => rw [hg] at hpB; exact Bool.noConfusion hpB.2
      | cst b => rw [hg] at hpB; exact Bool.noConfusion hpB.2
      | un op j => rw [hg] at hpC; exact Bool.noConfusion hpC.2
      | bin op j k => rw [hg] at hpB; exact Bool.noConfusion hpB.2
  have hABC : A.card + B.card + C.card ≤ R.card := by
    have h1 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hABdis
    have h2 : ((A ∪ B) ∪ C).card = (A ∪ B).card + C.card :=
      Finset.card_union_of_disjoint hABCdis
    have h3 : (A ∪ B) ∪ C ⊆ R := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp' | hp'
      · rcases Finset.mem_union.mp hp' with hp'' | hp''
        · exact (Finset.mem_filter.mp (hA ▸ hp'')).1
        · exact (Finset.mem_filter.mp (hB ▸ hp'')).1
      · exact (Finset.mem_filter.mp (hC ▸ hp')).1
    have h4 := Finset.card_le_card h3
    omega
  -- REFINED rooted count: every reader beyond the first is priced
  have hrc1 : ∀ w ∈ R.erase root,
      1 ≤ (R.filter (fun q => w ∈ childrenOf c q)).card := by
    intro w hw
    obtain ⟨hwne, hwR⟩ := Finset.mem_erase.mp hw
    rcases cone_parent c root w hwR with rfl | ⟨r, hr, hchild⟩
    · exact absurd rfl hwne
    · exact Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hchild⟩⟩
  have hdouble : ∑ p ∈ R, ((R.erase root).filter (fun w => w ∈ childrenOf c p)).card
      = ∑ w ∈ R.erase root, (R.filter (fun q => w ∈ childrenOf c q)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hincle : ∀ p ∈ R, ((R.erase root).filter (fun w => w ∈ childrenOf c p)).card
      ≤ (childrenOf c p).card := by
    intro p _
    apply Finset.card_le_card
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hsum_split : ∑ w ∈ R.erase root, (R.filter (fun q => w ∈ childrenOf c q)).card
      = (R.erase root).card + coneExcess c root := by
    have h : ∀ w ∈ R.erase root, (R.filter (fun q => w ∈ childrenOf c q)).card
        = 1 + ((R.filter (fun q => w ∈ childrenOf c q)).card - 1) := by
      intro w hw
      have := hrc1 w hw
      omega
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hsum1' : R.card + coneExcess c root ≤ 1 + ∑ p ∈ R, (childrenOf c p).card := by
    have h1 : ∑ w ∈ R.erase root, (R.filter (fun q => w ∈ childrenOf c q)).card
        ≤ ∑ p ∈ R, (childrenOf c p).card := by
      rw [← hdouble]
      exact Finset.sum_le_sum hincle
    have h2 : (R.erase root).card = R.card - 1 :=
      Finset.card_erase_of_mem (hRdef ▸ cone_self c root)
    have h3 : 1 ≤ R.card := Finset.card_pos.mpr ⟨root, hRdef ▸ cone_self c root⟩
    omega
  have hsum2 : ∑ p ∈ R, (childrenOf c p).card ≤ ∑ p ∈ R, gateWeight c p :=
    Finset.sum_le_sum (fun p _ => childrenOf_card_le c p)
  have hpt : ∀ p, gateWeight c p
      = (if isUnGate (c.getD p (CGate.cst false)) = true then 1 else 0)
        + (if isBinGate (c.getD p (CGate.cst false)) = true then 2 else 0) := by
    intro p
    unfold gateWeight
    cases c.getD p (CGate.cst false) <;> rfl
  have hsum3 : ∑ p ∈ R, gateWeight c p = B.card + 2 * C.card := by
    rw [Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_add_distrib]
    congr 1
    · rw [hB, Finset.card_filter]
    · have h2 : ∀ p ∈ R, (if isBinGate (c.getD p (CGate.cst false)) = true then 2 else 0)
          = 2 * (if isBinGate (c.getD p (CGate.cst false)) = true then 1 else 0) := by
        intro p _
        split <;> rfl
      rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, hC, Finset.card_filter]
  have hrange : R ⊆ Finset.range c.length := by
    intro p hp
    rw [Finset.mem_range]
    have h := cone_le c root p hp
    omega
  have hRlen : R.card ≤ c.length := by
    have h := Finset.card_le_card hrange
    rw [Finset.card_range] at h
    exact h
  omega

/-- **THE SAT LEDGER (proved)**: every circuit computing `sat3Family` pays for its sharing —
`2·m·D + coneExcess ≤ length + 1`. -/
theorem sat3_connectivity_fanout (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N)) :
    2 * (sat3M N * sat3D N) + coneExcess c (c.length - 1) ≤ c.length + 1 := by
  have hinj : Function.Injective
      (fun p : Fin (sat3M N) × Fin 3 × Fin (sat3V N + 1) =>
        sat3Bit N p.1 p.2.1 p.2.2.val p.2.2.isLt) := by
    intro p q h
    obtain ⟨hc, ht, hf⟩ := sat3Bit_inj N p.2.2.isLt q.2.2.isLt h
    exact Prod.ext hc (Prod.ext ht (Fin.ext hf))
  have h := connectivity_fanout (sat3Family N)
    (Finset.univ.image (fun p : Fin (sat3M N) × Fin 3 × Fin (sat3V N + 1) =>
      sat3Bit N p.1 p.2.1 p.2.2.val p.2.2.isLt))
    (by
      intro i hi
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨x₁, x₀, h1, h0, hforce⟩ :=
        sat3_layout_pair N hv hm2 p.1 p.2.1 p.2.2.val p.2.2.isLt
      exact ⟨x₁, x₀, hforce, by
        rw [h1, h0]
        decide⟩)
    c hcomp
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at h
  have hD : sat3M N * sat3D N = sat3M N * (3 * (sat3V N + 1)) := rfl
  omega

/-- **EXCESS PRICED AGAINST THE BUDGET (proved)**: for a minimal SAT circuit, every unit of excess fanout
raises the record — `2·m·D + coneExcess ≤ cbudget + 1`. -/
theorem sat3_excess_priced (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) :
    2 * (sat3M N * sat3D N) + coneExcess c (c.length - 1)
      ≤ cbudget (sat3Family N) + 1 := by
  rw [← hmin]
  exact sat3_connectivity_fanout N hv hm2 c hcomp

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.connectivity_fanout
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_connectivity_fanout
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_excess_priced
