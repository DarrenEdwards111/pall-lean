import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameJointTopMap

/-!
# N-Frame: K-port counting — the exact aggregate count, and its exact ceiling

The counting content of K-port compression, proved in full — and shown to be full:

  `mediated_triple_ext` — **PROVED**: the mediation data is determined by the selector — one variable, one
        gate, one reader.  A simultaneous mediation family is canonically indexed by its selectors.
  `selector_count_le_two_mul_ports` — **PROVED, the count**: a simultaneously mediated family of `K`
        selectors uses at least `⌈K/2⌉` distinct mediator ports — fibers of the port map have size at most
        two (`mediator_capacity_two`), summed over the image.
  `pinAll_congr` / `jointH_ports` — **PROVED, port-locality**: the joint top map reads its port vector only
        at the mediator positions — the `K`-port object is genuinely finite.

## Honest scope — where counting ends

This is the *complete* provable content of port counting, and it is tight: xor pair-gates realize two
selectors per port for every function (`xor_mediates_pair`), and ports are wires the connectivity bound
already prices.  No counting of ports, fibers, or positions can exceed edge strength.  The face's one open
step is **context-uniformity**: a single fixed set of port wire-functions and one pinned top must serve
*every* off-`S` context simultaneously, while SAT's remainders are context-dependent at every selector
(`sat3_reentry_not_rigid`) — counting SAT's realized subfunction patterns against that fixed family is the
remaining mountain, open and not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Extensionality: mediation data is determined by the selector -/

theorem mediated_triple_ext {n : ℕ} (c : List (CGate n)) (i : Fin n) (p r p' r' : ℕ)
    (h : MediatedAt c i p r) (h' : MediatedAt c i p' r') : p = p' ∧ r = r' := by
  have hp : p' = p := h.2.1 p' h'.1
  subst hp
  have hr : r' = r := h.2.2.2.2 r' h'.2.2.1
  exact ⟨rfl, hr.symm⟩

/-! ### Three distinct elements from a large fiber -/

theorem exists_three_of_two_lt_card {α : Type*} [DecidableEq α] {s : Finset α}
    (h : 2 < s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ d ∈ s, a ≠ b ∧ a ≠ d ∧ b ≠ d := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  have h1 : 0 < (s.erase a).card := by
    have := Finset.card_erase_of_mem ha
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp h1
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hbs : b ∈ s := Finset.mem_of_mem_erase hb
  have h2 : 0 < ((s.erase a).erase b).card := by
    have e1 := Finset.card_erase_of_mem ha
    have e2 := Finset.card_erase_of_mem hb
    omega
  obtain ⟨d, hd⟩ := Finset.card_pos.mp h2
  have hdb : d ≠ b := Finset.ne_of_mem_erase hd
  have hd' := Finset.mem_of_mem_erase hd
  have hda : d ≠ a := Finset.ne_of_mem_erase hd'
  exact ⟨a, ha, b, hbs, d, Finset.mem_of_mem_erase hd', fun hab => hba hab.symm,
    fun had => hda had.symm, fun hbd => hdb hbd.symm⟩

/-! ### The count -/

/-- **THE K-PORT COUNT (proved)**: a simultaneously mediated family of `K` selectors needs at least `⌈K/2⌉`
distinct mediator ports — port-map fibers have size at most two. -/
theorem selector_count_le_two_mul_ports {n : ℕ} (c : List (CGate n))
    (S : Finset (Fin n × ℕ × ℕ)) (hS : ∀ t ∈ S, MediatedAt c t.1 t.2.1 t.2.2) :
    S.card ≤ 2 * (S.image (fun t => t.2.2)).card := by
  classical
  have hfiber : ∀ b ∈ S.image (fun t => t.2.2),
      (S.filter (fun t => t.2.2 = b)).card ≤ 2 := by
    intro b _
    by_contra hbig
    push_neg at hbig
    obtain ⟨t₁, ht₁, t₂, ht₂, t₃, ht₃, h12, h13, h23⟩ :=
      exists_three_of_two_lt_card hbig
    rw [Finset.mem_filter] at ht₁ ht₂ ht₃
    have hm₁ := hS t₁ ht₁.1
    have hm₂ := hS t₂ ht₂.1
    have hm₃ := hS t₃ ht₃.1
    rw [ht₁.2] at hm₁
    rw [ht₂.2] at hm₂
    rw [ht₃.2] at hm₃
    -- distinct triples in a mediated family have distinct selectors
    have hi12 : t₁.1 ≠ t₂.1 := by
      intro hi
      apply h12
      obtain ⟨hp, -⟩ := mediated_triple_ext c t₁.1 t₁.2.1 b t₂.2.1 b hm₁ (hi ▸ hm₂)
      have h2a : t₁.2.2 = t₂.2.2 := by rw [ht₁.2, ht₂.2]
      exact Prod.ext hi (Prod.ext hp (by rw [ht₁.2, ht₂.2]))
    have hi13 : t₁.1 ≠ t₃.1 := by
      intro hi
      apply h13
      obtain ⟨hp, -⟩ := mediated_triple_ext c t₁.1 t₁.2.1 b t₃.2.1 b hm₁ (hi ▸ hm₃)
      exact Prod.ext hi (Prod.ext hp (by rw [ht₁.2, ht₃.2]))
    have hi23 : t₂.1 ≠ t₃.1 := by
      intro hi
      apply h23
      obtain ⟨hp, -⟩ := mediated_triple_ext c t₂.1 t₂.2.1 b t₃.2.1 b hm₂ (hi ▸ hm₃)
      exact Prod.ext hi (Prod.ext hp (by rw [ht₂.2, ht₃.2]))
    exact mediator_capacity_two c b t₁.1 t₂.1 t₃.1 t₁.2.1 t₂.2.1 t₃.2.1
      hm₁ hm₂ hm₃ hi12 hi13 hi23
  calc S.card = ∑ b ∈ S.image (fun t => t.2.2), (S.filter (fun t => t.2.2 = b)).card :=
        Finset.card_eq_sum_card_image (fun t => t.2.2) S
    _ ≤ ∑ _b ∈ S.image (fun t => t.2.2), 2 := Finset.sum_le_sum hfiber
    _ = 2 * (S.image (fun t => t.2.2)).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### Port-locality of the joint top map -/

theorem pinAll_congr {n : ℕ} (v v' : ℕ → Bool) :
    ∀ (S : List (Fin n × ℕ × ℕ)) (d : List (CGate n)),
      (∀ t ∈ S, v t.2.2 = v' t.2.2) → pinAll v S d = pinAll v' S d := by
  intro S
  induction S with
  | nil => intro d _; rfl
  | cons t rest ih =>
    intro d hv
    show pinAll v rest (d.take t.2.2 ++ CGate.cst (v t.2.2) :: d.drop (t.2.2 + 1))
        = pinAll v' rest (d.take t.2.2 ++ CGate.cst (v' t.2.2) :: d.drop (t.2.2 + 1))
    rw [hv t List.mem_cons_self]
    exact ih _ (fun t' ht' => hv t' (List.mem_cons_of_mem t ht'))

/-- **Port-locality (proved)**: the joint top map (the `pinAll` witness of `joint_top_map`) reads its port
vector only at the mediator positions. -/
theorem jointH_ports {n : ℕ} (c : List (CGate n)) (S : List (Fin n × ℕ × ℕ))
    (v v' : ℕ → Bool) (x : Fin n → Bool) (h : ∀ t ∈ S, v t.2.2 = v' t.2.2) :
    output (pinAll v S c) x = output (pinAll v' S c) x := by
  rw [pinAll_congr v v' S c h]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.mediated_triple_ext
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.selector_count_le_two_mul_ports
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.jointH_ports
