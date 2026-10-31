import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDAGTwoKill

/-!
# N-Frame: fan-out accounting — restriction kills `1 + fanout` gates through sharing

The sharing-aware per-step rate, made exact.  When a variable is fixed, its gate dies *and so does every
interior reader of its wire*: each reader absorbs the constant, becomes a constant or unary gate, and the
redundancy engine deletes them all — reuse of the dead wire is charged gate by gate.

  `redundantCount` / `shrink_all` — **PROVED, the engine**: a circuit computing a non-constant function shrinks
        below its interior constant and unary gates *simultaneously* — `cbudget f' + K ≤ length` for
        `K ≤ redundantCount` — because both surgeries map constants to constants and unary gates to unary or
        constant gates, so pending redundancy survives each deletion.
  `cbudget_fanout_kill` — **PROVED, the accounting**: for a minimal circuit, an essential variable with a
        non-constant restriction satisfies

        `cbudget (restrictF f i b) + 1 + fanout ≤ cbudget f`

        where `fanout` counts the interior readers of the variable's wire.  Fan-out `≥ 2` kills `≥ 3` gates —
        strictly beyond the two-kill rate.

## Honest scope

The accounting is exact and sharing-aware; what remains open is *forcing* fan-out — proving that minimal
circuits for a concrete target must share their variable wires.  That reuse-forcing problem is the precise
formal residue of "one shared subcircuit cannot service too many independent witness constraints", and it is
where the field's `2n`-internal-and-beyond bounds live.  Named, not claimed.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Redundancy and readers -/

def isRedundantGate {n : ℕ} : CGate n → Bool
  | .cst _ => true
  | .un _ _ => true
  | _ => false

/-- The interior redundancy count: constant or unary gates strictly before the output. -/
def redundantCount {n : ℕ} (d : List (CGate n)) : ℕ :=
  ((Finset.range (d.length - 1)).filter
    (fun p => isRedundantGate (d.getD p (CGate.cst false)) = true)).card

def readsWire {n : ℕ} (p : ℕ) : CGate n → Bool
  | .un _ j => j == p
  | .bin _ j k => j == p || k == p
  | _ => false

/-- The interior readers of wire `p` sitting above it — the live fan-out. -/
def interiorReaders {n : ℕ} (c : List (CGate n)) (p : ℕ) : Finset ℕ :=
  (Finset.range (c.length - 1)).filter
    (fun r => p < r ∧ readsWire p (c.getD r (CGate.cst false)) = true)

theorem elimGate_redundant {n : ℕ} (p : ℕ) (b : Bool) (g : CGate n)
    (h : isRedundantGate g = true) : isRedundantGate (elimGate p b g) = true := by
  cases g with
  | var i => exact absurd h (by simp [isRedundantGate])
  | cst c => exact h
  | un op j =>
    show isRedundantGate (if j = p then CGate.cst (op b) else CGate.un op (elimRef p j))
        = true
    by_cases hj : j = p
    · rw [if_pos hj]; rfl
    · rw [if_neg hj]; rfl
  | bin op j k => exact absurd h (by simp [isRedundantGate])

theorem elimUnGate_redundant {n : ℕ} (p : ℕ) (u : Bool → Bool) (w : ℕ) (g : CGate n)
    (h : isRedundantGate g = true) : isRedundantGate (elimUnGate p u w g) = true := by
  cases g with
  | var i => exact absurd h (by simp [isRedundantGate])
  | cst c => exact h
  | un op j =>
    show isRedundantGate (if j = p then CGate.un (fun a => op (u a)) (elimRef p w)
        else CGate.un op (elimRef p j)) = true
    by_cases hj : j = p
    · rw [if_pos hj]; rfl
    · rw [if_neg hj]; rfl
  | bin op j k => exact absurd h (by simp [isRedundantGate])

theorem elimGate_reader_redundant {n : ℕ} (p : ℕ) (b : Bool) (g : CGate n)
    (h : readsWire p g = true) : isRedundantGate (elimGate p b g) = true := by
  cases g with
  | var i => exact absurd h (by simp [readsWire])
  | cst c => exact absurd h (by simp [readsWire])
  | un op j =>
    have hj : j = p := by
      have h' : (j == p) = true := h
      exact beq_iff_eq.mp h'
    show isRedundantGate (if j = p then CGate.cst (op b) else CGate.un op (elimRef p j))
        = true
    rw [if_pos hj]
    rfl
  | bin op j k =>
    have h' : (j == p || k == p) = true := h
    show isRedundantGate (if j = p then
        (if k = p then CGate.cst (op b b) else CGate.un (fun c => op b c) (elimRef p k))
      else if k = p then CGate.un (fun a => op a b) (elimRef p j)
      else CGate.bin op (elimRef p j) (elimRef p k)) = true
    rcases Bool.or_eq_true_iff.mp h' with hj | hk
    · rw [if_pos (beq_iff_eq.mp hj)]
      by_cases hk2 : k = p
      · rw [if_pos hk2]
        try rfl
      · rw [if_neg hk2]
        try rfl
    · by_cases hj2 : j = p
      · rw [if_pos hj2, if_pos (beq_iff_eq.mp hk)]
        try rfl
      · rw [if_neg hj2, if_pos (beq_iff_eq.mp hk)]
        try rfl

theorem readsWire_subst {n : ℕ} (i : Fin n) (b : Bool) (p : ℕ) (g : CGate n) :
    readsWire p (substGateC i b g) = readsWire p g := by
  cases g with
  | var j =>
    show readsWire p (if j = i then CGate.cst b else CGate.var j) = readsWire p (CGate.var j)
    by_cases hj : j = i
    · rw [if_pos hj]
      try rfl
    · rw [if_neg hj]
      try rfl
  | cst c => rfl
  | un op j => rfl
  | bin op j k => rfl

/-! ### Positional reads through the surgery -/

theorem mapDrop_getD {n : ℕ} (d : List (CGate n)) (Φ : CGate n → CGate n) (p₁ p₂ : ℕ)
    (h12 : p₁ < p₂) (h2 : p₂ < d.length) :
    (d.take p₁ ++ (d.drop (p₁ + 1)).map Φ).getD (p₂ - 1) (CGate.cst false)
      = Φ (d.getD p₂ (CGate.cst false)) := by
  have htlen : (d.take p₁).length = p₁ := take_len d p₁ (by omega)
  rw [List.getD_append_right _ _ _ _ (by omega : (d.take p₁).length ≤ p₂ - 1)]
  rw [htlen]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop]
  rw [show p₁ + 1 + (p₂ - 1 - p₁) = p₂ by omega]
  rw [List.getElem?_eq_getElem h2]
  show Φ d[p₂] = Φ (d.getD p₂ (CGate.cst false))
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rfl

theorem mapDrop_getD_lt {n : ℕ} (d : List (CGate n)) (Φ : CGate n → CGate n) (p₁ q : ℕ)
    (hq : q < p₁) (h1 : p₁ ≤ d.length) :
    (d.take p₁ ++ (d.drop (p₁ + 1)).map Φ).getD q (CGate.cst false)
      = d.getD q (CGate.cst false) := by
  have htlen : (d.take p₁).length = p₁ := take_len d p₁ h1
  rw [List.getD_append _ _ _ _ (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hq,
    List.getD_eq_getElem?_getD]

/-- Redundancy survives either surgery: the deleted position costs at most one. -/
theorem redundantCount_elim_ge {n : ℕ} (d : List (CGate n)) (p : ℕ)
    (hp : p < d.length - 1) (Φ : CGate n → CGate n)
    (hΦ : ∀ g, isRedundantGate g = true → isRedundantGate (Φ g) = true) :
    redundantCount d - 1 ≤ redundantCount (d.take p ++ (d.drop (p + 1)).map Φ) := by
  classical
  have hlen : (d.take p ++ (d.drop (p + 1)).map Φ).length = d.length - 1 := by
    rw [List.length_append, List.length_map, List.length_drop, take_len d p (by omega)]
    omega
  have hinj : Set.InjOn (fun q => elimRef p q)
      ↑(((Finset.range (d.length - 1)).filter
        (fun q => isRedundantGate (d.getD q (CGate.cst false)) = true)).erase p) := by
    intro a ha a' ha' hEq
    have hap : a ≠ p := Finset.ne_of_mem_erase (Finset.mem_coe.mp ha)
    have hap' : a' ≠ p := Finset.ne_of_mem_erase (Finset.mem_coe.mp ha')
    show a = a'
    have h1 : elimRef p a = elimRef p a' := hEq
    unfold elimRef at h1
    by_cases h2 : a < p <;> by_cases h3 : a' < p
    · rw [if_pos h2, if_pos h3] at h1; exact h1
    · rw [if_pos h2, if_neg h3] at h1; omega
    · rw [if_neg h2, if_pos h3] at h1; omega
    · rw [if_neg h2, if_neg h3] at h1; omega
  have hmaps : ∀ q ∈ ((Finset.range (d.length - 1)).filter
      (fun q => isRedundantGate (d.getD q (CGate.cst false)) = true)).erase p,
      elimRef p q ∈ (Finset.range ((d.take p ++ (d.drop (p + 1)).map Φ).length - 1)).filter
        (fun q => isRedundantGate ((d.take p ++ (d.drop (p + 1)).map Φ).getD q
          (CGate.cst false)) = true) := by
    intro q hq
    have hqp : q ≠ p := Finset.ne_of_mem_erase hq
    have hq' := Finset.mem_of_mem_erase hq
    rw [Finset.mem_filter, Finset.mem_range] at hq'
    obtain ⟨hqr, hqred⟩ := hq'
    rw [Finset.mem_filter, Finset.mem_range, hlen]
    constructor
    · unfold elimRef
      by_cases h2 : q < p
      · rw [if_pos h2]; omega
      · rw [if_neg h2]; omega
    · by_cases h2 : q < p
      · rw [show elimRef p q = q from if_pos h2]
        rw [mapDrop_getD_lt d Φ p q h2 (by omega)]
        exact hqred
      · have hqgt : p < q := by omega
        rw [show elimRef p q = q - 1 from if_neg h2]
        rw [mapDrop_getD d Φ p q hqgt (by omega)]
        exact hΦ _ hqred
  have hcard : (((Finset.range (d.length - 1)).filter
      (fun q => isRedundantGate (d.getD q (CGate.cst false)) = true)).erase p).card
      ≤ ((Finset.range ((d.take p ++ (d.drop (p + 1)).map Φ).length - 1)).filter
        (fun q => isRedundantGate ((d.take p ++ (d.drop (p + 1)).map Φ).getD q
          (CGate.cst false)) = true)).card :=
    Finset.card_le_card_of_injOn (fun q => elimRef p q)
      (fun q hq => Finset.mem_coe.mpr (hmaps q (Finset.mem_coe.mp hq))) hinj
  have herase : ((Finset.range (d.length - 1)).filter
      (fun q => isRedundantGate (d.getD q (CGate.cst false)) = true)).card - 1
      ≤ (((Finset.range (d.length - 1)).filter
        (fun q => isRedundantGate (d.getD q (CGate.cst false)) = true)).erase p).card := by
    by_cases hpm : p ∈ (Finset.range (d.length - 1)).filter
        (fun q => isRedundantGate (d.getD q (CGate.cst false)) = true)
    · rw [Finset.card_erase_of_mem hpm]
    · rw [Finset.erase_eq_self.mpr hpm]
      omega
  show redundantCount d - 1 ≤ redundantCount _
  unfold redundantCount
  omega

/-! ### The redundancy engine -/

/-- **The engine (proved)**: a circuit computing a non-constant function shrinks below its interior constant
and unary gates simultaneously. -/
theorem shrink_all {n : ℕ} : ∀ (L : ℕ) (d : List (CGate n)) (f' : (Fin n → Bool) → Bool),
    d.length = L → computes d f' → (∃ u w : Fin n → Bool, f' u ≠ f' w) →
    ∀ K, K ≤ redundantCount d → cbudget f' + K ≤ d.length := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro d f' hL hcomp hnc K hK
    cases K with
    | zero =>
      have hb : cbudget f' ≤ d.length := Nat.sInf_le ⟨d, hcomp, rfl⟩
      omega
    | succ K' =>
      have hpos : 0 < redundantCount d := by omega
      obtain ⟨p, hpmem⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter, Finset.mem_range] at hpmem
      obtain ⟨hpint, hpred⟩ := hpmem
      cases hg : d.getD p (CGate.cst false) with
      | var i => rw [hg] at hpred; exact absurd hpred (by simp [isRedundantGate])
      | bin op j k => rw [hg] at hpred; exact absurd hpred (by simp [isRedundantGate])
      | cst b' =>
        obtain ⟨hd₁comp, hd₁len⟩ := computes_elim_at d f' b' p hcomp hg hpint
        have hred := redundantCount_elim_ge d p hpint (elimGate p b')
          (elimGate_redundant p b')
        have hres := ih (d.length - 1) (by omega) _ f' (by omega) hd₁comp hnc K'
          (by omega)
        omega
      | un u w =>
        by_cases hw : w < p
        · have hsplit := circuit_split_at d p (by omega)
          rw [hg] at hsplit
          have htlen : (d.take p).length = p := take_len d p (by omega)
          have hcomp' : computes (d.take p ++ CGate.un u w :: d.drop (p + 1)) f' := by
            rw [← hsplit]
            exact hcomp
          have hdne : d.drop (p + 1) ≠ [] := by
            intro hcon
            have h := congrArg List.length hcon
            rw [List.length_drop] at h
            simp at h
            omega
          have hres := computes_elim_un (d.take p) (d.drop (p + 1)) u w f' hcomp'
            (by omega) hdne
          rw [htlen] at hres
          have hlen1 : (d.take p ++ (d.drop (p + 1)).map (elimUnGate p u w)).length
              = d.length - 1 := by
            rw [List.length_append, List.length_map, List.length_drop, htlen]
            omega
          have hred := redundantCount_elim_ge d p hpint (elimUnGate p u w)
            (elimUnGate_redundant p u w)
          have hres2 := ih (d.length - 1) (by omega) _ f' hlen1 hres hnc K' (by omega)
          omega
        · -- garbage source: convert to a constant, then delete it
          have hsplit := circuit_split_at d p (by omega)
          rw [hg] at hsplit
          have htlen : (d.take p).length = p := take_len d p (by omega)
          have hcomp' : computes (d.take p ++ CGate.un u w :: d.drop (p + 1)) f' := by
            rw [← hsplit]
            exact hcomp
          have hrep := computes_congr_at (d.take p) (CGate.un u w) (CGate.cst (u false))
            (d.drop (p + 1)) f' (by
              intro x
              show u ((runFrom x [] (d.take p)).getD w false) = u false
              rw [List.getD_eq_default _ false (by
                rw [runFrom_length x (d.take p) []]
                show ([] : List Bool).length + (d.take p).length ≤ w
                simp only [List.length_nil]
                omega)]) hcomp'
          set d₀ : List (CGate n) := d.take p ++ CGate.cst (u false) :: d.drop (p + 1)
            with hd₀
          have hd₀len : d₀.length = d.length := by
            rw [hd₀, List.length_append, List.length_cons, List.length_drop, htlen]
            omega
          have hd₀g : d₀.getD p (CGate.cst false) = CGate.cst (u false) := by
            rw [hd₀, List.getD_append_right _ _ _ _ (by omega),
              show p - (d.take p).length = 0 by omega]
            rfl
          have hd₀gq : ∀ q, q ≠ p → d₀.getD q (CGate.cst false)
              = d.getD q (CGate.cst false) := by
            intro q hq
            by_cases h2 : q < p
            · rw [hd₀, List.getD_append _ _ _ _ (by omega)]
              rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h2,
                List.getD_eq_getElem?_getD]
            · have hqgt : p < q := by omega
              rw [hd₀, List.getD_append_right _ _ _ _ (by omega)]
              rw [show q - (d.take p).length = (q - p - 1) + 1 by omega]
              show (d.drop (p + 1)).getD (q - p - 1) (CGate.cst false)
                  = d.getD q (CGate.cst false)
              rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
                show p + 1 + (q - p - 1) = q by omega, List.getD_eq_getElem?_getD]
          have hd₀red : redundantCount d = redundantCount d₀ := by
            unfold redundantCount
            rw [hd₀len]
            congr 1
            apply Finset.filter_congr
            intro q hq
            by_cases hqp : q = p
            · subst hqp
              rw [hg, hd₀g]
              exact Iff.rfl
            · rw [hd₀gq q hqp]
          obtain ⟨hd₁comp, hd₁len⟩ := computes_elim_at d₀ f' (u false) p hrep hd₀g
            (by omega)
          have hred := redundantCount_elim_ge d₀ p (by omega) (elimGate p (u false))
            (elimGate_redundant p (u false))
          have hres := ih (d.length - 1) (by omega) _ f' (by omega) hd₁comp hnc K'
            (by omega)
          omega

/-! ### The fan-out multi-kill -/

/-- **THE FAN-OUT ACCOUNTING (proved)**: restricting an essential variable kills its gate *and every interior
reader of its wire* — `1 + fanout` gates — reuse charged gate by gate through the sharing. -/
theorem cbudget_fanout_kill {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (hnc : ∃ u w : Fin n → Bool, restrictF f i b u ≠ restrictF f i b w)
    (c : List (CGate n)) (hcomp : computes c f) (hmin : c.length = cbudget f)
    (p : ℕ) (hpg : c.getD p (CGate.cst false) = CGate.var i) :
    cbudget (restrictF f i b) + 1 + (interiorReaders c p).card ≤ cbudget f := by
  classical
  have hpL : p < c.length := by
    by_contra h'
    rw [List.getD_eq_default _ _ (by omega)] at hpg
    simp at hpg
  have hpint : p < c.length - 1 := by
    by_cases h' : p = c.length - 1
    · exfalso
      obtain ⟨u, w, hne'⟩ := hnc
      apply hne'
      have hfx : ∀ x : Fin n → Bool, f x = x i := by
        intro x
        rw [← hcomp x]
        show (runFrom x [] c).getD (c.length - 1) false = x i
        rw [output_getD_at x c (c.length - 1) (by omega), ← h', hpg]
        rfl
      show f (Function.update u i b) = f (Function.update w i b)
      rw [hfx, hfx, Function.update_self, Function.update_self]
    · omega
  set c' : List (CGate n) := c.map (substGateC i b) with hc'
  have hc'comp : computes c' (restrictF f i b) := computes_subst c f i b hcomp
  have hc'len : c'.length = c.length := by rw [hc', List.length_map]
  have hpg' : c'.getD p (CGate.cst false) = CGate.cst b := by
    rw [hc', getD_map_lt c (substGateC i b) p (by omega), hpg, substGateC_var_self]
  obtain ⟨hd₁comp, hd₁len⟩ := computes_elim_at c' (restrictF f i b) b p hc'comp hpg'
    (by omega)
  -- every interior reader's image is redundant in the shrunk circuit
  have hread : ∀ r ∈ interiorReaders c p,
      (r - 1) ∈ (Finset.range ((c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).length
        - 1)).filter (fun q => isRedundantGate
          ((c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).getD q
            (CGate.cst false)) = true) := by
    intro r hr
    rw [interiorReaders, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrint, hpr, hrw⟩ := hr
    rw [Finset.mem_filter, Finset.mem_range, hd₁len]
    constructor
    · omega
    · rw [mapDrop_getD c' (elimGate p b) p r hpr (by omega)]
      apply elimGate_reader_redundant
      rw [hc', getD_map_lt c (substGateC i b) r (by omega), readsWire_subst]
      exact hrw
  have hinj : Set.InjOn (fun r => r - 1) ↑(interiorReaders c p) := by
    intro a ha a' ha' hEq
    rw [Finset.mem_coe, interiorReaders, Finset.mem_filter] at ha ha'
    have h1 : a - 1 = a' - 1 := hEq
    have h2 : p < a := ha.2.1
    have h3 : p < a' := ha'.2.1
    omega
  have hcard : (interiorReaders c p).card
      ≤ ((Finset.range ((c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).length
        - 1)).filter (fun q => isRedundantGate
          ((c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).getD q
            (CGate.cst false)) = true)).card :=
    Finset.card_le_card_of_injOn (fun r => r - 1)
      (fun r hr => Finset.mem_coe.mpr (hread r (Finset.mem_coe.mp hr))) hinj
  have hK : (interiorReaders c p).card
      ≤ redundantCount (c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)) := hcard
  have hfinal := shrink_all (c.length - 1) _ (restrictF f i b) (by omega) hd₁comp hnc
    (interiorReaders c p).card hK
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.redundantCount_elim_ge
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.shrink_all
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_fanout_kill
