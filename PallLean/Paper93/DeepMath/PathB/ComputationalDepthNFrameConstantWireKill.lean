import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSplitSquares

/-!
# N-Frame: the constant-wire kill — minimal circuits carry no semantically constant interior wire

The frame-properness rung, complete.  A wire whose value is the same on every input can be absorbed: each
reader's op is pre-filled with the constant and its reference repointed away — then nothing reads the wire,
and Normal Form IV convicts the circuit.

  `rewireConst` / `runFrom_rewireConst` — **PROVED, the surgery**: absorb a constant wire into its
        readers' ops; the run is unchanged gate for gate.
  `no_constant_wire` — **PROVED, the kill**: no interior wire of a minimal circuit is semantically
        constant.  With `no_duplicate_wire`: interior wires of minimal circuits are pairwise
        xor-inequivalent *and* individually non-constant — every wire carries fresh information.
  `sat3_split_frame_proper` — **PROVED, the proper frame**: a minimal SAT circuit at excess zero yields a
        bipartite split over a **proper** cut — both cones must contain a variable gate (else their wire
        is constant and dies), and read-uniqueness keeps the sides apart.
  `sat3_excess_pos_of_no_proper_split` / `sat3_cbudget_2mD_of_no_proper_split` — **the conditional,
        now resting on square production alone**: `Sat3NoBipartiteSplitProper N → 2·m·D ≤ cbudget` —
        with no auxiliary properness hypothesis remaining.

## Honest scope

Rung (b) of the discharge is closed; the entire distance to `2·m·D ≤ cbudget` (the first record beyond
connectivity) is now rung (a) alone: producing, for every pair `(s₀, t₀)` of distinct coordinates, an
XOR-square and an odd-parity square at canonical bases — with the recorded obstruction that SAT is
monotone in every selector bit, so selector-involved pairs need the wider rectangle-closure route.
`Sat3NoBipartiteSplitProper` remains a named hypothesis, not a theorem.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The surgery -/

/-- Absorb the constant value `c₀` of wire `r` into every reader; repoint absorbed references to `r + 1`
(never equal to `r`, and ignored by the op). -/
def rewireConst {n : ℕ} (r : ℕ) (c₀ : Bool) : CGate n → CGate n
  | .var i => .var i
  | .cst b => .cst b
  | .un op j => if j = r then .un (fun _ => op c₀) (r + 1) else .un op j
  | .bin op j k =>
      .bin (fun a b => op (if j = r then c₀ else a) (if k = r then c₀ else b))
        (if j = r then r + 1 else j) (if k = r then r + 1 else k)

theorem evalGate_rewireConst {n : ℕ} (x : Fin n → Bool) (vals : List Bool) (r : ℕ)
    (c₀ : Bool) (hrel : vals.getD r false = c₀) (g : CGate n) :
    evalGate x vals (rewireConst r c₀ g) = evalGate x vals g := by
  cases g with
  | var i => rfl
  | cst b => rfl
  | un op j =>
    by_cases hj : j = r
    · simp only [rewireConst, if_pos hj]
      show op c₀ = op (vals.getD j false)
      rw [hj, hrel]
    · simp only [rewireConst, if_neg hj]
  | bin op j k =>
    simp only [rewireConst]
    by_cases hj : j = r
    · by_cases hk : k = r
      · rw [if_pos hj, if_pos hk]
        show op (if j = r then c₀ else vals.getD (r + 1) false)
            (if k = r then c₀ else vals.getD (r + 1) false)
          = op (vals.getD j false) (vals.getD k false)
        rw [if_pos hj, if_pos hk, hj, hk, hrel]
      · rw [if_pos hj, if_neg hk]
        show op (if j = r then c₀ else vals.getD (r + 1) false)
            (if k = r then c₀ else vals.getD k false)
          = op (vals.getD j false) (vals.getD k false)
        rw [if_pos hj, if_neg hk, hj, hrel]
    · by_cases hk : k = r
      · rw [if_neg hj, if_pos hk]
        show op (if j = r then c₀ else vals.getD j false)
            (if k = r then c₀ else vals.getD (r + 1) false)
          = op (vals.getD j false) (vals.getD k false)
        rw [if_neg hj, if_pos hk, hk, hrel]
      · rw [if_neg hj, if_neg hk]
        show op (if j = r then c₀ else vals.getD j false)
            (if k = r then c₀ else vals.getD k false)
          = op (vals.getD j false) (vals.getD k false)
        rw [if_neg hj, if_neg hk]

theorem readsWire_rewireConst {n : ℕ} (r : ℕ) (c₀ : Bool) (g : CGate n) :
    readsWire r (rewireConst r c₀ g) = false := by
  cases g with
  | var i => rfl
  | cst b => rfl
  | un op j =>
    by_cases hj : j = r
    · simp [rewireConst, hj, readsWire]
    · simp [rewireConst, hj, readsWire]
  | bin op j k =>
    by_cases hj : j = r <;> by_cases hk : k = r <;>
      simp [rewireConst, hj, hk, readsWire]

theorem runFrom_rewireConst {n : ℕ} (x : Fin n → Bool) (r : ℕ) (c₀ : Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool), r < vals.length →
      vals.getD r false = c₀ →
      runFrom x vals (gs.map (rewireConst r c₀)) = runFrom x vals gs := by
  intro gs
  induction gs with
  | nil => intro vals _ _; rfl
  | cons g rest ih =>
    intro vals hr hrel
    show runFrom x (vals ++ [evalGate x vals (rewireConst r c₀ g)])
        (rest.map (rewireConst r c₀))
        = runFrom x (vals ++ [evalGate x vals g]) rest
    rw [evalGate_rewireConst x vals r c₀ hrel g]
    exact ih (vals ++ [evalGate x vals g])
      (by rw [List.length_append]; omega)
      (by rw [List.getD_append _ _ _ _ hr]; exact hrel)

/-! ### The kill -/

/-- **THE CONSTANT-WIRE KILL (proved)**: no interior wire of a minimal circuit is semantically
constant. -/
theorem no_constant_wire {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (r : ℕ) (hr : r < c.length - 1) (c₀ : Bool)
    (hconst : ∀ x : Fin n → Bool, (runFrom x [] c).getD r false = c₀) : False := by
  classical
  set c' : List (CGate n) :=
    c.take (r + 1) ++ (c.drop (r + 1)).map (rewireConst r c₀) with hc'
  have hlen : c'.length = c.length := by
    rw [hc', List.length_append, List.length_map, List.length_take, List.length_drop]
    omega
  have hrun : ∀ x, runFrom x [] c' = runFrom x [] c := by
    intro x
    have hVlen : (runFrom x [] (c.take (r + 1))).length = r + 1 := by
      rw [runFrom_length]
      simp only [List.length_nil, List.length_take]
      omega
    have hrelV : (runFrom x [] (c.take (r + 1))).getD r false = c₀ := by
      rw [takeRun_getD_eq c x (r + 1) r (by omega) (by omega)]
      exact hconst x
    rw [hc', runFrom_append]
    conv_rhs => rw [← List.take_append_drop (r + 1) c]
    rw [runFrom_append]
    exact runFrom_rewireConst x r c₀ (c.drop (r + 1))
      (runFrom x [] (c.take (r + 1))) (by rw [hVlen]; omega) hrelV
  have hcomp' : computes c' f := by
    intro x
    show (runFrom x [] c').getD (c'.length - 1) false = f x
    rw [hrun x, hlen]
    exact hcomp x
  have hmin' : c'.length = cbudget f := by
    rw [hlen]
    exact hmin
  obtain ⟨q, hq, hqr⟩ := minimal_wire_read f c' hcomp' hmin' r (by rw [hlen]; omega)
  have hnoread : readsWire r (c'.getD q (CGate.cst false)) = false := by
    rcases Nat.lt_or_ge q c.length with hql | hql
    · have hget : c'.getD q (CGate.cst false)
          = rewireConst r c₀ (c.getD q (CGate.cst false)) := by
        rw [hc']
        exact takeMap_getD c (rewireConst r c₀) (r + 1) q (by omega) hql
      rw [hget]
      exact readsWire_rewireConst r c₀ _
    · rw [List.getD_eq_default _ _ (by rw [hlen]; omega)]
      rfl
  rw [hqr] at hnoread
  simp at hnoread

/-! ### The proper frame -/

/-- **THE PROPER FRAME (proved)**: excess zero in a minimal SAT circuit yields a bipartite split over a
proper cut — both cones must contain a variable gate, else their wire is constant and dies. -/
theorem sat3_split_frame_proper (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (hex : coneExcess c (c.length - 1) = 0) :
    ∃ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
      (∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) ∧
      (∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) ∧
      (∀ x, sat3Family N x = op (g x) (h x)) ∧
      (∃ s₀ : Fin N, s₀ ∈ S) ∧ (∃ t₀ : Fin N, t₀ ∉ S) := by
  classical
  obtain ⟨op, L, R, hroot, hL, hR, hLR⟩ := sat3_root_shape N hv hm3 hk c hcomp hmin
  obtain ⟨hdisj, hsplit⟩ := excess_zero_top_split (sat3Family N) c hcomp hex op L R
    hroot hL hR hLR
  set S : Finset (Fin N) := Finset.univ.filter (fun i => ∃ p ∈ coneOf c L,
    c.getD p (CGate.cst false) = CGate.var i) with hS
  have hcross : ∀ i : Fin N, ∀ p ∈ coneOf c R,
      c.getD p (CGate.cst false) = CGate.var i → i ∉ S := by
    intro i p hp hgate hiS
    rw [hS, Finset.mem_filter] at hiS
    obtain ⟨-, q, hq, hgate'⟩ := hiS
    have hplt : p < c.length - 1 := by
      have h1 := cone_le c R p hp
      omega
    have hqlt : q < c.length - 1 := by
      have h1 := cone_le c L q hq
      omega
    have hpq : p = q := by
      rcases Nat.lt_trichotomy p q with hlt | heq | hgt
      · exact absurd (var_gate_unique (sat3Family N) c hcomp hmin i p q hlt hqlt
          hgate hgate') (fun h => h)
      · exact heq
      · exact absurd (var_gate_unique (sat3Family N) c hcomp hmin i q p hgt hplt
          hgate' hgate) (fun h => h)
    rw [Finset.disjoint_left] at hdisj
    exact hdisj hq (hpq ▸ hp)
  refine ⟨op, fun x => (runFrom x [] c).getD L false,
    fun x => (runFrom x [] c).getD R false, S, ?_, ?_, hsplit, ?_, ?_⟩
  · intro x y hxy
    apply cone_val_agree c L x y ?_ L (cone_self c L)
    intro p hp i hgate
    apply hxy
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ i, p, hp, hgate⟩
  · intro x y hxy
    apply cone_val_agree c R x y ?_ R (cone_self c R)
    intro p hp i hgate
    apply hxy
    exact hcross i p hp hgate
  · -- S nonempty: else the L-wire is constant and dies
    by_contra hno
    push_neg at hno
    apply no_constant_wire (sat3Family N) c hcomp hmin L hL
      ((runFrom (fun _ => false) [] c).getD L false)
    intro x
    apply cone_val_agree c L x (fun _ => false) ?_ L (cone_self c L)
    intro p hp i hgate
    exfalso
    apply hno i
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ i, p, hp, hgate⟩
  · -- some variable escapes S: a var gate in cone R (else the R-wire is constant and dies)
    by_cases hvar : ∃ p ∈ coneOf c R, ∃ i : Fin N,
        c.getD p (CGate.cst false) = CGate.var i
    · obtain ⟨p, hp, i, hgate⟩ := hvar
      exact ⟨i, hcross i p hp hgate⟩
    · exfalso
      push_neg at hvar
      apply no_constant_wire (sat3Family N) c hcomp hmin R hR
        ((runFrom (fun _ => false) [] c).getD R false)
      intro x
      apply cone_val_agree c R x (fun _ => false) ?_ R (cone_self c R)
      intro p hp i hgate
      exact absurd hgate (hvar p hp i)

/-! ### The conditional, resting on square production alone -/

/-- **CONDITIONAL (hypothesis named, not claimed)**: no proper bipartite split ⇒ excess ≥ 1. -/
theorem sat3_excess_pos_of_no_proper_split (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hW : Sat3NoBipartiteSplitProper N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) :
    1 ≤ coneExcess c (c.length - 1) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨op, g, h, S, hg, hh, hf, hs, ht⟩ :=
    sat3_split_frame_proper N hv hm3 hk c hcomp hmin (by omega)
  exact hW op g h S hg hh hf hs ht

/-- **CONDITIONAL CASH-OUT (hypothesis named, not claimed)**: no proper bipartite split ⇒
`2·m·D ≤ cbudget` — one gate past the connectivity record. -/
theorem sat3_cbudget_2mD_of_no_proper_split (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hW : Sat3NoBipartiteSplitProper N) :
    2 * (sat3M N * sat3D N) ≤ cbudget (sat3Family N) := by
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem (cbudget_set_nonempty (sat3Family N))
  have hmin : c.length = cbudget (sat3Family N) := hlen
  have h1 := sat3_excess_priced N hv (by omega) c hcomp hmin
  have h2 := sat3_excess_pos_of_no_proper_split N hv hm3 hk hW c hcomp hmin
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.no_constant_wire
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_split_frame_proper
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_2mD_of_no_proper_split
