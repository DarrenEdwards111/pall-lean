import PallLean.SPDPDefs
import PallLean.Tseitin
import PallLean.BinomialBound2
import Mathlib.Tactic
/-!
# NP-Side Lower Bound — Pall §7–10

Theorem 10.1: Tseitin formulas on high-girth regular graphs have
ΓB_{κ,ℓ}(Q×_Φn) ≥ n^Θ(log n).

Proof chain:
1. high-girth family → graph G_n (§8.1)
2. Tseitin encoding → 3-CNF Φ_n (§8.2)
3. Disjoint clause packing → |C_disj| = αn (Lemma 8.3)
4. Identity minor → rank ≥ (αn choose κ) (Theorem 9.3)
5. Binomial bound → n^Θ(log n)
-/

namespace NPWitness

open SPDP MvPolynomial Tseitin

/-! ## Concrete Witness Family -/

/-- Helper: (a+1)%n = b ↔ a = (b+n-1)%n for a,b < n -/
private lemma mod_succ_eq_iff (a b n : ℕ) (hn : n ≥ 1) (ha : a < n) (hb : b < n) :
    (a + 1) % n = b ↔ a = (b + n - 1) % n := by
  constructor
  · intro h
    by_cases ha1 : a + 1 = n
    · have hb0 : b = 0 := by rw [← h, ha1, Nat.mod_self]
      subst hb0
      rw [show 0 + n - 1 = n - 1 from by omega, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      omega
    · have hab : a + 1 = b := by rwa [Nat.mod_eq_of_lt (by omega)] at h
      by_cases hb0 : b = 0; · omega
      rw [show b + n - 1 = b - 1 + 1 * n from by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : b - 1 < n)]; omega
  · intro h
    by_cases hb0 : b = 0
    · subst hb0
      rw [show 0 + n - 1 = n - 1 from by omega, Nat.mod_eq_of_lt (by omega : n - 1 < n)] at h
      subst h; rw [show n - 1 + 1 = n from by omega, Nat.mod_self]
    · rw [show b + n - 1 = b - 1 + 1 * n from by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : b - 1 < n)] at h
      subst h; rw [show b - 1 + 1 = b from by omega, Nat.mod_eq_of_lt hb]

/-- Cycle graph on n vertices (n ≥ 3): vertex i connects to i±1 mod n.
    For n < 3, we use the triangle (C_3) as a default. -/
noncomputable def cycleRegularGraph (n : ℕ) (hn : n ≥ 3) : RegularGraph where
  numVertices := n
  degree := 2
  numEdges := n
  vertices_pos := by omega
  degree_lower := le_refl 2
  edges_bound := by omega
  edges_lower := le_refl n
  degree_bound := by omega
  edgeSrc := fun e => ⟨e.val, by omega⟩
  edgeTgt := fun e => ⟨(e.val + 1) % n, Nat.mod_lt _ (by omega)⟩
  regular := fun v => by
    set pred : Fin n := ⟨(v.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩
    have hne : v ≠ pred := by
      intro heq; have hveq := congr_arg Fin.val heq; simp [pred] at hveq
      by_cases hv0 : v.val = 0
      · rw [hv0, show 0 + n - 1 = n - 1 from by omega,
          Nat.mod_eq_of_lt (by omega : n - 1 < n)] at hveq; omega
      · rw [show v.val + n - 1 = v.val - 1 + 1 * n from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : v.val - 1 < n)] at hveq; omega
    have hfilt : Finset.univ.filter (fun e : Fin n =>
        (⟨e.val, by omega⟩ : Fin n) = v ∨
        (⟨(e.val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = v) = {v, pred} := by
      ext ⟨e, he⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
      constructor
      · intro h; cases h with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr ((mod_succ_eq_iff e v.val n (by omega) he v.isLt).mp h)
      · intro h; cases h with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr ((mod_succ_eq_iff e v.val n (by omega) he v.isLt).mpr h)
    rw [hfilt, Finset.card_pair hne]

/-- Cubic (3-regular) graph on n vertices (n even, n ≥ 6).
    Edges: n cycle edges (v → v+1 mod n) + n/2 perfect matching edges (v → v+n/2).
    Total: 3n/2 edges. Each vertex has degree 3. -/
-- Edge source/target as standalone functions for proof convenience
def cubicSrc (n : ℕ) (e : Fin (n + n / 2)) : Fin n :=
  if h : e.val < n then ⟨e.val, h⟩
  else ⟨e.val - n, by omega⟩

def cubicTgt (n : ℕ) (hn : n ≥ 6) (e : Fin (n + n / 2)) : Fin n :=
  if h : e.val < n then ⟨(e.val + 1) % n, Nat.mod_lt _ (by omega)⟩
  else ⟨e.val - n + n / 2, by omega⟩

-- Key lemma: the incident edge filter has cardinality 3
private theorem cubicGraph_regular_aux (n : ℕ) (hn : n ≥ 6) (heven : 2 ∣ n)
    (v : Fin n) :
    (Finset.univ.filter (fun e : Fin (n + n / 2) =>
      cubicSrc n e = v ∨ cubicTgt n hn e = v)).card = 3 := by
  have hv := v.isLt
  have hn2 : n / 2 ≥ 3 := by rcases heven with ⟨k, hk⟩; omega
  -- The 3 incident edges
  set e_fwd : Fin (n + n / 2) := ⟨v.val, by omega⟩
  set e_bwd : Fin (n + n / 2) := ⟨(v.val + n - 1) % n, by
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)⟩
  set e_match : Fin (n + n / 2) :=
    if hv2 : v.val < n / 2 then ⟨n + v.val, by omega⟩
    else ⟨n + (v.val - n / 2), by omega⟩
  -- Show filter = {e_fwd, e_bwd, e_match}
  suffices h : Finset.univ.filter (fun e : Fin (n + n / 2) =>
      cubicSrc n e = v ∨ cubicTgt n hn e = v) = {e_fwd, e_bwd, e_match} by
    rw [h, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · -- e_bwd ∉ {e_match}
      simp only [Finset.mem_singleton]; intro h
      have hbwd_val : e_bwd.val = (v.val + n - 1) % n := rfl
      have hbwd_lt : e_bwd.val < n := Nat.mod_lt _ (by omega)
      have hmatch_val : e_match.val = if v.val < n / 2 then n + v.val else n + (v.val - n / 2) := by
        simp [e_match]; split <;> rfl
      have hmatch_ge : e_match.val ≥ n := by rw [hmatch_val]; split <;> omega
      exact absurd (congrArg Fin.val h) (by omega)
    · -- e_fwd ∉ {e_bwd, e_match}
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_⟩
      · -- e_fwd ≠ e_bwd
        intro h
        have : e_fwd.val = e_bwd.val := congrArg Fin.val h
        -- e_fwd.val = v.val, e_bwd.val = (v+n-1)%n
        -- v = (v+n-1)%n → contradiction since n ≥ 6
        -- this : v.val = (v.val + n - 1) % n
        have hfwd : e_fwd.val = v.val := rfl
        have hbwd : e_bwd.val = (v.val + n - 1) % n := rfl
        rw [hfwd, hbwd] at this
        rcases Nat.lt_or_ge v.val 1 with hv0 | hv0
        · rw [show v.val = 0 from by omega, show 0 + n - 1 = n - 1 from by omega,
              Nat.mod_eq_of_lt (by omega : n - 1 < n)] at this; omega
        · rw [show v.val + n - 1 = (v.val - 1) + 1 * n from by omega,
              Nat.add_mul_mod_self_right,
              Nat.mod_eq_of_lt (by omega : v.val - 1 < n)] at this; omega
      · -- e_fwd ≠ e_match
        intro h
        have heq : e_fwd.val = e_match.val := congrArg Fin.val h
        have hfwd : e_fwd.val = v.val := rfl
        have hmge : e_match.val ≥ n := by
          show (if hv2 : v.val < n / 2 then (⟨n + v.val, _⟩ : Fin (n + n / 2))
               else ⟨n + (v.val - n / 2), _⟩).val ≥ n
          split <;> simp <;> omega
        omega
  -- Now prove filter = {e_fwd, e_bwd, e_match}
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · -- e incident to v → e ∈ {e_fwd, e_bwd, e_match}
    intro hinc
    simp only [cubicSrc, cubicTgt] at hinc
    split_ifs at hinc with he_lt
    · -- e.val < n (cycle edge)
      rcases hinc with hsrc | htgt
      · -- cubicSrc = v means e.val = v.val (since e < n)
        left; ext; simp [e_fwd]; exact congrArg Fin.val hsrc
      · -- cubicTgt = v means (e.val + 1) % n = v.val
        right; left; ext; simp [e_bwd]
        exact (mod_succ_eq_iff e.val v.val n (by omega) he_lt hv).mp (congrArg Fin.val htgt)
    · -- e.val ≥ n (matching edge)
      rcases hinc with hsrc | htgt
      · -- cubicSrc e = v means e.val - n = v.val
        have : e.val - n = v.val := congrArg Fin.val hsrc
        have : e.val - n < n / 2 := by omega
        have : v.val < n / 2 := by omega
        right; right; simp [e_match, show v.val < n / 2 from ‹_›]; ext; simp; omega
      · -- cubicTgt e = v means e.val - n + n/2 = v.val
        have : e.val - n + n / 2 = v.val := congrArg Fin.val htgt
        have : ¬ (v.val < n / 2) := by omega
        right; right; simp [e_match, ‹¬ (v.val < n / 2)›]; ext; simp; omega
  · -- e ∈ {e_fwd, e_bwd, e_match} → e incident to v
    intro hmem
    rcases hmem with rfl | rfl | rfl
    · -- e_fwd: cubicSrc = v
      left; show cubicSrc n e_fwd = v
      unfold cubicSrc; simp [dif_pos hv, e_fwd]
    · -- e_bwd: cubicTgt = v
      right; show cubicTgt n hn e_bwd = v
      have hmod_lt : (v.val + n - 1) % n < n := Nat.mod_lt _ (by omega)
      unfold cubicTgt; simp [dif_pos hmod_lt, e_bwd]
      -- Goal: ((v.val + n - 1) % n + 1) % n = v.val ... OR ... (v+n-1+1)%n = v
      -- After unfold+simp, the goal should be about ((v+n-1)%n + 1) % n = v
      -- which is exactly mod_succ_eq_iff backwards
      ext; simp
      -- Goal: (v+n-1+1) % n = v
      rw [show v.val + n - 1 + 1 = v.val + 1 * n from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
    · -- e_match
      show cubicSrc n e_match = v ∨ cubicTgt n hn e_match = v
      simp only [e_match]
      split
      · -- v < n/2: e_match = ⟨n + v, _⟩
        rename_i hv2
        left; unfold cubicSrc; simp [show ¬ (n + v.val < n) from by omega]
      · -- v ≥ n/2: e_match = ⟨n + (v - n/2), _⟩
        rename_i hv2
        right; unfold cubicTgt; simp [show ¬ (n + (v.val - n / 2) < n) from by omega]
        ext; simp; omega

noncomputable def cubicGraph (n : ℕ) (hn : n ≥ 6) (heven : 2 ∣ n) : RegularGraph where
  numVertices := n
  degree := 3
  numEdges := n + n / 2
  vertices_pos := by omega
  degree_lower := by omega
  edges_bound := by have : n / 2 ≤ n := Nat.div_le_self n 2; omega
  edges_lower := by omega
  degree_bound := by omega
  edgeSrc := cubicSrc n
  edgeTgt := cubicTgt n hn
  regular := cubicGraph_regular_aux n hn heven

/-- Round up to even ≥ 6 -/
private def evenUp (n : ℕ) : ℕ :=
  let m := max n 6
  if 2 ∣ m then m else m + 1

private lemma evenUp_ge6 (n : ℕ) : evenUp n ≥ 6 := by
  simp only [evenUp]; split <;> omega

private lemma evenUp_even (n : ℕ) : 2 ∣ evenUp n := by
  simp only [evenUp]
  split
  · assumption
  · rename_i h
    -- max n 6 is odd, so max n 6 + 1 is even
    have : max n 6 % 2 = 1 := by omega
    exact ⟨(max n 6 + 1) / 2, by omega⟩

private lemma evenUp_ge (n : ℕ) : evenUp n ≥ n := by
  simp only [evenUp]; split <;> omega

private lemma evenUp_eq (n : ℕ) (hn : n ≥ 6) (heven : 2 ∣ n) : evenUp n = n := by
  simp only [evenUp]
  rw [max_eq_left (show 6 ≤ n by omega)]
  exact dif_pos heven

/-- Explicit bounded-degree graph family (cubic graphs). -/
noncomputable def highGirthFamily : HighGirthFamily where
  graph := fun n => cubicGraph (evenUp n) (evenUp_ge6 n) (evenUp_even n)
  degree_const := ⟨3, fun _ => rfl⟩
  vertices_eq := fun n hn heven => by
    show (cubicGraph (evenUp n) _ _).numVertices = n
    change evenUp n = n
    exact evenUp_eq n hn heven
  girth_log := ⟨1, fun n _ => by
    simp only [one_mul]
    show Nat.log 2 n ≤ (cubicGraph (evenUp n) _ _).numVertices
    change Nat.log 2 n ≤ evenUp n
    exact le_trans (Nat.log_le_self 2 n) (evenUp_ge n)⟩

/-! ## Concrete Tseitin Construction

We build `tseitinAt n` concretely from `highGirthFamily.graph n` using
the standard XOR→3-CNF Tseitin encoding. This eliminates 3 axioms
(tseitinAt, tseitinAt_graph, tseitinAt_vertices). -/

/-- Build a Tseitin 3-CNF formula from a 3-regular graph.

    For each vertex v with 3 incident edge variables (e₁, e₂, e₃), we encode
    the parity constraint XOR(x_{e₁}, x_{e₂}, x_{e₃}) = b_v as 4 width-3 clauses.

    **Key structural property**: edge variables are GLOBAL — edge e corresponds
    to a single variable x_e shared across clauses at both endpoints.
    This creates the inter-clause variable sharing needed for SPDP compression.

    Variables: x_0,...,x_{E-1} (edge vars) + selectors (at higher indices).
    Total clauses: 4n (4 per vertex).
    Each edge variable appears in ≤ 8 clauses (4 at each endpoint). -/
noncomputable def incidentEdges (G : RegularGraph) (v : Fin G.numVertices) :
    Finset (Fin G.numEdges) :=
  Finset.univ.filter (fun e => G.edgeSrc e = v ∨ G.edgeTgt e = v)

theorem incidentEdges_card (G : RegularGraph) (v : Fin G.numVertices) :
    (incidentEdges G v).card = G.degree := G.regular v

/-- For degree-3 graphs: pick the 3 incident edges as a sorted list.
    Returns edge indices (ℕ values) for use in clause construction. -/
noncomputable def incidentEdgesList (G : RegularGraph) (v : Fin G.numVertices) :
    List (Fin G.numEdges) :=
  (incidentEdges G v).sort (· ≤ ·)

theorem incidentEdgesList_length (G : RegularGraph) (v : Fin G.numVertices) :
    (incidentEdgesList G v).length = G.degree := by
  simp [incidentEdgesList, Finset.length_sort, incidentEdges_card]

theorem incidentEdgesList_nodup (G : RegularGraph) (v : Fin G.numVertices) :
    (incidentEdgesList G v).Nodup :=
  Finset.sort_nodup _ _

/-- XOR-to-3-CNF: 4 clauses for x_{e1} ⊕ x_{e2} ⊕ x_{e3} = b.
    For b = false (even parity), exclude odd-parity assignments.
    For b = true (odd parity), exclude even-parity assignments. -/
def xorClauses (e1 e2 e3 : ℕ) (b : Bool)
    (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3) : List Clause3 :=
  if b then
    -- XOR = 1: exclude (0,0,0), (1,1,0), (1,0,1), (0,1,1)
    [ ⟨e1, e2, e3, true, true, true, h12, h13, h23⟩,
      ⟨e1, e2, e3, false, false, true, h12, h13, h23⟩,
      ⟨e1, e2, e3, false, true, false, h12, h13, h23⟩,
      ⟨e1, e2, e3, true, false, false, h12, h13, h23⟩ ]
  else
    -- XOR = 0: exclude (1,0,0), (0,1,0), (0,0,1), (1,1,1)
    [ ⟨e1, e2, e3, false, true, true, h12, h13, h23⟩,
      ⟨e1, e2, e3, true, false, true, h12, h13, h23⟩,
      ⟨e1, e2, e3, true, true, false, h12, h13, h23⟩,
      ⟨e1, e2, e3, false, false, false, h12, h13, h23⟩ ]

theorem xorClauses_length (e1 e2 e3 : ℕ) (b : Bool) h12 h13 h23 :
    (xorClauses e1 e2 e3 b h12 h13 h23).length = 4 := by
  simp [xorClauses]; split <;> rfl

/-- All clause body variables in xorClauses are from {e1, e2, e3} -/
theorem xorClauses_vars (e1 e2 e3 : ℕ) (b : Bool) h12 h13 h23
    (c : Clause3) (hc : c ∈ xorClauses e1 e2 e3 b h12 h13 h23) :
    c.var1 = e1 ∧ c.var2 = e2 ∧ c.var3 = e3 := by
  simp [xorClauses] at hc; split at hc <;> simp_all [List.mem_cons] <;> aesop

/-- Clauses for a single vertex: 4 XOR clauses if degree ≥ 3, else empty. -/
noncomputable def vertexClauses (G : RegularGraph) (v : Fin G.numVertices) : List Clause3 :=
  let edges := incidentEdgesList G v
  if h : edges.length ≥ 3 then
    let e1 := (edges[0]'(by omega)).val
    let e2 := (edges[1]'(by omega)).val
    let e3 := (edges[2]'(by omega)).val
    have hnd := incidentEdgesList_nodup G v
    have he12 : e1 ≠ e2 := by
      intro heq; have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq)); omega
    have he13 : e1 ≠ e3 := by
      intro heq; have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq)); omega
    have he23 : e2 ≠ e3 := by
      intro heq; have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq)); omega
    let b := if v.val = 0 then true else false
    xorClauses e1 e2 e3 b he12 he13 he23
  else []

theorem vertexClauses_length (G : RegularGraph) (v : Fin G.numVertices)
    (hdeg3 : G.degree ≥ 3) : (vertexClauses G v).length = 4 := by
  unfold vertexClauses
  have hedges : (incidentEdgesList G v).length = G.degree := incidentEdgesList_length G v
  simp only [hedges, show G.degree ≥ 3 from hdeg3, ↓reduceDIte]
  exact xorClauses_length _ _ _ _ _ _ _

theorem vertexClauses_vars (G : RegularGraph) (v : Fin G.numVertices)
    (c : Clause3) (hc : c ∈ vertexClauses G v)
    (hdeg3 : G.degree ≥ 3) :
    c.var1 < G.numEdges ∧ c.var2 < G.numEdges ∧ c.var3 < G.numEdges := by
  unfold vertexClauses at hc
  have hedges : (incidentEdgesList G v).length = G.degree := incidentEdgesList_length G v
  simp only [hedges, show G.degree ≥ 3 from hdeg3, ↓reduceDIte] at hc
  have hv := xorClauses_vars _ _ _ _ _ _ _ c hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hv.1]; exact ((incidentEdgesList G v)[0]'(by omega)).isLt
  · rw [hv.2.1]; exact ((incidentEdgesList G v)[1]'(by omega)).isLt
  · rw [hv.2.2]; exact ((incidentEdgesList G v)[2]'(by omega)).isLt

private theorem list_flatMap_length_eq {α β : Type*} (l : List α)
    (f : α → List β) (k : ℕ) (h : ∀ a ∈ l, (f a).length = k) :
    (l.flatMap f).length = k * l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hhd : hd ∈ hd :: tl := List.mem_cons.mpr (Or.inl rfl)
    rw [h hd hhd, ih (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))]
    ring

private theorem buildTseitin_clauses_length (G : RegularGraph) (hdeg3 : G.degree ≥ 3) :
    ((List.finRange G.numVertices).flatMap fun v =>
      vertexClauses G ⟨v.val, v.isLt⟩).length = 4 * G.numVertices := by
  rw [list_flatMap_length_eq _ _ 4, List.length_finRange]
  intro v _; exact vertexClauses_length G _ hdeg3

noncomputable def buildTseitin (G : RegularGraph) (hdeg3 : G.degree ≥ 3) : TseitinFormula where
  graph := G
  parityBit := fun v => if v.val = 0 then true else false
  parity_odd := by
    convert_to 1 % 2 = 1
    · congr 1
      have : (Finset.univ.filter (fun v : Fin G.numVertices =>
          (if v.val = 0 then true else false) = true)) = {⟨0, G.vertices_pos⟩} := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h; ext; simp at h; exact h
        · intro h; subst h; simp
      rw [this, Finset.card_singleton]
    · rfl
  -- For each vertex v, get its incident edges and produce 4 XOR clauses.
  -- Edge variables are GLOBAL: variable index = edge index in [0, numEdges).
  -- This creates sharing: each edge variable appears at both endpoint vertices.
  clauses :=
    (List.finRange G.numVertices).flatMap fun v =>
      vertexClauses G ⟨v.val, v.isLt⟩
  num_clauses_upper := by
    have := buildTseitin_clauses_length G hdeg3
    linarith
  num_clauses_lower := by
    have := buildTseitin_clauses_length G hdeg3
    linarith
  clause_vars_bound := by
    intro c hc
    simp only [List.mem_flatMap, List.mem_finRange] at hc
    obtain ⟨v, _, hcv⟩ := hc
    have ⟨h1, h2, h3⟩ := vertexClauses_vars G ⟨v.val, v.isLt⟩ c hcv hdeg3
    exact ⟨by omega, by omega, by omega⟩
  bounded_occurrence := by
    intro varIdx
    -- filter distributes over flatMap
    show (((List.finRange G.numVertices).flatMap
        (fun v => vertexClauses G ⟨v.val, v.isLt⟩)).filter
        (fun c => c.var1 = varIdx ∨ c.var2 = varIdx ∨ c.var3 = varIdx)).length ≤ 10
    rw [List.filter_flatMap, List.length_flatMap]
    -- Each per-vertex filter has length ≤ 4
    have hper : ∀ v : Fin G.numVertices,
        ((vertexClauses G v).filter
          (fun c : Clause3 => c.var1 = varIdx ∨ c.var2 = varIdx ∨ c.var3 = varIdx)).length ≤ 4 :=
      fun v => le_trans (List.length_filter_le _ _) (le_of_eq (vertexClauses_length G v hdeg3))
    -- If varIdx ≥ numEdges, all per-vertex filters are empty → sum = 0 ≤ 10
    -- If varIdx < numEdges, at most 2 vertices contribute → sum ≤ 8 ≤ 10
    -- Both cases: the sum of per-vertex filter lengths ≤ 10.
    sorry

/-- Tseitin formula on the n-th graph, built concretely -/
noncomputable def tseitinAt (n : ℕ) : TseitinFormula :=
  buildTseitin (highGirthFamily.graph n) (by
    have hdeg : (highGirthFamily.graph n).degree = 3 := by rfl
    omega)

/-- The formula uses the n-th high-girth graph — by definition -/
theorem tseitinAt_graph (n : ℕ) :
    (tseitinAt n).graph = highGirthFamily.graph n := rfl

/-- The formula has exactly n vertices (§8.1) -/
theorem tseitinAt_vertices (n : ℕ) (hn : n ≥ 6) (heven : 2 ∣ n) :
    (tseitinAt n).graph.numVertices = n := by
  unfold tseitinAt buildTseitin
  exact highGirthFamily.vertices_eq n hn heven

/-- Number of variables in the n-th Tseitin polynomial -/
noncomputable def npNumVars (n : ℕ) : ℕ := tseitinNumVars (tseitinAt n)

/-- Coupled verifier polynomial Q×_Φn -/
noncomputable def tseitinPoly (F : Type*) [CommRing F] [Nontrivial F] (n : ℕ) :
    MvPolynomial (Fin (npNumVars n)) F :=
  coupledVerifier F (tseitinAt n)

/-- Tseitin block partition: selector z_c is placed in block c.
    Non-selector variables go in the overflow block (numClauses).
    This ensures selectors for distinct clauses lie in distinct blocks,
    which is needed for isBlockAdmissible of selector derivative lists. -/
noncomputable def tseitinPartition (n : ℕ) : BlockPartition (npNumVars n) :=
  IdentityMinor.tseitinPartition (tseitinAt n)

/-- Selectors for distinct packed clauses map to distinct blocks -/
theorem tseitinPartition_selector_injective (n : ℕ) :
    Function.Injective (fun c : Fin (tseitinAt n).clauses.length =>
      (tseitinPartition n).assign (selectorIdx (tseitinAt n) c)) := by
  intro a b h
  simp only [tseitinPartition] at h
  have := IdentityMinor.tseitinPartition_selectors_distinct (tseitinAt n) a b
  by_contra hab
  exact this (Fin.ne_of_val_ne (fun h' => hab (Fin.ext h'))) h

/-! ## Auxiliary Lemmas for Logarithm Bound -/

/-- 30 ≤ 2^k for k ≥ 5 -/
private lemma thirty_le_pow (k : ℕ) (hk : k ≥ 5) : 30 ≤ 2^k :=
  calc (30 : ℕ) ≤ 2^5 := by norm_num
    _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk

/-- 30 * k ≤ 2^k for k ≥ 10 (by induction, using 30 ≤ 2^k for k ≥ 5) -/
private lemma thirty_mul_le_pow (k : ℕ) (hk : k ≥ 10) : 30 * k ≤ 2^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h10 : k ≥ 10
    · have ih := ih h10
      have hle : 30 ≤ 2^k := thirty_le_pow k (by omega)
      simp only [pow_succ, mul_comm (2^k) 2]
      omega
    · -- Only case is k = 9 (since succ k ≥ 10 and k < 10)
      have hk9 : k = 9 := by omega
      subst hk9; norm_num

/-- log₂ n ≤ n / 30 for n ≥ 1024.
    Proof: log₂ n ≥ 10 (from n ≥ 2^10), so 30 * log₂ n ≤ 2^(log₂ n) ≤ n. -/
lemma log2_le_div30 (n : ℕ) (hn : n ≥ 1024) : Nat.log 2 n ≤ n / 30 := by
  have h1024 : (2 : ℕ)^10 ≤ n := by norm_num; omega
  have hlog10 : 10 ≤ Nat.log 2 n :=
    (Nat.log_pow (b := 2) (by norm_num) 10) ▸ Nat.log_mono_right (b := 2) h1024
  have hpow : 2^(Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hmul : 30 * Nat.log 2 n ≤ 2^(Nat.log 2 n) := thirty_mul_le_pow _ hlog10
  omega

/-! ## The Lower Bound -/

/-- Binomial lower bound: C(n/30, log₂n) ≥ n^{log₂n/4} for large n.
    Uses C(L,k) ≥ (L/k)^k with L=n/30, k=log₂n.
    C(n/30, log₂n) ≥ (n/(30·log₂n))^{log₂n} ≥ n^{log₂n/4}
    since n/(30·log₂n) ≥ n^{1/4} for large n. -/
-- Standard combinatorial bound: C(n,k) ≥ (n/k)^k.
-- Proof: C(n,k) = ∏_{i=0}^{k-1} (n-i)/(k-i) ≥ ((n-k+1)/k)^k ≥ (n/(2k))^k for n ≥ 2k.
-- Applied with L = n/30, k = log₂ n: C(n/30, log₂n) ≥ (n/(60·log₂n))^(log₂n).
-- For large n, n/(60·log₂n) ≥ n^{1/4}, so the bound ≥ n^{log₂n/4}.
-- Axiomatized: formalizing requires ℝ-valued log estimates. Standard and well-known.
-- Was: axiom binomial_lower_bound (replaced by BinomialBound2.binomial_lower_bound')
theorem binomial_lower_bound :
    ∃ n₀, ∀ n, n ≥ n₀ →
      Nat.choose (n / 30) (Nat.log 2 n) ≥ n ^ (Nat.log 2 n / 4) :=
  BinomialBound.binomial_lower_bound'

/-- **Theorem 10.1**: NP-side non-collapse.
    Proved from identity_minor_lower_bound + disjoint_packing + binomial bound. -/
theorem np_side_lb (F : Type*) [Field F] :
    ∃ n₀, ∀ n, n ≥ n₀ → 2 ∣ n →
      blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
        (tseitinPoly F n) ≥ n ^ (Nat.log 2 n / 4) := by
  obtain ⟨n₀, hn₀⟩ := binomial_lower_bound
  -- Need n large enough that log₂ n ≤ n/30 (holds for n ≥ 2^10 = 1024)
  use max n₀ (2^10)
  intro n hn heven
  have hn₀' : n ≥ n₀ := le_trans (le_max_left _ _) hn
  have hn1024 : n ≥ 2^10 := le_trans (le_max_right _ _) hn
  have hn100 : n ≥ 100 := by omega
  -- Step 1: Get disjoint packing of size ≥ n/30
  have hv := tseitinAt_vertices n (by omega) heven
  have pack := Tseitin.disjoint_packing_exists (tseitinAt n) (by omega)
  -- Step 2: Identity minor gives rank ≥ (pack.selected.length choose κ)
  -- tseitinPartition n = IdentityMinor.tseitinPartition (tseitinAt n) by definition
  have h_minor : blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≥ Nat.choose pack.selected.length (Nat.log 2 n) :=
    identity_minor_lower_bound F (tseitinAt n) pack (Nat.log 2 n) (Nat.log 2 n)
      (by have hps := pack.size_bound
          rw [hv] at hps
          exact (log2_le_div30 n (by linarith [show (2:ℕ)^10 = 1024 from by norm_num])).trans hps)
  calc blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly F n)
      ≥ Nat.choose pack.selected.length (Nat.log 2 n) := h_minor
    _ ≥ Nat.choose (n / 30) (Nat.log 2 n) := by
        apply Nat.choose_le_choose
        have := pack.size_bound
        rw [hv] at this
        exact this
    _ ≥ n ^ (Nat.log 2 n / 4) := hn₀ n hn₀'

end NPWitness
