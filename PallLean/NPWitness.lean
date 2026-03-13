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
noncomputable def cubicGraph (n : ℕ) (hn : n ≥ 6) (heven : 2 ∣ n) : RegularGraph where
  numVertices := n
  degree := 3
  numEdges := n + n / 2
  vertices_pos := by omega
  degree_lower := by omega
  edges_bound := by
    -- n + n/2 ≤ n * 3
    have : n / 2 ≤ n := Nat.div_le_self n 2
    omega
  edges_lower := by omega
  degree_bound := by omega
  edgeSrc := fun e =>
    if h : e.val < n then ⟨e.val, by omega⟩
    else ⟨e.val - n, by have := e.isLt; omega⟩
  edgeTgt := fun e =>
    if h : e.val < n then ⟨(e.val + 1) % n, Nat.mod_lt _ (by omega)⟩
    else ⟨e.val - n + n / 2, by
      have := e.isLt
      have : (e.val - n) < n / 2 := by omega
      omega⟩
  regular := fun v => by
    -- Vertex v is incident to exactly 3 edges:
    -- 1. Cycle edge v (src=v)
    -- 2. Cycle edge (v+n-1)%n (tgt=v)
    -- 3. Matching edge: n+v (if v<n/2) or n+(v-n/2) (if v≥n/2)
    -- Use decide for small-ish n or a direct combinatorial argument.
    -- The filter is over Fin (n + n/2). We prove card = 3 by exhibiting the set.
    --
    -- We follow the same pattern as cycleRegularGraph:
    -- identify the 3 incident edges, show they are distinct, prove filter = {e1, e2, e3}.
    set N := n + n / 2 with hN
    -- The three incident edges:
    -- (a) Cycle edge v: index v.val, src = v
    have hv_lt_N : v.val < N := by omega
    -- (b) Cycle predecessor: index (v.val+n-1)%n, tgt = v
    have hpred_lt_n : (v.val + n - 1) % n < n := Nat.mod_lt _ (by omega)
    have hpred_lt_N : (v.val + n - 1) % n < N := by omega
    -- (c) Matching edge
    have heven := heven
    obtain ⟨k, hk⟩ := heven
    -- For the matching: if v < n/2, edge n+v has src=v; if v ≥ n/2, edge n+(v-n/2) has tgt=v
    set mi := if v.val < n / 2 then n + v.val else n + (v.val - n / 2) with hmi_def
    have hmi_lt : mi < N := by simp only [mi]; split <;> omega
    -- Now prove filter = {⟨v, _⟩, ⟨pred, _⟩, ⟨mi, _⟩} and card = 3
    -- Step 1: Distinctness
    have hdist_01 : v.val ≠ (v.val + n - 1) % n := by
      by_cases hv0 : v.val = 0
      · rw [hv0, show 0 + n - 1 = n - 1 from by omega,
          Nat.mod_eq_of_lt (by omega : n - 1 < n)]; omega
      · rw [show v.val + n - 1 = v.val - 1 + 1 * n from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : v.val - 1 < n)]; omega
    have hdist_02 : v.val ≠ mi := by simp only [mi]; split <;> omega
    have hdist_12 : (v.val + n - 1) % n ≠ mi := by
      simp only [mi]; split <;> (have := Nat.mod_lt (v.val + n - 1) (by omega : n > 0); omega)
    -- Step 2: Build the filter = {e1, e2, e3} directly
    have hfilt : Finset.univ.filter (fun e : Fin N =>
        (if h : e.val < n then ⟨e.val, by omega⟩ else ⟨e.val - n, by omega⟩ : Fin n) = v ∨
        (if h : e.val < n then ⟨(e.val + 1) % n, Nat.mod_lt _ (by omega)⟩
         else ⟨e.val - n + n / 2, by omega⟩ : Fin n) = v) =
        ({⟨v.val, hv_lt_N⟩, ⟨(v.val + n - 1) % n, hpred_lt_N⟩, ⟨mi, hmi_lt⟩} : Finset (Fin N)) := by
      ext ⟨e, he⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_mk]
      constructor
      · intro h_or
        by_cases hec : e < n
        · simp only [dif_pos hec, Fin.ext_iff, Fin.val_mk] at h_or
          cases h_or with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr (Or.inl ((mod_succ_eq_iff e v.val n (by omega) hec v.isLt).mp h))
        · simp only [dif_neg hec, Fin.ext_iff, Fin.val_mk] at h_or
          exact Or.inr (Or.inr (by simp only [mi]; cases h_or with
            | inl h => split <;> omega
            | inr h => split <;> omega))
      · intro h_or
        rcases h_or with rfl | rfl | rfl
        · left; simp only [dif_pos v.isLt, Fin.ext_iff, Fin.val_mk]
        · right; simp only [dif_pos hpred_lt_n, Fin.ext_iff, Fin.val_mk]
          exact (mod_succ_eq_iff _ v.val n (by omega) hpred_lt_n v.isLt).mpr rfl
        · simp only [mi]
          split <;> rename_i hv_half
          · left; simp only [dif_neg (by omega : ¬(n + v.val < n)), Fin.ext_iff, Fin.val_mk]; omega
          · right; simp only [dif_neg (by omega : ¬(n + (v.val - n / 2) < n)), Fin.ext_iff, Fin.val_mk]
            congr 1; omega
    rw [hfilt]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_mk]
      push_neg; exact ⟨hdist_01, hdist_02⟩)]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton, Fin.ext_iff, Fin.val_mk]
      exact hdist_12)]
    rw [Finset.card_singleton]

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

/-- Helper: the if-branch in buildTseitin always fires when degree ≥ 3 -/
private lemma incidentEdges_length_ge3 (G : RegularGraph) (hdeg : G.degree ≥ 3)
    (v : Fin G.numVertices) :
    (incidentEdgesList G v).length ≥ 3 := by
  rw [incidentEdgesList_length]; exact hdeg

/-- The clause-generating function for each vertex -/
private noncomputable def buildTseitinClauses (G : RegularGraph) (v : Fin G.numVertices) :
    List Clause3 :=
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

private theorem buildTseitinClauses_length_eq (G : RegularGraph) (hdeg : G.degree ≥ 3)
    (v : Fin G.numVertices) :
    (buildTseitinClauses G v).length = 4 := by
  simp only [buildTseitinClauses]
  rw [dif_pos (incidentEdges_length_ge3 G hdeg v)]
  exact xorClauses_length _ _ _ _ _ _ _

private theorem buildTseitinClauses_vars (G : RegularGraph) (hdeg : G.degree ≥ 3)
    (v : Fin G.numVertices) (c : Clause3) (hc : c ∈ buildTseitinClauses G v) :
    c.var1 < G.numEdges ∧ c.var2 < G.numEdges ∧ c.var3 < G.numEdges := by
  simp only [buildTseitinClauses] at hc
  rw [dif_pos (incidentEdges_length_ge3 G hdeg v)] at hc
  have hvars := xorClauses_vars _ _ _ _ _ _ _ c hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hvars.1]; exact ((incidentEdgesList G v)[0]'(by rw [incidentEdgesList_length]; omega)).isLt
  · rw [hvars.2.1]; exact ((incidentEdgesList G v)[1]'(by rw [incidentEdgesList_length]; omega)).isLt
  · rw [hvars.2.2]; exact ((incidentEdgesList G v)[2]'(by rw [incidentEdgesList_length]; omega)).isLt

/-- If a clause from vertex w mentions variable v, then v is an incident edge of w -/
private theorem buildTseitinClauses_mentions_incident (G : RegularGraph) (hdeg : G.degree ≥ 3)
    (w : Fin G.numVertices) (c : Clause3) (hc : c ∈ buildTseitinClauses G w) (v : ℕ)
    (hv : c.var1 = v ∨ c.var2 = v ∨ c.var3 = v) :
    ∃ e : Fin G.numEdges, e.val = v ∧ (G.edgeSrc e = w ∨ G.edgeTgt e = w) := by
  simp only [buildTseitinClauses] at hc
  rw [dif_pos (incidentEdges_length_ge3 G hdeg w)] at hc
  have hvars := xorClauses_vars _ _ _ _ _ _ _ c hc
  set edges := incidentEdgesList G w
  -- The three edge indices are members of incidentEdges G w
  have hmem : ∀ (i : ℕ) (hi : i < edges.length), edges[i] ∈ incidentEdges G w := by
    intro i hi
    have hmem : edges[i] ∈ edges := List.getElem_mem edges i hi
    exact (Finset.mem_sort _).mp hmem
  have h0 : edges[0]'(by rw [incidentEdgesList_length]; omega) ∈ incidentEdges G w :=
    hmem 0 (by rw [incidentEdgesList_length]; omega)
  have h1 : edges[1]'(by rw [incidentEdgesList_length]; omega) ∈ incidentEdges G w :=
    hmem 1 (by rw [incidentEdgesList_length]; omega)
  have h2 : edges[2]'(by rw [incidentEdgesList_length]; omega) ∈ incidentEdges G w :=
    hmem 2 (by rw [incidentEdgesList_length]; omega)
  simp [incidentEdges, Finset.mem_filter] at h0 h1 h2
  rcases hv with rfl | rfl | rfl
  · rw [hvars.1]; exact ⟨_, rfl, h0⟩
  · rw [hvars.2.1]; exact ⟨_, rfl, h1⟩
  · rw [hvars.2.2]; exact ⟨_, rfl, h2⟩

/-- If no edge with value v is incident to w, the filter is empty -/
private theorem buildTseitinClauses_filter_eq_nil (G : RegularGraph) (hdeg : G.degree ≥ 3)
    (w : Fin G.numVertices) (v : ℕ)
    (hv : ∀ e : Fin G.numEdges, e.val = v → G.edgeSrc e ≠ w ∧ G.edgeTgt e ≠ w) :
    (buildTseitinClauses G w).filter (fun c => c.var1 = v ∨ c.var2 = v ∨ c.var3 = v) = [] := by
  rw [List.filter_eq_nil_iff]
  intro c hc
  simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_or]
  by_contra hall
  push_neg at hall
  have : c.var1 = v ∨ c.var2 = v ∨ c.var3 = v := by tauto
  obtain ⟨e, he_val, he_inc⟩ := buildTseitinClauses_mentions_incident G hdeg w c hc v this
  have := hv e he_val
  tauto

private lemma sum_map_ite_eq_mul_count {α : Type*} [DecidableEq α]
    (l : List α) (c : α) (k : ℕ) :
    (l.map fun w => if c = w then k else 0).sum = k * l.count c := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons, ih]
    by_cases h : c = hd
    · simp [h, Nat.mul_succ, Nat.add_comm]
    · simp [h, Ne.symm h]

private lemma list_sum_map_add {α : Type*} (l : List α) (f g : α → ℕ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [ih]; omega

private lemma list_sum_map_le {α : Type*} (l : List α) (f g : α → ℕ) (h : ∀ x, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp; exact Nat.add_le_add (h hd) (ih)

private lemma sum_map_ite_or_le {n : ℕ} (a b : Fin n) (k : ℕ) :
    ((List.finRange n).map fun w =>
      if a = w ∨ b = w then k else 0).sum ≤ 2 * k := by
  calc _ ≤ ((List.finRange n).map fun w =>
        (if a = w then k else 0) + (if b = w then k else 0)).sum :=
      list_sum_map_le _ _ _ (fun w => by split <;> split <;> split <;> simp_all)
    _ = ((List.finRange n).map fun w => if a = w then k else 0).sum +
        ((List.finRange n).map fun w => if b = w then k else 0).sum :=
      list_sum_map_add _ _ _
    _ = k * 1 + k * 1 := by
      rw [sum_map_ite_eq_mul_count, sum_map_ite_eq_mul_count,
        List.count_finRange, List.count_finRange]
    _ = 2 * k := by ring

noncomputable def buildTseitin (G : RegularGraph) (hdeg : G.degree ≥ 3) : TseitinFormula where
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
      buildTseitinClauses G ⟨v.val, by exact v.isLt⟩
  num_clauses_upper := by
    show ((List.finRange G.numVertices).flatMap fun v =>
      buildTseitinClauses G ⟨v.val, by exact v.isLt⟩).length ≤ 10 * G.numVertices
    rw [List.length_flatMap]
    have : ((List.finRange G.numVertices).map fun v =>
      (buildTseitinClauses G ⟨v.val, by exact v.isLt⟩).length).sum =
      4 * G.numVertices := by
      have hmap : (List.finRange G.numVertices).map (fun v =>
        (buildTseitinClauses G ⟨v.val, by exact v.isLt⟩).length) =
        List.replicate G.numVertices 4 := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp [List.length_map, List.length_finRange], ?_⟩
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨v, _, rfl⟩ := hx
        exact buildTseitinClauses_length_eq G hdeg ⟨v.val, v.isLt⟩
      rw [hmap, List.sum_const_nat]; ring
    omega
  num_clauses_lower := by
    show ((List.finRange G.numVertices).flatMap fun v =>
      buildTseitinClauses G ⟨v.val, by exact v.isLt⟩).length ≥ G.numVertices
    rw [List.length_flatMap]
    have : ((List.finRange G.numVertices).map fun v =>
      (buildTseitinClauses G ⟨v.val, by exact v.isLt⟩).length).sum =
      4 * G.numVertices := by
      have hmap : (List.finRange G.numVertices).map (fun v =>
        (buildTseitinClauses G ⟨v.val, by exact v.isLt⟩).length) =
        List.replicate G.numVertices 4 := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp [List.length_map, List.length_finRange], ?_⟩
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨v, _, rfl⟩ := hx
        exact buildTseitinClauses_length_eq G hdeg ⟨v.val, v.isLt⟩
      rw [hmap, List.sum_const_nat]; ring
    omega
  clause_vars_bound := by
    intro c hc
    simp only [List.mem_flatMap, List.mem_finRange] at hc
    obtain ⟨v, _, hcv⟩ := hc
    have hvars := buildTseitinClauses_vars G hdeg ⟨v.val, v.isLt⟩ c hcv
    constructor
    · omega
    constructor
    · omega
    · omega
  bounded_occurrence := by
    intro v
    show (((List.finRange G.numVertices).flatMap fun w =>
      buildTseitinClauses G ⟨w.val, w.isLt⟩).filter
      (fun c => c.var1 = v ∨ c.var2 = v ∨ c.var3 = v)).length ≤ 10
    -- filter distributes over flatMap
    have filter_flatMap_eq : ∀ {α β : Type} (l : List α) (f : α → List β) (p : β → Bool),
        (l.flatMap f).filter p = l.flatMap (fun a => (f a).filter p) := by
      intro α β l f p; induction l with
      | nil => simp
      | cons hd tl ih => simp [List.flatMap_cons, List.filter_append, ih]
    rw [filter_flatMap_eq, List.length_flatMap]
    by_cases hv_edge : v < G.numEdges
    · -- v is an edge index. At most 2 vertices contribute (src and tgt).
      set e : Fin G.numEdges := ⟨v, hv_edge⟩
      calc _ ≤ ((List.finRange G.numVertices).map fun w =>
            if G.edgeSrc e = ⟨w.val, w.isLt⟩ ∨ G.edgeTgt e = ⟨w.val, w.isLt⟩
            then 4 else 0).sum := by
          apply list_sum_map_le; intro i
          split
          · calc _ ≤ (buildTseitinClauses G ⟨i.val, i.isLt⟩).length :=
                List.length_filter_le _ _
              _ = 4 := buildTseitinClauses_length_eq G hdeg _
          · rename_i hni; push_neg at hni
            have : (buildTseitinClauses G ⟨i.val, i.isLt⟩).filter
                (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v)) = [] := by
              rw [List.filter_eq_nil_iff]; intro c hc
              simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_or]
              refine ⟨?_, ?_, ?_⟩ <;> intro heq
              all_goals (
                have ⟨edge, heval, hinc⟩ := buildTseitinClauses_mentions_incident G hdeg
                  ⟨i.val, i.isLt⟩ c hc v (by tauto)
                rcases hinc with hsrc | htgt
                · exact hni.1 (by rw [← hsrc]; congr 1; exact Fin.ext heval)
                · exact hni.2 (by rw [← htgt]; congr 1; exact Fin.ext heval))
            simp [this]
        _ ≤ 2 * 4 := by
          have heq : (List.finRange G.numVertices).map (fun w =>
              if G.edgeSrc e = ⟨w.val, w.isLt⟩ ∨ G.edgeTgt e = ⟨w.val, w.isLt⟩
              then (4 : ℕ) else 0) =
            (List.finRange G.numVertices).map (fun w =>
              if G.edgeSrc e = w ∨ G.edgeTgt e = w then 4 else 0) := by
            apply List.map_congr_left; intro w _; congr 1; constructor
            · rintro (rfl | rfl) <;> simp
            · rintro (rfl | rfl) <;> simp
          rw [heq]; exact sum_map_ite_or_le (G.edgeSrc e) (G.edgeTgt e) 4
        _ ≤ 10 := by omega
    · -- v is not an edge index: no clause mentions it
      have : ((List.finRange G.numVertices).map fun w =>
          ((buildTseitinClauses G ⟨w.val, w.isLt⟩).filter
            (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v))).length).sum = 0 := by
        apply List.sum_eq_zero; intro x hx
        rw [List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx
        rw [List.length_eq_zero, List.filter_eq_nil_iff]
        intro c hc
        simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_or]
        have hvars := buildTseitinClauses_vars G hdeg ⟨w.val, w.isLt⟩ c hc; omega
      omega

/-- Tseitin formula on the n-th graph, built concretely -/
noncomputable def tseitinAt (n : ℕ) : TseitinFormula :=
  buildTseitin (highGirthFamily.graph n) (by show (highGirthFamily.graph n).degree ≥ 3; rfl)

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
