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

/-- In a cycle on `n ≥ 3`, the predecessor of `v` is different from `v`. -/
private lemma pred_mod_ne_self (n : ℕ) (hn : n ≥ 3) (v : Fin n) :
    (v.val + n - 1) % n ≠ v.val := by
  intro h
  by_cases hv0 : v.val = 0
  · rw [hv0, show 0 + n - 1 = n - 1 from by omega,
      Nat.mod_eq_of_lt (by omega : n - 1 < n)] at h
    omega
  · rw [show v.val + n - 1 = v.val - 1 + 1 * n from by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : v.val - 1 < n)] at h
    omega

private lemma cubic_cycle_src_eq_iff
    (n : ℕ) (v : Fin n) (e : Fin (n + n / 2)) (he : e.val < n) :
    (⟨e.val, by omega⟩ : Fin n) = v ↔ e.val = v.val := by
  simp [Fin.ext_iff]

private lemma cubic_cycle_tgt_eq_iff
    (n : ℕ) (hn : n ≥ 1) (v : Fin n) (e : Fin (n + n / 2)) (he : e.val < n) :
    (⟨(e.val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = v ↔
      e.val = (v.val + n - 1) % n := by
  constructor
  · intro h
    exact (mod_succ_eq_iff e.val v.val n hn he v.isLt).mp (Fin.ext_iff.mp h)
  · intro h
    apply Fin.ext
    exact (mod_succ_eq_iff e.val v.val n hn he v.isLt).mpr h

private lemma cubic_match_src_eq_iff_left
    (n : ℕ) (v : Fin n) (hv : v.val < n / 2) (e : Fin (n + n / 2)) (he : ¬ e.val < n) :
    (⟨e.val - n, by have := e.isLt; omega⟩ : Fin n) = v ↔ e.val = n + v.val := by
  simp [Fin.ext_iff]
  omega

private lemma cubic_match_tgt_ne_left
    (n : ℕ) (v : Fin n) (hv : v.val < n / 2) (e : Fin (n + n / 2)) (he : ¬ e.val < n) :
    (⟨e.val - n + n / 2, by
        have := e.isLt
        have : e.val - n < n / 2 := by omega
        omega⟩ : Fin n) ≠ v := by
  intro h
  have hk : e.val - n < n / 2 := by
    have := e.isLt
    omega
  have hge : n / 2 ≤ e.val - n + n / 2 := by
    simpa [Nat.add_comm] using Nat.le_add_left (e.val - n) (n / 2)
  have hval : v.val = e.val - n + n / 2 := by
    simpa using (Fin.ext_iff.mp h).symm
  exact (Nat.not_lt.mpr hge) (hval ▸ hv)

private lemma cubic_match_src_ne_right
    (n : ℕ) (v : Fin n) (hv : ¬ v.val < n / 2) (e : Fin (n + n / 2)) (he : ¬ e.val < n) :
    (⟨e.val - n, by have := e.isLt; omega⟩ : Fin n) ≠ v := by
  intro h
  have hk : e.val - n < n / 2 := by
    have := e.isLt
    omega
  have hval : v.val = e.val - n := by
    simpa using (Fin.ext_iff.mp h).symm
  exact hv (hval ▸ hk)

private lemma cubic_match_tgt_eq_iff_right
    (n : ℕ) (v : Fin n) (hv : ¬ v.val < n / 2) (e : Fin (n + n / 2)) (he : ¬ e.val < n) :
    (⟨e.val - n + n / 2, by
        have := e.isLt
        have : e.val - n < n / 2 := by omega
        omega⟩ : Fin n) = v ↔ e.val = n + (v.val - n / 2) := by
  simp [Fin.ext_iff]
  omega

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
    classical
    have hne : 1 ≤ n := by omega
    let cycleEdge : Fin (n + n / 2) := ⟨v.val, by omega⟩
    let predEdge : Fin (n + n / 2) := ⟨(v.val + n - 1) % n,
      lt_of_lt_of_le (Nat.mod_lt _ hne) (Nat.le_add_right n (n / 2))⟩
    have hcycle_lt : cycleEdge.val < n := by
      simp [cycleEdge]
    have hpred_lt : predEdge.val < n := by
      simp [predEdge]
      exact Nat.mod_lt _ hne
    have hpred_ne : predEdge ≠ cycleEdge := by
      intro h
      have hval := congr_arg Fin.val h
      simp [predEdge, cycleEdge] at hval
      exact pred_mod_ne_self n (by omega) v hval
    by_cases hv : v.val < n / 2
    · let matchEdge : Fin (n + n / 2) := ⟨n + v.val, by omega⟩
      have hmatch_ge : n ≤ matchEdge.val := by
        simp [matchEdge]
      have hcycle_match : cycleEdge ≠ matchEdge := by
        intro h
        have hval : cycleEdge.val = matchEdge.val := congr_arg Fin.val h
        omega
      have hpred_match : predEdge ≠ matchEdge := by
        intro h
        have hval : predEdge.val = matchEdge.val := congr_arg Fin.val h
        omega
      have hfilt : Finset.univ.filter (fun e : Fin (n + n / 2) =>
          (if h : e.val < n then (⟨e.val, by omega⟩ : Fin n)
           else ⟨e.val - n, by have := e.isLt; omega⟩) = v ∨
          (if h : e.val < n then (⟨(e.val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n)
           else ⟨e.val - n + n / 2, by
             have := e.isLt
             have : e.val - n < n / 2 := by omega
             omega⟩) = v) = {cycleEdge, predEdge, matchEdge} := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases he : e.val < n
        · rw [dif_pos he, dif_pos he, cubic_cycle_src_eq_iff n v e he,
            cubic_cycle_tgt_eq_iff n hne v e he]
          constructor
          · intro h
            rcases h with h | h
            · exact Or.inl (Fin.ext h)
            · exact Or.inr <| Or.inl (Fin.ext h)
          · intro h
            rcases h with h | h
            · exact Or.inl (Fin.ext_iff.mp h)
            · rcases h with h | h
              · exact Or.inr (Fin.ext_iff.mp h)
              · exfalso
                have hval : e.val = matchEdge.val := congr_arg Fin.val h
                omega
        · rw [dif_neg he, dif_neg he]
          constructor
          · intro h
            rcases h with h | h
            · exact Or.inr <| Or.inr (Fin.ext ((cubic_match_src_eq_iff_left n v hv e he).mp h))
            · exact False.elim ((cubic_match_tgt_ne_left n v hv e he) h)
          · intro h
            rcases h with h | h
            · exfalso
              have hval : e.val = cycleEdge.val := congr_arg Fin.val h
              omega
            · rcases h with h | h
              · exfalso
                have hval : e.val = predEdge.val := congr_arg Fin.val h
                omega
              · have hval : e.val = n + v.val := by
                  simpa [matchEdge] using congr_arg Fin.val h
                exact Or.inl ((cubic_match_src_eq_iff_left n v hv e he).mpr hval)
      rw [hfilt]
      have hpred_not_mem : predEdge ∉ ({matchEdge} : Finset (Fin (n + n / 2))) := by
        simp [hpred_match]
      have hcycle_not_mem :
          cycleEdge ∉ ({predEdge, matchEdge} : Finset (Fin (n + n / 2))) := by
        simp [hcycle_match, ne_comm, hpred_ne]
      rw [Finset.card_insert_of_notMem hcycle_not_mem, Finset.card_insert_of_notMem hpred_not_mem,
        Finset.card_singleton]
    · let matchEdge : Fin (n + n / 2) := ⟨n + (v.val - n / 2), by omega⟩
      have hmatch_ge : n ≤ matchEdge.val := by
        simp [matchEdge]
      have hcycle_match : cycleEdge ≠ matchEdge := by
        intro h
        have hval : cycleEdge.val = matchEdge.val := congr_arg Fin.val h
        omega
      have hpred_match : predEdge ≠ matchEdge := by
        intro h
        have hval : predEdge.val = matchEdge.val := congr_arg Fin.val h
        omega
      have hfilt : Finset.univ.filter (fun e : Fin (n + n / 2) =>
          (if h : e.val < n then (⟨e.val, by omega⟩ : Fin n)
           else ⟨e.val - n, by have := e.isLt; omega⟩) = v ∨
          (if h : e.val < n then (⟨(e.val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n)
           else ⟨e.val - n + n / 2, by
             have := e.isLt
             have : e.val - n < n / 2 := by omega
             omega⟩) = v) = {cycleEdge, predEdge, matchEdge} := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases he : e.val < n
        · rw [dif_pos he, dif_pos he, cubic_cycle_src_eq_iff n v e he,
            cubic_cycle_tgt_eq_iff n hne v e he]
          constructor
          · intro h
            rcases h with h | h
            · exact Or.inl (Fin.ext h)
            · exact Or.inr <| Or.inl (Fin.ext h)
          · intro h
            rcases h with h | h
            · exact Or.inl (Fin.ext_iff.mp h)
            · rcases h with h | h
              · exact Or.inr (Fin.ext_iff.mp h)
              · exfalso
                have hval : e.val = matchEdge.val := congr_arg Fin.val h
                omega
        · rw [dif_neg he, dif_neg he]
          constructor
          · intro h
            rcases h with h | h
            · exact False.elim ((cubic_match_src_ne_right n v hv e he) h)
            · exact Or.inr <| Or.inr (Fin.ext ((cubic_match_tgt_eq_iff_right n v hv e he).mp h))
          · intro h
            rcases h with h | h
            · exfalso
              have hval : e.val = cycleEdge.val := congr_arg Fin.val h
              omega
            · rcases h with h | h
              · exfalso
                have hval : e.val = predEdge.val := congr_arg Fin.val h
                omega
              · have hval : e.val = n + (v.val - n / 2) := by
                  simpa [matchEdge] using congr_arg Fin.val h
                exact Or.inr ((cubic_match_tgt_eq_iff_right n v hv e he).mpr hval)
      rw [hfilt]
      have hpred_not_mem : predEdge ∉ ({matchEdge} : Finset (Fin (n + n / 2))) := by
        simp [hpred_match]
      have hcycle_not_mem :
          cycleEdge ∉ ({predEdge, matchEdge} : Finset (Fin (n + n / 2))) := by
        simp [hcycle_match, ne_comm, hpred_ne]
      rw [Finset.card_insert_of_notMem hcycle_not_mem, Finset.card_insert_of_notMem hpred_not_mem,
        Finset.card_singleton]

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

/-- The four XOR clauses contributed by a single vertex when the graph is cubic. -/
private noncomputable def vertexClauses (G : RegularGraph) (v : Fin G.numVertices) :
    List Clause3 :=
  let edges := incidentEdgesList G v
  if h : edges.length ≥ 3 then
    let e1 := (edges[0]'(by omega)).val
    let e2 := (edges[1]'(by omega)).val
    let e3 := (edges[2]'(by omega)).val
    have hnd := incidentEdgesList_nodup G v
    have he12 : e1 ≠ e2 := by
      intro heq; have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq))
      omega
    have he13 : e1 ≠ e3 := by
      intro heq; have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq))
      omega
    have he23 : e2 ≠ e3 := by
      intro heq; have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq))
      omega
    let b := if v.val = 0 then true else false
    xorClauses e1 e2 e3 b he12 he13 he23
  else []

private theorem vertexClauses_length_of_degree_eq_three (G : RegularGraph)
    (hdeg : G.degree = 3) (v : Fin G.numVertices) :
    (vertexClauses G v).length = 4 := by
  unfold vertexClauses
  have hedges : (incidentEdgesList G v).length = 3 := by
    simpa [hdeg] using incidentEdgesList_length G v
  have hbranch : (incidentEdgesList G v).length ≥ 3 := by omega
  simp [hbranch, xorClauses_length]

private theorem buildTseitin_clauses_length_of_degree_eq_three (G : RegularGraph)
    (hdeg : G.degree = 3) :
    ((List.finRange G.numVertices).flatMap (vertexClauses G)).length = 4 * G.numVertices := by
  rw [List.length_flatMap]
  have hmap :
      List.map (fun v => (vertexClauses G v).length) (List.finRange G.numVertices) =
        List.replicate G.numVertices 4 := by
    apply List.ext_getElem
    · simp [List.length_finRange]
    · intro i hi1 hi2
      rw [List.getElem_map, List.getElem_replicate]
      rw [List.getElem_finRange]
      simpa using
        vertexClauses_length_of_degree_eq_three G hdeg
          ⟨i, by simpa [List.length_finRange] using hi1⟩
  rw [hmap]
  simp [List.sum_replicate, Nat.mul_comm]

private theorem vertexClauses_vars_lt_numEdges (G : RegularGraph)
    (v : Fin G.numVertices) (c : Clause3) (hc : c ∈ vertexClauses G v) :
    c.var1 < G.numEdges ∧ c.var2 < G.numEdges ∧ c.var3 < G.numEdges := by
  unfold vertexClauses at hc
  by_cases hlen : (incidentEdgesList G v).length ≥ 3
  · have hnd := incidentEdgesList_nodup G v
    have he12 : ((incidentEdgesList G v)[0]'(by omega)).val ≠ ((incidentEdgesList G v)[1]'(by omega)).val := by
      intro heq
      have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq))
      omega
    have he13 : ((incidentEdgesList G v)[0]'(by omega)).val ≠ ((incidentEdgesList G v)[2]'(by omega)).val := by
      intro heq
      have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq))
      omega
    have he23 : ((incidentEdgesList G v)[1]'(by omega)).val ≠ ((incidentEdgesList G v)[2]'(by omega)).val := by
      intro heq
      have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq))
      omega
    by_cases hb : v.val = 0
    · simp [hlen, hb, xorClauses] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals
        constructor
        · simpa using ((incidentEdgesList G v)[0]'(by omega)).isLt
        constructor
        · simpa using ((incidentEdgesList G v)[1]'(by omega)).isLt
        · simpa using ((incidentEdgesList G v)[2]'(by omega)).isLt
    · simp [hlen, hb, xorClauses] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals
        constructor
        · simpa using ((incidentEdgesList G v)[0]'(by omega)).isLt
        constructor
        · simpa using ((incidentEdgesList G v)[1]'(by omega)).isLt
        · simpa using ((incidentEdgesList G v)[2]'(by omega)).isLt
  · simp [hlen] at hc

private theorem filter_flatMap_eq_flatMap_filter {α β : Type*}
    (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).filter p = l.flatMap (fun a => (f a).filter p) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih, List.filter_append]

private theorem edge_of_incident_getElem (G : RegularGraph) (v : Fin G.numVertices)
    (i : ℕ) (hi : i < (incidentEdgesList G v).length) :
    G.edgeSrc ((incidentEdgesList G v)[i]'hi) = v ∨
      G.edgeTgt ((incidentEdgesList G v)[i]'hi) = v := by
  have hmemList : ((incidentEdgesList G v)[i]'hi) ∈ incidentEdgesList G v :=
    List.getElem_mem _
  have hmemFinset : ((incidentEdgesList G v)[i]'hi) ∈ incidentEdges G v := by
    simpa [incidentEdgesList] using
      (Finset.mem_sort (s := incidentEdges G v) (r := (· ≤ ·))).1 hmemList
  simpa [incidentEdges] using hmemFinset

private theorem vertexClauses_contains_edge_imp_incident (G : RegularGraph)
    (v : Fin G.numVertices) (e : Fin G.numEdges) (c : Clause3)
    (hc : c ∈ vertexClauses G v)
    (hv : c.var1 = e.val ∨ c.var2 = e.val ∨ c.var3 = e.val) :
    G.edgeSrc e = v ∨ G.edgeTgt e = v := by
  unfold vertexClauses at hc
  by_cases hlen : (incidentEdgesList G v).length ≥ 3
  · have hnd := incidentEdgesList_nodup G v
    have he12 : ((incidentEdgesList G v)[0]'(by omega)).val ≠ ((incidentEdgesList G v)[1]'(by omega)).val := by
      intro heq
      have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq))
      omega
    have he13 : ((incidentEdgesList G v)[0]'(by omega)).val ≠ ((incidentEdgesList G v)[2]'(by omega)).val := by
      intro heq
      have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq))
      omega
    have he23 : ((incidentEdgesList G v)[1]'(by omega)).val ≠ ((incidentEdgesList G v)[2]'(by omega)).val := by
      intro heq
      have := hnd.getElem_inj_iff.mp (Fin.ext (by exact_mod_cast heq))
      omega
    by_cases hb : v.val = 0
    · have hvars := xorClauses_vars
        ((incidentEdgesList G v)[0]'(by omega)).val
        ((incidentEdgesList G v)[1]'(by omega)).val
        ((incidentEdgesList G v)[2]'(by omega)).val
        true he12 he13 he23 c
      simp [hlen, hb] at hc
      have hvars' := hvars hc
      rcases hvars' with ⟨h1, h2, h3⟩
      rcases hv with hv1 | hv2 | hv3
      · have hEq : ((incidentEdgesList G v)[0]'(by omega)) = e := by
          apply Fin.ext
          exact h1.symm.trans hv1
        simpa [hEq] using edge_of_incident_getElem G v 0 (by omega)
      · have hEq : ((incidentEdgesList G v)[1]'(by omega)) = e := by
          apply Fin.ext
          exact h2.symm.trans hv2
        simpa [hEq] using edge_of_incident_getElem G v 1 (by omega)
      · have hEq : ((incidentEdgesList G v)[2]'(by omega)) = e := by
          apply Fin.ext
          exact h3.symm.trans hv3
        simpa [hEq] using edge_of_incident_getElem G v 2 (by omega)
    · have hvars := xorClauses_vars
        ((incidentEdgesList G v)[0]'(by omega)).val
        ((incidentEdgesList G v)[1]'(by omega)).val
        ((incidentEdgesList G v)[2]'(by omega)).val
        false he12 he13 he23 c
      simp [hlen, hb] at hc
      have hvars' := hvars hc
      rcases hvars' with ⟨h1, h2, h3⟩
      rcases hv with hv1 | hv2 | hv3
      · have hEq : ((incidentEdgesList G v)[0]'(by omega)) = e := by
          apply Fin.ext
          exact h1.symm.trans hv1
        simpa [hEq] using edge_of_incident_getElem G v 0 (by omega)
      · have hEq : ((incidentEdgesList G v)[1]'(by omega)) = e := by
          apply Fin.ext
          exact h2.symm.trans hv2
        simpa [hEq] using edge_of_incident_getElem G v 1 (by omega)
      · have hEq : ((incidentEdgesList G v)[2]'(by omega)) = e := by
          apply Fin.ext
          exact h3.symm.trans hv3
        simpa [hEq] using edge_of_incident_getElem G v 2 (by omega)
  · simp [hlen] at hc

private theorem vertexClauses_filter_eq_nil_of_not_incident (G : RegularGraph)
    (v : Fin G.numVertices) (e : Fin G.numEdges)
    (hnot : ¬ (G.edgeSrc e = v ∨ G.edgeTgt e = v)) :
    (vertexClauses G v).filter
        (fun c => decide (c.var1 = e.val ∨ c.var2 = e.val ∨ c.var3 = e.val)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro c hc
  have hmem : c ∈ vertexClauses G v := List.mem_of_mem_filter hc
  have hvar : c.var1 = e.val ∨ c.var2 = e.val ∨ c.var3 = e.val := by
    simpa [decide_eq_true_eq] using List.of_mem_filter hc
  exact hnot (vertexClauses_contains_edge_imp_incident G v e c hmem hvar)

private theorem finRange_filter_incident_length_le_two (G : RegularGraph)
    (e : Fin G.numEdges) :
    ((List.finRange G.numVertices).filter
      (fun v => decide (G.edgeSrc e = v ∨ G.edgeTgt e = v))).length ≤ 2 := by
  have hnodup :
      ((List.finRange G.numVertices).filter
        (fun v => decide (G.edgeSrc e = v ∨ G.edgeTgt e = v))).Nodup := by
    exact (List.nodup_finRange _).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  have htoFinset :
      (((List.finRange G.numVertices).filter
        (fun v => decide (G.edgeSrc e = v ∨ G.edgeTgt e = v))).toFinset) =
      Finset.univ.filter (fun v : Fin G.numVertices => G.edgeSrc e = v ∨ G.edgeTgt e = v) := by
    ext v
    simp [List.mem_finRange, decide_eq_true_eq]
  rw [htoFinset]
  by_cases hst : G.edgeSrc e = G.edgeTgt e
  · have hs :
        (Finset.univ.filter (fun v : Fin G.numVertices => G.edgeSrc e = v ∨ G.edgeTgt e = v)) =
          {G.edgeSrc e} := by
        ext v
        constructor
        · intro hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hv ⊢
          rcases hv with hv | hv
          · exact hv.symm
          · exact (hst.trans hv).symm
        · intro hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hv ⊢
          left
          exact hv.symm
    rw [hs]
    simp
  · calc
      (Finset.univ.filter (fun v : Fin G.numVertices => G.edgeSrc e = v ∨ G.edgeTgt e = v)).card
        ≤ ({G.edgeSrc e, G.edgeTgt e} : Finset (Fin G.numVertices)).card := by
            apply Finset.card_le_card
            intro v hv
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
            simpa [eq_comm] using hv
      _ = 2 := by simp [hst]
noncomputable def buildTseitin (G : RegularGraph) (hdeg : G.degree = 3) : TseitinFormula where
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
    (List.finRange G.numVertices).flatMap (vertexClauses G)
  num_clauses_upper := by
    rw [buildTseitin_clauses_length_of_degree_eq_three G hdeg]
    omega
  num_clauses_lower := by
    rw [buildTseitin_clauses_length_of_degree_eq_three G hdeg]
    omega
  clause_vars_bound := by
    intro c hc
    rcases List.mem_flatMap.1 hc with ⟨v, hv, hc⟩
    have hvars := vertexClauses_vars_lt_numEdges G v c hc
    rcases hvars with ⟨h1, h2, h3⟩
    constructor
    · omega
    constructor
    · omega
    · omega
  bounded_occurrence := by
    -- Each edge variable appears at both endpoints: 4 clauses per endpoint = 8 total ≤ 10.
    intro v
    by_cases hv : v < G.numEdges
    · let e : Fin G.numEdges := ⟨v, hv⟩
      let verts :=
        (List.finRange G.numVertices).filter
          (fun w => decide (G.edgeSrc e = w ∨ G.edgeTgt e = w))
      have hfilter :
          (((List.finRange G.numVertices).flatMap (vertexClauses G)).filter
            (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v))) =
          (List.finRange G.numVertices).flatMap (fun w =>
            (vertexClauses G w).filter
              (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v))) := by
        simpa using filter_flatMap_eq_flatMap_filter
          (List.finRange G.numVertices) (vertexClauses G)
          (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v))
      rw [hfilter]
      have hsub :
          List.Sublist
            (((List.finRange G.numVertices).flatMap (fun w =>
              (vertexClauses G w).filter
                (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v)))))
            (((List.finRange G.numVertices).flatMap (fun w =>
              if G.edgeSrc e = w ∨ G.edgeTgt e = w then vertexClauses G w else []))) := by
        apply List.Sublist.flatMap_right
        intro w hw
        by_cases hw' : G.edgeSrc e = w ∨ G.edgeTgt e = w
        · simpa [hw'] using
            (List.filter_sublist
              (p := fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v))
              (l := vertexClauses G w))
        · have hnil :
            (vertexClauses G w).filter
              (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v)) = [] := by
            simpa [e] using vertexClauses_filter_eq_nil_of_not_incident G w e hw'
          rw [hnil]
          simp [hw']
      have hflat :
          (List.finRange G.numVertices).flatMap (fun w =>
            if G.edgeSrc e = w ∨ G.edgeTgt e = w then vertexClauses G w else []) =
          verts.flatMap (vertexClauses G) := by
        unfold verts
        induction List.finRange G.numVertices with
        | nil => rfl
        | cons a t ih =>
            by_cases ha : G.edgeSrc e = a ∨ G.edgeTgt e = a
            · simp [ha, ih]
            · simp [ha, ih]
      have hmain :
          (((List.finRange G.numVertices).flatMap (fun w =>
              (vertexClauses G w).filter
                (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v)))).length) ≤ 8 := by
        have hvertsLen : (verts.flatMap (vertexClauses G)).length = 4 * verts.length := by
          rw [List.length_flatMap]
          have hmap :
              List.map (fun w => (vertexClauses G w).length) verts =
                List.replicate verts.length 4 := by
            apply List.ext_getElem
            · simp
            · intro i hi1 hi2
              have hi : i < verts.length := by simpa using hi1
              rw [List.getElem_map, List.getElem_replicate]
              simpa using vertexClauses_length_of_degree_eq_three G hdeg (verts[i]'hi)
          rw [hmap]
          simp [List.sum_replicate, Nat.mul_comm]
        have hverts : verts.length ≤ 2 := by
          unfold verts
          exact finRange_filter_incident_length_le_two G e
        calc
          (((List.finRange G.numVertices).flatMap (fun w =>
              (vertexClauses G w).filter
                (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v)))).length)
              ≤ ((List.finRange G.numVertices).flatMap (fun w =>
                    if G.edgeSrc e = w ∨ G.edgeTgt e = w then vertexClauses G w else [])).length :=
                hsub.length_le
          _ = (verts.flatMap (vertexClauses G)).length := by simpa [hflat]
          _ = 4 * verts.length := hvertsLen
          _ ≤ 8 := by omega
      exact le_trans hmain (by omega)
    · have hnone :
          ((List.finRange G.numVertices).flatMap (vertexClauses G)).filter
            (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v)) = [] := by
        apply List.eq_nil_iff_forall_not_mem.2
        intro c hc
        have hc' : c ∈ (List.finRange G.numVertices).flatMap (vertexClauses G) :=
          List.mem_of_mem_filter hc
        rcases List.mem_flatMap.1 hc' with ⟨w, hw, hcw⟩
        have hvars := vertexClauses_vars_lt_numEdges G w c hcw
        rcases hvars with ⟨h1, h2, h3⟩
        have hvar : c.var1 = v ∨ c.var2 = v ∨ c.var3 = v := by
          simpa [decide_eq_true_eq] using List.of_mem_filter hc
        rcases hvar with hEq | hEq | hEq
        · exact (not_lt_of_ge (Nat.le_of_not_lt hv)) (hEq ▸ h1)
        · exact (not_lt_of_ge (Nat.le_of_not_lt hv)) (hEq ▸ h2)
        · exact (not_lt_of_ge (Nat.le_of_not_lt hv)) (hEq ▸ h3)
      rw [hnone]
      exact by decide

/-- Tseitin formula on the n-th graph, built concretely -/
noncomputable def tseitinAt (n : ℕ) : TseitinFormula :=
  buildTseitin (highGirthFamily.graph n) (by
    change (cubicGraph (evenUp n) (evenUp_ge6 n) (evenUp_even n)).degree = 3
    rfl)

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
