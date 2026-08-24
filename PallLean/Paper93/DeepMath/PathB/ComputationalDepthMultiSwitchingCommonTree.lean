import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter

/-!
# Common decision-tree carrier for multi-switching

The ordinary simultaneous switching API stores one independent canonical tree per gate and unions
their bad events.  A reusable multi-switching lemma instead needs one common query tree whose leaves
carry the residual state of every gate.  This file introduces that missing representation without
assuming a counting theorem.

`CommonTree n α` is a decision tree with an arbitrary leaf payload.  Its monadic `bind` operation
refines every leaf by another query tree.  `commonRefine` uses this operation to combine a list of
Boolean decision trees into one tree whose reached leaf is exactly the list of all their outputs.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- A query tree with data of type `α` at each leaf. -/
inductive CommonTree (n : ℕ) (α : Type) where
  | leaf : α → CommonTree n α
  | query : Fin n → CommonTree n α → CommonTree n α → CommonTree n α

namespace CommonTree

/-- The payload reached by a complete assignment. -/
def run {n : ℕ} {α : Type} : CommonTree n α → (Fin n → Bool) → α
  | .leaf a, _ => a
  | .query i lo hi, x => if x i then run hi x else run lo x

/-- Maximum number of queries on a root-to-leaf path. -/
def depth {n : ℕ} {α : Type} : CommonTree n α → ℕ
  | .leaf _ => 0
  | .query _ lo hi => max (depth lo) (depth hi) + 1

/-- The single shared branch transcript followed by an assignment. -/
def trace {n : ℕ} {α : Type} : CommonTree n α → (Fin n → Bool) → List Bool
  | .leaf _, _ => []
  | .query i lo hi, x =>
      if x i then true :: trace hi x else false :: trace lo x

/-- Queried coordinates on the branch followed by an assignment. -/
def queryVars {n : ℕ} {α : Type} : CommonTree n α → (Fin n → Bool) → List (Fin n)
  | .leaf _, _ => []
  | .query i lo hi, x =>
      i :: if x i then queryVars hi x else queryVars lo x

/-- Pathwise read-once normalization.  A repeated query already fixed by the current branch is
resolved immediately; a fresh query is retained and recorded in both recursive branch states. -/
def readOnce {n : ℕ} {α : Type} :
    Restriction n → CommonTree n α → CommonTree n α
  | _, .leaf a => .leaf a
  | σ, .query i lo hi =>
      match σ i with
      | some true => readOnce σ hi
      | some false => readOnce σ lo
      | none => .query i (readOnce (fixVar σ i false) lo)
          (readOnce (fixVar σ i true) hi)

/-- Truncate the read-once normalization after at most `budget` fresh queries and store the
accumulated residual restriction at every leaf.  This is the common trunk whose failure to have
shallow residual gates must supply the exact bad path used by the switching encoder. -/
def prefixEndpoints {n : ℕ} {α : Type} :
    Restriction n → CommonTree n α → ℕ → CommonTree n (Restriction n)
  | σ, .leaf _, _ => .leaf σ
  | σ, .query _ _ _, 0 => .leaf σ
  | σ, .query i lo hi, budget + 1 =>
      match σ i with
      | some true => prefixEndpoints σ hi (budget + 1)
      | some false => prefixEndpoints σ lo (budget + 1)
      | none => .query i
          (prefixEndpoints (fixVar σ i false) lo budget)
          (prefixEndpoints (fixVar σ i true) hi budget)

/-- The canonical prefix trunk never exceeds its query budget. -/
theorem depth_prefixEndpoints_le {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) :
    depth (prefixEndpoints σ t budget) ≤ budget := by
  induction t generalizing σ budget with
  | leaf a => simp [prefixEndpoints, depth]
  | query i lo hi ihlo ihhi =>
      cases budget with
      | zero => simp [prefixEndpoints, depth]
      | succ budget =>
          cases hσ : σ i with
          | none =>
              simp only [prefixEndpoints, hσ, depth]
              exact Nat.succ_le_succ (max_le (ihlo _ _) (ihhi _ _))
          | some b =>
              cases b <;> simp only [prefixEndpoints, hσ]
              · exact ihlo _ _
              · exact ihhi _ _

/-- The prefix trunk follows exactly the first `budget` bits of the normalized common path. -/
theorem trace_prefixEndpoints {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool) :
    trace (prefixEndpoints σ t budget) x = (trace (readOnce σ t) x).take budget := by
  induction t generalizing σ budget with
  | leaf a => simp [prefixEndpoints, readOnce, trace]
  | query i lo hi ihlo ihhi =>
      cases budget with
      | zero => simp [prefixEndpoints, trace]
      | succ budget =>
          cases hσ : σ i with
          | none =>
              by_cases hx : x i
              · simp [prefixEndpoints, readOnce, trace, hσ, hx, ihhi]
              · simp [prefixEndpoints, readOnce, trace, hσ, hx, ihlo]
          | some b =>
              cases b <;> simp [prefixEndpoints, readOnce, hσ, ihlo, ihhi]

/-- The prefix trunk queries exactly the first `budget` coordinates of the normalized common path. -/
theorem queryVars_prefixEndpoints {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool) :
    queryVars (prefixEndpoints σ t budget) x =
      (queryVars (readOnce σ t) x).take budget := by
  induction t generalizing σ budget with
  | leaf a => simp [prefixEndpoints, readOnce, queryVars]
  | query i lo hi ihlo ihhi =>
      cases budget with
      | zero => simp [prefixEndpoints, queryVars]
      | succ budget =>
          cases hσ : σ i with
          | none =>
              by_cases hx : x i
              · simp [prefixEndpoints, readOnce, queryVars, hσ, hx, ihhi]
              · simp [prefixEndpoints, readOnce, queryVars, hσ, hx, ihlo]
          | some b =>
              cases b <;> simp [prefixEndpoints, readOnce, hσ, ihlo, ihhi]

/-- The payload stored at a prefix leaf is exactly the root with the queried prefix fixed according
to the followed assignment. -/
theorem run_prefixEndpoints {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool) :
    run (prefixEndpoints σ t budget) x =
      fixOn σ (queryVars (prefixEndpoints σ t budget) x).toFinset x := by
  induction t generalizing σ budget with
  | leaf a =>
      simp only [prefixEndpoints, run, queryVars, List.toFinset_nil]
      funext j
      simp [fixOn]
  | query i lo hi ihlo ihhi =>
      cases budget with
      | zero =>
          simp only [prefixEndpoints, run, queryVars, List.toFinset_nil]
          funext j
          simp [fixOn]
      | succ budget =>
          cases hσ : σ i with
          | some b =>
              cases b <;> simp [prefixEndpoints, hσ, ihlo, ihhi]
          | none =>
              by_cases hx : x i
              · simp only [prefixEndpoints, hσ, run, hx, if_true, queryVars,
                  List.toFinset_cons, ihhi]
                funext j
                by_cases hji : j = i
                · subst j; simp [fixOn, fixVar, hx]
                · simp [fixOn, fixVar, hji]
              · simp only [prefixEndpoints, hσ, run, hx, Bool.false_eq_true, if_false,
                  queryVars, List.toFinset_cons, ihlo]
                funext j
                by_cases hji : j = i
                · subst j; simp [fixOn, fixVar, hx]
                · simp [fixOn, fixVar, hji]

/-- Read-once normalization preserves execution on every assignment extending the accumulated
branch restriction. -/
theorem run_readOnce {n : ℕ} {α : Type} (σ : Restriction n) (t : CommonTree n α)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    run (readOnce σ t) x = run t x := by
  induction t generalizing σ with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      cases hσ : σ i with
      | none =>
          by_cases hx : x i
          · simp only [readOnce, hσ, run, hx, if_true]
            exact ihhi _ (extends_fixVar hext hx)
          · simp only [readOnce, hσ, run, hx]
            exact ihlo _ (extends_fixVar hext (Bool.eq_false_of_not_eq_true hx))
      | some b =>
          have hxb : x i = b := hext i b hσ
          cases b <;> simp [readOnce, hσ, run, hxb, ihlo, ihhi, hext]

/-- A coordinate already fixed in the accumulated branch state never appears later on the
normalized execution path. -/
theorem not_mem_queryVars_readOnce_of_fixed {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) {j : Fin n} (hj : σ j ≠ none) :
    j ∉ queryVars (readOnce σ t) x := by
  induction t generalizing σ with
  | leaf a => simp [readOnce, queryVars]
  | query i lo hi ihlo ihhi =>
      cases hσ : σ i with
      | some b =>
          cases b <;> simp only [readOnce, hσ]
          · exact ihlo σ hext hj
          · exact ihhi σ hext hj
      | none =>
          have hji : j ≠ i := by
            intro h; subst h; exact hj hσ
          by_cases hx : x i
          · simp only [readOnce, hσ, queryVars, hx, if_true, List.mem_cons]
            refine fun h => h.elim hji ?_
            have hjfix : fixVar σ i true j ≠ none := by
              rw [fixVar, Function.update_of_ne hji]
              exact hj
            exact ihhi (fixVar σ i true) (extends_fixVar hext hx) hjfix
          · simp only [readOnce, hσ, queryVars, hx, Bool.false_eq_true,
              List.mem_cons]
            refine fun h => h.elim hji ?_
            have hjfix : fixVar σ i false j ≠ none := by
              rw [fixVar, Function.update_of_ne hji]
              exact hj
            exact ihlo (fixVar σ i false)
              (extends_fixVar hext (Bool.eq_false_of_not_eq_true hx)) hjfix

/-- Every normalized execution path queries each coordinate at most once. -/
theorem queryVars_readOnce_nodup {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    (queryVars (readOnce σ t) x).Nodup := by
  induction t generalizing σ with
  | leaf a => simp [readOnce, queryVars]
  | query i lo hi ihlo ihhi =>
      cases hσ : σ i with
      | some b =>
          cases b <;> simp only [readOnce, hσ]
          · exact ihlo σ hext
          · exact ihhi σ hext
      | none =>
          by_cases hx : x i
          · simp only [readOnce, hσ, queryVars, hx, if_true, List.nodup_cons]
            exact ⟨not_mem_queryVars_readOnce_of_fixed (fixVar σ i true) hi x
              (extends_fixVar hext hx) (by simp [fixVar]),
              ihhi _ (extends_fixVar hext hx)⟩
          · simp only [readOnce, hσ, queryVars, hx, List.nodup_cons]
            have hext' := extends_fixVar hext (Bool.eq_false_of_not_eq_true hx)
            exact ⟨not_mem_queryVars_readOnce_of_fixed (fixVar σ i false) lo x hext'
              (by simp [fixVar]), ihlo _ hext'⟩

/-- Normalization only removes repeated/fixed queries; every retained query occurred on the
original execution path. -/
theorem mem_queryVars_of_mem_readOnce {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) {j : Fin n}
    (hj : j ∈ queryVars (readOnce σ t) x) : j ∈ queryVars t x := by
  induction t generalizing σ with
  | leaf a => simp [readOnce, queryVars] at hj
  | query i lo hi ihlo ihhi =>
      cases hσ : σ i with
      | some b =>
          have hxb : x i = b := hext i b hσ
          cases b
          · simp only [readOnce, hσ] at hj
            simp only [queryVars, hxb, Bool.false_eq_true, List.mem_cons]
            exact Or.inr (ihlo σ hext hj)
          · simp only [readOnce, hσ] at hj
            simp only [queryVars, hxb, if_true, List.mem_cons]
            exact Or.inr (ihhi σ hext hj)
      | none =>
          by_cases hx : x i
          · simp only [readOnce, hσ, queryVars, hx, if_true, List.mem_cons] at hj ⊢
            exact hj.imp_right (ihhi _ (extends_fixVar hext hx))
          · simp only [readOnce, hσ, queryVars, hx, Bool.false_eq_true,
              List.mem_cons] at hj ⊢
            exact hj.imp_right (ihlo _
              (extends_fixVar hext (Bool.eq_false_of_not_eq_true hx)))

/-- Conversely, every originally queried coordinate that was free at the root survives somewhere
on the read-once path.  Repeated occurrences may disappear, but the queried-variable set does not. -/
theorem mem_queryVars_readOnce_of_mem_of_free {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) {j : Fin n}
    (hjfree : j ∈ freeVars σ) (hj : j ∈ queryVars t x) :
    j ∈ queryVars (readOnce σ t) x := by
  induction t generalizing σ with
  | leaf a => simp [queryVars] at hj
  | query i lo hi ihlo ihhi =>
      cases hσ : σ i with
      | some b =>
          have hji : j ≠ i := by
            intro h; subst h
            rw [mem_freeVars, hσ] at hjfree
            simp at hjfree
          have hxb : x i = b := hext i b hσ
          cases b
          · simp only [readOnce, hσ]
            simp only [queryVars, hxb, Bool.false_eq_true, List.mem_cons] at hj
            exact ihlo σ hext hjfree (hj.resolve_left hji)
          · simp only [readOnce, hσ]
            simp only [queryVars, hxb, if_true, List.mem_cons] at hj
            exact ihhi σ hext hjfree (hj.resolve_left hji)
      | none =>
          by_cases hx : x i
          · simp only [readOnce, hσ, queryVars, hx, if_true, List.mem_cons] at hj ⊢
            rcases hj with rfl | hj
            · exact Or.inl rfl
            · by_cases hji : j = i
              · exact Or.inl hji
              · refine Or.inr (ihhi (fixVar σ i true) (extends_fixVar hext hx) ?_ hj)
                rw [mem_freeVars, fixVar, Function.update_of_ne hji]
                exact mem_freeVars.mp hjfree
          · simp only [readOnce, hσ, queryVars, hx, Bool.false_eq_true,
              List.mem_cons] at hj ⊢
            rcases hj with rfl | hj
            · exact Or.inl rfl
            · by_cases hji : j = i
              · exact Or.inl hji
              · refine Or.inr (ihlo (fixVar σ i false)
                  (extends_fixVar hext (Bool.eq_false_of_not_eq_true hx)) ?_ hj)
                rw [mem_freeVars, fixVar, Function.update_of_ne hji]
                exact mem_freeVars.mp hjfree

/-- Read-once normalization preserves the queried-variable set whenever the original execution
queries only coordinates free at the root. -/
theorem queryVars_readOnce_toFinset_eq {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x)
    (hfree : ∀ j ∈ queryVars t x, j ∈ freeVars σ) :
    (queryVars (readOnce σ t) x).toFinset = (queryVars t x).toFinset := by
  ext j
  simp only [List.mem_toFinset]
  constructor
  · exact mem_queryVars_of_mem_readOnce σ t x hext
  · intro hj
    exact mem_queryVars_readOnce_of_mem_of_free σ t x hext (hfree j hj) hj

/-- Bit transcripts and queried-coordinate transcripts have identical lengths. -/
theorem trace_length_eq_queryVars_length {n : ℕ} {α : Type}
    (t : CommonTree n α) (x : Fin n → Bool) :
    (trace t x).length = (queryVars t x).length := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      by_cases hx : x i <;> simp [trace, queryVars, hx, ihlo, ihhi]

/-- A normalized common path has at most one query per ambient coordinate. -/
theorem trace_readOnce_length_le_ambient {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    (trace (readOnce σ t) x).length ≤ n := by
  rw [trace_length_eq_queryVars_length]
  simpa using (queryVars_readOnce_nodup σ t x hext).length_le_card

/-- Every coordinate retained on a normalized path was free in the starting restriction. -/
theorem mem_queryVars_readOnce_freeVars {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) {j : Fin n}
    (hj : j ∈ queryVars (readOnce σ t) x) : j ∈ freeVars σ := by
  rw [mem_freeVars]
  by_contra hnone
  exact not_mem_queryVars_readOnce_of_fixed σ t x hext hnone hj

/-- Every coordinate queried by a prefix trunk was live at its root. -/
theorem queryVars_prefixEndpoints_subset_free {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    (queryVars (prefixEndpoints σ t budget) x).toFinset ⊆ freeVars σ := by
  intro v hv
  rw [queryVars_prefixEndpoints] at hv
  exact mem_queryVars_readOnce_freeVars σ t x hext
    (List.mem_of_mem_take (List.mem_toFinset.mp hv))

/-- The residual restriction stored at a prefix leaf is still extended by the followed full
assignment. -/
theorem run_prefixEndpoints_extends {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    Rung4Restriction.Extends (run (prefixEndpoints σ t budget) x) x := by
  rw [run_prefixEndpoints]
  intro v b hv
  simp only [fixOn] at hv
  split at hv
  · exact Option.some.inj hv
  · exact hext v b hv

/-- The normalized shared transcript is bounded by the current live dimension, not the ambient
dimension and not the sum of the independent gate depths. -/
theorem trace_readOnce_length_le_stars {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    (trace (readOnce σ t) x).length ≤ stars σ := by
  rw [trace_length_eq_queryVars_length]
  have hnd := queryVars_readOnce_nodup σ t x hext
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro j hj
  exact mem_queryVars_readOnce_freeVars σ t x hext (List.mem_toFinset.mp hj)

/-- Replay a complete branch transcript, rejecting truncated or overlong transcripts. -/
def replay {n : ℕ} {α : Type} : CommonTree n α → List Bool → Option α
  | .leaf a, [] => some a
  | .leaf _, _ :: _ => none
  | .query _ _ _, [] => none
  | .query _ lo hi, b :: bs => if b then replay hi bs else replay lo bs

/-- Every actual transcript fits within the common tree's maximum depth. -/
theorem trace_length_le_depth {n : ℕ} {α : Type} (t : CommonTree n α)
    (x : Fin n → Bool) : (trace t x).length ≤ depth t := by
  induction t with
  | leaf a => simp [trace, depth]
  | query i lo hi ihlo ihhi =>
      by_cases h : x i
      · simp only [trace, h, if_true, List.length_cons, depth]
        exact Nat.succ_le_succ (ihhi.trans (Nat.le_max_right _ _))
      · simp only [trace, h, depth]
        exact Nat.succ_le_succ (ihlo.trans (Nat.le_max_left _ _))

/-- Replaying the transcript generated by an assignment reaches its exact payload. -/
theorem replay_trace {n : ℕ} {α : Type} (t : CommonTree n α)
    (x : Fin n → Bool) : replay t (trace t x) = some (run t x) := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      by_cases h : x i <;> simp [trace, replay, run, h, ihlo, ihhi]

/-- One shared transcript determines the entire structured leaf payload. -/
theorem run_eq_of_trace_eq {n : ℕ} {α : Type} (t : CommonTree n α)
    {x y : Fin n → Bool} (h : trace t x = trace t y) : run t x = run t y := by
  have hs : some (run t x) = some (run t y) := by
    rw [← replay_trace t x, ← replay_trace t y, h]
  exact Option.some.inj hs

/-- A depth-bounded common-path label.  It contains one shared bit string, not one string per gate. -/
def PathLabel (d : ℕ) := {bs : List Bool // bs.length ≤ d}

/-- A finite representation of a path of length at most `d`: its actual length and a `d`-bit
buffer.  Bits beyond the recorded length are ignored. -/
abbrev FinitePathLabel (d : ℕ) := Fin (d + 1) × (Fin d → Bool)

/-- The exact size of the finite common-path label space. -/
theorem card_finitePathLabel (d : ℕ) :
    Fintype.card (FinitePathLabel d) = (d + 1) * 2 ^ d := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- Store a bounded variable-length transcript in the finite label space. -/
def PathLabel.toFinite {d : ℕ} (p : PathLabel d) : FinitePathLabel d :=
  (⟨p.1.length, Nat.lt_succ_of_le p.2⟩, fun i => p.1.getD i.1 false)

/-- Length plus the padded bit buffer loses no bounded transcript information. -/
theorem PathLabel.toFinite_injective {d : ℕ} :
    Function.Injective (@PathLabel.toFinite d) := by
  intro p q h
  apply Subtype.ext
  apply List.ext_getElem (congrArg (fun z => z.1.1) h)
  intro i hip hiq
  have hfun : (fun j : Fin d => p.1.getD j.1 false) =
      (fun j : Fin d => q.1.getD j.1 false) := congrArg Prod.snd h
  have hi : i < d := hip.trans_le p.2
  have hbit := congrFun hfun ⟨i, hi⟩
  rw [List.getD_eq_getElem p.1 false hip, List.getD_eq_getElem q.1 false hiq] at hbit
  exact hbit

/-- A finite shared transcript label parameterized by the actual live dimension. -/
def liveFinitePathLabel {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) : FinitePathLabel (stars σ) :=
  PathLabel.toFinite ⟨trace (readOnce σ t) x,
    trace_readOnce_length_le_stars σ t x hext⟩

/-- The genuinely fresh coordinates queried by a common path. -/
def pathVars {n : ℕ} {α : Type} (σ : Restriction n) (t : CommonTree n α)
    (x : Fin n → Bool) : Finset (Fin n) :=
  (queryVars (readOnce σ t) x).toFinset

/-- The residual restriction reached by fixing exactly the fresh common-path coordinates. -/
def pathEndpoint {n : ℕ} {α : Type} (σ : Restriction n) (t : CommonTree n α)
    (x : Fin n → Bool) : Restriction n :=
  fixOn σ (pathVars σ t x) x

/-- The first `budget` genuinely fresh coordinates of a normalized common execution. -/
def prefixVars {n : ℕ} {α : Type} (σ : Restriction n) (t : CommonTree n α)
    (budget : ℕ) (x : Fin n → Bool) : Finset (Fin n) :=
  (queryVars (prefixEndpoints σ t budget) x).toFinset

/-- The restriction reached after the first `budget` fresh common queries. -/
def prefixEndpoint {n : ℕ} {α : Type} (σ : Restriction n) (t : CommonTree n α)
    (budget : ℕ) (x : Fin n → Bool) : Restriction n :=
  run (prefixEndpoints σ t budget) x

/-- The prefix-tree payload is exactly the root with its prefix variables fixed. -/
theorem prefixEndpoint_eq_fixOn {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool) :
    prefixEndpoint σ t budget x = fixOn σ (prefixVars σ t budget x) x := by
  exact run_prefixEndpoints σ t budget x

/-- Prefix variables inherit read-once uniqueness. -/
theorem queryVars_prefixEndpoints_nodup {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    (queryVars (prefixEndpoints σ t budget) x).Nodup := by
  rw [queryVars_prefixEndpoints]
  exact (queryVars_readOnce_nodup σ t x hext).take

/-- If the normalized path has at least `budget` queries, the prefix contains exactly `budget`
distinct variables. -/
theorem prefixVars_card_eq_of_le_trace {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x)
    (hlong : budget ≤ (trace (readOnce σ t) x).length) :
    (prefixVars σ t budget x).card = budget := by
  rw [prefixVars, List.toFinset_card_of_nodup
    (queryVars_prefixEndpoints_nodup σ t budget x hext), queryVars_prefixEndpoints]
  apply List.length_take_of_le
  simpa [trace_length_eq_queryVars_length] using hlong

/-- Every prefix coordinate was live at the root. -/
theorem prefixVars_subset_freeVars {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    prefixVars σ t budget x ⊆ freeVars σ :=
  queryVars_prefixEndpoints_subset_free σ t budget x hext

/-- Prefix fixing removes exactly the prefix variables from the live set. -/
theorem freeVars_prefixEndpoint {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool) :
    freeVars (prefixEndpoint σ t budget x) =
      freeVars σ \ prefixVars σ t budget x := by
  rw [prefixEndpoint_eq_fixOn]
  ext v
  simp only [mem_freeVars, fixOn, Finset.mem_sdiff]
  by_cases hv : v ∈ prefixVars σ t budget x <;> simp [hv]

/-- A long-enough path from a `K`-live root lands in the exact `(K-budget)` shell after its prefix. -/
theorem stars_prefixEndpoint {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    stars (prefixEndpoint σ t budget x) =
      stars σ - (prefixVars σ t budget x).card := by
  rw [stars, freeVars_prefixEndpoint,
    Finset.card_sdiff_of_subset (prefixVars_subset_freeVars σ t budget x hext), stars]

/-- Re-freeing the prefix variables recovers the root restriction. -/
theorem freeOn_prefixEndpoint {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (budget : ℕ) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    freeOn (prefixEndpoint σ t budget x) (prefixVars σ t budget x) = σ := by
  rw [prefixEndpoint_eq_fixOn]
  exact freeOn_fixOn σ (prefixVars σ t budget x) x
    (prefixVars_subset_freeVars σ t budget x hext)

/-- Prefix endpoint plus its selected variables is an injective encoding of the root. -/
theorem prefixEndpoint_inj_of_prefixVars_eq {n : ℕ} {α β : Type}
    {ρ σ : Restriction n} {tρ : CommonTree n α} {tσ : CommonTree n β}
    {budget : ℕ} {x y : Fin n → Bool}
    (hx : Rung4Restriction.Extends ρ x) (hy : Rung4Restriction.Extends σ y)
    (hE : prefixEndpoint ρ tρ budget x = prefixEndpoint σ tσ budget y)
    (hV : prefixVars ρ tρ budget x = prefixVars σ tσ budget y) : ρ = σ := by
  calc
    ρ = freeOn (prefixEndpoint ρ tρ budget x) (prefixVars ρ tρ budget x) :=
      (freeOn_prefixEndpoint ρ tρ budget x hx).symm
    _ = freeOn (prefixEndpoint σ tσ budget y) (prefixVars σ tσ budget y) := by
      rw [hE, hV]
    _ = σ := freeOn_prefixEndpoint σ tσ budget y hy

/-- Fixing the fresh common-path coordinates removes exactly those coordinates from the live set. -/
theorem freeVars_pathEndpoint {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool) :
    freeVars (pathEndpoint σ t x) = freeVars σ \ pathVars σ t x := by
  ext v
  simp only [pathEndpoint, mem_freeVars, fixOn, Finset.mem_sdiff]
  by_cases hv : v ∈ pathVars σ t x
  · simp [hv]
  · simp [hv]

/-- Every coordinate charged to the common path was live at its root. -/
theorem pathVars_subset_freeVars {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    pathVars σ t x ⊆ freeVars σ := by
  intro v hv
  exact mem_queryVars_readOnce_freeVars σ t x hext (List.mem_toFinset.mp hv)

/-- An exact length-`d` fresh path from a `K`-live root lands in the `(K-d)`-live shell. -/
theorem stars_pathEndpoint {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    stars (pathEndpoint σ t x) = stars σ - (pathVars σ t x).card := by
  rw [stars, freeVars_pathEndpoint,
    Finset.card_sdiff_of_subset (pathVars_subset_freeVars σ t x hext), stars]

/-- Re-freeing the common path exactly recovers its root restriction. -/
theorem freeOn_pathEndpoint {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    freeOn (pathEndpoint σ t x) (pathVars σ t x) = σ := by
  exact freeOn_fixOn σ (pathVars σ t x) x (pathVars_subset_freeVars σ t x hext)

/-- Endpoint plus the selected common-path coordinates is an injective encoding of the root.
This removes endpoint injectivity as an independent assumption: the remaining semantic obligation
for a compact witness is precisely to recover `pathVars` from its finite label. -/
theorem pathEndpoint_inj_of_pathVars_eq {n : ℕ} {α β : Type}
    {ρ σ : Restriction n} {tρ : CommonTree n α} {tσ : CommonTree n β}
    {x y : Fin n → Bool}
    (hx : Rung4Restriction.Extends ρ x) (hy : Rung4Restriction.Extends σ y)
    (hE : pathEndpoint ρ tρ x = pathEndpoint σ tσ y)
    (hV : pathVars ρ tρ x = pathVars σ tσ y) : ρ = σ := by
  calc
    ρ = freeOn (pathEndpoint ρ tρ x) (pathVars ρ tρ x) :=
      (freeOn_pathEndpoint ρ tρ x hx).symm
    _ = freeOn (pathEndpoint σ tσ y) (pathVars σ tσ y) := by rw [hE, hV]
    _ = σ := freeOn_pathEndpoint σ tσ y hy

/-- Exact size of the live-dimension shared transcript space. -/
theorem card_liveFinitePathLabel {n : ℕ} (σ : Restriction n) :
    Fintype.card (FinitePathLabel (stars σ)) =
      (stars σ + 1) * 2 ^ stars σ :=
  card_finitePathLabel _

/-- Equal live-dimension labels recover the complete normalized leaf payload. -/
theorem run_readOnce_eq_of_liveFinitePathLabel_eq {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) {x y : Fin n → Bool}
    (hx : Rung4Restriction.Extends σ x) (hy : Rung4Restriction.Extends σ y)
    (hlabel : liveFinitePathLabel σ t x hx = liveFinitePathLabel σ t y hy) :
    run (readOnce σ t) x = run (readOnce σ t) y := by
  apply run_eq_of_trace_eq
  exact congrArg Subtype.val (PathLabel.toFinite_injective hlabel)

/-- Package an assignment's actual branch transcript as a bounded common-path label. -/
def pathLabel {n : ℕ} {α : Type} (t : CommonTree n α) (x : Fin n → Bool) :
    PathLabel (depth t) :=
  ⟨trace t x, trace_length_le_depth t x⟩

/-- The finite common-path label generated by an assignment. -/
def finitePathLabel {n : ℕ} {α : Type} (t : CommonTree n α) (x : Fin n → Bool) :
    FinitePathLabel (depth t) :=
  (pathLabel t x).toFinite

/-- Equality of common-path labels recovers the complete reached payload. -/
theorem run_eq_of_pathLabel_eq {n : ℕ} {α : Type} (t : CommonTree n α)
    {x y : Fin n → Bool} (h : pathLabel t x = pathLabel t y) : run t x = run t y := by
  apply run_eq_of_trace_eq t
  exact congrArg Subtype.val h

/-- The explicitly finite label still determines the complete reached payload. -/
theorem run_eq_of_finitePathLabel_eq {n : ℕ} {α : Type} (t : CommonTree n α)
    {x y : Fin n → Bool} (h : finitePathLabel t x = finitePathLabel t y) :
    run t x = run t y := by
  apply run_eq_of_pathLabel_eq t
  exact PathLabel.toFinite_injective h

/-- Replace every leaf by a further common query tree. -/
def bind {n : ℕ} {α β : Type} : CommonTree n α → (α → CommonTree n β) → CommonTree n β
  | .leaf a, f => f a
  | .query i lo hi, f => .query i (bind lo f) (bind hi f)

/-- Relabel every query coordinate and transform every leaf payload.  This is the structural
operation used to place a local common tree on an injectively embedded block of ambient
coordinates. -/
def reindex {n m : ℕ} {α β : Type} (e : Fin n → Fin m) (f : α → β) :
    CommonTree n α → CommonTree m β
  | .leaf a => .leaf (f a)
  | .query i lo hi => .query (e i) (reindex e f lo) (reindex e f hi)

/-- Coordinate relabelling preserves the exact maximum query depth. -/
theorem depth_reindex {n m : ℕ} {α β : Type} (e : Fin n → Fin m) (f : α → β)
    (t : CommonTree n α) :
    depth (reindex e f t) = depth t := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi => simp [reindex, depth, ihlo, ihhi]

/-- Running a relabelled tree is the same as pulling the ambient assignment back along the
coordinate embedding and then transforming the reached local payload. -/
theorem run_reindex {n m : ℕ} {α β : Type} (e : Fin n → Fin m) (f : α → β)
    (t : CommonTree n α) (x : Fin m → Bool) :
    run (reindex e f t) x = f (run t (fun i => x (e i))) := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      by_cases h : x (e i) <;> simp [reindex, run, h, ihlo, ihhi]

/-- Replacing every leaf by a tree of depth at most `d` adds at most `d` to the outer tree's
depth.  In particular, sequentially composing disjoint local trunks pays the sum of their depth
bounds. -/
theorem depth_bind_le {n : ℕ} {α β : Type} (t : CommonTree n α)
    (f : α → CommonTree n β) (d : ℕ) (hf : ∀ a, depth (f a) ≤ d) :
    depth (bind t f) ≤ depth t + d := by
  induction t with
  | leaf a => simpa [bind, depth] using hf a
  | query i lo hi ihlo ihhi =>
      simp only [bind, depth]
      have hlo := ihlo
      have hhi := ihhi
      omega

@[simp] theorem run_leaf {n : ℕ} {α : Type} (a : α) (x : Fin n → Bool) :
    run (.leaf a : CommonTree n α) x = a := rfl

@[simp] theorem run_query {n : ℕ} {α : Type} (i : Fin n)
    (lo hi : CommonTree n α) (x : Fin n → Bool) :
    run (.query i lo hi) x = if x i then run hi x else run lo x := rfl

/-- Executing a refined tree first reaches an old leaf and then executes its replacement. -/
theorem run_bind {n : ℕ} {α β : Type} (t : CommonTree n α)
    (f : α → CommonTree n β) (x : Fin n → Bool) :
    run (bind t f) x = run (f (run t x)) x := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      simp only [bind, run]
      by_cases h : x i <;> simp [h, ihlo, ihhi]

/-- Refinement concatenates the transcript of the outer tree with that of the reached
replacement tree.  This is the canonical source of common-family segment boundaries. -/
theorem trace_bind {n : ℕ} {α β : Type} (t : CommonTree n α)
    (f : α → CommonTree n β) (x : Fin n → Bool) :
    trace (bind t f) x = trace t x ++ trace (f (run t x)) x := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      by_cases h : x i <;> simp [bind, trace, run, h, ihlo, ihhi]

/-- Query-coordinate paths obey the same concatenation law as bit transcripts. -/
theorem queryVars_bind {n : ℕ} {α β : Type} (t : CommonTree n α)
    (f : α → CommonTree n β) (x : Fin n → Bool) :
    queryVars (bind t f) x =
      queryVars t x ++ queryVars (f (run t x)) x := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      by_cases h : x i <;> simp [bind, queryVars, run, h, ihlo, ihhi]

/-- Regard an ordinary Boolean decision tree as a common tree with Boolean leaves. -/
def ofBool {n : ℕ} : BoolDecisionTree n → CommonTree n Bool
  | .leaf b => .leaf b
  | .query i lo hi => .query i (ofBool lo) (ofBool hi)

theorem run_ofBool {n : ℕ} (t : BoolDecisionTree n) (x : Fin n → Bool) :
    run (ofBool t) x = t.eval x := by
  induction t with
  | leaf b => rfl
  | query i lo hi ihlo ihhi =>
      simp only [ofBool, run, BoolDecisionTree.eval]
      by_cases h : x i <;> simp [h, ihlo, ihhi]

/-- Every coordinate queried on one execution path belongs to the tree's global queried set. -/
theorem queryVars_ofBool_toFinset_subset_queriedVars {n : ℕ}
    (t : BoolDecisionTree n) (x : Fin n → Bool) :
    (queryVars (ofBool t) x).toFinset ⊆ Depth3.queriedVars t := by
  induction t with
  | leaf b => simp [ofBool, queryVars, Depth3.queriedVars]
  | query i lo hi ihlo ihhi =>
      by_cases hx : x i
      · simp only [ofBool, queryVars, hx, if_true, List.toFinset_cons,
          Depth3.queriedVars]
        exact Finset.insert_subset_iff.mpr
          ⟨Finset.mem_insert_self _ _, fun _ hv =>
            Finset.mem_insert_of_mem (Finset.mem_union_right _ (ihhi hv))⟩
      · simp only [ofBool, queryVars, hx, Bool.false_eq_true, List.toFinset_cons,
          Depth3.queriedVars]
        exact Finset.insert_subset_iff.mpr
          ⟨Finset.mem_insert_self _ _, fun _ hv =>
            Finset.mem_insert_of_mem (Finset.mem_union_left _ (ihlo hv))⟩

/-- Sequential common refinement of a finite family.  The payload order matches the input list. -/
def commonRefine {n : ℕ} : List (BoolDecisionTree n) → CommonTree n (List Bool)
  | [] => .leaf []
  | t :: ts => bind (ofBool t) fun b =>
      bind (commonRefine ts) fun bs => .leaf (b :: bs)

/-- The common tree records every member tree's value at the same assignment. -/
theorem run_commonRefine {n : ℕ} (ts : List (BoolDecisionTree n)) (x : Fin n → Bool) :
    run (commonRefine ts) x = ts.map (fun t => t.eval x) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [commonRefine, run_bind, run_ofBool, run_leaf, List.map_cons]
      rw [ih]

/-- The common refinement transcript is canonically partitioned into the ordered transcript
segments of its member trees. -/
theorem trace_commonRefine {n : ℕ} (ts : List (BoolDecisionTree n))
    (x : Fin n → Bool) :
    trace (commonRefine ts) x =
      (ts.map fun t => trace (ofBool t) x).flatten := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [commonRefine, trace_bind, run_ofBool,
        List.map_cons, List.flatten_cons, trace]
      rw [ih]
      simp

/-- The raw family query-coordinate path is the ordered flattening of its gate segments. -/
theorem queryVars_commonRefine {n : ℕ} (ts : List (BoolDecisionTree n))
    (x : Fin n → Bool) :
    queryVars (commonRefine ts) x =
      (ts.map fun t => queryVars (ofBool t) x).flatten := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [commonRefine, queryVars_bind, run_ofBool,
        List.map_cons, List.flatten_cons, queryVars]
      rw [ih]
      simp

/-- Consequently, common-path length is the sum of its real per-tree segment lengths. -/
theorem trace_commonRefine_length {n : ℕ} (ts : List (BoolDecisionTree n))
    (x : Fin n → Bool) :
    (trace (commonRefine ts) x).length =
      (ts.map fun t => (trace (ofBool t) x).length).sum := by
  rw [trace_commonRefine, List.length_flatten]
  rw [List.map_map]
  simp only [Function.comp_def]

/-- Indexed-family form used by padded bottom-gate enumerations. -/
def commonRefineFin {n G : ℕ} (trees : Fin G → BoolDecisionTree n) :
    CommonTree n (Fin G → Bool) :=
  bind (commonRefine (List.ofFn trees)) fun values =>
    .leaf fun g => values.getD g.1 false

theorem run_commonRefineFin {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) (g : Fin G) :
    run (commonRefineFin trees) x g = (trees g).eval x := by
  simp only [commonRefineFin, run_bind, run_leaf, run_commonRefine]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The indexed common refinement has the same path as its underlying ordered list refinement;
the final payload-conversion leaf introduces no queries. -/
theorem trace_commonRefineFin {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) :
    trace (commonRefineFin trees) x = trace (commonRefine (List.ofFn trees)) x := by
  rw [commonRefineFin, trace_bind]
  simp only [trace, List.append_nil]

/-- Indexed-family form of the raw gate-segment query decomposition. -/
theorem queryVars_commonRefineFin {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) :
    queryVars (commonRefineFin trees) x =
      ((List.ofFn trees).map fun t => queryVars (ofBool t) x).flatten := by
  rw [commonRefineFin, queryVars_bind]
  simp only [queryVars, List.append_nil, queryVars_commonRefine]

/-- Exact indexed-family segment-length formula. -/
theorem trace_commonRefineFin_length {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) :
    (trace (commonRefineFin trees) x).length =
      ((List.ofFn trees).map fun t => (trace (ofBool t) x).length).sum := by
  rw [trace_commonRefineFin, trace_commonRefine_length]

end CommonTree

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- The exact common refinement of every canonical bottom-gate tree. -/
def canonicalFamilyTree {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) : CommonTree n (Fin G → Bool) :=
  CommonTree.commonRefineFin fun g => canonicalDT (gates g) fuel σ

/-- Read-once normalization of the genuine canonical family tree, initialized with its base
restriction. -/
def readOnceCanonicalFamilyTree {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) : CommonTree n (Fin G → Bool) :=
  CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)

/-- For canonical gate families, read-once normalization changes only multiplicity/order: its
queried set is exactly the set of variables appearing on the concatenated raw gate paths. -/
theorem pathVars_canonicalFamily_eq_raw {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    CommonTree.pathVars σ (canonicalFamilyTree gates fuel σ) x =
      (CommonTree.queryVars (canonicalFamilyTree gates fuel σ) x).toFinset := by
  apply CommonTree.queryVars_readOnce_toFinset_eq σ _ x hext
  intro j hj
  rw [canonicalFamilyTree, CommonTree.queryVars_commonRefineFin] at hj
  obtain ⟨segment, hsegment, hjsegment⟩ := List.mem_flatten.mp hj
  obtain ⟨tree, htree, rfl⟩ := List.mem_map.mp hsegment
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp htree
  apply canonicalDT_queriedVars_subset_free (gates g) fuel σ
  exact CommonTree.queryVars_ofBool_toFinset_subset_queriedVars
    (canonicalDT (gates g) fuel σ) x (List.mem_toFinset.mpr hjsegment)

/-- One common-tree execution simultaneously returns every canonical gate value. -/
theorem run_canonicalFamilyTree {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) (g : Fin G) :
    CommonTree.run (canonicalFamilyTree gates fuel σ) x g =
      (canonicalDT (gates g) fuel σ).eval x :=
  CommonTree.run_commonRefineFin _ x g

/-- With sufficient fuel, the common leaf payload is the vector of genuine DNF values on every
assignment extending the base restriction. -/
theorem run_canonicalFamilyTree_eq_dnf {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hstars : stars σ ≤ fuel) (hext : Rung4Restriction.Extends σ x)
    (g : Fin G) :
    CommonTree.run (canonicalFamilyTree gates fuel σ) x g = dnfEval (gates g) x := by
  rw [run_canonicalFamilyTree]
  exact canonicalDT_eval fuel σ x hstars hext

/-- The normalized family tree still returns every genuine DNF value. -/
theorem run_readOnceCanonicalFamilyTree_eq_dnf {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hstars : stars σ ≤ fuel) (hext : Rung4Restriction.Extends σ x)
    (g : Fin G) :
    CommonTree.run (readOnceCanonicalFamilyTree gates fuel σ) x g =
      dnfEval (gates g) x := by
  rw [readOnceCanonicalFamilyTree, CommonTree.run_readOnce σ _ x hext]
  exact run_canonicalFamilyTree_eq_dnf gates fuel σ x hstars hext g

/-- Every genuine normalized family path is read-once. -/
theorem queryVars_readOnceCanonicalFamilyTree_nodup {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    (CommonTree.queryVars (readOnceCanonicalFamilyTree gates fuel σ) x).Nodup := by
  exact CommonTree.queryVars_readOnce_nodup σ _ x hext

/-- One live-dimension finite label determines all genuine gate values simultaneously. -/
theorem canonicalFamily_values_eq_of_liveFinitePathLabel_eq {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    {x y : Fin n → Bool} (hx : Rung4Restriction.Extends σ x)
    (hy : Rung4Restriction.Extends σ y)
    (hlabel : CommonTree.liveFinitePathLabel σ (canonicalFamilyTree gates fuel σ) x hx =
      CommonTree.liveFinitePathLabel σ (canonicalFamilyTree gates fuel σ) y hy) :
    ∀ g, CommonTree.run (readOnceCanonicalFamilyTree gates fuel σ) x g =
      CommonTree.run (readOnceCanonicalFamilyTree gates fuel σ) y g := by
  intro g
  exact congrFun (CommonTree.run_readOnce_eq_of_liveFinitePathLabel_eq
    σ (canonicalFamilyTree gates fuel σ) hx hy hlabel) g

/-- A single common-path label determines all canonical outputs in the family simultaneously. -/
theorem canonicalFamily_values_eq_of_pathLabel_eq {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    {x y : Fin n → Bool}
    (h : CommonTree.pathLabel (canonicalFamilyTree gates fuel σ) x =
      CommonTree.pathLabel (canonicalFamilyTree gates fuel σ) y) :
    ∀ g, (canonicalDT (gates g) fuel σ).eval x =
      (canonicalDT (gates g) fuel σ).eval y := by
  intro g
  rw [← run_canonicalFamilyTree gates fuel σ x g,
    ← run_canonicalFamilyTree gates fuel σ y g]
  exact congrFun (CommonTree.run_eq_of_pathLabel_eq _ h) g

/-- The finite shared label, of cardinality `(d+1)·2^d`, determines the whole canonical family. -/
theorem canonicalFamily_values_eq_of_finitePathLabel_eq {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    {x y : Fin n → Bool}
    (h : CommonTree.finitePathLabel (canonicalFamilyTree gates fuel σ) x =
      CommonTree.finitePathLabel (canonicalFamilyTree gates fuel σ) y) :
    ∀ g, (canonicalDT (gates g) fuel σ).eval x =
      (canonicalDT (gates g) fuel σ).eval y := by
  intro g
  rw [← run_canonicalFamilyTree gates fuel σ x g,
    ← run_canonicalFamilyTree gates fuel σ y g]
  exact congrFun (CommonTree.run_eq_of_finitePathLabel_eq _ h) g

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_bind
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.depth_reindex
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_reindex
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.depth_bind_le
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_readOnce
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.queryVars_readOnce_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.mem_queryVars_of_mem_readOnce
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.queryVars_readOnce_toFinset_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.trace_readOnce_length_le_ambient
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.trace_readOnce_length_le_stars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_readOnce_eq_of_liveFinitePathLabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.card_liveFinitePathLabel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.freeVars_pathEndpoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.stars_pathEndpoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.freeOn_pathEndpoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.pathEndpoint_inj_of_pathVars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.prefixEndpoint_eq_fixOn
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.prefixVars_card_eq_of_le_trace
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.prefixVars_subset_freeVars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.stars_prefixEndpoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.freeOn_prefixEndpoint
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.prefixEndpoint_inj_of_prefixVars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.trace_bind
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.queryVars_bind
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_commonRefine
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.trace_commonRefine
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.queryVars_commonRefineFin
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.pathVars_canonicalFamily_eq_raw
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_commonRefineFin
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.trace_commonRefineFin_length
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.replay_trace
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.card_finitePathLabel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.PathLabel.toFinite_injective
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_eq_of_pathLabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_eq_of_finitePathLabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.run_canonicalFamilyTree_eq_dnf
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.run_readOnceCanonicalFamilyTree_eq_dnf
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.queryVars_readOnceCanonicalFamilyTree_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_values_eq_of_liveFinitePathLabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_values_eq_of_pathLabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_values_eq_of_finitePathLabel_eq
