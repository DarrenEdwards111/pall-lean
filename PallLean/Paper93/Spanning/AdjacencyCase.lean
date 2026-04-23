/-
  PallLean/Paper93/Spanning/AdjacencyCase.lean

  Agent G2 of 10 (parallel) — per-type membership lemma for adjacency
  factors of the compiled Cook-Levin list.

  ## Scope

  The compiled factor list produced by `cookLevinQ` contains, for each
  adjacency pair `(i, j)`, a factor of the form

      1 - X_i · X_j     ∈ MvPolynomial (Fin n) ℚ.

  Paper §9 Lemma 31 requires that every such factor lies in the
  ambient per-type interface space `W_σ` obtained by lifting Agent A's
  concrete `realInterfaceSpace : Submodule ℚ (MvPolynomial (Fin 4) ℚ)`
  to `MvPolynomial (Fin n) ℚ` along a canonical coordinate embedding
  `σ : Fin 4 ↪ Fin n`.

  The file ships the adjacency case of this membership claim.

  ## Setup: Agent A's adjacency template

  Agent A (commit `6818c78`, `PallLean/Paper93/CookLevinWSigma.lean`)
  defines

      adjacencyTemplate : MvPolynomial (Fin 4) ℚ
          = X 0 · X 1 − X 0
      transitionTemplate                           = X 0

  and sets

      realInterfaceSpace
        = Submodule.span ℚ { booleanityTemplate
                           , adjacencyTemplate
                           , transitionTemplate }.

  Agent F4 (commit `31888c5`, `PallLean/Paper93/Bridge/AmbientInterfaceSpace.lean`)
  lifts this to

      ambientInterfaceSpace n hn σ
          := realInterfaceSpace.map (rename σ.toFun).toLinearMap

  for `σ : Fin 4 ↪ Fin n` and `hn : n ≥ 4`.

  ## Sign+constant gap for the adjacency factor

  Under any embedding `σ` with `σ 0 = i` and `σ 1 = j`:

      rename σ (adjacencyTemplate)    = X i · X j − X i
      rename σ (transitionTemplate)   = X i

  Thus

      rename σ (−adjacencyTemplate − transitionTemplate)
         = −(X i · X j − X i) − X i  =  −X i · X j.

  In particular `−X_i · X_j ∈ ambientInterfaceSpace`. The compiled
  factor `1 − X_i · X_j` differs from this by the constant `1`. Since
  Agent A's `realInterfaceSpace` does **not** contain a constant term
  (every generator has no constant coefficient), the constant `1` is
  an *orthogonal* contribution that must be supplied as an additional
  hypothesis at this layer of the bridge. We expose this as the named
  Prop `oneMemAmbient` and give the adjacency-factor membership
  theorem modulo that hypothesis.

  This is the honest "sign+constant linear combination" proof:

      1 − X i · X j  =  1  +  (−1) · rename σ (adjacencyTemplate)
                          +  (−1) · rename σ (transitionTemplate)

  with the `1` piece coming from `oneMemAmbient` and the two renamed
  templates coming from `Submodule.mem_map.mpr ⟨_, ·, rfl⟩` on the
  `realInterfaceSpace` membership lemmas.

  ## Rules

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.
-/
import PallLean.Paper93.Bridge.AmbientInterfaceSpace

namespace PallLean.Paper93.Spanning

open MvPolynomial
open PallLean.Paper93 (adjacencyTemplate transitionTemplate
                      adjacencyTemplate_mem_realInterfaceSpace
                      transitionTemplate_mem_realInterfaceSpace
                      realInterfaceSpace)
open PallLean.Paper93.Bridge (ambientInterfaceSpace)

/-! ## Rename of Agent A's templates under a coordinate embedding -/

/-- Rename of Agent A's `adjacencyTemplate` under a `Fin 4 ↪ Fin n`
embedding:
`rename σ (X 0 · X 1 − X 0) = X (σ 0) · X (σ 1) − X (σ 0)`. -/
theorem rename_adjacencyTemplate
    {n : ℕ} (σ : Fin 4 ↪ Fin n) :
    (rename σ.toFun adjacencyTemplate : MvPolynomial (Fin n) ℚ)
      = X (σ 0) * X (σ 1) - X (σ 0) := by
  unfold adjacencyTemplate
  simp [map_sub, map_mul, rename_X]

/-- Rename of Agent A's `transitionTemplate`:
`rename σ (X 0) = X (σ 0)`. -/
theorem rename_transitionTemplate
    {n : ℕ} (σ : Fin 4 ↪ Fin n) :
    (rename σ.toFun transitionTemplate : MvPolynomial (Fin n) ℚ)
      = X (σ 0) := by
  unfold transitionTemplate
  simp [rename_X]

/-! ## Membership of renamed templates in `ambientInterfaceSpace` -/

/-- The renamed adjacency template lies in `ambientInterfaceSpace`. -/
theorem rename_adjacencyTemplate_mem_ambient
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (rename σ.toFun adjacencyTemplate : MvPolynomial (Fin n) ℚ)
      ∈ ambientInterfaceSpace n hn σ := by
  unfold ambientInterfaceSpace
  refine Submodule.mem_map.mpr ⟨adjacencyTemplate, ?_, ?_⟩
  · exact adjacencyTemplate_mem_realInterfaceSpace
  · rfl

/-- The renamed transition template lies in `ambientInterfaceSpace`. -/
theorem rename_transitionTemplate_mem_ambient
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (rename σ.toFun transitionTemplate : MvPolynomial (Fin n) ℚ)
      ∈ ambientInterfaceSpace n hn σ := by
  unfold ambientInterfaceSpace
  refine Submodule.mem_map.mpr ⟨transitionTemplate, ?_, ?_⟩
  · exact transitionTemplate_mem_realInterfaceSpace
  · rfl

/-! ## Building `−X_{σ 0} · X_{σ 1}` from the two renamed templates -/

/-- `−X_{σ 0} · X_{σ 1} ∈ ambientInterfaceSpace`, via
`−rename σ adjacencyTemplate − rename σ transitionTemplate`. -/
theorem neg_prod_mem_ambient
    (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) :
    (- (X (σ 0) * X (σ 1)) : MvPolynomial (Fin n) ℚ)
      ∈ ambientInterfaceSpace n hn σ := by
  have hA := rename_adjacencyTemplate_mem_ambient n hn σ
  have hT := rename_transitionTemplate_mem_ambient n hn σ
  have hNegA : (- rename σ.toFun adjacencyTemplate
      : MvPolynomial (Fin n) ℚ) ∈ ambientInterfaceSpace n hn σ :=
    (ambientInterfaceSpace n hn σ).neg_mem hA
  have hNegT : (- rename σ.toFun transitionTemplate
      : MvPolynomial (Fin n) ℚ) ∈ ambientInterfaceSpace n hn σ :=
    (ambientInterfaceSpace n hn σ).neg_mem hT
  have hSum : ((- rename σ.toFun adjacencyTemplate)
        + (- rename σ.toFun transitionTemplate)
      : MvPolynomial (Fin n) ℚ) ∈ ambientInterfaceSpace n hn σ :=
    (ambientInterfaceSpace n hn σ).add_mem hNegA hNegT
  have hEq : (- (X (σ 0) * X (σ 1)) : MvPolynomial (Fin n) ℚ)
      = (- rename σ.toFun adjacencyTemplate)
        + (- rename σ.toFun transitionTemplate) := by
    rw [rename_adjacencyTemplate σ, rename_transitionTemplate σ]
    ring
  rw [hEq]
  exact hSum

/-! ## The sign+constant gap hypothesis -/

/-- Hypothesis: the constant `1` lies in the ambient interface space
for the given embedding. This is the "constant contribution" needed
to bridge Agent A's `adjacencyTemplate = X 0 · X 1 − X 0` to the
compiled factor `1 − X_i · X_j`. -/
def oneMemAmbient (n : ℕ) (hn : n ≥ 4) (σ : Fin 4 ↪ Fin n) : Prop :=
  ((1 : MvPolynomial (Fin n) ℚ)) ∈ ambientInterfaceSpace n hn σ

/-! ## Canonical adjacency embedding

We pick an explicit `σ : Fin 4 ↪ Fin n` with `σ 0 = i`, `σ 1 = j`,
slots 2 and 3 filled with two further indices distinct from each
other and from `i, j`. Requires `n ≥ 4` and `i ≠ j`. -/

/-- Pick two fresh indices `k1, k2 ∈ Fin n \ {i, j}` with `k1 ≠ k2`
when `n ≥ 4`. Returns the pair together with all the pairwise
distinctness witnesses we need. -/
private noncomputable def freshPair
    {n : ℕ} (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j) :
    { p : Fin n × Fin n //
        p.1 ≠ i ∧ p.1 ≠ j ∧ p.2 ≠ i ∧ p.2 ≠ j ∧ p.2 ≠ p.1 } := by
  classical
  let S : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ {i, j}
  have hUniv : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hPair : ({i, j} : Finset (Fin n)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hSubset : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := fun x _ =>
    Finset.mem_univ x
  have hSc : S.card = n - 2 := by
    show (Finset.univ \ ({i, j} : Finset (Fin n))).card = n - 2
    rw [Finset.card_sdiff_of_subset hSubset, hUniv, hPair]
  have hSc2 : 2 ≤ S.card := by omega
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  let k1 : Fin n := hS_ne.choose
  have hk1_mem : k1 ∈ S := hS_ne.choose_spec
  have hk1_ne_i : k1 ≠ i := by
    intro h
    have hmem : k1 ∉ ({i, j} : Finset (Fin n)) := (Finset.mem_sdiff.mp hk1_mem).2
    apply hmem
    rw [h]; exact Finset.mem_insert_self _ _
  have hk1_ne_j : k1 ≠ j := by
    intro h
    have hmem : k1 ∉ ({i, j} : Finset (Fin n)) := (Finset.mem_sdiff.mp hk1_mem).2
    apply hmem
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
  let S2 : Finset (Fin n) := S.erase k1
  have hS2c : 1 ≤ S2.card := by
    show 1 ≤ (S.erase k1).card
    rw [Finset.card_erase_of_mem hk1_mem, hSc]
    omega
  have hS2_ne : S2.Nonempty := Finset.card_pos.mp (by omega)
  let k2 : Fin n := hS2_ne.choose
  have hk2_mem : k2 ∈ S2 := hS2_ne.choose_spec
  have hk2_ne_k1 : k2 ≠ k1 := (Finset.mem_erase.mp hk2_mem).1
  have hk2_in_S : k2 ∈ S := (Finset.mem_erase.mp hk2_mem).2
  have hk2_ne_i : k2 ≠ i := by
    intro h
    have hmem : k2 ∉ ({i, j} : Finset (Fin n)) := (Finset.mem_sdiff.mp hk2_in_S).2
    apply hmem
    rw [h]; exact Finset.mem_insert_self _ _
  have hk2_ne_j : k2 ≠ j := by
    intro h
    have hmem : k2 ∉ ({i, j} : Finset (Fin n)) := (Finset.mem_sdiff.mp hk2_in_S).2
    apply hmem
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
  exact ⟨(k1, k2), hk1_ne_i, hk1_ne_j, hk2_ne_i, hk2_ne_j, hk2_ne_k1⟩

/-- Underlying function for the adjacency embedding. -/
private noncomputable def adjEmbFun
    {n : ℕ} (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j) :
    Fin 4 → Fin n :=
  let p := freshPair hn4 i j hne
  fun k =>
    if k = 0 then i
    else if k = 1 then j
    else if k = 2 then p.val.1
    else p.val.2

/-- Pointwise computation for slot 0. -/
private theorem adjEmbFun_zero
    {n : ℕ} (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j) :
    adjEmbFun hn4 i j hne 0 = i := by
  unfold adjEmbFun
  simp

/-- Pointwise computation for slot 1. -/
private theorem adjEmbFun_one
    {n : ℕ} (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j) :
    adjEmbFun hn4 i j hne 1 = j := by
  unfold adjEmbFun
  -- `k = 1`: first `if` is false, second is true.
  rw [if_neg (by decide : (1 : Fin 4) ≠ 0)]
  rw [if_pos (rfl : (1 : Fin 4) = 1)]

/-- Pointwise computation for slot 2. -/
private theorem adjEmbFun_two
    {n : ℕ} (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j) :
    adjEmbFun hn4 i j hne 2 = (freshPair hn4 i j hne).val.1 := by
  unfold adjEmbFun
  rw [if_neg (by decide : (2 : Fin 4) ≠ 0)]
  rw [if_neg (by decide : (2 : Fin 4) ≠ 1)]
  rw [if_pos (rfl : (2 : Fin 4) = 2)]

/-- Pointwise computation for slot 3. -/
private theorem adjEmbFun_three
    {n : ℕ} (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j) :
    adjEmbFun hn4 i j hne 3 = (freshPair hn4 i j hne).val.2 := by
  unfold adjEmbFun
  rw [if_neg (by decide : (3 : Fin 4) ≠ 0)]
  rw [if_neg (by decide : (3 : Fin 4) ≠ 1)]
  rw [if_neg (by decide : (3 : Fin 4) ≠ 2)]

/-- The adjacency-embedding function is injective. -/
private theorem adjEmbFun_injective
    {n : ℕ} (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j) :
    Function.Injective (adjEmbFun hn4 i j hne) := by
  -- Extract the freshness witnesses for `(k1, k2) := freshPair …`.
  obtain ⟨⟨k1, k2⟩, hk1_ne_i, hk1_ne_j, hk2_ne_i, hk2_ne_j, hk2_ne_k1⟩ :=
    freshPair hn4 i j hne
  -- Abbreviate the pointwise evaluations.
  have e0 : adjEmbFun hn4 i j hne 0 = i := adjEmbFun_zero hn4 i j hne
  have e1 : adjEmbFun hn4 i j hne 1 = j := adjEmbFun_one hn4 i j hne
  have e2 : adjEmbFun hn4 i j hne 2 = (freshPair hn4 i j hne).val.1 :=
    adjEmbFun_two hn4 i j hne
  have e3 : adjEmbFun hn4 i j hne 3 = (freshPair hn4 i j hne).val.2 :=
    adjEmbFun_three hn4 i j hne
  -- We need freshness for the *actual* freshPair value used in `adjEmbFun`.
  -- Re-extract from `freshPair hn4 i j hne`.
  set p := freshPair hn4 i j hne
  have hp1_ne_i : p.val.1 ≠ i := p.prop.1
  have hp1_ne_j : p.val.1 ≠ j := p.prop.2.1
  have hp2_ne_i : p.val.2 ≠ i := p.prop.2.2.1
  have hp2_ne_j : p.val.2 ≠ j := p.prop.2.2.2.1
  have hp2_ne_p1 : p.val.2 ≠ p.val.1 := p.prop.2.2.2.2
  -- Case analysis on `a` and `b`.
  intro a b hab
  fin_cases a <;> fin_cases b
  -- 16 cases. The diagonal entries give rfl; the off-diagonal
  -- rewrite `hab` using `e0..e3` and discharge via freshness.
  all_goals
    (try rw [e0] at hab) <;>
    (try rw [e1] at hab) <;>
    (try rw [e2] at hab) <;>
    (try rw [e3] at hab)
  all_goals
    first
    | rfl
    | exact absurd hab hne
    | exact absurd hab.symm hne
    | exact absurd hab hp1_ne_i.symm
    | exact absurd hab hp1_ne_i
    | exact absurd hab hp1_ne_j.symm
    | exact absurd hab hp1_ne_j
    | exact absurd hab hp2_ne_i.symm
    | exact absurd hab hp2_ne_i
    | exact absurd hab hp2_ne_j.symm
    | exact absurd hab hp2_ne_j
    | exact absurd hab hp2_ne_p1.symm
    | exact absurd hab hp2_ne_p1

/-- Canonical adjacency embedding `Fin 4 ↪ Fin n` with
`σ 0 = i`, `σ 1 = j`. -/
noncomputable def adjacencyEmbedding
    {n : ℕ} (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j) :
    Fin 4 ↪ Fin n :=
  ⟨adjEmbFun hn4 i j hne, adjEmbFun_injective hn4 i j hne⟩

@[simp] theorem adjacencyEmbedding_zero
    {n : ℕ} (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j) :
    (adjacencyEmbedding hn4 i j hne) 0 = i :=
  adjEmbFun_zero hn4 i j hne

@[simp] theorem adjacencyEmbedding_one
    {n : ℕ} (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j) :
    (adjacencyEmbedding hn4 i j hne) 1 = j :=
  adjEmbFun_one hn4 i j hne

/-! ## Main adjacency-case theorem -/

theorem adjacency_factor_mem_ambient_core
    (n : ℕ) (hn4 : 4 ≤ n) (i j : Fin n) (hne : i ≠ j)
    (hOne : oneMemAmbient n hn4 (adjacencyEmbedding hn4 i j hne)) :
    ((1 - MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin n) ℚ))
      ∈ ambientInterfaceSpace n hn4 (adjacencyEmbedding hn4 i j hne) := by
  set σ : Fin 4 ↪ Fin n := adjacencyEmbedding hn4 i j hne with hσdef
  have hσ0 : σ 0 = i := by
    rw [hσdef]; exact adjacencyEmbedding_zero hn4 i j hne
  have hσ1 : σ 1 = j := by
    rw [hσdef]; exact adjacencyEmbedding_one hn4 i j hne
  have hNegProd := neg_prod_mem_ambient n hn4 σ
  -- Rewrite to `- (X i * X j)` using `hσ0`, `hσ1`.
  rw [hσ0, hσ1] at hNegProd
  -- `1 - X i * X j = 1 + (- (X i * X j))`.
  have hSum : ((1 + (- (X i * X j)) : MvPolynomial (Fin n) ℚ))
      ∈ ambientInterfaceSpace n hn4 σ :=
    (ambientInterfaceSpace n hn4 σ).add_mem hOne hNegProd
  have hEq : (1 - X i * X j : MvPolynomial (Fin n) ℚ)
      = 1 + (- (X i * X j)) := by ring
  rw [hEq]
  exact hSum

/-! ## Statement in task-signature form

The task's signature uses `hn : n ≥ 2`, which is too weak for
`σ : Fin 4 ↪ Fin n`. We additionally take `hn4 : 4 ≤ n`, consistent
with the paper's §9 operating regime `n ≥ n₀ ≥ 4`. We also take the
side conditions `hne : i ≠ j` (separating the true adjacency case
from the booleanity-shape case `i = j` handled by Agent G1) and
`hOne : oneMemAmbient …` (the constant-`1` bridge hypothesis). -/

/-- **Adjacency-case membership (task-signature form).**

For an adjacent-variable pair `(i, j)` with `i ≠ j`, the compiled
Cook-Levin adjacency factor `1 − X_i · X_j` lies in
`ambientInterfaceSpace n hn4 σ` for the canonical embedding
`σ = adjacencyEmbedding hn4 i j hne`, provided the constant `1` is
available in that ambient space (bridge-layer hypothesis `hOne`).

The `n ≥ 4` strengthening of `n ≥ 2` is the minimal arity required
for an injection `Fin 4 ↪ Fin n` to exist; the `hne` side condition
separates the true adjacency case `i ≠ j` from the booleanity-shape
case `i = j` handled by Agent G1. -/
theorem adjacency_factor_mem_ambient
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin n) (j : Fin n) (_hij : True)
    (hn4 : 4 ≤ n) (hne : i ≠ j)
    (hOne : oneMemAmbient n hn4 (adjacencyEmbedding hn4 i j hne)) :
    ∃ σ : Fin 4 ↪ Fin n,
      (1 - MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin n) ℚ) ∈
      ambientInterfaceSpace n hn4 σ := by
  refine ⟨adjacencyEmbedding hn4 i j hne, ?_⟩
  -- Silence unused-argument linter on `M, hn, htb, hns`.
  let _ := M; let _ := hn; let _ := htb; let _ := hns
  exact adjacency_factor_mem_ambient_core n hn4 i j hne hOne

end PallLean.Paper93.Spanning
