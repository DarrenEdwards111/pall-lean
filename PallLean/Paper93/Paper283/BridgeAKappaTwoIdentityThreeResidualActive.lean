import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityThreeStructural

/-!
# Residual active claim for identity (3) per-pair sum

This file discharges the second residual hypothesis consumed by
`identityThree_perPairSum_of_decomposition` (Section H of
`BridgeAKappaTwoIdentityThreeStructural`):

```
identityThree_residualActiveClaim M n k hk1 hk2 :=
  coeff probeLeft
    ((inertFactorsList M n k hk1 hk2).prod *
      pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
        (activeFactorsList M n k hk1 hk2)) =
  crossBlockKValue (transCoeffSum M).
```

## Strategy

The proof uses a single key insight: **multiplying by any factor whose
non-constant monomials all carry a "stray" variable outside the probe
`{3k, 3k+1}` does not change the bilinear coefficient at
`probeLeft = single 3k 1 + single 3k+1 1`**.  We call such factors
**probe-preservation factors**.

Concretely, the following are probe-preservation factors:
* `boolFactorPoly n ⟨3*k+2, _⟩` (bool@u = bool@3k+2): non-constant
  monomials `-X_u`, `+X_u²` both carry `X_u`, with `u = 3k+2 ∉ {3k, 3k+1}`.
* `cadjFactorPoly c ⟨i, _⟩ ⟨j, _⟩` whenever `{i, j}` contains an index
  not in `{3k, 3k+1}`: non-constant monomial `-c · X_i · X_j` carries the
  stray index.  This includes:
  * `cadj c (3k-1, 3k)` (inert; stray = 3k-1)
  * `cadj c (3k+1, u)` (active u-only; stray = u)
  * `cadj c (u, v)` (active u/v; stray = u and stray = v)

Once we know which factors are probe-preservation, we can show that

  `coeff probeLeft (inert.prod * U_only.prod * (UV \ {ℓ}).prod)`

is the **same constant** for every `ℓ ∈ R = {f3, t2_q : q}` (the
self-term residuals of `pderivListProdSumTwice u v active`), namely

  `coeff probeLeft essential_inert.prod = -S`,

where `essential_inert = [bool@3k, bool@3k+1, cadj 1 (3k, 3k+1)] ++
flatMap_q [trans@(3k, 3k+1)_q]` and `S = transCoeffSum M`.

Combined with the cross-term vanishing of Section J in
`BridgeAKappaTwoIdentityThreeAux`, this gives

  `LHS = Σ_{ℓ ∈ R} (-c_ℓ) · (-S) = (1 + S) · S = K`.

## Hard rules (project CLAUDE.md)

* No `sorry`.  No new axioms.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP
open BridgeABlockProductRule
open BridgeAKappaTwoTwoFoldLeibnizExpansion
open BridgeAKappaTwoFactorPairLemmas
open BridgeAKappaTwoIdentityOne
open BridgeAKappaTwoIdentityFour
open BridgeAKappaTwoIdentityThreeAux
open BridgeAKappaTwoIdentityThreeStructural
open BridgeAKappaTwoListInductionHelpers
open MultilinearCoefficientInfrastructure

attribute [local instance] Classical.dec

namespace BridgeAKappaTwoIdentityThreeResidualActive

/-! ## Section A: probe-preservation lemmas

A polynomial `f` is **probe-preserving** (with respect to indices
`a = 3k` and `b = 3k+1`) iff
`coeff (single a 1 + single b 1) (f * p) = coeff (single a 1 + single b 1) p`
for every polynomial `p`.

We do not introduce a `Prop`-valued predicate; we just prove the
equality directly for each factor shape we encounter. -/

/-! ## Section A0: generic list-product pass-through -/

/-- If every factor in `fs` preserves the bilinear probe coefficient
under left multiplication, then the whole list product preserves it.

This is the small induction needed later for the products of
`bool@u`, `cadj@(b,u)`, and `cadj@(u,v)` factors that carry at least
one row variable outside the probe. -/
theorem coeff_X_a_X_b_list_prod_mul_of_forall_preserve {n : ℕ}
    (a b : Fin n) (fs : List (MvPolynomial (Fin n) ℚ))
    (p : MvPolynomial (Fin n) ℚ)
    (hfs : ∀ f ∈ fs, ∀ p' : MvPolynomial (Fin n) ℚ,
      MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
          (f * p') =
        MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1) p') :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (fs.prod * p) =
      MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1) p := by
  induction fs with
  | nil =>
      simp
  | cons f fs ih =>
      rw [List.prod_cons]
      rw [mul_assoc]
      rw [hfs f (by simp) (fs.prod * p)]
      exact ih (fun g hg p' => hfs g (List.mem_cons_of_mem f hg) p')

/-- **bool@u preservation**: for `u ∉ {a, b}`, multiplying by
`boolFactorPoly n u` preserves the bilinear coefficient at
`single a 1 + single b 1`.

Proof: `boolFactorPoly n u = 1 - X_u (1 - X_u) = 1 - X_u + X_u²`.
The `-X_u` and `+X_u²` contributions both vanish under
`coeff_X_a_X_b_X_u_mul_zero` / `coeff_X_a_X_b_X_u_sq_mul_zero`. -/
theorem coeff_X_a_X_b_boolFactorPoly_mul {n : ℕ}
    (a b u : Fin n) (p : MvPolynomial (Fin n) ℚ)
    (hua : u ≠ a) (hub : u ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (boolFactorPoly n u * p) =
      MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1) p := by
  -- Expand `boolFactorPoly n u * p = p - X_u · p + X_u² · p`.
  have hexpand :
      (boolFactorPoly n u * p : MvPolynomial (Fin n) ℚ) =
      p + (- (MvPolynomial.X u * p))
        + (MvPolynomial.X u * MvPolynomial.X u * p) := by
    unfold boolFactorPoly
    ring
  rw [hexpand]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add]
  rw [MvPolynomial.coeff_neg]
  rw [coeff_X_a_X_b_X_u_mul_zero a b u p hua hub]
  rw [coeff_X_a_X_b_X_u_sq_mul_zero a b u p hua hub]
  ring

/-- **cadj preservation, stray first index**: for `i ∉ {a, b}`,
multiplying by `cadjFactorPoly c i j` preserves the bilinear coefficient
at `single a 1 + single b 1`.

Proof: `cadj c i j = 1 - C c · (X_i · X_j)`.  The `-C c · X_i · X_j`
contribution vanishes by `coeff_X_a_X_b_C_c_X_w_X_v_mul_zero_when_v_outside`
applied with `v := i`. -/
theorem coeff_X_a_X_b_cadjFactorPoly_mul_stray_fst {n : ℕ}
    (a b i j : Fin n) (c : ℚ) (p : MvPolynomial (Fin n) ℚ)
    (hia : i ≠ a) (hib : i ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (cadjFactorPoly c i j * p) =
      MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1) p := by
  have hexpand :
      (cadjFactorPoly c i j * p : MvPolynomial (Fin n) ℚ) =
      p + (- (MvPolynomial.C c * (MvPolynomial.X j * MvPolynomial.X i) * p)) := by
    unfold cadjFactorPoly
    ring
  rw [hexpand]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_neg]
  rw [coeff_X_a_X_b_C_c_X_w_X_v_mul_zero_when_v_outside a b j i c p hia hib]
  ring

/-- **cadj preservation, stray second index**: for `j ∉ {a, b}`,
multiplying by `cadjFactorPoly c i j` preserves the bilinear coefficient
at `single a 1 + single b 1`. -/
theorem coeff_X_a_X_b_cadjFactorPoly_mul_stray_snd {n : ℕ}
    (a b i j : Fin n) (c : ℚ) (p : MvPolynomial (Fin n) ℚ)
    (hja : j ≠ a) (hjb : j ≠ b) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1)
        (cadjFactorPoly c i j * p) =
      MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1) p := by
  have hexpand :
      (cadjFactorPoly c i j * p : MvPolynomial (Fin n) ℚ) =
      p + (- (MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j) * p)) := by
    unfold cadjFactorPoly
    ring
  rw [hexpand]
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_neg]
  rw [coeff_X_a_X_b_C_c_X_w_X_v_mul_zero_when_v_outside a b i j c p hja hjb]
  ring

/-! ## Section B: identity-(3)-specific probe-preservation instances -/

/-- `bool@u` preserves `probeLeft`, where
`u = 3k+2 ∉ {3k, 3k+1}`. -/
theorem coeff_probeLeft_bool_u_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (boolFactorPoly n (uIdx n k hk2) * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq]
  exact coeff_X_a_X_b_boolFactorPoly_mul
    (aIdx n k hk2) (bIdx n k hk2) (uIdx n k hk2) p
    (fun h => aIdx_ne_uIdx n k hk2 h.symm)
    (fun h => bIdx_ne_uIdx n k hk2 h.symm)

/-- Any factor `cadj@(b,u)` preserves `probeLeft`, because the second
coordinate `u = 3k+2` is outside the probe. -/
theorem coeff_probeLeft_cadj_b_u_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (cadjFactorPoly c (bIdx n k hk2) (uIdx n k hk2) * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq]
  exact coeff_X_a_X_b_cadjFactorPoly_mul_stray_snd
    (aIdx n k hk2) (bIdx n k hk2)
    (bIdx n k hk2) (uIdx n k hk2) c p
    (fun h => aIdx_ne_uIdx n k hk2 h.symm)
    (fun h => bIdx_ne_uIdx n k hk2 h.symm)

/-- Any factor `cadj@(u,v)` preserves `probeLeft`, because the first
coordinate `u = 3k+2` is outside the probe. -/
theorem coeff_probeLeft_cadj_u_v_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (cadjFactorPoly c (uIdx n k hk2) (vIdx n k hk2) * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq]
  exact coeff_X_a_X_b_cadjFactorPoly_mul_stray_fst
    (aIdx n k hk2) (bIdx n k hk2)
    (uIdx n k hk2) (vIdx n k hk2) c p
    (fun h => aIdx_ne_uIdx n k hk2 h.symm)
    (fun h => bIdx_ne_uIdx n k hk2 h.symm)

/-- Any left-adjacent factor `cadj@(3k-1,3k)` preserves `probeLeft`,
because the first coordinate `3k-1` is outside `{3k,3k+1}`. -/
theorem coeff_probeLeft_cadj_prev_a_mul
    (n k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (cadjFactorPoly c
          (⟨3 * k - 1, by omega⟩ : Fin n)
          (⟨3 * k - 1 + 1, by omega⟩ : Fin n) * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq]
  exact coeff_X_a_X_b_cadjFactorPoly_mul_stray_fst
    (aIdx n k hk2) (bIdx n k hk2)
    (⟨3 * k - 1, by omega⟩ : Fin n)
    (⟨3 * k - 1 + 1, by omega⟩ : Fin n) c p
    (by
      intro h
      have := congr_arg Fin.val h
      unfold aIdx at this
      simp at this
      omega)
    (by
      intro h
      have := congr_arg Fin.val h
      unfold bIdx at this
      simp at this)

/-! ## Section B1: direct probe factor update -/

/-- Multiplying by a direct probe factor `cadj@(a,b)` updates the
`probeLeft` coefficient by `-c * coeff 0 p` and preserves the old
probe coefficient.  This is the local quantitative contribution of
the inert `adj/trans@3k` family. -/
theorem coeff_probeLeft_cadj_a_b_mul
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2) * p) =
      -c * MvPolynomial.coeff 0 p +
        MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq]
  have hab : aIdx n k hk2 ≠ bIdx n k hk2 := aIdx_ne_bIdx n k hk2
  rw [coeff_X_v_X_w_cadjFactorPoly_mul c
    (aIdx n k hk2) (bIdx n k hk2)
    (aIdx n k hk2) (bIdx n k hk2) p hab hab]
  have ha :
      MvPolynomial.coeff (Finsupp.single (aIdx n k hk2) 1)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)) = 0 := by
    unfold cadjFactorPoly
    exact coeff_X_a_one_sub_C_X_mul_X
      (aIdx n k hk2) (aIdx n k hk2) (bIdx n k hk2) hab c
  have hb :
      MvPolynomial.coeff (Finsupp.single (bIdx n k hk2) 1)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)) = 0 := by
    unfold cadjFactorPoly
    exact coeff_X_a_one_sub_C_X_mul_X
      (bIdx n k hk2) (aIdx n k hk2) (bIdx n k hk2) hab c
  have hprobe :
      MvPolynomial.coeff
          (Finsupp.single (aIdx n k hk2) 1 + Finsupp.single (bIdx n k hk2) 1)
          (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)) = -c := by
    rw [coeff_X_v_X_w_cadjFactorPoly c
      (aIdx n k hk2) (bIdx n k hk2)
      (aIdx n k hk2) (bIdx n k hk2) hab hab]
    simp
  have hzero :
      MvPolynomial.coeff 0
          (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)) = 1 :=
    coeff_zero_cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2)
  rw [ha, hb, hprobe, hzero]
  ring

/-- If the tail has constant coefficient `1`, a direct probe factor
subtracts exactly its coefficient `c` from the probe coefficient. -/
theorem coeff_probeLeft_cadj_a_b_mul_of_coeff_zero_one
    (n k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (p : MvPolynomial (Fin n) ℚ)
    (hp0 : MvPolynomial.coeff 0 p = 1) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (cadjFactorPoly c (aIdx n k hk2) (bIdx n k hk2) * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p - c := by
  rw [coeff_probeLeft_cadj_a_b_mul n k hk2 c p, hp0]
  ring

/-! ## Section C: active-list factor split by support shape -/

/-- Active factors that involve `u = 3k+2` but not `v = 3k+3`:
`bool@u`, `cadj@(b,u)`, and the transition analogues. -/
noncomputable def activeBUFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (_hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [boolFactorPoly n (uIdx n k hk2),
   cadjFactorPoly 1 (bIdx n k hk2) (uIdx n k hk2)] ++
  (List.finRange M.numStates).flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (uIdx n k hk2)])

/-- Active factors that involve the full right row `(u,v)`.  These
are the self-term factors in identity (3). -/
noncomputable def activeUVFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (_hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [cadjFactorPoly 1 (uIdx n k hk2) (vIdx n k hk2)] ++
  (List.finRange M.numStates).flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q) (uIdx n k hk2) (vIdx n k hk2)])

/-- Split the per-state active transition `flatMap` into the `BU` and
`UV` halves. -/
private theorem activeTrans_flatMap_perm_split
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    ((List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (uIdx n k hk2),
         cadjFactorPoly (transCoeff M q) (uIdx n k hk2) (vIdx n k hk2)])).Perm
      ((List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (uIdx n k hk2)]) ++
       (List.finRange M.numStates).flatMap (fun q =>
          [cadjFactorPoly (transCoeff M q) (uIdx n k hk2) (vIdx n k hk2)])) := by
  exact (List.flatMap_append_perm (List.finRange M.numStates)
    (fun q : Fin M.numStates =>
      [cadjFactorPoly (transCoeff M q) (bIdx n k hk2) (uIdx n k hk2)])
    (fun q : Fin M.numStates =>
      [cadjFactorPoly (transCoeff M q) (uIdx n k hk2) (vIdx n k hk2)])).symm

/-- The structural active list is a permutation of the support-shape
split `BU ++ UV`. -/
theorem activeFactorsList_perm_BU_UV
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (activeFactorsList M n k hk1 hk2).Perm
      (activeBUFactorsList M n k hk1 hk2 ++
        activeUVFactorsList M n k hk1 hk2) := by
  unfold activeFactorsList activeBUFactorsList activeUVFactorsList
  unfold bIdx uIdx vIdx
  set B2 : MvPolynomial (Fin n) ℚ := boolFactorPoly n ⟨3 * k + 2, by omega⟩
  set A2 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (⟨3 * k + 1, by omega⟩ : Fin n)
      (⟨3 * k + 2, by omega⟩ : Fin n)
  set A3 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (⟨3 * k + 2, by omega⟩ : Fin n)
      (⟨3 * k + 3, hk2⟩ : Fin n)
  set Fbu : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q)
        (⟨3 * k + 1, by omega⟩ : Fin n)
        (⟨3 * k + 2, by omega⟩ : Fin n)])
  set Fuv : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q)
        (⟨3 * k + 2, by omega⟩ : Fin n)
        (⟨3 * k + 3, hk2⟩ : Fin n)])
  have hflat :
      ((List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q)
          (⟨3 * k + 1, by omega⟩ : Fin n)
          (⟨3 * k + 2, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)])).Perm (Fbu ++ Fuv) := by
    simpa [Fbu, Fuv, bIdx, uIdx, vIdx] using
      activeTrans_flatMap_perm_split M n k hk2
  refine (List.Perm.append_left [B2, A2, A3] hflat).trans ?_
  have hswap : (([A3] ++ Fbu) ++ Fuv).Perm ((Fbu ++ [A3]) ++ Fuv) :=
    (List.perm_append_comm (l₁ := [A3]) (l₂ := Fbu)).append_right Fuv
  have hprep : ([B2, A2] ++ (([A3] ++ Fbu) ++ Fuv)).Perm
      ([B2, A2] ++ ((Fbu ++ [A3]) ++ Fuv)) :=
    List.Perm.append_left [B2, A2] hswap
  simpa [List.append_assoc] using hprep

/-- Every `BU` active factor preserves `probeLeft`. -/
theorem activeBUFactorsList_forall_probe_preserve
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeBUFactorsList M n k hk1 hk2)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2) (f * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  unfold activeBUFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl) | ⟨q, _hq, rfl⟩)
  · exact coeff_probeLeft_bool_u_mul n k hk2 p
  · exact coeff_probeLeft_cadj_b_u_mul n k hk2 1 p
  · exact coeff_probeLeft_cadj_b_u_mul n k hk2 (transCoeff M q) p

/-- Every `UV` active factor preserves `probeLeft`. -/
theorem activeUVFactorsList_forall_probe_preserve
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeUVFactorsList M n k hk1 hk2)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2) (f * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  unfold activeUVFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with (rfl | ⟨q, _hq, rfl⟩)
  · exact coeff_probeLeft_cadj_u_v_mul n k hk2 1 p
  · exact coeff_probeLeft_cadj_u_v_mul n k hk2 (transCoeff M q) p

/-- The whole `BU` active subproduct preserves `probeLeft`. -/
theorem coeff_probeLeft_activeBU_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((activeBUFactorsList M n k hk1 hk2).prod * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeLeft_eq]
  exact activeBUFactorsList_forall_probe_preserve M n k hk1 hk2 f hf p'

/-- The whole `UV` active subproduct preserves `probeLeft`. -/
theorem coeff_probeLeft_activeUV_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((activeUVFactorsList M n k hk1 hk2).prod * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeLeft_eq]
  exact activeUVFactorsList_forall_probe_preserve M n k hk1 hk2 f hf p'

/-! ## Section D: constant coefficients of residual products -/

/-- Every inert factor has constant coefficient `1`. -/
theorem inertFactorsList_forall_coeff_zero_one
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ inertFactorsList M n k hk1 hk2) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold inertFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl | rfl | rfl) | ⟨q, _hq, rfl | rfl⟩)
  · exact coeff_zero_boolFactorPoly _
  · exact coeff_zero_boolFactorPoly _
  · exact coeff_zero_cadjFactorPoly 1 _ _
  · exact coeff_zero_cadjFactorPoly 1 _ _
  · exact coeff_zero_cadjFactorPoly (transCoeff M q) _ _
  · exact coeff_zero_cadjFactorPoly (transCoeff M q) _ _

/-- The inert product has constant coefficient `1`. -/
theorem coeff_zero_inertFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff 0 (inertFactorsList M n k hk1 hk2).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (inertFactorsList M n k hk1 hk2)
    (inertFactorsList_forall_coeff_zero_one M n k hk1 hk2)

/-- Every `BU` active factor has constant coefficient `1`. -/
theorem activeBUFactorsList_forall_coeff_zero_one
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeBUFactorsList M n k hk1 hk2) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold activeBUFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl) | ⟨q, _hq, rfl⟩)
  · exact coeff_zero_boolFactorPoly _
  · exact coeff_zero_cadjFactorPoly 1 _ _
  · exact coeff_zero_cadjFactorPoly (transCoeff M q) _ _

/-- The `BU` active product has constant coefficient `1`. -/
theorem coeff_zero_activeBUFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff 0 (activeBUFactorsList M n k hk1 hk2).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (activeBUFactorsList M n k hk1 hk2)
    (activeBUFactorsList_forall_coeff_zero_one M n k hk1 hk2)

/-- Every `UV` active factor has constant coefficient `1`. -/
theorem activeUVFactorsList_forall_coeff_zero_one
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeUVFactorsList M n k hk1 hk2) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold activeUVFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with (rfl | ⟨q, _hq, rfl⟩)
  · exact coeff_zero_cadjFactorPoly 1 _ _
  · exact coeff_zero_cadjFactorPoly (transCoeff M q) _ _

/-- The `UV` active product has constant coefficient `1`. -/
theorem coeff_zero_activeUVFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff 0 (activeUVFactorsList M n k hk1 hk2).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (activeUVFactorsList M n k hk1 hk2)
    (activeUVFactorsList_forall_coeff_zero_one M n k hk1 hk2)

/-! ## Section E: active-list two-fold Leibniz decomposition -/

/-- Generic zero criterion for a two-fold list Leibniz sum when every
factor is inert under the outer derivative and every inner derivative
is also inert under the outer derivative. -/
theorem pderivListProdSumTwice_eq_zero_of_all_outer_inert
    {N : ℕ} (u v : Fin N) (fs : List (MvPolynomial (Fin N) ℚ))
    (hv : ∀ f ∈ fs, MvPolynomial.pderiv v f = 0)
    (huv : ∀ f ∈ fs, MvPolynomial.pderiv v (MvPolynomial.pderiv u f) = 0) :
    pderivListProdSumTwice u v fs = 0 := by
  induction fs with
  | nil =>
      exact pderivListProdSumTwice_nil u v
  | cons f fs ih =>
      rw [pderivListProdSumTwice_cons]
      have hvf : MvPolynomial.pderiv v f = 0 := hv f (by simp)
      have huvf : MvPolynomial.pderiv v (MvPolynomial.pderiv u f) = 0 :=
        huv f (by simp)
      have hvfs : ∀ g ∈ fs, MvPolynomial.pderiv v g = 0 := by
        intro g hg
        exact hv g (List.mem_cons_of_mem f hg)
      have huvfs :
          ∀ g ∈ fs, MvPolynomial.pderiv v (MvPolynomial.pderiv u g) = 0 := by
        intro g hg
        exact huv g (List.mem_cons_of_mem f hg)
      have hpdv_prod : MvPolynomial.pderiv v fs.prod = 0 := by
        rw [pderiv_list_prod]
        exact pderivListProdSum_eq_zero_of_all_inert v fs hvfs
      rw [huvf, hvf, hpdv_prod, ih hvfs huvfs]
      ring

/-- Every `BU` active factor is inert under `v`. -/
theorem activeBUFactorsList_inert_at_v
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeBUFactorsList M n k hk1 hk2) :
    MvPolynomial.pderiv (vIdx n k hk2) f = 0 := by
  unfold activeBUFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl) | ⟨q, _hq, rfl⟩)
  · exact bool_at_3k_plus_2_inert_at_v n k hk2
  · exact cadj_at_3k_plus_1_inert_at_v n k hk2 1
  · exact cadj_at_3k_plus_1_inert_at_v n k hk2 (transCoeff M q)

/-- For every `BU` active factor, applying `u` then `v` gives zero. -/
theorem activeBUFactorsList_pderiv_v_pderiv_u_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeBUFactorsList M n k hk1 hk2) :
    MvPolynomial.pderiv (vIdx n k hk2)
      (MvPolynomial.pderiv (uIdx n k hk2) f) = 0 := by
  unfold activeBUFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with ((rfl | rfl) | ⟨q, _hq, rfl⟩)
  · rw [pderiv_w_pderiv_v_one_sub_boolLC_factor
      (uIdx n k hk2) (uIdx n k hk2) (vIdx n k hk2)]
    rw [if_neg]
    intro h
    exact uIdx_ne_vIdx n k hk2 h.2.symm
  · have hbu : bIdx n k hk2 ≠ uIdx n k hk2 := by
      intro h
      exact bIdx_ne_uIdx n k hk2 h
    rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X 1
      (bIdx n k hk2) (uIdx n k hk2)
      (uIdx n k hk2) (vIdx n k hk2) hbu]
    rw [if_neg]
    intro h
    rcases h with ⟨hu_b, _⟩ | ⟨_, hv_b⟩
    · exact hbu hu_b.symm
    · exact bIdx_ne_vIdx n k hk2 hv_b.symm
  · have hbu : bIdx n k hk2 ≠ uIdx n k hk2 := by
      intro h
      exact bIdx_ne_uIdx n k hk2 h
    rw [pderiv_w_pderiv_v_one_sub_C_X_mul_X (transCoeff M q)
      (bIdx n k hk2) (uIdx n k hk2)
      (uIdx n k hk2) (vIdx n k hk2) hbu]
    rw [if_neg]
    intro h
    rcases h with ⟨hu_b, _⟩ | ⟨_, hv_b⟩
    · exact hbu hu_b.symm
    · exact bIdx_ne_vIdx n k hk2 hv_b.symm

/-- The `BU` active sublist has zero `v`-Leibniz sum. -/
theorem pderivListProdSum_v_activeBU_eq_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    pderivListProdSum (vIdx n k hk2)
      (activeBUFactorsList M n k hk1 hk2) = 0 :=
  pderivListProdSum_eq_zero_of_all_inert (vIdx n k hk2)
    (activeBUFactorsList M n k hk1 hk2)
    (activeBUFactorsList_inert_at_v M n k hk1 hk2)

/-- The `BU` active sublist has zero two-fold `(u,v)` Leibniz sum. -/
theorem pderivListProdSumTwice_activeBU_eq_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
      (activeBUFactorsList M n k hk1 hk2) = 0 :=
  pderivListProdSumTwice_eq_zero_of_all_outer_inert
    (uIdx n k hk2) (vIdx n k hk2)
    (activeBUFactorsList M n k hk1 hk2)
    (activeBUFactorsList_inert_at_v M n k hk1 hk2)
    (activeBUFactorsList_pderiv_v_pderiv_u_zero M n k hk1 hk2)

/-- Decompose the active-list two-fold Leibniz expansion after the
`BU ++ UV` split.  The only remaining terms are the explicit cross
term and the `UV` two-fold self-term contribution. -/
theorem pderivListProdSumTwice_activeFactors_decompose
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
        (activeFactorsList M n k hk1 hk2) =
      pderivListProdSum (uIdx n k hk2)
          (activeBUFactorsList M n k hk1 hk2) *
        pderivListProdSum (vIdx n k hk2)
          (activeUVFactorsList M n k hk1 hk2)
      + (activeBUFactorsList M n k hk1 hk2).prod *
        pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
          (activeUVFactorsList M n k hk1 hk2) := by
  have hperm := activeFactorsList_perm_BU_UV M n k hk1 hk2
  rw [pderivListProdSumTwice_perm
    (uIdx n k hk2) (vIdx n k hk2)
    (activeFactorsList M n k hk1 hk2)
    (activeBUFactorsList M n k hk1 hk2 ++
      activeUVFactorsList M n k hk1 hk2) hperm]
  rw [pderivListProdSumTwice_append]
  rw [pderivListProdSumTwice_activeBU_eq_zero M n k hk1 hk2]
  rw [pderivListProdSum_v_activeBU_eq_zero M n k hk1 hk2]
  ring

/-! ## Section F: cross-term vanishing after the active split -/

/-- If every differentiated factor carries a common `X x` factor, then
the whole one-fold list Leibniz sum carries that `X x` factor. -/
theorem pderivListProdSum_has_X_factor_of_forall
    {N : ℕ} (x i : Fin N) (fs : List (MvPolynomial (Fin N) ℚ))
    (hfs : ∀ f ∈ fs, ∃ q : MvPolynomial (Fin N) ℚ,
      MvPolynomial.pderiv i f = MvPolynomial.X x * q) :
    ∃ q : MvPolynomial (Fin N) ℚ,
      pderivListProdSum i fs = MvPolynomial.X x * q := by
  induction fs with
  | nil =>
      refine ⟨0, ?_⟩
      rw [pderivListProdSum_nil, mul_zero]
  | cons f fs ih =>
      obtain ⟨qf, hqf⟩ := hfs f (by simp)
      have htail : ∀ g ∈ fs, ∃ q : MvPolynomial (Fin N) ℚ,
          MvPolynomial.pderiv i g = MvPolynomial.X x * q := by
        intro g hg
        exact hfs g (List.mem_cons_of_mem f hg)
      obtain ⟨qt, hqt⟩ := ih htail
      refine ⟨qf * fs.prod + f * qt, ?_⟩
      rw [pderivListProdSum_cons, hqf, hqt]
      ring

/-- The `v`-derivative of every `UV` active factor carries a common
`X_u` factor. -/
theorem activeUVFactorsList_pderiv_v_has_X_u_factor
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ activeUVFactorsList M n k hk1 hk2) :
    ∃ q : MvPolynomial (Fin n) ℚ,
      MvPolynomial.pderiv (vIdx n k hk2) f =
        MvPolynomial.X (uIdx n k hk2) * q := by
  unfold activeUVFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with (rfl | ⟨q, _hq, rfl⟩)
  · refine ⟨-(MvPolynomial.C (1 : ℚ)), ?_⟩
    change MvPolynomial.pderiv (vIdx n k hk2)
        (cadjFactorPoly 1
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)) =
      MvPolynomial.X (uIdx n k hk2) * -(MvPolynomial.C (1 : ℚ))
    rw [cadj_at_3k_plus_2_active_at_v n k hk2 1]
    ring
  · refine ⟨-(MvPolynomial.C (transCoeff M q)), ?_⟩
    change MvPolynomial.pderiv (vIdx n k hk2)
        (cadjFactorPoly (transCoeff M q)
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n)) =
      MvPolynomial.X (uIdx n k hk2) *
        -(MvPolynomial.C (transCoeff M q))
    rw [cadj_at_3k_plus_2_active_at_v n k hk2 (transCoeff M q)]
    ring

/-- The `v`-Leibniz sum of the `UV` active sublist carries a common
`X_u` factor. -/
theorem pderivListProdSum_v_activeUV_has_X_u_factor
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    ∃ q : MvPolynomial (Fin n) ℚ,
      pderivListProdSum (vIdx n k hk2)
          (activeUVFactorsList M n k hk1 hk2) =
        MvPolynomial.X (uIdx n k hk2) * q :=
  pderivListProdSum_has_X_factor_of_forall
    (uIdx n k hk2) (vIdx n k hk2)
    (activeUVFactorsList M n k hk1 hk2)
    (activeUVFactorsList_pderiv_v_has_X_u_factor M n k hk1 hk2)

/-- The explicit cross term produced by the active-list decomposition
has zero `probeLeft` coefficient after multiplication by the inert
product: it carries the stray row variable `X_u`. -/
theorem coeff_probeLeft_active_crossTerm_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk2)
              (activeBUFactorsList M n k hk1 hk2) *
            pderivListProdSum (vIdx n k hk2)
              (activeUVFactorsList M n k hk1 hk2))) = 0 := by
  obtain ⟨q, hq⟩ :=
    pderivListProdSum_v_activeUV_has_X_u_factor M n k hk1 hk2
  rw [hq]
  have hreassoc :
      ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk2)
              (activeBUFactorsList M n k hk1 hk2) *
            (MvPolynomial.X (uIdx n k hk2) * q)) :
        MvPolynomial (Fin n) ℚ) =
      MvPolynomial.X (uIdx n k hk2) *
        ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk2)
              (activeBUFactorsList M n k hk1 hk2) * q)) := by
    ring
  rw [hreassoc, probeLeft_eq]
  exact coeff_X_a_X_b_X_u_mul_zero
    (aIdx n k hk2) (bIdx n k hk2) (uIdx n k hk2)
    ((inertFactorsList M n k hk1 hk2).prod *
      (pderivListProdSum (uIdx n k hk2)
        (activeBUFactorsList M n k hk1 hk2) * q))
    (fun h => aIdx_ne_uIdx n k hk2 h.symm)
    (fun h => bIdx_ne_uIdx n k hk2 h.symm)

/-- After cross-term vanishing, the residual active coefficient reduces
to the `UV` self-term contribution multiplied by the `BU` product. -/
theorem coeff_probeLeft_activeFactors_reduce_to_UV
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
            (activeFactorsList M n k hk1 hk2)) =
      MvPolynomial.coeff (probeLeft n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          ((activeBUFactorsList M n k hk1 hk2).prod *
            pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
              (activeUVFactorsList M n k hk1 hk2))) := by
  rw [pderivListProdSumTwice_activeFactors_decompose M n k hk1 hk2]
  have hdistrib :
      ((inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk2)
              (activeBUFactorsList M n k hk1 hk2) *
            pderivListProdSum (vIdx n k hk2)
              (activeUVFactorsList M n k hk1 hk2)
          + (activeBUFactorsList M n k hk1 hk2).prod *
            pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
              (activeUVFactorsList M n k hk1 hk2)) :
        MvPolynomial (Fin n) ℚ) =
      (inertFactorsList M n k hk1 hk2).prod *
          (pderivListProdSum (uIdx n k hk2)
              (activeBUFactorsList M n k hk1 hk2) *
            pderivListProdSum (vIdx n k hk2)
              (activeUVFactorsList M n k hk1 hk2))
        + (inertFactorsList M n k hk1 hk2).prod *
          ((activeBUFactorsList M n k hk1 hk2).prod *
            pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
              (activeUVFactorsList M n k hk1 hk2)) := by
    ring
  rw [hdistrib, MvPolynomial.coeff_add]
  rw [coeff_probeLeft_active_crossTerm_zero M n k hk1 hk2]
  ring

/-! ## Section G: direct `adj/trans@3k` coefficient sum -/

/-- Transition factors of the direct probe shape `cadj@(a,b)`, indexed
by an arbitrary list of states. -/
noncomputable def transABFactorsListFrom
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates)) : List (MvPolynomial (Fin n) ℚ) :=
  qs.flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q) (aIdx n k hk2) (bIdx n k hk2)])

/-- The direct probe-shape transition factor product has constant
coefficient `1`. -/
theorem transABFactorsListFrom_forall_coeff_zero_one
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates))
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ transABFactorsListFrom M n k hk2 qs) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold transABFactorsListFrom at hf
  simp only [List.mem_flatMap, List.mem_singleton] at hf
  obtain ⟨q, _hq, rfl⟩ := hf
  exact coeff_zero_cadjFactorPoly (transCoeff M q) _ _

theorem coeff_zero_transABFactorsListFrom_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates)) :
    MvPolynomial.coeff 0 (transABFactorsListFrom M n k hk2 qs).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (transABFactorsListFrom M n k hk2 qs)
    (transABFactorsListFrom_forall_coeff_zero_one M n k hk2 qs)

/-- The list sum over `List.finRange` is the finite-type sum used by
`transCoeffSum`. -/
theorem transCoeff_finRange_list_sum
    (M : TuringMachine.DTM) :
    ((List.finRange M.numStates).map (fun q => transCoeff M q)).sum =
      transCoeffSum M := by
  unfold transCoeffSum
  rw [Fin.sum_univ_def]

/-- The direct transition probe factors contribute
`- Σ_q transCoeff M q` to the probe coefficient. -/
theorem coeff_probeLeft_transABFactorsListFrom_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates)) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (transABFactorsListFrom M n k hk2 qs).prod =
      -((qs.map (fun q => transCoeff M q)).sum) := by
  induction qs with
  | nil =>
      unfold transABFactorsListFrom
      simp [probeLeft_eq, coeff_two_mono_one]
  | cons q qs ih =>
      change MvPolynomial.coeff (probeLeft n k hk2)
          ((cadjFactorPoly (transCoeff M q)
              (aIdx n k hk2) (bIdx n k hk2) ::
            transABFactorsListFrom M n k hk2 qs).prod) =
        -(((q :: qs).map (fun q => transCoeff M q)).sum)
      rw [List.prod_cons]
      rw [coeff_probeLeft_cadj_a_b_mul_of_coeff_zero_one n k hk2
        (transCoeff M q) (transABFactorsListFrom M n k hk2 qs).prod
        (coeff_zero_transABFactorsListFrom_prod M n k hk2 qs)]
      rw [ih]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- The direct probe factors: adjacency at `(a,b)` plus all transition
analogues at `(a,b)`. -/
noncomputable def directABFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [cadjFactorPoly 1 (aIdx n k hk2) (bIdx n k hk2)] ++
    transABFactorsListFrom M n k hk2 (List.finRange M.numStates)

/-- The direct `adj/trans@3k` family contributes `-(1 + S)`, with
`S = transCoeffSum M`. -/
theorem coeff_probeLeft_directABFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (directABFactorsList M n k hk2).prod =
      -(1 + transCoeffSum M) := by
  unfold directABFactorsList
  change MvPolynomial.coeff (probeLeft n k hk2)
      ((cadjFactorPoly 1 (aIdx n k hk2) (bIdx n k hk2) ::
        transABFactorsListFrom M n k hk2 (List.finRange M.numStates)).prod) =
    -(1 + transCoeffSum M)
  rw [List.prod_cons]
  rw [coeff_probeLeft_cadj_a_b_mul_of_coeff_zero_one n k hk2 1
    (transABFactorsListFrom M n k hk2 (List.finRange M.numStates)).prod
    (coeff_zero_transABFactorsListFrom_prod M n k hk2 (List.finRange M.numStates))]
  rw [coeff_probeLeft_transABFactorsListFrom_prod]
  rw [transCoeff_finRange_list_sum]
  ring

/-! ## Section H: bool-pair contribution -/

/-- Single-variable coefficient of a booleanity factor. -/
theorem coeff_single_boolFactorPoly
    {n : ℕ} (a w : Fin n) :
    MvPolynomial.coeff (Finsupp.single a 1) (boolFactorPoly n w) =
      (if a = w then (-1 : ℚ) else 0) := by
  change MvPolynomial.coeff (Finsupp.single a 1)
      ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n w).poly) =
    (if a = w then (-1 : ℚ) else 0)
  exact coeff_X_a_one_sub_boolLC a w

/-- The two probe booleanity factors contribute the `+1` cross-talk
coefficient at `probeLeft`. -/
theorem coeff_probeLeft_bool_a_bool_b_prod
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (boolFactorPoly n (aIdx n k hk2) *
          boolFactorPoly n (bIdx n k hk2)) = 1 := by
  rw [probeLeft_eq]
  have hab : aIdx n k hk2 ≠ bIdx n k hk2 := aIdx_ne_bIdx n k hk2
  rw [coeff_two_mono_mul (aIdx n k hk2) (bIdx n k hk2) hab]
  rw [coeff_single_boolFactorPoly (aIdx n k hk2) (aIdx n k hk2)]
  rw [coeff_single_boolFactorPoly (bIdx n k hk2) (bIdx n k hk2)]
  rw [coeff_single_boolFactorPoly (bIdx n k hk2) (aIdx n k hk2)]
  rw [coeff_single_boolFactorPoly (aIdx n k hk2) (bIdx n k hk2)]
  rw [coeff_X_v_X_w_boolFactorPoly (aIdx n k hk2)
    (aIdx n k hk2) (bIdx n k hk2) hab]
  rw [coeff_zero_boolFactorPoly (aIdx n k hk2)]
  rw [coeff_X_v_X_w_boolFactorPoly (bIdx n k hk2)
    (aIdx n k hk2) (bIdx n k hk2) hab]
  rw [coeff_zero_boolFactorPoly (bIdx n k hk2)]
  simp [hab, hab.symm]

/-! ## Section I: inert product coefficient -/

/-- Single-variable coefficient of a product. -/
theorem coeff_single_mul {N : Nat} (v : Fin N)
    (p q : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff (Finsupp.single v 1) (p * q) =
      MvPolynomial.coeff (Finsupp.single v 1) p * MvPolynomial.coeff 0 q +
        MvPolynomial.coeff 0 p *
          MvPolynomial.coeff (Finsupp.single v 1) q := by
  rw [MvPolynomial.coeff_mul, Finsupp.antidiagonal_single]
  have hanti :
      Finset.antidiagonal 1 = ({(0, 1), (1, 0)} : Finset (Nat × Nat)) := by
    decide
  rw [hanti]
  simp [add_comm]

theorem coeff_single_ne_zero {N : Nat} (v : Fin N) :
    (0 : Fin N →₀ Nat) ≠ Finsupp.single v 1 := by
  intro h
  have := DFunLike.congr_fun h v
  simp at this

/-- If every factor has zero `X_v` coefficient, then so does the list
product. -/
theorem coeff_single_list_prod_eq_zero_of_forall {N : Nat} (v : Fin N)
    (ps : List (MvPolynomial (Fin N) ℚ))
    (hps : ∀ p ∈ ps, MvPolynomial.coeff (Finsupp.single v 1) p = 0) :
    MvPolynomial.coeff (Finsupp.single v 1) ps.prod = 0 := by
  induction ps with
  | nil =>
      simp [MvPolynomial.coeff_one, coeff_single_ne_zero v]
  | cons p ps ih =>
      rw [List.prod_cons, coeff_single_mul]
      rw [hps p (by simp), ih]
      · simp
      · intro q hq
        exact hps q (List.mem_cons_of_mem p hq)

theorem transABFactorsListFrom_forall_coeff_single_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates)) (v : Fin n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ transABFactorsListFrom M n k hk2 qs) :
    MvPolynomial.coeff (Finsupp.single v 1) f = 0 := by
  unfold transABFactorsListFrom at hf
  simp only [List.mem_flatMap, List.mem_singleton] at hf
  obtain ⟨q, _hq, rfl⟩ := hf
  exact coeff_X_a_one_sub_C_X_mul_X
    v (aIdx n k hk2) (bIdx n k hk2)
    (aIdx_ne_bIdx n k hk2) (transCoeff M q)

theorem coeff_single_transABFactorsListFrom_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates)) (v : Fin n) :
    MvPolynomial.coeff (Finsupp.single v 1)
      (transABFactorsListFrom M n k hk2 qs).prod = 0 :=
  coeff_single_list_prod_eq_zero_of_forall v
    (transABFactorsListFrom M n k hk2 qs)
    (transABFactorsListFrom_forall_coeff_single_zero M n k hk2 qs v)

theorem directABFactorsList_forall_coeff_zero_one
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ directABFactorsList M n k hk2) :
    MvPolynomial.coeff 0 f = 1 := by
  unfold directABFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | hf
  · exact coeff_zero_cadjFactorPoly 1 _ _
  · exact transABFactorsListFrom_forall_coeff_zero_one
      M n k hk2 (List.finRange M.numStates) f hf

theorem coeff_zero_directABFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff 0 (directABFactorsList M n k hk2).prod = 1 :=
  ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
    (directABFactorsList M n k hk2)
    (directABFactorsList_forall_coeff_zero_one M n k hk2)

theorem directABFactorsList_forall_coeff_single_zero
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (v : Fin n) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ directABFactorsList M n k hk2) :
    MvPolynomial.coeff (Finsupp.single v 1) f = 0 := by
  unfold directABFactorsList at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | hf
  · exact coeff_X_a_one_sub_C_X_mul_X
      v (aIdx n k hk2) (bIdx n k hk2)
      (aIdx_ne_bIdx n k hk2) 1
  · exact transABFactorsListFrom_forall_coeff_single_zero
      M n k hk2 (List.finRange M.numStates) v f hf

theorem coeff_single_directABFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n)
    (v : Fin n) :
    MvPolynomial.coeff (Finsupp.single v 1)
      (directABFactorsList M n k hk2).prod = 0 :=
  coeff_single_list_prod_eq_zero_of_forall v
    (directABFactorsList M n k hk2)
    (directABFactorsList_forall_coeff_single_zero M n k hk2 v)

theorem coeff_zero_bool_a_bool_b_prod
    (n k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff 0
        (boolFactorPoly n (aIdx n k hk2) *
          boolFactorPoly n (bIdx n k hk2)) = 1 := by
  have h :=
    ListProdDerivativeConstantCoeff.coeff_zero_list_prod_eq_one_of_forall
      ([boolFactorPoly n (aIdx n k hk2),
        boolFactorPoly n (bIdx n k hk2)] :
          List (MvPolynomial (Fin n) ℚ))
      (by
        intro f hf
        simp at hf
        rcases hf with rfl | rfl
        · exact coeff_zero_boolFactorPoly _
        · exact coeff_zero_boolFactorPoly _)
  simpa using h

/-- The base inert factors at the probe rows contribute `-S`: the two
booleanity factors give `+1`, while the direct adjacency/transition
family gives `-(1+S)`. -/
theorem coeff_probeLeft_boolPair_directAB_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((boolFactorPoly n (aIdx n k hk2) *
            boolFactorPoly n (bIdx n k hk2)) *
          (directABFactorsList M n k hk2).prod) =
      -transCoeffSum M := by
  rw [probeLeft_eq]
  have hab : aIdx n k hk2 ≠ bIdx n k hk2 := aIdx_ne_bIdx n k hk2
  rw [coeff_two_mono_mul (aIdx n k hk2) (bIdx n k hk2) hab]
  rw [coeff_single_directABFactorsList_prod M n k hk2 (bIdx n k hk2)]
  rw [coeff_single_directABFactorsList_prod M n k hk2 (aIdx n k hk2)]
  have hbool := coeff_probeLeft_bool_a_bool_b_prod n k hk2
  rw [probeLeft_eq] at hbool
  rw [hbool]
  rw [coeff_zero_directABFactorsList_prod M n k hk2]
  rw [coeff_zero_bool_a_bool_b_prod n k hk2]
  have hdirect := coeff_probeLeft_directABFactorsList_prod M n k hk2
  rw [probeLeft_eq] at hdirect
  rw [hdirect]
  ring

/-- Transition factors of the left-stray shape `cadj@(3k-1,3k)`. -/
noncomputable def prevABFactorsListFrom
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (qs : List (Fin M.numStates)) : List (MvPolynomial (Fin n) ℚ) :=
  qs.flatMap (fun q =>
    [cadjFactorPoly (transCoeff M q)
      (⟨3 * k - 1, by omega⟩ : Fin n)
      (⟨3 * k - 1 + 1, by omega⟩ : Fin n)])

/-- The left-stray inert family: adjacency at `(3k-1,3k)` plus all
transition analogues. -/
noncomputable def prevABFactorsList
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    List (MvPolynomial (Fin n) ℚ) :=
  [cadjFactorPoly 1
      (⟨3 * k - 1, by omega⟩ : Fin n)
      (⟨3 * k - 1 + 1, by omega⟩ : Fin n)] ++
    prevABFactorsListFrom M n k hk1 hk2 (List.finRange M.numStates)

private theorem inertTrans_flatMap_perm_split
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    ((List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q)
          (⟨3 * k - 1, by omega⟩ : Fin n)
          (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
          (⟨3 * k, by omega⟩ : Fin n)
          (⟨3 * k + 1, by omega⟩ : Fin n)])).Perm
      (prevABFactorsListFrom M n k hk1 hk2 (List.finRange M.numStates) ++
       transABFactorsListFrom M n k hk2 (List.finRange M.numStates)) := by
  unfold prevABFactorsListFrom transABFactorsListFrom aIdx bIdx
  exact (List.flatMap_append_perm (List.finRange M.numStates)
    (fun q : Fin M.numStates =>
      [cadjFactorPoly (transCoeff M q)
        (⟨3 * k - 1, by omega⟩ : Fin n)
        (⟨3 * k - 1 + 1, by omega⟩ : Fin n)])
    (fun q : Fin M.numStates =>
      [cadjFactorPoly (transCoeff M q)
        (⟨3 * k, by omega⟩ : Fin n)
        (⟨3 * k + 1, by omega⟩ : Fin n)])).symm

theorem prevABFactorsList_forall_probe_preserve
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ prevABFactorsList M n k hk1 hk2)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2) (f * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  unfold prevABFactorsList prevABFactorsListFrom at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange] at hf
  rcases hf with rfl | ⟨q, _hq, rfl⟩
  · exact coeff_probeLeft_cadj_prev_a_mul n k hk1 hk2 1 p
  · exact coeff_probeLeft_cadj_prev_a_mul n k hk1 hk2 (transCoeff M q) p

theorem coeff_probeLeft_prevABFactorsList_prod_mul
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((prevABFactorsList M n k hk1 hk2).prod * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeLeft_eq]
  exact prevABFactorsList_forall_probe_preserve M n k hk1 hk2 f hf p'

/-- The inert list splits into the left-stray preserving family and the
numeric base family. -/
theorem inertFactorsList_perm_prev_base
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    (inertFactorsList M n k hk1 hk2).Perm
      (prevABFactorsList M n k hk1 hk2 ++
        ([boolFactorPoly n (aIdx n k hk2),
          boolFactorPoly n (bIdx n k hk2)] ++
          directABFactorsList M n k hk2)) := by
  unfold inertFactorsList prevABFactorsList directABFactorsList
  unfold prevABFactorsListFrom transABFactorsListFrom aIdx bIdx
  set B0 : MvPolynomial (Fin n) ℚ := boolFactorPoly n ⟨3 * k, by omega⟩
  set B1 : MvPolynomial (Fin n) ℚ := boolFactorPoly n ⟨3 * k + 1, by omega⟩
  set P1 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (⟨3 * k - 1, by omega⟩ : Fin n)
      (⟨3 * k - 1 + 1, by omega⟩ : Fin n)
  set D1 : MvPolynomial (Fin n) ℚ :=
    cadjFactorPoly 1 (⟨3 * k, by omega⟩ : Fin n)
      (⟨3 * k + 1, by omega⟩ : Fin n)
  set FP : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q)
        (⟨3 * k - 1, by omega⟩ : Fin n)
        (⟨3 * k - 1 + 1, by omega⟩ : Fin n)])
  set FD : List (MvPolynomial (Fin n) ℚ) :=
    (List.finRange M.numStates).flatMap (fun q =>
      [cadjFactorPoly (transCoeff M q)
        (⟨3 * k, by omega⟩ : Fin n)
        (⟨3 * k + 1, by omega⟩ : Fin n)])
  have hflat :
      ((List.finRange M.numStates).flatMap (fun q =>
        [cadjFactorPoly (transCoeff M q)
          (⟨3 * k - 1, by omega⟩ : Fin n)
          (⟨3 * k - 1 + 1, by omega⟩ : Fin n),
         cadjFactorPoly (transCoeff M q)
          (⟨3 * k, by omega⟩ : Fin n)
          (⟨3 * k + 1, by omega⟩ : Fin n)])).Perm (FP ++ FD) := by
    simpa [FP, FD, prevABFactorsListFrom, transABFactorsListFrom, aIdx, bIdx]
      using inertTrans_flatMap_perm_split M n k hk1 hk2
  refine (List.Perm.append_left [B0, B1, P1, D1] hflat).trans ?_
  have hmoveP :
      (([B0, B1, P1, D1] : List (MvPolynomial (Fin n) ℚ)) ++ (FP ++ FD)).Perm
        ([P1] ++ ([B0, B1, D1] ++ (FP ++ FD))) := by
    have hmid :
        ([B0, B1] ++ P1 :: ([D1] ++ (FP ++ FD))).Perm
          (P1 :: ([B0, B1] ++ ([D1] ++ (FP ++ FD)))) :=
      List.perm_middle
    simpa [List.append_assoc] using hmid
  refine hmoveP.trans ?_
  have hswap :
      (([B0, B1, D1] : List (MvPolynomial (Fin n) ℚ)) ++ FP).Perm
        (FP ++ [B0, B1, D1]) :=
    List.perm_append_comm
  have hlift :
      ([P1] ++ (([B0, B1, D1] : List (MvPolynomial (Fin n) ℚ)) ++ FP) ++ FD).Perm
        ([P1] ++ (FP ++ [B0, B1, D1]) ++ FD) :=
    (List.Perm.append_left [P1] hswap).append_right FD
  simpa [List.append_assoc] using hlift

/-- The full inert product has probe coefficient `-S`. -/
theorem coeff_probeLeft_inertFactorsList_prod
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (inertFactorsList M n k hk1 hk2).prod =
      -transCoeffSum M := by
  have hperm := inertFactorsList_perm_prev_base M n k hk1 hk2
  rw [List.Perm.prod_eq hperm]
  rw [List.prod_append]
  rw [coeff_probeLeft_prevABFactorsList_prod_mul M n k hk1 hk2]
  have hbase :
      (([boolFactorPoly n (aIdx n k hk2),
          boolFactorPoly n (bIdx n k hk2)] ++
          directABFactorsList M n k hk2).prod :
        MvPolynomial (Fin n) ℚ) =
        (boolFactorPoly n (aIdx n k hk2) *
          boolFactorPoly n (bIdx n k hk2)) *
          (directABFactorsList M n k hk2).prod := by
    simp
    ring
  rw [hbase]
  exact coeff_probeLeft_boolPair_directAB_prod M n k hk2

/-! ## Section J: the `UV` self-term state sum -/

/-- A coefficient-parametrised list of the active `UV` factors. -/
noncomputable def uvFactorsFromCoeffs
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) : List (MvPolynomial (Fin n) ℚ) :=
  cs.map (fun c =>
    cadjFactorPoly c
      (⟨3 * k + 2, by omega⟩ : Fin n)
      (⟨3 * k + 3, hk2⟩ : Fin n))

@[simp] theorem uvFactorsFromCoeffs_nil
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n) :
    uvFactorsFromCoeffs n k hk2 [] = [] := by
  unfold uvFactorsFromCoeffs
  rfl

@[simp] theorem uvFactorsFromCoeffs_cons
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (c : ℚ) (cs : List ℚ) :
    uvFactorsFromCoeffs n k hk2 (c :: cs) =
      cadjFactorPoly c
        (⟨3 * k + 2, by omega⟩ : Fin n)
        (⟨3 * k + 3, hk2⟩ : Fin n) ::
      uvFactorsFromCoeffs n k hk2 cs := by
  unfold uvFactorsFromCoeffs
  rfl

theorem activeUVFactorsList_eq_uvFactorsFromCoeffs
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    activeUVFactorsList M n k hk1 hk2 =
      uvFactorsFromCoeffs n k hk2
        (1 :: (List.finRange M.numStates).map (fun q => transCoeff M q)) := by
  unfold activeUVFactorsList uvFactorsFromCoeffs uIdx vIdx
  simp only [List.map_cons, List.singleton_append, List.map_map]
  have htail := List.flatMap_pure_eq_map
    (fun q : Fin M.numStates =>
      cadjFactorPoly (transCoeff M q)
        (⟨3 * k + 2, by omega⟩ : Fin n)
        (⟨3 * k + 3, hk2⟩ : Fin n))
    (List.finRange M.numStates)
  simpa [Function.comp_def] using
    congrArg
      (fun t =>
        cadjFactorPoly 1
          (⟨3 * k + 2, by omega⟩ : Fin n)
          (⟨3 * k + 3, hk2⟩ : Fin n) :: t)
      htail

theorem uvFactorsFromCoeffs_forall_probe_preserve
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (f : MvPolynomial (Fin n) ℚ)
    (hf : f ∈ uvFactorsFromCoeffs n k hk2 cs)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2) (f * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  unfold uvFactorsFromCoeffs at hf
  simp only [List.mem_map] at hf
  obtain ⟨c, _hc, rfl⟩ := hf
  exact coeff_probeLeft_cadj_u_v_mul n k hk2 c p

theorem coeff_probeLeft_uvFactorsFromCoeffs_prod_mul
    (n : Nat) (k : Nat) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((uvFactorsFromCoeffs n k hk2 cs).prod * p) =
      MvPolynomial.coeff (probeLeft n k hk2) p := by
  rw [probeLeft_eq]
  apply coeff_X_a_X_b_list_prod_mul_of_forall_preserve
  intro f hf p'
  rw [← probeLeft_eq]
  exact uvFactorsFromCoeffs_forall_probe_preserve n k hk2 cs f hf p'

theorem coeff_probeLeft_inert_BU_uvFactorsFromCoeffs_twice
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n)
    (cs : List ℚ) :
    MvPolynomial.coeff (probeLeft n k hk2)
        ((inertFactorsList M n k hk1 hk2).prod *
          ((activeBUFactorsList M n k hk1 hk2).prod *
            pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
              (uvFactorsFromCoeffs n k hk2 cs))) =
      cs.sum * transCoeffSum M := by
  induction cs with
  | nil =>
      rw [uvFactorsFromCoeffs_nil, pderivListProdSumTwice_nil]
      simp
  | cons c cs ih =>
      rw [uvFactorsFromCoeffs_cons]
      rw [pderivListProdSumTwice_cons]
      rw [cadj_at_3k_plus_2_diagonal n k hk2 c]
      rw [cadj_at_3k_plus_2_active_at_u n k hk2 c]
      rw [cadj_at_3k_plus_2_active_at_v n k hk2 c]
      have hdistrib :
          ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (-(MvPolynomial.C c) *
                    (uvFactorsFromCoeffs n k hk2 cs).prod
                  + (-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                    MvPolynomial.pderiv (vIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk2 cs).prod
                  + (-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                    pderivListProdSum (uIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk2 cs)
                  + cadjFactorPoly c
                    (⟨3 * k + 2, by omega⟩ : Fin n)
                    (⟨3 * k + 3, hk2⟩ : Fin n) *
                    pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk2 cs))) :
            MvPolynomial (Fin n) ℚ) =
          (inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (-(MvPolynomial.C c) *
                  (uvFactorsFromCoeffs n k hk2 cs).prod))
            + (inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                  MvPolynomial.pderiv (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs).prod))
            + (inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                  pderivListProdSum (uIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs)))
            + (inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (cadjFactorPoly c
                  (⟨3 * k + 2, by omega⟩ : Fin n)
                  (⟨3 * k + 3, hk2⟩ : Fin n) *
                  pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs))) := by
        ring
      rw [hdistrib]
      rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
      have hdiag :
          MvPolynomial.coeff (probeLeft n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (-(MvPolynomial.C c) *
                  (uvFactorsFromCoeffs n k hk2 cs).prod))) =
            c * transCoeffSum M := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
                ((activeBUFactorsList M n k hk1 hk2).prod *
                  (-(MvPolynomial.C c) *
                    (uvFactorsFromCoeffs n k hk2 cs).prod)) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.C (-c) *
              ((uvFactorsFromCoeffs n k hk2 cs).prod *
                ((activeBUFactorsList M n k hk1 hk2).prod *
                  (inertFactorsList M n k hk1 hk2).prod)) := by
          rw [map_neg]
          ring
        rw [hreassoc, MvPolynomial.coeff_C_mul]
        rw [coeff_probeLeft_uvFactorsFromCoeffs_prod_mul n k hk2 cs]
        rw [coeff_probeLeft_activeBU_prod_mul M n k hk1 hk2]
        rw [coeff_probeLeft_inertFactorsList_prod M n k hk1 hk2]
        ring
      have hcrossV :
          MvPolynomial.coeff (probeLeft n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                  MvPolynomial.pderiv (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs).prod))) = 0 := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (vIdx n k hk2))) *
                  MvPolynomial.pderiv (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs).prod)) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (vIdx n k hk2) *
              (-(MvPolynomial.C c) *
                ((inertFactorsList M n k hk1 hk2).prod *
                  ((activeBUFactorsList M n k hk1 hk2).prod *
                    MvPolynomial.pderiv (vIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk2 cs).prod))) := by
          ring
        rw [hreassoc, probeLeft_eq]
        exact coeff_X_a_X_b_X_u_mul_zero
          (aIdx n k hk2) (bIdx n k hk2) (vIdx n k hk2)
          (-(MvPolynomial.C c) *
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                MvPolynomial.pderiv (vIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk2 cs).prod)))
          (fun h => aIdx_ne_vIdx n k hk2 h.symm)
          (fun h => bIdx_ne_vIdx n k hk2 h.symm)
      have hcrossU :
          MvPolynomial.coeff (probeLeft n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                  pderivListProdSum (uIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs)))) = 0 := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                ((-(MvPolynomial.C c * MvPolynomial.X (uIdx n k hk2))) *
                  pderivListProdSum (uIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs))) :
              MvPolynomial (Fin n) ℚ) =
            MvPolynomial.X (uIdx n k hk2) *
              (-(MvPolynomial.C c) *
                ((inertFactorsList M n k hk1 hk2).prod *
                  ((activeBUFactorsList M n k hk1 hk2).prod *
                    pderivListProdSum (uIdx n k hk2)
                      (uvFactorsFromCoeffs n k hk2 cs)))) := by
          ring
        rw [hreassoc, probeLeft_eq]
        exact coeff_X_a_X_b_X_u_mul_zero
          (aIdx n k hk2) (bIdx n k hk2) (uIdx n k hk2)
          (-(MvPolynomial.C c) *
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                pderivListProdSum (uIdx n k hk2)
                  (uvFactorsFromCoeffs n k hk2 cs))))
          (fun h => aIdx_ne_uIdx n k hk2 h.symm)
          (fun h => bIdx_ne_uIdx n k hk2 h.symm)
      have hrec :
          MvPolynomial.coeff (probeLeft n k hk2)
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (cadjFactorPoly c
                  (⟨3 * k + 2, by omega⟩ : Fin n)
                  (⟨3 * k + 3, hk2⟩ : Fin n) *
                  pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs)))) =
            cs.sum * transCoeffSum M := by
        have hreassoc :
            ((inertFactorsList M n k hk1 hk2).prod *
              ((activeBUFactorsList M n k hk1 hk2).prod *
                (cadjFactorPoly c
                  (⟨3 * k + 2, by omega⟩ : Fin n)
                  (⟨3 * k + 3, hk2⟩ : Fin n) *
                  pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs))) :
              MvPolynomial (Fin n) ℚ) =
            cadjFactorPoly c
              (⟨3 * k + 2, by omega⟩ : Fin n)
              (⟨3 * k + 3, hk2⟩ : Fin n) *
              ((inertFactorsList M n k hk1 hk2).prod *
                ((activeBUFactorsList M n k hk1 hk2).prod *
                  pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs))) := by
          ring
        rw [hreassoc]
        change MvPolynomial.coeff (probeLeft n k hk2)
            (cadjFactorPoly c (uIdx n k hk2) (vIdx n k hk2) *
              ((inertFactorsList M n k hk1 hk2).prod *
                ((activeBUFactorsList M n k hk1 hk2).prod *
                  pderivListProdSumTwice (uIdx n k hk2) (vIdx n k hk2)
                    (uvFactorsFromCoeffs n k hk2 cs)))) =
          cs.sum * transCoeffSum M
        rw [coeff_probeLeft_cadj_u_v_mul n k hk2 c]
        exact ih
      rw [hdiag, hcrossV, hcrossU, hrec]
      simp only [List.sum_cons]
      ring

/-- The residual active claim consumed by the structural decomposition. -/
theorem identityThree_residualActiveClaim
    (M : TuringMachine.DTM) (n : Nat)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    BridgeAKappaTwoIdentityThreeStructural.identityThree_residualActiveClaim
      M n k hk1 hk2 := by
  unfold BridgeAKappaTwoIdentityThreeStructural.identityThree_residualActiveClaim
  rw [coeff_probeLeft_activeFactors_reduce_to_UV M n k hk1 hk2]
  rw [activeUVFactorsList_eq_uvFactorsFromCoeffs M n k hk1 hk2]
  rw [coeff_probeLeft_inert_BU_uvFactorsFromCoeffs_twice M n k hk1 hk2]
  simp only [List.sum_cons]
  rw [transCoeff_finRange_list_sum M]
  unfold crossBlockKValue
  ring

/-- Identity (3)'s per-pair sum, obtained by combining the structural
partition theorem with the residual active computation. -/
theorem identityThree_perPairSum
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    BridgeAKappaTwoIdentityThree.identityThree_perPairSum
      M n hn htb hns k hk1 hk2 :=
  BridgeAKappaTwoIdentityThreeStructural.identityThree_perPairSum_of_decomposition
    M n hn htb hns k hk1 hk2
    (BridgeAKappaTwoIdentityThreeStructural.touchedListPoly_perm_partition
      M n k hk1 hk2)
    (identityThree_residualActiveClaim M n k hk1 hk2)

/-- Closed identity (3), no per-pair-sum hypothesis. -/
theorem kappaTwoIdentityThree
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : Nat) (hk1 : 1 ≤ k) (hk2 : 3 * k + 3 < n) :
    MvPolynomial.coeff (probeLeft n k hk2)
        (mlProj (iterDerivList (rowRight n k hk2)
          (cookLevinLocalBlockQ M n hn htb hns
            ⟨k, by rw [cook_levin_numBlocks]; omega⟩))) =
      crossBlockKValue (transCoeffSum M) :=
  BridgeAKappaTwoIdentityThree.kappaTwoIdentityThree
    M n hn htb hns k hk1 hk2
    (identityThree_perPairSum M n hn htb hns k hk1 hk2)

/-! ## Axiom audit anchors -/

#print axioms coeff_X_a_X_b_list_prod_mul_of_forall_preserve
#print axioms coeff_X_a_X_b_boolFactorPoly_mul
#print axioms coeff_X_a_X_b_cadjFactorPoly_mul_stray_fst
#print axioms coeff_X_a_X_b_cadjFactorPoly_mul_stray_snd
#print axioms coeff_probeLeft_bool_u_mul
#print axioms coeff_probeLeft_cadj_b_u_mul
#print axioms coeff_probeLeft_cadj_u_v_mul
#print axioms coeff_probeLeft_cadj_prev_a_mul
#print axioms coeff_probeLeft_cadj_a_b_mul
#print axioms coeff_probeLeft_cadj_a_b_mul_of_coeff_zero_one
#print axioms activeFactorsList_perm_BU_UV
#print axioms activeBUFactorsList_forall_probe_preserve
#print axioms activeUVFactorsList_forall_probe_preserve
#print axioms coeff_probeLeft_activeBU_prod_mul
#print axioms coeff_probeLeft_activeUV_prod_mul
#print axioms inertFactorsList_forall_coeff_zero_one
#print axioms coeff_zero_inertFactorsList_prod
#print axioms activeBUFactorsList_forall_coeff_zero_one
#print axioms coeff_zero_activeBUFactorsList_prod
#print axioms activeUVFactorsList_forall_coeff_zero_one
#print axioms coeff_zero_activeUVFactorsList_prod
#print axioms pderivListProdSumTwice_eq_zero_of_all_outer_inert
#print axioms activeBUFactorsList_inert_at_v
#print axioms activeBUFactorsList_pderiv_v_pderiv_u_zero
#print axioms pderivListProdSum_v_activeBU_eq_zero
#print axioms pderivListProdSumTwice_activeBU_eq_zero
#print axioms pderivListProdSumTwice_activeFactors_decompose
#print axioms pderivListProdSum_has_X_factor_of_forall
#print axioms activeUVFactorsList_pderiv_v_has_X_u_factor
#print axioms pderivListProdSum_v_activeUV_has_X_u_factor
#print axioms coeff_probeLeft_active_crossTerm_zero
#print axioms coeff_probeLeft_activeFactors_reduce_to_UV
#print axioms transCoeff_finRange_list_sum
#print axioms transABFactorsListFrom_forall_coeff_zero_one
#print axioms coeff_zero_transABFactorsListFrom_prod
#print axioms coeff_probeLeft_transABFactorsListFrom_prod
#print axioms coeff_probeLeft_directABFactorsList_prod
#print axioms coeff_single_boolFactorPoly
#print axioms coeff_probeLeft_bool_a_bool_b_prod
#print axioms coeff_single_mul
#print axioms coeff_single_list_prod_eq_zero_of_forall
#print axioms transABFactorsListFrom_forall_coeff_single_zero
#print axioms coeff_single_transABFactorsListFrom_prod
#print axioms directABFactorsList_forall_coeff_zero_one
#print axioms coeff_zero_directABFactorsList_prod
#print axioms directABFactorsList_forall_coeff_single_zero
#print axioms coeff_single_directABFactorsList_prod
#print axioms coeff_zero_bool_a_bool_b_prod
#print axioms coeff_probeLeft_boolPair_directAB_prod
#print axioms prevABFactorsList_forall_probe_preserve
#print axioms coeff_probeLeft_prevABFactorsList_prod_mul
#print axioms inertFactorsList_perm_prev_base
#print axioms coeff_probeLeft_inertFactorsList_prod
#print axioms activeUVFactorsList_eq_uvFactorsFromCoeffs
#print axioms uvFactorsFromCoeffs_forall_probe_preserve
#print axioms coeff_probeLeft_uvFactorsFromCoeffs_prod_mul
#print axioms coeff_probeLeft_inert_BU_uvFactorsFromCoeffs_twice
#print axioms identityThree_residualActiveClaim
#print axioms identityThree_perPairSum
#print axioms kappaTwoIdentityThree

end BridgeAKappaTwoIdentityThreeResidualActive

end PallLean.Paper93.Paper283
