import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFunctionResidualObserver

/-!
# The observer boundary is not formula-specific: a branching-program width lower bound

The Nečiporuk boundary `log₂ #{subfunctions on a block}` is a property of the **function**, not of any
representation.  The formula counting lemma bounds it by formula size; here we bound the *same* quantity by the
**width** of an oblivious branching program, showing the observer boundary lower-bounds a genuinely different
model.

We use an oblivious leveled branching program of width `w` (at level `ℓ` it reads variable `var ℓ` and applies a
transition `δ ℓ` on the `w` states).  If it reads a block `S` in a *contiguous* range of levels `[a, a+s)` (and
no `S`-variable elsewhere), then fixing the variables outside `S` collapses:

* the **prefix** `[0,a)` (reads non-`S`) to a single entry state `e ∈ Fin w`;
* the **suffix** `[a+s, len)` (reads non-`S`) to an exit-labeling `Fin w → Bool`.

The `S`-subfunction is `x ↦ exit(mid(e, x))` with `mid` fixed, so it is determined by the pair
`(e, exit) : Fin w × (Fin w → Bool)`.  Hence `#subfunctions ≤ w · 2^w`, and:

* `bp_card_funResiduals_le` — `#{subfunctions on S} ≤ w · 2^w`;
* `bp_boundary_le` — `log₂ #{subfunctions on S} ≤ 2w`;
* `hardF_bp_width_ge` — any such BP computing `hardF` (reading an address block contiguously) needs width
  `w` with `2^b − 1 ≤ 2w`, i.e. `w ≥ (2^b − 1)/2` — **exponential**.

The same block boundary `2^b − 1` that gave a super-linear *formula-size* bound (`hardF_litCount_lower`) gives an
*exponential width* bound for oblivious BPs.  One function property, two models.

## Honest scope

A restricted lower bound (oblivious leveled BP, block read contiguously) for an explicit function, demonstrating
the boundary's model-independence.  No separation, no new complexity-class bound.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BranchingProgram

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.FunctionResidualObserver

variable {n w : ℕ}

/-- An **oblivious leveled branching program** of width `w`. -/
structure LevBP (n w : ℕ) where
  /-- Number of levels. -/
  len : ℕ
  /-- Variable read at each level. -/
  var : ℕ → Fin n
  /-- State transition at each level (on the read bit). -/
  δ : ℕ → Fin w → Bool → Fin w
  /-- Start state. -/
  start : Fin w
  /-- Accepting states. -/
  accept : Fin w → Bool

/-- State after running the first `ℓ` levels from the start. -/
def LevBP.runUpto (P : LevBP n w) (y : Fin n → Bool) : ℕ → Fin w
  | 0 => P.start
  | ℓ + 1 => P.δ ℓ (P.runUpto y ℓ) (y (P.var ℓ))

/-- State after running `k` levels starting at level `j` from state `e`. -/
def LevBP.runFrom (P : LevBP n w) (y : Fin n → Bool) (e : Fin w) (j : ℕ) : ℕ → Fin w
  | 0 => e
  | k + 1 => P.δ (j + k) (P.runFrom y e j k) (y (P.var (j + k)))

/-- The function the program computes. -/
def LevBP.eval (P : LevBP n w) (y : Fin n → Bool) : Bool :=
  P.accept (P.runUpto y P.len)

/-- Running `j + k` levels = running `k` levels from the state after `j` levels. -/
theorem LevBP.runUpto_add (P : LevBP n w) (y : Fin n → Bool) (j k : ℕ) :
    P.runUpto y (j + k) = P.runFrom y (P.runUpto y j) j k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show P.δ (j + k) (P.runUpto y (j + k)) (y (P.var (j + k)))
         = P.δ (j + k) (P.runFrom y (P.runUpto y j) j k) (y (P.var (j + k)))
      rw [ih]

/-- **Prefix independence.**  If the first `ℓ` levels all read non-`S` variables, the state after them is
independent of the free `S`-part. -/
theorem LevBP.runUpto_congr (P : LevBP n w) (S : Finset (Fin n)) (α x x' : Fin n → Bool) (ℓ : ℕ)
    (h : ∀ j < ℓ, P.var j ∉ S) :
    P.runUpto (fun i => if i ∈ S then x i else α i) ℓ
      = P.runUpto (fun i => if i ∈ S then x' i else α i) ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
      show P.δ ℓ (P.runUpto _ ℓ) _ = P.δ ℓ (P.runUpto _ ℓ) _
      rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]
      congr 1
      simp only [if_neg (h ℓ (Nat.lt_succ_self ℓ))]

/-- **Mid independence.**  A segment reading only `S`-variables is independent of the outside setting. -/
theorem LevBP.runFrom_congr_mid (P : LevBP n w) (S : Finset (Fin n)) (α α' x : Fin n → Bool)
    (e : Fin w) (j k : ℕ) (h : ∀ i < k, P.var (j + i) ∈ S) :
    P.runFrom (fun i => if i ∈ S then x i else α i) e j k
      = P.runFrom (fun i => if i ∈ S then x i else α' i) e j k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show P.δ (j + k) (P.runFrom _ e j k) _ = P.δ (j + k) (P.runFrom _ e j k) _
      rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
      congr 1
      simp only [if_pos (h k (Nat.lt_succ_self k))]

/-- **Suffix independence.**  A segment reading only non-`S` variables is independent of the free `S`-part. -/
theorem LevBP.runFrom_congr_suffix (P : LevBP n w) (S : Finset (Fin n)) (α x x' : Fin n → Bool)
    (e : Fin w) (j k : ℕ) (h : ∀ i < k, P.var (j + i) ∉ S) :
    P.runFrom (fun i => if i ∈ S then x i else α i) e j k
      = P.runFrom (fun i => if i ∈ S then x' i else α i) e j k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show P.δ (j + k) (P.runFrom _ e j k) _ = P.δ (j + k) (P.runFrom _ e j k) _
      rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
      congr 1
      simp only [if_neg (h k (Nat.lt_succ_self k))]

/-! ## The counting lemma -/

/-- **Branching-program Nečiporuk counting.**  If an oblivious width-`w` leveled BP computes `f` and reads block
`S` exactly in the contiguous levels `[a, a+s)`, then the number of distinct subfunctions of `f` on `S` is at
most `w · 2^w`. -/
theorem bp_card_funResiduals_le (P : LevBP n w) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, P.eval x = f x) (S : Finset (Fin n)) (a s : ℕ) (has : a + s ≤ P.len)
    (hblock : ∀ ℓ, ℓ < P.len → (P.var ℓ ∈ S ↔ a ≤ ℓ ∧ ℓ < a + s)) :
    (funResiduals S f).card ≤ w * 2 ^ w := by
  classical
  have hpre : ∀ j < a, P.var j ∉ S := fun j hj => by
    rw [hblock j (by omega)]; omega
  have hmid : ∀ i < s, P.var (a + i) ∈ S := fun i hi => by
    rw [hblock (a + i) (by omega)]; omega
  have hsuf : ∀ i < P.len - (a + s), P.var (a + s + i) ∉ S := fun i hi => by
    rw [hblock (a + s + i) (by omega)]; omega
  -- reference outside value; the signature of α = (prefix entry state, suffix exit labeling)
  set d : Fin n → Bool := fun _ => false with hd
  set sig : (Fin n → Bool) → Fin w × (Fin w → Bool) :=
    (fun α => (P.runUpto (fun i => if i ∈ S then d i else α i) a,
               fun e => P.accept (P.runFrom (fun i => if i ∈ S then d i else α i) e (a + s)
                 (P.len - (a + s))))) with hsig
  -- the residual is determined by the signature
  have hdet : ∀ α : Fin n → Bool,
      (fun x : Fin n → Bool => f (fun i => if i ∈ S then x i else α i))
      = (fun x : Fin n → Bool =>
          (sig α).2 (P.runFrom (fun i => if i ∈ S then x i else d i) (sig α).1 a s)) := by
    intro α
    funext x
    simp only [hsig]
    rw [← hf]
    show P.accept (P.runUpto (fun i => if i ∈ S then x i else α i) P.len) = _
    have hlen : P.len = a + s + (P.len - (a + s)) := (Nat.add_sub_cancel' has).symm
    conv_lhs => rw [hlen, P.runUpto_add, P.runUpto_add]
    -- prefix indep of x, mid indep of α, suffix indep of x
    rw [P.runUpto_congr S α x d a hpre,
        P.runFrom_congr_mid S α d x _ a s hmid,
        P.runFrom_congr_suffix S α x d _ (a + s) (P.len - (a + s)) hsuf]
  -- every subfunction factors through its signature `sig α`
  have hsub : funResiduals S f ⊆ (Finset.univ.image sig).image
      (fun p : Fin w × (Fin w → Bool) =>
        (fun x : Fin n → Bool => p.2 (P.runFrom (fun i => if i ∈ S then x i else d i) p.1 a s))) := by
    intro g hg
    rw [mem_funRes] at hg
    obtain ⟨α, rfl⟩ := hg
    rw [Finset.mem_image]
    exact ⟨sig α, Finset.mem_image_of_mem sig (Finset.mem_univ α), (hdet α).symm⟩
  calc (funResiduals S f).card
      ≤ ((Finset.univ.image sig).image
          (fun p : Fin w × (Fin w → Bool) =>
            (fun x : Fin n → Bool => p.2 (P.runFrom (fun i => if i ∈ S then x i else d i) p.1 a s)))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.image sig).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin w × (Fin w → Bool))).card := Finset.card_le_univ _
    _ = w * 2 ^ w := by
        simp [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **Boundary bound.**  `log₂ #{subfunctions on S} ≤ 2w`. -/
theorem bp_boundary_le (P : LevBP n w) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, P.eval x = f x) (S : Finset (Fin n)) (a s : ℕ) (has : a + s ≤ P.len)
    (hblock : ∀ ℓ, ℓ < P.len → (P.var ℓ ∈ S ↔ a ≤ ℓ ∧ ℓ < a + s)) :
    Nat.log 2 ((funResiduals S f).card) ≤ 2 * w := by
  have hle : (funResiduals S f).card ≤ 2 ^ (2 * w) := by
    calc (funResiduals S f).card ≤ w * 2 ^ w := bp_card_funResiduals_le P f hf S a s has hblock
      _ ≤ 2 ^ w * 2 ^ w := by
          have hw : w ≤ 2 ^ w := Nat.le_of_lt (Nat.lt_two_pow_self)
          exact Nat.mul_le_mul_right _ hw
      _ = 2 ^ (2 * w) := by rw [← pow_add, two_mul]
  calc Nat.log 2 ((funResiduals S f).card)
      ≤ Nat.log 2 (2 ^ (2 * w)) := Nat.log_mono_right hle
    _ = 2 * w := Nat.log_pow (by norm_num) _

/-! ## Exponential width for the explicit hard function -/

/-- **Function-level per-block subfunction count for `hardF`.**  The `c0`-free data tables inject into the
subfunctions of `hardF` on an address block (via `hardF_merge`), so there are at least `2^{2^b − 1}` of them. -/
theorem card_funResiduals_hardF_ge {b m : ℕ} (k : Fin m) :
    2 ^ (Dsize b - 1) ≤ (funResiduals (blockS k) (hardF (b := b) (m := m))).card := by
  classical
  rw [← filter_c0_false_card]
  refine Finset.card_le_card_of_injOn
    (fun t => (fun x => hardF (fun i => if i ∈ blockS k then x i else mkt t i))) ?_ ?_
  · intro t _
    exact Finset.mem_coe.mpr (mem_funRes.mpr ⟨mkt t, rfl⟩)
  · intro t ht t' ht' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    funext c
    have hc := congrFun heq (wit k c)
    dsimp only at hc
    rw [hardF_merge k c t ht, hardF_merge k c t' ht'] at hc
    exact hc

/-- **Exponential width lower bound for `hardF`.**  Any oblivious width-`w` leveled BP computing `hardF` that
reads an address block in a contiguous level range needs `2^b − 1 ≤ 2w`, i.e. width `w ≥ (2^b − 1)/2` —
exponential in the block length `b`.  The *same* address-block boundary `2^b − 1` that gave a super-linear
formula-size bound (`hardF_litCount_lower`) gives an exponential width bound here: one function property, two
models. -/
theorem hardF_bp_width_ge {b m w : ℕ} (k : Fin m) (P : LevBP (nn b m) w)
    (hP : ∀ x, P.eval x = hardF x) (a s : ℕ) (has : a + s ≤ P.len)
    (hblock : ∀ ℓ, ℓ < P.len → (P.var ℓ ∈ blockS k ↔ a ≤ ℓ ∧ ℓ < a + s)) :
    Dsize b - 1 ≤ 2 * w := by
  have h1 := bp_boundary_le P (hardF (b := b) (m := m)) hP (blockS k) a s has hblock
  have h2 : Dsize b - 1 ≤ Nat.log 2 ((funResiduals (blockS k) (hardF (b := b) (m := m))).card) := by
    calc Dsize b - 1 = Nat.log 2 (2 ^ (Dsize b - 1)) := (Nat.log_pow (by norm_num) _).symm
      _ ≤ Nat.log 2 ((funResiduals (blockS k) (hardF (b := b) (m := m))).card) :=
        Nat.log_mono_right (card_funResiduals_hardF_ge k)
  omega

end PallLean.Paper93.DeepMath.PathB.BranchingProgram

#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgram.bp_card_funResiduals_le
#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgram.hardF_bp_width_ge
#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgram.bp_boundary_le
