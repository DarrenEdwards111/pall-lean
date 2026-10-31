import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNonlinearBase

/-!
# The GF(2)-degree calculus: products are degree-subadditive

To thread the base case through a whole circuit we need the general degree bound `wire-degree ≤
2^{#nonlinear gates}`.  Its engine is that a nonlinear (product) gate at most **adds** degrees, i.e.
GF(2)-degree is subadditive under products.  This file builds that calculus.

Degree is defined recursively via finite differences (`Delta a F(x) = F(x) ⊕ F(x⊕a)`): `IsDegLe 0 F`
means `F` is constant, and `IsDegLe (d+1) F` means every `Delta a F` has degree `≤ d`.

* **`isDegLe_const` / `isDegLe_mono` / `isDegLe_xor` / `isDegLe_andConst` / `isDegLe_shift` (proved)** —
  structural closure of the degree classes.
* **`isDegLe_and` (proved)** — **the crux**: `IsDegLe d a → IsDegLe e b → IsDegLe (d+e) (a ∧ b)`
  (discrete Leibniz rule + strong induction on `d+e`).
* **`isDegLe_op` (proved)** — any binary op: degree `≤ d+e` (the `a∧b` term dominates).
* **`isDegLe_op_affine` (proved)** — an *affine* op keeps degree at `max` (no product term), so affine
  gates don't inflate degree; only nonlinear gates do.
* **`isDegLe_var` / `isDegLe_unary` (proved)** — inputs have degree ≤ 1; unary ops preserve degree.

**Honest scope.**  The degree engine.  The remaining step is circuit threading (`runFrom` induction)
plus "SAT has high degree"; together a `log₂(deg)` bound on nonlinear-gate count — real but logarithmic,
short of the full Uhlig bound.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DegreeCalculus

open PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy
open PallLean.Paper93.DeepMath.PathB.AffineSemantics
open PallLean.Paper93.DeepMath.PathB.NonlinearBase

variable {n : ℕ}

/-- The finite difference `Δ_a F(x) = F(x) ⊕ F(x⊕a)`. -/
def Delta (a : Fin n → Bool) (F : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => Bool.xor (F x) (F (fun i => Bool.xor (x i) (a i)))

/-- **GF(2)-degree ≤ d**: degree `0` = constant; degree `≤ d+1` = every first difference has degree
`≤ d`. -/
def IsDegLe : ℕ → ((Fin n → Bool) → Bool) → Prop
  | 0 => fun F => ∀ x y, F x = F y
  | d + 1 => fun F => ∀ a, IsDegLe d (Delta a F)

/-- Constants have every degree. -/
theorem isDegLe_const (d : ℕ) : ∀ b : Bool, IsDegLe d (fun _ : Fin n → Bool => b) := by
  induction d with
  | zero => intro b x y; rfl
  | succ d ih =>
    intro b a
    have hd : Delta a (fun _ : Fin n → Bool => b) = fun _ => false := by
      funext x; simp only [Delta]; exact Bool.xor_self b
    rw [hd]; exact ih false

/-- Degree bounds only weaken: `IsDegLe d ⟹ IsDegLe (d+1)`. -/
theorem isDegLe_mono : ∀ (d : ℕ) (F : (Fin n → Bool) → Bool), IsDegLe d F → IsDegLe (d + 1) F := by
  intro d
  induction d with
  | zero =>
    intro F hF a x y
    have hx : F (fun i => Bool.xor (x i) (a i)) = F x := hF _ _
    have hy : F (fun i => Bool.xor (y i) (a i)) = F y := hF _ _
    simp only [Delta, hx, hy, Bool.xor_self]
  | succ d ih =>
    intro F hF a
    exact ih (Delta a F) (hF a)

/-- Iterated monotonicity. -/
theorem isDegLe_mono_le {d d' : ℕ} (h : d ≤ d') (F : (Fin n → Bool) → Bool) (hF : IsDegLe d F) :
    IsDegLe d' F := by
  induction h with
  | refl => exact hF
  | step _ ih => exact isDegLe_mono _ _ ih

/-- `Δ_a` distributes over XOR. -/
theorem Delta_xor (a : Fin n → Bool) (f g : (Fin n → Bool) → Bool) :
    Delta a (fun x => Bool.xor (f x) (g x))
      = fun x => Bool.xor (Delta a f x) (Delta a g x) := by
  funext x; simp only [Delta]
  cases f x <;> cases f (fun i => Bool.xor (x i) (a i)) <;>
    cases g x <;> cases g (fun i => Bool.xor (x i) (a i)) <;> decide

/-- The degree classes are closed under XOR. -/
theorem isDegLe_xor : ∀ (d : ℕ) (f g : (Fin n → Bool) → Bool),
    IsDegLe d f → IsDegLe d g → IsDegLe d (fun x => Bool.xor (f x) (g x)) := by
  intro d
  induction d with
  | zero =>
    intro f g hf hg x y
    show Bool.xor (f x) (g x) = Bool.xor (f y) (g y)
    rw [hf x y, hg x y]
  | succ d ih =>
    intro f g hf hg a
    rw [Delta_xor]
    exact ih _ _ (hf a) (hg a)

/-- Closed under AND with a right constant. -/
theorem isDegLe_andConst (d : ℕ) (F : (Fin n → Bool) → Bool) (hF : IsDegLe d F) (c : Bool) :
    IsDegLe d (fun x => Bool.and (F x) c) := by
  cases c with
  | false => simp only [Bool.and_false]; exact isDegLe_const d false
  | true => simp only [Bool.and_true]; exact hF

/-- Closed under AND with a left constant. -/
theorem isDegLe_constAnd (c : Bool) (d : ℕ) (F : (Fin n → Bool) → Bool) (hF : IsDegLe d F) :
    IsDegLe d (fun x => Bool.and c (F x)) := by
  cases c with
  | false => simp only [Bool.false_and]; exact isDegLe_const d false
  | true => simp only [Bool.true_and]; exact hF

/-- `Δ_a` commutes with an input shift. -/
theorem Delta_shift (a v : Fin n → Bool) (F : (Fin n → Bool) → Bool) :
    Delta a (fun x => F (fun i => Bool.xor (x i) (v i)))
      = fun x => Delta a F (fun i => Bool.xor (x i) (v i)) := by
  funext x
  simp only [Delta]
  have harg : (fun i => Bool.xor (Bool.xor (x i) (a i)) (v i))
            = (fun i => Bool.xor (Bool.xor (x i) (v i)) (a i)) := by
    funext i; cases x i <;> cases a i <;> cases v i <;> decide
  rw [harg]

/-- Degree is preserved by an input shift. -/
theorem isDegLe_shift (v : Fin n → Bool) : ∀ (d : ℕ) (F : (Fin n → Bool) → Bool),
    IsDegLe d F → IsDegLe d (fun x => F (fun i => Bool.xor (x i) (v i))) := by
  intro d
  induction d with
  | zero => intro F hF x y; exact hF _ _
  | succ d ih =>
    intro F hF a
    rw [Delta_shift]
    exact ih (Delta a F) (hF a)

/-- **Discrete Leibniz rule**: `Δ_a(a·b) = a·(Δ_a b) ⊕ (Δ_a a)·(shift b)`. -/
theorem Delta_and (v : Fin n → Bool) (a b : (Fin n → Bool) → Bool) :
    Delta v (fun x => Bool.and (a x) (b x))
      = fun x => Bool.xor (Bool.and (a x) (Delta v b x))
          (Bool.and (Delta v a x) (b (fun i => Bool.xor (x i) (v i)))) := by
  funext x
  simp only [Delta]
  cases a x <;> cases a (fun i => Bool.xor (x i) (v i)) <;>
    cases b x <;> cases b (fun i => Bool.xor (x i) (v i)) <;> decide

/-- **THE CRUX (proved): GF(2)-degree is subadditive under products.** -/
theorem isDegLe_and :
    ∀ (N d e : ℕ), d + e ≤ N → ∀ (a b : (Fin n → Bool) → Bool),
      IsDegLe d a → IsDegLe e b → IsDegLe (d + e) (fun x => Bool.and (a x) (b x)) := by
  intro N
  induction N with
  | zero =>
    intro d e hN a b ha hb
    obtain ⟨rfl, rfl⟩ : d = 0 ∧ e = 0 := by omega
    intro x y
    show Bool.and (a x) (b x) = Bool.and (a y) (b y)
    rw [ha x y, hb x y]
  | succ N ih =>
    intro d e hN a b ha hb
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      by_cases hav : a (fun _ => false) = true
      · have hb' : (fun x => Bool.and (a x) (b x)) = b := by
          funext x; show Bool.and (a x) (b x) = b x
          rw [ha x (fun _ => false), hav, Bool.true_and]
        rw [hb']; exact isDegLe_mono_le (by omega) b hb
      · simp only [Bool.not_eq_true] at hav
        have hb' : (fun x => Bool.and (a x) (b x)) = fun _ => false := by
          funext x; show Bool.and (a x) (b x) = false
          rw [ha x (fun _ => false), hav, Bool.false_and]
        rw [hb']; exact isDegLe_const _ false
    · rcases Nat.eq_zero_or_pos e with he | he
      · subst he
        by_cases hbv : b (fun _ => false) = true
        · have ha' : (fun x => Bool.and (a x) (b x)) = a := by
            funext x; show Bool.and (a x) (b x) = a x
            rw [hb x (fun _ => false), hbv, Bool.and_true]
          rw [ha']; exact isDegLe_mono_le (by omega) a ha
        · simp only [Bool.not_eq_true] at hbv
          have ha' : (fun x => Bool.and (a x) (b x)) = fun _ => false := by
            funext x; show Bool.and (a x) (b x) = false
            rw [hb x (fun _ => false), hbv, Bool.and_false]
          rw [ha']; exact isDegLe_const _ false
      · obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
        obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
        intro v
        rw [Delta_and]
        apply isDegLe_xor
        · exact ih (d' + 1) e' (by omega) a (Delta v b) ha (hb v)
        · have hkey := ih d' (e' + 1) (by omega) (Delta v a)
            (fun x => b (fun i => Bool.xor (x i) (v i))) (ha v) (isDegLe_shift v (e' + 1) b hb)
          have hrw : d' + (e' + 1) = (d' + 1) + e' := by omega
          rw [hrw] at hkey
          exact hkey

/-- **Any binary op has degree ≤ d+e (proved).** -/
theorem isDegLe_op (op : Bool → Bool → Bool) (d e : ℕ) (a b : (Fin n → Bool) → Bool)
    (ha : IsDegLe d a) (hb : IsDegLe e b) :
    IsDegLe (d + e) (fun x => op (a x) (b x)) := by
  have hform : (fun x => op (a x) (b x)) = fun x =>
      Bool.xor (Bool.xor (Bool.xor (op false false)
        (Bool.and (Bool.xor (op false false) (op true false)) (a x)))
        (Bool.and (Bool.xor (op false false) (op false true)) (b x)))
        (Bool.and (Bool.xor (Bool.xor (Bool.xor (op false false) (op false true)) (op true false))
          (op true true)) (Bool.and (a x) (b x))) := by
    funext x; exact op_anf op (a x) (b x)
  rw [hform]
  refine isDegLe_xor _ _ _ (isDegLe_xor _ _ _ (isDegLe_xor _ _ _ ?_ ?_) ?_) ?_
  · exact isDegLe_const (d + e) (op false false)
  · exact isDegLe_mono_le (Nat.le_add_right d e) _ (isDegLe_constAnd _ d a ha)
  · exact isDegLe_mono_le (Nat.le_add_left e d) _ (isDegLe_constAnd _ e b hb)
  · exact isDegLe_constAnd _ (d + e) _ (isDegLe_and (d + e) d e (le_refl _) a b ha hb)

/-- **An affine binary op keeps the degree (proved)** — no product term, so it does not inflate. -/
theorem isDegLe_op_affine {op : Bool → Bool → Bool} (hop : IsAffineOp op) (D : ℕ)
    (a b : (Fin n → Bool) → Bool) (ha : IsDegLe D a) (hb : IsDegLe D b) :
    IsDegLe D (fun x => op (a x) (b x)) := by
  have hform : (fun x => op (a x) (b x)) = fun x =>
      Bool.xor (Bool.xor (op false false)
        (Bool.and (a x) (Bool.xor (op false false) (op true false))))
        (Bool.and (b x) (Bool.xor (op false false) (op false true))) := by
    funext x; exact op_affine_decomp hop (a x) (b x)
  rw [hform]
  refine isDegLe_xor _ _ _ (isDegLe_xor _ _ _ ?_ ?_) ?_
  · exact isDegLe_const D (op false false)
  · exact isDegLe_andConst D a ha _
  · exact isDegLe_andConst D b hb _

/-- Input projections have degree ≤ 1. -/
theorem isDegLe_var (i : Fin n) : IsDegLe 1 (fun x : Fin n → Bool => x i) := by
  intro a x y
  simp only [Delta]
  cases x i <;> cases y i <;> cases a i <;> decide

/-- Unary ops preserve degree. -/
theorem isDegLe_unary (op : Bool → Bool) (d : ℕ) (a : (Fin n → Bool) → Bool) (ha : IsDegLe d a) :
    IsDegLe d (fun x => op (a x)) := by
  have hform : (fun x => op (a x))
      = fun x => Bool.xor (op false) (Bool.and (a x) (Bool.xor (op false) (op true))) := by
    funext x; cases a x <;> cases op false <;> cases op true <;> decide
  rw [hform]
  exact isDegLe_xor _ _ _ (isDegLe_const d (op false)) (isDegLe_andConst d a ha _)

end PallLean.Paper93.DeepMath.PathB.DegreeCalculus

#print axioms PallLean.Paper93.DeepMath.PathB.DegreeCalculus.isDegLe_and
#print axioms PallLean.Paper93.DeepMath.PathB.DegreeCalculus.isDegLe_op
#print axioms PallLean.Paper93.DeepMath.PathB.DegreeCalculus.isDegLe_op_affine
