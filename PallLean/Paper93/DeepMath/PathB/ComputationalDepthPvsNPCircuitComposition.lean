import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal

/-!
# Circuit composition and closure of `AC⁰[p]` under substitution — brick 2 of the cross-model bridge

The cross-model bridge needs to compose a claimed `AC⁰[p]` SAT-decider circuit with the (`AC⁰`, brick 1)
reduction map, and conclude the composite is still an `AC⁰[p]` circuit computing the hard function.  The
missing operation is **substitution**: replacing each input wire `i` of a circuit `C : BoolCircuitSyntax n`
by a subcircuit `f i : BoolCircuitSyntax k`.  This file:

* defines `subst C f : BoolCircuitSyntax k`;
* proves the **composition-eval identity** `eval (subst C f) σ = eval C (fun i => eval (f i) σ)`;
* proves **closure of `AC⁰[p]` (and `AC⁰`) under substitution**: substituting `AC⁰[p]` subcircuits into an
  `AC⁰[p]` circuit yields an `AC⁰[p]` circuit;
* proves a **depth bound** `depth (subst C f) ≤ depth C + max_i depth (f i)`.

These are the genuine composition-closure facts one needs to push a lower bound backwards along a reduction:
if `MOD_q` reduces to SAT by an `AC⁰` map and SAT had an `AC⁰[p]` circuit, the composite would be an
`AC⁰[p]` circuit for `MOD_q`, contradicting the prime capstone.

## Honest scope

Brick 2: substitution on `BoolCircuitSyntax` and closure of `AC⁰[p]`/`AC⁰` under it, with a depth bound.
Real classical circuit mathematics, `sorry`-free.  It supplies the *composition* half of the bridge; the
remaining bricks — realising the reduction map itself as a concrete `AC⁰` circuit family over the CNF
bit-encoding, and assembling the `RestrictedCapstoneTransfer` instance — are separate.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPCircuitComposition

open PallLean.Paper93.DeepMath.PathB
open BoolCircuitSyntax

/-! ## A size-bounded strong induction principle for the nested inductive -/

/-- The initial accumulator only grows under the size fold. -/
theorem foldl_size_ge {n : Nat} (Cs : List (BoolCircuitSyntax n)) (acc : Nat) :
    acc ≤ Cs.foldl (fun s C => s + C.size) acc := by
  induction Cs generalizing acc with
  | nil => simp
  | cons d Cs ih =>
    rw [List.foldl_cons]
    have := ih (acc + d.size)
    omega

/-- Each child's size is at most the size fold of the child list. -/
theorem size_le_foldl {n : Nat} (Cs : List (BoolCircuitSyntax n)) :
    ∀ (acc : Nat) (c : BoolCircuitSyntax n), c ∈ Cs →
      c.size ≤ Cs.foldl (fun s C => s + C.size) acc := by
  induction Cs with
  | nil => intro acc c hc; simp at hc
  | cons d Cs ih =>
    intro acc c hc
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hc with rfl | hc'
    · have := foldl_size_ge Cs (acc + c.size)
      omega
    · exact ih (acc + d.size) c hc'

/-- **Custom induction for `BoolCircuitSyntax`** (size-bounded strong induction): in the list-gate cases the
hypothesis ranges over every child `c ∈ Cs`. -/
@[elab_as_elim]
theorem rec_size {n : Nat} {motive : BoolCircuitSyntax n → Prop}
    (const : ∀ b, motive (.const b))
    (input : ∀ i, motive (.input i))
    (not : ∀ C, motive C → motive (.not C))
    (andGate : ∀ Cs, (∀ C ∈ Cs, motive C) → motive (.andGate Cs))
    (orGate : ∀ Cs, (∀ C ∈ Cs, motive C) → motive (.orGate Cs))
    (modGate : ∀ q r Cs, (∀ C ∈ Cs, motive C) → motive (.modGate q r Cs)) :
    ∀ C, motive C := by
  have H : ∀ k, ∀ C : BoolCircuitSyntax n, C.size ≤ k → motive C := by
    intro k
    induction k with
    | zero => intro C hC; exact absurd hC (by have := BoolCircuitSyntax.size_pos C; omega)
    | succ k ih =>
      intro C hC
      cases C with
      | const b => exact const b
      | input i => exact input i
      | not C => simp only [BoolCircuitSyntax.size] at hC; exact not C (ih C (by omega))
      | andGate Cs =>
        simp only [BoolCircuitSyntax.size] at hC
        exact andGate Cs (fun c hc => ih c (by have := size_le_foldl Cs 0 c hc; omega))
      | orGate Cs =>
        simp only [BoolCircuitSyntax.size] at hC
        exact orGate Cs (fun c hc => ih c (by have := size_le_foldl Cs 0 c hc; omega))
      | modGate q r Cs =>
        simp only [BoolCircuitSyntax.size] at hC
        exact modGate q r Cs (fun c hc => ih c (by have := size_le_foldl Cs 0 c hc; omega))
  intro C
  exact H C.size C (Nat.le_refl _)

/-! ## Substitution -/

/-- Substitute a subcircuit `f i : BoolCircuitSyntax k` for each input wire `i` of `C`. -/
def subst {n k : Nat} : BoolCircuitSyntax n → (Fin n → BoolCircuitSyntax k) → BoolCircuitSyntax k
  | .const b, _ => .const b
  | .input i, f => f i
  | .not C, f => .not (subst C f)
  | .andGate Cs, f => .andGate (Cs.map (fun C => subst C f))
  | .orGate Cs, f => .orGate (Cs.map (fun C => subst C f))
  | .modGate q r Cs, f => .modGate q r (Cs.map (fun C => subst C f))

/-! ## Substitution size accounting -/

/-- The size fold is the initial accumulator plus the sum of the child sizes. -/
theorem foldl_size_eq {n : Nat} (Cs : List (BoolCircuitSyntax n)) (a : Nat) :
    Cs.foldl (fun s C => s + C.size) a = a + (Cs.map BoolCircuitSyntax.size).sum := by
  induction Cs generalizing a with
  | nil => simp
  | cons c cs ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

/-- **Substitution size bound.** If every input replacement has size at most `M`, with `M ≥ 1`,
then substituting them into `C` increases size by at most a factor of `M`. -/
theorem subst_size_le {n k : Nat} (f : Fin n → BoolCircuitSyntax k) (M : Nat)
    (hM : ∀ i, (f i).size ≤ M) (hM1 : 1 ≤ M) :
    ∀ C : BoolCircuitSyntax n, (subst C f).size ≤ C.size * M := by
  intro C
  induction C using rec_size with
  | const b => simp only [subst, BoolCircuitSyntax.size, one_mul]; exact hM1
  | input i => simpa only [subst, BoolCircuitSyntax.size, one_mul] using hM i
  | not C ih => simp only [subst, BoolCircuitSyntax.size]; nlinarith
  | andGate Cs ih =>
      have hsum : ((Cs.map (fun c => subst c f)).map BoolCircuitSyntax.size).sum
          ≤ (Cs.map BoolCircuitSyntax.size).sum * M := by
        rw [List.map_map, ← List.sum_map_mul_right]
        exact List.sum_le_sum (fun c hc => ih c hc)
      simp only [subst, BoolCircuitSyntax.size, foldl_size_eq]
      nlinarith
  | orGate Cs ih =>
      have hsum : ((Cs.map (fun c => subst c f)).map BoolCircuitSyntax.size).sum
          ≤ (Cs.map BoolCircuitSyntax.size).sum * M := by
        rw [List.map_map, ← List.sum_map_mul_right]
        exact List.sum_le_sum (fun c hc => ih c hc)
      simp only [subst, BoolCircuitSyntax.size, foldl_size_eq]
      nlinarith
  | modGate q r Cs ih =>
      have hsum : ((Cs.map (fun c => subst c f)).map BoolCircuitSyntax.size).sum
          ≤ (Cs.map BoolCircuitSyntax.size).sum * M := by
        rw [List.map_map, ← List.sum_map_mul_right]
        exact List.sum_le_sum (fun c hc => ih c hc)
      simp only [subst, BoolCircuitSyntax.size, foldl_size_eq]
      nlinarith

/-! ## Composition-eval identity -/

/-- **The composition identity:** evaluating a substitution equals evaluating the outer circuit on the
pointwise-evaluated inner circuits. -/
theorem eval_subst {n k : Nat} (C : BoolCircuitSyntax n) (f : Fin n → BoolCircuitSyntax k)
    (σ : Fin k → Bool) :
    (subst C f).eval σ = C.eval (fun i => (f i).eval σ) := by
  induction C using rec_size with
  | const b => simp only [subst, BoolCircuitSyntax.eval]
  | input i => simp only [subst, BoolCircuitSyntax.eval]
  | not C ih => simp only [subst, BoolCircuitSyntax.eval, ih]
  | andGate Cs ih =>
    simp only [subst, BoolCircuitSyntax.eval, List.map_map]
    refine congrArg (fun l : List Bool => l.all id) ?_
    apply List.map_congr_left
    intro c hc
    exact ih c hc
  | orGate Cs ih =>
    simp only [subst, BoolCircuitSyntax.eval, List.map_map]
    refine congrArg (fun l : List Bool => l.any id) ?_
    apply List.map_congr_left
    intro c hc
    exact ih c hc
  | modGate q r Cs ih =>
    simp only [subst, BoolCircuitSyntax.eval, List.map_map]
    refine congrArg (fun l => decide (((List.filter id l).length) % q = r % q)) ?_
    apply List.map_congr_left
    intro c hc
    exact ih c hc

/-! ## Closure of `AC⁰[p]` and `AC⁰` under substitution -/

/-- **`AC⁰[p]` is closed under substitution by `AC⁰[p]` subcircuits.** -/
theorem isAC0pSyntax_subst {n k : Nat} (p : Nat) (C : BoolCircuitSyntax n)
    (f : Fin n → BoolCircuitSyntax k) (hf : ∀ i, (f i).IsAC0pSyntax p) :
    C.IsAC0pSyntax p → (subst C f).IsAC0pSyntax p := by
  induction C using rec_size with
  | const b => intro _; simp only [subst, BoolCircuitSyntax.IsAC0pSyntax]
  | input i => intro _; simp only [subst]; exact hf i
  | not C ih =>
    intro hC
    simp only [subst, BoolCircuitSyntax.IsAC0pSyntax] at hC ⊢
    exact ih hC
  | andGate Cs ih =>
    intro hC
    simp only [subst, BoolCircuitSyntax.IsAC0pSyntax] at hC ⊢
    intro D hD
    rcases List.mem_map.mp hD with ⟨c, hc, rfl⟩
    exact ih c hc (hC c hc)
  | orGate Cs ih =>
    intro hC
    simp only [subst, BoolCircuitSyntax.IsAC0pSyntax] at hC ⊢
    intro D hD
    rcases List.mem_map.mp hD with ⟨c, hc, rfl⟩
    exact ih c hc (hC c hc)
  | modGate q r Cs ih =>
    intro hC
    simp only [subst, BoolCircuitSyntax.IsAC0pSyntax] at hC ⊢
    refine ⟨hC.1, ?_⟩
    intro D hD
    rcases List.mem_map.mp hD with ⟨c, hc, rfl⟩
    exact ih c hc (hC.2 c hc)

/-- **`AC⁰` is closed under substitution by `AC⁰` subcircuits.** -/
theorem isAC0Syntax_subst {n k : Nat} (C : BoolCircuitSyntax n)
    (f : Fin n → BoolCircuitSyntax k) (hf : ∀ i, (f i).IsAC0Syntax) :
    C.IsAC0Syntax → (subst C f).IsAC0Syntax := by
  induction C using rec_size with
  | const b => intro _; simp only [subst, BoolCircuitSyntax.IsAC0Syntax]
  | input i => intro _; simp only [subst]; exact hf i
  | not C ih =>
    intro hC
    simp only [subst, BoolCircuitSyntax.IsAC0Syntax] at hC ⊢
    exact ih hC
  | andGate Cs ih =>
    intro hC
    simp only [subst, BoolCircuitSyntax.IsAC0Syntax] at hC ⊢
    intro D hD
    rcases List.mem_map.mp hD with ⟨c, hc, rfl⟩
    exact ih c hc (hC c hc)
  | orGate Cs ih =>
    intro hC
    simp only [subst, BoolCircuitSyntax.IsAC0Syntax] at hC ⊢
    intro D hD
    rcases List.mem_map.mp hD with ⟨c, hc, rfl⟩
    exact ih c hc (hC c hc)
  | modGate q r Cs _ =>
    intro hC
    simp only [BoolCircuitSyntax.IsAC0Syntax] at hC

/-! ## Depth bound under substitution -/

/-- Fold-max of the substituted child list is bounded by fold-max of the originals plus `D`, given each
child's substitution grows depth by at most `D`. -/
theorem foldl_max_depth_subst_le {n k : Nat} (D : Nat) (f : Fin n → BoolCircuitSyntax k)
    (Cs : List (BoolCircuitSyntax n))
    (h : ∀ c ∈ Cs, (subst c f).depth ≤ c.depth + D) :
    ∀ a b, a ≤ b + D →
      (Cs.map (fun C => subst C f)).foldl (fun m C => max m C.depth) a
        ≤ Cs.foldl (fun m C => max m C.depth) b + D := by
  induction Cs with
  | nil => intro a b hab; simpa using hab
  | cons c Cs ih =>
    intro a b hab
    simp only [List.map_cons, List.foldl_cons]
    refine ih (fun d hd => h d (List.mem_cons_of_mem c hd)) _ _ ?_
    have hc := h c (by simp)
    have h1 : a ≤ max b c.depth + D :=
      le_trans hab (by have := Nat.le_max_left b c.depth; omega)
    have h2 : (subst c f).depth ≤ max b c.depth + D :=
      le_trans hc (by have := Nat.le_max_right b c.depth; omega)
    exact Nat.max_le.mpr ⟨h1, h2⟩

/-- **Depth composes additively.**  Substituting circuits of depth `≤ D` into `C` gives depth
`≤ depth C + D`. -/
theorem depth_subst_le {n k : Nat} (D : Nat) (C : BoolCircuitSyntax n)
    (f : Fin n → BoolCircuitSyntax k) (hf : ∀ i, (f i).depth ≤ D) :
    (subst C f).depth ≤ C.depth + D := by
  induction C using rec_size with
  | const b => simp [subst, BoolCircuitSyntax.depth]
  | input i => simpa [subst, BoolCircuitSyntax.depth] using hf i
  | not C ih =>
    simp only [subst, BoolCircuitSyntax.depth]
    omega
  | andGate Cs ih =>
    simp only [subst, BoolCircuitSyntax.depth]
    have hbound := foldl_max_depth_subst_le D f Cs (fun c hc => ih c hc) 0 0 (Nat.zero_le _)
    omega
  | orGate Cs ih =>
    simp only [subst, BoolCircuitSyntax.depth]
    have hbound := foldl_max_depth_subst_le D f Cs (fun c hc => ih c hc) 0 0 (Nat.zero_le _)
    omega
  | modGate q r Cs ih =>
    simp only [subst, BoolCircuitSyntax.depth]
    have hbound := foldl_max_depth_subst_le D f Cs (fun c hc => ih c hc) 0 0 (Nat.zero_le _)
    omega

end PallLean.Paper93.DeepMath.PathB.PvsNPCircuitComposition

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPCircuitComposition.eval_subst
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPCircuitComposition.subst_size_le
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPCircuitComposition.isAC0pSyntax_subst
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPCircuitComposition.isAC0Syntax_subst
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPCircuitComposition.depth_subst_le
