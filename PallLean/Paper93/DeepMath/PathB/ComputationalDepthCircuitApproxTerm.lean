import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitApprox
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOrPoly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGateApproxGen
import Mathlib

/-!
# The term-carrying circuit approximation (PROVED: structure + base/unary constructors)

The final wrapper packages, for each circuit `C`, a concrete approximating polynomial together with its
correctness (`ApproxOn`), degree bound (`degApprox`), and bad-set bound (`size · 2^(n-t)`):

  `CircuitApproxData p t C` — the package `⟨poly, bad, approx, degree_le, bad_le⟩`.

This file proves the package's **base and unary constructors** — the cases that are *exact* (no probabilistic
error):

  `caVar` / `caConst` — inputs and constants: the polynomial is `Xᵢ` / a constant, `bad = ∅`.
  `caNot` — negation: `1 - poly`, same bad set (via `ApproxOn.unary`-style reasoning), degree preserved.

These thread the polynomial through the easy parts of the `Circuit` recursion.  The **gate constructors** —
`AND`/`OR` (probabilistic, via `GateApprox.exists_good_forms_gen` substituting the children's polynomials into the
OR-approximator) and `MOD_p` (exact, via `modPoly`) — together with the well-founded recursion assembling them
(the pattern of `degApprox_le_pow_depth`), are the remaining core.  Once assembled, feeding the resulting
low-degree approximator on a large agreement set into `boosting_surjection` yields the Razborov–Smolensky bound.
-/

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.CircuitApprox (ApproxOn)

namespace PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

variable {n : ℕ}

/-- The circuit, as a `ZMod p`-valued function on the cube (`0/1` outputs cast into `𝔽_p`). -/
noncomputable def cf (p : ℕ) (C : Circuit n) : (Fin n → Bool) → ZMod p :=
  fun x => ((Circuit.eval x C).toNat : ZMod p)

/-- A polynomial, as a `ZMod p`-valued function on the cube (evaluated at the `0/1` point). -/
noncomputable def pf (p : ℕ) (P : MvPolynomial (Fin n) (ZMod p)) : (Fin n → Bool) → ZMod p :=
  fun x => MvPolynomial.eval (fun i => ((x i).toNat : ZMod p)) P

/-- The term-carrying approximation package for a circuit `C`: a polynomial approximating `C` off a bad set,
with degree `≤ degApprox (t(p-1)) C` and bad set `≤ size C · 2^(n-t)`. -/
structure CircuitApproxData (p t : ℕ) (C : Circuit n) where
  poly : MvPolynomial (Fin n) (ZMod p)
  bad : Finset (Fin n → Bool)
  approx : ApproxOn (cf p C) (pf p poly) bad
  degree_le : poly.totalDegree ≤ degApprox (t * (p - 1)) C
  bad_le : bad.card ≤ size C * 2 ^ (n - t)

/-- **Input constructor.**  `var i` is computed exactly by the monomial `Xᵢ`. -/
noncomputable def caVar (p t : ℕ) [Fact p.Prime] (i : Fin n) : CircuitApproxData p t (var i) where
  poly := X i
  bad := ∅
  approx := ApproxOn.exact (fun x => by simp [cf, pf, Circuit.eval_var])
  degree_le := by rw [degApprox]; exact le_of_eq (totalDegree_X i)
  bad_le := by rw [Finset.card_empty]; exact Nat.zero_le _

/-- **Constant constructor.**  `const b` is computed exactly by the constant polynomial `b.toNat`. -/
noncomputable def caConst (p t : ℕ) [Fact p.Prime] (b : Bool) :
    CircuitApproxData p t (const b : Circuit n) where
  poly := MvPolynomial.C (b.toNat : ZMod p)
  bad := ∅
  approx := ApproxOn.exact (fun x => by simp [cf, pf])
  degree_le := by rw [degApprox]; exact le_trans (le_of_eq (totalDegree_C _)) (Nat.zero_le 1)
  bad_le := by rw [Finset.card_empty]; exact Nat.zero_le _

/-- **Negation constructor.**  From an approximation of `c`, `not c` is approximated by `1 - poly` on the same bad
set: off `bad`, `1 - poly = 1 - c.eval = (!c.eval)`.  Degree is preserved. -/
noncomputable def caNot (p t : ℕ) (c : Circuit n) (d : CircuitApproxData p t c) :
    CircuitApproxData p t (not c) where
  poly := 1 - d.poly
  bad := d.bad
  approx := by
    intro x hx
    have h := d.approx x hx
    simp only [cf, pf, Circuit.eval_not, map_sub, map_one] at h ⊢
    rw [← h]
    cases Circuit.eval x c <;> simp
  degree_le := by
    rw [degApprox]
    refine le_trans (totalDegree_sub _ _) ?_
    rw [totalDegree_one]
    exact max_le (Nat.zero_le _) d.degree_le
  bad_le := by
    rw [size]
    exact le_trans d.bad_le (Nat.mul_le_mul_right _ (Nat.le_succ _))

/-- **OR-to-`Fin`-indexed bridge.**  The circuit `or cs` (a `List`-based disjunction) as an `𝔽_p`-function equals
the `OR`-indicator over the `Fin`-indexed children: `0` if every child `cs.get i` evaluates to `false`, else `1`.
This connects the `Circuit` `OR` gate to the form `OrPoly.orPoly_eval_eq_or` consumes (`b i = (cs.get i).eval x`). -/
theorem cf_or_eq (p : ℕ) (cs : List (Circuit n)) (x : Fin n → Bool) :
    cf p (or cs) x
      = if (∀ i : Fin cs.length, Circuit.eval x (cs.get i) = false) then (0 : ZMod p) else 1 := by
  rw [cf, Circuit.eval_or]
  cases hany : cs.any (Circuit.eval x) with
  | false =>
    have hcond : ∀ i : Fin cs.length, Circuit.eval x (cs.get i) = false := by
      intro i
      by_contra hi
      rw [Bool.not_eq_false] at hi
      have hT : cs.any (Circuit.eval x) = true :=
        List.any_eq_true.mpr ⟨cs.get i, List.get_mem cs i, hi⟩
      rw [hany] at hT
      exact Bool.false_ne_true hT
    rw [Bool.toNat_false, if_pos hcond]
    simp
  | true =>
    have hcond : ¬ ∀ i : Fin cs.length, Circuit.eval x (cs.get i) = false := by
      rw [List.any_eq_true] at hany
      obtain ⟨a, ha, hpa⟩ := hany
      obtain ⟨i, rfl⟩ := List.get_of_mem ha
      intro hall
      rw [hall i] at hpa
      exact Bool.false_ne_true hpa
    rw [Bool.toNat_true, if_neg hcond]
    simp

/-- **OR-gate pointwise correctness (assembled).**  At a point `x` off the children's bad sets (`hchild`: each
child's polynomial equals the child's value there) and off the gate's bad set (`hdis`: the forms do not disagree),
the gate polynomial `orPoly P Ss` evaluates to `cf (or cs)` — the `OR` of the children.  Combines `cf_or_eq` (the
circuit `OR` as the `Fin`-indexed indicator) with `OrPoly.orPoly_eval_eq_or` (the gate polynomial as that same
indicator).  This is the `ApproxOn` content of `caOr`, pointwise. -/
theorem caOr_pointwise {p t : ℕ} [Fact p.Prime] (cs : List (Circuit n))
    (P : Fin cs.length → MvPolynomial (Fin n) (ZMod p)) (Ss : Fin t → Finset (Fin cs.length))
    (x : Fin n → Bool) (hchild : ∀ i, cf p (cs.get i) x = pf p (P i) x)
    (hdis : ¬ ((∀ j, OrApprox.linForm (fun i => ((Circuit.eval x (cs.get i)).toNat : ZMod p)) (Ss j) = 0)
              ∧ (fun i => ((Circuit.eval x (cs.get i)).toNat : ZMod p)) ≠ 0)) :
    cf p (or cs) x = pf p (OrPoly.orPoly P Ss) x := by
  have hv : ∀ i, MvPolynomial.eval (fun j => ((x j).toNat : ZMod p)) (P i)
      = ((Circuit.eval x (cs.get i)).toNat : ZMod p) :=
    fun i => by simpa only [cf, pf] using (hchild i).symm
  rw [cf_or_eq, pf, OrPoly.orPoly_eval_eq_or P Ss (fun j => ((x j).toNat : ZMod p))
    (fun i => Circuit.eval x (cs.get i)) hv hdis]

/-- **OR-gate degree bound (assembled).**  If each child polynomial has degree `≤ degApprox D (cs.get i)`, then
the OR-gate polynomial `orPoly P Ss` has degree `≤ degApprox D (or cs) = D · degApproxList D cs`.  This is `caOr`'s
`degree_le` field: `orPoly_totalDegree_le` with bound `B = degApproxList D cs`, each child degree `≤ B` by
`degApprox_le_degApproxList`. -/
theorem orPoly_degree_le_or {p t : ℕ} (cs : List (Circuit n))
    (P : Fin cs.length → MvPolynomial (Fin n) (ZMod p)) (Ss : Fin t → Finset (Fin cs.length))
    (hdeg : ∀ i, (P i).totalDegree ≤ degApprox (t * (p - 1)) (cs.get i)) :
    (OrPoly.orPoly P Ss).totalDegree ≤ degApprox (t * (p - 1)) (or cs) := by
  rw [degApprox]
  exact OrPoly.orPoly_totalDegree_le P Ss (degApproxList (t * (p - 1)) cs)
    (fun i => le_trans (hdeg i) (degApprox_le_degApproxList cs (cs.get i) (List.get_mem cs i)))

/-- The sum of the children's sizes (over `Fin cs.length`) equals `sizeList cs` — needed for the `OR`/`AND` gate
bad-set card bound (`card_biUnion_le` gives `Σ child.bad.card`, bounded by `Σ size · 2^(n-t)`). -/
theorem sum_size_eq_sizeList (cs : List (Circuit n)) :
    ∑ i : Fin cs.length, size (cs.get i) = sizeList cs := by
  induction cs with
  | nil => simp [sizeList]
  | cons c cs ih =>
    rw [sizeList, ← ih]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp

/-- **AND-to-`Fin`-indexed bridge.**  The circuit `and cs` as an `𝔽_p`-function equals the `AND`-indicator over
the `Fin`-indexed children: `1` if every child evaluates to `true`, else `0`.  The AND analogue of `cf_or_eq`. -/
theorem cf_and_eq (p : ℕ) (cs : List (Circuit n)) (x : Fin n → Bool) :
    cf p (and cs) x
      = if (∀ i : Fin cs.length, Circuit.eval x (cs.get i) = true) then (1 : ZMod p) else 0 := by
  rw [cf, Circuit.eval_and]
  cases hall : cs.all (Circuit.eval x) with
  | true =>
    have hcond : ∀ i : Fin cs.length, Circuit.eval x (cs.get i) = true := by
      rw [List.all_eq_true] at hall
      intro i
      exact hall _ (List.get_mem cs i)
    rw [Bool.toNat_true, if_pos hcond]
    simp
  | false =>
    have hcond : ¬ ∀ i : Fin cs.length, Circuit.eval x (cs.get i) = true := by
      intro hall'
      have hT : cs.all (Circuit.eval x) = true := by
        rw [List.all_eq_true]
        intro a ha
        obtain ⟨i, rfl⟩ := List.get_of_mem ha
        exact hall' i
      rw [hall] at hT
      exact Bool.false_ne_true hT
    rw [Bool.toNat_false, if_neg hcond]
    simp

open Classical in
/-- **The OR-gate constructor.**  From the children's approximation data, build the `CircuitApproxData` for
`or cs`: the gate polynomial `orPoly P Ss` (children's polys substituted into the OR-approximator with forms `Ss`
chosen by `exists_forms_few_disagree`), the bad set `(⋃ child bad) ∪ (disagree set)`, and the three field proofs
(`approx` via `caOr_pointwise`, `degree_le` via `orPoly_degree_le_or`, `bad_le` via `card_biUnion_le` +
`sum_size_eq_sizeList` + the disagree count).  Requires `cs` nonempty (`1 ≤ cs.length`) and `t ≤ n`. -/
noncomputable def caOr {p t : ℕ} [Fact p.Prime] (cs : List (Circuit n))
    (hk : 1 ≤ cs.length) (htn : t ≤ n)
    (dat : ∀ i : Fin cs.length, CircuitApproxData p t (cs.get i)) :
    CircuitApproxData p t (or cs) :=
  let P : Fin cs.length → MvPolynomial (Fin n) (ZMod p) := fun i => (dat i).poly
  let v : (Fin n → Bool) → (Fin cs.length → ZMod p) :=
    fun x i => MvPolynomial.eval (fun j => ((x j).toNat : ZMod p)) (P i)
  let Ss := (GateApprox.exists_forms_few_disagree hk htn v).choose
  { poly := OrPoly.orPoly P Ss
    bad := (Finset.univ.biUnion fun i => (dat i).bad)
            ∪ Finset.univ.filter fun x => GateApprox.disagreeGen v Ss x
    approx := by
      intro x hx
      have hbu : ∀ i, x ∉ (dat i).bad := fun i hi =>
        hx (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩))
      have hfilt : ¬ GateApprox.disagreeGen v Ss x := fun hd =>
        hx (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hd⟩))
      have hchild : ∀ i, cf p (cs.get i) x = pf p (P i) x := fun i => (dat i).approx x (hbu i)
      refine caOr_pointwise cs P Ss x hchild (fun hcon => ?_)
      have hvx : v x = fun i => ((Circuit.eval x (cs.get i)).toNat : ZMod p) := by
        funext i
        have h := hchild i
        simp only [cf, pf] at h
        exact h.symm
      exact hfilt (by simp only [GateApprox.disagreeGen, hvx]; exact hcon)
    degree_le := orPoly_degree_le_or cs P Ss (fun i => (dat i).degree_le)
    bad_le := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have hbu : (Finset.univ.biUnion fun i => (dat i).bad).card ≤ sizeList cs * 2 ^ (n - t) := by
        refine le_trans Finset.card_biUnion_le ?_
        calc ∑ i : Fin cs.length, ((dat i).bad).card
            ≤ ∑ i : Fin cs.length, size (cs.get i) * 2 ^ (n - t) :=
              Finset.sum_le_sum (fun i _ => (dat i).bad_le)
          _ = (∑ i : Fin cs.length, size (cs.get i)) * 2 ^ (n - t) := by rw [← Finset.sum_mul]
          _ = sizeList cs * 2 ^ (n - t) := by rw [sum_size_eq_sizeList]
      have hf := (GateApprox.exists_forms_few_disagree hk htn v).choose_spec
      rw [size]
      calc (Finset.univ.biUnion fun i => (dat i).bad).card
              + (Finset.univ.filter fun x => GateApprox.disagreeGen v Ss x).card
          ≤ sizeList cs * 2 ^ (n - t) + 2 ^ (n - t) := Nat.add_le_add hbu hf
        _ = (sizeList cs + 1) * 2 ^ (n - t) := by ring }

/-- **AND-gate pointwise correctness (assembled).**  AND via De Morgan at the polynomial level: the AND-gate
polynomial is `1 - orPoly (fun i => 1 - Pᵢ) Ss` (the OR-approximator on the *negated* children).  Off the children's
bad sets and the gate's bad set, it evaluates to `cf (and cs)`.  Combines `cf_and_eq` with `orPoly_eval_eq_or`
applied to the negated children `b'ᵢ = ¬(cs.get i).eval x`. -/
theorem caAnd_pointwise {p t : ℕ} [Fact p.Prime] (cs : List (Circuit n))
    (P : Fin cs.length → MvPolynomial (Fin n) (ZMod p)) (Ss : Fin t → Finset (Fin cs.length))
    (x : Fin n → Bool) (hchild : ∀ i, cf p (cs.get i) x = pf p (P i) x)
    (hdis : ¬ ((∀ j, OrApprox.linForm
                (fun i => ((!Circuit.eval x (cs.get i)).toNat : ZMod p)) (Ss j) = 0)
              ∧ (fun i => ((!Circuit.eval x (cs.get i)).toNat : ZMod p)) ≠ 0)) :
    cf p (and cs) x = pf p (1 - OrPoly.orPoly (fun i => 1 - P i) Ss) x := by
  have hv : ∀ i, MvPolynomial.eval (fun j => ((x j).toNat : ZMod p)) (1 - P i)
      = ((!Circuit.eval x (cs.get i)).toNat : ZMod p) := by
    intro i
    rw [map_sub, map_one]
    have h := hchild i
    simp only [cf, pf] at h
    rw [← h]
    cases Circuit.eval x (cs.get i) <;> simp
  rw [cf_and_eq, pf, map_sub, map_one,
    OrPoly.orPoly_eval_eq_or (fun i => 1 - P i) Ss (fun j => ((x j).toNat : ZMod p))
      (fun i => !Circuit.eval x (cs.get i)) hv hdis]
  by_cases h : ∀ i, Circuit.eval x (cs.get i) = true
  · rw [if_pos h, if_pos (fun i => by rw [h i]; rfl)]
    simp
  · rw [if_neg h, if_neg ?_]
    · simp
    · intro hc
      exact h (fun i => by have := hc i; cases hb : Circuit.eval x (cs.get i) <;> simp_all)

open Classical in
/-- **The AND-gate constructor.**  AND via De Morgan at the polynomial level: from the children's data, build the
`CircuitApproxData` for `and cs` with polynomial `1 - orPoly (fun i => 1 - Pᵢ) Ss` (the OR-approximator on the
negated children, then negated).  Mirrors `caOr`: `Ss` from `exists_forms_few_disagree` on the negated value
vector, bad set `(⋃ child bad) ∪ (disagree set)`, fields via `caAnd_pointwise` / `orPoly_totalDegree_le` /
`card_biUnion_le` + `sum_size_eq_sizeList`. -/
noncomputable def caAnd {p t : ℕ} [Fact p.Prime] (cs : List (Circuit n))
    (hk : 1 ≤ cs.length) (htn : t ≤ n)
    (dat : ∀ i : Fin cs.length, CircuitApproxData p t (cs.get i)) :
    CircuitApproxData p t (and cs) :=
  let P : Fin cs.length → MvPolynomial (Fin n) (ZMod p) := fun i => (dat i).poly
  let v : (Fin n → Bool) → (Fin cs.length → ZMod p) :=
    fun x i => MvPolynomial.eval (fun j => ((x j).toNat : ZMod p)) (1 - P i)
  let Ss := (GateApprox.exists_forms_few_disagree hk htn v).choose
  { poly := 1 - OrPoly.orPoly (fun i => 1 - P i) Ss
    bad := (Finset.univ.biUnion fun i => (dat i).bad)
            ∪ Finset.univ.filter fun x => GateApprox.disagreeGen v Ss x
    approx := by
      intro x hx
      have hbu : ∀ i, x ∉ (dat i).bad := fun i hi =>
        hx (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩))
      have hfilt : ¬ GateApprox.disagreeGen v Ss x := fun hd =>
        hx (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hd⟩))
      have hchild : ∀ i, cf p (cs.get i) x = pf p (P i) x := fun i => (dat i).approx x (hbu i)
      refine caAnd_pointwise cs P Ss x hchild (fun hcon => ?_)
      have hvx : v x = fun i => ((!Circuit.eval x (cs.get i)).toNat : ZMod p) := by
        funext i
        show MvPolynomial.eval (fun j => ((x j).toNat : ZMod p)) (1 - P i) = _
        rw [map_sub, map_one]
        have h := hchild i
        simp only [cf, pf] at h
        rw [← h]
        cases Circuit.eval x (cs.get i) <;> simp
      exact hfilt (by simp only [GateApprox.disagreeGen, hvx]; exact hcon)
    degree_le := by
      rw [degApprox]
      refine le_trans (totalDegree_sub _ _) ?_
      rw [totalDegree_one]
      refine max_le (Nat.zero_le _) ?_
      exact OrPoly.orPoly_totalDegree_le (fun i => 1 - P i) Ss (degApproxList (t * (p - 1)) cs)
        (fun i => by
          refine le_trans (totalDegree_sub _ _) ?_
          rw [totalDegree_one]
          exact max_le (Nat.zero_le _)
            (le_trans (dat i).degree_le (degApprox_le_degApproxList cs (cs.get i) (List.get_mem cs i))))
    bad_le := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have hbu : (Finset.univ.biUnion fun i => (dat i).bad).card ≤ sizeList cs * 2 ^ (n - t) := by
        refine le_trans Finset.card_biUnion_le ?_
        calc ∑ i : Fin cs.length, ((dat i).bad).card
            ≤ ∑ i : Fin cs.length, size (cs.get i) * 2 ^ (n - t) :=
              Finset.sum_le_sum (fun i _ => (dat i).bad_le)
          _ = (∑ i : Fin cs.length, size (cs.get i)) * 2 ^ (n - t) := by rw [← Finset.sum_mul]
          _ = sizeList cs * 2 ^ (n - t) := by rw [sum_size_eq_sizeList]
      have hf := (GateApprox.exists_forms_few_disagree hk htn v).choose_spec
      rw [size]
      calc (Finset.univ.biUnion fun i => (dat i).bad).card
              + (Finset.univ.filter fun x => GateApprox.disagreeGen v Ss x).card
          ≤ sizeList cs * 2 ^ (n - t) + 2 ^ (n - t) := Nat.add_le_add hbu hf
        _ = (sizeList cs + 1) * 2 ^ (n - t) := by ring }

end PallLean.Paper93.DeepMath.PathB.ACC0.Circuit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.caVar
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.caNot
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.cf_or_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.caOr_pointwise
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.orPoly_degree_le_or
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.sum_size_eq_sizeList
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.caOr
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.cf_and_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.caAnd_pointwise
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.Circuit.caAnd
