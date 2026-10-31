import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Agreement
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DimensionCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3DegreeComposition

/-!
# Layer 3 — the Razborov–Smolensky contradiction assembled

This file ties the two halves of the Razborov–Smolensky AC⁰[p] lower bound together.

* **Agreement side** (`ComputationalDepthLayer3Agreement`): `composed_error_le` /
  `exists_large_agreement_set` — an `AC⁰[p]` circuit's composed low-degree approximant agrees with the
  circuit on a `(3/4)` fraction of inputs.
* **Dimension side** (`ComputationalDepthLayer3DimensionCount`): `smolensky_contradiction` — if the full
  `±1` product `χ_univ` has a degree-`Δ` representative on such a large agreement set `G`, with the band
  margin window, then `False`.

The bridge between them is the observation that `χ_univ(x) = ∏ᵢ pmOne(xᵢ) = (-1)^{#ones} = pmOne(parity x)`:
**if the circuit computes parity** (`∏ᵢ pmOne(xᵢ) = pmOne(C.eval x)`), then `1 - 2·g_C` is a low-degree
representative of `χ_univ` on `G` (using `pmOne b = 1 - 2·boolToZMod b`).  Assembling all three gives
`parity_circuit_false`: no parity-computing `AC⁰[p]` circuit can simultaneously have a low-degree
approximant (small size/depth) and enough agreement (large time horizon) — the Razborov–Smolensky
size–depth tradeoff for `PARITY`.

The only remaining *mathematical* inputs are the explicit hypotheses of `parity_circuit_false`: that the
circuit computes parity (the statement being refuted), that it is `AC⁰[p]`, that `p` is odd, the
`toAgree`-degree bound (the degree side, `((p-1)t)^depth`), and the parameter conditions
`pᵗ ≥ 4·#subcircuits` and `16Δ² < 2m+3` (whose simultaneous satisfiability for a *small* circuit is the
size lower bound).
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open MvPolynomial

/-- `pmOne b = 1 - 2·boolToZMod b` (the `{0,1} ↦ ±1` linear change of variable, over any `ZMod p`). -/
theorem pmOne_eq_one_sub_two_boolToZMod (p : ℕ) (b : Bool) :
    pmOne p b = 1 - 2 * boolToZMod p b := by cases b <;> simp [pmOne, boolToZMod] <;> ring

/-- The full `±1` product is the parity sign: `∏ᵢ pmOne(xᵢ) = (-1)^{#ones}`. -/
theorem prod_pmOne (p : ℕ) {n : ℕ} (x : Fin n → Bool) :
    (∏ i, pmOne p (x i)) = (-1 : ZMod p) ^ (Finset.univ.filter (fun i => x i = true)).card := by
  simp only [pmOne]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]

/-- `pmOne (decide (Odd k)) = (-1)^k` — the `±1` encoding of the parity bit is the sign `(-1)^k`. -/
theorem pmOne_decide_odd (p k : ℕ) : pmOne p (decide (Odd k)) = (-1 : ZMod p) ^ k := by
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow]; simp [pmOne, Nat.not_odd_iff_even.mpr he]
  · rw [ho.neg_one_pow]; simp [pmOne, ho]

/-- **The `MOD_q ↔ χ_univ` bridge.**  If `g_C` is a degree-`≤Δ` polynomial agreeing on `G` with the
circuit value `boolToZMod(C.eval ·)`, and the circuit **computes parity** in the sense
`∏ᵢ pmOne(xᵢ) = pmOne(C.eval x)`, then `1 - 2·g_C` is a degree-`≤Δ` polynomial representing the full
`±1` product `χ_univ = ∏ᵢ pmOne(xᵢ)` on `G`.  (`χ_univ(x) = pmOne(C.eval x) = 1 - 2·boolToZMod(C.eval x)`
and `g_C` realises `boolToZMod(C.eval ·)` on `G`.)  This is the genuinely function-specific step:
parity is exactly the function whose `AC⁰[p]` approximant yields a low-degree `χ_univ`. -/
theorem chi_univ_repr (p : ℕ) [Fact p.Prime] {n : ℕ} (G : Finset (Fin n → Bool)) (Δ : ℕ)
    (Cir : BoolCircuitSyntax n) (gC : MvPolynomial (Fin n) (ZMod p)) (hdeg : gC.totalDegree ≤ Δ)
    (hagree : ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) gC = boolToZMod p (Cir.eval x))
    (hpar : ∀ x : Fin n → Bool, (∏ i, pmOne p (x i)) = pmOne p (Cir.eval x)) :
    ∃ g : MvPolynomial (Fin n) (ZMod p), g.totalDegree ≤ Δ ∧
      ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) g = ∏ i, pmOne p (x i) := by
  refine ⟨1 - 2 * gC, ?_, ?_⟩
  · refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
    · rw [totalDegree_one]; exact Nat.zero_le Δ
    · rw [show (2 : MvPolynomial (Fin n) (ZMod p)) = MvPolynomial.C 2 from (map_ofNat MvPolynomial.C 2).symm]
      exact le_trans (totalDegree_mul _ _) (by rw [totalDegree_C, zero_add]; exact hdeg)
  · intro x hx
    rw [map_sub, map_one, map_mul, map_ofNat, hagree x hx, ← pmOne_eq_one_sub_two_boolToZMod]
    exact (hpar x).symm

/-- **Degree bound for the faithful approximant `toAgree`.**  Bundles the per-gate degree recurrence
(`genOrApprox_totalDegree_le` for `∨`/`∧`, Fermat degree `p-1` for `MOD`, degree `≤1` leaves) into an
`ApproxDegreeData`, so `approxDegree_le` gives `deg(toAgree C) ≤ ((p-1)·t)^{depth C}` — the same
`((p-1)t)^d` Smolensky degree proven for `toApprox`, now for the agreement-side approximant. -/
noncomputable def toAgreeData (p t : ℕ) [Fact p.Prime] {n : ℕ} (ht : 1 ≤ t)
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) : ApproxDegreeData p n where
  A := toAgree p t R
  K := (p - 1) * t
  hK := by
    have h2 := (Fact.out (p := p.Prime)).two_le
    have : 1 * 1 ≤ (p - 1) * t := Nat.mul_le_mul (by omega) ht
    simpa using this
  hconst := fun b => by simp only [toAgree, totalDegree_C]; exact Nat.zero_le 1
  hinput := fun i => by simp only [toAgree, totalDegree_X]; exact le_refl 1
  hnot := fun C => by
    simp only [toAgree]
    refine le_trans (totalDegree_sub _ _) ?_
    rw [totalDegree_one, Nat.zero_max]
  hor := fun cs => by
    simp only [toAgree]
    refine le_trans (genOrApprox_totalDegree_le p _ _
      (cs.foldl (fun m c => max m (toAgree p t R c).totalDegree) 0)
      (fun j => le_foldl_max (fun c => (toAgree p t R c).totalDegree) cs 0 (List.get_mem _ j))) ?_
    exact le_of_eq (by ring)
  hand := fun cs => by
    simp only [toAgree]
    refine le_trans (totalDegree_sub _ _) ?_
    rw [totalDegree_one, Nat.zero_max]
    refine le_trans (genOrApprox_totalDegree_le p _ _
      (cs.foldl (fun m c => max m (toAgree p t R c).totalDegree) 0)
      (fun j => ?_)) (le_of_eq (by ring))
    refine le_trans (totalDegree_sub _ _) ?_
    rw [totalDegree_one, Nat.zero_max]
    exact le_foldl_max (fun c => (toAgree p t R c).totalDegree) cs 0 (List.get_mem _ j)
  hmod := fun q r cs => by
    simp only [toAgree]
    set D := cs.foldl (fun m c => max m (toAgree p t R c).totalDegree) 0 with hD
    have hsum : (∑ j : Fin cs.length, toAgree p t R (cs.get j)).totalDegree ≤ D :=
      le_trans (totalDegree_finset_sum _ _)
        (Finset.sup_le (fun j _ =>
          le_foldl_max (fun c => (toAgree p t R c).totalDegree) cs 0 (List.get_mem _ j)))
    have hsub : ((∑ j : Fin cs.length, toAgree p t R (cs.get j)) - C (r : ZMod p)).totalDegree ≤ D := by
      refine le_trans (totalDegree_sub _ _) ?_
      rw [totalDegree_C, Nat.max_zero]; exact hsum
    have h1 : (1 - ((∑ j : Fin cs.length, toAgree p t R (cs.get j)) - C (r : ZMod p)) ^ (p - 1)).totalDegree
        ≤ (p - 1) * D := by
      refine le_trans (totalDegree_sub _ _) ?_
      rw [totalDegree_one, Nat.zero_max]
      exact le_trans (totalDegree_pow _ _) (Nat.mul_le_mul_left _ hsub)
    exact le_trans h1 (le_trans (Nat.le_mul_of_pos_right _ ht) (le_of_eq (by ring)))

/-- **`deg(toAgree C) ≤ ((p-1)·t)^{depth C}`** — the Smolensky degree for the agreement-side
approximant (so the degree hypothesis of `chi_univ_repr` / `smolensky_contradiction` is *discharged*,
not assumed). -/
theorem toAgree_totalDegree_le (p t : ℕ) [Fact p.Prime] {n : ℕ} (ht : 1 ≤ t)
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) (C : BoolCircuitSyntax n) :
    (toAgree p t R C).totalDegree ≤ ((p - 1) * t) ^ C.depth :=
  (toAgreeData p t ht R).approxDegree_le C

open Classical in
/-- **The Razborov–Smolensky contradiction for `PARITY`.**  Let `Cir` be an `AC⁰[p]` circuit on
`2m+1` variables (`p` odd) that **computes parity** (`∏ᵢ pmOne(xᵢ) = pmOne(Cir.eval x)`).  Suppose, at
time horizon `t`, its composed approximant `toAgree` has total degree `≤ Δ`, the horizon satisfies
`pᵗ ≥ 4·#subcircuits` (so the agreement set covers `≥ 3/4` of the cube), and the band-margin window
`16Δ² < 2m+3` holds (so `Δ = O(√m)`).  Then `False`.

In other words: a parity-computing `AC⁰[p]` circuit cannot simultaneously achieve a degree-`Δ`
approximant **and** the agreement-horizon and band-margin conditions — the obstruction whose
quantitative form (`Δ ≈ ((p-1)t)^depth` small `vs` `pᵗ ≥ 4·size`) is the `PARITY ∉ AC⁰[p]` lower bound.
This assembles `exists_large_agreement_set` (agreement-set size), `chi_univ_repr` (the parity bridge),
`toAgree_totalDegree_le` (the degree side, `((p-1)t)^depth`), and `smolensky_contradiction` (the
dimension contradiction).  The degree `Δ = ((p-1)·t)^{depth Cir}` is *concrete* — the only remaining
inputs are the parity-computing assumption, `AC⁰[p]`-ness, `p` odd, and the parameter conditions
`pᵗ ≥ 4·#subcircuits` and `16·(((p-1)t)^{depth})² < 2m+3`. -/
theorem parity_circuit_false (p : ℕ) [Fact p.Prime] {m : ℕ} (hp2 : (2 : ZMod p) ≠ 0)
    (Cir : BoolCircuitSyntax (2 * m + 1)) (t : ℕ) (ht1 : 1 ≤ t)
    (hpar : ∀ x : Fin (2 * m + 1) → Bool, (∏ i, pmOne p (x i)) = pmOne p (Cir.eval x))
    (hmod : ∀ q r cs,
      (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax (2 * m + 1)) ∈ subcircuits Cir → q = p)
    (ht : 4 * (subcircuits Cir).toFinset.card ≤ p ^ t)
    (hwindow : 16 * (((p - 1) * t) ^ Cir.depth) ^ 2 < 2 * m + 3) : False := by
  obtain ⟨ω, hGsize⟩ := exists_large_agreement_set p t Cir hmod ht
  set G := Finset.univ.filter (fun x : Fin (2 * m + 1) → Bool =>
    eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t Cir ω) Cir)
      = boolToZMod p (Cir.eval x)) with hG
  have hagree : ∀ x ∈ G, eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t Cir ω) Cir)
      = boolToZMod p (Cir.eval x) := by
    intro x hx; rw [hG, Finset.mem_filter] at hx; exact hx.2
  obtain ⟨g, hgdeg, hgeval⟩ := chi_univ_repr p G (((p - 1) * t) ^ Cir.depth) Cir
    (toAgree p t (oracleOf p t Cir ω) Cir) (toAgree_totalDegree_le p t ht1 _ Cir) hagree hpar
  exact smolensky_contradiction p hp2 G g hgdeg hgeval hwindow hGsize

/-! **The `PARITY ∉ AC⁰[p]` size lower bound** (contrapositive of `parity_circuit_false`).  Any `AC⁰[p]`
circuit (`p` odd) on `2m+1` variables that **computes parity** must have **more than `pᵗ/4`
subcircuits** for *every* time horizon `t` in the band-margin window
`16·(((p-1)t)^{depth})² < 2m+3` (i.e. `1 ≤ t` with `((p-1)t)^{depth} = O(√m)`):
\[
  4 \cdot \#\text{subcircuits}(Cir) > p^{\,t}.
\]
Reading off the largest such `t` (`t ≈ m^{1/(2·depth)}/(p-1)`) gives
`#subcircuits ≥ p^{Ω(m^{1/(2·depth)})}` — super-polynomial for any constant depth, and since
`size ≥ #subcircuits`, the Razborov–Smolensky exponential `PARITY` lower bound for `AC⁰[p]`. -/
open Classical in
theorem parity_circuit_size_lower_bound (p : ℕ) [Fact p.Prime] {m : ℕ} (hp2 : (2 : ZMod p) ≠ 0)
    (Cir : BoolCircuitSyntax (2 * m + 1)) (t : ℕ) (ht1 : 1 ≤ t)
    (hpar : ∀ x : Fin (2 * m + 1) → Bool, (∏ i, pmOne p (x i)) = pmOne p (Cir.eval x))
    (hmod : ∀ q r cs,
      (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax (2 * m + 1)) ∈ subcircuits Cir → q = p)
    (hwindow : 16 * (((p - 1) * t) ^ Cir.depth) ^ 2 < 2 * m + 3) :
    p ^ t < 4 * (subcircuits Cir).toFinset.card := by
  by_contra h
  push_neg at h
  exact parity_circuit_false p hp2 Cir t ht1 hpar hmod h hwindow

/-! **`PARITY ∉ AC⁰[p]`, depth-`≤ d` form.**  The size bound stated in terms of a *depth upper bound* `d`
(how `AC⁰[p]` lower bounds are phrased: `depth = O(1)`).  Since `((p-1)t)^{depth Cir} ≤ ((p-1)t)^d` when
`depth Cir ≤ d`, the window for `d` implies the window for the actual depth, so: a parity-computing
`AC⁰[p]` circuit (`p` odd) of depth `≤ d` on `2m+1` variables has `4·#subcircuits > pᵗ` for every `t ≥ 1`
with `16·(((p-1)t)^d)² < 2m+3`.  For fixed `d` the window is satisfiable up to `t = Θ(m^{1/(2d)})`,
giving `#subcircuits ≥ p^{Ω(m^{1/(2d)})}` — the explicit exponential `PARITY` lower bound. -/
open Classical in
theorem parity_size_lower_bound_depth_le (p : ℕ) [Fact p.Prime] {m d : ℕ} (hp2 : (2 : ZMod p) ≠ 0)
    (Cir : BoolCircuitSyntax (2 * m + 1)) (hd : Cir.depth ≤ d) (t : ℕ) (ht1 : 1 ≤ t)
    (hpar : ∀ x : Fin (2 * m + 1) → Bool, (∏ i, pmOne p (x i)) = pmOne p (Cir.eval x))
    (hmod : ∀ q r cs,
      (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax (2 * m + 1)) ∈ subcircuits Cir → q = p)
    (hwindow : 16 * (((p - 1) * t) ^ d) ^ 2 < 2 * m + 3) :
    p ^ t < 4 * (subcircuits Cir).toFinset.card := by
  have hbase : 1 ≤ (p - 1) * t := by
    have h2 := (Fact.out (p := p.Prime)).two_le
    have : 1 * 1 ≤ (p - 1) * t := Nat.mul_le_mul (by omega) ht1
    simpa using this
  have hmono : ((p - 1) * t) ^ Cir.depth ≤ ((p - 1) * t) ^ d := Nat.pow_le_pow_right hbase hd
  have hwin : 16 * (((p - 1) * t) ^ Cir.depth) ^ 2 < 2 * m + 3 :=
    lt_of_le_of_lt (by gcongr) hwindow
  exact parity_circuit_size_lower_bound p hp2 Cir t ht1 hpar hmod hwin

/-! **`PARITY ∉ AC⁰[p]`, explicit exponential form.**  Parametrising by the time horizon `t` (rather than
solving the window for `t` via a `d`-th root): once the number of variables is large enough relative to
`t` — precisely `m ≥ 8·((p-1)t)^{2d}`, since then `16·(((p-1)t)^d)² ≤ 2m < 2m+3` — a parity-computing
`AC⁰[p]` circuit (`p` odd) of depth `≤ d` on `2m+1` variables must have
\[
  4 \cdot \#\text{subcircuits}(Cir) > p^{\,t}.
\]
Choosing `t` maximal (`t = Θ((m/8)^{1/(2d)}) = Θ(m^{1/(2d)})`, so `n = 2m+1 ≈ 16·((p-1)t)^{2d}`) gives
`#subcircuits ≥ p^{\,t}/4 = p^{Ω(m^{1/(2d)})} = 2^{Ω(n^{1/(2d)})}` — and `size ≥ #subcircuits` — the
exponential Razborov–Smolensky `PARITY` lower bound for constant-depth `AC⁰[p]`. -/
open Classical in
theorem parity_size_lower_bound_explicit (p : ℕ) [Fact p.Prime] {m d : ℕ} (hp2 : (2 : ZMod p) ≠ 0)
    (Cir : BoolCircuitSyntax (2 * m + 1)) (hd : Cir.depth ≤ d) (t : ℕ) (ht1 : 1 ≤ t)
    (hpar : ∀ x : Fin (2 * m + 1) → Bool, (∏ i, pmOne p (x i)) = pmOne p (Cir.eval x))
    (hmod : ∀ q r cs,
      (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax (2 * m + 1)) ∈ subcircuits Cir → q = p)
    (hm : 8 * (((p - 1) * t) ^ d) ^ 2 ≤ m) :
    p ^ t < 4 * (subcircuits Cir).toFinset.card :=
  parity_size_lower_bound_depth_le p hp2 Cir hd t ht1 hpar hmod (by omega)

/-! **`PARITY ∉ AC⁰[p]` — for the literal parity function.**  The previous bounds take the
parity-computing hypothesis in `±1` form (`∏ᵢ pmOne(xᵢ) = pmOne(Cir.eval x)`); this restates it for the
honest **Boolean parity function** `x ↦ (#{i : xᵢ} is odd)`.  Since `∏ᵢ pmOne(xᵢ) = (-1)^{#ones}`
(`prod_pmOne`) `= pmOne(decide(Odd #ones))` (`pmOne_decide_odd`), a circuit `Cir` with
`Cir.eval x = decide(Odd #ones)` computes parity in the required sense.  So: any `AC⁰[p]` circuit (`p`
odd) of depth `≤ d` on `2m+1` variables that **computes the parity function** has, for every `t≥1` with
`m ≥ 8·((p-1)t)^{2d}`, more than `pᵗ/4` subcircuits — `2^{Ω(n^{1/(2d)})}` at the optimal `t`. -/
open Classical in
theorem parity_function_lower_bound (p : ℕ) [Fact p.Prime] {m d : ℕ} (hp2 : (2 : ZMod p) ≠ 0)
    (Cir : BoolCircuitSyntax (2 * m + 1)) (hd : Cir.depth ≤ d) (t : ℕ) (ht1 : 1 ≤ t)
    (hparity : ∀ x : Fin (2 * m + 1) → Bool,
      Cir.eval x = decide (Odd (Finset.univ.filter (fun i => x i = true)).card))
    (hmod : ∀ q r cs,
      (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax (2 * m + 1)) ∈ subcircuits Cir → q = p)
    (hm : 8 * (((p - 1) * t) ^ d) ^ 2 ≤ m) :
    p ^ t < 4 * (subcircuits Cir).toFinset.card :=
  parity_size_lower_bound_explicit p hp2 Cir hd t ht1
    (fun x => by rw [prod_pmOne, hparity x, pmOne_decide_odd]) hmod hm

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.pmOne_eq_one_sub_two_boolToZMod
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.chi_univ_repr
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.toAgree_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.parity_circuit_false
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.parity_circuit_size_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.parity_size_lower_bound_depth_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.parity_size_lower_bound_explicit
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.parity_function_lower_bound
