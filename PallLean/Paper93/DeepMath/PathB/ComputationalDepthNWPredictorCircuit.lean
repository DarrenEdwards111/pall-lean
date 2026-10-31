import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNWPredictorSize

/-!
# Socket-2 (IKW): a circuit-size model for the Nisan–Wigderson predictor

Rung 6 (`nwGen_other_is_junta`) showed that, as a function of the target coordinate's `q` seed bits, each *other* output
coordinate of the NW generator is a **junta on `< k` bits**.  Rung 7 (this file) supplies the missing framework HAL flagged
as the cleanest next step: an *actual Boolean-circuit model with a size measure*, and the **table-lookup / Shannon-expansion
realisation theorem** that turns a junta into a concretely small circuit.  It then cashes the substrate out:

  `Circuit ι` — a lightweight Boolean circuit over inputs `ι → Bool`: `const / var / not / and / or`, with `Circuit.eval`
        and a `Circuit.size` gate count.
  `DependsOn g S` — `g` is a junta on `S`: agreement on `S` forces equal output.
  `shannon` — the Shannon-expansion (decision-tree) construction of a circuit for `g` over a list of variables.
  `shannon_correct` / `shannon_size` — **PROVED**: the construction computes `g` on any junta list, with size `+ 6 ≤ 7·2^len`.
  `DependsOn.exists_circuit` — **PROVED, the realisation theorem**: any junta on `S` is computed by a circuit of size
        `≤ 7·2^{|S|}` — the `< 2^k`-table realisation made concrete in a real circuit model.
  `nwGen_other_has_small_circuit` — **PROVED**: each other coordinate `w ↦ nwGen f (patchSet z w p) p'` has a circuit of
        size `≤ 7·2^{|overlap|}` in the target's `q` seed bits.
  `nwGen_other_circuit_size_lt` — **PROVED, the cash-out**: for distinct degree-`<k` polynomials that circuit has size
        `< 7·2^k` — bounded by `k` alone, independent of `q`.  The junta cheapness is now a genuine small circuit.

So the size asymmetry is realised in an honest circuit model: the target reads all `q` bits, while each of the `q^k` other
coordinates is computed by a circuit of size `< 7·2^k`.  This is the concrete bridge from the NW combinatorics to
"small predictor components" that HAL recommended before touching probability or the full collapse.

## Honest scope — a circuit-size realisation of the junta components, not the predictor's correctness

This builds a real circuit model and proves that the other coordinates are computed by small (`< 7·2^k`) circuits — the
concrete cash-out of rung 6's cheapness bound.  It does **not** assemble the whole next-bit predictor as one circuit (which
also needs the hard-wired background `z` and the wiring of the `q^k` components), nor the probabilistic **hybrid /
next-bit-predictor** advantage argument (needs a probability framework), nor the IKW easy-witness collapse.  Those are the
deep `NEXP`-strength content of socket 2, not established here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoolCircuit

variable {ι : Type*}

/-- A lightweight Boolean circuit over inputs indexed by `ι`: constants, input variables, `NOT`, `AND`, `OR`. -/
inductive Circuit (ι : Type*) where
  | const : Bool → Circuit ι
  | var : ι → Circuit ι
  | not : Circuit ι → Circuit ι
  | and : Circuit ι → Circuit ι → Circuit ι
  | or : Circuit ι → Circuit ι → Circuit ι

namespace Circuit

/-- Evaluation of a circuit on an input assignment `x : ι → Bool`. -/
def eval : Circuit ι → (ι → Bool) → Bool
  | const b, _ => b
  | var i, x => x i
  | not c, x => !(c.eval x)
  | and c d, x => (c.eval x) && (d.eval x)
  | or c d, x => (c.eval x) || (d.eval x)

/-- The size (gate/leaf count) of a circuit. -/
def size : Circuit ι → ℕ
  | const _ => 1
  | var _ => 1
  | not c => c.size + 1
  | and c d => c.size + d.size + 1
  | or c d => c.size + d.size + 1

end Circuit

/-- `g` is a **junta on `S`**: any two inputs agreeing on `S` produce the same output. -/
def DependsOn (g : (ι → Bool) → Bool) (S : Finset ι) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → g x = g y

/-- **Shannon expansion** of `g` over a list of variables `l`: a decision-tree circuit branching on each variable of `l`
and reading off the value of `g` at the leaves.  On any input, it recomputes `g` provided `l` covers `g`'s support. -/
def shannon [DecidableEq ι] : ((ι → Bool) → Bool) → List ι → Circuit ι
  | g, [] => Circuit.const (g (fun _ => false))
  | g, (i :: l) =>
      Circuit.or
        (Circuit.and (Circuit.var i) (shannon (fun y => g (Function.update y i true)) l))
        (Circuit.and (Circuit.not (Circuit.var i)) (shannon (fun y => g (Function.update y i false)) l))

/-- **Correctness of Shannon expansion (proved)**: if `g` is a junta on the variables listed in `l`, then the circuit
`shannon g l` computes `g` on every input. -/
theorem shannon_correct [DecidableEq ι] (l : List ι) :
    ∀ (g : (ι → Bool) → Bool), DependsOn g l.toFinset →
      ∀ x, (shannon g l).eval x = g x := by
  induction l with
  | nil =>
      intro g hg x
      simp only [shannon, Circuit.eval]
      exact hg (fun _ => false) x (fun i hi => by simp at hi)
  | cons i l ih =>
      intro g hg x
      -- Fixing the head variable to a constant keeps a junta on the tail.
      have hbranch : ∀ (b : Bool),
          DependsOn (fun y => g (Function.update y i b)) l.toFinset := by
        intro b a a' haa'
        show g (Function.update a i b) = g (Function.update a' i b)
        refine hg (Function.update a i b) (Function.update a' i b) (fun j hj => ?_)
        simp only [Function.update_apply]
        by_cases hji : j = i
        · simp [hji]
        · rw [if_neg hji, if_neg hji]
          rw [List.toFinset_cons, Finset.mem_insert] at hj
          rcases hj with h | h
          · exact absurd h hji
          · exact haa' j h
      have et : (shannon (fun y => g (Function.update y i true)) l).eval x
          = g (Function.update x i true) := ih _ (hbranch true) x
      have ef : (shannon (fun y => g (Function.update y i false)) l).eval x
          = g (Function.update x i false) := ih _ (hbranch false) x
      simp only [shannon, Circuit.eval]
      rw [et, ef]
      -- Fixing a variable to its actual value leaves the input unchanged.
      have upd_self : ∀ (b : Bool), x i = b → Function.update x i b = x := by
        intro b hb; funext j; rw [Function.update_apply]
        by_cases hj : j = i
        · rw [if_pos hj, hj, hb]
        · rw [if_neg hj]
      rcases Bool.eq_false_or_eq_true (x i) with hxi | hxi
      · rw [hxi, upd_self true hxi]; simp
      · rw [hxi, upd_self false hxi]; simp

/-- **Size bound for Shannon expansion (proved)**: `size (shannon g l) + 6 ≤ 7 · 2^{|l|}` — the decision tree over `|l|`
variables has size `O(2^{|l|})`. -/
theorem shannon_size [DecidableEq ι] (l : List ι) :
    ∀ g : (ι → Bool) → Bool, (shannon g l).size + 6 ≤ 7 * 2 ^ l.length := by
  induction l with
  | nil =>
      intro g
      simp only [shannon, Circuit.size, List.length_nil, pow_zero]
      omega
  | cons i l ih =>
      intro g
      have hA := ih (fun y => g (Function.update y i true))
      have hB := ih (fun y => g (Function.update y i false))
      have hsize : (shannon g (i :: l)).size
          = (shannon (fun y => g (Function.update y i true)) l).size
          + (shannon (fun y => g (Function.update y i false)) l).size + 6 := by
        simp only [shannon, Circuit.size]; omega
      rw [hsize]
      simp only [List.length_cons]
      rw [pow_succ]
      omega

/-- **The realisation theorem (proved)**: any junta on a finite set `S` is computed by a circuit of size `≤ 7 · 2^{|S|}`.
This is the `< 2^{|S|}`-table lookup made concrete in a real circuit model. -/
theorem DependsOn.exists_circuit [DecidableEq ι] {g : (ι → Bool) → Bool} {S : Finset ι}
    (hg : DependsOn g S) :
    ∃ C : Circuit ι, (∀ x, C.eval x = g x) ∧ C.size ≤ 7 * 2 ^ S.card := by
  refine ⟨shannon g S.toList, ?_, ?_⟩
  · intro x
    have h' : DependsOn g S.toList.toFinset := by rw [Finset.toList_toFinset]; exact hg
    exact shannon_correct S.toList g h' x
  · have hs := shannon_size S.toList g
    rw [Finset.length_toList] at hs
    omega

end PallLean.Paper93.DeepMath.PathB.BoolCircuit

namespace PallLean.Paper93.DeepMath.PathB.NWDesign

open Polynomial PallLean.Paper93.DeepMath.PathB.BoolCircuit

variable {q : ℕ} [Fact q.Prime]

/-- **Each other coordinate has a small circuit (proved)**: the map `w ↦ nwGen f (patchSet z w p) p'`, viewed as a
function of the target's `q` seed bits, is computed by a circuit of size `≤ 7 · 2^{|overlap|}` — the junta cheapness of
rung 6 realised in the circuit model. -/
theorem nwGen_other_has_small_circuit (f : (ZMod q → Bool) → Bool)
    (z : ZMod q × ZMod q → Bool) (p p' : (ZMod q)[X]) :
    ∃ C : Circuit (ZMod q × ZMod q),
      (∀ w, C.eval w = nwGen f (patchSet z w p) p') ∧
      C.size ≤ 7 * 2 ^ (nwSet p ∩ nwSet p').card := by
  have hj : BoolCircuit.DependsOn (fun w => nwGen f (patchSet z w p) p') (nwSet p ∩ nwSet p') := by
    intro w w' h
    exact nwGen_other_is_junta f z p p' w w' h
  exact hj.exists_circuit

/-- **The cash-out (proved)**: for distinct degree-`<k` polynomials, each other coordinate is computed by a circuit of size
`< 7 · 2^k` — bounded by `k` alone, independent of `q`.  The size asymmetry (target reads `q`, others computed by a
`k`-bounded circuit) is now realised in a genuine circuit model. -/
theorem nwGen_other_circuit_size_lt (f : (ZMod q → Bool) → Bool)
    (z : ZMod q × ZMod q → Bool) (p p' : (ZMod q)[X]) (hne : p ≠ p')
    (k : ℕ) (hp : p.natDegree < k) (hp' : p'.natDegree < k) :
    ∃ C : Circuit (ZMod q × ZMod q),
      (∀ w, C.eval w = nwGen f (patchSet z w p) p') ∧ C.size < 7 * 2 ^ k := by
  obtain ⟨C, hC, hsz⟩ := nwGen_other_has_small_circuit f z p p'
  refine ⟨C, hC, lt_of_le_of_lt hsz ?_⟩
  have hlt : 2 ^ (nwSet p ∩ nwSet p').card < 2 ^ k :=
    Nat.pow_lt_pow_right (by norm_num) (nwSet_inter_lt p p' hne k hp hp')
  omega

end PallLean.Paper93.DeepMath.PathB.NWDesign

#print axioms PallLean.Paper93.DeepMath.PathB.BoolCircuit.shannon_correct
#print axioms PallLean.Paper93.DeepMath.PathB.BoolCircuit.shannon_size
#print axioms PallLean.Paper93.DeepMath.PathB.BoolCircuit.DependsOn.exists_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwGen_other_has_small_circuit
#print axioms PallLean.Paper93.DeepMath.PathB.NWDesign.nwGen_other_circuit_size_lt
