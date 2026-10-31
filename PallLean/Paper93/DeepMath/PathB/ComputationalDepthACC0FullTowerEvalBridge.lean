import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaIndicator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaModGate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OrNode

/-!
# The eval-bridge: the full-tower polynomial computes the Boolean circuit value (PROVED)

The readout-correctness core.  The degree/sparsity bounds live on the *polynomial* tower
`ACC0FullTowerDegree.frep` (leaf = input); the value congruence lived on a separate *value* tower (leaf =
`MOD` gate).  This file connects them: it gives `frep`'s **Boolean circuit semantics** `bval` (leaf = the
input value `eval x q`, gates = `MOD`/`AND`/`OR`) and proves the polynomial *evaluated at any point* equals
that Boolean value modulo `p^{2^k}`:

  `eval_frep_bridge` — `p^{2^k} ∣ (eval x (frep p k t) − bval p x t)`.

So the same `frep` that is degree-`K^depth` (`frep_totalDegree_le`) and `(n+1)^{K^depth}`-sparse
(`full_tower_sparse`) also *computes* the circuit's Boolean output mod `p^{2^k}` at every input — the
polynomial **is** the circuit, as a quasipoly `SYM∘AND`.  The `MOD` gate flows via `todaAmpIterP_eval`
(eval of the Toda polynomial = Toda of eval) + the count transfer; `AND`/`OR` via the product/De-Morgan
congruences pushed through `eval`.

## What is proved (clean axioms, no `sorry`)

* `bval` — the Boolean circuit semantics of an `FTower` (leaf = input value).
* `dvd_sum_sub_gen` — generic list-sum divisibility transfer.
* `eval_frep_bridge` / `_list` — `p^{2^k} ∣ (eval x (frep t) − bval t)` (mutual recursion).

## Honest scope

The polynomial computes the Boolean value mod `p^{2^k}` at every point — readout correctness for the
representation.  Combined with `full_tower_extract`/`vval_mem_bool`/`full_tower_sparse` and the modulus
choice, this is a complete quasipoly `SYM∘AND` for bounded-`AND`/`OR` ACC⁰[p].  The `NEXP ⊄ ACC⁰`
contradiction (Williams) remains.  Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FullTowerEvalBridge

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerDegree (FTower frep)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaModGate (todaMod_amplifies)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaIterate (todaAmpIter)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaIndicator (todaAmpIterP_eval)
open PallLean.Paper93.DeepMath.PathB.ACC0OrNode (dvd_prod_sub_gen or_node_dvd)

variable {n : ℕ}

/-- The Boolean circuit semantics of an `FTower` at input `x`: leaf = input value, gates `MOD`/`AND`/`OR`. -/
def bval (p : ℕ) (x : Fin n → ℤ) : FTower (Fin n) → ℤ
  | .leaf q => eval x q
  | .modN ts => if (p : ℤ) ∣ ((ts.map (bval p x)).sum) then 1 else 0
  | .andN ts => (ts.map (bval p x)).prod
  | .orN ts => 1 - (ts.map (fun t => 1 - bval p x t)).prod

/-- **Generic list-sum divisibility transfer (proved).** -/
theorem dvd_sum_sub_gen {α : Type*} {M : ℤ} (f g : α → ℤ) :
    (l : List α) → (∀ a ∈ l, M ∣ (f a - g a)) → M ∣ ((l.map f).sum - (l.map g).sum)
  | [], _ => by simp
  | a :: t, h => by
      simp only [List.map_cons, List.sum_cons]
      have h1 : M ∣ (f a - g a) := h a (by simp)
      have h2 : M ∣ ((t.map f).sum - (t.map g).sum) :=
        dvd_sum_sub_gen f g t (fun x hx => h x (by simp [hx]))
      have he : (f a + (t.map f).sum) - (g a + (t.map g).sum)
          = (f a - g a) + ((t.map f).sum - (t.map g).sum) := by ring
      rw [he]; exact dvd_add h1 h2

mutual

/-- **Eval-bridge (proved): `p^{2^k} ∣ (eval x (frep p k t) − bval p x t)`** — the full-tower polynomial
computes the Boolean circuit value mod `p^{2^k}` at every input. -/
theorem eval_frep_bridge (p k : ℕ) [Fact p.Prime] (x : Fin n → ℤ) :
    (t : FTower (Fin n)) → (p : ℤ) ^ (2 ^ k) ∣ (eval x (frep p k t) - bval p x t)
  | .leaf q => by rw [frep, bval]; simp
  | .andN ts => by
      have hchild : ∀ t ∈ ts, (p : ℤ) ^ (2 ^ k) ∣ (eval x (frep p k t) - bval p x t) :=
        fun t ht => eval_frep_bridge_list p k x ts t ht
      have hev : eval x (frep p k (.andN ts)) = (ts.map (fun t => eval x (frep p k t))).prod := by
        rw [frep, map_list_prod, List.map_map]; rfl
      rw [hev, bval]
      exact dvd_prod_sub_gen (fun t => eval x (frep p k t)) (bval p x) ts hchild
  | .orN ts => by
      have hchild : ∀ t ∈ ts, (p : ℤ) ^ (2 ^ k) ∣ (eval x (frep p k t) - bval p x t) :=
        fun t ht => eval_frep_bridge_list p k x ts t ht
      have hlist : ((ts.map (frep p k)).map (fun q => 1 - q)).map (eval x)
          = ts.map (fun t => 1 - eval x (frep p k t)) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro t _
        simp only [Function.comp_apply, map_sub, map_one]
      have hev : eval x (frep p k (.orN ts))
          = 1 - (ts.map (fun t => 1 - eval x (frep p k t))).prod := by
        rw [frep, map_sub, map_one, map_list_prod, hlist]
      rw [hev, bval]
      exact or_node_dvd (fun t => eval x (frep p k t)) (bval p x) ts hchild
  | .modN ts => by
      have hchild : ∀ t ∈ ts, (p : ℤ) ∣ (eval x (frep p k t) - bval p x t) := fun t ht =>
        dvd_trans (dvd_pow_self (p : ℤ) (by positivity : (2 : ℕ) ^ k ≠ 0))
          (eval_frep_bridge_list p k x ts t ht)
      have hY : (p : ℤ) ∣ ((ts.map (fun t => eval x (frep p k t))).sum - (ts.map (bval p x)).sum) :=
        dvd_sum_sub_gen (fun t => eval x (frep p k t)) (bval p x) ts hchild
      have hiff : ((p : ℤ) ∣ (ts.map (fun t => eval x (frep p k t))).sum)
          ↔ ((p : ℤ) ∣ (ts.map (bval p x)).sum) := by
        constructor
        · intro h
          have h2 := dvd_sub h hY
          rwa [show (ts.map (fun t => eval x (frep p k t))).sum
            - ((ts.map (fun t => eval x (frep p k t))).sum - (ts.map (bval p x)).sum)
            = (ts.map (bval p x)).sum from by ring] at h2
        · intro h
          have h2 := dvd_add h hY
          rwa [show (ts.map (bval p x)).sum
            + ((ts.map (fun t => eval x (frep p k t))).sum - (ts.map (bval p x)).sum)
            = (ts.map (fun t => eval x (frep p k t))).sum from by ring] at h2
      have htoda := todaMod_amplifies p ((ts.map (fun t => eval x (frep p k t))).sum) k
      have heq : (if (p : ℤ) ∣ (ts.map (bval p x)).sum then (1 : ℤ) else 0)
          = (if (p : ℤ) ∣ (ts.map (fun t => eval x (frep p k t))).sum then (1 : ℤ) else 0) := by
        by_cases h : (p : ℤ) ∣ (ts.map (fun t => eval x (frep p k t))).sum
        · rw [if_pos (hiff.mp h), if_pos h]
        · rw [if_neg (fun hv => h (hiff.mpr hv)), if_neg h]
      have hev : eval x (frep p k (.modN ts))
          = todaAmpIter k (1 - ((ts.map (fun t => eval x (frep p k t))).sum) ^ (p - 1)) := by
        rw [frep, todaAmpIterP_eval, map_sub, map_one, map_pow, map_list_sum, List.map_map]; rfl
      rw [hev, bval, heq]
      exact htoda

/-- List companion. -/
theorem eval_frep_bridge_list (p k : ℕ) [Fact p.Prime] (x : Fin n → ℤ) :
    (ts : List (FTower (Fin n))) →
      ∀ t ∈ ts, (p : ℤ) ^ (2 ^ k) ∣ (eval x (frep p k t) - bval p x t)
  | [] => fun t ht => absurd ht (by simp)
  | a :: ts => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact eval_frep_bridge p k x t
      · exact eval_frep_bridge_list p k x ts t hmem

end

/-!
**Eval-bridge proved.**  `p^{2^k} ∣ (eval x (frep p k t) − bval p x t)`: the degree-`K^depth`,
`(n+1)^{K^depth}`-sparse polynomial `frep` computes the circuit's Boolean output mod `p^{2^k}` at every
input — the polynomial *is* the circuit, a quasipoly `SYM∘AND`.  The `NEXP ⊄ ACC⁰` contradiction
(Williams) remains.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FullTowerEvalBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FullTowerEvalBridge.eval_frep_bridge
