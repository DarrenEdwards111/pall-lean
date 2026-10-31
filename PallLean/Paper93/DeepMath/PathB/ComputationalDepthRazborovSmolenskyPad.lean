import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyPerGateAnd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyJoint

/-!
# Beigel–Tarui, rung 28: the padding + image translation (`#(ubadSet g) = redNumErr` at a common arity)

Rung 27's `exists_low_error_family` produces one subset family `F : Fin t → Finset (Fin N)` at a *common* arity `N`, but
each gate `uor l` has its own fan-in `l.length ≤ N`.  This file supplies the translation that identifies a gate's bad
set (over the shared `ℕ`-subset list imaged from `F`) with rung 24's `redNumErr` of the gate's reduced map **padded** to
arity `N`.

  `padOr` — the `OR`-gate reduced map padded to `Fin N`: `(l.get j).eval x` for `j < l.length`, `false` beyond.
  `linSumNVal_pad_or` — **PROVED**: the linear form over the children at `S.image Fin.val` (`S : Finset (Fin N)`) equals
        `ssum S (padOr l x)` — the out-of-range indices contribute `0` on both sides (`getD` default vs padded `false`).
  `uor_eval_pad` — **PROVED**: `(uor l).eval x = true ↔ ∃ j : Fin N, padOr l x j = true` (padding adds no `true`s).
  `ubadSet_uor_card_eq` — **PROVED, the translation**: with `subsets := (ofFn F).map (·.image Fin.val)`,
        `#(ubadSet subsets (uor l)) = redNumErr (padOr l) t F` — a gate's bad set is exactly the common-arity `redNumErr`
        of its padded reduced map.

## Honest scope

This is the padding + `Finset.image Fin.val` translation for an `OR` gate: it lets a gate defined at fan-in `l.length`
consume the shared common-arity-`N` family `F` of rung 27, with `#(ubadSet …) = redNumErr (padOr l) t F`.  The `AND` gate
is the exact dual (padding the negated reduced map `redAnd`), and `var`/`NOT` gates have empty bad sets (`redNumErr = 0`);
summing these identities over the gates of a circuit and feeding rung 27's `exists_low_error_family` +
`whole_circuit_error_lt_of_sum` yields the whole-circuit error `< 2^n` — the final assembly, whose only remaining content
is this same translation applied uniformly across gate types.  This introduces no new mathematics.  The composite-`MOD_m`
case remains the proven two-fields barrier.  Nothing here is the Beigel–Tarui reduction in full, `NEXP ⊄ ACC⁰`, or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (embed embed_not)

variable {p : ℕ} [Fact p.Prime] {n N : ℕ}

/-- The `OR`-gate reduced map padded to arity `N`: the child truth value for `j < l.length`, `false` beyond. -/
noncomputable def padOr (l : List (UForm n)) (x : Fin n → Bool) : Fin N → Bool :=
  fun j => if h : j.val < l.length then (l.get ⟨j.val, h⟩).eval x else false

/-- **The padded linear form is `ssum` of the padded map (proved)**: out-of-range indices contribute `0` on both sides. -/
theorem linSumNVal_pad_or (l : List (UForm n)) (x : Fin n → Bool) (S : Finset (Fin N)) :
    linSumNVal (l.map (fun a => (embed (a.eval x) : ZMod p))) (S.image Fin.val)
      = ssum (p := p) S (padOr (N := N) l x) := by
  rw [linSumNVal, Finset.sum_image (fun a _ b _ h => Fin.val_injective h), ssum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j.val < l.length
  · have hpad : padOr (N := N) l x j = (l.get ⟨j.val, hj⟩).eval x := by
      simp only [padOr, dif_pos hj]
    rw [List.getD_eq_getElem _ 0 (by rw [List.length_map]; exact hj), List.getElem_map, xf, hpad]
    simp [embed]
  · have hpad : padOr (N := N) l x j = false := by simp only [padOr, dif_neg hj]
    rw [List.getD_eq_default _ 0 (by rw [List.length_map]; omega), xf, hpad]
    simp

/-- **The padded map is nonzero iff the gate is `true` (proved)**: padding adds no `true`s. -/
theorem uor_eval_pad {l : List (UForm n)} (hN : l.length ≤ N) (x : Fin n → Bool) :
    (UForm.uor l).eval x = true ↔ ∃ j : Fin N, padOr (N := N) l x j = true := by
  rw [uor_eval_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨⟨i.val, lt_of_lt_of_le i.2 hN⟩, ?_⟩
    simpa only [padOr, dif_pos i.2] using hi
  · rintro ⟨j, hj⟩
    simp only [padOr] at hj
    split_ifs at hj with h
    exact ⟨⟨j.val, h⟩, hj⟩

/-- **The translation (proved)**: a gate's bad set over the shared `ℕ`-subset list imaged from `F` equals the
common-arity `redNumErr` of the gate's padded reduced map. -/
theorem ubadSet_uor_card_eq {l : List (UForm n)} (hN : l.length ≤ N) {t : ℕ}
    (F : Fin t → Finset (Fin N)) :
    (ubadSet (p := p) ((List.ofFn F).map (fun S => S.image Fin.val)) (UForm.uor l)).card
      = redNumErr (p := p) (padOr (N := N) l) t F := by
  rw [redNumErr]
  congr 1
  rw [ubadSet]
  ext x
  rw [Finset.mem_filter, Finset.mem_filter, redNZ, Finset.mem_filter]
  constructor
  · rintro ⟨_, hgate, hall⟩
    refine ⟨⟨Finset.mem_univ x, (uor_eval_pad hN x).mp hgate⟩, ?_⟩
    rw [mem_allFail]
    intro i
    have hi := hall ((F i).image Fin.val)
      (by rw [List.mem_map]; exact ⟨F i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩)
    rw [linSumNVal_pad_or] at hi
    exact hi
  · rintro ⟨⟨_, hnz⟩, hne⟩
    rw [mem_allFail] at hne
    refine ⟨Finset.mem_univ x, (uor_eval_pad hN x).mpr hnz, ?_⟩
    intro S hS
    rw [List.mem_map] at hS
    obtain ⟨S', hS', rfl⟩ := hS
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hS'
    rw [linSumNVal_pad_or]
    exact hne i

/-! ### The `AND` gate (De Morgan dual) -/

/-- The `AND`-gate reduced map padded to arity `N`: `¬(l.get j).eval x` for `j < l.length`, `false` beyond. -/
noncomputable def padAnd (l : List (UForm n)) (x : Fin n → Bool) : Fin N → Bool :=
  fun j => if h : j.val < l.length then !(l.get ⟨j.val, h⟩).eval x else false

/-- **The padded negated linear form is `ssum` of `padAnd` (proved)**. -/
theorem linSumNVal_pad_and (l : List (UForm n)) (x : Fin n → Bool) (S : Finset (Fin N)) :
    linSumNVal (l.map (fun a => (1 - embed (a.eval x) : ZMod p))) (S.image Fin.val)
      = ssum (p := p) S (padAnd (N := N) l x) := by
  have hmap : l.map (fun a => (1 - embed (a.eval x) : ZMod p))
            = l.map (fun a => (embed (!(a.eval x)) : ZMod p)) := by
    apply List.map_congr_left; intro a _; rw [embed_not]
  rw [hmap, linSumNVal, Finset.sum_image (fun a _ b _ h => Fin.val_injective h), ssum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j.val < l.length
  · have hpad : padAnd (N := N) l x j = !(l.get ⟨j.val, hj⟩).eval x := by
      simp only [padAnd, dif_pos hj]
    rw [List.getD_eq_getElem _ 0 (by rw [List.length_map]; exact hj), List.getElem_map, xf, hpad]
    simp [embed]
  · have hpad : padAnd (N := N) l x j = false := by simp only [padAnd, dif_neg hj]
    rw [List.getD_eq_default _ 0 (by rw [List.length_map]; omega), xf, hpad]
    simp

/-- **The padded map is nonzero iff the `AND` gate is `false` (proved)**. -/
theorem uand_eval_pad {l : List (UForm n)} (hN : l.length ≤ N) (x : Fin n → Bool) :
    (UForm.uand l).eval x = false ↔ ∃ j : Fin N, padAnd (N := N) l x j = true := by
  rw [uand_redNZ_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨⟨i.val, lt_of_lt_of_le i.2 hN⟩, ?_⟩
    simpa only [padAnd, dif_pos i.2, redAnd] using hi
  · rintro ⟨j, hj⟩
    simp only [padAnd] at hj
    split_ifs at hj with h
    exact ⟨⟨j.val, h⟩, by simpa only [redAnd] using hj⟩

/-- **The `AND`-gate translation (proved)**. -/
theorem ubadSet_uand_card_eq {l : List (UForm n)} (hN : l.length ≤ N) {t : ℕ}
    (F : Fin t → Finset (Fin N)) :
    (ubadSet (p := p) ((List.ofFn F).map (fun S => S.image Fin.val)) (UForm.uand l)).card
      = redNumErr (p := p) (padAnd (N := N) l) t F := by
  rw [redNumErr]
  congr 1
  rw [ubadSet]
  ext x
  rw [Finset.mem_filter, Finset.mem_filter, redNZ, Finset.mem_filter]
  constructor
  · rintro ⟨_, hgate, hall⟩
    refine ⟨⟨Finset.mem_univ x, (uand_eval_pad hN x).mp hgate⟩, ?_⟩
    rw [mem_allFail]
    intro i
    have hi := hall ((F i).image Fin.val)
      (by rw [List.mem_map]; exact ⟨F i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩)
    rw [linSumNVal_pad_and] at hi
    exact hi
  · rintro ⟨⟨_, hnz⟩, hne⟩
    rw [mem_allFail] at hne
    refine ⟨Finset.mem_univ x, (uand_eval_pad hN x).mpr hnz, ?_⟩
    intro S hS
    rw [List.mem_map] at hS
    obtain ⟨S', hS', rfl⟩ := hS
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hS'
    rw [linSumNVal_pad_and]
    exact hne i

/-! ### The whole-circuit assembly -/

/-- The fan-in (arity) of a gate: the children count for `OR`/`AND`, `0` for `var`/`NOT`. -/
def gateArity : UForm n → ℕ
  | .uor l => l.length
  | .uand l => l.length
  | _ => 0

/-- Each gate's reduced map padded to the common arity `N` (`var`/`NOT` map to the all-`false` reduced input). -/
noncomputable def gateRed : UForm n → ((Fin n → Bool) → (Fin N → Bool))
  | .uor l => padOr (N := N) l
  | .uand l => padAnd (N := N) l
  | _ => fun _ => fun _ => false

/-- **The all-`false` reduced input has empty nonzero set (proved)**. -/
theorem redNZ_const_false : redNZ (fun (_ : Fin n → Bool) => fun (_ : Fin N) => false) = ∅ := by
  rw [redNZ, Finset.filter_eq_empty_iff]
  intro x _
  push_neg
  intro i
  simp

/-- **The per-gate translation for every gate type (proved)**: with the shared subset list imaged from `F`, every gate's
bad-set count equals the common-arity `redNumErr` of its padded reduced map. -/
theorem gate_card_eq (g : UForm n) (hg : gateArity g ≤ N) {t : ℕ} (F : Fin t → Finset (Fin N)) :
    (ubadSet (p := p) ((List.ofFn F).map (fun S => S.image Fin.val)) g).card
      = redNumErr (p := p) (gateRed (N := N) g) t F := by
  cases g with
  | var i => simp [ubadSet, gateRed, redNumErr, redNZ_const_false]
  | unot a => simp [ubadSet, gateRed, redNumErr, redNZ_const_false]
  | uor l => rw [gateRed]; exact ubadSet_uor_card_eq hg F
  | uand l => rw [gateRed]; exact ubadSet_uand_card_eq hg F

/-- **The whole-circuit error bound (proved)**: if all gates have fan-in `≤ N` and the circuit has fewer than `2^t`
gates, then some subset family makes the unbounded RS-substituted polynomial err on `< 2^n` inputs — the whole-circuit
`< 2^n` error, assembled from rung 27's single-shared-family averaging and this rung's per-gate translation. -/
theorem whole_circuit_error_exists (f : UForm n) (t : ℕ)
    (hN : ∀ g ∈ usubforms f, gateArity g ≤ N)
    (hgates : (usubforms f).toFinset.card < 2 ^ t) :
    ∃ subsets : List (Finset ℕ),
      (Finset.univ.filter (fun x =>
        uArithApproxVal (p := p) subsets f (fun i => embed (x i)) ≠ embed (f.eval x))).card < 2 ^ n := by
  obtain ⟨F, hF⟩ := exists_low_error_family (p := p)
    (fun g : {g // g ∈ (usubforms f).toFinset} => gateRed (N := N) g.val) t
  refine ⟨(List.ofFn F).map (fun S => S.image Fin.val), ?_⟩
  refine whole_circuit_error_lt_of_sum _ f t ?_ hgates
  have hsum_eq : ∑ g ∈ (usubforms f).toFinset,
        (ubadSet (p := p) ((List.ofFn F).map (fun S => S.image Fin.val)) g).card
      = ∑ g : {g // g ∈ (usubforms f).toFinset}, redNumErr (p := p) (gateRed (N := N) g.val) t F := by
    rw [← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    exact gate_card_eq g.val (hN g.val (List.mem_toFinset.mp g.2)) F
  rw [hsum_eq]
  calc 2 ^ t * ∑ g : {g // g ∈ (usubforms f).toFinset}, redNumErr (p := p) (gateRed (N := N) g.val) t F
      ≤ Fintype.card {g // g ∈ (usubforms f).toFinset} * 2 ^ n := hF
    _ = (usubforms f).toFinset.card * 2 ^ n := by rw [Fintype.card_coe]

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.ubadSet_uor_card_eq
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.gate_card_eq
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.whole_circuit_error_exists
