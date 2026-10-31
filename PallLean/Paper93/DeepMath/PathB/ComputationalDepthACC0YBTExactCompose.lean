import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTSocket

/-!
# The YBT exact normal-form socket: exact `SYM∘AND` closure by mixed-radix counting

The Yao–Beigel–Tarui socket `HasExactSymAndForm` (`…ACC0YBTSocket`) asks for an **exact** `SYM∘AND` representation of
an `ACC⁰` circuit.  This file discharges the *existence / decoding* half of that socket as a genuine theorem — and
makes the irreducible remainder (the **size**) precise.

The key construction is Beigel–Tarui's **mixed-radix merge**: two symmetric gates `SYM_{h₁}(g₁)` and `SYM_{h₂}(g₂)`
combine into a *single* symmetric gate over the merged family, by counting in base `m₁+1`.  Concretely, duplicate each
gate of family 2 exactly `m₁+1` times; then the merged count is

```
C(x)  =  c₁(x)  +  (m₁+1)·c₂(x) ,   with c₁ ≤ m₁ < m₁+1,
```

so `C mod (m₁+1) = c₁` and `C div (m₁+1) = c₂` recover *both* counts — and a top
`H(C) = comb(h₁(C mod (m₁+1)), h₂(C div (m₁+1)))` computes any Boolean combination `comb(f,g)` **exactly**.

## What is proved (clean axioms, no `sorry`)

* `HasSymAndForm f s` — `f` equals a `SYM` (count) gate over `≤ s` monomial-`AND`s (function-level, size-tracked).
* Base cases: `hasSymAndForm_const`, `hasSymAndForm_monoAND`, `hasSymAndForm_var`, and **`hasSymAndForm_mod`** (a
  `MOD_q` gate is a symmetric function of its support literals — exact, size `|S|`).
* `hasSymAndForm_not` (unary), and **`hasSymAndForm_combine`** — the headline mixed-radix merge: closed under *any*
  binary `comb : Bool → Bool → Bool`, with size `s₁ + (s₁+1)·s₂`.  Corollaries `hasSymAndForm_and`/`_or`.
* **`acc0circuit_hasSymAndForm`** — *every* `ACC0Circuit` has an exact `SYM∘AND` form (structural recursion over
  `const`/`var`/`not`/`and`/`or`/`mod`), with explicit size `symAndSize C`.
* **`acc0circuit_hasExactSymAndForm`** — the bridge: reindexing to `Fin m` (via `Fintype.equivFin`) yields the
  socket's `HasExactSymAndForm C`, *provided* `symAndSize C + 1 < 2^n`.

## Honest scope — the exactness is proved; the *size* is the wall

This is the **exact** side of YBT, proved in full: the decoding is real, and the socket holds whenever the size fits.
But `symAndSize` is **multiplicative** at every `AND`/`OR` (`s₁ + (s₁+1)·s₂`), so it is **exponential** in the circuit
in general — `symAndSize C + 1 < 2^n` fails for ordinary poly-size circuits.  Getting an exact `SYM∘AND` of
**quasipolynomial** size (true Beigel–Tarui) needs the polynomial method's *additive* degree composition
(`…ACC0AdditiveDegree`), which the corpus has only in **approximate** form (`…ACC0ApproxConsequence`) and which stops
at prime-power `MOD` (`…ACC0ModPExact`, the composite-`MOD` barrier).  So this file converts "the whole YBT socket"
into the sharp residue **"exact + quasipolynomial size simultaneously"** — exactly the wall `…ACC0ExactCompose`
names.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket

variable {n : ℕ}

/-- The count of accepting monomial-`AND` gates, over an arbitrary finite index. -/
def saCount {ι : Type} [Fintype ι] (mono : ι → Finset (Fin n)) (x : Fin n → Bool) : ℕ :=
  ∑ j : ι, if monoAND (mono j) x then 1 else 0

/-- **`f` has an exact `SYM∘AND` form of size `≤ s`**: a count gate over `≤ s` monomial-`AND`s. -/
def HasSymAndForm (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (mono : ι → Finset (Fin n)) (h : ℕ → Bool),
    Fintype.card ι ≤ s ∧ f = fun x => h (saCount mono x)

/-- **The count is `≤` the number of gates (proved).** -/
theorem saCount_le_card {ι : Type} [Fintype ι] (mono : ι → Finset (Fin n)) (x : Fin n → Bool) :
    saCount mono x ≤ Fintype.card ι := by
  unfold saCount
  calc ∑ j : ι, (if monoAND (mono j) x then 1 else 0)
      ≤ ∑ _j : ι, 1 := Finset.sum_le_sum (fun j _ => by split <;> simp)
    _ = Fintype.card ι := by simp [Finset.card_univ]

/-- **A monomial-`AND` of a singleton is the literal (proved).** -/
theorem monoAND_singleton (i : Fin n) (x : Fin n → Bool) :
    monoAND ({i} : Finset (Fin n)) x = x i := by
  unfold monoAND
  cases h : x i <;> simp [h]

/-- **The count over a disjoint union splits additively (proved).** -/
theorem saCount_sum_elim {ι1 T : Type} [Fintype ι1] [Fintype T]
    (m1 : ι1 → Finset (Fin n)) (m2 : T → Finset (Fin n)) (x : Fin n → Bool) :
    saCount (Sum.elim m1 m2) x = saCount m1 x + saCount m2 x := by
  simp only [saCount, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- **The sum of a constant over `Fin r` is `r` times it (proved).** -/
theorem fin_sum_const_nat (r c : ℕ) : (∑ _i : Fin r, c) = r * c := by
  induction r with
  | zero => simp
  | succ k ih => rw [Fin.sum_univ_succ, ih]; ring

/-- **Replicating a family `r` times multiplies its count by `r` (proved): the base-`r` radix step.** -/
theorem saCount_prod_const {T : Type} [Fintype T] (r : ℕ) (m2 : T → Finset (Fin n))
    (x : Fin n → Bool) :
    saCount (fun p : Fin r × T => m2 p.2) x = r * saCount m2 x := by
  simp only [saCount, Fintype.sum_prod_type]
  rw [fin_sum_const_nat r (∑ x_2 : T, if monoAND (m2 x_2) x then (1:ℕ) else 0)]

/-- **Constants have an exact form of size `0` (proved).** -/
theorem hasSymAndForm_const (b : Bool) : HasSymAndForm (fun _ : Fin n → Bool => b) 0 :=
  ⟨Empty, inferInstance, Empty.elim, fun _ => b, by simp, by funext _; rfl⟩

/-- **A monomial-`AND` gate has an exact form of size `1` (proved).** -/
theorem hasSymAndForm_monoAND (S : Finset (Fin n)) :
    HasSymAndForm (fun x => monoAND S x) 1 :=
  ⟨Unit, inferInstance, fun _ => S, fun c => decide (1 ≤ c), by simp, by
    funext x
    simp only [saCount, Finset.univ_unique, Finset.sum_singleton]
    cases monoAND S x <;> rfl⟩

/-- **A variable (literal) has an exact form of size `1` (proved).** -/
theorem hasSymAndForm_var (i : Fin n) : HasSymAndForm (fun x => x i) 1 := by
  have he : (fun x : Fin n → Bool => x i) = fun x => monoAND ({i} : Finset (Fin n)) x := by
    funext x; rw [monoAND_singleton]
  rw [he]; exact hasSymAndForm_monoAND {i}

/-- **`MOD_q` is exactly a symmetric function of its support literals (proved): size `|S|`.**  This is the exact
`SYM∘AND` form of a `MOD` gate — `AND`s of fan-in `1`, top `h(c) = [c ≡ t (mod q)]`. -/
theorem hasSymAndForm_mod (q : ℕ) (S : Finset (Fin n)) (t : ZMod q) :
    HasSymAndForm (fun x => decide (modQStatOn S q x = t)) S.card := by
  refine ⟨{i // i ∈ S}, inferInstance, fun j => ({j.1} : Finset (Fin n)),
    fun c => decide (((c : ℕ) : ZMod q) = t), by rw [Fintype.card_coe], ?_⟩
  funext x
  have hcount : saCount (fun j : {i // i ∈ S} => ({j.1} : Finset (Fin n))) x = weightOn S x := by
    unfold saCount weightOn
    rw [show (∑ j : {i // i ∈ S}, if monoAND ({j.1} : Finset (Fin n)) x then (1:ℕ) else 0)
          = ∑ j : {i // i ∈ S}, if x j.1 then (1:ℕ) else 0 from
          Finset.sum_congr rfl (fun j _ => by rw [monoAND_singleton])]
    exact Finset.sum_coe_sort S (fun i => if x i then (1:ℕ) else 0)
  show decide (modQStatOn S q x = t) = decide (((saCount _ x : ℕ) : ZMod q) = t)
  rw [hcount]
  rfl

/-- **Closed under `NOT` (proved).** -/
theorem hasSymAndForm_not {f : (Fin n → Bool) → Bool} {s : ℕ} (hf : HasSymAndForm f s) :
    HasSymAndForm (fun x => !f x) s := by
  obtain ⟨ι, hι, mono, h, hcard, hfe⟩ := hf
  exact ⟨ι, hι, mono, fun c => !(h c), hcard, by subst hfe; rfl⟩

/-- **The mixed-radix merge (proved): exact `SYM∘AND` is closed under any binary Boolean combiner.**  Two forms of
sizes `s₁, s₂` combine into one of size `s₁ + (s₁+1)·s₂`, via base-`(m₁+1)` counting. -/
theorem hasSymAndForm_combine {f g : (Fin n → Bool) → Bool} {s1 s2 : ℕ}
    (comb : Bool → Bool → Bool) (hf : HasSymAndForm f s1) (hg : HasSymAndForm g s2) :
    HasSymAndForm (fun x => comb (f x) (g x)) (s1 + (s1 + 1) * s2) := by
  obtain ⟨ι1, hι1, mono1, h1, hcard1, hfe⟩ := hf
  obtain ⟨ι2, hι2, mono2, h2, hcard2, hge⟩ := hg
  letI := hι1; letI := hι2
  have hb1 : Fintype.card ι1 ≤ s1 := hcard1
  have hb2 : Fintype.card ι2 ≤ s2 := hcard2
  have hfe2 : f = fun x => h1 (saCount mono1 x) := hfe
  have hge2 : g = fun x => h2 (saCount mono2 x) := hge
  refine ⟨ι1 ⊕ (Fin (Fintype.card ι1 + 1) × ι2), inferInstance,
    Sum.elim mono1 (fun p => mono2 p.2),
    fun c => comb (h1 (c % (Fintype.card ι1 + 1))) (h2 (c / (Fintype.card ι1 + 1))), ?_, ?_⟩
  · -- size bound: card ι1 + (card ι1 + 1) * card ι2 ≤ s1 + (s1+1)*s2
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    exact Nat.add_le_add hb1 (Nat.mul_le_mul (Nat.succ_le_succ hb1) hb2)
  · funext x
    -- the merged count splits as c₁ + (m₁+1)·c₂
    have hsplit : saCount (Sum.elim mono1 (fun p : Fin (Fintype.card ι1 + 1) × ι2 => mono2 p.2)) x
        = saCount mono1 x + (Fintype.card ι1 + 1) * saCount mono2 x := by
      rw [saCount_sum_elim, saCount_prod_const]
    have hc1 : saCount mono1 x < Fintype.card ι1 + 1 :=
      Nat.lt_succ_of_le (saCount_le_card mono1 x)
    show comb (f x) (g x)
        = comb (h1 (saCount (Sum.elim mono1 (fun p : Fin (Fintype.card ι1 + 1) × ι2 => mono2 p.2)) x
                    % (Fintype.card ι1 + 1)))
               (h2 (saCount (Sum.elim mono1 (fun p : Fin (Fintype.card ι1 + 1) × ι2 => mono2 p.2)) x
                    / (Fintype.card ι1 + 1)))
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc1,
      Nat.add_mul_div_left _ _ (Nat.succ_pos _), Nat.div_eq_of_lt hc1, Nat.zero_add, hfe2, hge2]

/-- **Closed under `AND` (proved).** -/
theorem hasSymAndForm_and {f g : (Fin n → Bool) → Bool} {s1 s2 : ℕ}
    (hf : HasSymAndForm f s1) (hg : HasSymAndForm g s2) :
    HasSymAndForm (fun x => f x && g x) (s1 + (s1 + 1) * s2) :=
  hasSymAndForm_combine (· && ·) hf hg

/-- **Closed under `OR` (proved).** -/
theorem hasSymAndForm_or {f g : (Fin n → Bool) → Bool} {s1 s2 : ℕ}
    (hf : HasSymAndForm f s1) (hg : HasSymAndForm g s2) :
    HasSymAndForm (fun x => f x || g x) (s1 + (s1 + 1) * s2) :=
  hasSymAndForm_combine (· || ·) hf hg

/-- The size of the exact `SYM∘AND` form produced by the structural construction (multiplicative at `AND`/`OR`). -/
def symAndSize : ACC0Circuit n → ℕ
  | .const _ => 0
  | .var _ => 1
  | .not c => symAndSize c
  | .and a b => symAndSize a + (symAndSize a + 1) * symAndSize b
  | .or a b => symAndSize a + (symAndSize a + 1) * symAndSize b
  | .mod _ S _ => S.card

/-- **Every `ACC0Circuit` has an exact `SYM∘AND` form (proved), of size `symAndSize C`.**  Structural recursion:
`const`/`var`/`mod` are base symmetric gates; `not` is free; `and`/`or` use the mixed-radix merge. -/
theorem acc0circuit_hasSymAndForm :
    ∀ C : ACC0Circuit n, HasSymAndForm (fun x => eval C x) (symAndSize C)
  | .const b => hasSymAndForm_const b
  | .var i => hasSymAndForm_var i
  | .not c => hasSymAndForm_not (acc0circuit_hasSymAndForm c)
  | .and a b => hasSymAndForm_and (acc0circuit_hasSymAndForm a) (acc0circuit_hasSymAndForm b)
  | .or a b => hasSymAndForm_or (acc0circuit_hasSymAndForm a) (acc0circuit_hasSymAndForm b)
  | .mod q S t => hasSymAndForm_mod q S t

/-- **The bridge to the socket `Fin m` shape (proved): reindex a `HasSymAndForm` to `Fin (card)`.** -/
theorem hasExactSymAndForm_of_hasSymAndForm {f : (Fin n → Bool) → Bool} {s : ℕ}
    (hf : HasSymAndForm f s) (hs : s + 1 < 2 ^ n) :
    ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool),
      f = symEval (fun j x => monoAND (mono j) x) h ∧ m + 1 < 2 ^ n := by
  obtain ⟨ι, hι, mono, h, hcard, hfe⟩ := hf
  refine ⟨@Fintype.card ι hι, fun j => mono ((@Fintype.equivFin ι hι).symm j), h, ?_,
    lt_of_le_of_lt (Nat.succ_le_succ hcard) hs⟩
  funext x
  rw [hfe]
  simp only [symEval, gateCount, saCount]
  congr 1
  exact (Equiv.sum_comp (@Fintype.equivFin ι hι).symm
    (fun i => if monoAND (mono i) x then 1 else 0)).symm

/-- **The socket, discharged whenever the (exact-form) size fits (proved).**  `acc0circuit_hasSymAndForm` always
produces an exact `SYM∘AND`; once `symAndSize C + 1 < 2^n` it *is* the socket `HasExactSymAndForm C`.  The hypothesis
is the wall: `symAndSize` is exponential in general (multiplicative at every `AND`/`OR`). -/
theorem acc0circuit_hasExactSymAndForm (C : ACC0Circuit n) (hsize : symAndSize C + 1 < 2 ^ n) :
    HasExactSymAndForm C :=
  hasExactSymAndForm_of_hasSymAndForm (acc0circuit_hasSymAndForm C) hsize

end PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose.hasSymAndForm_combine
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose.acc0circuit_hasSymAndForm
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose.acc0circuit_hasExactSymAndForm
