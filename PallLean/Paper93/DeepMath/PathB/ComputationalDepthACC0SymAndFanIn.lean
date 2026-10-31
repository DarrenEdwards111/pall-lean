import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTExactCompose

/-!
# The per-layer merge over the concrete `ACC0Circuit` datatype — fan-in tracking

Entry 168 reduced `FanInStaysPolylog` to a single per-layer merge: that composing a gate's children's `SYM∘AND` forms
controls the bottom AND fan-in.  This file does that merge **over the concrete `ACC0Circuit` datatype**
(`…ACC0CircuitModel`), refining the existing `HasSymAndForm` (`…ACC0YBTExactCompose`, which tracks only the *count* of
AND gates) to **also track the AND fan-in** `w` (the max literal-count of any monomial).

The result clarifies the BT picture sharply and honestly:

* **The per-layer fan-in merge is `max` — no growth (proved).**  Composing two forms of fan-in `w₁, w₂` under any binary
  Boolean combiner yields fan-in `max w₁ w₂`: the merged monomials are exactly the children's monomials (disjoint-union
  + replication of the count construction), so their literal-counts are unchanged.  `NOT` preserves fan-in.
* **Every `ACC0Circuit` has fan-in `≤ 1` in this representation (proved).**  The base gates are singleton-AND symmetric
  gates (`var`, `mod` are sums of single literals, fan-in `1`; `const` fan-in `0`), and `max`/`NOT` preserve `≤ 1`.  So
  in the *exact* `SYM∘AND` form the bottom AND fan-in is trivially bounded — fan-in is **not** the bottleneck.

The honest consequence: in this exact representation the per-layer fan-in merge is `max` (factor `1` in the entry-168
recurrence), discharging the fan-in side of `FanInStaysPolylog` completely.  The genuine Beigel–Tarui wall is therefore
*not* the fan-in but the **count** (`symAndSize`, multiplicative `s₁+(s₁+1)·s₂` at each `AND`/`OR`, hence exponential);
taming that count to quasipolynomial is the polynomial-method / additive-degree content (`…ACC0AdditiveDegree`,
approximate only, prime-power `MOD`) — the recognised wall, unchanged.

## What is proved (clean axioms, no `sorry`)

* **`HasSymAndFormFanIn f s w`** — `f` is a count gate over `≤ s` monomial-`AND`s each of fan-in `≤ w`.
* base cases **`…_const` / `…_monoAND` / `…_var` / `…_mod`**, **`…_not`**, the merge **`hasSymAndFormFanIn_combine`**
  (fan-in `max w₁ w₂`, size `s₁+(s₁+1)·s₂`) and `…_and` / `…_or`.
* **`acc0circuit_hasSymAndFormFanIn`** — every `ACC0Circuit` has such a form with size `symAndSize C` and fan-in
  `fanInBound C`; **`fanInBound_le_one`** — `fanInBound C ≤ 1`.

## Honest scope

This formalises the per-layer merge for the **fan-in** measure over the concrete datatype, and shows fan-in is `≤ 1`
here (not the bottleneck).  It does **not** produce the quasipolynomial *count* bound — that is the Beigel–Tarui
mixed-radix/additive-degree content (a proven classical theorem; `NEXP ⊄ ACC⁰` is Williams 2011, also proven), whose
full formalisation is the large remaining work.  Nothing here is a new separation, an open problem, or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit eval)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (modQStatOn weightOn)
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose
  (saCount HasSymAndForm saCount_le_card monoAND_singleton saCount_sum_elim saCount_prod_const symAndSize)

variable {n : ℕ}

/-- **`f` has an exact `SYM∘AND` form of size `≤ s` and AND fan-in `≤ w`** (refines `HasSymAndForm` with a fan-in
bound). -/
def HasSymAndFormFanIn (f : (Fin n → Bool) → Bool) (s w : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (mono : ι → Finset (Fin n)) (h : ℕ → Bool),
    Fintype.card ι ≤ s ∧ (∀ j, (mono j).card ≤ w) ∧ f = fun x => h (saCount mono x)

/-- **Constants: size `0`, fan-in `0` (proved).** -/
theorem hasSymAndFormFanIn_const (b : Bool) :
    HasSymAndFormFanIn (fun _ : Fin n → Bool => b) 0 0 :=
  ⟨Empty, inferInstance, Empty.elim, fun _ => b, by simp, fun j => j.elim, by funext _; rfl⟩

/-- **A monomial-`AND` over `S`: size `1`, fan-in `S.card` (proved).** -/
theorem hasSymAndFormFanIn_monoAND (S : Finset (Fin n)) :
    HasSymAndFormFanIn (fun x => monoAND S x) 1 S.card :=
  ⟨Unit, inferInstance, fun _ => S, fun c => decide (1 ≤ c), by simp, fun _ => le_refl _, by
    funext x
    simp only [saCount, Finset.univ_unique, Finset.sum_singleton]
    cases monoAND S x <;> rfl⟩

/-- **A variable (literal): size `1`, fan-in `1` (proved).** -/
theorem hasSymAndFormFanIn_var (i : Fin n) :
    HasSymAndFormFanIn (fun x => x i) 1 1 := by
  have he : (fun x : Fin n → Bool => x i) = fun x => monoAND ({i} : Finset (Fin n)) x := by
    funext x; rw [monoAND_singleton]
  rw [he]
  have := hasSymAndFormFanIn_monoAND ({i} : Finset (Fin n))
  simpa using this

/-- **`MOD_q` is a symmetric function of single-literal `AND`s: size `|S|`, fan-in `1` (proved).** -/
theorem hasSymAndFormFanIn_mod (q : ℕ) (S : Finset (Fin n)) (t : ZMod q) :
    HasSymAndFormFanIn (fun x => decide (modQStatOn S q x = t)) S.card 1 := by
  refine ⟨{i // i ∈ S}, inferInstance, fun j => ({j.1} : Finset (Fin n)),
    fun c => decide (((c : ℕ) : ZMod q) = t), by rw [Fintype.card_coe], fun _ => by simp, ?_⟩
  funext x
  have hcount : saCount (fun j : {i // i ∈ S} => ({j.1} : Finset (Fin n))) x
      = weightOn S x := by
    unfold saCount weightOn
    rw [show (∑ j : {i // i ∈ S}, if monoAND ({j.1} : Finset (Fin n)) x then (1:ℕ) else 0)
          = ∑ j : {i // i ∈ S}, if x j.1 then (1:ℕ) else 0 from
          Finset.sum_congr rfl (fun j _ => by rw [monoAND_singleton])]
    exact Finset.sum_coe_sort S (fun i => if x i then (1:ℕ) else 0)
  show decide (modQStatOn S q x = t) = decide (((saCount _ x : ℕ) : ZMod q) = t)
  rw [hcount]; rfl

/-- **Closed under `NOT`: preserves size and fan-in (proved).** -/
theorem hasSymAndFormFanIn_not {f : (Fin n → Bool) → Bool} {s w : ℕ}
    (hf : HasSymAndFormFanIn f s w) : HasSymAndFormFanIn (fun x => !f x) s w := by
  obtain ⟨ι, hι, mono, h, hcard, hfan, hfe⟩ := hf
  exact ⟨ι, hι, mono, fun c => !(h c), hcard, hfan, by subst hfe; rfl⟩

/-- **The per-layer merge (proved): fan-in is `max w₁ w₂` — no growth.**  Any binary combiner merges two forms into one
of size `s₁+(s₁+1)·s₂` (the multiplicative count blow-up) but fan-in only `max w₁ w₂`: the merged monomials are exactly
the children's (disjoint-union + replication), so their literal-counts are unchanged. -/
theorem hasSymAndFormFanIn_combine {f g : (Fin n → Bool) → Bool} {s1 s2 w1 w2 : ℕ}
    (comb : Bool → Bool → Bool) (hf : HasSymAndFormFanIn f s1 w1) (hg : HasSymAndFormFanIn g s2 w2) :
    HasSymAndFormFanIn (fun x => comb (f x) (g x)) (s1 + (s1 + 1) * s2) (max w1 w2) := by
  obtain ⟨ι1, hι1, mono1, h1, hcard1, hfan1, hfe⟩ := hf
  obtain ⟨ι2, hι2, mono2, h2, hcard2, hfan2, hge⟩ := hg
  letI := hι1; letI := hι2
  have hfe2 : f = fun x => h1 (saCount mono1 x) := hfe
  have hge2 : g = fun x => h2 (saCount mono2 x) := hge
  refine ⟨ι1 ⊕ (Fin (Fintype.card ι1 + 1) × ι2), inferInstance,
    Sum.elim mono1 (fun p => mono2 p.2),
    fun c => comb (h1 (c % (Fintype.card ι1 + 1))) (h2 (c / (Fintype.card ι1 + 1))), ?_, ?_, ?_⟩
  · rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    exact Nat.add_le_add hcard1 (Nat.mul_le_mul (Nat.succ_le_succ hcard1) hcard2)
  · rintro (a | p)
    · exact le_trans (hfan1 a) (le_max_left w1 w2)
    · exact le_trans (hfan2 p.2) (le_max_right w1 w2)
  · funext x
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
theorem hasSymAndFormFanIn_and {f g : (Fin n → Bool) → Bool} {s1 s2 w1 w2 : ℕ}
    (hf : HasSymAndFormFanIn f s1 w1) (hg : HasSymAndFormFanIn g s2 w2) :
    HasSymAndFormFanIn (fun x => f x && g x) (s1 + (s1 + 1) * s2) (max w1 w2) :=
  hasSymAndFormFanIn_combine (· && ·) hf hg

/-- **Closed under `OR` (proved).** -/
theorem hasSymAndFormFanIn_or {f g : (Fin n → Bool) → Bool} {s1 s2 w1 w2 : ℕ}
    (hf : HasSymAndFormFanIn f s1 w1) (hg : HasSymAndFormFanIn g s2 w2) :
    HasSymAndFormFanIn (fun x => f x || g x) (s1 + (s1 + 1) * s2) (max w1 w2) :=
  hasSymAndFormFanIn_combine (· || ·) hf hg

/-- The bottom AND fan-in produced by the structural `SYM∘AND` construction. -/
def fanInBound : ACC0Circuit n → ℕ
  | .const _ => 0
  | .var _ => 1
  | .not c => fanInBound c
  | .and a b => max (fanInBound a) (fanInBound b)
  | .or a b => max (fanInBound a) (fanInBound b)
  | .mod _ _ _ => 1

/-- **Every `ACC0Circuit` has a `SYM∘AND` form with size `symAndSize C` and fan-in `fanInBound C` (proved).** -/
theorem acc0circuit_hasSymAndFormFanIn :
    ∀ C : ACC0Circuit n, HasSymAndFormFanIn (fun x => eval C x)
      (symAndSize C) (fanInBound C)
  | .const b => hasSymAndFormFanIn_const b
  | .var i => hasSymAndFormFanIn_var i
  | .not c => hasSymAndFormFanIn_not (acc0circuit_hasSymAndFormFanIn c)
  | .and a b => hasSymAndFormFanIn_and (acc0circuit_hasSymAndFormFanIn a) (acc0circuit_hasSymAndFormFanIn b)
  | .or a b => hasSymAndFormFanIn_or (acc0circuit_hasSymAndFormFanIn a) (acc0circuit_hasSymAndFormFanIn b)
  | .mod q S t => hasSymAndFormFanIn_mod q S t

/-- **The fan-in is `≤ 1` in the exact representation (proved).**  Bottom `AND`s are single literals — so fan-in is
*not* the Beigel–Tarui bottleneck; the count `symAndSize` (multiplicative, exponential) is. -/
theorem fanInBound_le_one : ∀ C : ACC0Circuit n, fanInBound C ≤ 1
  | .const _ => by simp [fanInBound]
  | .var _ => by simp [fanInBound]
  | .not c => by simpa [fanInBound] using fanInBound_le_one c
  | .and a b => by simp only [fanInBound]; exact max_le (fanInBound_le_one a) (fanInBound_le_one b)
  | .or a b => by simp only [fanInBound]; exact max_le (fanInBound_le_one a) (fanInBound_le_one b)
  | .mod _ _ _ => by simp [fanInBound]

end PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn.hasSymAndFormFanIn_combine
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn.acc0circuit_hasSymAndFormFanIn
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn.fanInBound_le_one
