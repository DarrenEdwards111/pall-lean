import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameGlobalInterfaceBound

/-!
# N-Frame: the trace-extraction dictionary — wire frontiers meet the global bound

The extraction interface, built as a dictionary per HAL's plan, with **one honest correction**.
HAL's step 3 asked: "communication through `r` frontier wires ⇒ coordinate-interfaced factorization
with `|A ∩ B| ≤ O(r)`."  In the coordinate form this is **false**: a shared subtree routes
arbitrarily many coordinates through **one** frontier wire, so the coordinate interface of the
natural cut is unbounded in `r`.  The true bridge object is the **trace-interfaced factorization**,
where the interface is the `r` wire *values*, not their cone's coordinates:

  `TraceInterfacedFactorization f S j` — `f = op (G, H)` with `H` blind on `S`, and `G` determined
        by the `S`-coordinates plus a `j`-bit trace `φ` that is itself blind on `S`.
  `trace_split_row_capacity` / `rows_force_trace` — **PROVED, the corrected step 3**: pairwise
        distinct rows over `S` are bounded by `2^(j+1)` — rows are determined by `(φ y, H y)`.
        This is the engine on which the excess-side upgrade runs: for the circuit's top cut,
        `φ` = exit-wire values and `j` = #exit wires `≤ coneExcess`.
  `varsOf` / `varsOf_agree_wire` / `top_split_eval` — steps 1–2: the coordinate support of a cone
        and the excess-free top-cut evaluation split.
  `sat3_top_cut_dichotomy` — **PROVED, the first instantiation**: for every minimal SAT circuit,
        the root is a binary gate whose children's cones satisfy: `Ω(m)` **shared variables**
        (`m ≤ 2·|varsOf L ∩ varsOf R| + 4`), or one child's variable support **swallows** the
        other's.  This is the global PAC bound speaking directly about circuits.

## Honest scope

The dichotomy's first branch bounds shared *variables*, not excess — a shared subtree makes the two
quantities incomparable, which is exactly why the trace engine exists.  The remaining rungs to
`coneExcess ≥ Ω(m)`: (1) the exit-set instantiation (`φ` from wire values via `frontier_val_agree`,
`j` = #exits charged to `coneExcess` via the multi-reader bound); (2) the swallowed-side recursion;
(3) the trace upgrade of the counting arc — the row-capacity family upgrades mechanically, the
coordinate-interning counts do **not**, and that residue is the genuine remaining semantic work.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE CORRECTED BRIDGE OBJECT**: a factorization whose interface is a `j`-bit wire trace — `H`
blind on `S`, `G` determined by the `S`-coordinates plus the trace, the trace blind on `S`. -/
def TraceInterfacedFactorization {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) (j : ℕ) : Prop :=
  ∃ (op : Bool → Bool → Bool) (G H : (Fin n → Bool) → Bool)
    (φ : (Fin n → Bool) → (Fin j → Bool)),
    (∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → φ x = φ y) ∧
    (∀ x y : Fin n → Bool, (∀ i, i ∈ S → x i = y i) → φ x = φ y → G x = G y) ∧
    (∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → H x = H y) ∧
    (∀ x, f x = op (G x) (H x))

/-- **THE TRACE ROW-CAPACITY ENGINE (proved)**: pairwise-distinct rows over `S` are bounded by
`2^(j+1)` — every row is determined by its trace `(φ y, H y)`. -/
theorem trace_split_row_capacity {n j : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) (op : Bool → Bool → Bool)
    (G H : (Fin n → Bool) → Bool) (φ : (Fin n → Bool) → (Fin j → Bool))
    (hφ : ∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → φ x = φ y)
    (hG : ∀ x y : Fin n → Bool, (∀ i, i ∈ S → x i = y i) → φ x = φ y → G x = G y)
    (hH : ∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → H x = H y)
    (hf : ∀ x, f x = op (G x) (H x))
    (Y : Finset (Fin n → Bool))
    (hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, f (mixOn S x y) ≠ f (mixOn S x y')) :
    Y.card ≤ 2 ^ (j + 1) := by
  classical
  by_contra hbig
  push_neg at hbig
  set ψ : (Fin n → Bool) → ((Fin j → Bool) × Bool) :=
    fun y => (φ y, H y) with hψ
  have hcard : (Finset.univ : Finset ((Fin j → Bool) × Bool)).card < Y.card := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
    have h2 : (2 : ℕ) ^ j * 2 = 2 ^ (j + 1) := by
      rw [pow_succ]
    omega
  obtain ⟨y, hy, y', hy', hne, hcol⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (fun y _ => Finset.mem_univ (ψ y))
  have hφeq : φ y = φ y' := congrArg Prod.fst hcol
  have hHeq : H y = H y' := congrArg Prod.snd hcol
  have hrows : ∀ x, f (mixOn S x y) = f (mixOn S x y') := by
    intro x
    rw [hf, hf]
    have hmix : ∀ (z : Fin n → Bool) (i : Fin n), i ∉ S → mixOn S x z i = z i := by
      intro z i hi
      show (if i ∈ S then x i else z i) = z i
      rw [if_neg hi]
    have hφy : φ (mixOn S x y) = φ y := hφ _ _ (hmix y)
    have hφy' : φ (mixOn S x y') = φ y' := hφ _ _ (hmix y')
    congr 1
    · apply hG
      · intro i hi
        show (if i ∈ S then x i else y i) = (if i ∈ S then x i else y' i)
        rw [if_pos hi, if_pos hi]
      · rw [hφy, hφy', hφeq]
    · have h1 : H (mixOn S x y) = H y := hH _ _ (hmix y)
      have h2 : H (mixOn S x y') = H y' := hH _ _ (hmix y')
      rw [h1, h2, hHeq]
  obtain ⟨x, hx⟩ := hdist y hy y' hy' hne
  exact hx (hrows x)

/-- **THE CONTRAPOSITIVE (proved)**: more than `2^(k+1)` pairwise-distinct rows force a trace wider
than `k` — many rows cannot flow through few wires. -/
theorem rows_force_trace {n j : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) (op : Bool → Bool → Bool)
    (G H : (Fin n → Bool) → Bool) (φ : (Fin n → Bool) → (Fin j → Bool))
    (hφ : ∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → φ x = φ y)
    (hG : ∀ x y : Fin n → Bool, (∀ i, i ∈ S → x i = y i) → φ x = φ y → G x = G y)
    (hH : ∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → H x = H y)
    (hf : ∀ x, f x = op (G x) (H x))
    (Y : Finset (Fin n → Bool))
    (hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, f (mixOn S x y) ≠ f (mixOn S x y'))
    (k : ℕ) (hY : 2 ^ (k + 1) < Y.card) : k < j := by
  by_contra hcon
  push_neg at hcon
  have h1 := trace_split_row_capacity f S op G H φ hφ hG hH hf Y hdist
  have h2 : (2 : ℕ) ^ (j + 1) ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

open Classical in
/-- The coordinate support of a cone: the variables its gates read. -/
noncomputable def varsOf {n : ℕ} (c : List (CGate n)) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ p ∈ coneOf c r,
    c.getD p (CGate.cst false) = CGate.var i)

/-- Agreement on a cone's variable support determines its wire value. -/
theorem varsOf_agree_wire {n : ℕ} (c : List (CGate n)) (r : ℕ)
    (x y : Fin n → Bool) (hxy : ∀ i ∈ varsOf c r, x i = y i) :
    (runFrom x [] c).getD r false = (runFrom y [] c).getD r false := by
  classical
  apply cone_val_agree c r x y ?_ r (cone_self c r)
  intro p hp i hgate
  apply hxy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, p, hp, hgate⟩

/-- **THE EXCESS-FREE TOP SPLIT (proved)**: a binary root evaluates as `op` of its children's wire
values — no excess hypothesis. -/
theorem top_split_eval {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (op : Bool → Bool → Bool) (L R : ℕ)
    (hroot : c.getD (c.length - 1) (CGate.cst false) = CGate.bin op L R)
    (hLlt : L < c.length - 1) (hRlt : R < c.length - 1) :
    ∀ x : Fin n → Bool,
      f x = op ((runFrom x [] c).getD L false) ((runFrom x [] c).getD R false) := by
  intro x
  have h : (runFrom x [] c).getD (c.length - 1) false = f x := hcomp x
  rw [← h, output_getD_at x c (c.length - 1) (by omega), hroot]
  show op ((runFrom x [] (c.take (c.length - 1))).getD L false)
      ((runFrom x [] (c.take (c.length - 1))).getD R false)
    = op ((runFrom x [] c).getD L false) ((runFrom x [] c).getD R false)
  have hpre : ∀ q, q < c.length - 1 →
      (runFrom x [] (c.take (c.length - 1))).getD q false
        = (runFrom x [] c).getD q false := by
    intro q hq
    have hVlen : (runFrom x [] (c.take (c.length - 1))).length = c.length - 1 := by
      rw [runFrom_length]
      simp only [List.length_nil, List.length_take]
      omega
    have hfull : runFrom x [] c
        = runFrom x (runFrom x [] (c.take (c.length - 1))) (c.drop (c.length - 1)) := by
      conv_lhs => rw [← List.take_append_drop (c.length - 1) c]
      rw [runFrom_append]
    rw [hfull, runFrom_getD_stable x (c.drop (c.length - 1))
      (runFrom x [] (c.take (c.length - 1))) q (by rw [hVlen]; omega)]
  rw [hpre L hLlt, hpre R hRlt]

/-- **THE TOP-CUT DICHOTOMY (proved)**: every minimal SAT circuit's root children satisfy — `Ω(m)`
shared variables between their cones, or one cone's variable support swallows the other's.  The
global PAC bound, speaking directly about circuits. -/
theorem sat3_top_cut_dichotomy (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hDN : sat3M N * sat3D N = N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) :
    ∃ (op : Bool → Bool → Bool) (L R : ℕ),
      c.getD (c.length - 1) (CGate.cst false) = CGate.bin op L R ∧
      (sat3M N ≤ 2 * (varsOf c L ∩ varsOf c R).card + 4
        ∨ varsOf c L \ varsOf c R = ∅
        ∨ varsOf c R \ varsOf c L = ∅) := by
  classical
  obtain ⟨op, L, R, hroot, hL, hR, hLR⟩ :=
    sat3_root_shape N hv hm3 hk c hcomp hmin
  refine ⟨op, L, R, hroot, ?_⟩
  by_cases hpL : varsOf c L \ varsOf c R = ∅
  · exact Or.inr (Or.inl hpL)
  by_cases hpR : varsOf c R \ varsOf c L = ∅
  · exact Or.inr (Or.inr hpR)
  left
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hpL
  obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hpR
  exact sat3_global_interface_bound N hv hm3 hk hDN op
    (fun x => (runFrom x [] c).getD L false)
    (fun x => (runFrom x [] c).getD R false)
    (varsOf c L) (varsOf c R)
    (fun x y hxy => varsOf_agree_wire c L x y hxy)
    (fun x y hxy => varsOf_agree_wire c R x y hxy)
    (top_split_eval (sat3Family N) c hcomp op L R hroot hL hR)
    p hp q hq

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.trace_split_row_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.top_split_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_top_cut_dichotomy
