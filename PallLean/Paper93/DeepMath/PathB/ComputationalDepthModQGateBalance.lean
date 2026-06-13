import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolonomyBalanceFragments

/-!
# Testing the ACC⁰‑approximation bridge on a single `MOD q` gate

`…HolonomyBalanceFragments` bit *restricted* predictors via a **missed parity variable**: a predictor that never
reads some `v ∈ D` is invariant under `flipAt v`, an involution that toggles the holonomy parity, forcing exact
per‑class balance.  The named open bridge `ACC0ApproximatesByLowRankPredictors` asked what happens for a genuine
ACC⁰ gate that reads *all* variables, where no unread coordinate exists.  Here we run the smallest such case
explicitly: a single `MOD q` gate.

A `MOD q` gate is the cleanest **low‑rank predictor**: it depends on the input only through the count statistic
`modQStat q x = (∑_i x_i) ∈ ZMod q`, i.e. it factors through `q` classes.  But the missed‑variable involution
*breaks*: flipping one coordinate `v ∈ D` changes the count by `±1`, so it leaves the `MOD q` class — the very
obstruction the bridge predicted.

## What survives — a count‑preserving pair swap

The fix is a **two‑coordinate swap** `pairSwap v w`: flip `v ∈ D` *and* a witness `w ∉ D` simultaneously.  On the
**off‑diagonal** set `{x : x_v ≠ x_w}` this is a fixed‑point‑free involution that

* **preserves the count exactly** (`modQStat_pairSwap_offdiag`: one coordinate goes `0→1`, the other `1→0`), hence
  preserves the `MOD q` class — unlike the single flip; and
* **toggles the holonomy parity** (`fParity_pairSwap`: only `v ∈ D` lies in the parity support).

So `balanced_per_class_of_involution` applies *on the off‑diagonal*, giving **exact per‑class balance there** and,
via the engine seed, **no correlation advantage of the `MOD q` gate against the holonomy parity on the
off‑diagonal** (`modQ_gate_low_correlation_offdiagonal`).

## What is proved (clean axioms, no `sorry`)

* `modQStat`, `pairSwap` (+ `pairSwap_v/_w/_other`, `pairSwap_involutive`) — the explicit low‑rank statistic and
  the count‑preserving involution.
* `modQStat_pairSwap_offdiag` — the swap preserves the `MOD q` count off‑diagonal.
* `fParity_pairSwap` — the swap toggles the holonomy parity.
* `modQ_class_balanced_offdiagonal` — **exact balance of the holonomy parity inside each `MOD q` class, on the
  off‑diagonal**.
* `offdiag_balanced` — the same for *every* residue (empty classes trivially balanced).
* `modQ_gate_low_correlation_offdiagonal` — **`2 · agreement ≤ #off‑diagonal inputs`**: the `MOD q` gate has no
  correlation advantage against the holonomy parity on the off‑diagonal.
* `modQ_class_imbalance_on_diagonal` — **the localization theorem**: the holonomy‑parity imbalance of a whole
  `MOD q` class *equals* the imbalance of its diagonal `{x_v = x_w}` — the off‑diagonal contributes exactly
  nothing.  So "the entire residual lives on the diagonal" is a *theorem*, not an observation
  (`card_eq_offdiag_add_diag` split + `balanced_of_involution` off‑diagonal balance).
* `modQStat_two_pairSwap`, `modQ2_diagonal_balanced`, `modQ2_class_balanced`, `modQ2_gate_zero_correlation` —
  **the recursion closes for `q = 2`**: on the diagonal the flip‑both involution changes the count by `±2`, which
  is `0` mod `2`, so the diagonal is balanced too — giving **exact zero correlation advantage of a `MOD 2` gate
  against any holonomy parity** (`D ⊊` variables), over *all* inputs.
* `imbalance_localize_step`, `imbalance_stacked` — **disjoint pair stacking, all `q`**: each fresh disjoint pair
  `(v_i ∈ D, w_i ∉ D)` peels off an exactly‑balanced layer (its off‑diagonal flip‑both moves one coordinate
  `0→1`, the other `1→0`, count change `0` mod any `q`, leaving earlier pairs untouched), confining the imbalance
  of a `MOD q` class to the `k`‑fold diagonal `⋂_i {x_{v_i} = x_{w_i}}` — for `q > 2` too.

## The honest verdict — the approximate version *partly* survives, and the residual is named exactly

The count‑preserving pair swap recovers what the single flip lost — but **only off the diagonal**.  On the
diagonal `{x_v = x_w}` flipping the pair changes the count by `±2`, so it leaves the `MOD q` class and the
involution gives nothing.  Hence the full‑class balance does **not** follow by involution; the entire residual
imbalance lives on the diagonal — now a *theorem* (`modQ_class_imbalance_on_diagonal`: full‑class imbalance =
diagonal imbalance), not just an observation.  That residual is exactly the classical
**`MOD q`‑vs‑parity correlation**, which
is exponentially small in `n − |D|` (a Fourier/character estimate: the imbalance is
`2^{-Ω(n)} · ∑_{j≠0} (1±ω^j)^{n-|D|}(…)^{|D|}`, all main terms cancelling) — but its smallness is an *analytic
recursion*, not an involution, and is **not** supplied here.  This is `ModQParityCorrelationExpSmall` below, named
honestly: the approximate bridge survives as a count‑preserving symmetry off‑diagonal, and the remaining
diagonal residual is the genuine Razborov–Smolensky‑flavoured correlation bound — the same `NP ⊄ ACC⁰`‑strength
content the fragment route always reduces to.  The test confirms the engine's prediction *precisely*: an unread
coordinate gives exact balance; a *read* low‑rank statistic gives balance on the symmetric part and an
exponentially small, analytically‑bounded deficit on the rest.

**Attacking the diagonal recursively settles the modulus split.**  The closing question — does the diagonal
recursion bottom out at an involutive bound or at the character sum? — has a clean answer: it depends on `q`.  On
the diagonal the only count‑preserving parity‑toggling move is the flip‑both involution (count change `±2`).  For
`q = 2` that `±2` is `0`, so the diagonal is exactly balanced and the recursion **closes** — `MOD 2` has *exactly
zero* correlation advantage against any holonomy parity over `D ⊊` variables, fully by involution
(`modQ2_gate_zero_correlation`).  For `q > 2` the single‑pair flip‑both is blocked, but **disjoint pair stacking**
(`imbalance_stacked`) keeps the recursion going: each fresh disjoint pair `(v_i ∈ D, w_i ∉ D)` flips one‑up /
one‑down (count change `0` mod *any* `q`) and peels another balanced layer, confining the `q > 2` imbalance to the
`k`‑fold diagonal `⋂_i {x_{v_i} = x_{w_i}}`.  So even for `q > 2` involution does real work — it shrinks the
imbalance‑carrying support pair by pair — and only the *final core* (no fresh disjoint `(in‑D, out‑D)` pair left)
is the genuine character sum.  The clean delineation: modulus `2` is fully involutive; higher moduli are involutive
down to a shrinking diagonal core, with the character sum needed only there.
-/

namespace PallLean.Paper93.DeepMath.PathB.ModQGateBalance

open PallLean.Paper93.DeepMath.PathB.HolonomyCorrelationEngine
open PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments

variable {n : ℕ}

/-! ## The explicit low‑rank statistic and the count‑preserving involution -/

/-- The `MOD q` count statistic: a single `ZMod q`‑valued observable (`q` classes). -/
def modQStat (q : ℕ) (x : Fin n → Bool) : ZMod q :=
  ∑ i, (if x i then (1 : ZMod q) else 0)

/-- Simultaneously flip coordinates `v` and `w`. -/
def pairSwap (v w : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = v then !(x v) else if i = w then !(x w) else x i

@[simp] theorem pairSwap_v (v w : Fin n) (x : Fin n → Bool) : pairSwap v w x v = !(x v) := by
  simp [pairSwap]

theorem pairSwap_w (v w : Fin n) (x : Fin n → Bool) (h : w ≠ v) : pairSwap v w x w = !(x w) := by
  simp [pairSwap, h]

theorem pairSwap_other (v w : Fin n) (x : Fin n → Bool) {i : Fin n} (hv : i ≠ v) (hw : i ≠ w) :
    pairSwap v w x i = x i := by
  simp only [pairSwap, if_neg hv, if_neg hw]

theorem pairSwap_involutive (v w : Fin n) (h : v ≠ w) (x : Fin n → Bool) :
    pairSwap v w (pairSwap v w x) = x := by
  funext i
  rcases eq_or_ne i v with rfl | hiv
  · rw [pairSwap_v, pairSwap_v, Bool.not_not]
  · rcases eq_or_ne i w with rfl | hiw
    · rw [pairSwap_w _ _ _ h.symm, pairSwap_w _ _ _ h.symm, Bool.not_not]
    · rw [pairSwap_other _ _ _ hiv hiw, pairSwap_other _ _ _ hiv hiw]

/-- `¬a ≠ ¬b` whenever `a ≠ b` (used to keep the off‑diagonal stable under the swap). -/
theorem bool_not_ne : ∀ a b : Bool, a ≠ b → (!a) ≠ (!b) := by decide

/-- **Global balance from a sign‑reversing involution (proved).**  The class‑free specialisation of
`balanced_per_class_of_involution`: an involution on `Inputs` that toggles `f` forces `#{f=true} = #{f=false}`. -/
theorem balanced_of_involution {ι : Type*} (Inputs : Finset ι) (f : ι → Bool) (τ : ι → ι)
    (hmem : ∀ x ∈ Inputs, τ x ∈ Inputs) (hinv : ∀ x ∈ Inputs, τ (τ x) = x)
    (hflip : ∀ x ∈ Inputs, f (τ x) = !(f x)) :
    (Inputs.filter (fun x => f x = true)).card = (Inputs.filter (fun x => f x = false)).card := by
  refine Finset.card_nbij' τ τ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    exact ⟨hmem a ha.1, by rw [hflip a ha.1, ha.2]; rfl⟩
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    exact ⟨hmem a ha.1, by rw [hflip a ha.1, ha.2]; rfl⟩
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha
    exact hinv a ha.1
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter] at ha
    exact hinv a ha.1

/-- **Split any class by the off‑diagonal / diagonal of a coordinate pair (proved).** -/
theorem card_eq_offdiag_add_diag (C : Finset (Fin n → Bool)) (v w : Fin n)
    (p : (Fin n → Bool) → Prop) [DecidablePred p] :
    (C.filter p).card
      = ((C.filter (fun x => x v ≠ x w)).filter p).card
        + ((C.filter (fun x => x v = x w)).filter p).card := by
  have e1 : (C.filter p).filter (fun x => x v ≠ x w) = (C.filter (fun x => x v ≠ x w)).filter p := by
    rw [Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr; intro x _; exact and_comm
  have e2 : (C.filter p).filter (fun x => ¬ (x v ≠ x w)) = (C.filter (fun x => x v = x w)).filter p := by
    rw [Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr; intro x _; rw [ne_eq, not_not]; exact and_comm
  rw [← e1, ← e2]
  exact (Finset.card_filter_add_card_filter_not (fun x : Fin n → Bool => x v ≠ x w)).symm

/-! ## The swap preserves the `MOD q` count off‑diagonal -/

/-- Split a sum over `Fin n` by pulling out two distinct coordinates. -/
theorem sum_extract_two {M : Type*} [AddCommMonoid M] (v w : Fin n) (h : v ≠ w) (f : Fin n → M) :
    ∑ i, f i = f v + f w + ∑ i ∈ (Finset.univ.erase v).erase w, f i := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ v),
      ← Finset.add_sum_erase (Finset.univ.erase v) f
        (Finset.mem_erase.mpr ⟨h.symm, Finset.mem_univ w⟩)]
  abel

/-- **The pair swap preserves the `MOD q` count on the off‑diagonal (proved).**  When `x_v ≠ x_w`, the swap moves
one coordinate `0→1` and the other `1→0`, leaving `∑_i x_i` — and hence the `MOD q` class — unchanged. -/
theorem modQStat_pairSwap_offdiag (q : ℕ) (v w : Fin n) (h : v ≠ w) (x : Fin n → Bool)
    (hoff : x v ≠ x w) : modQStat q (pairSwap v w x) = modQStat q x := by
  unfold modQStat
  rw [sum_extract_two v w h (fun i => if pairSwap v w x i then (1 : ZMod q) else 0),
      sum_extract_two v w h (fun i => if x i then (1 : ZMod q) else 0)]
  have hR : ∑ i ∈ (Finset.univ.erase v).erase w, (if pairSwap v w x i then (1 : ZMod q) else 0)
      = ∑ i ∈ (Finset.univ.erase v).erase w, (if x i then (1 : ZMod q) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiw : i ≠ w := Finset.ne_of_mem_erase hi
    have hiv : i ≠ v := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    rw [pairSwap_other _ _ _ hiv hiw]
  rw [hR, pairSwap_v, pairSwap_w v w x h.symm]
  cases hxv : x v <;> cases hxw : x w <;> simp_all

/-! ## The swap toggles the holonomy parity -/

/-- Flipping a single Boolean inside the `ZMod 2` indicator changes it by `1`. -/
theorem gToggle : ∀ b : Bool, (if !b then (1 : ZMod 2) else 0) = (if b then (1 : ZMod 2) else 0) + 1 := by
  decide

/-- **The pair swap toggles the holonomy parity (proved).**  Only `v ∈ D` lies in the parity support (`w ∉ D`), so
the swap flips exactly one summand of the parity. -/
theorem fParity_pairSwap (D : Finset (Fin n)) (v w : Fin n) (hvD : v ∈ D) (hwD : w ∉ D) (h : v ≠ w)
    (x : Fin n → Bool) : fParity D (pairSwap v w x) = !(fParity D x) := by
  unfold fParity
  have hcharge : parityCharge D (pairSwap v w x) = parityCharge D x + 1 := by
    unfold parityCharge
    rw [← Finset.add_sum_erase D (fun i => if pairSwap v w x i then (1 : ZMod 2) else 0) hvD,
        ← Finset.add_sum_erase D (fun i => if x i then (1 : ZMod 2) else 0) hvD]
    have hR : ∑ i ∈ D.erase v, (if pairSwap v w x i then (1 : ZMod 2) else 0)
        = ∑ i ∈ D.erase v, (if x i then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiv : i ≠ v := Finset.ne_of_mem_erase hi
      have hiw : i ≠ w := by rintro rfl; exact hwD (Finset.mem_of_mem_erase hi)
      rw [pairSwap_other _ _ _ hiv hiw]
    rw [hR, pairSwap_v, gToggle (x v)]
    abel
  rw [hcharge]
  exact zmod2_toggle (parityCharge D x)

/-! ## Exact balance of the holonomy parity inside each `MOD q` class, off‑diagonal -/

/-- **The headline (proved): on the off‑diagonal `{x_v ≠ x_w}`, the holonomy parity is exactly balanced inside
every `MOD q` class.**  The count‑preserving pair swap is a class‑preserving, parity‑toggling involution there, so
`balanced_per_class_of_involution` applies. -/
theorem modQ_class_balanced_offdiagonal (q : ℕ) (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) :
    ∀ c ∈ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).image (modQStat q),
      ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => modQStat q x = c)).filter (fun x => fParity D x = true)).card
        = ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
            (fun x => modQStat q x = c)).filter (fun x => fParity D x = false)).card := by
  apply balanced_per_class_of_involution _ (modQStat q) (fParity D) (pairSwap v w)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [pairSwap_v, pairSwap_w v w x hvw.symm]
    exact bool_not_ne _ _ hx.2
  · intro x _; exact pairSwap_involutive v w hvw x
  · intro x hx; exact modQStat_pairSwap_offdiag q v w hvw x (Finset.mem_filter.mp hx).2
  · intro x _; exact fParity_pairSwap D v w hvD hwD hvw x

/-- Off‑diagonal balance for *every* residue (empty classes are trivially balanced). -/
theorem offdiag_balanced (q : ℕ) (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) (c : ZMod q) :
    ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
        (fun x => modQStat q x = c)).filter (fun x => fParity D x = true)).card
      = ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => modQStat q x = c)).filter (fun x => fParity D x = false)).card := by
  by_cases hc : c ∈ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).image (modQStat q)
  · exact modQ_class_balanced_offdiagonal q D v w hvw hvD hwD c hc
  · have hempty : ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
        (fun x => modQStat q x = c) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hcx
      exact hc (hcx ▸ Finset.mem_image_of_mem (modQStat q) hx)
    rw [hempty]; simp

/-! ## No correlation advantage of the `MOD q` gate against the holonomy parity, off‑diagonal -/

set_option maxHeartbeats 1000000 in
/-- **The cash‑out (proved): a `MOD q` gate `g ∘ modQStat` has no correlation advantage against the holonomy
parity on the off‑diagonal** — `2 · agreement ≤ #off‑diagonal inputs`.  Off‑diagonal balance feeds the engine seed
`low_rank_predictor_low_correlation_with_full_holonomy`. -/
theorem modQ_gate_low_correlation_offdiagonal (q : ℕ) (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) (g : ZMod q → Bool) :
    2 * (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => g (modQStat q x) = fParity D x)).card
      ≤ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).card :=
  low_rank_predictor_low_correlation_with_full_holonomy
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w))
    (modQStat q) g (fParity D)
    (modQ_class_balanced_offdiagonal q D v w hvw hvD hwD)

/-! ## The imbalance lives *exactly* on the diagonal -/

/-- **The localization theorem (proved): the holonomy‑parity imbalance of a whole `MOD q` class equals the
imbalance of its diagonal `{x_v = x_w}`.**  Written without subtraction:
`#{parity=true in C} + #{parity=false in C∩diag} = #{parity=false in C} + #{parity=true in C∩diag}` — i.e. the
off‑diagonal part contributes *nothing* to the imbalance (it is exactly balanced), so every bit of the
`MOD q`‑vs‑parity correlation is carried by the diagonal.  Proof: split each class by off/diagonal
(`card_eq_offdiag_add_diag`), use exact off‑diagonal balance (`balanced_of_involution` via the count‑preserving
pair swap), and cancel. -/
theorem modQ_class_imbalance_on_diagonal (q : ℕ) (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) (c : ZMod q) :
    (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat q x = c)).filter
        (fun x => fParity D x = true)).card
      + ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat q x = c)).filter
          (fun x => x v = x w)).filter (fun x => fParity D x = false)).card
    = (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat q x = c)).filter
        (fun x => fParity D x = false)).card
      + ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat q x = c)).filter
          (fun x => x v = x w)).filter (fun x => fParity D x = true)).card := by
  set C := (Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat q x = c) with hC
  have hbal : ((C.filter (fun x => x v ≠ x w)).filter (fun x => fParity D x = true)).card
            = ((C.filter (fun x => x v ≠ x w)).filter (fun x => fParity D x = false)).card := by
    apply balanced_of_involution (C.filter (fun x => x v ≠ x w)) (fParity D) (pairSwap v w)
    · intro x hx
      simp only [hC, Finset.mem_filter] at hx ⊢
      obtain ⟨⟨_, hcx⟩, hoff⟩ := hx
      refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [modQStat_pairSwap_offdiag q v w hvw x hoff]; exact hcx
      · rw [pairSwap_v, pairSwap_w v w x hvw.symm]; exact bool_not_ne _ _ hoff
    · intro x _; exact pairSwap_involutive v w hvw x
    · intro x _; exact fParity_pairSwap D v w hvD hwD hvw x
  have sT := card_eq_offdiag_add_diag C v w (fun x => fParity D x = true)
  have sF := card_eq_offdiag_add_diag C v w (fun x => fParity D x = false)
  omega

/-! ## Attacking the diagonal: the recursion *closes* for `q = 2`

The localization confined all imbalance to the diagonal `{x_v = x_w}`.  On the diagonal the *only* count‑preserving
parity‑toggling move flips a pair *both inside or both outside* — concretely `pairSwap v w` itself, which is just
"flip both `v` and `w`": it keeps `x_v = x_w` (both toggle) and changes the count by `±2` (both move the same way).
Mod `2` that `±2` vanishes, so **for `q = 2` the diagonal is balanced too** and the recursion bottoms out at exact
balance.  For `q > 2` the `±2` is nonzero mod `q`, the diagonal involution fails, and the residual is the genuine
character sum (`ModQParityCorrelationExpSmall`). -/

/-- **The pair swap preserves the `MOD 2` count unconditionally (proved).**  Flipping two coordinates changes the
count by an even amount, which is `0` in `ZMod 2` — no off‑diagonal hypothesis needed (unlike general `q`). -/
theorem modQStat_two_pairSwap (v w : Fin n) (h : v ≠ w) (x : Fin n → Bool) :
    modQStat 2 (pairSwap v w x) = modQStat 2 x := by
  unfold modQStat
  rw [sum_extract_two v w h (fun i => if pairSwap v w x i then (1 : ZMod 2) else 0),
      sum_extract_two v w h (fun i => if x i then (1 : ZMod 2) else 0)]
  have hR : ∑ i ∈ (Finset.univ.erase v).erase w, (if pairSwap v w x i then (1 : ZMod 2) else 0)
      = ∑ i ∈ (Finset.univ.erase v).erase w, (if x i then (1 : ZMod 2) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiw : i ≠ w := Finset.ne_of_mem_erase hi
    have hiv : i ≠ v := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    rw [pairSwap_other _ _ _ hiv hiw]
  have key : ∀ a b : Bool, (if !a then (1 : ZMod 2) else 0) + (if !b then (1 : ZMod 2) else 0)
      = (if a then (1 : ZMod 2) else 0) + (if b then (1 : ZMod 2) else 0) := by decide
  rw [hR, pairSwap_v, pairSwap_w v w x h.symm, key (x v) (x w)]

/-- **The diagonal is balanced for `q = 2` (proved): the recursion's closing step.**  On `{x_v = x_w}` the
flip‑both involution `pairSwap v w` preserves the diagonal, preserves the `MOD 2` count (unconditionally), and
toggles the parity — so `balanced_of_involution` applies on the diagonal too. -/
theorem modQ2_diagonal_balanced (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) (c : ZMod 2) :
    ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat 2 x = c)).filter
        (fun x => x v = x w)).filter (fun x => fParity D x = true)).card
      = ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat 2 x = c)).filter
          (fun x => x v = x w)).filter (fun x => fParity D x = false)).card := by
  apply balanced_of_involution _ (fParity D) (pairSwap v w)
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    obtain ⟨⟨_, hcx⟩, hdiageq⟩ := hx
    refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [modQStat_two_pairSwap v w hvw x]; exact hcx
    · rw [pairSwap_v, pairSwap_w v w x hvw.symm, hdiageq]
  · intro x _; exact pairSwap_involutive v w hvw x
  · intro x _; exact fParity_pairSwap D v w hvD hwD hvw x

/-- **The recursion closes: a `MOD 2` class is *exactly* balanced against any holonomy parity (proved).**  The
localization (`modQ_class_imbalance_on_diagonal`) plus diagonal balance (`modQ2_diagonal_balanced`) cancel: the
full class has equal `parity=true` and `parity=false` counts. -/
theorem modQ2_class_balanced (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) (c : ZMod 2) :
    (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat 2 x = c)).filter
        (fun x => fParity D x = true)).card
      = (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat 2 x = c)).filter
          (fun x => fParity D x = false)).card := by
  have hloc := modQ_class_imbalance_on_diagonal 2 D v w hvw hvD hwD c
  have hdiag := modQ2_diagonal_balanced D v w hvw hvD hwD c
  omega

/-- **The full cash‑out for `q = 2` (proved): a `MOD 2` gate has *zero* correlation advantage against any holonomy
parity** (`2 · agreement ≤ #inputs` over *all* inputs, not just the off‑diagonal).  This is the recursion closing
completely: where general `q` left a diagonal residual, `q = 2` eliminates it. -/
theorem modQ2_gate_zero_correlation (D : Finset (Fin n)) (v w : Fin n)
    (hvw : v ≠ w) (hvD : v ∈ D) (hwD : w ∉ D) (g : ZMod 2 → Bool) :
    2 * ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => g (modQStat 2 x) = fParity D x)).card
      ≤ (Finset.univ : Finset (Fin n → Bool)).card :=
  low_rank_predictor_low_correlation_with_full_holonomy
    Finset.univ (modQStat 2) g (fParity D)
    (fun c _ => modQ2_class_balanced D v w hvw hvD hwD c)

/-! ## Extending to `q > 2`: disjoint pair stacking

For `q > 2` the diagonal flip‑both fails (count change `±2 ≢ 0`).  But a *fresh disjoint* witness pair
`(v₂, w₂)` with `v₂ ∈ D`, `w₂ ∉ D`, all coordinates distinct from the first, gives a flip‑both that — on its own
off‑diagonal `{x_{v₂} ≠ x_{w₂}}` — moves one coordinate `0→1` and the other `1→0` (count change `0` mod **any**
`q`) while *leaving the first pair's coordinates untouched* (so it preserves `{x_v = x_w}`).  It peels another
exactly‑balanced layer off the diagonal.  Stacking `k` disjoint such pairs confines the entire imbalance to the
`k`‑fold diagonal `⋂_i {x_{v_i} = x_{w_i}}`, for all `q`. -/

/-- **General localization step (proved).**  For any ambient `S` closed under the flip‑both involution
`pairSwap v w` on its off‑diagonal, the holonomy‑parity imbalance of `S` equals that of its `(v,w)`‑diagonal. -/
theorem imbalance_localize_step (D : Finset (Fin n)) (v w : Fin n)
    (hvD : v ∈ D) (hwD : w ∉ D) (hvw : v ≠ w) (S : Finset (Fin n → Bool))
    (hS : ∀ x ∈ S, x v ≠ x w → pairSwap v w x ∈ S) :
    (S.filter (fun x => fParity D x = true)).card
      + ((S.filter (fun x => x v = x w)).filter (fun x => fParity D x = false)).card
    = (S.filter (fun x => fParity D x = false)).card
      + ((S.filter (fun x => x v = x w)).filter (fun x => fParity D x = true)).card := by
  have hbal : ((S.filter (fun x => x v ≠ x w)).filter (fun x => fParity D x = true)).card
            = ((S.filter (fun x => x v ≠ x w)).filter (fun x => fParity D x = false)).card := by
    apply balanced_of_involution (S.filter (fun x => x v ≠ x w)) (fParity D) (pairSwap v w)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hS x hx.1 hx.2,
        by rw [pairSwap_v, pairSwap_w v w x hvw.symm]; exact bool_not_ne _ _ hx.2⟩
    · intro x _; exact pairSwap_involutive v w hvw x
    · intro x _; exact fParity_pairSwap D v w hvD hwD hvw x
  have sT := card_eq_offdiag_add_diag S v w (fun x => fParity D x = true)
  have sF := card_eq_offdiag_add_diag S v w (fun x => fParity D x = false)
  omega

/-- **Disjoint pair stacking (proved, all `q`): the imbalance of a `MOD q` class equals that of its `k`‑fold
diagonal** over any family `L` of disjoint witness pairs (each `v_i ∈ D`, `w_i ∉ D`, all coordinates distinct).
Each stacked pair peels off an exactly‑balanced off‑diagonal layer via a count‑preserving flip‑both involution,
confining the support that can carry the imbalance to `⋂_i {x_{v_i} = x_{w_i}}`. -/
theorem imbalance_stacked (q : ℕ) (D : Finset (Fin n)) (c : ZMod q) (L : List (Fin n × Fin n)) :
    (∀ p ∈ L, p.1 ∈ D ∧ p.2 ∉ D) →
    (L.flatMap (fun p => [p.1, p.2])).Nodup →
    (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat q x = c)).filter
        (fun x => fParity D x = true)).card
      + ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat q x = c)).filter
          (fun x => ∀ p ∈ L, x p.1 = x p.2)).filter (fun x => fParity D x = false)).card
    = (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat q x = c)).filter
        (fun x => fParity D x = false)).card
      + ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat q x = c)).filter
          (fun x => ∀ p ∈ L, x p.1 = x p.2)).filter (fun x => fParity D x = true)).card := by
  induction L with
  | nil =>
    intro _ _
    have hfilt : (Finset.univ.filter (fun x : Fin n → Bool => modQStat q x = c)).filter
        (fun x => ∀ p ∈ ([] : List (Fin n × Fin n)), x p.1 = x p.2)
        = Finset.univ.filter (fun x => modQStat q x = c) := by
      apply Finset.filter_true_of_mem
      intro x _ p hp
      exact absurd hp (by simp)
    rw [hfilt]; omega
  | cons hd tl ih =>
    intro hpairs hnodup
    obtain ⟨v, w⟩ := hd
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, not_or] at hnodup
    obtain ⟨⟨hvw, hv_rest⟩, hw_rest, hnd⟩ := hnodup
    have hvD : v ∈ D := (hpairs (v, w) (by simp)).1
    have hwD : w ∉ D := (hpairs (v, w) (by simp)).2
    have hpairs_tl : ∀ p ∈ tl, p.1 ∈ D ∧ p.2 ∉ D :=
      fun p hp => hpairs p (List.mem_cons_of_mem _ hp)
    have ihC := ih hpairs_tl hnd
    set C := (Finset.univ : Finset (Fin n → Bool)).filter (fun x => modQStat q x = c) with hC
    set R' := C.filter (fun x => ∀ p ∈ tl, x p.1 = x p.2) with hR'
    have hS : ∀ x ∈ R', x v ≠ x w → pairSwap v w x ∈ R' := by
      intro x hx hoff
      rw [hR', Finset.mem_filter] at hx
      obtain ⟨hxC, hxst⟩ := hx
      rw [hC, Finset.mem_filter] at hxC
      obtain ⟨_, hcx⟩ := hxC
      rw [hR', Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hC, Finset.mem_filter]
        exact ⟨Finset.mem_univ _,
          by rw [modQStat_pairSwap_offdiag q v w hvw x hoff]; exact hcx⟩
      · intro p hp
        have hp1 : p.1 ∈ tl.flatMap (fun p => [p.1, p.2]) := List.mem_flatMap.mpr ⟨p, hp, by simp⟩
        have hp2 : p.2 ∈ tl.flatMap (fun p => [p.1, p.2]) := List.mem_flatMap.mpr ⟨p, hp, by simp⟩
        rw [pairSwap_other v w x (fun h : p.1 = v => hv_rest (h ▸ hp1))
              (fun h : p.1 = w => hw_rest (h ▸ hp1)),
            pairSwap_other v w x (fun h : p.2 = v => hv_rest (h ▸ hp2))
              (fun h : p.2 = w => hw_rest (h ▸ hp2))]
        exact hxst p hp
    have step := imbalance_localize_step D v w hvD hwD hvw R' hS
    have hReq : R'.filter (fun x => x v = x w)
        = C.filter (fun x => ∀ p ∈ (v, w) :: tl, x p.1 = x p.2) := by
      rw [hR', Finset.filter_filter]
      apply Finset.filter_congr
      intro x _
      rw [List.forall_mem_cons]
      exact and_comm
    rw [hReq] at step
    omega

/-! ## The residual — named honestly -/

/-- **(Named open — `NP ⊄ ACC⁰`‑strength, for `q > 2`).**  The full‑class imbalance of the holonomy parity inside
a `MOD q` level set is exponentially small in `n − |D|`.  The off‑diagonal part is *exactly* balanced
(`offdiag_balanced`), so this residual is entirely the **diagonal** `{x_v = x_w}` contribution — the classical
`MOD q`‑vs‑parity correlation, bounded by a Fourier/character recursion (cancelling main terms), *not* by any
involution **for `q > 2`**, *but only on the final core*: `imbalance_stacked` shows disjoint pair stacking confines
the `q > 2` imbalance to the `k`‑fold diagonal `⋂_{i≤k} {x_{v_i} = x_{w_i}}` (one balanced layer peeled per fresh
disjoint pair), a support shrinking with each pair.  What stacking cannot do is balance that final core (where no
fresh disjoint `(in‑D, out‑D)` pair remains) — *that* is the irreducible character‑sum residue.  For `q = 2` the
whole thing *is* supplied — `modQ2_gate_zero_correlation` gives exact zero correlation by involution.  Supplying
the `q > 2` core would let `modQ_gate_low_correlation_offdiagonal`‑style bounds extend to the whole class; it is the
same Razborov–Smolensky‑flavoured content every fragment route reduces to. -/
def ModQParityCorrelationExpSmall (fullImbalance : ℕ → ℕ) (expSmallBound : ℕ → ℕ) : Prop :=
  ∀ n, fullImbalance n ≤ expSmallBound n

end PallLean.Paper93.DeepMath.PathB.ModQGateBalance

#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.pairSwap_involutive
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.modQStat_pairSwap_offdiag
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.fParity_pairSwap
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.modQ_class_balanced_offdiagonal
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.offdiag_balanced
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.modQ_gate_low_correlation_offdiagonal
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.modQ_class_imbalance_on_diagonal
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.modQ2_diagonal_balanced
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.modQ2_class_balanced
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.modQ2_gate_zero_correlation
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.imbalance_localize_step
#print axioms PallLean.Paper93.DeepMath.PathB.ModQGateBalance.imbalance_stacked
