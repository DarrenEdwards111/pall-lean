import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKhrK2

/-!
# Shrinkage brick A1: the constant-extended model

The shrinkage campaign works over DeMorgan formulas WITH constant leaves,
measured by VAR-leaf count (`lsize0`, constants free) — restrictions create
constants, and the classical accounting charges only variable occurrences:

* `DMTreeC` / `eval` / `lsize0` — the extended grammar and measure;
* `DMTree.toC` — the embedding (evaluation- and size-transparent);
* **`khrapchenkoC` (proved)** — K1 transfers verbatim: constants contribute
  no Hamming edges, so `|E(A,B)|² ≤ lsize0 · |A| · |B|` still holds;
* **`lsize_lb_of_lsize0_lb` (proved)** — the bridge: every `lsize0` lower
  bound transfers UP to the constant-free `lsize` measure;
* **`parityC_lb` (proved)** — the calibration anchor survives migration:
  `n² ≤ lsize0` for parity.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- DeMorgan formulas with constant leaves. -/
inductive DMTreeC (n : ℕ)
  | lit (i : Fin n) (b : Bool)
  | cst (v : Bool)
  | and (l r : DMTreeC n)
  | or (l r : DMTreeC n)

namespace DMTreeC

def eval {n : ℕ} : DMTreeC n → (Fin n → Bool) → Bool
  | .lit i b, x => x i == b
  | .cst v, _ => v
  | .and l r, x => l.eval x && r.eval x
  | .or l r, x => l.eval x || r.eval x

/-- Var-leaf count: constants are free. -/
def lsize0 {n : ℕ} : DMTreeC n → ℕ
  | .lit _ _ => 1
  | .cst _ => 0
  | .and l r => l.lsize0 + r.lsize0
  | .or l r => l.lsize0 + r.lsize0

end DMTreeC

/-- The embedding of constant-free formulas. -/
def DMTree.toC {n : ℕ} : DMTree n → DMTreeC n
  | .lit i b => .lit i b
  | .and l r => .and l.toC r.toC
  | .or l r => .or l.toC r.toC

theorem toC_eval {n : ℕ} (t : DMTree n) (x : Fin n → Bool) :
    t.toC.eval x = t.eval x := by
  induction t with
  | lit i b => rfl
  | and l r ihl ihr => simp only [DMTree.toC, DMTreeC.eval, DMTree.eval, ihl, ihr]
  | or l r ihl ihr => simp only [DMTree.toC, DMTreeC.eval, DMTree.eval, ihl, ihr]

theorem toC_lsize0 {n : ℕ} (t : DMTree n) : t.toC.lsize0 = t.lsize := by
  induction t with
  | lit i b => rfl
  | and l r ihl ihr => simp only [DMTree.toC, DMTreeC.lsize0, DMTree.lsize, ihl, ihr]
  | or l r ihl ihr => simp only [DMTree.toC, DMTreeC.lsize0, DMTree.lsize, ihl, ihr]

/-- **KHRAPCHENKO SOUNDNESS FOR THE EXTENDED MODEL (proved)**: constants
contribute no edges. -/
theorem khrapchenkoC {n : ℕ} (t : DMTreeC n) :
    ∀ (A B : Finset (Fin n → Bool)),
      (∀ x ∈ A, t.eval x = true) → (∀ x ∈ B, t.eval x = false) →
      (hamEdges n A B).card ^ 2 ≤ t.lsize0 * A.card * B.card := by
  induction t with
  | lit i b =>
    intro A B hA hB
    have hdet : ∀ p ∈ hamEdges n A B,
        p.2 = Function.update p.1 i (!(p.1 i)) := by
      intro p hp
      obtain ⟨hpA, hpB, j, hj⟩ := mem_hamEdges.mp hp
      have h1 := hA p.1 hpA
      have h2 := hB p.2 hpB
      by_cases hij : j = i
      · rw [hij] at hj
        exact hj
      · exfalso
        rw [hj] at h2
        have hne : i ≠ j := fun h => hij h.symm
        have hup : Function.update p.1 j (!(p.1 j)) i = p.1 i :=
          Function.update_of_ne hne (!(p.1 j)) p.1
        have h2' : (Function.update p.1 j (!(p.1 j)) i == b) = false := h2
        rw [hup] at h2'
        have h1' : (p.1 i == b) = true := h1
        rw [h1'] at h2'
        exact Bool.noConfusion h2'
    have hrec : ∀ p ∈ hamEdges n A B,
        p.1 = Function.update p.2 i (!(p.2 i)) := by
      intro p hp
      have h1 := hdet p hp
      rw [h1, Function.update_self, Bool.not_not, Function.update_idem,
        Function.update_eq_self]
    have hle1 : (hamEdges n A B).card ≤ A.card := by
      refine Finset.card_le_card_of_injOn Prod.fst
        (fun p hp => (mem_hamEdges.mp hp).1) ?_
      intro p hp q hq hfst
      have hp' := hdet p (Finset.mem_coe.mp hp)
      have hq' := hdet q (Finset.mem_coe.mp hq)
      refine Prod.ext_iff.mpr ⟨hfst, ?_⟩
      rw [hp', hq', hfst]
    have hle2 : (hamEdges n A B).card ≤ B.card := by
      refine Finset.card_le_card_of_injOn Prod.snd
        (fun p hp => (mem_hamEdges.mp hp).2.1) ?_
      intro p hp q hq hsnd
      have hp' := hrec p (Finset.mem_coe.mp hp)
      have hq' := hrec q (Finset.mem_coe.mp hq)
      refine Prod.ext_iff.mpr ⟨?_, hsnd⟩
      rw [hp', hq', hsnd]
    show (hamEdges n A B).card ^ 2 ≤ 1 * A.card * B.card
    rw [one_mul, pow_two]
    exact Nat.mul_le_mul hle1 hle2
  | cst v =>
    intro A B hA hB
    have hE : ∀ p, p ∉ hamEdges n A B := by
      intro p hp
      obtain ⟨hp1, hp2, -⟩ := mem_hamEdges.mp hp
      have h1' : v = true := hA p.1 hp1
      have h2' : v = false := hB p.2 hp2
      rw [h1'] at h2'
      exact Bool.noConfusion h2'
    have hcard : (hamEdges n A B).card = 0 := by
      rcases Finset.eq_empty_or_nonempty (hamEdges n A B) with he | ⟨p, hp⟩
      · rw [he]
        rfl
      · exact absurd hp (hE p)
    rw [hcard]
    simp
  | and l r ihl ihr =>
    intro A B hA hB
    classical
    have hAl : ∀ x ∈ A, l.eval x = true := fun x hx =>
      (Bool.and_eq_true _ _ |>.mp (hA x hx)).1
    have hAr : ∀ x ∈ A, r.eval x = true := fun x hx =>
      (Bool.and_eq_true _ _ |>.mp (hA x hx)).2
    have hB₁ : ∀ x ∈ B.filter (fun x => l.eval x = false),
        l.eval x = false := fun x hx => (Finset.mem_filter.mp hx).2
    have hB₂ : ∀ x ∈ B.filter (fun x => ¬ l.eval x = false),
        r.eval x = false := by
      intro x hx
      obtain ⟨hxB, hxl⟩ := Finset.mem_filter.mp hx
      have hand := hB x hxB
      cases hl : l.eval x with
      | false => exact absurd hl hxl
      | true =>
        show r.eval x = false
        have h : (l.eval x && r.eval x) = false := hand
        rw [hl, Bool.true_and] at h
        exact h
    have h₁ := ihl A (B.filter (fun x => l.eval x = false)) hAl hB₁
    have h₂ := ihr A (B.filter (fun x => ¬ l.eval x = false)) hAr hB₂
    have hsplit := hamEdges_card_split_right A B (fun x => l.eval x = false)
    have hb : (B.filter (fun x => l.eval x = false)).card
        + (B.filter (fun x => ¬ l.eval x = false)).card = B.card :=
      Finset.card_filter_add_card_filter_not (fun x => l.eval x = false)
    show (hamEdges n A B).card ^ 2 ≤ (l.lsize0 + r.lsize0) * A.card * B.card
    rw [hsplit, ← hb]
    exact khr_add _ _ _ _ _ _ _ h₁ h₂
  | or l r ihl ihr =>
    intro A B hA hB
    classical
    have hBl : ∀ x ∈ B, l.eval x = false := by
      intro x hx
      have hor := hB x hx
      cases hl : l.eval x with
      | false => rfl
      | true =>
        exfalso
        have h : (l.eval x || r.eval x) = false := hor
        rw [hl, Bool.true_or] at h
        exact Bool.noConfusion h
    have hBr : ∀ x ∈ B, r.eval x = false := by
      intro x hx
      have hor := hB x hx
      cases hr : r.eval x with
      | false => rfl
      | true =>
        exfalso
        have h : (l.eval x || r.eval x) = false := hor
        rw [hr, Bool.or_true] at h
        exact Bool.noConfusion h
    have hA₁ : ∀ x ∈ A.filter (fun x => l.eval x = true),
        l.eval x = true := fun x hx => (Finset.mem_filter.mp hx).2
    have hA₂ : ∀ x ∈ A.filter (fun x => ¬ l.eval x = true),
        r.eval x = true := by
      intro x hx
      obtain ⟨hxA, hxl⟩ := Finset.mem_filter.mp hx
      have hor := hA x hxA
      cases hl : l.eval x with
      | true => exact absurd hl hxl
      | false =>
        show r.eval x = true
        have h : (l.eval x || r.eval x) = true := hor
        rw [hl, Bool.false_or] at h
        exact h
    have h₁ := ihl (A.filter (fun x => l.eval x = true)) B hA₁ hBl
    have h₂ := ihr (A.filter (fun x => ¬ l.eval x = true)) B hA₂ hBr
    have hsplit := hamEdges_card_split_left A B (fun x => l.eval x = true)
    have ha : (A.filter (fun x => l.eval x = true)).card
        + (A.filter (fun x => ¬ l.eval x = true)).card = A.card :=
      Finset.card_filter_add_card_filter_not (fun x => l.eval x = true)
    show (hamEdges n A B).card ^ 2 ≤ (l.lsize0 + r.lsize0) * A.card * B.card
    rw [hsplit, ← ha]
    exact khr_add' _ _ _ _ _ _ _ h₁ h₂

/-! ### The measure and the bridges -/

/-- Constant-extended DeMorgan formula size (var leaves only). -/
noncomputable def dmsizeC {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {L | ∃ t : DMTreeC n, (∀ x, t.eval x = f x) ∧ t.lsize0 = L}

/-- The extended measure never exceeds a constant-free witness. -/
theorem dmsizeC_le {n : ℕ} (f : (Fin n → Bool) → Bool) (t : DMTree n)
    (ht : ∀ x, t.eval x = f x) : dmsizeC f ≤ t.lsize :=
  Nat.sInf_le ⟨t.toC, fun x => by rw [toC_eval]; exact ht x, toC_lsize0 t⟩

/-- **THE BRIDGE (proved)**: `lsize0` lower bounds transfer UP to `lsize`. -/
theorem lsize_lb_of_lsize0_lb {n : ℕ} (f : (Fin n → Bool) → Bool) (c : ℕ)
    (h : ∀ t : DMTreeC n, (∀ x, t.eval x = f x) → c ≤ t.lsize0) :
    ∀ t : DMTree n, (∀ x, t.eval x = f x) → c ≤ t.lsize := by
  intro t ht
  have h1 := h t.toC (fun x => by rw [toC_eval]; exact ht x)
  rw [toC_lsize0] at h1
  exact h1

/-- **The calibration anchor survives migration (proved)**: parity still
needs `n²` var leaves, constants notwithstanding. -/
theorem parityC_lb (n : ℕ) (hn : 1 ≤ n) (t : DMTreeC n)
    (ht : ∀ x, t.eval x = oddF n x) : n ^ 2 ≤ t.lsize0 := by
  have hA : ∀ x ∈ oddSet n, t.eval x = true := by
    intro x hx
    rw [ht]
    exact (Finset.mem_filter.mp hx).2
  have hB : ∀ x ∈ evenSet n, t.eval x = false := by
    intro x hx
    rw [ht]
    exact (Finset.mem_filter.mp hx).2
  have hk := khrapchenkoC t (oddSet n) (evenSet n) hA hB
  rw [parity_edges_card, oddSet_card n hn, evenSet_card n hn] at hk
  have e1 : (2 ^ (n - 1) * n) ^ 2 = n ^ 2 * (2 ^ (n - 1) * 2 ^ (n - 1)) := by
    ring
  have e2 : t.lsize0 * 2 ^ (n - 1) * 2 ^ (n - 1)
      = t.lsize0 * (2 ^ (n - 1) * 2 ^ (n - 1)) := by ring
  rw [e1, e2] at hk
  exact Nat.le_of_mul_le_mul_right hk
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.khrapchenkoC
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.lsize_lb_of_lsize0_lb
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.parityC_lb
