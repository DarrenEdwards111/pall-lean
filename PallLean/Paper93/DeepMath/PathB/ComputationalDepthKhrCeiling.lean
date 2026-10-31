import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKhrK2

/-!
# The parity ceiling: `dmsize (⊕_{2^k}) = 4^k` — exact closure

The matching upper bound: the classical XOR doubling pair.  A DeMorgan XOR
needs both polarities, so the construction carries a (tree, negated tree) pair
and doubles: `T' = (T∧F̄)∨(F∧T̄)`, `F' = (T∧T̄)∨(F∧F̄)`, quadrupling leaves.

* `DMTree.relabel` — variable re-indexing (eval/lsize transparent);
* **`card_halves` (proved)** — the weight of a `2^(k+1)`-vector splits across
  the two halves (two explicit bijections);
* **`oddF_split` (proved)** — parity of the whole is the XOR of the halves;
* **`xorTrees_eval`/`xorTrees_lsize` (proved)** — the pair computes
  (parity, ¬parity) with `4^k` leaves each;
* **`dmsize_parity` (proved)** — with K2: `dmsize (oddF (2^k)) = 4^k = n²`
  EXACTLY.  The testbed-closure discipline of `AEm_exact`, one level up.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Relabeling -/

def DMTree.relabel {n m : ℕ} (f : Fin n → Fin m) : DMTree n → DMTree m
  | .lit i b => .lit (f i) b
  | .and l r => .and (l.relabel f) (r.relabel f)
  | .or l r => .or (l.relabel f) (r.relabel f)

theorem relabel_eval {n m : ℕ} (f : Fin n → Fin m) (t : DMTree n)
    (x : Fin m → Bool) :
    (t.relabel f).eval x = t.eval (fun i => x (f i)) := by
  induction t with
  | lit i b => rfl
  | and l r ihl ihr => simp only [DMTree.relabel, DMTree.eval, ihl, ihr]
  | or l r ihl ihr => simp only [DMTree.relabel, DMTree.eval, ihl, ihr]

theorem relabel_lsize {n m : ℕ} (f : Fin n → Fin m) (t : DMTree n) :
    (t.relabel f).lsize = t.lsize := by
  induction t with
  | lit i b => rfl
  | and l r ihl ihr => simp only [DMTree.relabel, DMTree.lsize, ihl, ihr]
  | or l r ihl ihr => simp only [DMTree.relabel, DMTree.lsize, ihl, ihr]

/-! ### The half embeddings -/

def leftE (k : ℕ) (j : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨j.val, by
    have h := j.isLt
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    omega⟩

def rightE (k : ℕ) (j : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 ^ k + j.val, by
    have h := j.isLt
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    omega⟩

/-- **The weight splits across the halves (proved).** -/
theorem card_halves (k : ℕ) (x : Fin (2 ^ (k + 1)) → Bool) :
    (Finset.univ.filter (fun j : Fin (2 ^ (k + 1)) => x j = true)).card
      = (Finset.univ.filter (fun j : Fin (2 ^ k) => x (leftE k j) = true)).card
        + (Finset.univ.filter
            (fun j : Fin (2 ^ k) => x (rightE k j) = true)).card := by
  classical
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
  have hLR := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun j : Fin (2 ^ (k + 1)) => x j = true))
    (fun j : Fin (2 ^ (k + 1)) => j.val < 2 ^ k)
  have hL : ((Finset.univ.filter (fun j : Fin (2 ^ (k + 1)) => x j = true)).filter
        (fun j => j.val < 2 ^ k)).card
      = (Finset.univ.filter
          (fun j : Fin (2 ^ k) => x (leftE k j) = true)).card := by
    refine (Finset.card_bij (fun (j : Fin (2 ^ k)) _ => leftE k j) ?_ ?_ ?_).symm
    · intro j hj
      have hxj : x (leftE k j) = true := (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩, ?_⟩
      exact j.isLt
    · intro j₁ h₁ j₂ h₂ he
      have he' : leftE k j₁ = leftE k j₂ := he
      have hv0 := congrArg Fin.val he'
      have hv : j₁.val = j₂.val := hv0
      exact Fin.ext hv
    · intro w hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
      have hxw : x w = true := (Finset.mem_filter.mp hw1).2
      refine ⟨⟨w.val, hw2⟩, ?_, Fin.ext rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have he : leftE k ⟨w.val, hw2⟩ = w := Fin.ext rfl
      rw [he]
      exact hxw
  have hR : ((Finset.univ.filter (fun j : Fin (2 ^ (k + 1)) => x j = true)).filter
        (fun j => ¬ j.val < 2 ^ k)).card
      = (Finset.univ.filter
          (fun j : Fin (2 ^ k) => x (rightE k j) = true)).card := by
    refine (Finset.card_bij (fun (j : Fin (2 ^ k)) _ => rightE k j) ?_ ?_ ?_).symm
    · intro j hj
      have hxj : x (rightE k j) = true := (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩, ?_⟩
      exact (by omega : ¬ 2 ^ k + j.val < 2 ^ k)
    · intro j₁ h₁ j₂ h₂ he
      have he' : rightE k j₁ = rightE k j₂ := he
      have hv0 := congrArg Fin.val he'
      have hv : (2 : ℕ) ^ k + j₁.val = 2 ^ k + j₂.val := hv0
      exact Fin.ext (by omega)
    · intro w hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
      have hxw : x w = true := (Finset.mem_filter.mp hw1).2
      have hge : 2 ^ k ≤ w.val := by omega
      have hlt : w.val - 2 ^ k < 2 ^ k := by
        have := w.isLt
        omega
      have he : rightE k ⟨w.val - 2 ^ k, hlt⟩ = w :=
        Fin.ext (show 2 ^ k + (w.val - 2 ^ k) = w.val by omega)
      refine ⟨⟨w.val - 2 ^ k, hlt⟩, ?_, he⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [he]
      exact hxw
  omega

/-- **Parity of the whole is the XOR of the halves (proved).** -/
theorem oddF_split (k : ℕ) (x : Fin (2 ^ (k + 1)) → Bool) :
    oddF (2 ^ (k + 1)) x
      = ((oddF (2 ^ k) (fun j => x (leftE k j))
            && !(oddF (2 ^ k) (fun j => x (rightE k j))))
        || (!(oddF (2 ^ k) (fun j => x (leftE k j)))
            && oddF (2 ^ k) (fun j => x (rightE k j)))) := by
  classical
  have hs := card_halves k x
  simp only [oddF]
  rw [hs]
  by_cases ha : (Finset.univ.filter
      (fun j : Fin (2 ^ k) => x (leftE k j) = true)).card % 2 = 1
  · by_cases hb : (Finset.univ.filter
        (fun j : Fin (2 ^ k) => x (rightE k j) = true)).card % 2 = 1
    · have hab : ((Finset.univ.filter
            (fun j : Fin (2 ^ k) => x (leftE k j) = true)).card
          + (Finset.univ.filter
            (fun j : Fin (2 ^ k) => x (rightE k j) = true)).card) % 2 = 0 := by
        omega
      rw [ha, hb, hab]
      decide
    · have hb' : (Finset.univ.filter
          (fun j : Fin (2 ^ k) => x (rightE k j) = true)).card % 2 = 0 := by
        omega
      have hab : ((Finset.univ.filter
            (fun j : Fin (2 ^ k) => x (leftE k j) = true)).card
          + (Finset.univ.filter
            (fun j : Fin (2 ^ k) => x (rightE k j) = true)).card) % 2 = 1 := by
        omega
      rw [ha, hb', hab]
      decide
  · have ha' : (Finset.univ.filter
        (fun j : Fin (2 ^ k) => x (leftE k j) = true)).card % 2 = 0 := by
      omega
    by_cases hb : (Finset.univ.filter
        (fun j : Fin (2 ^ k) => x (rightE k j) = true)).card % 2 = 1
    · have hab : ((Finset.univ.filter
            (fun j : Fin (2 ^ k) => x (leftE k j) = true)).card
          + (Finset.univ.filter
            (fun j : Fin (2 ^ k) => x (rightE k j) = true)).card) % 2 = 1 := by
        omega
      rw [ha', hb, hab]
      decide
    · have hb' : (Finset.univ.filter
          (fun j : Fin (2 ^ k) => x (rightE k j) = true)).card % 2 = 0 := by
        omega
      have hab : ((Finset.univ.filter
            (fun j : Fin (2 ^ k) => x (leftE k j) = true)).card
          + (Finset.univ.filter
            (fun j : Fin (2 ^ k) => x (rightE k j) = true)).card) % 2 = 0 := by
        omega
      rw [ha', hb', hab]
      decide

/-! ### The doubling pair -/

/-- The (parity, ¬parity) DeMorgan pair on `2^k` variables. -/
def xorTrees : (k : ℕ) → DMTree (2 ^ k) × DMTree (2 ^ k)
  | 0 => (.lit ⟨0, Nat.two_pow_pos 0⟩ true, .lit ⟨0, Nat.two_pow_pos 0⟩ false)
  | k + 1 =>
    (.or (.and ((xorTrees k).1.relabel (leftE k))
               ((xorTrees k).2.relabel (rightE k)))
         (.and ((xorTrees k).2.relabel (leftE k))
               ((xorTrees k).1.relabel (rightE k))),
     .or (.and ((xorTrees k).1.relabel (leftE k))
               ((xorTrees k).1.relabel (rightE k)))
         (.and ((xorTrees k).2.relabel (leftE k))
               ((xorTrees k).2.relabel (rightE k))))

theorem oddF_one (x : Fin (2 ^ 0) → Bool) :
    oddF (2 ^ 0) x = x ⟨0, Nat.two_pow_pos 0⟩ := by
  classical
  have huniv : (Finset.univ : Finset (Fin (2 ^ 0)))
      = {⟨0, Nat.two_pow_pos 0⟩} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    refine Fin.ext ?_
    have := j.isLt
    have h1 : (2 : ℕ) ^ 0 = 1 := by norm_num
    omega
  show decide ((Finset.univ.filter
      (fun j : Fin (2 ^ 0) => x j = true)).card % 2 = 1)
    = x ⟨0, Nat.two_pow_pos 0⟩
  rw [huniv]
  by_cases hx : x ⟨0, Nat.two_pow_pos 0⟩ = true
  · rw [Finset.filter_singleton, if_pos hx, hx]
    simp
  · have hx' : x ⟨0, Nat.two_pow_pos 0⟩ = false := by
      cases h : x ⟨0, Nat.two_pow_pos 0⟩
      · rfl
      · exact absurd h hx
    rw [Finset.filter_singleton, if_neg hx, hx']
    simp

/-- **The pair computes (parity, ¬parity) (proved).** -/
theorem xorTrees_eval (k : ℕ) :
    (∀ x, (xorTrees k).1.eval x = oddF (2 ^ k) x)
      ∧ (∀ x, (xorTrees k).2.eval x = !(oddF (2 ^ k) x)) := by
  induction k with
  | zero =>
    constructor <;> intro x
    · show (x ⟨0, Nat.two_pow_pos 0⟩ == true) = oddF (2 ^ 0) x
      rw [oddF_one]
      cases h : x ⟨0, Nat.two_pow_pos 0⟩ <;> rfl
    · show (x ⟨0, Nat.two_pow_pos 0⟩ == false) = !(oddF (2 ^ 0) x)
      rw [oddF_one]
      cases h : x ⟨0, Nat.two_pow_pos 0⟩ <;> rfl
  | succ k ih =>
    obtain ⟨ihT, ihF⟩ := ih
    have e1 : ∀ x : Fin (2 ^ (k + 1)) → Bool,
        ((xorTrees k).1.relabel (leftE k)).eval x
          = oddF (2 ^ k) (fun j => x (leftE k j)) := by
      intro x
      rw [relabel_eval]
      exact ihT _
    have e2 : ∀ x : Fin (2 ^ (k + 1)) → Bool,
        ((xorTrees k).1.relabel (rightE k)).eval x
          = oddF (2 ^ k) (fun j => x (rightE k j)) := by
      intro x
      rw [relabel_eval]
      exact ihT _
    have e3 : ∀ x : Fin (2 ^ (k + 1)) → Bool,
        ((xorTrees k).2.relabel (leftE k)).eval x
          = !(oddF (2 ^ k) (fun j => x (leftE k j))) := by
      intro x
      rw [relabel_eval]
      exact ihF _
    have e4 : ∀ x : Fin (2 ^ (k + 1)) → Bool,
        ((xorTrees k).2.relabel (rightE k)).eval x
          = !(oddF (2 ^ k) (fun j => x (rightE k j))) := by
      intro x
      rw [relabel_eval]
      exact ihF _
    constructor <;> intro x
    · show ((((xorTrees k).1.relabel (leftE k)).eval x
          && ((xorTrees k).2.relabel (rightE k)).eval x)
        || (((xorTrees k).2.relabel (leftE k)).eval x
          && ((xorTrees k).1.relabel (rightE k)).eval x))
        = oddF (2 ^ (k + 1)) x
      rw [e1, e2, e3, e4, oddF_split]
    · show ((((xorTrees k).1.relabel (leftE k)).eval x
          && ((xorTrees k).1.relabel (rightE k)).eval x)
        || (((xorTrees k).2.relabel (leftE k)).eval x
          && ((xorTrees k).2.relabel (rightE k)).eval x))
        = !(oddF (2 ^ (k + 1)) x)
      rw [e1, e2, e3, e4, oddF_split]
      cases hp : oddF (2 ^ k) (fun j => x (leftE k j))
        <;> cases hq : oddF (2 ^ k) (fun j => x (rightE k j)) <;> rfl

/-- **The pair has `4^k` leaves each (proved).** -/
theorem xorTrees_lsize (k : ℕ) :
    (xorTrees k).1.lsize = 4 ^ k ∧ (xorTrees k).2.lsize = 4 ^ k := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hpow : (4 : ℕ) ^ (k + 1) = 4 ^ k * 4 := by rw [pow_succ]
    constructor
    · show ((xorTrees k).1.relabel (leftE k)).lsize
          + ((xorTrees k).2.relabel (rightE k)).lsize
        + (((xorTrees k).2.relabel (leftE k)).lsize
          + ((xorTrees k).1.relabel (rightE k)).lsize) = 4 ^ (k + 1)
      rw [relabel_lsize, relabel_lsize, relabel_lsize, relabel_lsize,
        h1, h2, hpow]
      omega
    · show ((xorTrees k).1.relabel (leftE k)).lsize
          + ((xorTrees k).1.relabel (rightE k)).lsize
        + (((xorTrees k).2.relabel (leftE k)).lsize
          + ((xorTrees k).2.relabel (rightE k)).lsize) = 4 ^ (k + 1)
      rw [relabel_lsize, relabel_lsize, relabel_lsize, relabel_lsize,
        h1, h2, hpow]
      omega

/-! ### The exact closure -/

/-- DeMorgan formula size of a function: minimal leaf count. -/
noncomputable def dmsize {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {L | ∃ t : DMTree n, (∀ x, t.eval x = f x) ∧ t.lsize = L}

/-- **THE EXACT PARITY COMPLEXITY (proved)**: `dmsize (⊕_{2^k}) = 4^k = n²`. -/
theorem dmsize_parity (k : ℕ) : dmsize (oddF (2 ^ k)) = 4 ^ k := by
  have hub : dmsize (oddF (2 ^ k)) ≤ 4 ^ k :=
    Nat.sInf_le ⟨(xorTrees k).1, (xorTrees_eval k).1, (xorTrees_lsize k).1⟩
  have hne : {L | ∃ t : DMTree (2 ^ k),
      (∀ x, t.eval x = oddF (2 ^ k) x) ∧ t.lsize = L}.Nonempty :=
    ⟨4 ^ k, (xorTrees k).1, (xorTrees_eval k).1, (xorTrees_lsize k).1⟩
  obtain ⟨t, hteval, htl⟩ := Nat.sInf_mem hne
  have hlb := parity_formula_lb (2 ^ k) (Nat.two_pow_pos k) t hteval
  have hpow : ((2 : ℕ) ^ k) ^ 2 = 4 ^ k := by
    have hh1 : ((2 : ℕ) ^ k) ^ 2 = 2 ^ (k * 2) := (pow_mul 2 k 2).symm
    have hh2 : (4 : ℕ) ^ k = 2 ^ (2 * k) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    rw [hh1, hh2, Nat.mul_comm]
  have htl' : t.lsize = dmsize (oddF (2 ^ k)) := htl
  have hlb' : ((2 : ℕ) ^ k) ^ 2 ≤ dmsize (oddF (2 ^ k)) := by
    rw [← htl']
    exact hlb
  omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmsize_parity
