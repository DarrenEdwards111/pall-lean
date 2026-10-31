import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW4
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA6b

/-!
# KRW brick 5: the size↔depth bridge and the hard-gadget depth lower bound

The bridge between the Andreev SIZE results and the KRW DEPTH framework: a
depth-`D` formula has `≤ 2^D` leaves, so `dmsize f ≤ 2^{dmdepth f}`.  Hence a
size-hard function (`exists_hard_card`) is depth-hard, giving a gadget of depth
`≈ log₂(size)`.  Feeding it to `krw_iter_lb_of_ge` yields, under the conjecture,
functions on `a^{d+1}` variables of depth `≥ (d+1)·s` — the super-logarithmic
depth of the KRW lever (`a = 2^k`: depth `≥ (d+1)·s`, `log₂(arity) = (d+1)·k`).

* **`lsize_le_two_pow_dep` (proved)** — `lsize t ≤ 2^{dep t}`;
* **`dmsizeC_le_dmsize` / `dmsize_le_two_pow_dmdepth` (proved)** — the measure
  chain `dmsizeC f ≤ dmsize f ≤ 2^{dmdepth f}`;
* **`exists_deep` (proved)** — `2^s ≤ B` + the counting condition ⟹ a function of
  depth `≥ s` (size-hardness ⇒ depth-hardness);
* **`nonconstant_of_dmdepth` (proved)** — depth `≥ 2` ⟹ nonconstant;
* **`krw_iter_deep` (from the conjecture)** — the super-logarithmic-depth family.

HONEST SCOPE: this yields, under KRW, the EXISTENCE of super-logarithmic-depth
functions (non-uniform, via counting).  The step to a UNIFORM `P ⊄ NC¹` needs an
EXPLICIT gadget in `P` — the actual difficulty the KRW program addresses; the
composition amplification proved here is its engine, not that separation.  And
`KRWConjectureDepth` itself stays an open socket.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### The size↔depth bridge -/

/-- A depth-`D` formula has at most `2^D` leaves. -/
theorem lsize_le_two_pow_dep {n : ℕ} (t : DMTree n) : t.lsize ≤ 2 ^ t.dep := by
  induction t with
  | lit i b => simp [DMTree.lsize, DMTree.dep]
  | and l r ihl ihr =>
    show l.lsize + r.lsize ≤ 2 ^ (1 + max l.dep r.dep)
    have h1 : (2 : ℕ) ^ l.dep ≤ 2 ^ max l.dep r.dep :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2 : (2 : ℕ) ^ r.dep ≤ 2 ^ max l.dep r.dep :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    have h3 : (2 : ℕ) ^ (1 + max l.dep r.dep)
        = 2 ^ max l.dep r.dep + 2 ^ max l.dep r.dep := by rw [pow_add]; ring
    omega
  | or l r ihl ihr =>
    show l.lsize + r.lsize ≤ 2 ^ (1 + max l.dep r.dep)
    have h1 : (2 : ℕ) ^ l.dep ≤ 2 ^ max l.dep r.dep :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2 : (2 : ℕ) ^ r.dep ≤ 2 ^ max l.dep r.dep :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    have h3 : (2 : ℕ) ^ (1 + max l.dep r.dep)
        = 2 ^ max l.dep r.dep + 2 ^ max l.dep r.dep := by rw [pow_add]; ring
    omega

/-- `dmsizeC f ≤ dmsize f` (the extended measure never exceeds the min formula). -/
theorem dmsizeC_le_dmsize {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    dmsizeC f ≤ dmsize f := by
  obtain ⟨t, hte, htl⟩ := Nat.sInf_mem (dmsize_set_nonempty hn f)
  have hle : dmsizeC f ≤ t.lsize := dmsizeC_le f t hte
  have htl' : t.lsize = dmsize f := htl
  omega

/-- **The bridge (proved)**: `dmsize f ≤ 2^{dmdepth f}`. -/
theorem dmsize_le_two_pow_dmdepth {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    dmsize f ≤ 2 ^ dmdepth f := by
  obtain ⟨t, hte, htd⟩ := Nat.sInf_mem (dmdepth_set_nonempty hn f)
  have htd' : t.dep = dmdepth f := htd
  have h1 : dmsize f ≤ t.lsize := Nat.sInf_le ⟨t, hte, rfl⟩
  have h2 : t.lsize ≤ 2 ^ t.dep := lsize_le_two_pow_dep t
  rw [htd'] at h2
  omega

/-! ### Size-hardness ⇒ depth-hardness -/

/-- **A size-hard function is depth-hard (proved)**: with `2^s ≤ B` and the
counting condition, some function has depth `≥ s`. -/
theorem exists_deep (a B s : ℕ) (ha : 0 < a) (hsB : 2 ^ s ≤ B)
    (hnum : (2 * B + 1) * (2 * a + 4) ^ (2 * B) < 2 ^ (2 ^ a)) :
    ∃ g : (Fin a → Bool) → Bool, s ≤ dmdepth g := by
  obtain ⟨f, hf⟩ := exists_hard_card a B hnum
  refine ⟨f, ?_⟩
  have h1 : dmsizeC f ≤ dmsize f := dmsizeC_le_dmsize ha f
  have h2 : dmsize f ≤ 2 ^ dmdepth f := dmsize_le_two_pow_dmdepth ha f
  have h3 : 2 ^ s ≤ 2 ^ dmdepth f := by omega
  by_contra hc
  push_neg at hc
  have : 2 ^ dmdepth f < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) hc
  omega

/-- **Depth `≥ 2` ⟹ nonconstant (proved)** (constants have depth `1`). -/
theorem nonconstant_of_dmdepth {a : ℕ} (ha : 0 < a) (g : (Fin a → Bool) → Bool)
    (h : 2 ≤ dmdepth g) : ∃ y y', g y ≠ g y' := by
  by_contra hc
  push_neg at hc
  have hconst : ∀ x, (constTree a ha (g (fun _ => false))).eval x = g x := by
    intro x; rw [constTree_eval]; exact hc (fun _ => false) x
  have hle : dmdepth g ≤ (constTree a ha (g (fun _ => false))).dep :=
    Nat.sInf_le ⟨_, hconst, rfl⟩
  have hdep : (constTree a ha (g (fun _ => false))).dep = 1 := by
    cases g (fun _ => false) <;> simp [constTree, DMTree.dep]
  omega

/-! ### The super-logarithmic-depth family -/

/-- **KRW ⟹ the super-logarithmic-depth family (proved from the conjecture)**:
a depth-`≥ s` gadget on `a` bits iterates to a function on `a^{d+1}` bits of depth
`≥ (d+1)·s`.  With `a = 2^k`, `s ≈ 2^k`, this is depth `ω(log₂ arity)`. -/
theorem krw_iter_deep (H : KRWConjectureDepth) (a B s : ℕ) (ha : 0 < a) (hs2 : 2 ≤ s)
    (hsB : 2 ^ s ≤ B) (hnum : (2 * B + 1) * (2 * a + 4) ^ (2 * B) < 2 ^ (2 ^ a)) (d : ℕ) :
    ∃ g : (Fin a → Bool) → Bool,
      (iterComp ha g d).1 = a ^ (d + 1) ∧ (d + 1) * s ≤ dmdepth (iterComp ha g d).2 := by
  obtain ⟨g, hg⟩ := exists_deep a B s ha hsB hnum
  have hnc : ∃ y y', g y ≠ g y' := nonconstant_of_dmdepth ha g (by omega)
  exact ⟨g, iterComp_arity ha g d, krw_iter_lb_of_ge H ha g hnc s hg d⟩

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmsize_le_two_pow_dmdepth
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.exists_deep
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.krw_iter_deep
