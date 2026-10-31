import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSeparationNoGo

/-!
# The language-rank kill — a poly-time language with provably superpolynomial rank profile

**Step 4/5 gate, concrete half.**  The abstract no-go (`SeparationNoGo`) left exactly one
non-circular calibration for an invariant route: `InvGenSound` — the invariant is polynomial
on *every* poly-time machine.  This brick kills that calibration for every invariant that
dominates a classical language-rank measure, by exhibiting a polynomial-time language whose
rank profile is **provably** superpolynomial.

**The MOD_q correction (honest).**  The phase plan named this "the MOD_q kill".  That was
wrong, and the corpus itself shows why: the *proved* MOD_q rank bounds are linear —
`nframeComplexity_omegaFn_univ_ge` gives `≥ ⌈n/2⌉`, `n_le_globalCubeRank_modQFn` gives
`≥ n` — and linear is polynomial, so MOD_q violates no generic soundness.  Structurally,
MOD_q is an automaton language: across any input cut it has `O(q)` distinct subfunctions
(Myhill–Nerode), so no subfunction-type measure is superpolynomial on it.  Restricted-model
hardness (MOD_q vs shallow ΣΠ, MOD_q vs AC⁰[p]) does **not** produce a superpolynomial
absolute rank profile.  The kill needs a *communication-type* witness.

**The witness: doubled INDEX.**  `dIndexLang` — data block of 3-cell units
`[live?, mark?, payload]`, a terminator, then a 2-cell-unit unary address; the output is the
data payload at the live-address count.  Its language spec is three small total recursions
(`liveData`, `postData`, `liveCount`), designed to match the two-pointer marking machine of
the next brick on *all* inputs (marked units are skipped, so the spec is stable under the
machine's own in-place consumption discipline).  Across the middle cut, distinct data blocks
give distinct subfunctions — evaluated at unary addresses they read out every data bit — so
the slice subfunction count (`subfunCountAt`, Nečiporuk's measure) is `≥ 2^m` at slice
`6m+6` (`two_pow_le_subfunCountAt_dIndex`), and the profile is not polynomially bounded
(`subfunProfile_dIndex_not_polyBounded`, by the `(k+1)·s` cancellation trick — no
exp-vs-poly asymptotics needed).

**The kill.**  `subfun_dominating_not_genSound`: *given* a poly decider of `dIndexLang`
(the machine is the next brick — a two-pointer marking construction, M1's named "remaining
mountain", stated here as the explicit fence `DIndexInP` and **not** asserted), every
invariant dominating the subfunction profile of `dIndexLang` at that machine fails
`InvGenSound`; and `langRank_kill`: every language-level measure dominating subfunction
counts on all languages fails `LangGenSound`.  Consequences for the SPDP candidate: a
language-level extraction cannot be generically sound unless its measure stays polynomial
on `dIndexLang` — i.e. unless it *refuses* to see communication-type rank — while `InvHard`
for SAT demands it see superpolynomial rank there.  A measure doing both would itself
separate P from NP at the language level; that is the content, not the wiring.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LangRankKill

open Classical
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo
open PallLean.Paper93.DeepMath.PathB.ComposableMachine (Machine Decides InP)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## The doubled-INDEX language -/

/-- Data-block decoder: 3-cell units `[live?, mark?, payload]`.  A live unit
(`true, true, d`) contributes its payload; a marked unit (`true, false, d`) is skipped
(the machine's consumption discipline); a `false` head cell is the terminator (or void)
and stops the block. -/
def liveData : List Bool → List Bool
  | true :: m :: d :: r => if m then d :: liveData r else liveData r
  | _ => []

/-- What follows the data block: skip 3-cell data units, then consume the 3-cell
terminator. -/
def postData : List Bool → List Bool
  | true :: _ :: _ :: r => postData r
  | rest => rest.drop 3

/-- Live-address count: 2-cell units.  `(true, true)` is a live address unit,
`(true, false)` a consumed one; a `false` head cell ends the address block. -/
def liveCount : List Bool → ℕ
  | true :: a :: r => (if a then 1 else 0) + liveCount r
  | _ => 0

/-- **The doubled-INDEX language**: the live data payload at the live-address count. -/
def dIndexLang (w : List Bool) : Bool :=
  (liveData w).getD (liveCount (postData w)) false

/-- Pristine data encoding: each bit becomes a live 3-cell unit. -/
def encData : List Bool → List Bool
  | [] => []
  | b :: d => true :: true :: b :: encData d

theorem encData_length (d : List Bool) : (encData d).length = 3 * d.length := by
  induction d with
  | nil => rfl
  | cons b d ih =>
    show (true :: true :: b :: encData d).length = 3 * (b :: d).length
    simp only [List.length_cons, ih]
    omega

/-! ## Well-formed evaluation -/

theorem liveData_stop (r : List Bool) : liveData (false :: r) = [] := rfl

theorem liveData_live (d : Bool) (r : List Bool) :
    liveData (true :: true :: d :: r) = d :: liveData r := rfl

theorem liveData_wf (d : List Bool) (rest : List Bool) :
    liveData (encData d ++ false :: rest) = d := by
  induction d with
  | nil => exact liveData_stop rest
  | cons b d ih =>
    show liveData (true :: true :: b :: (encData d ++ false :: rest)) = b :: d
    rw [liveData_live, ih]

theorem postData_wf (d : List Bool) (x y : Bool) (rest : List Bool) :
    postData (encData d ++ false :: x :: y :: rest) = rest := by
  induction d with
  | nil => rfl
  | cons b d ih =>
    show postData (true :: true :: b :: (encData d ++ false :: x :: y :: rest)) = rest
    exact ih

theorem liveCount_wf (i : ℕ) (rest : List Bool) :
    liveCount (List.replicate (2 * i) true ++ false :: rest) = i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 from by omega, List.replicate_succ,
      List.replicate_succ]
    show 1 + liveCount (List.replicate (2 * i) true ++ false :: rest) = i + 1
    rw [ih]
    omega

/-- **Well-formed split evaluation**: pristine data, terminator, unary address — the
output is the addressed data bit. -/
theorem dIndexLang_split (d : List Bool) (i : ℕ) (pad : List Bool) :
    dIndexLang (encData d
        ++ false :: false :: false :: (List.replicate (2 * i) true ++ false :: pad))
      = d.getD i false := by
  unfold dIndexLang
  rw [liveData_wf, postData_wf, liveCount_wf]

/-! ## The subfunction-count measure (Nečiporuk) -/

/-- The number of distinct subfunctions of `L` induced on length-`e` suffixes by length-`c`
prefixes.  This is the classical Nečiporuk/one-way-communication rank of the slice at the
cut `c`. -/
noncomputable def subfunCountAt (L : List Bool → Bool) (c e : ℕ) : ℕ :=
  (Finset.univ.image
    (fun u : Fin c → Bool => fun v : Fin e → Bool =>
      L (List.ofFn u ++ List.ofFn v))).card

/-- The middle-cut subfunction profile of a language. -/
noncomputable def subfunProfile (L : List Bool → Bool) (n : ℕ) : ℕ :=
  subfunCountAt L (n / 2) (n - n / 2)

/-! ## Vector/list plumbing -/

theorem ofFn_getD (l : List Bool) (c : ℕ) (hl : l.length = c) :
    List.ofFn (fun j : Fin c => l.getD (↑j) false) = l := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

theorem getD_ofFn {m : ℕ} (a : Fin m → Bool) (i : Fin m) :
    (List.ofFn a).getD (↑i) false = a i := by
  rw [List.getD_eq_getElem?_getD]
  simp

/-- The prefix vector: pristine data plus terminator, as a length-`3m+3` tuple. -/
def encU (m : ℕ) (a : Fin m → Bool) : Fin (3 * m + 3) → Bool := fun j =>
  (encData (List.ofFn a) ++ [false, false, false]).getD (↑j) false

/-- The suffix vector: the unary address `i` padded to length `3m+3`. -/
def encV (m : ℕ) (i : Fin m) : Fin (3 * m + 3) → Bool := fun j =>
  (List.replicate (2 * ↑i) true ++ false :: List.replicate (3 * m + 2 - 2 * ↑i) false).getD
    (↑j) false

theorem ofFn_encU (m : ℕ) (a : Fin m → Bool) :
    List.ofFn (encU m a) = encData (List.ofFn a) ++ [false, false, false] := by
  apply ofFn_getD
  simp [encData_length]

theorem ofFn_encV (m : ℕ) (i : Fin m) :
    List.ofFn (encV m i)
      = List.replicate (2 * ↑i) true ++ false :: List.replicate (3 * m + 2 - 2 * ↑i) false := by
  apply ofFn_getD
  have := i.isLt
  simp
  omega

/-- **The readout**: the subfunction of the data prefix, evaluated at the unary address
`i`, returns the `i`-th data bit. -/
theorem eval_encU_encV (m : ℕ) (a : Fin m → Bool) (i : Fin m) :
    dIndexLang (List.ofFn (encU m a) ++ List.ofFn (encV m i)) = a i := by
  rw [ofFn_encU, ofFn_encV, List.append_assoc]
  show dIndexLang (encData (List.ofFn a)
      ++ false :: false :: false ::
        (List.replicate (2 * ↑i) true ++ false :: List.replicate (3 * m + 2 - 2 * ↑i) false))
    = a i
  rw [dIndexLang_split, getD_ofFn]

/-! ## The superpolynomial lower bound -/

/-- **`2^m` subfunctions at the middle cut of slice `6m+6`**: distinct data blocks induce
distinct subfunctions, read out by the unary-address suffixes. -/
theorem two_pow_le_subfunCountAt_dIndex (m : ℕ) :
    2 ^ m ≤ subfunCountAt dIndexLang (3 * m + 3) (3 * m + 3) := by
  unfold subfunCountAt
  have hinj : Function.Injective
      (fun a : Fin m → Bool => fun v : Fin (3 * m + 3) → Bool =>
        dIndexLang (List.ofFn (encU m a) ++ List.ofFn v)) := by
    intro a b hab
    funext i
    have h : dIndexLang (List.ofFn (encU m a) ++ List.ofFn (encV m i))
        = dIndexLang (List.ofFn (encU m b) ++ List.ofFn (encV m i)) :=
      congrFun hab (encV m i)
    rwa [eval_encU_encV, eval_encU_encV] at h
  have hcard1 : (Finset.univ.image
      (fun a : Fin m → Bool => fun v : Fin (3 * m + 3) → Bool =>
        dIndexLang (List.ofFn (encU m a) ++ List.ofFn v))).card = 2 ^ m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp
  have hsub : Finset.univ.image
      (fun a : Fin m → Bool => fun v : Fin (3 * m + 3) → Bool =>
        dIndexLang (List.ofFn (encU m a) ++ List.ofFn v))
      ⊆ Finset.univ.image
        (fun u : Fin (3 * m + 3) → Bool => fun v : Fin (3 * m + 3) → Bool =>
          dIndexLang (List.ofFn u ++ List.ofFn v)) := by
    intro y hy
    simp only [Finset.mem_image] at hy ⊢
    obtain ⟨a, _, rfl⟩ := hy
    exact ⟨encU m a, Finset.mem_univ _, rfl⟩
  calc 2 ^ m
      = (Finset.univ.image
          (fun a : Fin m → Bool => fun v : Fin (3 * m + 3) → Bool =>
            dIndexLang (List.ofFn (encU m a) ++ List.ofFn v))).card := hcard1.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem subfunProfile_dIndex_eq (m : ℕ) :
    subfunProfile dIndexLang (6 * m + 6)
      = subfunCountAt dIndexLang (3 * m + 3) (3 * m + 3) := by
  unfold subfunProfile
  rw [show (6 * m + 6) / 2 = 3 * m + 3 from by omega]
  rw [show 6 * m + 6 - (3 * m + 3) = 3 * m + 3 from by omega]

/-- **The profile is not polynomially bounded.**  From `2^m ≤ C·(m+1)^k` at
`m := (k+1)·s`, the power `(s+1)^{k+1} ≤ (2^s)^{k+1}` cancels against `(s+1)^k` to force
`s + 1 ≤ C·(k+1)^k` for every `s` — false at `s := C·(k+1)^k`. -/
theorem subfunProfile_dIndex_not_polyBounded :
    ¬ PolyBounded (subfunProfile dIndexLang) := by
  rintro ⟨c, k, h⟩
  have key : ∀ m, 2 ^ m ≤ c * 7 ^ k * (m + 1) ^ k := by
    intro m
    have h1 := h (6 * m + 6)
    rw [subfunProfile_dIndex_eq] at h1
    have h2 := (two_pow_le_subfunCountAt_dIndex m).trans h1
    have h4 : (6 * m + 6 + 1) ^ k ≤ (7 * (m + 1)) ^ k :=
      Nat.pow_le_pow_left (by omega) k
    calc 2 ^ m ≤ c * (6 * m + 6 + 1) ^ k := h2
      _ ≤ c * (7 * (m + 1)) ^ k := Nat.mul_le_mul_left c h4
      _ = c * 7 ^ k * (m + 1) ^ k := by rw [Nat.mul_pow]; ring
  have key2 : ∀ s, s + 1 ≤ c * 7 ^ k * (k + 1) ^ k := by
    intro s
    have hk := key ((k + 1) * s)
    have hpos : (0 : ℕ) < (s + 1) ^ k := pow_pos (by omega) k
    have ha : (s + 1) ^ (k + 1) ≤ 2 ^ ((k + 1) * s) := by
      have h1 : s + 1 ≤ 2 ^ s := Nat.succ_le_of_lt Nat.lt_two_pow_self
      calc (s + 1) ^ (k + 1) ≤ (2 ^ s) ^ (k + 1) := Nat.pow_le_pow_left h1 (k + 1)
        _ = 2 ^ (s * (k + 1)) := (pow_mul 2 s (k + 1)).symm
        _ = 2 ^ ((k + 1) * s) := by rw [Nat.mul_comm]
    have hb : ((k + 1) * s + 1) ^ k ≤ ((k + 1) * (s + 1)) ^ k := by
      refine Nat.pow_le_pow_left ?_ k
      have hexp : (k + 1) * (s + 1) = (k + 1) * s + (k + 1) := by ring
      omega
    have hchain : (s + 1) ^ k * (s + 1) ≤ (s + 1) ^ k * (c * 7 ^ k * (k + 1) ^ k) := by
      calc (s + 1) ^ k * (s + 1)
          = (s + 1) ^ (k + 1) := (pow_succ (s + 1) k).symm
        _ ≤ 2 ^ ((k + 1) * s) := ha
        _ ≤ c * 7 ^ k * ((k + 1) * s + 1) ^ k := hk
        _ ≤ c * 7 ^ k * ((k + 1) * (s + 1)) ^ k := Nat.mul_le_mul_left _ hb
        _ = c * 7 ^ k * ((k + 1) ^ k * (s + 1) ^ k) := by rw [Nat.mul_pow]
        _ = (s + 1) ^ k * (c * 7 ^ k * (k + 1) ^ k) := by ring
    exact Nat.le_of_mul_le_mul_left hchain hpos
  have := key2 (c * 7 ^ k * (k + 1) ^ k)
  omega

/-! ## The kill -/

/-- **The machine-level kill.**  Given any polynomial-time decider of the doubled-INDEX
language (the two-pointer marking machine — the next brick), every invariant dominating
the language's subfunction profile at that machine fails generic soundness. -/
theorem subfun_dominating_not_genSound {M : Machine} {T : ℕ → ℕ}
    (hT : PolyBounded T) (hM : Decides M dIndexLang T) (Inv : Invariant)
    (hdom : ∀ n, subfunProfile dIndexLang n ≤ Inv M n) :
    ¬ InvGenSound Inv := by
  intro hG
  have hpoly : PolyBounded (Inv M) := hG M ⟨T, hT, fun x => (hM x).1⟩
  exact subfunProfile_dIndex_not_polyBounded (polyBounded_of_le hdom hpoly)

/-- A language-level measure: a rank profile assigned to every language. -/
def LangMeasure := (List Bool → Bool) → ℕ → ℕ

/-- Language-level generic soundness: polynomial languages have polynomial measure. -/
def LangGenSound (μ : LangMeasure) : Prop := ∀ L, InP L → PolyBounded (μ L)

/-- **The engineering fence** (the next brick, *not* asserted): the doubled-INDEX
language has a polynomial-time decider — the classic two-pointer marking machine. -/
def DIndexInP : Prop := InP dIndexLang

/-- **The language-level kill.**  Modulo the machine fence, every language-level measure
dominating subfunction counts fails language-level generic soundness: it cannot serve as
the sound half of an invariant route.  A language-level extraction must therefore be
*blind* to communication-type rank — while SAT-hardness of such a measure would demand
exactly that rank be visible.  That tension is the entire content of the language-level
route. -/
theorem langRank_kill (μ : LangMeasure) (hdom : ∀ L n, subfunProfile L n ≤ μ L n)
    (hfence : DIndexInP) : ¬ LangGenSound μ := by
  intro hG
  exact subfunProfile_dIndex_not_polyBounded
    (polyBounded_of_le (hdom dIndexLang) (hG _ hfence))

end PallLean.Paper93.DeepMath.PathB.LangRankKill
