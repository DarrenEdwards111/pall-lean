import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBlockRowCount

/-!
# N-Frame: positive-cell obstruction — crossing cells are interface-blind

The "amplituhedron" rung, at its honest formal strength.  The discrete content of the positive-geometry
intuition ("positivity prevents destructive interference, so fragmentation cannot cancel local
obstructions") turns out to be a real theorem about *interfaced* factorizations `f = op (g|_A, h|_B)`:

**a hypercube 2-cell whose two flip-coordinates are invisible to the opposite factors constrains the
combiner `op` exactly as in the zero-interface case — the shared interface `A ∩ B` never enters the
computation.**

  `opParity` — the combiner's cell invariant: the parity of its full truth table.
  `xor_square_combo_even` / `odd_combo_odd` — **PROVED, the Bool cores**: a 2×2 corner table of
        XOR-square type forces `opParity op = false`; an odd-parity table forces `opParity op = true`.
  `crossing_cells_kill_interfaced` — **PROVED, the engine**: an XOR-square crossing at `(s₁, t₁)` and an
        odd square crossing at `(s₂, t₂)` (possibly different pairs, different base points — `op` is
        global) refute any factorization with `s ∉ B`, `t ∉ A`, **regardless of `|A ∩ B|`**.  The
        zero-interface `two_squares_kill_split` is the special case `A = S`, `B = Sᶜ`.
  `sat3_sign_cells_kill_interfaced` — **PROVED, the instantiation**: for every block `cIdx` and pin `j₀`,
        the produced XOR + odd squares on the (pin-sign, designated-sign) pair kill any interfaced
        factorization of `sat3Family` whose exclusive sides separate that pair (both orientations).
  `sat3_sign_pair_dodge` — **PROVED, the dodge constraint**: contrapositive — every interfaced
        factorization must, for **every** `(cIdx, j₀)`, keep the sign pair un-separated: each pair is
        co-located or touches the interface.

## Honest scope — what positivity does and does not buy

Proved: fragmentation via a large interface does **not** weaken a crossing cell; the adversary cannot
dodge the sign-cell family by paying interface *elsewhere* — the dodge must touch each pair itself.
NOT proved (the remaining mountain, unclaimed): HAL's target `every_adversarial_cut_crosses_many_cells` —
i.e. that dodging **all** pattern families simultaneously forces `|A ∩ B| ≥ Ω(m)`.  That is the lift of
the whole Track A residual chain (sign-aligned → all-pins → … → discharge) to interfaced cuts, plus a
counting argument over the dodge graph; the alignment escape (all non-interned sign bits on one exclusive
side) must then be killed by the *other* produced families, exactly as in Track A.  No continuous
amplituhedron geometry is formalized or used — it is motivation language only.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The combiner's cell invariant: the parity of its full truth table. -/
def opParity (op : Bool → Bool → Bool) : Bool :=
  xor (xor (op false false) (op false true)) (xor (op true false) (op true true))

/-- **Bool core I (proved)**: an XOR-square corner table forces even combiner parity. -/
theorem xor_square_combo_even (op : Bool → Bool → Bool) (a a₂ b b₂ α : Bool)
    (e1 : op a b = α) (e2 : op a₂ b = !α) (e3 : op a b₂ = !α) (e4 : op a₂ b₂ = α) :
    opParity op = false := by
  cases a <;> cases a₂ <;> cases b <;> cases b₂ <;> cases α <;>
    simp_all [opParity]

/-- **Bool core II (proved)**: an odd-parity corner table forces odd combiner parity. -/
theorem odd_combo_odd (op : Bool → Bool → Bool) (a a₂ b b₂ : Bool)
    (hodd : xor (xor (op a b) (op a₂ b)) (xor (op a b₂) (op a₂ b₂)) = true) :
    opParity op = true := by
  cases a <;> cases a₂ <;> cases b <;> cases b₂ <;>
    cases h1 : op true true <;> cases h2 : op true false <;>
    cases h3 : op false true <;> cases h4 : op false false <;>
    simp_all [opParity]

/-- **THE INTERFACE-BLIND KILL ENGINE (proved)**: crossing cells refute interfaced factorizations no
matter how large the shared interface is.  Each cell needs only `s ∉ B` and `t ∉ A` — the flips are
invisible to the opposite factors; `A ∩ B` never enters. -/
theorem crossing_cells_kill_interfaced {n : ℕ} (f : (Fin n → Bool) → Bool)
    (A B : Finset (Fin n)) (op : Bool → Bool → Bool) (g h : (Fin n → Bool) → Bool)
    (hg : ∀ x y : Fin n → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin n → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, f x = op (g x) (h x))
    (s₁ t₁ : Fin n) (hs₁ : s₁ ∉ B) (ht₁ : t₁ ∉ A) (hst₁ : s₁ ≠ t₁)
    (s₂ t₂ : Fin n) (hs₂ : s₂ ∉ B) (ht₂ : t₂ ∉ A) (hst₂ : s₂ ≠ t₂)
    (u w : Fin n → Bool) (α : Bool)
    -- the XOR-square crossing at (s₁, t₁), base u
    (hu : f u = α)
    (hus : f (Function.update u s₁ (!(u s₁))) = !α)
    (hut : f (Function.update u t₁ (!(u t₁))) = !α)
    (hust : f (Function.update (Function.update u s₁ (!(u s₁))) t₁ (!(u t₁))) = α)
    -- the odd-parity square crossing at (s₂, t₂), base w
    (hodd : xor (xor (f w) (f (Function.update w s₂ (!(w s₂)))))
        (xor (f (Function.update w t₂ (!(w t₂))))
          (f (Function.update (Function.update w s₂ (!(w s₂))) t₂ (!(w t₂))))) = true) :
    False := by
  classical
  -- flips at s ∉ B are invisible to h; flips at t ∉ A are invisible to g
  have hhs₁ : ∀ (z : Fin n → Bool) (v : Bool), h (Function.update z s₁ v) = h z := by
    intro z v
    apply hh
    intro i hi
    exact Function.update_of_ne (fun hc => hs₁ (by rw [← hc]; exact hi)) _ _
  have hgt₁ : ∀ (z : Fin n → Bool) (v : Bool), g (Function.update z t₁ v) = g z := by
    intro z v
    apply hg
    intro i hi
    exact Function.update_of_ne (fun hc => ht₁ (by rw [← hc]; exact hi)) _ _
  have hhs₂ : ∀ (z : Fin n → Bool) (v : Bool), h (Function.update z s₂ v) = h z := by
    intro z v
    apply hh
    intro i hi
    exact Function.update_of_ne (fun hc => hs₂ (by rw [← hc]; exact hi)) _ _
  have hgt₂ : ∀ (z : Fin n → Bool) (v : Bool), g (Function.update z t₂ v) = g z := by
    intro z v
    apply hg
    intro i hi
    exact Function.update_of_ne (fun hc => ht₂ (by rw [← hc]; exact hi)) _ _
  -- the XOR-square corners in op-form
  simp only [hf] at hu hus hut hust
  rw [hhs₁] at hus
  rw [hgt₁] at hut
  rw [hgt₁, Function.update_comm hst₁, hhs₁] at hust
  have heven := xor_square_combo_even op (g u) (g (Function.update u s₁ (!(u s₁))))
    (h u) (h (Function.update u t₁ (!(u t₁)))) α hu hus hut hust
  -- the odd-square corners in op-form
  simp only [hf] at hodd
  rw [hhs₂, hgt₂, hgt₂, Function.update_comm hst₂, hhs₂] at hodd
  have hoddp := odd_combo_odd op (g w) (g (Function.update w s₂ (!(w s₂))))
    (h w) (h (Function.update w t₂ (!(w t₂)))) hodd
  rw [heven] at hoddp
  exact Bool.noConfusion hoddp

/-- **THE SAT SIGN-CELL INSTANTIATION (proved)**: for every block and pin, the produced XOR + odd squares
kill any interfaced factorization whose exclusive sides separate the (pin-sign, designated-sign) pair —
both orientations, any interface. -/
theorem sat3_sign_cells_kill_interfaced (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (hsep : (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ B ∧ sat3SignBit N cIdx ∉ A)
      ∨ (sat3SignBit N cIdx ∉ B ∧ sat3Bit N (sat3PinClause N cIdx hk j₀)
        ⟨0, by omega⟩ (sat3V N) (by omega) ∉ A)) : False := by
  classical
  obtain ⟨u, hu, hus, hut, hust⟩ :=
    sat3_xor_square_all_pins N hv hm3 hk cIdx j₀ (fun _ => false)
  obtain ⟨w, hodd⟩ := sat3_odd_square_all_pins N hv hm3 hk cIdx j₀ (fun _ => false)
  have hne : (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
      (sat3V N) (by omega) : Fin N) ≠ sat3SignBit N cIdx :=
    sat3Bit_ne_of_clause N _ _ _ _
      (fun h' => sat3PinClause_ne N cIdx hk j₀ h')
  rcases hsep with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · -- s := pin-sign (∉ B), t := designated sign (∉ A): producer format verbatim
    exact crossing_cells_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      (sat3SignBit N cIdx) hp hq hne
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      (sat3SignBit N cIdx) hp hq hne
      u w false hu hus hut hust hodd
  · -- s := designated sign (∉ B), t := pin-sign (∉ A): commute the double update, shuffle the parity
    have hust' : sat3Family N (Function.update (Function.update u
        (sat3SignBit N cIdx) (!(u (sat3SignBit N cIdx))))
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
        (!(u (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
          (sat3V N) (by omega))))) = false := by
      rw [show Function.update (Function.update u
          (sat3SignBit N cIdx) (!(u (sat3SignBit N cIdx))))
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(u (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
            (sat3V N) (by omega))))
        = Function.update (Function.update u
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(u (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
            (sat3V N) (by omega)))))
          (sat3SignBit N cIdx) (!(u (sat3SignBit N cIdx))) from
        Function.update_comm hne.symm _ _ _]
      exact hust
    have hodd' : xor (xor (sat3Family N w)
        (sat3Family N (Function.update w (sat3SignBit N cIdx)
          (!(w (sat3SignBit N cIdx))))))
        (xor (sat3Family N (Function.update w
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(w (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
            (sat3V N) (by omega))))))
          (sat3Family N (Function.update (Function.update w
            (sat3SignBit N cIdx) (!(w (sat3SignBit N cIdx))))
            (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
            (!(w (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
              (sat3V N) (by omega))))))) = true := by
      rw [show Function.update (Function.update w
          (sat3SignBit N cIdx) (!(w (sat3SignBit N cIdx))))
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(w (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
            (sat3V N) (by omega))))
        = Function.update (Function.update w
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(w (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
            (sat3V N) (by omega)))))
          (sat3SignBit N cIdx) (!(w (sat3SignBit N cIdx))) from
        Function.update_comm hne.symm _ _ _]
      rw [xor_shuffle]
      exact hodd
    exact crossing_cells_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3SignBit N cIdx)
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      hq hp hne.symm
      (sat3SignBit N cIdx)
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      hq hp hne.symm
      u w false hu hut hus hust' hodd'

/-- **THE DODGE CONSTRAINT (proved)**: every interfaced factorization must keep **every** sign pair
un-separated — the pair is co-located or touches the interface; paying interface elsewhere does not
help. -/
theorem sat3_sign_pair_dodge (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) :
    ¬ ((sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ B ∧ sat3SignBit N cIdx ∉ A)
      ∨ (sat3SignBit N cIdx ∉ B ∧ sat3Bit N (sat3PinClause N cIdx hk j₀)
        ⟨0, by omega⟩ (sat3V N) (by omega) ∉ A)) :=
  fun hsep => sat3_sign_cells_kill_interfaced N hv hm3 hk op g h A B hg hh hf
    cIdx j₀ hsep

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.crossing_cells_kill_interfaced
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_cells_kill_interfaced
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_pair_dodge
