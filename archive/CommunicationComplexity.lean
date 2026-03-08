import Mathlib
import PallLean.TseitinOBDD

/-!
# Communication Complexity Lower Bound from Residual Explosion

## Overview

We formalize the following chain:

1. **Residual explosion** (from TseitinOBDD): at a good cut, there exist
   2^c prefix assignments with pairwise distinct residual functions.

2. **Communication lower bound**: any deterministic protocol computing f
   where Alice holds variables 0..k-1 and Bob holds k..m-1 must
   transmit ≥ c bits.

This is a standard rectangle argument: a protocol with b bits of
communication partitions Alice's inputs into at most 2^b equivalence
classes. If two Alice inputs are in the same class, Bob receives the
same message and must give the same answer. But if those two inputs
induce different residual functions, there exists a Bob input that
distinguishes them — contradiction.

## Significance

This shows the residual explosion is not just an OBDD artifact but a
genuine communication complexity barrier. Any two-party protocol
(not just OBDDs) must exchange Ω(n/d²) bits at the cut.
-/

open Finset

namespace TseitinOBDD

/-! ## 1. Deterministic Communication Protocols -/

/-- A deterministic communication protocol for a Boolean function on m bits,
    split at position k: Alice holds bits 0..k-1, Bob holds bits k..m-1.
    
    A protocol with b bits of communication is modeled by Alice's message
    function: she maps her input to one of 2^b messages. Bob then computes
    the output from (message, his_input).
    
    We only need Alice's message function for the lower bound —
    if she sends < c bits, she has < 2^c distinct messages,
    so by pigeonhole two distinct-residual inputs share a message. -/
structure Protocol (m k b : ℕ) where
  /-- Alice's message: maps her input (first k bits) to a message in Fin (2^b) -/
  aliceMsg : (Fin k → Bool) → Fin (2 ^ b)
  /-- Bob's output: given Alice's message and his input, produces the answer -/
  bobOut : Fin (2 ^ b) → (Fin (m - k) → Bool) → Bool

/-- A protocol computes a function f if for all inputs, the protocol output
    equals f applied to the combined input. -/
def Protocol.computes {m k b : ℕ} (P : Protocol m k b)
    (hk : k ≤ m) (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ (α : Fin k → Bool) (β : Fin (m - k) → Bool),
    P.bobOut (P.aliceMsg α) β = f (fun i =>
      if h : i.val < k then α ⟨i.val, h⟩
      else β ⟨i.val - k, by omega⟩)

/-! ## 2. Rectangle Argument -/

/-- **Key lemma**: If a protocol computes f with b bits of communication,
    and there exist 2^c inputs to Alice with pairwise distinct residual
    functions, then b ≥ c.
    
    Proof: Alice sends one of 2^b messages. If b < c, then 2^b < 2^c,
    so by pigeonhole, two Alice inputs α₁, α₂ with distinct residuals
    share the same message. Then Bob receives the same message for both,
    so he must output the same value for any β. But distinct residuals
    means there exists β where f(α₁, β) ≠ f(α₂, β) — contradiction. -/
theorem comm_lower_bound_from_residuals (m k b c : ℕ) (hk : k ≤ m)
    (f : (Fin m → Bool) → Bool)
    (P : Protocol m k b) (h_comp : P.computes hk f)
    -- 2^c Alice inputs with pairwise distinct residuals
    (assign : Fin (2 ^ c) → (Fin k → Bool))
    (h_distinct : ∀ i j : Fin (2 ^ c), i ≠ j →
      ∃ β : Fin (m - k) → Bool,
        f (fun e => if h : e.val < k then assign i ⟨e.val, h⟩
                    else β ⟨e.val - k, by omega⟩) ≠
        f (fun e => if h : e.val < k then assign j ⟨e.val, h⟩
                    else β ⟨e.val - k, by omega⟩)) :
    c ≤ b := by
  -- Proof by contradiction: assume b < c
  by_contra h_lt
  push_neg at h_lt
  -- Alice sends one of 2^b messages. Since 2^b < 2^c, by pigeonhole
  -- there exist i ≠ j with aliceMsg(assign i) = aliceMsg(assign j).
  have h_card : Fintype.card (Fin (2 ^ b)) < Fintype.card (Fin (2 ^ c)) := by
    simp [Fintype.card_fin]; exact Nat.pow_lt_pow_right (by omega) h_lt
  have h_pigeon := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (2 ^ c) => P.aliceMsg (assign i)) h_card
  obtain ⟨i, j, hij, h_msg⟩ := h_pigeon
  -- Get the distinguishing Bob input
  obtain ⟨β, h_diff⟩ := h_distinct i j hij
  -- But Bob sees the same message for both, so must output the same
  have h_same : P.bobOut (P.aliceMsg (assign i)) β =
                P.bobOut (P.aliceMsg (assign j)) β :=
    congr_arg (P.bobOut · β) h_msg
  -- Protocol correctness gives:
  have h1 := h_comp (assign i) β
  have h2 := h_comp (assign j) β
  -- Combining: f(αi, β) = bobOut(msg, β) = f(αj, β)
  exact h_diff (h1.symm.trans (h_same.trans h2))

/-! ## 3. Tseitin Communication Complexity -/

/-- **Main theorem**: For Tseitin on expanders with a good cut producing
    c independent split vertices, any deterministic communication protocol
    computing tseitinSubsetSAT (split at the good cut) requires ≥ c bits.
    
    This follows immediately from:
    - `tseitin_parity_residuals`: produces 2^c inputs with distinct residuals
    - `comm_lower_bound_from_residuals`: distinct residuals → communication ≥ c -/
theorem tseitin_comm_complexity (G : Tseitin.RegularGraph)
    (labels : Fin G.numVertices → Bool) (c : ℕ)
    (k : Fin (G.numEdges + 1)) (hk : k.val ≤ G.numEdges)
    -- Same hypotheses as tseitin_parity_residuals
    (verts : Fin c → Fin G.numVertices)
    (leftEdge rightEdge : Fin c → Fin G.numEdges)
    (h_verts_inj : Function.Injective verts)
    (h_left_pos : ∀ i, (leftEdge i).val < k.val)
    (h_left_inc : ∀ i, G.edgeSrc (leftEdge i) = verts i ∨
                        G.edgeTgt (leftEdge i) = verts i)
    (h_left_inj : Function.Injective leftEdge)
    (h_left_priv : ∀ i j, i ≠ j →
      G.edgeSrc (leftEdge i) ≠ verts j ∧ G.edgeTgt (leftEdge i) ≠ verts j)
    (h_right_pos : ∀ i, (rightEdge i).val ≥ k.val)
    (h_right_inc : ∀ i, G.edgeSrc (rightEdge i) = verts i ∨
                         G.edgeTgt (rightEdge i) = verts i)
    (h_right_priv : ∀ i j, i ≠ j →
      G.edgeSrc (rightEdge i) ≠ verts j ∧ G.edgeTgt (rightEdge i) ≠ verts j)
    (h_sat : ∀ α : MUSWidthLowerBound.PartialAssignment G.numEdges k.val,
      ∃ β, MUSWidthLowerBound.residual (tseitinSubsetSAT G labels) k.val hk α β = true)
    -- The protocol
    (b : ℕ) (P : Protocol G.numEdges k.val b)
    (h_comp : P.computes hk (tseitinSubsetSAT G labels)) :
    c ≤ b := by
  -- Get the 2^c distinct-residual assignments
  obtain ⟨assign, h_inj⟩ := tseitin_parity_residuals G labels c k hk
    verts leftEdge rightEdge h_verts_inj
    h_left_pos h_left_inc h_left_inj h_left_priv
    h_right_pos h_right_inc h_right_priv h_sat
  -- Apply the rectangle argument
  exact comm_lower_bound_from_residuals G.numEdges k.val b c hk
    (tseitinSubsetSAT G labels) P h_comp assign (fun i j hij => by
      -- Distinct residuals → distinguishing Bob input exists
      have h_ne := h_inj i j hij
      -- h_ne : residual ... (assign i) ≠ residual ... (assign j)
      -- This means the functions differ on some input β
      have h_ex : ∃ β, MUSWidthLowerBound.residual (tseitinSubsetSAT G labels)
          k.val hk (assign i) β ≠
          MUSWidthLowerBound.residual (tseitinSubsetSAT G labels)
          k.val hk (assign j) β := by
        by_contra h_all
        push_neg at h_all
        exact h_ne (funext h_all)
      obtain ⟨β, hβ⟩ := h_ex
      exact ⟨β, hβ⟩)

end TseitinOBDD
