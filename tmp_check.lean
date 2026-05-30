import PallLean.Paper93.DeepMath.PathB.ComputationalDepthStepAObligationCertificates

namespace PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation

example {n d : Nat} (h : Rat.ofInt (Int.ofNat n) <= Rat.ofInt (Int.ofNat d)) : n <= d := by
  norm_num at h
  exact h

example {n d : Nat} (h : (n : Rat) <= (d : Rat)) : n <= d := by
  exact_mod_cast h

example {n d : Nat} (h : Rat.ofInt (Int.ofNat n) <= Rat.ofInt (Int.ofNat d)) : n <= d := by
  have h' : (n : Rat) <= (d : Rat) := by simpa using h
  exact_mod_cast h'

end PallLean.Paper93.DeepMath.PathB
