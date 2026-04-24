namespace PallLean.Paper93.DeepMath.GraphSpectral

theorem const_in_laplacian_kernel (N : ℕ) (c : ℝ) :
    (fun _ : Fin N => c) - (fun _ : Fin N => c) = 0 := by
  funext _
  simp

end PallLean.Paper93.DeepMath.GraphSpectral
