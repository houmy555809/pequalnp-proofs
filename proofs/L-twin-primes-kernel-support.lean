import Mathlib

theorem PEqualNP.Outside.L_twin_primes_kernel_support :
    ∀ K : ℝ → ℝ, (∀ v, 1/20 ≤ |v| → K v = 0) → (∀ v, |v| < 1/20 → 0 < K v) → let H := fun (v : ℝ) => K v / 2 - K (v-1/5)/4 - K (v+1/5)/4; (∀ v, 1/4 ≤ |v| → H v = 0) ∧ (∀ v, |v| < 1/20 → 0 < H v) := by
  intro K h0 hpos
  dsimp only
  constructor
  · intro v hv
    have hv1 : K v = 0 := h0 v (by linarith)
    have hv2 : K (v - 1/5) = 0 := by
      apply h0
      have h := abs_sub_abs_le_abs_sub v (1/5 : ℝ)
      have h5 : |(1/5 : ℝ)| = 1/5 := by norm_num
      rw [h5] at h
      linarith
    have hv3 : K (v + 1/5) = 0 := by
      apply h0
      have h := abs_sub_abs_le_abs_sub v (-(1/5) : ℝ)
      have h5 : |(-(1/5) : ℝ)| = 1/5 := by norm_num
      rw [h5] at h
      have : v + 1/5 = v - (-(1/5)) := by ring
      rw [this]
      linarith
    rw [hv1, hv2, hv3]
    norm_num
  · intro v hv
    have hv1 : 0 < K v := hpos v hv
    have hv2 : K (v - 1/5) = 0 := by
      apply h0
      have h := abs_sub_abs_le_abs_sub (1/5 : ℝ) v
      have h5 : |(1/5 : ℝ)| = 1/5 := by norm_num
      rw [h5] at h
      have hcomm : |(1/5 : ℝ) - v| = |v - 1/5| := abs_sub_comm _ _
      rw [hcomm] at h
      linarith
    have hv3 : K (v + 1/5) = 0 := by
      apply h0
      have h := abs_sub_abs_le_abs_sub (-(1/5) : ℝ) v
      have h5 : |(-(1/5) : ℝ)| = 1/5 := by norm_num
      rw [h5] at h
      have hcomm : |(-(1/5) : ℝ) - v| = |v + 1/5| := by
        rw [abs_sub_comm]
        congr 1
        ring
      rw [hcomm] at h
      linarith
    rw [hv2, hv3]
    linarith
