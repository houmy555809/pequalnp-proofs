import Mathlib

theorem PEqualNP.Outside.L_twin_primes_vanishing_error :
    let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; Filter.Tendsto e Filter.atTop (nhds 0) := by

  dsimp only
  have hbase : Filter.Tendsto (fun x : ℝ => Real.log x ^ (3:ℕ) / x ^ ((1:ℝ)/2)) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun x : ℝ => Real.log x ^ (3:ℝ) / x ^ ((1:ℝ)/2)) Filter.atTop (nhds 0) :=
      (isLittleO_log_rpow_rpow_atTop (3:ℝ) (by norm_num)).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with x hx
    have h3 : (3:ℝ) = ((3:ℕ):ℝ) := by norm_num
    rw [h3, Real.rpow_natCast]
  have hnat : Filter.Tendsto (fun X : ℕ => (X:ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hg : Filter.Tendsto (fun X : ℕ => 8 * (Real.log (X:ℝ) ^ 3 / (X:ℝ) ^ ((1:ℝ)/2))) Filter.atTop (nhds 0) := by
    have h := hbase.comp hnat
    simpa using h.const_mul 8
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards with X
    have hXnn : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
    have hlog : 0 ≤ Real.log (2 + (X:ℝ)) := Real.log_nonneg (by linarith)
    exact div_nonneg (pow_nonneg hlog 3) (Real.sqrt_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop (2:ℕ)] with X hX
    have hX2 : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
    have hX0 : (0:ℝ) < (X:ℝ) := by linarith
    have hlogX : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg (by linarith : (1:ℝ) ≤ (X:ℝ))
    have hlog2X : Real.log (2 + (X:ℝ)) ≤ 2 * Real.log (X:ℝ) := by
      have hle : (2:ℝ) + X ≤ 2 * X := by linarith
      have h1 : Real.log (2 + (X:ℝ)) ≤ Real.log (2 * (X:ℝ)) :=
        Real.log_le_log (by positivity) hle
      have h2 : Real.log (2 * (X:ℝ)) = Real.log 2 + Real.log (X:ℝ) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hX0)]
      have h3 : Real.log 2 ≤ Real.log (X:ℝ) := Real.log_le_log (by norm_num) hX2
      linarith
    have hcube : Real.log (2 + (X:ℝ)) ^ 3 ≤ 8 * Real.log (X:ℝ) ^ 3 := by
      have hnn : 0 ≤ Real.log (2 + (X:ℝ)) := Real.log_nonneg (by linarith)
      have h := pow_le_pow_left₀ hnn hlog2X 3
      calc Real.log (2 + (X:ℝ)) ^ 3 ≤ (2 * Real.log (X:ℝ)) ^ 3 := h
        _ = 8 * Real.log (X:ℝ) ^ 3 := by ring
    have hsqrt : Real.sqrt (X:ℝ) = (X:ℝ) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow (X:ℝ)
    rw [hsqrt]
    have hden : 0 < (X:ℝ) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hX0 _
    rw [div_le_iff₀ hden]
    have hmul : 8 * (Real.log (X:ℝ) ^ 3 / (X:ℝ) ^ ((1:ℝ)/2)) * (X:ℝ) ^ ((1:ℝ)/2) = 8 * Real.log (X:ℝ) ^ 3 := by
      field_simp
    rw [hmul]
    exact hcube