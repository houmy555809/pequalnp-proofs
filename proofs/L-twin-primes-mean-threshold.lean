import Mathlib

theorem PEqualNP.Outside.L_twin_primes_mean_threshold :
    ∀ θ : ℝ, θ < 7/8 → ∃ ε : ℝ, 0 < ε ∧ Filter.Tendsto (fun x : ℝ => x ^ (θ+1/8+ε) / x) Filter.atTop (nhds 0) := by

  intro θ hθ
  refine ⟨(7/8 - θ)/2, by linarith, ?_⟩
  have hy : 0 < (7/8 - θ)/2 := by linarith
  have hexp : θ + 1/8 + (7/8 - θ)/2 = 1 + -((7/8 - θ)/2) := by ring
  rw [hexp]
  refine (tendsto_rpow_neg_atTop hy).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with x hx
  rw [Real.rpow_add hx, Real.rpow_one]
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp