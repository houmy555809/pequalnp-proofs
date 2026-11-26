import Mathlib

theorem PEqualNP.Outside.L_twin_primes_positive_product :
    let f := fun (p : ℕ) => if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1; let twinC := ∏' p : ℕ, f p; 0 < twinC := by
  dsimp only
  have habs : ∀ a : ℝ, 0 ≤ a → a ≤ 1/2 → |Real.log (1 - a)| ≤ 2 * a := by
    intro a ha0 ha1
    have hpos1 : 0 < 1 - a := by linarith
    have hle1 : 1 - a ≤ 1 := by linarith
    have hlog : Real.log (1 - a) ≤ 0 := Real.log_nonpos hpos1.le hle1
    rw [abs_of_nonpos hlog]
    have h1 : -Real.log (1 - a) = Real.log ((1 - a)⁻¹) := by
      rw [Real.log_inv]
    rw [h1]
    have h2 : Real.log ((1 - a)⁻¹) ≤ (1 - a)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : (1 - a)⁻¹ - 1 = a / (1 - a) := by
      field_simp
      ring
    have h4 : a / (1 - a) ≤ 2 * a := by
      rw [div_le_iff₀ hpos1]
      nlinarith
    linarith
  have hpos : ∀ p : ℕ, 0 < (if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1) := by
    intro p
    by_cases h : p.Prime ∧ 2 < p
    · rw [if_pos h]
      have hp : (3:ℝ) ≤ (p:ℝ) := by
        have h3 : 3 ≤ p := by omega
        exact_mod_cast h3
      have hden : (0:ℝ) < ((p:ℝ)-1)^2 := by nlinarith
      have hlt : 1/((p:ℝ)-1)^2 ≤ 1/4 := by
        rw [div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 4)]
        nlinarith
      linarith
    · rw [if_neg h]; norm_num
  have hbound : ∀ p : ℕ, |Real.log (if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1)| ≤ 8/(p:ℝ)^2 := by
    intro p
    by_cases h : p.Prime ∧ 2 < p
    · rw [if_pos h]
      have hp : (3:ℝ) ≤ (p:ℝ) := by
        have h3 : 3 ≤ p := by omega
        exact_mod_cast h3
      have hden : (0:ℝ) < ((p:ℝ)-1)^2 := by nlinarith
      have hy : (0:ℝ) < (p:ℝ)^2 := by positivity
      have ha0 : 0 ≤ 1/((p:ℝ)-1)^2 := by positivity
      have ha1 : 1/((p:ℝ)-1)^2 ≤ 1/2 := by
        rw [div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
        nlinarith
      have hb := habs (1/((p:ℝ)-1)^2) ha0 ha1
      have h68 : 2 * (1/((p:ℝ)-1)^2) ≤ 8/(p:ℝ)^2 := by
        rw [show (2:ℝ) * (1/((p:ℝ)-1)^2) = 2/((p:ℝ)-1)^2 by ring]
        rw [div_le_div_iff₀ hden hy]
        nlinarith
      linarith
    · rw [if_neg h, Real.log_one, abs_zero]
      positivity
  have hbase : Summable (fun p : ℕ => 8 / (p:ℝ)^2) := by
    have h2 : Summable (fun p : ℕ => 1 / (p:ℝ)^2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h3 := h2.mul_left (8:ℝ)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h3
  have hsum : Summable (fun p : ℕ => Real.log (if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1)) := by
    refine Summable.of_norm_bounded hbase ?_
    intro p
    rw [Real.norm_eq_abs]
    exact hbound p
  rw [← Real.rexp_tsum_eq_tprod hpos hsum]
  exact Real.exp_pos _
