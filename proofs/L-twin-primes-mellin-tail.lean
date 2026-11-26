import Mathlib

theorem PEqualNP.Outside.L_twin_primes_mellin_tail :
    ∀ C : ℝ, 0 ≤ C → ∃ D : ℝ, 0 ≤ D ∧ ∀ (L : ℕ) (m : ℕ → ℝ), (∀ n, 0 ≤ m n ∧ m n ≤ C*Real.log (2+(n:ℝ))) → (∑' n : ℕ, m (L+n)/(1+(L:ℝ)+n)^6) ≤ D/(1+(L:ℝ))^4 := by
  intro C hC
  refine ⟨6 * Real.sqrt 2 * C + 1, by positivity, ?_⟩
  intro L m hm
  have hlogsqrt : ∀ y : ℝ, 0 ≤ y → Real.log y ≤ 2 * Real.sqrt y := by
    intro y hy
    have h := Real.log_le_rpow_div hy (by norm_num : (0:ℝ) < 1/2)
    rw [← Real.sqrt_eq_rpow] at h
    have h2 : Real.sqrt y / (1/2) = 2 * Real.sqrt y := by ring
    rw [h2] at h
    exact h
  have ht_nonneg : ∀ n : ℕ, 0 ≤ 1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2) := by
    intro n
    have h1 : 0 < Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
    have h2 : Real.sqrt ((n:ℝ)+1) ≤ Real.sqrt ((n:ℝ)+2) := Real.sqrt_le_sqrt (by linarith)
    have h3 : 1/Real.sqrt ((n:ℝ)+2) ≤ 1/Real.sqrt ((n:ℝ)+1) := one_div_le_one_div_of_le h1 h2
    linarith
  have hpartial : ∀ N : ℕ, (∑ n ∈ Finset.range N, (1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2)))
      = 1 - 1/Real.sqrt ((N:ℝ)+1) := by
    intro N
    have h := Finset.sum_range_sub (fun n : ℕ => 1/Real.sqrt ((n:ℝ)+1)) N
    have hneg : (∑ n ∈ Finset.range N, (1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2)))
        = - (∑ n ∈ Finset.range N, (1/Real.sqrt (((n+1:ℕ):ℝ)+1) - 1/Real.sqrt ((n:ℝ)+1))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      ring
    rw [hneg, h]
    push_cast
    have hf0 : (1:ℝ)/Real.sqrt ((0:ℝ)+1) = 1 := by norm_num
    rw [hf0]
    ring
  have htendsto : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2))) Filter.atTop (nhds 1) := by
    have hlim : Filter.Tendsto (fun N : ℕ => 1/Real.sqrt ((N:ℝ)+1)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun N : ℕ => (N:ℝ)+1) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right Filter.atTop (1:ℝ) tendsto_natCast_atTop_atTop
      have h2 := Real.tendsto_sqrt_atTop.comp h1
      have h3 := h2.inv_tendsto_atTop
      change Filter.Tendsto (fun N : ℕ => ((fun x : ℝ => Real.sqrt x) ((N:ℝ)+1))⁻¹) Filter.atTop (nhds 0) at h3
      simpa only [one_div] using h3
    simp only [hpartial]
    simpa using (tendsto_const_nhds.sub hlim)
  have htel : HasSum (fun n : ℕ => 1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2)) 1 :=
    (hasSum_iff_tendsto_nat_of_nonneg ht_nonneg 1).mpr htendsto
  have hshift : ∀ n : ℕ, 1/(Real.sqrt ((n:ℝ)+2))^3 ≤ 2*(1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2)) := by
    intro n
    have ha : 0 < Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
    have hb : 0 < Real.sqrt ((n:ℝ)+2) := Real.sqrt_pos.mpr (by positivity)
    have hab : Real.sqrt ((n:ℝ)+1) ≤ Real.sqrt ((n:ℝ)+2) := Real.sqrt_le_sqrt (by linarith)
    have hsq : (Real.sqrt ((n:ℝ)+2))^2 - (Real.sqrt ((n:ℝ)+1))^2 = 1 := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      push_cast
      ring
    have hsumpos : 0 < Real.sqrt ((n:ℝ)+2) + Real.sqrt ((n:ℝ)+1) := by positivity
    have hsub : Real.sqrt ((n:ℝ)+2) - Real.sqrt ((n:ℝ)+1) = 1/(Real.sqrt ((n:ℝ)+2) + Real.sqrt ((n:ℝ)+1)) := by
      rw [eq_div_iff (ne_of_gt hsumpos)]
      nlinarith [hsq]
    have hdiff : 1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2)
        = 1/(Real.sqrt ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+2) * (Real.sqrt ((n:ℝ)+2) + Real.sqrt ((n:ℝ)+1))) := by
      calc 1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2)
          = (Real.sqrt ((n:ℝ)+2) - Real.sqrt ((n:ℝ)+1))/(Real.sqrt ((n:ℝ)+1)*Real.sqrt ((n:ℝ)+2)) := by
              field_simp
        _ = (1/(Real.sqrt ((n:ℝ)+2) + Real.sqrt ((n:ℝ)+1)))/(Real.sqrt ((n:ℝ)+1)*Real.sqrt ((n:ℝ)+2)) := by rw [hsub]
        _ = 1/(Real.sqrt ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+2) * (Real.sqrt ((n:ℝ)+2) + Real.sqrt ((n:ℝ)+1))) := by
              field_simp
    rw [hdiff]
    rw [show (2:ℝ) * (1/(Real.sqrt ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+2) * (Real.sqrt ((n:ℝ)+2) + Real.sqrt ((n:ℝ)+1)))) = 2/(Real.sqrt ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+2) * (Real.sqrt ((n:ℝ)+2) + Real.sqrt ((n:ℝ)+1))) by ring]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (Real.sqrt ((n:ℝ)+2))^3)
      (by positivity : (0:ℝ) < Real.sqrt ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+2) * (Real.sqrt ((n:ℝ)+2) + Real.sqrt ((n:ℝ)+1)))]
    have hmain : Real.sqrt ((n:ℝ)+1) * (Real.sqrt ((n:ℝ)+1) + Real.sqrt ((n:ℝ)+2)) ≤ 2 * (Real.sqrt ((n:ℝ)+2))^2 := by
      have h1 : (Real.sqrt ((n:ℝ)+1))^2 ≤ (Real.sqrt ((n:ℝ)+2))^2 := by
        nlinarith [mul_self_le_mul_self (le_of_lt ha) hab]
      have h2 : Real.sqrt ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+2) ≤ (Real.sqrt ((n:ℝ)+2))^2 := by
        nlinarith [mul_le_mul_of_nonneg_right hab (le_of_lt hb)]
      nlinarith [h1, h2]
    have h3 : Real.sqrt ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+2) * (Real.sqrt ((n:ℝ)+2) + Real.sqrt ((n:ℝ)+1))
        = Real.sqrt ((n:ℝ)+2) * (Real.sqrt ((n:ℝ)+1) * (Real.sqrt ((n:ℝ)+1) + Real.sqrt ((n:ℝ)+2))) := by ring
    rw [h3]
    have h4 : Real.sqrt ((n:ℝ)+2) * (Real.sqrt ((n:ℝ)+1) * (Real.sqrt ((n:ℝ)+1) + Real.sqrt ((n:ℝ)+2)))
        ≤ Real.sqrt ((n:ℝ)+2) * (2 * (Real.sqrt ((n:ℝ)+2))^2) :=
      mul_le_mul_of_nonneg_left hmain (le_of_lt hb)
    have h5 : Real.sqrt ((n:ℝ)+2) * (2 * (Real.sqrt ((n:ℝ)+2))^2) = 2 * (Real.sqrt ((n:ℝ)+2))^3 := by ring
    linarith [h4, h5]
  have ht_summable : Summable (fun n : ℕ => 1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2)) := htel.summable
  have ht_tsum : (∑' n : ℕ, (1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2))) = 1 := htel.tsum_eq
  have hu_succ : ∀ n : ℕ, (1/(Real.sqrt (((n+1:ℕ):ℝ)+1))^3) ≤ 2*(1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2)) := by
    intro n
    have harg : (((n+1:ℕ):ℝ)+1) = (n:ℝ)+2 := by push_cast; ring
    rw [harg]
    exact hshift n
  have hu_succ_summable : Summable (fun n : ℕ => 1/(Real.sqrt (((n+1:ℕ):ℝ)+1))^3) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (ht_summable.mul_left 2)
    exact hu_succ n
  have hu_summable : Summable (fun n : ℕ => 1/(Real.sqrt ((n:ℝ)+1))^3) := by
    exact (summable_nat_add_iff (f := fun n : ℕ => 1/(Real.sqrt ((n:ℝ)+1))^3) (k := 1)).mp (by
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hu_succ_summable)
  have hu_bound : (∑' n : ℕ, (1/(Real.sqrt ((n:ℝ)+1))^3)) ≤ 3 := by
    rw [hu_summable.tsum_eq_zero_add]
    have hu0 : (1/(Real.sqrt (((0:ℕ):ℝ)+1))^3) = 1 := by norm_num [Real.sqrt_one]
    rw [hu0]
    have hle : (∑' n : ℕ, (1/(Real.sqrt (((n+1:ℕ):ℝ)+1))^3)) ≤ 2 * (∑' n : ℕ, (1/Real.sqrt ((n:ℝ)+1) - 1/Real.sqrt ((n:ℝ)+2))) := by
      rw [← tsum_mul_left]
      apply Summable.tsum_le_tsum
      · intro n
        exact hu_succ n
      · exact hu_succ_summable
      · exact ht_summable.mul_left 2
    rw [ht_tsum] at hle
    linarith
  have hterm : ∀ n : ℕ, m (L+n)/(1+(L:ℝ)+n)^6 ≤ (2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4) * (1/(Real.sqrt ((n:ℝ)+1))^3) := by
    intro n
    have hm1 : 0 ≤ m (L+n) := (hm (L+n)).1
    have hm2 : m (L+n) ≤ C * Real.log (2 + ((L+n : ℕ) : ℝ)) := (hm (L+n)).2
    have hy : (0:ℝ) ≤ 2 + ((L+n : ℕ) : ℝ) := by positivity
    have hlog1 : Real.log (2 + ((L+n : ℕ) : ℝ)) ≤ 2 * Real.sqrt (2 + ((L+n : ℕ) : ℝ)) := hlogsqrt _ hy
    have hsqrt1 : Real.sqrt (2 + ((L+n : ℕ) : ℝ)) ≤ Real.sqrt 2 * Real.sqrt (1 + (L:ℝ) + n) := by
      have hle : 2 + ((L+n : ℕ) : ℝ) ≤ 2 * (1 + (L:ℝ) + n) := by
        push_cast
        nlinarith [show (0:ℝ) ≤ (L:ℝ) from Nat.cast_nonneg L, show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n]
      calc Real.sqrt (2 + ((L+n : ℕ) : ℝ)) ≤ Real.sqrt (2 * (1 + (L:ℝ) + n)) := Real.sqrt_le_sqrt hle
        _ = Real.sqrt 2 * Real.sqrt (1 + (L:ℝ) + n) := Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (1 + (L:ℝ) + n)
    have hlog2 : Real.log (2 + ((L+n : ℕ) : ℝ)) ≤ 2 * (Real.sqrt 2 * Real.sqrt (1 + (L:ℝ) + n)) := by
      have h1 : 2 * Real.sqrt (2 + ((L+n : ℕ) : ℝ)) ≤ 2 * (Real.sqrt 2 * Real.sqrt (1 + (L:ℝ) + n)) :=
        mul_le_mul_of_nonneg_left hsqrt1 (by norm_num)
      linarith
    have hmb : m (L+n) ≤ C * (2 * (Real.sqrt 2 * Real.sqrt (1 + (L:ℝ) + n))) :=
      le_trans hm2 (mul_le_mul_of_nonneg_left hlog2 hC)
    have hmono : Real.sqrt (1 + (L:ℝ) + n)/(1 + (L:ℝ) + n)^6
        ≤ (1/((1:ℝ)+(L:ℝ))^4) * (1/(Real.sqrt ((n:ℝ)+1))^3) := by
      have hypos : 0 < 1 + (L:ℝ) + n := by positivity
      have hident : Real.sqrt (1 + (L:ℝ) + n)/(1 + (L:ℝ) + n)^6
          = 1/((1 + (L:ℝ) + n)^4 * (Real.sqrt (1 + (L:ℝ) + n))^3) := by
        have hs : Real.sqrt (1 + (L:ℝ) + n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hypos)
        have hyne : (1 + (L:ℝ) + n) ≠ 0 := ne_of_gt hypos
        field_simp
        nlinarith [Real.sq_sqrt (le_of_lt hypos)]
      rw [hident]
      have h1 : (1:ℝ) + (L:ℝ) ≤ 1 + (L:ℝ) + n := by
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      have h2 : (n:ℝ) + 1 ≤ 1 + (L:ℝ) + n := by
        have : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
        linarith
      have hden_le : ((1:ℝ)+(L:ℝ))^4 * (Real.sqrt ((n:ℝ)+1))^3 ≤ (1 + (L:ℝ) + n)^4 * (Real.sqrt (1 + (L:ℝ) + n))^3 := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (by positivity) h1 4
        · exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h2) 3
        · positivity
        · positivity
      have hdenpos : 0 < ((1:ℝ)+(L:ℝ))^4 * (Real.sqrt ((n:ℝ)+1))^3 := by positivity
      rw [show (1/((1:ℝ)+(L:ℝ))^4) * (1/(Real.sqrt ((n:ℝ)+1))^3) = 1/(((1:ℝ)+(L:ℝ))^4 * (Real.sqrt ((n:ℝ)+1))^3) by field_simp]
      exact one_div_le_one_div_of_le hdenpos hden_le
    calc m (L+n)/(1+(L:ℝ)+n)^6
        ≤ (C * (2 * (Real.sqrt 2 * Real.sqrt (1+(L:ℝ)+n))))/(1+(L:ℝ)+n)^6 := by
          apply div_le_div_of_nonneg_right hmb (by positivity)
      _ = (C * (2 * Real.sqrt 2)) * (Real.sqrt (1+(L:ℝ)+n)/(1+(L:ℝ)+n)^6) := by ring
      _ ≤ (C * (2 * Real.sqrt 2)) * ((1/((1:ℝ)+(L:ℝ))^4) * (1/(Real.sqrt ((n:ℝ)+1))^3)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4) * (1/(Real.sqrt ((n:ℝ)+1))^3) := by ring
  have hf_nonneg : ∀ n : ℕ, 0 ≤ m (L+n)/(1+(L:ℝ)+n)^6 := by
    intro n
    exact div_nonneg (hm (L+n)).1 (by positivity)
  have hAu_summable : Summable (fun n : ℕ => (2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4) * (1/(Real.sqrt ((n:ℝ)+1))^3)) :=
    hu_summable.mul_left _
  have hf_summable : Summable (fun n : ℕ => m (L+n)/(1+(L:ℝ)+n)^6) :=
    Summable.of_nonneg_of_le hf_nonneg hterm hAu_summable
  have hstep1 : (∑' n : ℕ, m (L+n)/(1+(L:ℝ)+n)^6) ≤ (2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4) * (∑' n : ℕ, (1/(Real.sqrt ((n:ℝ)+1))^3)) := by
    have h := Summable.tsum_le_tsum hterm hf_summable hAu_summable
    have hmul : (∑' n : ℕ, (2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4) * (1/(Real.sqrt ((n:ℝ)+1))^3))
        = (2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4) * (∑' n : ℕ, (1/(Real.sqrt ((n:ℝ)+1))^3)) :=
      tsum_mul_left
    linarith [h, hmul]
  have hstep2 : (2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4) * (∑' n : ℕ, (1/(Real.sqrt ((n:ℝ)+1))^3)) ≤ (6*Real.sqrt 2*C + 1)/((1:ℝ)+(L:ℝ))^4 := by
    have hApos : 0 ≤ 2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4 := by positivity
    have h1 : (2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4) * (∑' n : ℕ, (1/(Real.sqrt ((n:ℝ)+1))^3)) ≤ (2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4) * 3 :=
      mul_le_mul_of_nonneg_left hu_bound hApos
    have h2 : (2*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4) * 3 = 6*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4 := by ring
    have h3 : 6*Real.sqrt 2*C/((1:ℝ)+(L:ℝ))^4 ≤ (6*Real.sqrt 2*C + 1)/((1:ℝ)+(L:ℝ))^4 := by
      apply div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith [h1, h3]
  linarith [hstep1, hstep2]
