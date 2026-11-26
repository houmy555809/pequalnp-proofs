import Mathlib

theorem PEqualNP.Outside.L_twin_primes_finite_band_sum :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let f := fun (x n j : ℝ) => x * Real.log (1+j/n); ∀ (X : ℕ) (u : ℕ → ℝ) (H : ℝ → ℝ), 1000 ≤ X → (∀ v, 1/4 ≤ |v| → H v = 0) → (w X).sum (fun n => ((w X).filter (fun m => n < m)).sum (fun m => u n*u m*H (f X n (m-n) - 2))) = ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => u n*u (n+2)*H (f X n 2 - 2)) := by
  intro w' f' X u H hX hH
  let W : Finset ℕ := (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
  have hW : w' X = W := rfl
  rw [hW]
  have hX1000 : (1000:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hXpos : (0:ℝ) < (X:ℝ) := by linarith
  have hmemW : ∀ n, n ∈ W → X < n ∧ 50*n < 51*X := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hnpos : ∀ n, n ∈ W → (0:ℝ) < (n:ℝ) := by
    intro n hn
    have h : 0 < n := by have := (hmemW n hn).1; omega
    exact_mod_cast h
  have hband_lo : ∀ n, n ∈ W → (X:ℝ) * Real.log (1 + 1/(n:ℝ)) < 1 := by
    intro n hn
    have hnp := hnpos n hn
    have hlog : Real.log (1 + 1/(n:ℝ)) ≤ 1/(n:ℝ) := by
      have hx : (0:ℝ) < 1 + 1/(n:ℝ) := by positivity
      have h := Real.log_le_sub_one_of_pos hx
      linarith
    have hstep : (X:ℝ) * (1/(n:ℝ)) < 1 := by
      rw [mul_one_div]
      exact (div_lt_one hnp).mpr (by exact_mod_cast (hmemW n hn).1)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlog (le_of_lt hXpos)) hstep
  have hband_hi : ∀ n, n ∈ W → ∀ j : ℝ, 3 ≤ j → (9:ℝ)/4 < (X:ℝ) * Real.log (1 + j/(n:ℝ)) := by
    intro n hn j hj
    have hnp := hnpos n hn
    have h50 : (50:ℝ)*(n:ℝ) < 51*(X:ℝ) := by exact_mod_cast (hmemW n hn).2
    have hfrac2 : (150:ℝ)/(51*(X:ℝ)) < (3:ℝ)/(n:ℝ) := by
      rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 51*(X:ℝ)) hnp]
      nlinarith
    have hlogmono : Real.log (1 + 150/(51*(X:ℝ))) ≤ Real.log (1 + (3:ℝ)/(n:ℝ)) := by
      apply Real.log_le_log (by positivity : (0:ℝ) < 1 + 150/(51*(X:ℝ)))
      linarith
    have hloglower : (150/(51*(X:ℝ)))/(1 + 150/(51*(X:ℝ))) ≤ Real.log (1 + 150/(51*(X:ℝ))) := by
      set y : ℝ := 150/(51*(X:ℝ)) with hydef
      have hy : 0 < y := by positivity
      have h1y : (0:ℝ) < 1 + y := by positivity
      have h1 : (0:ℝ) < 1/(1 + y) := by positivity
      have hle := Real.log_le_sub_one_of_pos h1
      have heq : Real.log (1/(1 + y)) = - Real.log (1 + y) := by rw [one_div, Real.log_inv]
      rw [heq] at hle
      have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt h1y)
      have hsimp1 : (1 + y) * (-Real.log (1 + y)) = -((1 + y) * Real.log (1 + y)) := by ring
      have hsimp2 : (1 + y) * (1/(1 + y) - 1) = -y := by field_simp; ring
      rw [hsimp1, hsimp2] at hmul
      have hkey : y ≤ (1 + y) * Real.log (1 + y) := by linarith
      rw [div_le_iff₀ h1y]
      linarith
    have hmul : (X:ℝ) * ((150/(51*(X:ℝ)))/(1 + 150/(51*(X:ℝ))))
        ≤ (X:ℝ) * Real.log (1 + (3:ℝ)/(n:ℝ)) :=
      mul_le_mul_of_nonneg_left (le_trans hloglower hlogmono) (le_of_lt hXpos)
    have heqX : (X:ℝ) * ((150/(51*(X:ℝ)))/(1 + 150/(51*(X:ℝ)))) = 150*(X:ℝ)/(51*(X:ℝ)+150) := by
      field_simp
    have hnum : (9:ℝ)/4 < 150*(X:ℝ)/(51*(X:ℝ)+150) := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 51*(X:ℝ)+150)]
      nlinarith [hX1000]
    have hlogmono2 : Real.log (1 + (3:ℝ)/(n:ℝ)) ≤ Real.log (1 + j/(n:ℝ)) := by
      apply Real.log_le_log (by positivity : (0:ℝ) < 1 + (3:ℝ)/(n:ℝ))
      have hfrac : (3:ℝ)/(n:ℝ) ≤ j/(n:ℝ) := div_le_div_of_nonneg_right hj (le_of_lt hnp)
      linarith
    have hmul2 : (X:ℝ) * Real.log (1 + (3:ℝ)/(n:ℝ)) ≤ (X:ℝ) * Real.log (1 + j/(n:ℝ)) :=
      mul_le_mul_of_nonneg_left hlogmono2 (le_of_lt hXpos)
    have h1 : (9:ℝ)/4 < (X:ℝ) * (150/(51*(X:ℝ))/(1 + 150/(51*(X:ℝ)))) := by
      rw [heqX]; exact hnum
    linarith
  have hzero : ∀ n ∈ W, ∀ m ∈ W, n < m → m ≠ n+2 → H (f' X n ((m:ℝ) - (n:ℝ)) - 2) = 0 := by
    intro n hn m hm hnm hne
    have hnp := hnpos n hn
    by_cases h1 : m = n + 1
    · apply hH
      have hcast : ((m:ℝ) - (n:ℝ)) = 1 := by rw [h1]; push_cast; ring
      have hf : f' X n ((m:ℝ) - (n:ℝ)) = (X:ℝ) * Real.log (1 + 1/(n:ℝ)) := by rw [hcast]
      have hlt : f' X n ((m:ℝ) - (n:ℝ)) - 2 < -(1/4:ℝ) := by
        rw [hf]; linarith [hband_lo n hn]
      have habs : (1/4:ℝ) ≤ |f' X n ((m:ℝ) - (n:ℝ)) - 2| := by
        rw [abs_of_neg (by linarith)]; linarith
      exact habs
    · by_cases h2 : m = n + 2
      · exact absurd h2 hne
      · apply hH
        have hj3 : (3:ℝ) ≤ (m:ℝ) - (n:ℝ) := by
          have h3 : n + 3 ≤ m := by omega
          have h3' : ((n + 3 : ℕ) : ℝ) ≤ (m:ℝ) := Nat.cast_le.mpr h3
          push_cast at h3'
          linarith
        have hf : f' X n ((m:ℝ) - (n:ℝ)) = (X:ℝ) * Real.log (1 + ((m:ℝ) - (n:ℝ))/(n:ℝ)) := rfl
        have hgt : (9:ℝ)/4 < f' X n ((m:ℝ) - (n:ℝ)) := by
          rw [hf]; exact hband_hi n hn ((m:ℝ) - (n:ℝ)) hj3
        have habs : (1/4:ℝ) ≤ |f' X n ((m:ℝ) - (n:ℝ)) - 2| := by
          rw [abs_of_pos (by linarith)]; linarith
        exact habs
  have hinner : ∀ n ∈ W, ((W.filter (fun m => n < m)).sum (fun m => u n * u m * H (f' X n ((m:ℝ) - (n:ℝ)) - 2)))
      = (if n+2 ∈ W then u n * u (n+2) * H (f' X n 2 - 2) else 0) := by
    intro n hn
    rw [Finset.sum_filter]
    have hcongr : ∀ m ∈ W, (if n < m then u n * u m * H (f' X n ((m:ℝ) - (n:ℝ)) - 2) else 0)
        = (if m = n + 2 then u n * u m * H (f' X n ((m:ℝ) - (n:ℝ)) - 2) else 0) := by
      intro m hm
      by_cases hmn : m = n + 2
      · subst hmn
        rw [if_pos rfl, if_pos (by omega : n < n + 2)]
      · by_cases hlt : n < m
        · rw [if_pos hlt, if_neg hmn]
          have hz := hzero n hn m hm hlt hmn
          rw [hz, mul_zero]
        · rw [if_neg hlt, if_neg hmn]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']
    have hcast : ((↑(n + 2) : ℝ) - (n:ℝ)) = 2 := by push_cast; ring
    rw [hcast]
  calc W.sum (fun n => ((W.filter (fun m => n < m)).sum (fun m => u n * u m * H (f' X n ((m:ℝ) - (n:ℝ)) - 2))))
      = W.sum (fun n => if n+2 ∈ W then u n * u (n+2) * H (f' X n 2 - 2) else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hinner n hn
    _ = (W.filter (fun n => n+2 ∈ W)).sum (fun n => u n * u (n+2) * H (f' X n 2 - 2)) := by
        conv_rhs => rw [Finset.sum_filter]
