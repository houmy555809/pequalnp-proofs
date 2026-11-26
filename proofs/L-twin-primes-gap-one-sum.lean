import Mathlib

theorem PEqualNP.Outside.L_twin_primes_gap_one_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, (Finset.range X).sum (fun n => ArithmeticFunction.vonMangoldt n*ArithmeticFunction.vonMangoldt (n+1)) ≤ C * Real.log (2+(X:ℝ))^2 := by
  refine ⟨40, by norm_num, ?_⟩
  intro X
  rcases Nat.eq_zero_or_pos X with rfl | hXpos
  · simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero]
    positivity
  set K : ℕ := Nat.log 2 X + 1 with hK
  set g : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+1) with hg
  set A : Finset ℕ := (Finset.range (K+1)).image (fun k => 2^k) with hA
  set B : Finset ℕ := (Finset.range (K+1)).image (fun k => 2^k - 1) with hB
  have hgnonneg : ∀ n, 0 ≤ g n := fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  have hsupp : ∀ n ∈ Finset.range X, g n ≠ 0 → n ∈ A ∪ B := by
    intro n hn hne
    have h1 : ArithmeticFunction.vonMangoldt n ≠ 0 := fun h => hne (by simp [hg, h])
    have h2 : ArithmeticFunction.vonMangoldt (n+1) ≠ 0 := fun h => hne (by simp [hg, h])
    have hp1 : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h1
    have hp2 : IsPrimePow (n+1) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h2
    have hnlt : n < X := Finset.mem_range.mp hn
    rcases Nat.even_or_odd n with hev | hod
    · obtain ⟨k, hklog, hkpos, hnk⟩ := (isPrimePow_nat_iff_bounded_log_minFac n).mp hp1
      have hn0 : n ≠ 0 := by rintro rfl; exact h1 (by simp)
      have h2dvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp hev)
      have hmin : n.minFac = 2 := (Nat.minFac_eq_two_iff n).mpr h2dvd
      have hn2 : n = 2^k := by rw [hnk, hmin]
      have hkX : k ≤ K := by
        have h1 : k ≤ Nat.log 2 X := le_trans hklog (Nat.log_mono_right (Nat.le_of_lt hnlt))
        simp only [hK]; omega
      refine Finset.mem_union_left B (Finset.mem_image.mpr ⟨k, ?_, hn2.symm⟩)
      simp only [Finset.mem_range]; omega
    · obtain ⟨k, hklog, hkpos, hnk⟩ := (isPrimePow_nat_iff_bounded_log_minFac (n+1)).mp hp2
      obtain ⟨mm, hmm⟩ := hod
      have hnp1 : Even (n+1) := ⟨mm+1, by omega⟩
      have h2dvd : 2 ∣ n+1 := Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp hnp1)
      have hmin : (n+1).minFac = 2 := (Nat.minFac_eq_two_iff (n+1)).mpr h2dvd
      have hn2 : n+1 = 2^k := by rw [hnk, hmin]
      have hkX : k ≤ K := by
        have h1 : k ≤ Nat.log 2 X := le_trans hklog (Nat.log_mono_right (by omega))
        simp only [hK]; omega
      refine Finset.mem_union_right A (Finset.mem_image.mpr ⟨k, ?_, ?_⟩)
      · simp only [Finset.mem_range]; omega
      · omega
  set s : Finset ℕ := (Finset.range X).filter (fun n => g n ≠ 0) with hs
  have hS : s.sum g = (Finset.range X).sum g := by
    rw [hs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : g n = 0
    · rw [if_neg (by simp [h]), h]
    · rw [if_pos h]
  have htermA : ∀ k ∈ Finset.range (K+1), g (2^k) ≤ Real.log 2 ^ 2 * ((K:ℝ)+1) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp only [hg, pow_zero, ArithmeticFunction.vonMangoldt_apply_one, zero_mul]
      have hL : (0:ℝ) ≤ Real.log 2 ^ 2 := sq_nonneg _
      have hK : (0:ℝ) ≤ (K:ℝ) + 1 := by
        have h0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
        linarith
      exact mul_nonneg hL hK
    · have hL2 : ArithmeticFunction.vonMangoldt (2^k) = Real.log 2 := by
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0)]
        rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        norm_num
      have hL1 : ArithmeticFunction.vonMangoldt (2^k+1) ≤ ((K:ℝ)+1) * Real.log 2 := by
        have h1 : ArithmeticFunction.vonMangoldt (2^k+1) ≤ Real.log (((2^k+1 : ℕ)) : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
        have hpow : ((2^k+1 : ℕ) : ℝ) ≤ (2:ℝ)^(k+1) := by
          have hnat : (2:ℕ)^k + 1 ≤ (2:ℕ)^(k+1) := by
            have h4 : (0:ℕ) < 2^k := pow_pos (by norm_num) k
            calc (2:ℕ)^k + 1 ≤ (2:ℕ)^k + (2:ℕ)^k := by omega
              _ = (2:ℕ)^(k+1) := by rw [pow_succ]; ring
          exact_mod_cast hnat
        have h2 : Real.log (((2^k+1 : ℕ)) : ℝ) ≤ ((k:ℝ)+1) * Real.log 2 := by
          have h := Real.log_le_log (by positivity : (0:ℝ) < ((2^k+1 : ℕ) : ℝ)) hpow
          rw [Real.log_pow] at h
          have hc : ((k+1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
          rw [hc] at h
          exact h
        have h3 : ((k:ℝ)+1) ≤ (K:ℝ)+1 := by
          have : k+1 ≤ K+1 := by omega
          exact_mod_cast this
        have h4 : ((k:ℝ)+1) * Real.log 2 ≤ ((K:ℝ)+1) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h3 (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
        exact le_trans h1 (le_trans h2 h4)
      calc g (2^k) = ArithmeticFunction.vonMangoldt (2^k) * ArithmeticFunction.vonMangoldt (2^k+1) := by
            simp [hg]
        _ = Real.log 2 * ArithmeticFunction.vonMangoldt (2^k+1) := by rw [hL2]
        _ ≤ Real.log 2 * (((K:ℝ)+1) * Real.log 2) :=
            mul_le_mul_of_nonneg_left hL1 (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
        _ = Real.log 2 ^ 2 * ((K:ℝ)+1) := by ring
  have htermB : ∀ k ∈ Finset.range (K+1), g (2^k - 1) ≤ Real.log 2 ^ 2 * ((K:ℝ)+1) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp only [hg, pow_zero, Nat.sub_self]
      have hzero : ArithmeticFunction.vonMangoldt 0 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
        exact not_isPrimePow_zero
      rw [hzero, zero_mul]
      have hL : (0:ℝ) ≤ Real.log 2 ^ 2 := sq_nonneg _
      have hK : (0:ℝ) ≤ (K:ℝ) + 1 := by
        have h0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
        linarith
      exact mul_nonneg hL hK
    · have hL2 : ArithmeticFunction.vonMangoldt (2^k) = Real.log 2 := by
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0)]
        rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        norm_num
      have hL1 : ArithmeticFunction.vonMangoldt (2^k-1) ≤ (K:ℝ) * Real.log 2 := by
        have h1 : ArithmeticFunction.vonMangoldt (2^k-1) ≤ Real.log (((2^k-1 : ℕ)) : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
        have hpos : (0:ℝ) < (((2^k-1 : ℕ)) : ℝ) := by
          have h4 : (0:ℕ) < 2^k - 1 := by
            have h5 : (0:ℕ) < 2^k := pow_pos (by norm_num) k
            have h6 : 1 < (2:ℕ)^k := by
              rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨j, rfl⟩
              have hp : (0:ℕ) < 2^j := pow_pos (by norm_num) j
              rw [pow_succ]
              omega
            omega
          exact_mod_cast h4
        have h2 : Real.log (((2^k-1 : ℕ)) : ℝ) ≤ (k:ℝ) * Real.log 2 := by
          have hle : (((2^k-1 : ℕ)) : ℝ) ≤ (2:ℝ)^k := by
            have h6 : (2^k - 1 : ℕ) ≤ 2^k := Nat.sub_le _ _
            exact_mod_cast h6
          have h := Real.log_le_log hpos hle
          rwa [Real.log_pow] at h
        have hkK : (k:ℝ) ≤ (K:ℝ) := by
          have : k ≤ K := by omega
          exact_mod_cast this
        have h3 : (k:ℝ) * Real.log 2 ≤ (K:ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hkK (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
        exact le_trans h1 (le_trans h2 h3)
      calc g (2^k - 1) = ArithmeticFunction.vonMangoldt (2^k-1) * ArithmeticFunction.vonMangoldt ((2^k-1)+1) := by
            simp [hg]
        _ = ArithmeticFunction.vonMangoldt (2^k-1) * Real.log 2 := by
            rw [show (2^k-1)+1 = 2^k by
              have h0 : (0:ℕ) < 2^k := pow_pos (by norm_num) k
              omega, hL2]
        _ ≤ ((K:ℝ) * Real.log 2) * Real.log 2 :=
            mul_le_mul_of_nonneg_right hL1 (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
        _ ≤ Real.log 2 ^ 2 * ((K:ℝ)+1) := by
            have hL : (0:ℝ) ≤ Real.log 2 ^ 2 := sq_nonneg _
            nlinarith [hL]
  have hA_bound : ∑ n ∈ A, g n ≤ ((K:ℝ)+1) * (Real.log 2 ^ 2 * ((K:ℝ)+1)) := by
    have h1 : ∑ n ∈ A, g n = ∑ k ∈ Finset.range (K+1), g (2^k) := by
      rw [hA, Finset.sum_image]
      intro a ha b hb hab
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hab
    rw [h1]
    calc ∑ k ∈ Finset.range (K+1), g (2^k)
        ≤ ∑ k ∈ Finset.range (K+1), (Real.log 2 ^ 2 * ((K:ℝ)+1)) :=
          Finset.sum_le_sum htermA
      _ = ((K:ℝ)+1) * (Real.log 2 ^ 2 * ((K:ℝ)+1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hB_bound : ∑ n ∈ B, g n ≤ ((K:ℝ)+1) * (Real.log 2 ^ 2 * ((K:ℝ)+1)) := by
    have h1 : ∑ n ∈ B, g n = ∑ k ∈ Finset.range (K+1), g (2^k - 1) := by
      rw [hB, Finset.sum_image]
      intro a ha b hb hab
      have h2 : (2:ℕ)^a = (2:ℕ)^b := by
        have hab' : (2:ℕ)^a - 1 = (2:ℕ)^b - 1 := hab
        have ha : 1 ≤ (2:ℕ)^a := by have := pow_pos (by norm_num : (0:ℕ) < 2) a; omega
        have hb : 1 ≤ (2:ℕ)^b := by have := pow_pos (by norm_num : (0:ℕ) < 2) b; omega
        calc (2:ℕ)^a = ((2:ℕ)^a - 1) + 1 := (Nat.sub_add_cancel ha).symm
          _ = ((2:ℕ)^b - 1) + 1 := by rw [hab']
          _ = (2:ℕ)^b := Nat.sub_add_cancel hb
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
    rw [h1]
    calc ∑ k ∈ Finset.range (K+1), g (2^k - 1)
        ≤ ∑ k ∈ Finset.range (K+1), (Real.log 2 ^ 2 * ((K:ℝ)+1)) :=
          Finset.sum_le_sum htermB
      _ = ((K:ℝ)+1) * (Real.log 2 ^ 2 * ((K:ℝ)+1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hA1 : ∑ n ∈ s.filter (fun n => n ∈ A), g n ≤ ∑ n ∈ A, g n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro i hi hinot
      exact hgnonneg i
  have hB1 : ∑ n ∈ s.filter (fun n => ¬ n ∈ A), g n ≤ ∑ n ∈ B, g n := by
    have heq : ∑ n ∈ s.filter (fun n => ¬ n ∈ A), g n
        = ∑ n ∈ (s.filter (fun n => ¬ n ∈ A)).filter (fun n => n ∈ B), g n := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro x hx
        exact (Finset.mem_filter.mp hx).1
      · intro n hn hnnot
        by_contra hne
        have hns : n ∈ s := (Finset.filter_subset _ _ hn)
        have hnA : ¬ n ∈ A := (Finset.mem_filter.mp hn).2
        have hmem : n ∈ A ∪ B := hsupp n (Finset.mem_filter.mp hns).1 (Finset.mem_filter.mp hns).2
        have : n ∈ B := by
          rcases Finset.mem_union.mp hmem with h | h
          · exact absurd h hnA
          · exact h
        exact hnnot (Finset.mem_filter.mpr ⟨hn, this⟩)
    rw [heq]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro i hi hinot
      exact hgnonneg i
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log (X:ℝ) := by
    have hle : (2:ℕ)^(Nat.log 2 X) ≤ X := Nat.pow_log_le_self 2 (by omega)
    have hle' : (2:ℝ)^(Nat.log 2 X) ≤ (X:ℝ) := by exact_mod_cast hle
    have hpos : (0:ℝ) < (2:ℝ)^(Nat.log 2 X) := by positivity
    calc (Nat.log 2 X : ℝ) * Real.log 2 = Real.log ((2:ℝ)^(Nat.log 2 X)) := by rw [Real.log_pow]
      _ ≤ Real.log (X:ℝ) := Real.log_le_log hpos hle'
  have hlogmono : Real.log (X:ℝ) ≤ Real.log (2 + (X:ℝ)) := by
    apply Real.log_le_log (by positivity)
    linarith [show (0:ℝ) ≤ (X:ℝ) from Nat.cast_nonneg X]
  have hlog2le : Real.log 2 ≤ Real.log (2 + (X:ℝ)) := by
    apply Real.log_le_log (by norm_num)
    linarith [show (0:ℝ) ≤ (X:ℝ) from Nat.cast_nonneg X]
  have hKbound : (K:ℝ) + 1 ≤ 4 * (Real.log (2 + (X:ℝ)) / Real.log 2) := by
    have hKdef : (K:ℝ) = (Nat.log 2 X : ℝ) + 1 := by simp [hK]
    have h1 : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log (2 + (X:ℝ)) := le_trans hlogX hlogmono
    have h2 : (1:ℝ) * Real.log 2 ≤ Real.log (2 + (X:ℝ)) := by linarith
    rw [hKdef, show (4:ℝ) * (Real.log (2 + (X:ℝ)) / Real.log 2) = 4 * Real.log (2 + (X:ℝ)) / Real.log 2 by ring]
    rw [le_div_iff₀ hlog2pos]
    nlinarith
  have hxl : ((K:ℝ)+1) * Real.log 2 ≤ 4 * Real.log (2 + (X:ℝ)) := by
    calc ((K:ℝ)+1) * Real.log 2 ≤ (4 * (Real.log (2 + (X:ℝ)) / Real.log 2)) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hKbound (le_of_lt hlog2pos)
      _ = 4 * Real.log (2 + (X:ℝ)) := by field_simp
  have htot : ∑ n ∈ A, g n + ∑ n ∈ B, g n ≤ 2 * (Real.log 2 ^ 2 * ((K:ℝ)+1)^2) := by
    have heq : ((K:ℝ)+1) * (Real.log 2 ^ 2 * ((K:ℝ)+1)) + ((K:ℝ)+1) * (Real.log 2 ^ 2 * ((K:ℝ)+1))
        = 2 * (Real.log 2 ^ 2 * ((K:ℝ)+1)^2) := by ring
    linarith [hA_bound, hB_bound, heq.le, heq.ge]
  have hfin : 2 * (Real.log 2 ^ 2 * ((K:ℝ)+1)^2) ≤ 40 * Real.log (2 + (X:ℝ)) ^ 2 := by
    have hsq : (((K:ℝ)+1) * Real.log 2)^2 ≤ (4 * Real.log (2 + (X:ℝ)))^2 :=
      pow_le_pow_left₀ (by positivity) hxl 2
    nlinarith [hsq, sq_nonneg (Real.log (2 + (X:ℝ)))]
  rw [← hS]
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun n => n ∈ A) g
  rw [← hsplit]
  linarith [hA1, hB1, htot, hfin]
