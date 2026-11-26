import Mathlib

theorem PEqualNP.Outside.L_twin_primes_divisor_bridge :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let primes := fun X => (w X).filter Nat.Prime; let c := fun (d : ℕ) => -(ArithmeticFunction.moebius d : ℝ)*Real.log d; let short := fun (X D : ℕ) => (primes X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => d ≤ D)).sum c))/(X:ℝ); let D := fun (X : ℕ) => Nat.floor ((X:ℝ)^(1/3:ℝ)); let f := fun (p : ℕ) => if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1; let twinC := ∏' p : ℕ, f p; Filter.Tendsto (fun X : ℕ => short X (D X)) Filter.atTop (nhds (2*twinC/50))) → (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let primes := fun X => (w X).filter Nat.Prime; let c := fun (d : ℕ) => -(ArithmeticFunction.moebius d : ℝ)*Real.log d; let long := fun (X D : ℕ) => (primes X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => D < d)).sum c))/(X:ℝ); let D := fun (X : ℕ) => Nat.floor ((X:ℝ)^(1/3:ℝ)); let f := fun (p : ℕ) => if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1; let twinC := ∏' p : ℕ, f p; ∃ κ : ℝ, 0 < κ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ -2*twinC/50 + κ < long X (D X)) → (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let E := fun (X : ℕ) => ((w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → E X ≤ C * e X) → (∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ (p+2).Prime) := by
  intro h1 h2 h3 B
  dsimp only at h1 h2 h3
  let W : ℕ → Finset ℕ := fun X => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
  let Pf : ℕ → Finset ℕ := fun X => (W X).filter Nat.Prime
  let cf : ℕ → ℝ := fun d => -(ArithmeticFunction.moebius d : ℝ)*Real.log d
  let Df : ℕ → ℕ := fun X => Nat.floor ((X:ℝ)^(1/3:ℝ))
  let Short : ℕ → ℕ → ℝ := fun X D => (Pf X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => d ≤ D)).sum cf))/(X:ℝ)
  let Long : ℕ → ℕ → ℝ := fun X D => (Pf X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => D < d)).sum cf))/(X:ℝ)
  let vv : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)
  let EE : ℕ → ℝ := fun X => ((W X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum vv / (X:ℝ)
  let Mf : ℕ → ℝ := fun X => (W X).sum vv / (X:ℝ)
  let ee : ℕ → ℝ := fun X => Real.log (2+(X:ℝ))^3 / Real.sqrt X
  let fT : ℕ → ℝ := fun (p : ℕ) => if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1
  let twinC : ℝ := ∏' p : ℕ, fT p
  have h1' : Filter.Tendsto (fun X : ℕ => Short X (Df X)) Filter.atTop (nhds (2*twinC/50)) := h1
  have h2' : ∃ κ : ℝ, 0 < κ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ -2*twinC/50 + κ < Long X (Df X) := h2
  have h3' : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → EE X ≤ C * ee X := h3
  obtain ⟨κ, hκpos, hκ⟩ := h2'
  obtain ⟨C, hCpos, hC⟩ := h3'
  have hsplit : ∀ X D : ℕ, Short X D + Long X D = (Pf X).sum (fun p => Real.log p * ArithmeticFunction.vonMangoldt (p+2))/(X:ℝ) := by
    intro X D
    have hmain : ∀ n : ℕ, (∑ d ∈ n.divisors, cf d) = ArithmeticFunction.vonMangoldt n := by
      intro n
      have h' : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d:ℝ))
          = -ArithmeticFunction.vonMangoldt n := by
        simpa using ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
      calc (∑ d ∈ n.divisors, cf d)
          = -(∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d:ℝ)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro d hd
            simp only [cf, neg_mul]
        _ = -(-ArithmeticFunction.vonMangoldt n) := by rw [h']
        _ = ArithmeticFunction.vonMangoldt n := by simp
    simp only [Short, Long]
    rw [← add_div]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← mul_add]
    congr 1
    have hfilter : (p+2).divisors.filter (fun d => D < d)
        = (p+2).divisors.filter (fun d => ¬ d ≤ D) := by
      apply Finset.filter_congr
      intro d hd
      simp only [Nat.not_le]
    rw [hfilter, Finset.sum_filter_add_sum_filter_not (s := (p+2).divisors) (p := fun d => d ≤ D) (f := cf)]
    exact hmain (p+2)
  have hPrimeSum : ∀ X : ℕ, (Pf X).sum vv = (Pf X).sum (fun p => Real.log p * ArithmeticFunction.vonMangoldt (p+2)) := by
    intro X
    apply Finset.sum_congr rfl
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    simp only [vv, ArithmeticFunction.vonMangoldt_apply_prime hpp]
  have hNonNeg : ∀ X : ℕ, 0 ≤ ((W X).filter (fun n => ¬ n.Prime)).sum vv := by
    intro X
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  have hMdecomp : ∀ X : ℕ, Mf X = Short X (Df X) + Long X (Df X) + ((W X).filter (fun n => ¬ n.Prime)).sum vv / (X:ℝ) := by
    intro X
    have hpart := Finset.sum_filter_add_sum_filter_not (s := W X) (p := Nat.Prime) (f := vv)
    have hsumW : (W X).sum vv = (Pf X).sum (fun p => Real.log p * ArithmeticFunction.vonMangoldt (p+2)) + ((W X).filter (fun n => ¬ n.Prime)).sum vv := by
      rw [← hpart, hPrimeSum X]
    simp only [Mf]
    rw [hsumW, add_div, ← hsplit X (Df X)]
  have hMge : ∀ X : ℕ, 0 < X → Short X (Df X) + Long X (Df X) ≤ Mf X := by
    intro X hX
    rw [hMdecomp X]
    have hb : 0 ≤ ((W X).filter (fun n => ¬ n.Prime)).sum vv / (X:ℝ) :=
      div_nonneg (hNonNeg X) (by positivity)
    linarith
  have hTwin : ∀ X : ℕ, 0 < X → Mf X - EE X = ((W X).filter (fun n => n.Prime ∧ (n+2).Prime)).sum vv / (X:ℝ) := by
    intro X hX
    have hpart := Finset.sum_filter_add_sum_filter_not (s := W X) (p := fun n => n.Prime ∧ (n+2).Prime) (f := vv)
    have hsumW : (W X).sum vv = ((W X).filter (fun n => n.Prime ∧ (n+2).Prime)).sum vv + ((W X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum vv := by
      rw [← hpart]
    simp only [Mf, EE]
    rw [hsumW, add_div]
    ring
  have hee_pos : ∀ X : ℕ, 2 ≤ X → 0 < ee X := by
    intro X hX
    have hX0 : (0:ℝ) < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
    have h2X : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
    apply div_pos (pow_pos ?_ 3) (Real.sqrt_pos.mpr hX0)
    exact Real.log_pos (by linarith)
  have he_tend : Filter.Tendsto (fun X : ℕ => Real.log (2+(X:ℝ))^(3:ℝ) / (2+(X:ℝ))^((1:ℝ)/2)) Filter.atTop (nhds 0) := by
    have hlo : (fun x : ℝ => Real.log x ^ (3:ℝ)) =o[Filter.atTop] (fun x : ℝ => x ^ ((1:ℝ)/2)) :=
      isLittleO_log_rpow_rpow_atTop (3:ℝ) (by norm_num)
    have hcomp : (fun X : ℕ => Real.log (2+(X:ℝ))^(3:ℝ)) =o[Filter.atTop] (fun X : ℕ => (2+(X:ℝ))^((1:ℝ)/2)) :=
      hlo.comp_tendsto (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop)
    exact hcomp.tendsto_div_nhds_zero
  have hbound : ∀ X : ℕ, 2 ≤ X → Real.log (2+(X:ℝ))^(3:ℝ) / (2+(X:ℝ))^((1:ℝ)/2) < κ/(4*(C+1)*Real.sqrt 2) → (C+1) * ee X < κ/4 := by
    intro X hX2 hX1
    have hX0 : (0:ℝ) < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
    have h2X : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX2
    have hsqrtpos : 0 < Real.sqrt (X:ℝ) := Real.sqrt_pos.mpr hX0
    have hlogpos : 0 < Real.log (2 + (X:ℝ)) := Real.log_pos (by linarith)
    have hden2 : 0 < Real.sqrt (2 + (X:ℝ)) := Real.sqrt_pos.mpr (by linarith)
    have hlog3 : Real.log (2 + (X:ℝ))^3 = Real.log (2 + (X:ℝ))^(3:ℝ) := (Real.rpow_natCast _ 3).symm
    have hratio : Real.sqrt (2 + (X:ℝ)) ≤ Real.sqrt 2 * Real.sqrt (X:ℝ) := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      apply Real.sqrt_le_sqrt
      nlinarith
    have hee_le : ee X ≤ (Real.log (2+(X:ℝ))^(3:ℝ) / Real.sqrt (2+(X:ℝ))) * Real.sqrt 2 := by
      simp only [ee]
      rw [hlog3]
      have hLnn : 0 ≤ Real.log (2+(X:ℝ))^(3:ℝ) := Real.rpow_nonneg (le_of_lt hlogpos) 3
      have key : Real.log (2+(X:ℝ))^(3:ℝ) / Real.sqrt (X:ℝ)
          = (Real.log (2+(X:ℝ))^(3:ℝ) / Real.sqrt (2+(X:ℝ))) * (Real.sqrt (2+(X:ℝ)) / Real.sqrt (X:ℝ)) := by
        field_simp
      rw [key]
      apply mul_le_mul_of_nonneg_left ?_ (div_nonneg hLnn (le_of_lt hden2))
      rw [div_le_iff₀ hsqrtpos]
      exact hratio
    have hC1 : 0 < C + 1 := by linarith
    have hsqrt2pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    calc (C+1) * ee X
        ≤ (C+1) * ((Real.log (2+(X:ℝ))^(3:ℝ) / Real.sqrt (2+(X:ℝ))) * Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hee_le (le_of_lt hC1)
      _ = ((C+1) * Real.sqrt 2) * (Real.log (2+(X:ℝ))^(3:ℝ) / Real.sqrt (2+(X:ℝ))) := by ring
      _ = ((C+1) * Real.sqrt 2) * (Real.log (2+(X:ℝ))^(3:ℝ) / (2+(X:ℝ))^((1:ℝ)/2)) := by
          rw [show Real.sqrt (2 + (X:ℝ)) = (2 + (X:ℝ))^((1:ℝ)/2) from Real.sqrt_eq_rpow _]
      _ < ((C+1) * Real.sqrt 2) * (κ/(4*(C+1)*Real.sqrt 2)) := by
          apply mul_lt_mul_of_pos_left hX1 (by positivity)
      _ = κ/4 := by
          field_simp
  have hev : ∃ N : ℕ, ∀ X ≥ N, (C+1) * ee X < κ/4 := by
    have hδpos : 0 < κ/(4*(C+1)*Real.sqrt 2) := by
      have hsqrt2pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      apply div_pos hκpos
      have hC1 : 0 < C + 1 := by linarith
      have h4 : (0:ℝ) < 4 := by norm_num
      exact mul_pos (mul_pos h4 hC1) hsqrt2pos
    have hev1 : ∀ᶠ X : ℕ in Filter.atTop, Real.log (2+(X:ℝ))^(3:ℝ) / (2+(X:ℝ))^((1:ℝ)/2) < κ/(4*(C+1)*Real.sqrt 2) :=
      he_tend.eventually (Iio_mem_nhds hδpos)
    have hev2 : ∀ᶠ X : ℕ in Filter.atTop, 2 ≤ X := Filter.eventually_atTop.2 ⟨2, fun b hb => hb⟩
    have hevall : ∀ᶠ X : ℕ in Filter.atTop, (C+1) * ee X < κ/4 := by
      filter_upwards [hev1, hev2] with X hX1 hX2
      exact hbound X hX2 hX1
    exact Filter.eventually_atTop.mp hevall
  have hshort_ev : ∃ N : ℕ, ∀ X ≥ N, 2*twinC/50 - κ/4 < Short X (Df X) := by
    have hmem : Set.Ioi (2*twinC/50 - κ/4) ∈ nhds (2*twinC/50) := Ioi_mem_nhds (by linarith)
    exact Filter.eventually_atTop.mp (h1'.eventually hmem)
  obtain ⟨N1, hN1⟩ := hshort_ev
  obtain ⟨N2, hN2⟩ := hev
  obtain ⟨X, hXB, hXlong⟩ := hκ (max (max B 2) (max N1 N2))
  have hXN1 : N1 ≤ X := by omega
  have hXN2 : N2 ≤ X := by omega
  have hX2 : 2 ≤ X := by omega
  have hX0 : 0 < X := by omega
  have hX0R : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX0
  have hshortX := hN1 X hXN1
  have heX := hN2 X hXN2
  have hEX := hC X hX2
  have hP : 3*κ/4 < Short X (Df X) + Long X (Df X) := by linarith
  have hM : 3*κ/4 < Mf X := lt_of_lt_of_le hP (hMge X hX0)
  have hMX : (C+1) * ee X < Mf X := by linarith
  have hTdiv : ee X < ((W X).filter (fun n => n.Prime ∧ (n+2).Prime)).sum vv / (X:ℝ) := by
    rw [← hTwin X hX0]
    have h2 : (C+1) * ee X - C * ee X = ee X := by ring
    linarith [hMX, hEX, h2]
  have hTpos : 0 < ((W X).filter (fun n => n.Prime ∧ (n+2).Prime)).sum vv := by
    have hpos : 0 < ((W X).filter (fun n => n.Prime ∧ (n+2).Prime)).sum vv / (X:ℝ) :=
      lt_trans (hee_pos X hX2) hTdiv
    have hmul := mul_pos hpos hX0R
    have hcalc : ((W X).filter (fun n => n.Prime ∧ (n+2).Prime)).sum vv / (X:ℝ) * (X:ℝ) = ((W X).filter (fun n => n.Prime ∧ (n+2).Prime)).sum vv := by
      field_simp
    rwa [hcalc] at hmul
  have hne : ((W X).filter (fun n => n.Prime ∧ (n+2).Prime)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hTpos
    simp at hTpos
  obtain ⟨n, hn⟩ := hne
  have hmemW : n ∈ W X := (Finset.mem_filter.mp hn).1
  have hmem : n ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X) := hmemW
  have hlt : X < n := (Finset.mem_filter.mp hmem).2.1
  have hBlt : B < n := by omega
  exact ⟨n, hBlt, (Finset.mem_filter.mp hn).2.1, (Finset.mem_filter.mp hn).2.2⟩
