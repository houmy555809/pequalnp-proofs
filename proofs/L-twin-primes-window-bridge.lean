import Mathlib

theorem PEqualNP.Outside.L_twin_primes_window_bridge :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let E := fun (X : ℕ) => ((w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → E X ≤ C * e X) → (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) → (∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ (p+2).Prime) := by

  intro hC hS B
  set w : ℕ → Finset ℕ := fun X => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X) with hw
  set v : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) with hv
  set E : ℕ → ℝ := fun X => ((w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v / (X:ℝ) with hE
  set e : ℕ → ℝ := fun X => Real.log (2+(X:ℝ))^3 / Real.sqrt X with he
  set M : ℕ → ℝ := fun X => (w X).sum v / (X:ℝ) with hM
  change (∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → E X ≤ C * e X) at hC
  change (∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) at hS
  obtain ⟨C, hCpos, hCbound⟩ := hC
  obtain ⟨X, hBX, hXsurp⟩ := hS (C+1) (max B 2)
  have hX2 : 2 ≤ X := le_of_lt (lt_of_le_of_lt (le_max_right B 2) hBX)
  have hBX' : B < X := lt_of_le_of_lt (le_max_left B 2) hBX
  have hpos_e : 0 < e X := by
    rw [he]
    apply div_pos
    · have h1 : (1:ℝ) < 2 + (X:ℝ) := by
        have hx0 : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
        linarith
      exact pow_pos (Real.log_pos h1) 3
    · have hXpos : (0:ℝ) < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
      exact Real.sqrt_pos.2 hXpos
  have hv_nonneg : ∀ n, 0 ≤ v n := by
    intro n
    rw [hv]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  by_cases hne : ((w X).filter (fun n => n.Prime ∧ (n+2).Prime)).Nonempty
  · obtain ⟨n, hn⟩ := hne
    obtain ⟨hnw, hnp⟩ := Finset.mem_filter.mp hn
    rw [hw] at hnw
    have hnX : X < n := (Finset.mem_filter.mp hnw).2.1
    exact ⟨n, by omega, hnp.1, hnp.2⟩
  · exfalso
    have hempty : ((w X).filter (fun n => n.Prime ∧ (n+2).Prime)) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hsum : (w X).sum v = ((w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v := by
      have h := Finset.sum_filter_add_sum_filter_not (s := w X)
        (p := fun n => n.Prime ∧ (n+2).Prime) (f := v)
      rw [hempty] at h
      simp only [Finset.sum_empty, zero_add] at h
      exact h.symm
    have hM_eq_E : M X = E X := by
      simp only [hM, hE]
      rw [hsum]
    rw [hM_eq_E] at hXsurp
    have hEbound := hCbound X hX2
    nlinarith [hXsurp, hEbound, hpos_e]