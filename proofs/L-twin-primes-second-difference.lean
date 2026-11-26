import Mathlib

theorem PEqualNP.Outside.L_twin_primes_second_difference :
    let v := fun (X n : ℕ) => if n ≤ X then ArithmeticFunction.vonMangoldt n else 0; let F := fun (X H : ℕ) => (Finset.range (X+H+1)).sum (fun t => ((Finset.range H).sum (fun j => if j ≤ t then v X (t-j) else 0))^2); let C := fun (X h : ℕ) => (Finset.range (X+1)).sum (fun n => v X n * v X (n+h)); ∀ X : ℕ, F X 3-2*F X 2+F X 1 = 2*C X 2 := by
  intro v' F' C' X
  let a : ℕ → ℝ := fun n => v' X n
  have ha0 : a 0 = 0 := by simp [a, v']
  have haX : ∀ n, X < n → a n = 0 := by
    intro n hn
    simp [a, v', show ¬ n ≤ X by omega]
  have hguard : ∀ t j : ℕ, (if j ≤ t then a (t - j) else 0) = a (t - j) := by
    intro t j
    by_cases h : j ≤ t
    · simp [h]
    · have hz : t - j = 0 := by omega
      simp [h, hz, a, v']
  let S : ℕ → ℕ → ℝ := fun H t => ∑ j ∈ Finset.range H, a (t - j)
  have hF : ∀ H, F' X H = ∑ t ∈ Finset.range (X+H+1), (S H t)^2 := by
    intro H
    simp only [F']
    apply Finset.sum_congr rfl
    intro t ht
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact hguard t j
  have hS : ∀ H t, X + H < t → S H t = 0 := by
    intro H t ht
    apply Finset.sum_eq_zero
    intro j hj
    have hjlt : j < H := Finset.mem_range.mp hj
    exact haX (t - j) (by omega)
  have hF1 : F' X 1 = ∑ t ∈ Finset.range (X+4), (S 1 t)^2 := by
    rw [hF 1, show X + 1 + 1 = X + 2 by omega]
    refine Finset.sum_subset ?_ ?_
    · intro t ht; simp only [Finset.mem_range] at ht ⊢; omega
    · intro t ht4 hnot
      simp only [Finset.mem_range] at ht4 hnot
      rw [hS 1 t (by omega)]
      ring
  have hF2 : F' X 2 = ∑ t ∈ Finset.range (X+4), (S 2 t)^2 := by
    rw [hF 2, show X + 2 + 1 = X + 3 by omega]
    refine Finset.sum_subset ?_ ?_
    · intro t ht; simp only [Finset.mem_range] at ht ⊢; omega
    · intro t ht4 hnot
      simp only [Finset.mem_range] at ht4 hnot
      rw [hS 2 t (by omega)]
      ring
  have hF3 : F' X 3 = ∑ t ∈ Finset.range (X+4), (S 3 t)^2 := by
    rw [hF 3, show X + 3 + 1 = X + 4 by omega]
  have hpt : ∀ t, (S 3 t)^2 - 2*(S 2 t)^2 + (S 1 t)^2
      = 2*(a t * a (t-2)) - 2*(a t * a (t-1)) + 2*(a (t-1) * a (t-2)) + (a (t-2))^2 - (a (t-1))^2 := by
    intro t
    simp only [S, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero, Nat.sub_zero]
    ring
  have hC : C' X 2 = ∑ n ∈ Finset.range (X+1), a n * a (n+2) := by
    simp only [C', a]
  have e1 : (∑ t ∈ Finset.range (X+4), a t * a (t-2)) = ∑ n ∈ Finset.range (X+1), a n * a (n+2) := by
    rw [show X + 4 = 2 + (X + 2) by omega]
    rw [Finset.sum_range_add (fun t => a t * a (t - 2)) 2 (X + 2)]
    have h0 : (∑ t ∈ Finset.range 2, a t * a (t - 2)) = 0 := by
      simp [Finset.sum_range_succ, a, v']
    rw [h0, zero_add]
    rw [show X + 2 = (X + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    have hz1 : a (X + 3) = 0 := haX (X+3) (by omega)
    rw [show 2 + (X + 1) = X + 3 by omega, show (X + 3) - 2 = X + 1 by omega]
    rw [hz1, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (2 + n) - 2 = n by omega, show 2 + n = n + 2 by omega]
    ring
  have e2 : (∑ t ∈ Finset.range (X+4), a t * a (t-1)) = ∑ n ∈ Finset.range (X+1), a n * a (n+1) := by
    rw [show X + 4 = 1 + (X + 3) by omega]
    rw [Finset.sum_range_add (fun t => a t * a (t - 1)) 1 (X + 3)]
    have h0 : (∑ t ∈ Finset.range 1, a t * a (t - 1)) = 0 := by
      simp [a, v']
    rw [h0, zero_add]
    rw [show X + 3 = (X + 2) + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [show X + 2 = (X + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    have hz1 : a (X + 2) = 0 := haX (X+2) (by omega)
    have hz2 : a (X + 3) = 0 := haX (X+3) (by omega)
    rw [show 1 + (X + 1) = X + 2 by omega, show 1 + (X + 2) = X + 3 by omega]
    rw [show (X + 2) - 1 = X + 1 by omega, show (X + 3) - 1 = X + 2 by omega]
    rw [hz1, hz2]
    simp
    apply Finset.sum_congr rfl
    intro n hn
    rw [show 1 + n = n + 1 by omega]
    ring
  have e3 : (∑ t ∈ Finset.range (X+4), a (t-1) * a (t-2)) = ∑ n ∈ Finset.range (X+1), a n * a (n+1) := by
    rw [show X + 4 = 2 + (X + 2) by omega]
    rw [Finset.sum_range_add (fun t => a (t - 1) * a (t - 2)) 2 (X + 2)]
    have h0 : (∑ t ∈ Finset.range 2, a (t - 1) * a (t - 2)) = 0 := by
      simp [Finset.sum_range_succ, a, v']
    rw [h0, zero_add]
    rw [show X + 2 = (X + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    have hz1 : a (X + 2) = 0 := haX (X+2) (by omega)
    rw [show 2 + (X + 1) = X + 3 by omega]
    rw [show (X + 3) - 1 = X + 2 by omega, show (X + 3) - 2 = X + 1 by omega]
    rw [hz1, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (2 + n) - 1 = n + 1 by omega]
    rw [show (2 + n) - 2 = n by omega]
    ring
  have e4 : (∑ t ∈ Finset.range (X+4), (a (t-2))^2) = ∑ n ∈ Finset.range (X+1), (a n)^2 := by
    rw [show X + 4 = 2 + (X + 2) by omega]
    rw [Finset.sum_range_add (fun t => (a (t - 2))^2) 2 (X + 2)]
    have h0 : (∑ t ∈ Finset.range 2, (a (t - 2))^2) = 0 := by
      simp [Finset.sum_range_succ, a, v']
    rw [h0, zero_add]
    rw [show X + 2 = (X + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    have hz1 : a (X + 1) = 0 := haX (X+1) (by omega)
    rw [show 2 + (X + 1) = X + 3 by omega, show (X + 3) - 2 = X + 1 by omega]
    rw [hz1]
    simp
  have e5 : (∑ t ∈ Finset.range (X+4), (a (t-1))^2) = ∑ n ∈ Finset.range (X+1), (a n)^2 := by
    rw [show X + 4 = 1 + (X + 3) by omega]
    rw [Finset.sum_range_add (fun t => (a (t - 1))^2) 1 (X + 3)]
    have h0 : (∑ t ∈ Finset.range 1, (a (t - 1))^2) = 0 := by
      simp [a, v']
    rw [h0, zero_add]
    rw [show X + 3 = (X + 2) + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [show X + 2 = (X + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    have hz1 : a (X + 1) = 0 := haX (X+1) (by omega)
    have hz2 : a (X + 2) = 0 := haX (X+2) (by omega)
    rw [show 1 + (X + 1) = X + 2 by omega, show 1 + (X + 2) = X + 3 by omega]
    rw [show (X + 2) - 1 = X + 1 by omega, show (X + 3) - 1 = X + 2 by omega]
    rw [hz1, hz2]
    simp
  have hsplit : (∑ t ∈ Finset.range (X+4), (2*(a t * a (t-2)) - 2*(a t * a (t-1)) + 2*(a (t-1) * a (t-2)) + (a (t-2))^2 - (a (t-1))^2))
      = 2*(∑ t ∈ Finset.range (X+4), a t * a (t-2)) - 2*(∑ t ∈ Finset.range (X+4), a t * a (t-1)) + 2*(∑ t ∈ Finset.range (X+4), a (t-1) * a (t-2)) + (∑ t ∈ Finset.range (X+4), (a (t-2))^2) - (∑ t ∈ Finset.range (X+4), (a (t-1))^2) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsum : (∑ t ∈ Finset.range (X+4), ((S 3 t)^2 - 2*(S 2 t)^2 + (S 1 t)^2))
      = 2 * (∑ n ∈ Finset.range (X+1), a n * a (n+2)) := by
    rw [Finset.sum_congr rfl (fun t ht => hpt t)]
    rw [hsplit, e1, e2, e3, e4, e5]
    ring
  calc F' X 3 - 2*F' X 2 + F' X 1
      = (∑ t ∈ Finset.range (X+4), (S 3 t)^2) - 2*(∑ t ∈ Finset.range (X+4), (S 2 t)^2) + (∑ t ∈ Finset.range (X+4), (S 1 t)^2) := by
        rw [hF3, hF2, hF1]
    _ = ∑ t ∈ Finset.range (X+4), ((S 3 t)^2 - 2*(S 2 t)^2 + (S 1 t)^2) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    _ = 2 * (∑ n ∈ Finset.range (X+1), a n * a (n+2)) := hsum
    _ = 2 * C' X 2 := by rw [hC]
