import Mathlib

theorem PEqualNP.Outside.L_twin_primes_no_wrap :
    ∀ (N X : ℕ) [NeZero N] (f : ℕ → ℝ), X+2 < N → (∀ n, X < n → f n=0) → (∑ j : ZMod N, f j.val * f (j+2).val) = (Finset.range (X+1)).sum (fun n => f n*f (n+2)) := by
  intro N X hinst f hN hf
  have h2N : 2 < N := by omega
  have hpoint : ∀ j : ZMod N, f j.val * f (j+2).val = if j.val ≤ X then f j.val * f (j.val+2) else 0 := by
    intro j
    by_cases hj : j.val ≤ X
    · rw [if_pos hj]
      have hval : (j + 2).val = j.val + 2 := by
        have h1 := ZMod.val_add j (2 : ZMod N)
        have h2 : (2 : ZMod N).val = 2 := by
          change ((2 : ℕ) : ZMod N).val = 2
          rw [ZMod.val_cast_of_lt h2N]
        rw [h2] at h1
        have hlt : j.val + 2 < N := by
          have := ZMod.val_lt j
          omega
        rw [h1, Nat.mod_eq_of_lt hlt]
      rw [hval]
    · rw [if_neg hj]
      have h0 : f j.val = 0 := hf j.val (by omega)
      rw [h0, zero_mul]
  have hsum1 : (∑ j : ZMod N, f j.val * f (j+2).val)
      = ∑ j : ZMod N, (if j.val ≤ X then f j.val * f (j.val+2) else 0) :=
    Finset.sum_congr rfl (fun j _ => hpoint j)
  rw [hsum1]
  have hsum2 : (∑ j : ZMod N, (if j.val ≤ X then f j.val * f (j.val+2) else 0))
      = ∑ n ∈ Finset.range N, (if n ≤ X then f n * f (n+2) else 0) := by
    refine Finset.sum_nbij (fun j : ZMod N => j.val) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range]
      exact ZMod.val_lt j
    · intro a ha b hb hab
      exact ZMod.val_injective N hab
    · intro b hb
      have hbN : b < N := by simpa using hb
      exact ⟨(b : ZMod N), Finset.mem_univ _, by
        show ZMod.val ((b : ℕ) : ZMod N) = b
        rw [ZMod.val_cast_of_lt hbN]⟩
    · intro j hj
      rfl
  rw [hsum2]
  have hsum3 : (∑ n ∈ Finset.range (X+1), (if n ≤ X then f n * f (n+2) else 0))
      = ∑ n ∈ Finset.range N, (if n ≤ X then f n * f (n+2) else 0) := by
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n hnN hnNot
      simp only [Finset.mem_range] at hnN hnNot
      rw [if_neg (by omega)]
  rw [← hsum3]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_range] at hn
  rw [if_pos (by omega)]
