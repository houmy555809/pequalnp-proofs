import Mathlib

theorem PEqualNP.Outside.L_twin_primes_window_extraction :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let E := fun (X : ℕ) => ((w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v / (X : ℝ); ∀ X : ℕ, 0 < X → E X < M X → ∃ n ∈ w X, n.Prime ∧ (n+2).Prime := by
  intro w' v' M' E' X hX h
  simp only [M', E'] at h
  have hXr : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
  have hAB : ((w' X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v' < (w' X).sum v' :=
    (div_lt_div_iff_of_pos_right hXr).mp h
  have hsplit : ((w' X).filter (fun n => n.Prime ∧ (n+2).Prime)).sum v'
      + ((w' X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v' = (w' X).sum v' :=
    Finset.sum_filter_add_sum_filter_not (s := w' X) (p := fun n => n.Prime ∧ (n+2).Prime) v'
  have hTpos : 0 < ((w' X).filter (fun n => n.Prime ∧ (n+2).Prime)).sum v' := by linarith
  have hne : ((w' X).filter (fun n => n.Prime ∧ (n+2).Prime)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hTpos
    simp at hTpos
  obtain ⟨n, hn⟩ := hne
  exact ⟨n, (Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2.1, (Finset.mem_filter.mp hn).2.2⟩
