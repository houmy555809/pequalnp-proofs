import Mathlib

theorem PEqualNP.Outside.L_twin_primes_euler_factor :
    ∀ (p : ℕ) (u : ℝ), 2 < p → u ≠ (p:ℝ) → (1-u/((p:ℝ)-1))/(1-u/p) = 1-u/((p:ℝ)*((p:ℝ)-1)*(1-u/p)) := by

  intro p u hp hu
  have hp2 : (2:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hp0 : (p:ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hp1 : (p:ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hq : 1 - u/(p:ℝ) ≠ 0 := by
    intro h
    have hu_eq : u = (p:ℝ) := by
      field_simp [hp0] at h
      linarith
    exact hu hu_eq
  field_simp
  ring