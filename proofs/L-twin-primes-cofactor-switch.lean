import Mathlib

theorem PEqualNP.Outside.L_twin_primes_cofactor_switch :
    ∀ p d D : ℕ, 0 < d → d ∣ p+2 → (D < d ↔ D*((p+2)/d) < p+2) ∧ ((p+2)/d)*d = p+2 := by

  intro p d D hd hdiv
  set m := (p+2)/d with hmdef
  have hm : m * d = p+2 := by rw [hmdef]; exact Nat.div_mul_cancel hdiv
  have hp2 : 0 < p + 2 := by omega
  have hle : d ≤ p + 2 := Nat.le_of_dvd hp2 hdiv
  have hpos : 0 < m := by rw [hmdef]; exact Nat.div_pos hle hd
  have hiff : D * m < p + 2 ↔ D < d := by
    rw [← hm, mul_comm m d]
    exact Nat.mul_lt_mul_right hpos
  exact ⟨hiff.symm, hm⟩