import Mathlib

theorem PEqualNP.Outside.L_twin_primes_unit_class :
    ∀ d : ℕ, Odd d → Nat.Coprime 2 d ∧ ∀ p : ℕ, d ∣ p+2 ↔ ((p:ZMod d) = -(2:ZMod d)) := by

  intro d hodd
  constructor
  · exact Nat.coprime_two_left.mpr hodd
  · intro p
    rw [← ZMod.natCast_eq_zero_iff (p+2) d]
    push_cast
    exact eq_neg_iff_add_eq_zero.symm