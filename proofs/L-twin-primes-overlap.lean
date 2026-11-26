import Mathlib

theorem PEqualNP.Outside.L_twin_primes_overlap :
    ∀ n m H : ℕ, n ≤ m → ((Finset.Ico n (n+H)) ∩ (Finset.Ico m (m+H))).card = H-(m-n) := by

  intro n m H hnm
  have hset : Finset.Ico n (n+H) ∩ Finset.Ico m (m+H) = Finset.Ico m (n+H) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_Ico]
    omega
  rw [hset, Nat.card_Ico]
  omega