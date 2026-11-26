import Mathlib

theorem PEqualNP.Outside.L_twin_primes_sifted_correlation :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); ∀ X : ℕ, 9 ≤ X → let Q := ((Finset.range (Nat.sqrt (2*X+2)+1)).filter Nat.Prime).prod id; ((w X).filter (fun n => Nat.Coprime n Q ∧ Nat.Coprime (n+2) Q)) = ((w X).filter (fun n => n.Prime ∧ (n+2).Prime)) := by
  dsimp only
  intro X hX
  set Q : ℕ := ((Finset.range (Nat.sqrt (2*X+2)+1)).filter Nat.Prime).prod id with hQ
  have hsqrt_le : Nat.sqrt (2*X+2) ≤ X := by
    by_contra h
    have h1 : X+1 ≤ Nat.sqrt (2*X+2) := by omega
    have h2 : (X+1)*(X+1) ≤ 2*X+2 := Nat.le_sqrt.mp h1
    nlinarith
  have helper : ∀ k : ℕ, 2 ≤ k → k ≤ 2*X+2 → Nat.Coprime k Q → k.Prime := by
    intro k hk2 hkY hck
    by_contra hnp
    have hk_ne1 : k ≠ 1 := by omega
    have hmin : k.minFac ≤ Nat.sqrt (2*X+2) := by
      rw [Nat.le_sqrt]
      have hdiv : k.minFac ∣ k := Nat.minFac_dvd k
      have hfac : k.minFac * (k / k.minFac) = k := Nat.mul_div_cancel' hdiv
      have hge2 : 2 ≤ k / k.minFac := by
        rcases Nat.lt_or_ge (k / k.minFac) 2 with h | h
        · have h0 : k / k.minFac ≠ 0 := by
            intro h0
            rw [h0] at hfac
            simp at hfac
            omega
          have h1 : 1 ≤ k / k.minFac := Nat.one_le_iff_ne_zero.mpr h0
          have h3 : k / k.minFac = 1 := by omega
          rw [h3] at hfac
          have hkminfac : k = k.minFac := by omega
          rw [hkminfac] at hnp
          exact absurd (Nat.minFac_prime hk_ne1) hnp
        · exact h
      have hdvd : k / k.minFac ∣ k := ⟨k.minFac, by rw [mul_comm]; exact hfac.symm⟩
      have hle : k.minFac ≤ k / k.minFac := Nat.minFac_le_of_dvd hge2 hdvd
      calc k.minFac * k.minFac ≤ k.minFac * (k / k.minFac) := Nat.mul_le_mul_left _ hle
        _ = k := hfac
        _ ≤ 2*X+2 := hkY
    have hmem : k.minFac ∈ (Finset.range (Nat.sqrt (2*X+2)+1)).filter Nat.Prime := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by omega), Nat.minFac_prime hk_ne1⟩
    have hdvdQ : k.minFac ∣ Q := by
      rw [hQ]
      exact Finset.dvd_prod_of_mem id hmem
    have hdvdn : k.minFac ∣ k := Nat.minFac_dvd k
    have hgcd : k.minFac ∣ Nat.gcd k Q := Nat.dvd_gcd hdvdn hdvdQ
    rw [Nat.coprime_iff_gcd_eq_one.mp hck] at hgcd
    have h1 : k.minFac = 1 := Nat.dvd_one.mp hgcd
    have h2 : k.minFac.Prime := Nat.minFac_prime hk_ne1
    rw [h1] at h2
    exact Nat.not_prime_one h2
  ext n
  constructor
  · intro hn
    obtain ⟨hnw, hc1, hc2⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnR, hXn, h50⟩ := Finset.mem_filter.mp hnw
    have hnlt : n < 2*X+1 := Finset.mem_range.mp hnR
    have hn2 : 2 ≤ n := by omega
    have hnY : n ≤ 2*X+2 := by omega
    have hn2Y : n+2 ≤ 2*X+2 := by omega
    exact Finset.mem_filter.mpr ⟨hnw, helper n hn2 hnY hc1, helper (n+2) (by omega) hn2Y hc2⟩
  · intro hn
    obtain ⟨hnw, hpn, hpn2⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnR, hXn, h50⟩ := Finset.mem_filter.mp hnw
    have hnlt : n < 2*X+1 := Finset.mem_range.mp hnR
    refine Finset.mem_filter.mpr ⟨hnw, ?_, ?_⟩
    · rw [hQ, Nat.coprime_prod_right_iff]
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpR, hpp⟩ := hp
      have hp_le : p ≤ Nat.sqrt (2*X+2) := by have := Finset.mem_range.mp hpR; omega
      have hpX : p ≤ X := le_trans hp_le hsqrt_le
      exact (Nat.coprime_primes hpn hpp).mpr (by omega)
    · rw [hQ, Nat.coprime_prod_right_iff]
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpR, hpp⟩ := hp
      have hp_le : p ≤ Nat.sqrt (2*X+2) := by have := Finset.mem_range.mp hpR; omega
      have hpX : p ≤ X := le_trans hp_le hsqrt_le
      exact (Nat.coprime_primes hpn2 hpp).mpr (by omega)
