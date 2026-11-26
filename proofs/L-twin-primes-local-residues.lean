import Mathlib

private lemma lr_coprime_left (p n : ℕ) (hp : p.Prime) (hn : n < p) :
    Nat.Coprime n p ↔ n ≠ 0 := by
  constructor
  · intro hc h0
    subst h0
    rw [Nat.coprime_zero_left] at hc
    exact hp.ne_one hc
  · intro hn0
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    exact hn0 (Nat.eq_zero_of_dvd_of_lt hd hn)

private lemma lr_coprime_shift (p n : ℕ) (hp : p.Prime) (hn : n < p) :
    Nat.Coprime (n+2) p ↔ n + 2 ≠ p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  have hp2 : 2 ≤ p := hp.two_le
  have hkey : p ∣ n + 2 → n + 2 = p := by
    intro hd
    obtain ⟨k, hk⟩ := hd
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
    have hk1 : k ≤ 1 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · omega
      · exfalso
        have h2 : p * 2 ≤ p * k := Nat.mul_le_mul_left p h
        omega
    have hk2 : k = 1 := by omega
    rw [hk2, Nat.mul_one] at hk
    exact hk
  constructor
  · rintro h hd
    have h1 : p ∣ n + 2 := by rw [hd]
    exact h h1
  · intro h hd
    exact h (hkey hd)

private lemma lr_filter (p : ℕ) (hp : p.Prime) :
    (Finset.range p).filter (fun n => Nat.Coprime n p ∧ Nat.Coprime (n+2) p)
      = (Finset.range p).filter (fun n => n ≠ 0 ∧ n ≠ p - 2) := by
  apply Finset.filter_congr
  intro n hn
  have hnlt : n < p := Finset.mem_range.mp hn
  rw [lr_coprime_left p n hp hnlt, lr_coprime_shift p n hp hnlt]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 (by omega)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 (by omega)⟩

private lemma lr_card (p : ℕ) (hp : p.Prime) :
    ((Finset.range p).filter (fun n => n ≠ 0 ∧ n ≠ p - 2)).card = if p = 2 then 1 else p - 2 := by
  have hp2 : 2 ≤ p := hp.two_le
  rcases eq_or_ne p 2 with h2 | hne
  · subst h2
    decide
  · have h3 : 3 ≤ p := by omega
    have h0mem : 0 ∈ Finset.range p := by simp [hp.pos]
    have hbmem : p - 2 ∈ Finset.range p := by simp; omega
    have h0b : (0:ℕ) ≠ p - 2 := by omega
    have hb0mem : p - 2 ∈ (Finset.range p).erase 0 := by
      simp only [Finset.mem_erase]
      exact ⟨fun h => h0b h.symm, hbmem⟩
    have hfilter : (Finset.range p).filter (fun n => n ≠ 0 ∧ n ≠ p - 2)
        = ((Finset.range p).erase 0).erase (p - 2) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h3, h2, h1⟩
      · rintro ⟨h3, h2, h1⟩
        exact ⟨h1, h2, h3⟩
    rw [hfilter, Finset.card_erase_of_mem hb0mem, Finset.card_erase_of_mem h0mem]
    simp only [hne, ite_false, Finset.card_range]
    omega

theorem PEqualNP.Outside.L_twin_primes_local_residues :
    ∀ p : ℕ, p.Prime → ((Finset.range p).filter (fun n => Nat.Coprime n p ∧ Nat.Coprime (n+2) p)).card = if p=2 then 1 else p-2 := by
  intro p hp
  rw [lr_filter p hp]
  exact lr_card p hp
