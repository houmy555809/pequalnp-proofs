import Mathlib

theorem PEqualNP.Outside.L_twin_primes_power_count :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 2 ≤ Y → (((Finset.range (Y+1)).filter (fun n => IsPrimePow n ∧ ¬n.Prime)).card : ℝ) ≤ C * Real.sqrt Y * Real.log (2+(Y:ℝ)) := by
  classical
  refine ⟨3, by norm_num, ?_⟩
  intro Y hY
  have hY0 : 0 < Y := by omega
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℕ := Nat.log 2 Y + 1 with hKdef
  set R : ℕ := Nat.sqrt Y + 1 with hRdef
  set S : Finset ℕ := (Finset.range (Y+1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) with hS
  have hex : ∀ n ∈ S, ∃ q : ℕ × ℕ, q.1 ∈ Finset.Icc 2 K ∧ q.2 ∈ Finset.range R ∧ n = q.2 ^ q.1 := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hnrange : n ∈ Finset.range (Y+1) := hmem.1
    have his : IsPrimePow n := hmem.2.1
    have hnprime : ¬ n.Prime := hmem.2.2
    have hnY : n ≤ Y := by
      have := Finset.mem_range.mp hnrange
      omega
    obtain ⟨k, hkle, hkpos, p, hpn, hnpow, hpprime⟩ := (isPrimePow_nat_iff_bounded_log n).mp his
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · have hk1 : k = 1 := by omega
        refine absurd ?_ hnprime
        rw [hnpow, hk1, pow_one]
        exact hpprime
      · exact hge
    have hkK : k ∈ Finset.Icc 2 K := by
      rw [Finset.mem_Icc]
      refine ⟨hk2, ?_⟩
      have h2 : Nat.log 2 n ≤ Nat.log 2 Y := Nat.log_mono_right hnY
      simp only [hKdef]
      omega
    have hpnR : p ∈ Finset.range R := by
      rw [Finset.mem_range]
      have hppow : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hpprime.pos hk2
      have hp2n : p ^ 2 ≤ n := by
        rw [hnpow]
        exact hppow
      have hpsqrt : p ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hp2n
      have hsqrtmono : Nat.sqrt n ≤ Nat.sqrt Y := Nat.sqrt_le_sqrt hnY
      simp only [hRdef]
      omega
    exact ⟨(k, p), hkK, hpnR, hnpow⟩
  let φ : ℕ → ℕ × ℕ := fun n => if hn : n ∈ S then Classical.choose (hex n hn) else (0, 0)
  have hφprop : ∀ n (hn : n ∈ S), (φ n).1 ∈ Finset.Icc 2 K ∧ (φ n).2 ∈ Finset.range R ∧ n = (φ n).2 ^ (φ n).1 := by
    intro n hn
    have hφeq : φ n = Classical.choose (hex n hn) := by
      dsimp only [φ]
      rw [dif_pos hn]
    rw [hφeq]
    exact Classical.choose_spec (hex n hn)
  have hmain : S.card ≤ (Finset.Icc 2 K).card * R := by
    have hmaps : Set.MapsTo φ (S : Set ℕ) (((Finset.Icc 2 K).product (Finset.range R)) : Set (ℕ × ℕ)) := by
      intro n hn
      exact Finset.mem_product.mpr ⟨(hφprop n hn).1, (hφprop n hn).2.1⟩
    have hinj : (S : Set ℕ).InjOn φ := by
      intro n hn m hm heq
      have hn' := (hφprop n hn).2.2
      have hm' := (hφprop m hm).2.2
      calc n = (φ n).2 ^ (φ n).1 := hn'
        _ = (φ m).2 ^ (φ m).1 := by rw [heq]
        _ = m := hm'.symm
    calc S.card ≤ ((Finset.Icc 2 K).product (Finset.range R)).card :=
          Finset.card_le_card_of_injOn φ hmaps hinj
      _ = (Finset.Icc 2 K).card * (Finset.range R).card := Finset.card_product _ _
      _ = (Finset.Icc 2 K).card * R := by rw [Finset.card_range]
  have hKcard : ((Finset.Icc 2 K).card : ℝ) = (Nat.log 2 Y : ℝ) := by
    have hnat : (Finset.Icc 2 K).card = Nat.log 2 Y := by
      rw [Nat.card_Icc]
      simp only [hKdef]
      omega
    exact_mod_cast hnat
  have hmainR : (S.card : ℝ) ≤ (Nat.log 2 Y : ℝ) * (R : ℝ) := by
    have h := hmain
    calc (S.card : ℝ) ≤ (((Finset.Icc 2 K).card * R : ℕ) : ℝ) := by exact_mod_cast h
      _ = ((Finset.Icc 2 K).card : ℝ) * (R : ℝ) := by push_cast; ring
      _ = (Nat.log 2 Y : ℝ) * (R : ℝ) := by rw [hKcard]
  have hpowY : (2:ℕ) ^ Nat.log 2 Y ≤ Y := Nat.pow_log_le_self 2 (by omega)
  have hpowY' : (2:ℝ) ^ Nat.log 2 Y ≤ (Y:ℝ) := by exact_mod_cast hpowY
  have hlogY : (Nat.log 2 Y : ℝ) * Real.log 2 ≤ Real.log (Y:ℝ) :=
    Real.le_log_of_pow_le (by norm_num) hpowY'
  have hlogYle : Real.log (Y:ℝ) ≤ Real.log (2 + (Y:ℝ)) := by
    apply Real.log_le_log (by positivity)
    linarith [(Nat.cast_nonneg Y : (0:ℝ) ≤ (Y:ℝ))]
  have hKreal : (Nat.log 2 Y : ℝ) ≤ Real.log (2 + (Y:ℝ)) / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    linarith
  have hsqrtY : (Nat.sqrt Y : ℝ) ≤ Real.sqrt (Y:ℝ) := by
    have h1 : (Nat.sqrt Y : ℝ) ^ 2 ≤ (Y:ℝ) := by
      have := Nat.sqrt_le' Y
      exact_mod_cast this
    exact Real.le_sqrt_of_sq_le h1
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt (Y:ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hRreal : (R : ℝ) ≤ 2 * Real.sqrt (Y:ℝ) := by
    simp only [hRdef]
    push_cast
    linarith
  have hcoef : (2:ℝ) / Real.log 2 ≤ 3 := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [Real.log_two_gt_d9]
  have hRnonneg : (0:ℝ) ≤ (R:ℝ) := by positivity
  have hbdnonneg : (0:ℝ) ≤ Real.log (2 + (Y:ℝ)) / Real.log 2 := by
    apply div_nonneg
    · apply Real.log_nonneg
      linarith [(Nat.cast_nonneg Y : (0:ℝ) ≤ (Y:ℝ))]
    · exact le_of_lt hlog2pos
  have hsqrtYnonneg : 0 ≤ Real.sqrt (Y:ℝ) := Real.sqrt_nonneg _
  have hlogYnonneg : 0 ≤ Real.log (2 + (Y:ℝ)) := by
    apply Real.log_nonneg
    linarith [(Nat.cast_nonneg Y : (0:ℝ) ≤ (Y:ℝ))]
  calc (S.card : ℝ) ≤ (Nat.log 2 Y : ℝ) * (R : ℝ) := hmainR
    _ ≤ (Real.log (2 + (Y:ℝ)) / Real.log 2) * (2 * Real.sqrt (Y:ℝ)) := by
        exact mul_le_mul hKreal hRreal hRnonneg hbdnonneg
    _ = (2 / Real.log 2) * (Real.sqrt (Y:ℝ) * Real.log (2 + (Y:ℝ))) := by ring
    _ ≤ 3 * (Real.sqrt (Y:ℝ) * Real.log (2 + (Y:ℝ))) := by
        apply mul_le_mul_of_nonneg_right hcoef
        positivity
    _ = 3 * Real.sqrt (Y:ℝ) * Real.log (2 + (Y:ℝ)) := by ring
