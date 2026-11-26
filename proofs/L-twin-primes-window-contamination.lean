import Mathlib

private lemma power_count_bound (Y : ℕ) (hY : 2 ≤ Y) :
    (((Finset.range (Y+1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℝ)
      ≤ 3 * Real.sqrt Y * Real.log (2+(Y:ℝ)) := by
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

theorem PEqualNP.Outside.L_twin_primes_window_contamination :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let E := fun (X : ℕ) => ((w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → E X ≤ C * e X := by
  refine ⟨100, by norm_num, ?_⟩
  intro X hX
  let w : ℕ → Finset ℕ := fun X => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
  let v : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)
  let L : ℝ := Real.log (2 + (X:ℝ))
  let S : Finset ℕ := (w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))
  let S2 : Finset ℕ := S.filter (fun n => v n ≠ 0)
  let P : Finset ℕ := (Finset.range (2*X+3)).filter (fun q => IsPrimePow q ∧ ¬ q.Prime)
  let B : Finset ℕ := (Finset.range (2*X+1)).filter (fun n => IsPrimePow (n+2) ∧ ¬ (n+2).Prime)
  change S.sum v / (X:ℝ) ≤ 100 * (L^3 / Real.sqrt (X:ℝ))
  have hX0 : (0:ℝ) < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX2 : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hLnonneg : 0 ≤ L := by
    apply Real.log_nonneg
    linarith
  have hv_nonneg : ∀ n : ℕ, 0 ≤ v n := fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  have hterm : ∀ n ∈ S, v n ≤ 4 * L^2 := by
    intro n hn
    have hnS : n ∈ w X := (Finset.mem_filter.mp hn).1
    have hnmem : n ∈ Finset.range (2*X+1) := (Finset.mem_filter.mp hnS).1
    have hnlt : n < 2*X+1 := Finset.mem_range.mp hnmem
    have hn3 : (3:ℕ) ≤ n := by
      have hXn : X < n := (Finset.mem_filter.mp hnS).2.1
      omega
    have hnltR : ((n:ℝ)) < 2*(X:ℝ)+1 := by exact_mod_cast hnlt
    have hlarith : ((n+2:ℕ):ℝ) ≤ ((X:ℝ)+2)^2 := by
      push_cast
      nlinarith [hnltR, hX2, sq_nonneg ((X:ℝ)+1)]
    have hlarith1 : ((n:ℕ):ℝ) ≤ ((X:ℝ)+2)^2 := by
      push_cast
      nlinarith [hnltR, hX2, sq_nonneg ((X:ℝ)+1)]
    have hlog2 : Real.log ((n+2:ℕ):ℝ) ≤ 2*L := by
      have hpos : (0:ℝ) < ((n+2:ℕ):ℝ) := by positivity
      have h := Real.log_le_log hpos hlarith
      rw [Real.log_pow] at h
      have hL : Real.log ((X:ℝ)+2) = L := by
        change Real.log ((X:ℝ)+2) = Real.log (2 + (X:ℝ))
        congr 1; ring
      rw [hL] at h
      simpa using h
    have hlog1 : Real.log ((n:ℕ):ℝ) ≤ 2*L := by
      have hpos : (0:ℝ) < ((n:ℕ):ℝ) := by positivity
      have h := Real.log_le_log hpos hlarith1
      rw [Real.log_pow] at h
      have hL : Real.log ((X:ℝ)+2) = L := by
        change Real.log ((X:ℝ)+2) = Real.log (2 + (X:ℝ))
        congr 1; ring
      rw [hL] at h
      simpa using h
    have hlog1nonneg : 0 ≤ Real.log ((n:ℕ):ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ n)
    have hlog2nonneg : 0 ≤ Real.log ((n+2:ℕ):ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ n+2)
    have h2Lnonneg : 0 ≤ 2*L := by linarith
    calc v n = ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) := rfl
      _ ≤ Real.log ((n:ℕ):ℝ) * Real.log ((n+2:ℕ):ℝ) :=
          mul_le_mul ArithmeticFunction.vonMangoldt_le_log ArithmeticFunction.vonMangoldt_le_log
            ArithmeticFunction.vonMangoldt_nonneg hlog1nonneg
      _ ≤ (2*L) * (2*L) := mul_le_mul hlog1 hlog2 hlog2nonneg h2Lnonneg
      _ = 4 * L^2 := by ring
  have hsum_eq : S.sum v = S2.sum v := by
    change S.sum v = (S.filter (fun n => v n ≠ 0)).sum v
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : v n ≠ 0
    · rw [if_pos h]
    · rw [if_neg h]
      exact not_not.mp h
  have hcardS2 : (S2.card : ℝ) ≤ 2 * (P.card : ℝ) := by
    have hsub : S2 ⊆ P ∪ B := by
      intro n hn
      have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
      have hvne : v n ≠ 0 := (Finset.mem_filter.mp hn).2
      have hnS1 : n ∈ w X := (Finset.mem_filter.mp hnS).1
      have hnotboth : ¬ (n.Prime ∧ (n+2).Prime) := (Finset.mem_filter.mp hnS).2
      have hnlt : n < 2*X+1 := Finset.mem_range.mp (Finset.mem_filter.mp hnS1).1
      have hΛ1 : ArithmeticFunction.vonMangoldt n ≠ 0 := by
        intro h
        apply hvne
        change ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2) = 0
        rw [h, zero_mul]
      have hΛ2 : ArithmeticFunction.vonMangoldt (n+2) ≠ 0 := by
        intro h
        apply hvne
        change ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2) = 0
        rw [h, mul_zero]
      have hipn : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ1
      have hipn2 : IsPrimePow (n+2) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ2
      by_cases hnp : n.Prime
      · have hn2np : ¬ (n+2).Prime := fun h => hnotboth ⟨hnp, h⟩
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hipn2, hn2np⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hipn, hnp⟩)
    have h1 : S2.card ≤ P.card + B.card :=
      calc S2.card ≤ (P ∪ B).card := Finset.card_le_card hsub
        _ ≤ P.card + B.card := Finset.card_union_le P B
    have h2 : B.card ≤ P.card := by
      apply Finset.card_le_card_of_injOn (fun n : ℕ => n + 2)
      · intro n hn
        have h := Finset.mem_filter.mp hn
        have hnlt : n < 2*X+1 := Finset.mem_range.mp h.1
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [Finset.mem_range]
          change n + 2 < 2*X+3
          omega
        · simpa using h.2
      · intro a ha b hb hab
        exact Nat.add_right_cancel hab
    have h1' : (S2.card : ℝ) ≤ (P.card : ℝ) + (B.card : ℝ) := by exact_mod_cast h1
    have h2' : (B.card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast h2
    linarith
  have hPbound : (P.card : ℝ) ≤ 12 * Real.sqrt (X:ℝ) * L := by
    have hp := power_count_bound (2*X+2) (by omega)
    have hsqr : Real.sqrt (((2*X+2 : ℕ) : ℝ)) ≤ 2 * Real.sqrt (X:ℝ) := by
      have hle : (((2*X+2 : ℕ) : ℝ)) ≤ 4 * (X:ℝ) := by push_cast; nlinarith [hX2]
      calc Real.sqrt (((2*X+2 : ℕ) : ℝ)) ≤ Real.sqrt (4 * (X:ℝ)) := Real.sqrt_le_sqrt hle
        _ = 2 * Real.sqrt (X:ℝ) := by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
            norm_num
    have hlogle : Real.log (2 + (((2*X+2 : ℕ) : ℝ))) ≤ 2*L := by
      have harg : 2 + (((2*X+2 : ℕ) : ℝ)) ≤ ((X:ℝ)+2)^2 := by push_cast; nlinarith
      have hpos : (0:ℝ) < 2 + (((2*X+2 : ℕ) : ℝ)) := by positivity
      have h := Real.log_le_log hpos harg
      rw [Real.log_pow] at h
      have hL : Real.log ((X:ℝ)+2) = L := by
        change Real.log ((X:ℝ)+2) = Real.log (2 + (X:ℝ))
        congr 1; ring
      rw [hL] at h
      simpa using h
    have hlognonneg : (0:ℝ) ≤ Real.log (2 + (((2*X+2 : ℕ) : ℝ))) := by
      apply Real.log_nonneg
      push_cast
      nlinarith [(Nat.cast_nonneg X : (0:ℝ) ≤ (X:ℝ))]
    calc (P.card : ℝ) ≤ 3 * Real.sqrt (((2*X+2 : ℕ) : ℝ)) * Real.log (2 + (((2*X+2 : ℕ) : ℝ))) := hp
      _ ≤ 3 * (2*Real.sqrt (X:ℝ)) * (2*L) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hsqr (by norm_num)
          · exact hlogle
          · exact hlognonneg
          · positivity
      _ = 12 * Real.sqrt (X:ℝ) * L := by ring
  have hsum_bound : S.sum v ≤ 96 * Real.sqrt (X:ℝ) * L^3 := by
    rw [hsum_eq]
    calc S2.sum v ≤ S2.card • (4 * L^2) := by
          apply Finset.sum_le_card_nsmul
          intro n hn
          exact hterm n (Finset.mem_filter.mp hn).1
      _ = S2.card * (4 * L^2) := by rw [nsmul_eq_mul]
      _ ≤ (2 * (P.card : ℝ)) * (4 * L^2) := by
          apply mul_le_mul_of_nonneg_right hcardS2
          positivity
      _ ≤ (2 * (12 * Real.sqrt (X:ℝ) * L)) * (4 * L^2) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left hPbound (by norm_num)
          · positivity
      _ = 96 * Real.sqrt (X:ℝ) * L^3 := by ring
  have hsqrtpos : 0 < Real.sqrt (X:ℝ) := Real.sqrt_pos.mpr hX0
  calc S.sum v / (X:ℝ) ≤ (96 * Real.sqrt (X:ℝ) * L^3) / (X:ℝ) :=
        div_le_div_of_nonneg_right hsum_bound (le_of_lt hX0)
    _ = 96 * L^3 / Real.sqrt (X:ℝ) := by
        have hXne : (X:ℝ) ≠ 0 := ne_of_gt hX0
        have hsqrtne : Real.sqrt (X:ℝ) ≠ 0 := ne_of_gt hsqrtpos
        field_simp
        ring_nf
        rw [Real.sq_sqrt (le_of_lt hX0)]
        ring
    _ ≤ 100 * L^3 / Real.sqrt (X:ℝ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hsqrtpos)
        have hL3 : 0 ≤ L^3 := by positivity
        nlinarith
    _ = 100 * (L^3 / Real.sqrt (X:ℝ)) := by ring
