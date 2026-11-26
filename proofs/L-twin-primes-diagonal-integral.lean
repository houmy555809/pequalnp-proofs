import Mathlib
open MeasureTheory
open scoped Topology

/-- The bump function `t ↦ if a < t ∧ t < b then exp (-1/((t-a)*(b-t))) else 0` is the standard
glue function evaluated at `(t-a)*(b-t)` (for `a < b`). -/
private lemma bump_eq_glue (a b t : ℝ) (hab : a < b) :
    (if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0)
      = expNegInvGlue ((t-a)*(b-t)) := by
  rcases lt_or_ge t b with htb | htb
  · rcases lt_or_ge a t with hat | hat
    · rw [if_pos ⟨hat, htb⟩]
      have hpos : 0 < (t-a)*(b-t) := mul_pos (by linarith) (by linarith)
      rw [expNegInvGlue, if_neg (not_le.mpr hpos)]
      congr 1
      rw [neg_div, one_div]
    · rw [if_neg (fun h => absurd h.1 (not_lt.mpr hat))]
      have h0 : expNegInvGlue ((t-a)*(b-t)) = 0 :=
        expNegInvGlue.zero_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
      exact h0.symm
  · rw [if_neg (fun h => absurd h.2 (not_lt.mpr htb))]
    have h0 : expNegInvGlue ((t-a)*(b-t)) = 0 :=
      expNegInvGlue.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
    exact h0.symm

/-- Second-difference positivity of the harmonic kernel. -/
private lemma curvature_identity (u c : ℝ) (hc : 0 < c) (hcu : c < u) :
    1/(u+c)+1/(u-c)-2/u = 2*c^2/(u*(u^2-c^2)) ∧ 0 < 1/(u+c)+1/(u-c)-2/u := by
  have hu : 0 < u := lt_trans hc hcu
  have hsq : 0 < u ^ 2 - c ^ 2 := by
    have h : 0 < (u - c) * (u + c) := mul_pos (sub_pos.mpr hcu) (add_pos hu hc)
    nlinarith [h]
  have hu0 : u ≠ 0 := ne_of_gt hu
  have huc : u + c ≠ 0 := ne_of_gt (add_pos hu hc)
  have humc : u - c ≠ 0 := ne_of_gt (sub_pos.mpr hcu)
  have hsq0 : u ^ 2 - c ^ 2 ≠ 0 := ne_of_gt hsq
  have hid : 1/(u+c)+1/(u-c)-2/u = 2*c^2/(u*(u^2-c^2)) := by
    field_simp
    ring
  exact ⟨hid, by rw [hid]; exact div_pos (by positivity) (mul_pos hu hsq)⟩

/-- Convolution of a continuous compactly supported function with itself is continuous. -/
private lemma conv_cont (g : ℝ → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g) :
    Continuous (fun v : ℝ => ∫ u : ℝ, g u * g (v - u)) := by
  have h1 : (fun v : ℝ => ∫ u : ℝ, g u * g (v - u))
      = convolution g g (ContinuousLinearMap.mul ℝ ℝ) := by
    funext v
    simp [convolution]
  rw [h1]
  exact hgs.continuous_convolution_right _ hg.locallyIntegrable hg

/-- An integral of a pointwise zero function vanishes. -/
private lemma integral_eq_zero_of_pointwise_zero {F : ℝ → ℝ} (h : ∀ u, F u = 0) :
    (∫ u : ℝ, F u) = 0 := by
  simp only [h, integral_zero]

/-- The product of a continuous function vanishing off `[-1/20,1/20]` with a function that is
continuous at every point of `[-1/20,1/20]` is continuous. -/
private lemma mul_zero_outside_cont (K φ : ℝ → ℝ) (hK : Continuous K)
    (hKzero : ∀ v, (1/20 : ℝ) ≤ |v| → K v = 0)
    (hφ : ∀ x, |x| ≤ 1/20 → ContinuousAt φ x) :
    Continuous (fun v => K v * φ v) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_or_ge |x| (1/20) with hlt | hge
  · show ContinuousAt (K * φ) x
    exact ContinuousAt.mul hK.continuousAt (hφ x (le_of_lt hlt))
  · rcases lt_or_eq_of_le hge with hlt2 | heq
    · have hopen : IsOpen {v : ℝ | (1/20 : ℝ) < |v|} := isOpen_lt continuous_const continuous_abs
      have hev : ∀ᶠ v in 𝓝 x, K v = 0 :=
        Filter.Eventually.mono (IsOpen.mem_nhds hopen hlt2) (fun v hv => hKzero v (le_of_lt hv))
      refine ContinuousAt.congr (f := fun _ : ℝ => (0:ℝ)) continuousAt_const ?_
      filter_upwards [hev] with v hv
      simp [hv]
    · have h0 : K x = 0 := hKzero x (le_of_eq heq)
      have hthis : ContinuousAt (K * φ) x := ContinuousAt.mul hK.continuousAt (hφ x (le_of_eq heq.symm))
      show ContinuousAt (K * φ) x
      simpa [h0] using hthis

/-- The `W` bump of the statement. -/
private noncomputable def TpW (t : ℝ) : ℝ :=
  if (1:ℝ) < t ∧ t < (51/50:ℝ) then Real.exp (-1/((t-1)*(51/50-t))) else 0

/-- The `b` bump of the statement. -/
private noncomputable def tpB (t : ℝ) : ℝ :=
  if (-1/40:ℝ) < t ∧ t < (1/40:ℝ) then Real.exp (-1/((t-(-1/40))*((1/40)-t))) else 0

/-- The kernel `K` of the statement. -/
private noncomputable def TpK (v : ℝ) : ℝ := ∫ u : ℝ, tpB u * tpB (v-u)

/-- The bracket whose positivity gives the second factor. -/
private noncomputable def tpPhi (h v : ℝ) : ℝ := 1/(h+v+1/5) + 1/(h+v-1/5) - 2/(h+v)

private lemma TpW_eq (t : ℝ) :
    TpW t = (if (1:ℝ) < t ∧ t < (51/50:ℝ) then Real.exp (-1/((t-1)*(51/50-t))) else 0) := rfl

private lemma tpB_eq (t : ℝ) :
    tpB t = (if (-1/40:ℝ) < t ∧ t < (1/40:ℝ) then Real.exp (-1/((t-(-1/40))*((1/40)-t))) else 0) :=
  rfl

private lemma tpPhi_eq (h v : ℝ) :
    tpPhi h v = 1/(h+v+1/5) + 1/(h+v-1/5) - 2/(h+v) := rfl

private lemma TpW_cont : Continuous TpW := by
  have hge : TpW = fun t : ℝ => expNegInvGlue ((t-1)*(51/50-t)) := by
    funext t
    rw [TpW_eq t]
    exact bump_eq_glue 1 (51/50) t (by norm_num)
  rw [hge]
  fun_prop

private lemma TpW_zero : ∀ t : ℝ, t ∉ Set.Icc (1:ℝ) (51/50) → TpW t = 0 := by
  intro t ht
  rw [TpW_eq t, if_neg]
  intro hcon
  exact ht ⟨le_of_lt hcon.1, le_of_lt hcon.2⟩

private lemma TpW_nn : ∀ t : ℝ, 0 ≤ TpW t := by
  intro t
  rw [TpW_eq t]
  by_cases hc : (1:ℝ) < t ∧ t < 51/50
  · rw [if_pos hc]
    exact le_of_lt (Real.exp_pos _)
  · rw [if_neg hc]

private lemma TpW_pos : ∀ t : ℝ, 1 < t → t < 51/50 → 0 < TpW t := by
  intro t h1 h2
  rw [TpW_eq t, if_pos ⟨h1, h2⟩]
  exact Real.exp_pos _

private lemma TpW_compact : HasCompactSupport TpW :=
  HasCompactSupport.intro (K := Set.Icc (1:ℝ) (51/50)) isCompact_Icc (fun t ht => TpW_zero t ht)

/-- The first factor of `d h` is positive. -/
private lemma TpW_integral_pos : 0 < ∫ u : ℝ, (TpW u)^2/u := by
  have hcont : Continuous (fun u : ℝ => (TpW u)^2/u) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with hx | hx
    · rw [hx]
      have hev : ∀ᶠ u : ℝ in 𝓝 0, TpW u = 0 :=
        Filter.Eventually.mono
          (IsOpen.mem_nhds isOpen_Ioo (show (0:ℝ) ∈ Set.Ioo (-1) 1 by norm_num)) (fun u hu =>
            TpW_zero u (by intro hmem; linarith [hmem.1, hu.2]))
      refine ContinuousAt.congr (f := fun _ : ℝ => (0:ℝ)) continuousAt_const ?_
      filter_upwards [hev] with u hu
      simp [hu]
    · show ContinuousAt ((fun u : ℝ => (TpW u)^2) / (fun u : ℝ => u)) x
      exact ContinuousAt.div ((TpW_cont.pow 2).continuousAt) continuousAt_id hx
  have hcomp : HasCompactSupport (fun u : ℝ => (TpW u)^2/u) := by
    refine HasCompactSupport.intro (K := Set.Icc (1:ℝ) (51/50)) isCompact_Icc ?_
    intro t ht
    have h0 : TpW t = 0 := TpW_zero t ht
    rw [h0]
    simp
  have hnn : ∀ u : ℝ, 0 ≤ (TpW u)^2/u := by
    intro u
    rcases lt_trichotomy u 0 with h | h | h
    · have h0 : TpW u = 0 := TpW_zero u (by intro hmem; linarith [hmem.1])
      rw [h0]
      simp
    · rw [h]
      simp
    · exact div_nonneg (sq_nonneg _) (le_of_lt h)
  have hne : (TpW (101/100))^2/(101/100) ≠ 0 := by
    have hp : 0 < TpW (101/100) := TpW_pos (101/100) (by norm_num) (by norm_num)
    have hd : (0:ℝ) < 101/100 := by norm_num
    exact ne_of_gt (div_pos (pow_pos hp 2) hd)
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := 101/100) hcont hcomp hnn hne

private lemma tpB_cont : Continuous tpB := by
  have hge : tpB = fun t : ℝ => expNegInvGlue ((t-(-1/40))*((1/40)-t)) := by
    funext t
    rw [tpB_eq t]
    exact bump_eq_glue (-1/40) (1/40) t (by norm_num)
  rw [hge]
  fun_prop

private lemma tpB_zero : ∀ t : ℝ, t ∉ Set.Icc (-1/40:ℝ) (1/40) → tpB t = 0 := by
  intro t ht
  rw [tpB_eq t, if_neg]
  intro hcon
  exact ht ⟨le_of_lt hcon.1, le_of_lt hcon.2⟩

private lemma tpB_nn : ∀ t : ℝ, 0 ≤ tpB t := by
  intro t
  rw [tpB_eq t]
  by_cases hc : (-1/40:ℝ) < t ∧ t < 1/40
  · rw [if_pos hc]
    exact le_of_lt (Real.exp_pos _)
  · rw [if_neg hc]

private lemma tpB_ne : ∀ t : ℝ, tpB t ≠ 0 → (-1/40:ℝ) < t ∧ t < 1/40 := by
  intro t ht
  by_contra hcon
  exact ht (by rw [tpB_eq t, if_neg hcon])

private lemma TpK_cont : Continuous TpK := by
  have h : TpK = fun v : ℝ => ∫ u : ℝ, tpB u * tpB (v-u) := rfl
  rw [h]
  exact conv_cont tpB tpB_cont
    (HasCompactSupport.intro (K := Set.Icc (-1/40:ℝ) (1/40)) isCompact_Icc (fun t ht => tpB_zero t ht))

private lemma TpK_zero : ∀ v : ℝ, (1/20:ℝ) ≤ |v| → TpK v = 0 := by
  intro v hv
  have hzero : ∀ u : ℝ, tpB u * tpB (v-u) = 0 := by
    intro u
    by_contra hne
    have h1 : tpB u ≠ 0 := (mul_ne_zero_iff.mp hne).1
    have h2 : tpB (v-u) ≠ 0 := (mul_ne_zero_iff.mp hne).2
    have hu : (-1/40:ℝ) < u ∧ u < 1/40 := tpB_ne u h1
    have hvu : (-1/40:ℝ) < v - u ∧ v - u < 1/40 := tpB_ne (v-u) h2
    have habs : |v| < 1/20 := by
      have hu' : |u| < 1/40 := abs_lt.mpr ⟨by linarith [hu.1], hu.2⟩
      have hvu' : |v-u| < 1/40 := abs_lt.mpr ⟨by linarith [hvu.1], hvu.2⟩
      calc |v| = |u + (v-u)| := by rw [show u + (v-u) = v from by ring]
        _ ≤ |u| + |v-u| := abs_add_le u (v-u)
        _ < 1/40 + 1/40 := add_lt_add hu' hvu'
        _ = 1/20 := by norm_num
    exact absurd habs (not_lt.mpr hv)
  have h : TpK v = ∫ u : ℝ, tpB u * tpB (v-u) := rfl
  rw [h]
  exact integral_eq_zero_of_pointwise_zero hzero

private lemma TpK_nn : ∀ v : ℝ, 0 ≤ TpK v := by
  intro v
  have h : TpK v = ∫ u : ℝ, tpB u * tpB (v-u) := rfl
  rw [h]
  exact integral_nonneg (f := fun u : ℝ => tpB u * tpB (v-u))
    (fun u => mul_nonneg (tpB_nn u) (tpB_nn (v-u)))

private lemma TpK_pos : 0 < TpK 0 := by
  have h : TpK 0 = ∫ u : ℝ, tpB u * tpB (0-u) := rfl
  rw [h]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := (0:ℝ)) ?_ ?_ ?_ ?_
  · exact tpB_cont.mul (tpB_cont.comp (by continuity))
  · refine HasCompactSupport.intro (K := Set.Icc (-1/40:ℝ) (1/40)) isCompact_Icc ?_
    intro t ht
    rw [tpB_zero t ht, zero_mul]
  · intro u
    exact mul_nonneg (tpB_nn u) (tpB_nn (0-u))
  · have hb0 : 0 < tpB 0 := by
      rw [tpB_eq 0, if_pos (by norm_num)]
      exact Real.exp_pos _
    rw [sub_zero]
    exact ne_of_gt (mul_pos hb0 hb0)

private lemma tpPhi_eq' (h v : ℝ) :
    tpPhi h v = 1/(h+v+1/5) + 1/(h+v-1/5) - 2/(h+v) := rfl

private lemma tpPhi_pos (h v : ℝ) (hh : 1 ≤ h) (hv : |v| ≤ 1/20) : 0 < tpPhi h v := by
  rw [tpPhi_eq' h v]
  have hv1 : -(1/20:ℝ) ≤ v := (abs_le.mp hv).1
  have hu : (1/5:ℝ) < h + v := by linarith
  exact (curvature_identity (h+v) (1/5) (by norm_num) hu).2

private lemma tpPhi_cont (h : ℝ) (hh : 1 ≤ h) :
    ∀ x : ℝ, |x| ≤ (1/20:ℝ) → ContinuousAt (tpPhi h) x := by
  intro x hx
  have hx1 : -(1/20:ℝ) ≤ x := (abs_le.mp hx).1
  have hd1 : h + x + 1/5 ≠ 0 := by intro hc; linarith
  have hd2 : h + x - 1/5 ≠ 0 := by intro hc; linarith
  have hd3 : h + x ≠ 0 := by intro hc; linarith
  have h : tpPhi h = fun v : ℝ => 1/(h+v+1/5) + 1/(h+v-1/5) - 2/(h+v) := rfl
  rw [h]
  fun_prop

/-- The second factor of `d h` is positive. -/
private lemma TpB_integral_pos (h : ℝ) (hh : 1 ≤ h) : 0 < ∫ v : ℝ, TpK v * tpPhi h v := by
  have hcont : Continuous (fun v : ℝ => TpK v * tpPhi h v) :=
    mul_zero_outside_cont TpK (tpPhi h) TpK_cont TpK_zero (tpPhi_cont h hh)
  have hcomp : HasCompactSupport (fun v : ℝ => TpK v * tpPhi h v) := by
    refine HasCompactSupport.intro (K := Set.Icc (-(1/20):ℝ) (1/20)) isCompact_Icc ?_
    intro t ht
    have h0 : TpK t = 0 := by
      apply TpK_zero
      rcases not_and_or.mp ht with h1 | h1
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [h0, zero_mul]
  have hnn : ∀ v : ℝ, 0 ≤ TpK v * tpPhi h v := by
    intro v
    by_cases hv : (1/20:ℝ) ≤ |v|
    · rw [TpK_zero v hv, zero_mul]
    · have hv' : |v| ≤ 1/20 := le_of_lt (not_le.mp hv)
      exact mul_nonneg (TpK_nn v) (le_of_lt (tpPhi_pos h v hh hv'))
  have hne : TpK 0 * tpPhi h 0 ≠ 0 :=
    ne_of_gt (mul_pos TpK_pos (tpPhi_pos h 0 hh (by norm_num)))
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := (0:ℝ)) hcont hcomp hnn hne

theorem PEqualNP.Outside.L_twin_primes_diagonal_integral :
    let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0; let W := bump 1 (51/50); let b := bump (-1/40) (1/40); let K := fun (v : ℝ) => ∫ u : ℝ, b u * b (v-u); let d := fun (h : ℝ) => (∫ u : ℝ, (W u)^2/u)/16 * (∫ v : ℝ, K v*(1/(h+v+1/5)+1/(h+v-1/5)-2/(h+v))); ∀ h : ℝ, 1 ≤ h → 0 < d h := by
  intro bump W b K d h hh
  have hWeq : W = TpW := rfl
  have hbeq : b = tpB := rfl
  have hKeq : K = TpK := rfl
  have hA : 0 < ∫ u : ℝ, (W u)^2/u := by
    rw [hWeq]
    exact TpW_integral_pos
  have hB : 0 < ∫ v : ℝ, K v * (1/(h+v+1/5) + 1/(h+v-1/5) - 2/(h+v)) := by
    rw [hKeq]
    exact TpB_integral_pos h hh
  have hdform : d h = (∫ u : ℝ, (W u)^2/u)/16 *
      (∫ v : ℝ, K v*(1/(h+v+1/5)+1/(h+v-1/5)-2/(h+v))) := rfl
  rw [hdform]
  exact mul_pos (div_pos hA (by norm_num)) hB
