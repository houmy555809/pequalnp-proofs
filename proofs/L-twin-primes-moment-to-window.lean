import Mathlib

/-!
# Twin primes, TP-0015 final: the frozen moment-to-window implication, unconditionally

Frozen statements are those of `claim-work-tp/research/problems.json` (`twin-primes.gaps`),
read verbatim.  The main theorem of this file,

  `PEqualNP.Outside.L_twin_primes_moment_to_window`,

is the frozen TP-0015 text itself: the implication from the signed-moment margin to the
window surplus.  Its hypothesis stays a hypothesis, as the frozen statement is an
implication.  Only Mathlib is used, and every proof is complete.

The file has two halves.

* **The frozen TP-0013 two-moment identity, proved unconditionally.**  The whole
  development of `open/twin/two-moment-identity-candidate.lean` is embedded: the frozen
  bump and window data, the finite-square expansion `norm_sq_P`, the `1 ± cos`
  cancellation `I_one_sub_neg_one`, the integrability and finite-sum exchange
  (`twoMomentExpansionInput_of_integrable`), the substitution `t = T u`
  (`bandIntegral_eq_T_mul_pairKernel`), the Schwartz/Fourier computation of the pair
  kernel (`pairKernelFormula`) and the finite-sum collapse (`sum_collapse_pair`), ending
  in `TwinPrimes.twoMomentIdentity : TwoMomentIdentity`.  Its frozen-statement form is
  `PEqualNP.Outside.L_twin_primes_two_moment_identity`.
* **The TP-0015 reduction.**  `TwinPrimes.momentToWindow_of_twoMomentIdentityHyp :
  TwoMomentIdentityHyp → SignedMomentMargin → WindowSurplus` turns the frozen
  two-moment margin into the arithmetic window surplus.  Both kernel bounds on the
  twin-shift range are proved outright here (`kernelUpperBound`, `kernelLowerBound`);
  the remaining glue is `fX_sub_two_mem_Icc` (the twin shift lands in `[-1/25, 0]`),
  `uu_le_v_div` (moment weights are at most `Λ Λ / X`), the monotone finite-sum
  comparisons, and the decay `tendsto_e_zero` / `eventually_mul_e_lt` of
  `e X = log ^ 3 (2 + X) / sqrt X`, which upgrades a constant window mass to a surplus
  over every fixed multiple `K`.

The final theorem instantiates the unconditional identity in the reduction.  A weaker
one-sided bridge (`MomentUpperBridge`) and the TP-0014 chain are kept at the end of the
TP-0015 half as additional reductions.
-/

open MeasureTheory

open scoped ENNReal

namespace TwinPrimes

noncomputable section

/-! ## Frozen data -/

/-- The frozen bump function on `(a,b)`. -/
def bump (a b t : ℝ) : ℝ := if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0

/-- The frozen long window weight `W = bump 1 (51/50)`. -/
def W : ℝ → ℝ := bump 1 (51/50)

/-- The frozen band bump `b = bump (-1/40) (1/40)`. -/
def bumpB : ℝ → ℝ := bump (-1/40) (1/40)

/-- The frozen band kernel `k`. -/
def k (t : ℝ) : ℝ := ∫ y : ℝ, bumpB y * Real.cos (2*Real.pi*y*t)

/-- The frozen test function `l`. -/
def l (t : ℝ) : ℝ := Real.sin (Real.pi*t/5)*k t

/-- The frozen scale `T X = 2*pi*X`. -/
def T (X : ℕ) : ℝ := 2*Real.pi*(X:ℝ)

/-- The frozen narrow gap-two window. -/
def w (X : ℕ) : Finset ℕ := (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)

/-- The frozen window weight. -/
def u (X n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n

/-- The frozen Dirichlet polynomial. -/
def P (X : ℕ) (t : ℝ) : ℂ :=
  (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ)))

/-- The frozen two-moment functional. -/
def I (X : ℕ) (σ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2

/-- The frozen autocorrelation `K = b * b`. -/
def Kf (v : ℝ) : ℝ := ∫ y : ℝ, bumpB y * bumpB (v-y)

/-- The frozen band kernel `H`. -/
def H (v : ℝ) : ℝ := Kf v / 2 - Kf (v-1/5)/4 - Kf (v+1/5)/4

/-- The frozen log-scale offset `f`. -/
def fX (x n j : ℝ) : ℝ := x * Real.log (1+j/n)

/-- The frozen two-point von Mangoldt weight. -/
def v (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)

/-- The frozen normalized window mass. -/
def M (X : ℕ) : ℝ := (w X).sum v / (X:ℝ)

/-- The frozen vanishing error scale. -/
def e (X : ℕ) : ℝ := Real.log (2+(X:ℝ))^3 / Real.sqrt X

/-! ## Frozen statements as predicates -/

/-- Frozen TP-0014 `L-twin-primes-signed-moment-margin`. -/
def SignedMomentMargin : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ δ*T X < I X 1-I X (-1)

/-- Frozen TP-0013 `L-twin-primes-two-moment-identity`. -/
def TwoMomentIdentityHyp : Prop :=
  ∀ X : ℕ, 1000 ≤ X →
    I X 1 - I X (-1) =
      T X * ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => u X n*u X (n+2)*H (fX X n 2 - 2))

/-- Frozen TP-0015 `L-twin-primes-moment-to-window`. -/
def WindowSurplus : Prop := ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X

/-! ## Frozen-statement audit (definitional equality with the frozen text) -/

/-- Frozen TP-0014 is definitionally `SignedMomentMargin`. -/
theorem frozen_signedMomentMargin_eq :
    (let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0
     let W := bump 1 (51/50)
     let b := bump (-1/40) (1/40)
     let k := fun (t : ℝ) => ∫ v : ℝ, b v * Real.cos (2*Real.pi*v*t)
     let l := fun (t : ℝ) => Real.sin (Real.pi*t/5)*k t
     let T := fun (X : ℕ) => 2*Real.pi*(X:ℝ)
     let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
     let u := fun (X n : ℕ) => ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n
     let P := fun (X : ℕ) (t : ℝ) =>
       (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ)))
     let I := fun (X : ℕ) (σ : ℝ) =>
       ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2
     ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ δ*T X < I X 1-I X (-1)) =
      SignedMomentMargin := rfl

/-- Frozen TP-0013 is definitionally `TwoMomentIdentityHyp`. -/
theorem frozen_twoMomentIdentityHyp_eq :
    (let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0
     let W := bump 1 (51/50)
     let b := bump (-1/40) (1/40)
     let K := fun (v : ℝ) => ∫ u : ℝ, b u * b (v-u)
     let H := fun (v : ℝ) => K v / 2 - K (v-1/5)/4 - K (v+1/5)/4
     let k := fun (t : ℝ) => ∫ v : ℝ, b v * Real.cos (2*Real.pi*v*t)
     let l := fun (t : ℝ) => Real.sin (Real.pi*t/5)*k t
     let T := fun (X : ℕ) => 2*Real.pi*(X:ℝ)
     let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
     let u := fun (X n : ℕ) => ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n
     let P := fun (X : ℕ) (t : ℝ) =>
       (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ)))
     let I := fun (X : ℕ) (σ : ℝ) =>
       ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2
     let f := fun (x n j : ℝ) => x * Real.log (1+j/n)
     ∀ X : ℕ, 1000 ≤ X →
       I X 1 - I X (-1) =
         T X * ((w X).filter (fun n => n+2 ∈ w X)).sum
           (fun n => u X n*u X (n+2)*H (f X n 2 - 2))) = TwoMomentIdentityHyp := rfl

/-- Frozen TP-0015 is definitionally `SignedMomentMargin → WindowSurplus`. -/
theorem frozen_momentToWindow_eq :
    (let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0
     let W := bump 1 (51/50)
     let b := bump (-1/40) (1/40)
     let k := fun (t : ℝ) => ∫ v : ℝ, b v * Real.cos (2*Real.pi*v*t)
     let l := fun (t : ℝ) => Real.sin (Real.pi*t/5)*k t
     let T := fun (X : ℕ) => 2*Real.pi*(X:ℝ)
     let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
     let u := fun (X n : ℕ) => ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n
     let P := fun (X : ℕ) (t : ℝ) =>
       (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ)))
     let I := fun (X : ℕ) (σ : ℝ) =>
       ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2
     (∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ δ*T X < I X 1-I X (-1)) →
       (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
        let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)
        let M := fun (X : ℕ) => (w X).sum v / (X : ℝ)
        let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X
        ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X)) =
      (SignedMomentMargin → WindowSurplus) := rfl

/-! ## Shared elementary facts -/

/-- The frozen narrow window is contained in `Ioi X`. -/
lemma mem_window_bounds {X n : ℕ} (hn : n ∈ w X) : X < n ∧ 50*n < 51*X := by
  rw [w] at hn
  exact (Finset.mem_filter.mp hn).2

/-- The window weight is nonnegative. -/
lemma W_nonneg (t : ℝ) : 0 ≤ W t := by
  rw [W, bump]
  split_ifs with h
  · exact (Real.exp_pos _).le
  · exact le_refl 0

/-- The window weight is at most one. -/
lemma W_le_one (t : ℝ) : W t ≤ 1 := by
  rw [W, bump]
  split_ifs with h
  · have hpos : 0 < (t-1)*(51/50-t) := mul_pos (by linarith [h.1]) (by linarith [h.2])
    have hneg : -1/((t-1)*(51/50-t)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hpos.le
    calc Real.exp (-1/((t-1)*(51/50-t))) ≤ Real.exp 0 := Real.exp_le_exp.2 hneg
      _ = 1 := Real.exp_zero
  · exact zero_le_one

/-- A uniform positive lower bound for the window weight on the fixed relative
core `[1005/1000, 1010/1000]` (well inside the frozen window `(1, 51/50)`). -/
lemma W_ge_of_mem {t : ℝ} (h1 : 1005/1000 ≤ t) (h2 : t ≤ 1010/1000) :
    Real.exp (-(20000:ℝ)) ≤ W t := by
  rw [W, bump]
  have hmem : 1 < t ∧ t < 51/50 := by constructor <;> linarith
  simp only [hmem]
  apply Real.exp_le_exp.2
  have hpos : 0 < (t-1)*(51/50-t) := mul_pos (by linarith) (by linarith)
  have hle : (5:ℝ)/100000 ≤ (t-1)*(51/50-t) := by nlinarith
  have h1d : 1/((t-1)*(51/50-t)) ≤ 20000 := by
    have h := one_div_le_one_div_of_le (show (0:ℝ) < 5/100000 by norm_num) hle
    have h20000 : (1:ℝ)/(5/100000) = 20000 := by norm_num
    linarith [h, h20000]
  have h2d : -(20000:ℝ) ≤ -(1/((t-1)*(51/50-t))) := neg_le_neg h1d
  have heq : -(1/((t-1)*(51/50-t))) = -1/((t-1)*(51/50-t)) := by ring
  linarith [h2d, heq]

/-- The window weight `u` is nonnegative. -/
lemma u_nonneg (X n : ℕ) : 0 ≤ u X n := by
  rw [u]
  exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (W_nonneg _))
    (Real.sqrt_nonneg n)

/-- The two-point von Mangoldt weight is nonnegative. -/
lemma v_nonneg (n : ℕ) : 0 ≤ v n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg

/-- The frozen scale is positive. -/
lemma T_pos {X : ℕ} (hX : 0 < X) : 0 < T X := by
  rw [T]
  have hXR : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hXR

/-- The frozen error scale is nonnegative. -/
lemma e_nonneg (X : ℕ) : 0 ≤ e X := by
  rw [e]
  apply div_nonneg
  · apply pow_nonneg
    apply Real.log_nonneg
    have : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
    linarith
  · exact Real.sqrt_nonneg X

/-! ## The log-scale range of the twin shift

The frozen identity evaluates the band kernel at `f X n 2 - 2 = X*log(1+2/n) - 2`.
Inside the frozen window (`n > X`, `50*(n+2) < 51*X`) this argument lies in
`[-1/25, 0]`, strictly inside the support `[-1/20, 1/20]` of the autocorrelation `K`.
-/

lemma fX_sub_two_mem_Icc {X n : ℕ} (hX : 1000 ≤ X) (hn : n ∈ w X) (hn2 : n+2 ∈ w X) :
    fX (X:ℝ) (n:ℝ) 2 - 2 ∈ Set.Icc (-(1/25) : ℝ) 0 := by
  obtain ⟨hXn, -⟩ := mem_window_bounds hn
  obtain ⟨-, h2⟩ := mem_window_bounds hn2
  have hXpos : (0:ℝ) < (X:ℝ) := by positivity
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hcast : (50:ℝ)*((n:ℝ)+2) < 51*(X:ℝ) := by
    have hh : ((50*(n+2) : ℕ) : ℝ) < ((51*X : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at hh
    linarith
  have hXn' : (X:ℝ) < (n:ℝ) := by exact_mod_cast hXn
  have hu : (0:ℝ) < 1 + 2/(n:ℝ) := by positivity
  have hub : Real.log (1 + 2/(n:ℝ)) ≤ 2/(n:ℝ) := by
    have h := Real.log_le_sub_one_of_pos hu
    linarith
  have hlb : 2/((n:ℝ)+2) ≤ Real.log (1 + 2/(n:ℝ)) := by
    have h := Real.one_sub_inv_le_log_of_pos hu
    have heq : (1:ℝ) - (1 + 2/(n:ℝ))⁻¹ = 2/((n:ℝ)+2) := by
      field_simp
      ring
    linarith [h, heq]
  constructor
  · simp only [fX]
    have hpos2 : (0:ℝ) < (n:ℝ)+2 := by linarith
    have h2' : (49:ℝ)/25 < (X:ℝ) * (2/((n:ℝ)+2)) := by
      rw [mul_div_assoc']
      rw [lt_div_iff₀ hpos2]
      nlinarith [hcast, hXn', hXpos]
    have h1' : (X:ℝ) * (2/((n:ℝ)+2)) ≤ (X:ℝ) * Real.log (1 + 2/(n:ℝ)) :=
      mul_le_mul_of_nonneg_left hlb hXpos.le
    linarith
  · simp only [fX]
    have h1' : (X:ℝ) * Real.log (1 + 2/(n:ℝ)) ≤ (X:ℝ)*(2/(n:ℝ)) :=
      mul_le_mul_of_nonneg_left hub hXpos.le
    have h2' : (X:ℝ) * (2/(n:ℝ)) < 2 := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (show (0:ℝ) < (n:ℝ) by linarith)]
      nlinarith [hXn', hXpos]
    linarith

/-! ## The vanishing error scale `log^3 X / sqrt X` -/

lemma e_le_eight (X : ℕ) (hX : 2 ≤ X) : e X ≤ 8 * (Real.log (X:ℝ)^3 / Real.sqrt (X:ℝ)) := by
  rw [e]
  have hXpos : (0:ℝ) < (X:ℝ) := by
    have : 0 < X := by omega
    exact_mod_cast this
  have hsX : (0:ℝ) < Real.sqrt (X:ℝ) := Real.sqrt_pos.2 hXpos
  have hX2 : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hlogX : (0:ℝ) ≤ Real.log (X:ℝ) := Real.log_nonneg (by linarith)
  have h2X : (2:ℝ) + (X:ℝ) ≤ (X:ℝ)^2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (X:ℝ)-2 by linarith)
      (show (0:ℝ) ≤ (X:ℝ)+1 by linarith)]
  have hlog2X : Real.log (2+(X:ℝ)) ≤ 2*Real.log (X:ℝ) := by
    have h1 : Real.log (2+(X:ℝ)) ≤ Real.log ((X:ℝ)^2) :=
      Real.log_le_log (by linarith) h2X
    have h2 : Real.log ((X:ℝ)^2) = 2*Real.log (X:ℝ) := by
      rw [Real.log_pow]; push_cast; ring
    linarith
  have hlog2X0 : (0:ℝ) ≤ Real.log (2+(X:ℝ)) := Real.log_nonneg (by linarith)
  have hcube : Real.log (2+(X:ℝ))^3 ≤ 8*Real.log (X:ℝ)^3 := by
    have h := pow_le_pow_left₀ hlog2X0 hlog2X 3
    calc Real.log (2+(X:ℝ))^3 ≤ (2*Real.log (X:ℝ))^3 := h
      _ = 8*Real.log (X:ℝ)^3 := by ring
  calc Real.log (2+(X:ℝ))^3 / Real.sqrt (X:ℝ)
      ≤ 8*Real.log (X:ℝ)^3 / Real.sqrt (X:ℝ) := div_le_div_of_nonneg_right hcube hsX.le
    _ = 8 * (Real.log (X:ℝ)^3 / Real.sqrt (X:ℝ)) := by ring

/-- The frozen error scale vanishes. -/
lemma tendsto_e_zero : Filter.Tendsto (fun X : ℕ => e X) Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun x : ℝ => Real.log x ^ (3:ℕ) / Real.sqrt x)
      Filter.atTop (nhds 0) := by
    have ho : (fun x : ℝ => Real.log x ^ (3:ℕ)) =o[Filter.atTop]
        (fun x : ℝ => x ^ ((1:ℝ)/2)) := by
      have h := isLittleO_log_rpow_rpow_atTop (r := (3:ℝ)) (s := ((1:ℝ)/2)) (by norm_num)
      simpa [Real.rpow_natCast] using h
    have ht := ho.tendsto_div_nhds_zero
    simpa [Real.sqrt_eq_rpow] using ht
  have hnat : Filter.Tendsto (fun X : ℕ => Real.log (X:ℝ) ^ (3:ℕ) / Real.sqrt (X:ℝ))
      Filter.atTop (nhds 0) := hbase.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (g := fun X : ℕ => 8 * (Real.log (X:ℝ)^3 / Real.sqrt (X:ℝ))) ?_ ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 2] with X hX using e_nonneg X
  · filter_upwards [Filter.eventually_ge_atTop 2] with X hX using e_le_eight X hX
  · simpa using hnat.const_mul (8:ℝ)

/-- For every constant `K` and every positive `m`, eventually `K * e X < m`. -/
lemma eventually_mul_e_lt {K m : ℝ} (hm : 0 < m) :
    ∀ᶠ X : ℕ in Filter.atTop, K * e X < m := by
  have h : Filter.Tendsto (fun X : ℕ => K * e X) Filter.atTop (nhds (K*0)) :=
    tendsto_const_nhds.mul tendsto_e_zero
  rw [mul_zero] at h
  exact h.eventually (isOpen_Iio.mem_nhds (show (0:ℝ) ∈ Set.Iio m from hm))

/-! ## Frozen statements as predicates -/

/-- Frozen TP-0013 `L-twin-primes-two-moment-identity`. -/
def TwoMomentIdentity : Prop :=
  ∀ X : ℕ, 1000 ≤ X →
    I X 1 - I X (-1) =
      T X * ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => u X n*u X (n+2)*H (fX X n 2 - 2))

/-- The band integral attached to a pair `(n,m)` (the frozen `1 ± cos` difference after
expansion, normalized by `T`). -/
def bandIntegral (X n m : ℕ) : ℝ :=
  2 * ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2 * Real.cos (4*Real.pi*t/T X) *
    Real.cos (t*(Real.log m - Real.log n))

/-- The band integrand (without the outer factor `2`). -/
def bandIntegrand (X n m : ℕ) (t : ℝ) : ℝ :=
  (l (t/T X))^2 * Real.cos (4*Real.pi*t/T X) * Real.cos (t*(Real.log m - Real.log n))

/-- TP-0013 input (i): expanding the finite square of `P` inside the two moments
(integrability plus interchange of the finite sum with the integral). -/
def TwoMomentExpansionInput : Prop :=
  ∀ X : ℕ, 1000 ≤ X →
    I X 1 - I X (-1) =
      (w X).sum (fun n => (w X).sum (fun m => u X n * u X m * bandIntegral X n m))

/-! ## The finite-square expansion of `‖P‖²` -/

/-- `exp (-I x) = cos x - I sin x` for real `x`. -/
lemma exp_neg_I_mul (x : ℝ) :
    Complex.exp (-Complex.I * (x : ℂ)) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
  have harg : -Complex.I * (x:ℂ) = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [harg, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

/-- Real part of the frozen Dirichlet polynomial. -/
lemma P_re (X : ℕ) (t : ℝ) :
    (P X t).re = (w X).sum (fun n => u X n * Real.cos (t * Real.log n)) := by
  unfold P
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have harg : -Complex.I * (t : ℂ) * (Real.log n : ℂ)
      = -Complex.I * ((t * Real.log n : ℝ) : ℂ) := by push_cast; ring
  rw [harg, exp_neg_I_mul, Complex.mul_re]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero]

/-- Imaginary part of the frozen Dirichlet polynomial. -/
lemma P_im (X : ℕ) (t : ℝ) :
    (P X t).im = -((w X).sum (fun n => u X n * Real.sin (t * Real.log n))) := by
  unfold P
  rw [Complex.im_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have harg : -Complex.I * (t : ℂ) * (Real.log n : ℂ)
      = -Complex.I * ((t * Real.log n : ℝ) : ℂ) := by push_cast; ring
  rw [harg, exp_neg_I_mul, Complex.mul_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, zero_sub, add_zero]
  ring

/-- Expansion of the squared modulus of the finite exponential sum: a pure finite double
sum with cosine of the log-phase differences. -/
theorem norm_sq_P (X : ℕ) (t : ℝ) :
    ‖P X t‖^2 = (w X).sum (fun n => (w X).sum (fun m =>
      u X n * u X m * Real.cos (t * (Real.log n - Real.log m)))) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, P_re, P_im]
  set S := w X
  set c : ℕ → ℝ := fun n => u X n * Real.cos (t * Real.log n) with hc
  set s : ℕ → ℝ := fun n => u X n * Real.sin (t * Real.log n) with hs
  have hbase : (S.sum c) * (S.sum c) + (-(S.sum s)) * (-(S.sum s))
      = S.sum (fun n => S.sum (fun m =>
          (u X n * Real.cos (t * Real.log n)) * (u X m * Real.cos (t * Real.log m))
          + (u X n * Real.sin (t * Real.log n)) * (u X m * Real.sin (t * Real.log m)))) := by
    rw [show (-(S.sum s)) * (-(S.sum s)) = (S.sum s) * (S.sum s) by ring,
      Finset.sum_mul_sum S S (fun n => u X n * Real.cos (t * Real.log n))
        (fun m => u X m * Real.cos (t * Real.log m)),
      Finset.sum_mul_sum S S (fun n => u X n * Real.sin (t * Real.log n))
        (fun m => u X m * Real.sin (t * Real.log m))]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← Finset.sum_add_distrib]
  rw [hbase]
  refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
  have hcos : Real.cos (t * (Real.log n - Real.log m))
      = Real.cos (t * Real.log n) * Real.cos (t * Real.log m)
        + Real.sin (t * Real.log n) * Real.sin (t * Real.log m) := by
    rw [show t * (Real.log n - Real.log m) = t * Real.log n - t * Real.log m by ring,
      Real.cos_sub]
  rw [hcos]
  ring

/-! ## The `1 ± cos` cancellation: `I 1 - I (-1)` is the cosine-weighted energy -/

/-- Under the two integrability hypotheses, the `1` in `1 + σ cos` cancels and
`I X 1 - I X (-1) = 2 ∫_{t>0} l(t/T)² cos(4πt/T) ‖P‖²`. -/
theorem I_one_sub_neg_one (X : ℕ)
    (h1 : Integrable (fun t : ℝ =>
      (l (t/T X))^2*(1+1*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2)
      (volume.restrict (Set.Ioi (0:ℝ))))
    (h2 : Integrable (fun t : ℝ =>
      (l (t/T X))^2*(1+(-1)*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2)
      (volume.restrict (Set.Ioi (0:ℝ)))) :
    I X 1 - I X (-1) =
      2 * ∫ t in Set.Ioi (0:ℝ),
        (l (t/T X))^2*Real.cos (4*Real.pi*t/T X)*‖P X t‖^2 := by
  rw [I, I, ← MeasureTheory.integral_sub h1 h2, ← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  ring

/-! ## Integrability: one hypothesis implies all the required integrabilities -/

/-- The single analytic input of the expansion: `l²` is integrable on the half-line.  Since
`l = sin(π·/5)·k` and `k` is the Fourier transform of the compactly supported bump `b`,
this is the (standard) rapid-decay statement for `k`; `l²` is bounded below/above by `k²`
so it is exactly `k ∈ L²(0,∞)` up to the bounded sine factor. -/
def ExpansionIntegrable : Prop :=
  ∀ X : ℕ, 1000 ≤ X → IntegrableOn (fun t : ℝ => (l (t/T X))^2) (Set.Ioi (0:ℝ))

/-- A uniform bound for `‖P X t‖` by the (finite) sum of the absolute weights. -/
lemma norm_P_le (X : ℕ) (t : ℝ) :
    ‖P X t‖ ≤ (w X).sum (fun n => |u X n|) := by
  unfold P
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun n _ => ?_)
  have harg : -Complex.I * (t : ℂ) * (Real.log n : ℂ)
      = (-(t * Real.log n) : ℝ) * Complex.I := by push_cast; ring
  rw [norm_mul, harg, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- The finite sum of absolute weights is nonnegative. -/
lemma sum_abs_u_nonneg (X : ℕ) : 0 ≤ (w X).sum (fun n => |u X n|) :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- The squared modulus of `P` is bounded by the square of the absolute-weight sum. -/
lemma norm_sq_P_le (X : ℕ) (t : ℝ) :
    ‖P X t‖^2 ≤ ((w X).sum (fun n => |u X n|))^2 := by
  have hC := sum_abs_u_nonneg X
  have h := norm_P_le X t
  nlinarith [norm_nonneg (P X t)]


/-! ## Continuity and integrability plumbing -/

/-- `t ↦ ‖P X t‖²` is continuous. -/
lemma continuous_norm_sq_P (X : ℕ) : Continuous (fun t : ℝ => ‖P X t‖^2) := by
  have hP : Continuous (fun t : ℝ => P X t) := by
    unfold P
    refine continuous_finsetSum _ (fun n _ => ?_)
    refine Continuous.mul continuous_const ?_
    refine Complex.continuous_exp.comp ?_
    exact (continuous_const.mul Complex.continuous_ofReal).mul continuous_const
  exact hP.norm.pow 2

/-- Multiplying an integrable function by a continuous function bounded by `c` keeps it
integrable. -/
lemma integrableOn_mul_bounded {X : ℕ}
    (hLx : Integrable (fun t : ℝ => (l (t/T X))^2) (volume.restrict (Set.Ioi (0:ℝ))))
    (g : ℝ → ℝ) (hg : Continuous g) (c : ℝ) (hgb : ∀ t : ℝ, |g t| ≤ c) :
    Integrable (fun t : ℝ => (l (t/T X))^2 * g t) (volume.restrict (Set.Ioi (0:ℝ))) := by
  refine hLx.mul_bdd (c := c) hg.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs]
  exact hgb t

/-! ## Exchange of the finite double sum with the integral -/

/-- The cosine-weighted energy is the double sum of `u u` times the band integrals: the
finite square expansion commuted with the integral over `(0,∞)`. -/
theorem integral_cos_weighted_normSq_eq_sum {X : ℕ}
    (hLx : Integrable (fun t : ℝ => (l (t/T X))^2) (volume.restrict (Set.Ioi (0:ℝ)))) :
    ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2 * Real.cos (4*Real.pi*t/T X) * ‖P X t‖^2
      = (w X).sum (fun n => (w X).sum (fun m =>
          u X n * u X m * ∫ t in Set.Ioi (0:ℝ), bandIntegrand X n m t)) := by
  have hcos_swap : ∀ (t : ℝ) (n m : ℕ),
      Real.cos (t * (Real.log n - Real.log m))
        = Real.cos (t * (Real.log m - Real.log n)) := by
    intro t n m
    rw [show t * (Real.log n - Real.log m) = -(t * (Real.log m - Real.log n)) by ring,
      Real.cos_neg]
  have hpt : ∀ t : ℝ, (l (t/T X))^2 * Real.cos (4*Real.pi*t/T X) * ‖P X t‖^2
      = (w X).sum (fun n => (w X).sum (fun m => u X n * u X m * bandIntegrand X n m t)) := by
    intro t
    rw [norm_sq_P X t, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hcos_swap t n m]
    unfold bandIntegrand
    ring
  have hband : ∀ n m : ℕ, Integrable (fun t : ℝ => bandIntegrand X n m t)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    intro n m
    have hcont : Continuous (fun t : ℝ =>
        Real.cos (4*Real.pi*t/T X) * Real.cos (t*(Real.log m - Real.log n))) := by
      have h1 : Continuous (fun t : ℝ => 4*Real.pi*t/T X) := by
        have h2 : Continuous (fun t : ℝ => (4*Real.pi/T X) * t) :=
          continuous_const.mul continuous_id
        convert h2 using 1
        ext t
        ring
      have h2 : Continuous (fun t : ℝ => t*(Real.log m - Real.log n)) :=
        continuous_id.mul continuous_const
      exact (Real.continuous_cos.comp h1).mul (Real.continuous_cos.comp h2)
    have hbnd : ∀ t : ℝ,
        |Real.cos (4*Real.pi*t/T X) * Real.cos (t*(Real.log m - Real.log n))| ≤ 1 := by
      intro t
      rw [abs_mul]
      calc |Real.cos (4*Real.pi*t/T X)| * |Real.cos (t*(Real.log m - Real.log n))|
          ≤ 1 * 1 := mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
              (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hbase := integrableOn_mul_bounded hLx
      (fun t : ℝ => Real.cos (4*Real.pi*t/T X) * Real.cos (t*(Real.log m - Real.log n)))
      hcont 1 hbnd
    refine hbase.congr ?_
    filter_upwards with t
    unfold bandIntegrand
    ring
  rw [show (fun t : ℝ => (l (t/T X))^2 * Real.cos (4*Real.pi*t/T X) * ‖P X t‖^2)
      = (fun t => (w X).sum (fun n => (w X).sum (fun m =>
          u X n * u X m * bandIntegrand X n m t))) from funext hpt]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [MeasureTheory.integral_const_mul]
    · exact fun m _ => (hband n m).const_mul _
  · exact fun n _ => MeasureTheory.integrable_finsetSum _
      (fun m _ => (hband n m).const_mul _)


/-- `I X 1 - I X (-1)` as the double sum of `u u` times the band integrals. -/
theorem diff_eq_double_sum (hL : ExpansionIntegrable) {X : ℕ} (hX : 1000 ≤ X) :
    I X 1 - I X (-1) =
      (w X).sum (fun n => (w X).sum (fun m => u X n * u X m * bandIntegral X n m)) := by
  have hLx : Integrable (fun t : ℝ => (l (t/T X))^2) (volume.restrict (Set.Ioi (0:ℝ))) :=
    hL X hX
  set C : ℝ := (w X).sum (fun n => |u X n|) with hCdef
  have hCnonneg : 0 ≤ C := by rw [hCdef]; exact sum_abs_u_nonneg X
  have hcont_cos : Continuous (fun t : ℝ => 4*Real.pi*t/T X) := by
    have h2 : Continuous (fun t : ℝ => (4*Real.pi/T X) * t) :=
      continuous_const.mul continuous_id
    convert h2 using 1
    ext t
    ring
  -- integrability of `l² ‖P‖²`
  have hA : Integrable (fun t : ℝ => (l (t/T X))^2 * ‖P X t‖^2)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    refine integrableOn_mul_bounded hLx (fun t => ‖P X t‖^2) (continuous_norm_sq_P X) (C^2) ?_
    intro t
    rw [abs_of_nonneg (sq_nonneg _)]
    exact norm_sq_P_le X t
  -- integrability of `l² cos ‖P‖²`
  have hB : Integrable (fun t : ℝ => (l (t/T X))^2 *
      (Real.cos (4*Real.pi*t/T X) * ‖P X t‖^2)) (volume.restrict (Set.Ioi (0:ℝ))) := by
    refine integrableOn_mul_bounded hLx
      (fun t => Real.cos (4*Real.pi*t/T X) * ‖P X t‖^2)
      ((Real.continuous_cos.comp hcont_cos).mul (continuous_norm_sq_P X)) (C^2) ?_
    intro t
    calc |Real.cos (4*Real.pi*t/T X) * ‖P X t‖^2|
        = |Real.cos (4*Real.pi*t/T X)| * |‖P X t‖^2| := abs_mul _ _
      _ = |Real.cos (4*Real.pi*t/T X)| * ‖P X t‖^2 := by
            rw [abs_of_nonneg (sq_nonneg (‖P X t‖))]
      _ ≤ 1 * C^2 := mul_le_mul (Real.abs_cos_le_one _) (norm_sq_P_le X t)
            (sq_nonneg _) (by norm_num)
      _ = C^2 := one_mul _
  have h1 : Integrable (fun t : ℝ =>
      (l (t/T X))^2*(1+1*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    refine (hA.add hB).congr ?_
    filter_upwards with t
    simp only [Pi.add_apply]
    ring_nf
  have h2 : Integrable (fun t : ℝ =>
      (l (t/T X))^2*(1+(-1)*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    refine (hA.sub hB).congr ?_
    filter_upwards with t
    simp only [Pi.sub_apply]
    ring_nf
  have hdiff := I_one_sub_neg_one X h1 h2
  have hswap := integral_cos_weighted_normSq_eq_sum (X := X) hLx
  calc I X 1 - I X (-1)
      = 2 * ∫ t in Set.Ioi (0:ℝ),
          (l (t/T X))^2 * Real.cos (4*Real.pi*t/T X) * ‖P X t‖^2 := hdiff
    _ = 2 * (w X).sum (fun n => (w X).sum (fun m =>
          u X n * u X m * ∫ t in Set.Ioi (0:ℝ), bandIntegrand X n m t)) := by rw [hswap]
    _ = (w X).sum (fun n => (w X).sum (fun m =>
          u X n * u X m * bandIntegral X n m)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        unfold bandIntegral bandIntegrand
        ring

/-- **Interface theorem for TP-0013 (expansion half).**  The single analytic input is the
integrability of `l²` on the half-line (rapid decay of `k = b̂`).  Everything else — the
squared-modulus expansion, the `1 ± cos` cancellation, the exchange of the finite double
sum with the integral and the identification of the summands with `bandIntegral` — is
proved unconditionally. -/
theorem twoMomentExpansionInput_of_integrable (hL : ExpansionIntegrable) :
    TwoMomentExpansionInput := by
  intro X hX
  exact diff_eq_double_sum hL hX

/-! ## The substitution `u = t/T`: the pair kernel in frequency form -/

/-- The pair kernel: the cosine-weighted band integral as a function of the frequency
`v = X (log m - log n)` (with the `u = t/T` substitution performed). -/
def pairKernel (v : ℝ) : ℝ :=
  2 * ∫ u in Set.Ioi (0:ℝ), (l u)^2 * Real.cos (4*Real.pi*u) * Real.cos (2*Real.pi*v*u)

/-- The substitution `u = t/T` (`dt = T du`) in the band integral. -/
theorem bandIntegral_eq_T_mul_pairKernel {X : ℕ} (hX : 0 < X) (n m : ℕ) :
    bandIntegral X n m = T X * pairKernel (X * (Real.log m - Real.log n)) := by
  have hTpos : 0 < T X := T_pos hX
  have hTne : T X ≠ 0 := ne_of_gt hTpos
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi'
    (g := fun t : ℝ => (l (t/T X))^2 * Real.cos (4*Real.pi*t/T X) *
      Real.cos (t*(Real.log m - Real.log n))) (a := (0:ℝ)) hTpos
  rw [mul_zero] at hsub
  have hcongr : ∫ u in Set.Ioi (0:ℝ),
        (l ((T X * u)/T X))^2 * Real.cos (4*Real.pi*(T X * u)/T X) *
          Real.cos ((T X * u)*(Real.log m - Real.log n))
      = ∫ u in Set.Ioi (0:ℝ),
        (l u)^2 * Real.cos (4*Real.pi*u) * Real.cos (2*Real.pi*(X*(Real.log m - Real.log n))*u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [mul_div_cancel_left₀ u hTne]
    have hT : T X = 2*Real.pi*(X:ℝ) := rfl
    have harg1 : 4*Real.pi*(T X * u)/T X = 4*Real.pi*u := by
      rw [show 4*Real.pi*(T X * u)/T X = T X * (4*Real.pi*u)/T X by ring]
      exact mul_div_cancel_left₀ _ hTne
    have harg2 : (T X * u)*(Real.log m - Real.log n)
        = 2*Real.pi*(X*(Real.log m - Real.log n))*u := by
      rw [hT]; ring
    rw [harg1, harg2]
  unfold bandIntegral pairKernel
  rw [← hsub, hcongr]
  simp only [smul_eq_mul]
  ring

/-! ## The analytic core: `k = b̂`, its autocorrelation transform, and the pair kernel -/

open scoped SchwartzMap Convolution FourierTransform ContDiff

/-! ### The band bump as a Schwartz function -/

lemma bumpB_eq_glue (t : ℝ) :
    bumpB t = expNegInvGlue ((t - (-1/40)) * (1/40 - t)) := by
  rw [bumpB, bump]
  rcases lt_or_ge t (1/40) with htb | htb
  · rcases lt_or_ge (-1/40) t with hat | hat
    · rw [if_pos ⟨hat, htb⟩]
      have hpos : 0 < (t - (-1/40)) * (1/40 - t) := mul_pos (by linarith) (by linarith)
      rw [expNegInvGlue, if_neg (not_le.mpr hpos)]
      congr 1
      rw [neg_div, one_div]
    · rw [if_neg (fun h => absurd h.1 (not_lt.mpr hat))]
      exact (expNegInvGlue.zero_of_nonpos
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))).symm
  · rw [if_neg (fun h => absurd h.2 (not_lt.mpr htb))]
    exact (expNegInvGlue.zero_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))).symm

lemma bumpB_contDiff : ContDiff ℝ ∞ bumpB := by
  have h : bumpB = fun t : ℝ => expNegInvGlue ((t - (-1/40)) * (1/40 - t)) :=
    funext bumpB_eq_glue
  rw [h]
  exact (expNegInvGlue.contDiff (n := ⊤)).comp
    ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id))

lemma bumpB_continuous : Continuous bumpB := bumpB_contDiff.continuous

lemma bumpB_zero_of_notMem {t : ℝ} (ht : t ∉ Set.Icc (-1/40) (1/40)) : bumpB t = 0 := by
  rw [bumpB_eq_glue]
  apply expNegInvGlue.zero_of_nonpos
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h <;> nlinarith

lemma bumpB_hasCompactSupport : HasCompactSupport bumpB :=
  HasCompactSupport.intro (K := Set.Icc (-1/40) (1/40)) isCompact_Icc
    (fun t ht => bumpB_zero_of_notMem ht)

lemma bumpB_support_lt {t : ℝ} (ht : bumpB t ≠ 0) : |t| < 1/40 := by
  rw [bumpB_eq_glue] at ht
  have hp : 0 < (t - (-1/40)) * (1/40 - t) := by
    by_contra h
    exact ht (expNegInvGlue.zero_of_nonpos (le_of_not_gt h))
  have hsum : (t - (-1/40)) + (1/40 - t) = 1/20 := by ring
  rw [abs_lt]
  constructor <;> nlinarith [hp, hsum]

lemma bumpB_even : Function.Even bumpB := by
  intro t
  rw [bumpB_eq_glue, bumpB_eq_glue]
  congr 1
  ring

/-- Negation preserves the Lebesgue integral on `ℝ`. -/
lemma integral_comp_neg_eq {f : ℝ → ℝ} : (∫ y : ℝ, f (-y)) = ∫ y : ℝ, f y := by
  have hφ : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  calc ∫ y : ℝ, f (-y) = ∫ y : ℝ, f y ∂(Measure.map (fun x : ℝ => -x) volume) :=
        (hφ.integral_map f).symm
    _ = ∫ y : ℝ, f y := by rw [Measure.map_neg_eq_self (volume : Measure ℝ)]

/-! ### The complex Schwartz model of `b` -/

def bC : ℝ → ℂ := fun t => (bumpB t : ℂ)

lemma bC_contDiff : ContDiff ℝ ∞ bC := by
  have h : bC = fun t => Complex.ofRealCLM (bumpB t) := rfl
  rw [h]
  exact Complex.ofRealCLM.contDiff.comp bumpB_contDiff

lemma bC_continuous : Continuous bC := bC_contDiff.continuous

lemma bC_hasCompactSupport : HasCompactSupport bC :=
  HasCompactSupport.intro (K := Set.Icc (-1/40) (1/40)) isCompact_Icc
    (fun t ht => by
      have h0 : bumpB t = 0 := bumpB_zero_of_notMem ht
      simp [bC, h0])

def bS : 𝓢(ℝ, ℂ) := bC_hasCompactSupport.toSchwartzMap bC_contDiff

lemma bS_apply (t : ℝ) : (bS : ℝ → ℂ) t = (bumpB t : ℂ) := rfl

lemma bC_eq_bS : bC = (bS : ℝ → ℂ) := funext (fun t => (bS_apply t).symm)

lemma bS_integrable : Integrable bC := by
  have h : Integrable (bS : ℝ → ℂ) := SchwartzMap.integrable bS
  convert h using 1
  funext t
  exact bS_apply t

/-- The Schwartz model of the Fourier transform of `b`. -/
def kSch : 𝓢(ℝ, ℂ) := (𝓕 bS : 𝓢(ℝ, ℂ))

lemma kSch_coe : (⇑kSch : ℝ → ℂ) = 𝓕 bC := by
  refine (SchwartzMap.fourier_coe bS).trans ?_
  rw [← bC_eq_bS]

/-- The frozen cosine transform `k` is the Fourier transform of `b`. -/
lemma kSch_apply (c : ℝ) : (⇑kSch) c = (k c : ℂ) := by
  rw [kSch_coe, Real.fourier_eq']
  have hint1 : Integrable (fun v : ℝ => ((bumpB v * Real.cos (2*Real.pi*v*c) : ℝ) : ℂ)) := by
    have hbd : ∀ᵐ v : ℝ, ‖(Real.cos (2*Real.pi*v*c) : ℂ)‖ ≤ 1 := by
      filter_upwards with v
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have haesm : AEStronglyMeasurable (fun v : ℝ => (Real.cos (2*Real.pi*v*c) : ℂ)) :=
      (Complex.continuous_ofReal.comp (by continuity : Continuous fun v : ℝ => Real.cos (2*Real.pi*v*c))).aestronglyMeasurable
    have h := bS_integrable.bdd_mul haesm hbd
    convert h using 1
    funext v
    simp only [bC]
    push_cast
    ring
  have hint2 : Integrable (fun v : ℝ => ((bumpB v * Real.sin (2*Real.pi*v*c) : ℝ) : ℂ) * Complex.I) := by
    have hb : Integrable (fun v : ℝ => ((bumpB v * Real.sin (2*Real.pi*v*c) : ℝ) : ℂ)) := by
      have hbd : ∀ᵐ v : ℝ, ‖(Real.sin (2*Real.pi*v*c) : ℂ)‖ ≤ 1 := by
        filter_upwards with v
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_sin_le_one _
      have haesm : AEStronglyMeasurable (fun v : ℝ => (Real.sin (2*Real.pi*v*c) : ℂ)) :=
        (Complex.continuous_ofReal.comp (by continuity : Continuous fun v : ℝ => Real.sin (2*Real.pi*v*c))).aestronglyMeasurable
      have h := bS_integrable.bdd_mul haesm hbd
      convert h using 1
      funext v
      simp only [bC]
      push_cast
      ring
    exact hb.mul_const Complex.I
  have hpt : ∀ v : ℝ,
      Complex.exp (↑(-2*Real.pi*(inner ℝ v c))*Complex.I) • bC v
        = ((bumpB v * Real.cos (2*Real.pi*v*c) : ℝ) : ℂ)
          - ((bumpB v * Real.sin (2*Real.pi*v*c) : ℝ) : ℂ) * Complex.I := by
    intro v
    rw [Real.inner_apply, smul_eq_mul]
    rw [show (↑(-2*Real.pi*(v*c))*Complex.I : ℂ) = ((-(2*Real.pi*(v*c)) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
    have hc : Real.cos (-(2*Real.pi*(v*c))) = Real.cos (2*Real.pi*v*c) := by
      rw [show (-(2*Real.pi*(v*c))) = -(2*Real.pi*v*c) by ring, Real.cos_neg]
    have hs : Real.sin (-(2*Real.pi*(v*c))) = - Real.sin (2*Real.pi*v*c) := by
      rw [show (-(2*Real.pi*(v*c))) = -(2*Real.pi*v*c) by ring, Real.sin_neg]
    rw [hc, hs]
    simp only [bC]
    push_cast
    ring
  have hsin : ∫ v : ℝ, (bumpB v * Real.sin (2*Real.pi*v*c) : ℝ) = 0 := by
    set f : ℝ → ℝ := fun v => bumpB v * Real.sin (2*Real.pi*v*c) with hf
    have hodd : ∀ v, f (-v) = - f v := by
      intro v
      simp only [hf]
      rw [bumpB_even v]
      rw [show (2:ℝ)*Real.pi*(-v)*c = -((2:ℝ)*Real.pi*v*c) by ring, Real.sin_neg]
      ring
    have hmap : ∫ v : ℝ, f (-v) = - ∫ v : ℝ, f v := by
      rw [show (fun v => f (-v)) = (fun v => - f v) from funext hodd, integral_neg]
    have h3 : ∫ v : ℝ, f (-v) = ∫ v : ℝ, f v := integral_comp_neg_eq
    have hzero : ∫ v : ℝ, f v = 0 := by linarith
    exact hzero
  rw [funext hpt]
  rw [integral_sub hint1 hint2]
  have hc1 : (∫ a : ℝ, ((bumpB a * Real.cos (2*Real.pi*a*c) : ℝ) : ℂ))
      = ((∫ a : ℝ, bumpB a * Real.cos (2*Real.pi*a*c) : ℝ) : ℂ) := integral_ofReal
  have hs1 : (∫ a : ℝ, ((bumpB a * Real.sin (2*Real.pi*a*c) : ℝ) : ℂ))
      = ((∫ a : ℝ, bumpB a * Real.sin (2*Real.pi*a*c) : ℝ) : ℂ) := integral_ofReal
  rw [integral_mul_const, hc1, hs1, hsin]
  simp [k]

lemma exp_mul_re (x y : ℝ) :
    ((Complex.exp (↑x * Complex.I)) * ((y : ℂ) * (y : ℂ))).re = y^2 * Real.cos x := by
  rw [show ((y : ℂ) * (y : ℂ)) = ((y*y : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma k_eq_re (c : ℝ) : k c = ((⇑kSch) c).re := by
  rw [kSch_apply]
  simp

lemma k_continuous : Continuous k := by
  have h : k = fun c : ℝ => ((⇑kSch) c).re := funext k_eq_re
  rw [h]
  exact Complex.reCLM.continuous.comp kSch.continuous

lemma l_continuous : Continuous l := by
  unfold l
  exact (Real.continuous_sin.comp (by continuity : Continuous fun t : ℝ => Real.pi*t/5)).mul
    k_continuous

lemma k_even (c : ℝ) : k (-c) = k c := by
  rw [k, k]
  apply integral_congr_ae
  filter_upwards with y
  rw [show (2:ℝ)*Real.pi*y*(-c) = -((2:ℝ)*Real.pi*y*c) by ring, Real.cos_neg]

/-! ### Integrability of the squared kernel -/

set_option maxHeartbeats 1000000 in
lemma integrable_kS_sq : Integrable (fun ξ : ℝ => (⇑kSch) ξ * (⇑kSch) ξ) := by
  have h1 : Integrable (⇑kSch) := SchwartzMap.integrable kSch
  have hb : ∀ᵐ ξ : ℝ, ‖(⇑kSch) ξ‖ ≤ SchwartzMap.seminorm ℝ 0 0 kSch := by
    filter_upwards with ξ
    have h := SchwartzMap.le_seminorm (𝕜 := ℝ) 0 0 kSch ξ
    simpa using h
  exact h1.bdd_mul h1.aestronglyMeasurable hb

set_option maxHeartbeats 1000000 in
lemma integrable_k_sq : Integrable (fun x : ℝ => (k x)^2) := by
  have hz : Integrable (fun x : ℝ => ‖(⇑kSch) x‖^2) := by
    have h1 : Integrable (fun x : ℝ => ‖(⇑kSch) x * (⇑kSch) x‖) := integrable_kS_sq.norm
    refine h1.congr ?_
    filter_upwards with x
    rw [norm_mul, sq]
  refine hz.mono' (k_continuous.pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  rw [k_eq_re, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((⇑kSch) x).re)]
  have h1 : |((⇑kSch) x).re| ≤ ‖(⇑kSch) x‖ := Complex.abs_re_le_norm _
  have h2 : (0:ℝ) ≤ ‖(⇑kSch) x‖ := norm_nonneg _
  have h3 : |((⇑kSch) x).re|^2 ≤ ‖(⇑kSch) x‖^2 := by
    have h4 : (0:ℝ) ≤ |((⇑kSch) x).re| := abs_nonneg _
    nlinarith
  rwa [sq_abs] at h3

set_option maxHeartbeats 1000000 in
lemma integrable_k_sq_cos (C : ℝ) : Integrable (fun x : ℝ => (k x)^2 * Real.cos (2*Real.pi*C*x)) := by
  have hcos : Continuous (fun x : ℝ => Real.cos (2*Real.pi*C*x)) :=
    Real.continuous_cos.comp (by fun_prop : Continuous fun x : ℝ => 2*Real.pi*C*x)
  have hbd : ∀ᵐ x : ℝ, ‖Real.cos (2*Real.pi*C*x)‖ ≤ 1 := by
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have h := integrable_k_sq.bdd_mul (f := fun x : ℝ => Real.cos (2*Real.pi*C*x))
    hcos.aestronglyMeasurable hbd
  refine h.congr ?_
  filter_upwards with x
  ring

/-! ### The kernel transform `∫ k(u)² cos(2πCu) du = K(C)` -/

set_option maxHeartbeats 1000000 in
lemma kernel_whole (C : ℝ) :
    ∫ x : ℝ, (k x)^2 * Real.cos (2*Real.pi*C*x) = Kf C := by
  set gS : 𝓢(ℝ, ℂ) := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) bS bS with hgS
  have hfint : Integrable bC := bS_integrable
  have hgS_eq : (gS : ℝ → ℂ) = convolution bC bC (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext x
    rw [hgS, SchwartzMap.convolution_apply, convolution_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [bS_apply, bS_apply]
    rfl
  have hFgS : ∀ ξ : ℝ, 𝓕 (gS : ℝ → ℂ) ξ = (⇑kSch) ξ * (⇑kSch) ξ := by
    intro ξ
    rw [hgS_eq, Real.fourier_mul_convolution_eq hfint hfint ξ, kSch_coe]
  have hcont : Continuous (gS : ℝ → ℂ) := gS.continuous
  have hgint : Integrable (gS : ℝ → ℂ) := gS.integrable
  have hFint : Integrable (𝓕 (gS : ℝ → ℂ)) := by
    refine integrable_kS_sq.congr ?_
    filter_upwards with ξ
    exact (hFgS ξ).symm
  have hinv : 𝓕⁻ (𝓕 (gS : ℝ → ℂ)) = (gS : ℝ → ℂ) :=
    Continuous.fourierInv_fourier_eq hcont hgint hFint
  have hval : (gS : ℝ → ℂ) C
      = ∫ ξ : ℝ, Complex.exp (↑(2*Real.pi*(inner ℝ ξ C))*Complex.I)
          • ((⇑kSch) ξ * (⇑kSch) ξ) := by
    rw [← congr_fun hinv C, Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hFgS ξ]
  have hInt : Integrable (fun ξ : ℝ =>
      Complex.exp (↑(2*Real.pi*(inner ℝ ξ C))*Complex.I)
        • ((⇑kSch) ξ * (⇑kSch) ξ)) := by
    have hbdd : ∀ᵐ ξ : ℝ, ‖Complex.exp (↑(2*Real.pi*(inner ℝ ξ C))*Complex.I)‖ ≤ 1 := by
      filter_upwards with ξ
      rw [Complex.norm_exp]
      have hre : (↑(2*Real.pi*(inner ℝ ξ C)) * Complex.I : ℂ).re = 0 := by simp
      rw [hre, Real.exp_zero]
    have haesm : AEStronglyMeasurable (fun ξ : ℝ =>
        Complex.exp (↑(2*Real.pi*(inner ℝ ξ C))*Complex.I)) := by
      have hinner : Continuous (fun ξ : ℝ => inner ℝ ξ C) := by
        have hc : Continuous (fun ξ : ℝ => C * ξ) := continuous_const.mul continuous_id
        convert hc using 1
      have h2 : Continuous (fun ξ : ℝ => (↑(2*Real.pi*(inner ℝ ξ C)) : ℂ)) :=
        Complex.continuous_ofReal.comp (hinner.const_mul (2*Real.pi))
      exact (Complex.continuous_exp.comp (h2.mul continuous_const)).aestronglyMeasurable
    exact integrable_kS_sq.bdd_mul haesm hbdd
  have hre : (∫ ξ : ℝ, Complex.exp (↑(2*Real.pi*(inner ℝ ξ C))*Complex.I)
        • ((⇑kSch) ξ * (⇑kSch) ξ)).re
      = ∫ ξ : ℝ, (k ξ)^2 * Real.cos (2*Real.pi*C*ξ) := by
    have hsplit : (∫ ξ : ℝ, Complex.exp (↑(2*Real.pi*(inner ℝ ξ C))*Complex.I)
        • ((⇑kSch) ξ * (⇑kSch) ξ)).re
        = ∫ ξ : ℝ, (Complex.exp (↑(2*Real.pi*(inner ℝ ξ C))*Complex.I)
            • ((⇑kSch) ξ * (⇑kSch) ξ)).re := by
      have h := Complex.reCLM.integral_comp_comm hInt
      simpa [Complex.reCLM_apply] using h.symm
    rw [hsplit]
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [kSch_apply]
    rw [smul_eq_mul]
    have hkey := exp_mul_re (2*Real.pi*(inner ℝ ξ C)) (k ξ)
    rw [Real.inner_apply] at hkey
    have harg : 2*Real.pi*(ξ*C) = 2*Real.pi*C*ξ := by ring
    rw [harg] at hkey
    rw [Real.inner_apply, harg]
    exact hkey
  have hgC : (gS : ℝ → ℂ) C = ((Kf C : ℝ) : ℂ) := by
    have h1 : (gS : ℝ → ℂ) C = ∫ t : ℝ, ((bumpB t * bumpB (C - t) : ℝ) : ℂ) := by
      rw [hgS_eq, convolution_mul]
      apply integral_congr_ae
      filter_upwards with t
      simp only [bC]
      push_cast
      ring
    rw [h1, Kf]
    exact integral_ofReal
  calc ∫ ξ : ℝ, (k ξ)^2 * Real.cos (2*Real.pi*C*ξ)
      = (∫ ξ : ℝ, Complex.exp (↑(2*Real.pi*(inner ℝ ξ C))*Complex.I)
          • ((⇑kSch) ξ * (⇑kSch) ξ)).re := hre.symm
    _ = ((gS : ℝ → ℂ) C).re := by rw [← hval]
    _ = Kf C := by rw [hgC]; simp

set_option maxHeartbeats 1000000 in
/-- The kernel transform over the positive half-line. -/
lemma kernel_Ioi (C : ℝ) :
    ∫ x in Set.Ioi (0:ℝ), (k x)^2 * Real.cos (2*Real.pi*C*x) = Kf C / 2 := by
  set F : ℝ → ℝ := fun x => (k x)^2 * Real.cos (2*Real.pi*C*x) with hF
  have hfull : ∫ x : ℝ, F x = Kf C := by
    rw [hF]
    exact kernel_whole C
  have hInt : Integrable F := integrable_k_sq_cos C
  have hsplit : ∫ x : ℝ, F x
      = (∫ x in Set.Iic (0:ℝ), F x) + ∫ x in Set.Ioi (0:ℝ), F x := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hInt.integrableOn hInt.integrableOn, Set.Iic_union_Ioi, Measure.restrict_univ]
  have heven : ∫ x in Set.Iic (0:ℝ), F x = ∫ x in Set.Ioi (0:ℝ), F x := by
    have h1 : ∫ x in Set.Iic (0:ℝ), F (-x) = ∫ x in Set.Ioi (0:ℝ), F x := by
      rw [integral_comp_neg_Iic]
      simp
    rw [← h1]
    apply setIntegral_congr_fun measurableSet_Iic
    intro x _
    simp only [hF]
    rw [k_even]
    rw [show 2*Real.pi*C*(-x) = -(2*Real.pi*C*x) by ring, Real.cos_neg]
  linarith [hfull, hsplit, heven]

/-! ### The autocorrelation is even and supported in `[-1/20,1/20]` -/

set_option maxHeartbeats 1000000 in
lemma Kf_even : Function.Even Kf := by
  intro v
  rw [Kf, Kf]
  have hA : ∫ y, bumpB y * bumpB (-v - y) = ∫ y, bumpB y * bumpB (v + y) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [show -v - y = -(v + y) by ring, bumpB_even]
  have hB : ∫ y, bumpB y * bumpB (v - y) = ∫ y, bumpB y * bumpB (v + y) := by
    rw [← integral_comp_neg_eq (f := fun z => bumpB z * bumpB (v - z))]
    apply integral_congr_ae
    filter_upwards with y
    rw [show (v:ℝ) - (-y) = v + y by ring, bumpB_even]
  rw [hA, ← hB]

lemma Kf_zero_of_abs_ge {v : ℝ} (hv : (1/20:ℝ) ≤ |v|) : Kf v = 0 := by
  have hzero : ∀ y : ℝ, bumpB y * bumpB (v - y) = 0 := by
    intro y
    by_contra hne
    have h1 : bumpB y ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : bumpB (v - y) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hy := bumpB_support_lt h1
    have hvy := bumpB_support_lt h2
    have htri : |v| ≤ |y| + |v - y| := by
      calc |v| = |y + (v - y)| := by ring_nf
        _ ≤ |y| + |v - y| := abs_add_le _ _
    linarith
  rw [Kf, show (fun y => bumpB y * bumpB (v - y)) = fun _ => 0 from funext hzero]
  simp

lemma H_even : Function.Even H := by
  intro v
  have h1 : Kf (-v) = Kf v := Kf_even v
  have h2 : Kf (-v - 1/5) = Kf (v + 1/5) := by
    rw [show -v - 1/5 = -(v + 1/5) by ring]
    exact Kf_even (v + 1/5)
  have h3 : Kf (-v + 1/5) = Kf (v - 1/5) := by
    rw [show -v + 1/5 = -(v - 1/5) by ring]
    exact Kf_even (v - 1/5)
  rw [H, H, h1, h2, h3]
  ring

lemma H_zero_of_abs_ge {v : ℝ} (hv : (1/4:ℝ) ≤ |v|) : H v = 0 := by
  have h1 : Kf v = 0 := Kf_zero_of_abs_ge (by linarith)
  have h2 : Kf (v - 1/5) = 0 := by
    apply Kf_zero_of_abs_ge
    have htri : |v| ≤ |v - 1/5| + |1/5| := by
      calc |v| = |(v - 1/5) + 1/5| := by ring_nf
        _ ≤ |v - 1/5| + |1/5| := abs_add_le _ _
    have h5 : |(1/5:ℝ)| = 1/5 := abs_of_pos (by norm_num)
    rw [h5] at htri
    linarith
  have h3 : Kf (v + 1/5) = 0 := by
    apply Kf_zero_of_abs_ge
    have htri : |v| ≤ |v + 1/5| + |1/5| := by
      calc |v| = |(v + 1/5) - 1/5| := by ring_nf
        _ ≤ |v + 1/5| + |1/5| := by
              simpa using abs_add_le (v + 1/5) (-(1/5))
    have h5 : |(1/5:ℝ)| = 1/5 := abs_of_pos (by norm_num)
    rw [h5] at htri
    linarith
  rw [H, h1, h2, h3]
  ring
/-! ### Two-cosine and three-cosine kernel integrals -/

lemma continuous_cos_mul (A : ℝ) : Continuous (fun u : ℝ => Real.cos (A*u)) :=
  Real.continuous_cos.comp (continuous_const.mul continuous_id)

lemma cos_mul_cos_split (a b : ℝ) :
    Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

set_option maxHeartbeats 1000000 in
lemma integrableOn_k2_two_cos (a b : ℝ) :
    IntegrableOn (fun u : ℝ => (k u)^2 * Real.cos (2*Real.pi*a*u) * Real.cos (2*Real.pi*b*u))
      (Set.Ioi 0) := by
  have hbase : IntegrableOn (fun u : ℝ => (k u)^2) (Set.Ioi 0) := integrable_k_sq.integrableOn
  have hcont : Continuous
      (fun u : ℝ => (k u)^2 * Real.cos (2*Real.pi*a*u) * Real.cos (2*Real.pi*b*u)) := by
    have hk2 : Continuous (fun u : ℝ => (k u)^2) := k_continuous.pow 2
    have h1 : Continuous (fun u : ℝ => Real.cos (2*Real.pi*a*u)) := by continuity
    have h2 : Continuous (fun u : ℝ => Real.cos (2*Real.pi*b*u)) := by continuity
    exact (hk2.mul h1).mul h2
  refine hbase.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (k u))]
  have h1 := Real.abs_cos_le_one (2*Real.pi*a*u)
  have h2 := Real.abs_cos_le_one (2*Real.pi*b*u)
  have h0 : (0:ℝ) ≤ (k u)^2 := sq_nonneg _
  have h1' : (0:ℝ) ≤ |Real.cos (2*Real.pi*a*u)| := abs_nonneg _
  have h2' : (0:ℝ) ≤ |Real.cos (2*Real.pi*b*u)| := abs_nonneg _
  have hprod : |Real.cos (2*Real.pi*a*u)| * |Real.cos (2*Real.pi*b*u)| ≤ 1 := by
    nlinarith [mul_le_mul h1 h2 h2' zero_le_one]
  calc (k u)^2 * |Real.cos (2*Real.pi*a*u)| * |Real.cos (2*Real.pi*b*u)|
      = (k u)^2 * (|Real.cos (2*Real.pi*a*u)| * |Real.cos (2*Real.pi*b*u)|) := by ring
    _ ≤ (k u)^2 * 1 := mul_le_mul_of_nonneg_left hprod h0
    _ = (k u)^2 := by ring

set_option maxHeartbeats 2000000 in
lemma integrableOn_k2_three_cos (a b c : ℝ) :
    IntegrableOn (fun u : ℝ => (k u)^2 * Real.cos (2*Real.pi*a*u) * Real.cos (2*Real.pi*b*u)
      * Real.cos (2*Real.pi*c*u)) (Set.Ioi 0) := by
  have hbase : IntegrableOn (fun u : ℝ => (k u)^2) (Set.Ioi 0) := integrable_k_sq.integrableOn
  have hcont : Continuous (fun u : ℝ => (k u)^2 * Real.cos (2*Real.pi*a*u)
      * Real.cos (2*Real.pi*b*u) * Real.cos (2*Real.pi*c*u)) := by
    have hk2 : Continuous (fun u : ℝ => (k u)^2) := k_continuous.pow 2
    have h1 : Continuous (fun u : ℝ => Real.cos (2*Real.pi*a*u)) := continuous_cos_mul _
    have h2 : Continuous (fun u : ℝ => Real.cos (2*Real.pi*b*u)) := continuous_cos_mul _
    have h3 : Continuous (fun u : ℝ => Real.cos (2*Real.pi*c*u)) := continuous_cos_mul _
    exact ((hk2.mul h1).mul h2).mul h3
  refine hbase.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (k u))]
  have h1 := Real.abs_cos_le_one (2*Real.pi*a*u)
  have h2 := Real.abs_cos_le_one (2*Real.pi*b*u)
  have h3 := Real.abs_cos_le_one (2*Real.pi*c*u)
  have h0 : (0:ℝ) ≤ (k u)^2 := sq_nonneg _
  have h1' : (0:ℝ) ≤ |Real.cos (2*Real.pi*a*u)| := abs_nonneg _
  have h2' : (0:ℝ) ≤ |Real.cos (2*Real.pi*b*u)| := abs_nonneg _
  have h3' : (0:ℝ) ≤ |Real.cos (2*Real.pi*c*u)| := abs_nonneg _
  have h23 : |Real.cos (2*Real.pi*a*u)| * |Real.cos (2*Real.pi*b*u)| ≤ 1 := by
    nlinarith [mul_le_mul h1 h2 h2' zero_le_one]
  have h23' : (0:ℝ) ≤ |Real.cos (2*Real.pi*a*u)| * |Real.cos (2*Real.pi*b*u)| :=
    mul_nonneg h1' h2'
  have hprod : |Real.cos (2*Real.pi*a*u)| * |Real.cos (2*Real.pi*b*u)|
      * |Real.cos (2*Real.pi*c*u)| ≤ 1 := by
    have := mul_le_mul h23 h3 h3' zero_le_one
    linarith
  calc (k u)^2 * |Real.cos (2*Real.pi*a*u)| * |Real.cos (2*Real.pi*b*u)|
        * |Real.cos (2*Real.pi*c*u)|
      = (k u)^2 * (|Real.cos (2*Real.pi*a*u)| * |Real.cos (2*Real.pi*b*u)|
          * |Real.cos (2*Real.pi*c*u)|) := by ring
    _ ≤ (k u)^2 * 1 := mul_le_mul_of_nonneg_left hprod h0
    _ = (k u)^2 := by ring

set_option maxHeartbeats 1000000 in
lemma integral_k2_two_cos (a b : ℝ) :
    ∫ u in Set.Ioi (0:ℝ), (k u)^2 * Real.cos (2*Real.pi*a*u) * Real.cos (2*Real.pi*b*u)
      = (Kf (a - b) + Kf (a + b)) / 4 := by
  have hpt : ∀ u : ℝ, (k u)^2 * Real.cos (2*Real.pi*a*u) * Real.cos (2*Real.pi*b*u)
      = 1/2 * ((k u)^2 * Real.cos (2*Real.pi*(a-b)*u))
        + 1/2 * ((k u)^2 * Real.cos (2*Real.pi*(a+b)*u)) := by
    intro u
    have h := cos_mul_cos_split (2*Real.pi*a*u) (2*Real.pi*b*u)
    have e1 : 2*Real.pi*a*u - 2*Real.pi*b*u = 2*Real.pi*(a-b)*u := by ring
    have e2 : 2*Real.pi*a*u + 2*Real.pi*b*u = 2*Real.pi*(a+b)*u := by ring
    rw [e1, e2] at h
    have hrr : (k u)^2 * Real.cos (2*Real.pi*a*u) * Real.cos (2*Real.pi*b*u)
        = (k u)^2 * (Real.cos (2*Real.pi*a*u) * Real.cos (2*Real.pi*b*u)) := by ring
    rw [hrr, h]
    ring
  have h1 : IntegrableOn (fun u : ℝ => 1/2 * ((k u)^2 * Real.cos (2*Real.pi*(a-b)*u)))
      (Set.Ioi 0) := (integrable_k_sq_cos (a-b)).integrableOn.const_mul (1/2)
  have h2 : IntegrableOn (fun u : ℝ => 1/2 * ((k u)^2 * Real.cos (2*Real.pi*(a+b)*u)))
      (Set.Ioi 0) := (integrable_k_sq_cos (a+b)).integrableOn.const_mul (1/2)
  rw [funext hpt, integral_add h1 h2]
  rw [integral_const_mul, integral_const_mul, kernel_Ioi, kernel_Ioi]
  ring

set_option maxHeartbeats 1000000 in
/-- The three-cosine integral with the frozen fifth-frequency factor. -/
lemma integral_k2_fifth (v : ℝ) :
    ∫ u in Set.Ioi (0:ℝ), (k u)^2 * Real.cos (2*Real.pi*(1/5)*u)
        * Real.cos (2*Real.pi*2*u) * Real.cos (2*Real.pi*v*u)
      = 1/8 * (Kf (v - 11/5) + Kf (v - 9/5) + Kf (v + 9/5) + Kf (v + 11/5)) := by
  have hpt : ∀ u : ℝ,
      (k u)^2 * Real.cos (2*Real.pi*(1/5)*u) * Real.cos (2*Real.pi*2*u) * Real.cos (2*Real.pi*v*u)
        = 1/2 * ((k u)^2 * Real.cos (2*Real.pi*(1/5)*u) * Real.cos (2*Real.pi*(v-2)*u))
          + 1/2 * ((k u)^2 * Real.cos (2*Real.pi*(1/5)*u) * Real.cos (2*Real.pi*(v+2)*u)) := by
    intro u
    have h := cos_mul_cos_split (2*Real.pi*2*u) (2*Real.pi*v*u)
    have e1 : 2*Real.pi*2*u - 2*Real.pi*v*u = 2*Real.pi*(2-v)*u := by ring
    have e2 : 2*Real.pi*2*u + 2*Real.pi*v*u = 2*Real.pi*(2+v)*u := by ring
    rw [e1, e2] at h
    have e3 : Real.cos (2*Real.pi*(2-v)*u) = Real.cos (2*Real.pi*(v-2)*u) := by
      rw [show 2*Real.pi*(2-v)*u = -(2*Real.pi*(v-2)*u) by ring, Real.cos_neg]
    have e4 : Real.cos (2*Real.pi*(2+v)*u) = Real.cos (2*Real.pi*(v+2)*u) := by
      congr 1
      ring
    rw [e3, e4] at h
    have hrr : (k u)^2 * Real.cos (2*Real.pi*(1/5)*u) * Real.cos (2*Real.pi*2*u)
        * Real.cos (2*Real.pi*v*u)
        = (k u)^2 * Real.cos (2*Real.pi*(1/5)*u)
          * (Real.cos (2*Real.pi*2*u) * Real.cos (2*Real.pi*v*u)) := by ring
    rw [hrr, h]
    ring
  have h1 : IntegrableOn (fun u : ℝ =>
      1/2 * ((k u)^2 * Real.cos (2*Real.pi*(1/5)*u) * Real.cos (2*Real.pi*(v-2)*u)))
      (Set.Ioi 0) := (integrableOn_k2_two_cos (1/5) (v-2)).const_mul (1/2)
  have h2 : IntegrableOn (fun u : ℝ =>
      1/2 * ((k u)^2 * Real.cos (2*Real.pi*(1/5)*u) * Real.cos (2*Real.pi*(v+2)*u)))
      (Set.Ioi 0) := (integrableOn_k2_two_cos (1/5) (v+2)).const_mul (1/2)
  rw [funext hpt, integral_add h1 h2]
  rw [integral_const_mul, integral_const_mul,
    integral_k2_two_cos (1/5) (v-2), integral_k2_two_cos (1/5) (v+2)]
  have e1 : (1/5:ℝ) - (v - 2) = -(v - 11/5) := by ring
  have e2 : (1/5:ℝ) + (v - 2) = v - 9/5 := by ring
  have e3 : (1/5:ℝ) - (v + 2) = -(v + 9/5) := by ring
  have e4 : (1/5:ℝ) + (v + 2) = v + 11/5 := by ring
  rw [e1, e2, e3, e4, Kf_even (v - 11/5), Kf_even (v + 9/5)]
  ring

/-! ### The pair kernel formula -/

/-- The explicit analytic input isolated by the expansion file. -/
def PairKernelFormula : Prop := ∀ v : ℝ, pairKernel v = (H (v-2) + H (v+2))/2

set_option maxHeartbeats 1000000 in
lemma pairKernelFormula : PairKernelFormula := by
  intro v
  have hp : pairKernel v
      = ∫ u in Set.Ioi (0:ℝ), 2 * ((l u)^2 * Real.cos (2*Real.pi*2*u) * Real.cos (2*Real.pi*v*u)) := by
    rw [pairKernel, ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    rw [show (4:ℝ)*Real.pi*u = 2*Real.pi*2*u by ring]
  rw [hp]
  have hpt : ∀ u : ℝ,
      2 * ((l u)^2 * Real.cos (2*Real.pi*2*u) * Real.cos (2*Real.pi*v*u))
        = (k u)^2 * Real.cos (2*Real.pi*2*u) * Real.cos (2*Real.pi*v*u)
          - (k u)^2 * Real.cos (2*Real.pi*(1/5)*u) * Real.cos (2*Real.pi*2*u)
            * Real.cos (2*Real.pi*v*u) := by
    intro u
    have hsin : 2 * (Real.sin (Real.pi*u/5))^2
        = 1 - Real.cos (2*Real.pi*(1/5)*u) := by
      have h2 := Real.cos_two_mul (Real.pi*u/5)
      have hs := Real.sin_sq (Real.pi*u/5)
      have harg : 2*(Real.pi*u/5) = 2*Real.pi*(1/5)*u := by ring
      rw [harg] at h2
      linarith
    unfold l
    calc 2 * ((Real.sin (Real.pi*u/5) * k u)^2 * Real.cos (2*Real.pi*2*u)
          * Real.cos (2*Real.pi*v*u))
        = (2 * (Real.sin (Real.pi*u/5))^2)
            * ((k u)^2 * Real.cos (2*Real.pi*2*u) * Real.cos (2*Real.pi*v*u)) := by ring
      _ = (1 - Real.cos (2*Real.pi*(1/5)*u))
            * ((k u)^2 * Real.cos (2*Real.pi*2*u) * Real.cos (2*Real.pi*v*u)) := by rw [hsin]
      _ = _ := by ring
  have h1 : IntegrableOn (fun u : ℝ => (k u)^2 * Real.cos (2*Real.pi*2*u) * Real.cos (2*Real.pi*v*u))
      (Set.Ioi 0) := integrableOn_k2_two_cos 2 v
  have h2 : IntegrableOn (fun u : ℝ => (k u)^2 * Real.cos (2*Real.pi*(1/5)*u)
      * Real.cos (2*Real.pi*2*u) * Real.cos (2*Real.pi*v*u)) (Set.Ioi 0) :=
    integrableOn_k2_three_cos (1/5) 2 v
  rw [funext hpt, integral_sub h1 h2, integral_k2_two_cos 2 v, integral_k2_fifth v]
  rw [show (2:ℝ) - v = -(v - 2) by ring, Kf_even (v - 2)]
  rw [show (2:ℝ) + v = v + 2 by ring]
  rw [H, H]
  have e1 : (v:ℝ) - 2 - 1/5 = v - 11/5 := by ring
  have e2 : (v:ℝ) - 2 + 1/5 = v - 9/5 := by ring
  have e3 : (v:ℝ) + 2 - 1/5 = v + 9/5 := by ring
  have e4 : (v:ℝ) + 2 + 1/5 = v + 11/5 := by ring
  rw [e1, e2, e3, e4]
  ring

/-! ### The expansion integrability input -/

set_option maxHeartbeats 1000000 in
lemma expansionIntegrable : ExpansionIntegrable := by
  intro X hX
  have hXpos : 0 < X := by omega
  have hTpos : 0 < T X := T_pos hXpos
  have hk : Integrable (fun t : ℝ => (k (t / T X))^2)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    have h1 : IntegrableOn (fun t : ℝ => (k (t * (T X)⁻¹))^2) (Set.Ioi (0:ℝ)) :=
      (integrableOn_Ioi_comp_mul_right_iff (f := fun u : ℝ => (k u)^2) (c := (0:ℝ))
        (a := (T X)⁻¹) (inv_pos.mpr hTpos)).mpr
        (by simpa using integrable_k_sq.integrableOn)
    have h2 : (fun t : ℝ => (k (t / T X))^2) = (fun t : ℝ => (k (t * (T X)⁻¹))^2) := by
      funext t
      rw [div_eq_mul_inv]
    rw [h2]
    exact h1
  refine hk.mono' ?_ ?_
  · exact ((l_continuous.comp (continuous_id.div_const (T X))).pow 2).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs]
    have hs : (Real.sin (Real.pi*(t/T X)/5))^2 ≤ 1 := by
      have h1 := Real.abs_sin_le_one (Real.pi*(t/T X)/5)
      have h2 := abs_nonneg (Real.sin (Real.pi*(t/T X)/5))
      have h3 : |Real.sin (Real.pi*(t/T X)/5)|^2 ≤ 1 := by nlinarith
      rwa [sq_abs] at h3
    have hk2 : (0:ℝ) ≤ (k (t/T X))^2 := sq_nonneg _
    have hsq : (l (t/T X))^2 = (Real.sin (Real.pi*(t/T X)/5))^2 * (k (t/T X))^2 := by
      unfold l
      ring
    rw [hsq, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (Real.pi*(t/T X)/5))),
      abs_of_nonneg hk2]
    nlinarith [hs, hk2]
/-! ### Window data on the real line -/

lemma window_real {X n : ℕ} (hn : n ∈ w X) :
    (X:ℝ) ≤ (n:ℝ) ∧ 50*(n:ℝ) < 51*(X:ℝ) ∧ (0:ℝ) < (n:ℝ) := by
  obtain ⟨h1, h2⟩ := mem_window_bounds hn
  have h2' : ((50*n : ℕ):ℝ) < ((51*X : ℕ):ℝ) := by exact_mod_cast h2
  push_cast at h2'
  exact ⟨by exact_mod_cast (le_of_lt h1), h2', by exact_mod_cast (by omega : 0 < n)⟩

/-! ### The three band ranges (frozen unit band, outer band, shift two) -/

set_option maxHeartbeats 1000000 in
lemma fX_unit {x n : ℝ} (hx : 1000 ≤ x) (hxn : x ≤ n) (hwin : 50*n ≤ 51*x) :
    1/4 < fX x n 1 ∧ fX x n 1 < 7/4 := by
  unfold fX
  have hn : 0 < n := by linarith
  have hx0 : 0 < x := by linarith
  have hlog_lower : 2/(2*n+1) ≤ Real.log (1 + 1/n) := by
    have h := Real.le_log_one_add_of_nonneg (x := 1/n) (by positivity)
    have he : (2:ℝ) * (1/n) / ((1/n) + 2) = 2/(2*n+1) := by
      field_simp
      ring
    rwa [he] at h
  have hlog_upper : Real.log (1 + 1/n) ≤ 1/n := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/n by positivity)
    simpa using h
  constructor
  · have h1 : x * (2/(2*n+1)) ≤ x * Real.log (1 + 1/n) :=
      mul_le_mul_of_nonneg_left hlog_lower (le_of_lt hx0)
    have h2 : x * (2/(2*n+1)) = 2*x/(2*n+1) := by ring
    rw [h2] at h1
    have h3 : (1:ℝ)/4 < 2*x/(2*n+1) := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2*n + 1)]
      nlinarith
    linarith
  · have h1 : x * Real.log (1 + 1/n) ≤ x * (1/n) :=
      mul_le_mul_of_nonneg_left hlog_upper (le_of_lt hx0)
    have h2 : x * (1/n) = x/n := by ring
    rw [h2] at h1
    have h3 : x/n ≤ 1 := by
      rw [div_le_one hn]
      linarith
    linarith

set_option maxHeartbeats 1000000 in
lemma fX_outer {x n : ℝ} {j : ℕ} (hx : 1000 ≤ x) (hxn : x ≤ n) (hwin : 50*n ≤ 51*x)
    (hj : 3 ≤ j) : 9/4 < fX x n (j:ℝ) := by
  unfold fX
  have hn : 0 < n := by linarith
  have hx0 : 0 < x := by linarith
  have hj3 : (3:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hmono : Real.log (1 + 3/n) ≤ Real.log (1 + (j:ℝ)/n) := by
    apply Real.log_le_log (by positivity)
    have hle : (3:ℝ)/n ≤ (j:ℝ)/n := div_le_div_of_nonneg_right hj3 (le_of_lt hn)
    linarith
  have hlog3 : 6/(2*n+3) ≤ Real.log (1 + 3/n) := by
    have h := Real.le_log_one_add_of_nonneg (x := 3/n) (by positivity)
    have he : (2:ℝ) * (3/n) / ((3/n) + 2) = 6/(2*n+3) := by
      field_simp
      ring
    rwa [he] at h
  have hstep : 6*x/(2*n+3) ≤ x * Real.log (1 + (j:ℝ)/n) := by
    have ha : 6*x/(2*n+3) = x * (6/(2*n+3)) := by ring
    rw [ha]
    exact le_trans (mul_le_mul_of_nonneg_left hlog3 (le_of_lt hx0))
      (mul_le_mul_of_nonneg_left hmono (le_of_lt hx0))
  have h4 : (9:ℝ)/4 < 6*x/(2*n+3) := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2*n + 3)]
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- The twin shift `f(X,n,2) - 2` lands in `[-1/25, 0]`. -/
lemma fX_shift2 {X n : ℕ} (hX : 1000 ≤ X) (hn : n ∈ w X) (hn2 : n+2 ∈ w X) :
    fX (X:ℝ) (n:ℝ) 2 - 2 ∈ Set.Icc (-(1/25) : ℝ) 0 := by
  obtain ⟨hXn, -⟩ := mem_window_bounds hn
  obtain ⟨-, h2⟩ := mem_window_bounds hn2
  have hXpos : (0:ℝ) < (X:ℝ) := by positivity
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hcast : (50:ℝ)*((n:ℝ)+2) < 51*(X:ℝ) := by
    have hh : ((50*(n+2) : ℕ) : ℝ) < ((51*X : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at hh
    linarith
  have hXn' : (X:ℝ) < (n:ℝ) := by exact_mod_cast hXn
  have hu : (0:ℝ) < 1 + 2/(n:ℝ) := by positivity
  have hub : Real.log (1 + 2/(n:ℝ)) ≤ 2/(n:ℝ) := by
    have h := Real.log_le_sub_one_of_pos hu
    linarith
  have hlb : 2/((n:ℝ)+2) ≤ Real.log (1 + 2/(n:ℝ)) := by
    have h := Real.one_sub_inv_le_log_of_pos hu
    have heq : (1:ℝ) - (1 + 2/(n:ℝ))⁻¹ = 2/((n:ℝ)+2) := by
      field_simp
      ring
    linarith [h, heq]
  constructor
  · simp only [fX]
    have hpos2 : (0:ℝ) < (n:ℝ)+2 := by linarith
    have h2' : (49:ℝ)/25 < (X:ℝ) * (2/((n:ℝ)+2)) := by
      rw [mul_div_assoc']
      rw [lt_div_iff₀ hpos2]
      nlinarith [hcast, hXn', hXpos]
    have h1' : (X:ℝ) * (2/((n:ℝ)+2)) ≤ (X:ℝ) * Real.log (1 + 2/(n:ℝ)) :=
      mul_le_mul_of_nonneg_left hlb hXpos.le
    linarith
  · simp only [fX]
    have h1' : (X:ℝ) * Real.log (1 + 2/(n:ℝ)) ≤ (X:ℝ)*(2/(n:ℝ)) :=
      mul_le_mul_of_nonneg_left hub hXpos.le
    have h2' : (X:ℝ) * (2/(n:ℝ)) < 2 := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (show (0:ℝ) < (n:ℝ) by linarith)]
      nlinarith [hXn', hXpos]
    linarith

/-! ### The log-difference as a frozen `fX` -/

lemma log_diff_eq_fX {X n m : ℕ} (hn : 0 < n) (hnm : n < m) :
    (X:ℝ) * (Real.log m - Real.log n) = fX (X:ℝ) (n:ℝ) (((m - n : ℕ)):ℝ) := by
  rw [fX]
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hcast : (m:ℝ) = (n:ℝ) + (((m - n : ℕ)):ℝ) := by
    rw [Nat.cast_sub (le_of_lt hnm)]
    push_cast
    ring
  have hlog : Real.log (m:ℝ) - Real.log (n:ℝ)
      = Real.log (1 + (((m - n : ℕ)):ℝ)/(n:ℝ)) := by
    rw [← Real.log_div (ne_of_gt hm0) (ne_of_gt hn0)]
    congr 1
    rw [hcast]
    field_simp
  rw [hlog]

lemma log_diff_eq_neg_fX {X n m : ℕ} (hm : 0 < m) (hnm : m < n) :
    (X:ℝ) * (Real.log m - Real.log n) = - fX (X:ℝ) (m:ℝ) (((n - m : ℕ)):ℝ) := by
  have h := log_diff_eq_fX (X := X) hm hnm
  have h2 : (X:ℝ) * (Real.log m - Real.log n)
      = - ((X:ℝ) * (Real.log n - Real.log m)) := by ring
  rw [h2, h]

lemma A_shift2 {X n : ℕ} (hn : 0 < n) :
    (X:ℝ) * (Real.log ((n+2:ℕ):ℝ) - Real.log (n:ℝ)) = fX (X:ℝ) (n:ℝ) 2 := by
  have h := log_diff_eq_fX (X := X) hn (show n < n + 2 by omega)
  have hcast : ((((n + 2) - n : ℕ)):ℝ) = 2 := by
    rw [show ((n + 2) - n : ℕ) = 2 by omega]
    norm_num
  rw [hcast] at h
  exact h

lemma A_shift2_neg {X m : ℕ} (hm : 0 < m) :
    (X:ℝ) * (Real.log (m:ℝ) - Real.log ((m+2:ℕ):ℝ)) = - fX (X:ℝ) (m:ℝ) 2 := by
  have h := log_diff_eq_neg_fX (X := X) hm (show m < m + 2 by omega)
  have hcast : ((((m + 2) - m : ℕ)):ℝ) = 2 := by
    rw [show ((m + 2) - m : ℕ) = 2 by omega]
    norm_num
  rw [hcast] at h
  exact h

lemma A_shift1 {X n : ℕ} (hn : 0 < n) :
    (X:ℝ) * (Real.log ((n+1:ℕ):ℝ) - Real.log (n:ℝ)) = fX (X:ℝ) (n:ℝ) 1 := by
  have h := log_diff_eq_fX (X := X) hn (show n < n + 1 by omega)
  have hcast : ((((n + 1) - n : ℕ)):ℝ) = 1 := by
    rw [show ((n + 1) - n : ℕ) = 1 by omega]
    norm_num
  rw [hcast] at h
  exact h

lemma A_shift1_neg {X m : ℕ} (hm : 0 < m) :
    (X:ℝ) * (Real.log (m:ℝ) - Real.log ((m+1:ℕ):ℝ)) = - fX (X:ℝ) (m:ℝ) 1 := by
  have h := log_diff_eq_neg_fX (X := X) hm (show m < m + 1 by omega)
  have hcast : ((((m + 1) - m : ℕ)):ℝ) = 1 := by
    rw [show ((m + 1) - m : ℕ) = 1 by omega]
    norm_num
  rw [hcast] at h
  exact h

/-! ### Pointwise collapse of the pair kernel -/

set_option maxHeartbeats 1000000 in
lemma pairKernel_collapse {X n m : ℕ} (hX : 1000 ≤ X) (hn : n ∈ w X) (hm : m ∈ w X) :
    (H ((X:ℝ) * (Real.log m - Real.log n) - 2) + H ((X:ℝ) * (Real.log m - Real.log n) + 2))/2
      = (if m = n+2 then H (fX (X:ℝ) (n:ℝ) 2 - 2)/2 else 0)
        + (if n = m+2 then H (fX (X:ℝ) (m:ℝ) 2 - 2)/2 else 0) := by
  have hXr : (1000:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  obtain ⟨hXn, hwin_n, hnpos⟩ := window_real hn
  obtain ⟨hXm, hwin_m, hmpos⟩ := window_real hm
  have hwin_n' : 50*(n:ℝ) ≤ 51*(X:ℝ) := le_of_lt hwin_n
  have hwin_m' : 50*(m:ℝ) ≤ 51*(X:ℝ) := le_of_lt hwin_m
  have hn0 : 0 < n := by exact_mod_cast hnpos
  have hm0 : 0 < m := by exact_mod_cast hmpos
  rcases lt_trichotomy m n with hlt | heq | hgt
  · by_cases h2 : n = m + 2
    · subst h2
      have hA : (X:ℝ) * (Real.log (m:ℝ) - Real.log ((m+2:ℕ):ℝ)) = - fX (X:ℝ) (m:ℝ) 2 :=
        A_shift2_neg hm0
      have hsh := fX_shift2 hX hm (by omega : m + 2 ∈ w X)
      have hz : H (fX (X:ℝ) (m:ℝ) 2 + 2) = 0 := by
        apply H_zero_of_abs_ge
        rw [abs_of_pos (by linarith [hsh.1])]
        linarith [hsh.1]
      have h1 : H (- fX (X:ℝ) (m:ℝ) 2 - 2) = H (fX (X:ℝ) (m:ℝ) 2 + 2) := by
        rw [show - fX (X:ℝ) (m:ℝ) 2 - 2 = - (fX (X:ℝ) (m:ℝ) 2 + 2) by ring]
        exact H_even _
      have h2' : H (- fX (X:ℝ) (m:ℝ) 2 + 2) = H (fX (X:ℝ) (m:ℝ) 2 - 2) := by
        rw [show - fX (X:ℝ) (m:ℝ) 2 + 2 = - (fX (X:ℝ) (m:ℝ) 2 - 2) by ring]
        exact H_even _
      rw [hA, h1, h2', hz]
      rw [if_neg (by omega), if_pos rfl]
      ring
    · by_cases h1 : n = m + 1
      · subst h1
        have hA : (X:ℝ) * (Real.log (m:ℝ) - Real.log ((m+1:ℕ):ℝ)) = - fX (X:ℝ) (m:ℝ) 1 :=
          A_shift1_neg hm0
        have hb := fX_unit hXr hXm hwin_m'
        have hz1 : H (- fX (X:ℝ) (m:ℝ) 1 - 2) = 0 := by
          apply H_zero_of_abs_ge
          rw [show - fX (X:ℝ) (m:ℝ) 1 - 2 = - (fX (X:ℝ) (m:ℝ) 1 + 2) by ring, abs_neg,
            abs_of_pos (by linarith [hb.1])]
          linarith [hb.1]
        have hz2 : H (- fX (X:ℝ) (m:ℝ) 1 + 2) = 0 := by
          apply H_zero_of_abs_ge
          rw [show - fX (X:ℝ) (m:ℝ) 1 + 2 = - (fX (X:ℝ) (m:ℝ) 1 - 2) by ring, abs_neg,
            abs_of_neg (by linarith [hb.2])]
          linarith [hb.2]
        rw [hA, hz1, hz2]
        rw [if_neg (by omega), if_neg (by omega)]
        ring
      · have hge : m + 3 ≤ n := by omega
        have hA : (X:ℝ) * (Real.log (m:ℝ) - Real.log (n:ℝ))
            = - fX (X:ℝ) (m:ℝ) (((n - m : ℕ)):ℝ) := log_diff_eq_neg_fX hm0 hlt
        have hj : 3 ≤ (n - m : ℕ) := by omega
        have hb := fX_outer hXr hXm hwin_m' hj
        have hz1 : H (- fX (X:ℝ) (m:ℝ) (((n - m : ℕ)):ℝ) - 2) = 0 := by
          apply H_zero_of_abs_ge
          rw [show - fX (X:ℝ) (m:ℝ) (((n - m : ℕ)):ℝ) - 2
            = - (fX (X:ℝ) (m:ℝ) (((n - m : ℕ)):ℝ) + 2) by ring, abs_neg,
            abs_of_pos (by linarith)]
          linarith
        have hz2 : H (- fX (X:ℝ) (m:ℝ) (((n - m : ℕ)):ℝ) + 2) = 0 := by
          apply H_zero_of_abs_ge
          rw [show - fX (X:ℝ) (m:ℝ) (((n - m : ℕ)):ℝ) + 2
            = - (fX (X:ℝ) (m:ℝ) (((n - m : ℕ)):ℝ) - 2) by ring, abs_neg,
            abs_of_pos (by linarith)]
          linarith
        rw [hA, hz1, hz2]
        rw [if_neg (by omega), if_neg (by omega)]
        ring
  · subst heq
    have hA : (X:ℝ) * (Real.log (m:ℝ) - Real.log (m:ℝ)) = 0 := by ring
    have hz1 : H (0 - 2) = 0 := by
      apply H_zero_of_abs_ge
      norm_num
    have hz2 : H (0 + 2) = 0 := by
      apply H_zero_of_abs_ge
      norm_num
    rw [hA, hz1, hz2]
    rw [if_neg (by omega)]
    ring
  · by_cases h2 : m = n + 2
    · subst h2
      have hA : (X:ℝ) * (Real.log ((n+2:ℕ):ℝ) - Real.log (n:ℝ)) = fX (X:ℝ) (n:ℝ) 2 :=
        A_shift2 hn0
      have hsh := fX_shift2 hX hn (by omega : n + 2 ∈ w X)
      have hz : H (fX (X:ℝ) (n:ℝ) 2 + 2) = 0 := by
        apply H_zero_of_abs_ge
        rw [abs_of_pos (by linarith [hsh.1])]
        linarith [hsh.1]
      rw [hA, hz]
      rw [if_pos rfl, if_neg (by omega)]
      ring
    · by_cases h1 : m = n + 1
      · subst h1
        have hA : (X:ℝ) * (Real.log ((n+1:ℕ):ℝ) - Real.log (n:ℝ)) = fX (X:ℝ) (n:ℝ) 1 :=
          A_shift1 hn0
        have hb := fX_unit hXr hXn hwin_n'
        have hz1 : H (fX (X:ℝ) (n:ℝ) 1 - 2) = 0 := by
          apply H_zero_of_abs_ge
          rw [abs_of_neg (by linarith [hb.2])]
          linarith [hb.2]
        have hz2 : H (fX (X:ℝ) (n:ℝ) 1 + 2) = 0 := by
          apply H_zero_of_abs_ge
          rw [abs_of_pos (by linarith [hb.1])]
          linarith [hb.1]
        rw [hA, hz1, hz2]
        rw [if_neg (by omega), if_neg (by omega)]
        ring
      · have hge : n + 3 ≤ m := by omega
        have hA : (X:ℝ) * (Real.log (m:ℝ) - Real.log (n:ℝ))
            = fX (X:ℝ) (n:ℝ) (((m - n : ℕ)):ℝ) := log_diff_eq_fX hn0 hgt
        have hj : 3 ≤ (m - n : ℕ) := by omega
        have hb := fX_outer hXr hXn hwin_n' hj
        have hz1 : H (fX (X:ℝ) (n:ℝ) (((m - n : ℕ)):ℝ) - 2) = 0 := by
          apply H_zero_of_abs_ge
          rw [abs_of_pos (by linarith)]
          linarith
        have hz2 : H (fX (X:ℝ) (n:ℝ) (((m - n : ℕ)):ℝ) + 2) = 0 := by
          apply H_zero_of_abs_ge
          rw [abs_of_pos (by linarith)]
          linarith
        rw [hA, hz1, hz2]
        rw [if_neg (by omega), if_neg (by omega)]
        ring

/-! ### The finite-sum collapse -/

set_option maxHeartbeats 1000000 in
lemma sum_collapse_pair (X : ℕ) :
    (w X).sum (fun n => (w X).sum (fun m => u X n * u X m *
        ((if m = n+2 then H (fX (X:ℝ) (n:ℝ) 2 - 2)/2 else 0)
          + (if n = m+2 then H (fX (X:ℝ) (m:ℝ) 2 - 2)/2 else 0))))
      = ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n =>
          u X n * u X (n+2) * H (fX (X:ℝ) (n:ℝ) 2 - 2)) := by
  have hsplit : (w X).sum (fun n => (w X).sum (fun m => u X n * u X m *
        ((if m = n+2 then H (fX (X:ℝ) (n:ℝ) 2 - 2)/2 else 0)
          + (if n = m+2 then H (fX (X:ℝ) (m:ℝ) 2 - 2)/2 else 0))))
      = (w X).sum (fun n => (w X).sum (fun m => u X n * u X m *
            (if m = n+2 then H (fX (X:ℝ) (n:ℝ) 2 - 2)/2 else 0)))
        + (w X).sum (fun n => (w X).sum (fun m => u X n * u X m *
            (if n = m+2 then H (fX (X:ℝ) (m:ℝ) 2 - 2)/2 else 0))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hA1 : (w X).sum (fun n => (w X).sum (fun m => u X n * u X m *
            (if m = n+2 then H (fX (X:ℝ) (n:ℝ) 2 - 2)/2 else 0)))
      = (w X).sum (fun n => if n+2 ∈ w X then
            u X n * u X (n+2) * (H (fX (X:ℝ) (n:ℝ) 2 - 2)/2) else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hterm : ∀ m : ℕ, u X n * u X m * (if m = n+2 then H (fX (X:ℝ) (n:ℝ) 2 - 2)/2 else 0)
        = if m = n+2 then (u X n * u X (n+2) * (H (fX (X:ℝ) (n:ℝ) 2 - 2)/2)) else 0 := by
      intro m
      by_cases h : m = n + 2
      · subst h
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_ite_eq']
  have hA2 : (w X).sum (fun n => (w X).sum (fun m => u X n * u X m *
            (if n = m+2 then H (fX (X:ℝ) (m:ℝ) 2 - 2)/2 else 0)))
      = (w X).sum (fun m => if m+2 ∈ w X then
            u X (m+2) * u X m * (H (fX (X:ℝ) (m:ℝ) 2 - 2)/2) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    have hterm : ∀ n : ℕ, u X n * u X m * (if n = m+2 then H (fX (X:ℝ) (m:ℝ) 2 - 2)/2 else 0)
        = if n = m+2 then (u X (m+2) * u X m * (H (fX (X:ℝ) (m:ℝ) 2 - 2)/2)) else 0 := by
      intro n
      by_cases h : n = m + 2
      · subst h
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_ite_eq']
  rw [hsplit, hA1, hA2]
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : n + 2 ∈ w X
  · rw [if_pos h, if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h, if_neg h]
    ring

/-! ### The frozen two-moment identity -/

set_option maxHeartbeats 1000000 in
theorem twoMomentIdentity : TwoMomentIdentity := by
  intro X hX
  have hXpos : 0 < X := by omega
  have hL := expansionIntegrable
  rw [diff_eq_double_sum hL hX]
  have hstep : ∀ n ∈ w X, ∀ m ∈ w X,
      u X n * u X m * bandIntegral X n m
        = T X * (u X n * u X m * ((if m = n+2 then H (fX (X:ℝ) (n:ℝ) 2 - 2)/2 else 0)
            + (if n = m+2 then H (fX (X:ℝ) (m:ℝ) 2 - 2)/2 else 0))) := by
    intro n hn m hm
    rw [bandIntegral_eq_T_mul_pairKernel hXpos n m, pairKernelFormula]
    rw [pairKernel_collapse hX hn hm]
    ring
  rw [Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => hstep n hn m hm))]
  have hT : (w X).sum (fun n => (w X).sum (fun m =>
        T X * (u X n * u X m * ((if m = n+2 then H (fX (X:ℝ) (n:ℝ) 2 - 2)/2 else 0)
            + (if n = m+2 then H (fX (X:ℝ) (m:ℝ) 2 - 2)/2 else 0)))))
      = T X * (w X).sum (fun n => (w X).sum (fun m =>
          u X n * u X m * ((if m = n+2 then H (fX (X:ℝ) (n:ℝ) 2 - 2)/2 else 0)
            + (if n = m+2 then H (fX (X:ℝ) (m:ℝ) 2 - 2)/2 else 0)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
  rw [hT, sum_collapse_pair]
/-! ## The core sub-window and the two pointwise comparisons -/

/-- The twin-pair sub-window of the frozen window. -/
def core (X : ℕ) : Finset ℕ := (w X).filter (fun n => n+2 ∈ w X)

/-- On the twin sub-window, the moment weight is at most the normalized arithmetic weight. -/
lemma uu_le_v_div {X n : ℕ} (hX : 1000 ≤ X) (hn : n ∈ w X) (_hn2 : n+2 ∈ w X) :
    u X n * u X (n+2) ≤ v n / (X:ℝ) := by
  obtain ⟨hXn, -⟩ := mem_window_bounds hn
  have hXpos : (0:ℝ) < (X:ℝ) := by positivity
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hXn' : (X:ℝ) < (n:ℝ) := by exact_mod_cast hXn
  have hLam : 0 ≤ ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) :=
    v_nonneg n
  have hden : (X:ℝ) ≤ Real.sqrt (n:ℝ) * Real.sqrt ((n+2:ℕ):ℝ) := by
    rw [← Real.sqrt_mul (le_of_lt hnpos)]
    rw [← Real.sqrt_mul_self hXpos.le]
    apply Real.sqrt_le_sqrt
    push_cast
    nlinarith [hXn', hnpos]
  have hprod : W ((n:ℝ)/X) * W (((n+2:ℕ):ℝ)/X) ≤ 1 := by
    have h1 := W_le_one ((n:ℝ)/X)
    have h2 := W_le_one (((n+2:ℕ):ℝ)/X)
    have h3 := W_nonneg ((n:ℝ)/X)
    have h4 := W_nonneg (((n+2:ℕ):ℝ)/X)
    nlinarith
  have hnum : ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) *
      (W ((n:ℝ)/X) * W (((n+2:ℕ):ℝ)/X)) ≤
      ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) := by
    calc _ ≤ ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) * 1 :=
          mul_le_mul_of_nonneg_left hprod hLam
      _ = _ := by ring
  have hkey : u X n * u X (n+2) =
      (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) *
        (W ((n:ℝ)/X) * W (((n+2:ℕ):ℝ)/X))) /
      (Real.sqrt (n:ℝ) * Real.sqrt ((n+2:ℕ):ℝ)) := by
    rw [u, u, div_mul_div_comm]
    congr 1
    ring
  rw [hkey, div_le_div_iff₀ (by positivity) hXpos, v]
  calc ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) *
        (W ((n:ℝ)/X) * W (((n+2:ℕ):ℝ)/X)) * (X:ℝ)
      ≤ ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) * (X:ℝ) :=
        mul_le_mul_of_nonneg_right hnum hXpos.le
    _ ≤ ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) *
        (Real.sqrt (n:ℝ) * Real.sqrt ((n+2:ℕ):ℝ)) :=
        mul_le_mul_of_nonneg_left hden hLam

/-- The fixed relative core of the frozen window on which the weight `W` is bounded
below by a positive constant independent of `X`. -/
def coreBox (X : ℕ) : Finset ℕ :=
  (core X).filter (fun n => 1005*X ≤ 1000*n ∧ 1000*(n+2) ≤ 1010*X)

/-- On the fixed relative core, the moment weight is bounded below by a positive
constant times the normalized arithmetic weight. -/
lemma uu_ge_of_box {X n : ℕ} (hX : 1000 ≤ X) (hn : n ∈ coreBox X) :
    Real.exp (-(40000:ℝ)) * (100/101) * (v n / (X:ℝ)) ≤ u X n * u X (n+2) := by
  obtain ⟨hncore, hnbox⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnw, _hn2w⟩ := Finset.mem_filter.mp hncore
  obtain ⟨hXn, -⟩ := mem_window_bounds hnw
  obtain ⟨hb1, hb2⟩ := hnbox
  have hXpos : (0:ℝ) < (X:ℝ) := by positivity
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hb1R : (1005:ℝ)*(X:ℝ) ≤ 1000*(n:ℝ) := by
    have hh : ((1005*X : ℕ) : ℝ) ≤ ((1000*n : ℕ) : ℝ) := by exact_mod_cast hb1
    push_cast at hh
    linarith
  have hb2R : (1000:ℝ)*((n:ℝ)+2) ≤ 1010*(X:ℝ) := by
    have hh : ((1000*(n+2) : ℕ) : ℝ) ≤ ((1010*X : ℕ) : ℝ) := by exact_mod_cast hb2
    push_cast at hh
    linarith
  have hLam : 0 ≤ ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) :=
    v_nonneg n
  have ht1 : (1005/1000 : ℝ) ≤ (n:ℝ)/X := by
    rw [le_div_iff₀ hXpos]; nlinarith
  have ht1' : (n:ℝ)/X ≤ 1010/1000 := by
    rw [div_le_iff₀ hXpos]; nlinarith
  have ht2 : (1005/1000 : ℝ) ≤ ((n+2:ℕ):ℝ)/X := by
    rw [le_div_iff₀ hXpos]; push_cast; nlinarith
  have ht2' : ((n+2:ℕ):ℝ)/X ≤ 1010/1000 := by
    rw [div_le_iff₀ hXpos]; push_cast; nlinarith
  have hW1 : Real.exp (-(20000:ℝ)) ≤ W ((n:ℝ)/X) := W_ge_of_mem ht1 ht1'
  have hW2 : Real.exp (-(20000:ℝ)) ≤ W (((n+2:ℕ):ℝ)/X) := W_ge_of_mem ht2 ht2'
  have hexp : Real.exp (-(20000:ℝ)) * Real.exp (-(20000:ℝ)) = Real.exp (-(40000:ℝ)) := by
    rw [← Real.exp_add]; norm_num
  have hprod : Real.exp (-(40000:ℝ)) ≤ W ((n:ℝ)/X) * W (((n+2:ℕ):ℝ)/X) := by
    rw [← hexp]
    exact mul_le_mul hW1 hW2 (le_of_lt (Real.exp_pos _)) (W_nonneg _)
  have hden : Real.sqrt (n:ℝ) * Real.sqrt ((n+2:ℕ):ℝ) ≤ (1010/1000)*(X:ℝ) := by
    have h1 : Real.sqrt (n:ℝ) * Real.sqrt ((n+2:ℕ):ℝ) = Real.sqrt ((n:ℝ)*((n+2:ℕ):ℝ)) := by
      rw [Real.sqrt_mul (le_of_lt hnpos)]
    rw [h1]
    have h3 : Real.sqrt (((n:ℝ)+2)^2) = (n:ℝ)+2 := Real.sqrt_sq (by linarith)
    calc Real.sqrt ((n:ℝ)*((n+2:ℕ):ℝ)) ≤ Real.sqrt (((n:ℝ)+2)^2) := by
          apply Real.sqrt_le_sqrt
          push_cast
          nlinarith
      _ = (n:ℝ)+2 := h3
      _ ≤ (1010/1000)*(X:ℝ) := by nlinarith
  have hDpos : (0:ℝ) < Real.sqrt (n:ℝ) * Real.sqrt ((n+2:ℕ):ℝ) :=
    mul_pos (Real.sqrt_pos.2 hnpos) (Real.sqrt_pos.2 (by positivity))
  have hkey : u X n * u X (n+2) =
      (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) *
        (W ((n:ℝ)/X) * W (((n+2:ℕ):ℝ)/X))) /
      (Real.sqrt (n:ℝ) * Real.sqrt ((n+2:ℕ):ℝ)) := by
    rw [u, u, div_mul_div_comm]
    congr 1
    ring
  have hA : ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) *
        Real.exp (-(40000:ℝ)) / ((1010/1000)*(X:ℝ)) ≤
      ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) *
        Real.exp (-(40000:ℝ)) / (Real.sqrt (n:ℝ) * Real.sqrt ((n+2:ℕ):ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) hDpos hden
  have hB : ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) *
        Real.exp (-(40000:ℝ)) / (Real.sqrt (n:ℝ) * Real.sqrt ((n+2:ℕ):ℝ)) ≤
      (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) *
        (W ((n:ℝ)/X) * W (((n+2:ℕ):ℝ)/X))) /
      (Real.sqrt (n:ℝ) * Real.sqrt ((n+2:ℕ):ℝ)) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hLam) hDpos.le
  have hC : Real.exp (-(40000:ℝ)) * (100/101) * (v n / (X:ℝ)) =
      ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) *
        Real.exp (-(40000:ℝ)) / ((1010/1000)*(X:ℝ)) := by
    rw [v]
    field_simp
    ring
  rw [hkey, hC]
  exact le_trans hA hB

/-- Frequency isolation: a double sum whose kernel only survives on the shift-two
diagonal collapses to the single sum over the twin sub-window. -/
lemma sum_collapse (s : Finset ℕ) (uw : ℕ → ℝ) (Hb : ℕ → ℝ) (c : ℝ) :
    s.sum (fun n => s.sum (fun m => uw n * uw m * (c * (if m = n+2 then Hb n else 0))))
      = c * (s.filter (fun n => n+2 ∈ s)).sum (fun n => uw n * uw (n+2) * Hb n) := by
  have inner : ∀ n ∈ s, s.sum (fun m => uw n * uw m * (c * (if m = n+2 then Hb n else 0)))
      = c * (if n+2 ∈ s then uw n * uw (n+2) * Hb n else 0) := by
    intro n _
    have hterm : ∀ m, uw n * uw m * (c * (if m = n+2 then Hb n else 0))
        = if m = n+2 then (c * (uw n * uw (n+2) * Hb n)) else 0 := by
      intro m
      by_cases hm : m = n+2
      · subst hm; simp; ring
      · simp [hm]
    calc s.sum (fun m => uw n * uw m * (c * (if m = n+2 then Hb n else 0)))
        = s.sum (fun m => if m = n+2 then (c * (uw n * uw (n+2) * Hb n)) else 0) :=
          Finset.sum_congr rfl (fun m _ => hterm m)
      _ = if n+2 ∈ s then c * (uw n * uw (n+2) * Hb n) else 0 := by
          rw [Finset.sum_ite_eq']
      _ = c * (if n+2 ∈ s then uw n * uw (n+2) * Hb n else 0) := by
          split_ifs <;> ring
  rw [Finset.sum_congr rfl inner]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_filter]

/-! ## Explicit analytic inputs -/

/-- TP-0014 input: a uniform positive lower bound for the band kernel on the
log-scale range of the twin shift. -/
def KernelLowerBound : Prop :=
  ∃ h : ℝ, 0 < h ∧ ∀ v ∈ Set.Icc (-(1/25) : ℝ) 0, h ≤ H v

/-- TP-0014 input (arithmetic form): the frozen window's fixed relative core
`[1005/1000, 1010/1000] * X` carries a positive proportion of the twin Mangoldt mass
on unbounded scales.  This is the singular-series-strength twin lower bound. -/
def WindowTwinMassLinear : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ 1000 ≤ X ∧
    c * (X:ℝ) ≤ (coreBox X).sum v

/-- The moment form of the same input (the weights `u` of the identity, not `Λ Λ`). -/
def WindowMomentGrowth : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ 1000 ≤ X ∧
    m ≤ (core X).sum (fun n => u X n * u X (n+2))

/-- The explicit input of TP-0014: the two-moment identity, a positive lower bound
for the band kernel, and the arithmetic window twin-mass lower bound. -/
def SignedMomentMarginInput : Prop := TwoMomentIdentityHyp ∧ KernelLowerBound ∧ WindowTwinMassLinear

/-- TP-0015 input: a uniform positive upper bound for the band kernel on the
log-scale range of the twin shift.  Unlike the lower bound this is elementary, and it
is proved below (`kernelUpperBound`); it is recorded as a predicate for the audit. -/
def KernelUpperBound : Prop :=
  ∃ h : ℝ, 0 < h ∧ ∀ v ∈ Set.Icc (-(1/25) : ℝ) 0, H v ≤ h


/-! ## The band kernel is bounded above on the twin-shift range

The band kernel `H` of the frozen statement is built from the autocorrelation
`Kf v = ∫ y, b y * b (v - y)` of the band bump `b = bump (-1/40) (1/40)`.  That bump is
nonnegative, at most one, and vanishes outside `(-1/40, 1/40)`, so for every `v` the
integrand `b y * b (v - y)` is at most the indicator of `(-1/40, 1/40)`.  Hence
`Kf v ≤ 1/20`, and from `Kf ≥ 0` we get `H v ≤ Kf v / 2 ≤ 1/40`.  This is the uniform
upper bound the frozen TP-0015 reduction needs on the twin-shift range `[-1/25, 0]`. -/

/-- On its support the frozen bump is the exponential, and outside it is zero. -/
lemma bump_eq_indicator (a b : ℝ) :
    bump a b = (Set.Ioo a b).indicator (fun t => Real.exp (-1/((t-a)*(b-t)))) := by
  funext t
  rw [bump]
  by_cases h : a < t ∧ t < b
  · rw [if_pos h, Set.indicator_of_mem (Set.mem_Ioo.mpr h)]
  · rw [if_neg h, Set.indicator_of_notMem (by simpa [Set.mem_Ioo] using h)]

/-- The frozen bump is measurable. -/
lemma bump_measurable (a b : ℝ) : Measurable (bump a b) := by
  rw [bump_eq_indicator]
  apply Measurable.indicator _ measurableSet_Ioo
  measurability

/-- The frozen bump is nonnegative. -/
lemma bump_nonneg (a b t : ℝ) : 0 ≤ bump a b t := by
  rw [bump]
  split_ifs with h
  · exact (Real.exp_pos _).le
  · exact le_refl 0

/-- The frozen bump is at most one. -/
lemma bump_le_one (a b t : ℝ) : bump a b t ≤ 1 := by
  rw [bump]
  split_ifs with h
  · have hpos : 0 < (t-a)*(b-t) := mul_pos (by linarith [h.1]) (by linarith [h.2])
    have hneg : -1/((t-a)*(b-t)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hpos.le
    calc Real.exp (-1/((t-a)*(b-t))) ≤ Real.exp 0 := Real.exp_le_exp.2 hneg
      _ = 1 := Real.exp_zero
  · exact zero_le_one

/-- The frozen bump vanishes outside its open support. -/
lemma bump_eq_zero_of_not_mem {a b t : ℝ} (h : t ∉ Set.Ioo a b) : bump a b t = 0 := by
  rw [bump]
  have h' : ¬ (a < t ∧ t < b) := fun hh => h (Set.mem_Ioo.mpr hh)
  rw [if_neg h']

/-- The autocorrelation `Kf` is nonnegative. -/
lemma Kf_nonneg (v : ℝ) : 0 ≤ Kf v := by
  rw [Kf]
  apply integral_nonneg
  intro y
  exact mul_nonneg (bump_nonneg _ _ _) (bump_nonneg _ _ _)

/-- The volume of the band support is finite. -/
lemma band_volume_ne_top : (volume : Measure ℝ) (Set.Ioo (-1/40:ℝ) (1/40)) ≠ ⊤ := by
  rw [Real.volume_Ioo]
  simp

/-- The indicator of the band support is integrable. -/
lemma integrable_band_indicator :
    Integrable ((Set.Ioo (-1/40:ℝ) (1/40)).indicator (fun _ => (1:ℝ))) := by
  have hIntOn : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioo (-1/40:ℝ) (1/40)) :=
    integrableOn_const band_volume_ne_top (by simp)
  exact hIntOn.integrable_indicator measurableSet_Ioo

/-- The autocorrelation is at most the length of the band support: `Kf v ≤ 1/20`. -/
lemma Kf_le (v : ℝ) : Kf v ≤ 1/20 := by
  rw [Kf]
  set f : ℝ → ℝ := fun y => bumpB y * bumpB (v-y) with hf
  set g : ℝ → ℝ := (Set.Ioo (-1/40) (1/40)).indicator (fun _ => (1:ℝ)) with hg
  have hf_nonneg : 0 ≤ᵐ[volume] f :=
    ae_of_all _ (fun y => mul_nonneg (bump_nonneg _ _ _) (bump_nonneg _ _ _))
  have hg_int : Integrable g := hg ▸ integrable_band_indicator
  have hfg : f ≤ᵐ[volume] g := by
    apply ae_of_all
    intro y
    by_cases hy : y ∈ Set.Ioo (-1/40:ℝ) (1/40)
    · rw [hg, Set.indicator_of_mem hy, hf]
      show bumpB y * bumpB (v-y) ≤ 1
      have h1 : bumpB y ≤ 1 := bump_le_one (-1/40) (1/40) y
      have h2 : bumpB (v-y) ≤ 1 := bump_le_one (-1/40) (1/40) (v-y)
      have h3 : 0 ≤ bumpB y := bump_nonneg (-1/40) (1/40) y
      have h4 : 0 ≤ bumpB (v-y) := bump_nonneg (-1/40) (1/40) (v-y)
      nlinarith
    · rw [hg, Set.indicator_of_notMem hy, hf]
      show bumpB y * bumpB (v-y) ≤ 0
      have h1 : bumpB y = 0 := bump_eq_zero_of_not_mem hy
      rw [h1, zero_mul]
  have hmono : ∫ y, f y ≤ ∫ y, g y := integral_mono_of_nonneg hf_nonneg hg_int hfg
  have hgval : ∫ y, g y = 1/20 := by
    rw [hg]
    change ∫ y, (Set.Ioo (-1/40:ℝ) (1/40)).indicator (1 : ℝ → ℝ) y = 1/20
    rw [integral_indicator_one measurableSet_Ioo, Real.volume_real_Ioo_of_le (by norm_num)]
    norm_num
  linarith

/-- The band kernel is at most `1/40` everywhere. -/
lemma H_le_fortieth (v : ℝ) : H v ≤ 1/40 := by
  have h1 : Kf v ≤ 1/20 := Kf_le v
  have h2 : 0 ≤ Kf (v - 1/5) := Kf_nonneg _
  have h3 : 0 ≤ Kf (v + 1/5) := Kf_nonneg _
  rw [H]
  linarith

/-- The band kernel has a uniform positive upper bound on the twin-shift range. -/
theorem kernelUpperBound : KernelUpperBound := by
  refine ⟨1/40, by norm_num, ?_⟩
  intro v _
  exact H_le_fortieth v



/-! ## The band kernel is positive on the twin-shift range

The same support analysis bounds `Kf` from below.  On the fixed interval
`Icc (-49/2000) (-31/2000)` both `y` and `v - y` stay at distance at least `1/2000`
from the endpoints of `(-1/40, 1/40)`, uniformly in `v ∈ [-1/25, 0]`; there the band
bump is at least `exp (-4000000)`, so `Kf v ≥ exp (-8000000) * 9/1000`.  Together with
the two vanishing translates (`|v - 1/5|` and `|v + 1/5|` are at least `1/5 > 1/20`)
this gives `H v ≥ exp (-8000000) * 9/2000` on the twin-shift range. -/

/-- The band bump vanishes outside its open support: `|y| ≥ 1/40` gives `bumpB y = 0`. -/
lemma bumpB_eq_zero_of_abs_ge {y : ℝ} (hy : 1/40 ≤ |y|) : bumpB y = 0 := by
  apply bump_eq_zero_of_not_mem
  intro hmem
  rw [Set.mem_Ioo] at hmem
  have hlt : |y| < 1/40 := by
    rw [abs_lt]
    exact ⟨by linarith [hmem.1], hmem.2⟩
  linarith

/-- A concrete lower bound for the frozen bump from uniform interior margins of its
support: margins `δ` with `δ * δ = 1/4000000` force the exponent below `-4000000`. -/
lemma bump_ge_of_margin {a b t δ : ℝ} (hδ : 0 < δ)
    (h1 : δ ≤ t - a) (h2 : δ ≤ b - t) (h3 : δ * δ = 1/4000000) :
    Real.exp (-(4000000:ℝ)) ≤ bump a b t := by
  rw [bump]
  rw [if_pos (by constructor <;> linarith)]
  apply Real.exp_le_exp.2
  rw [neg_div]
  have hpa : 0 < t - a := by linarith
  have hpb : 0 < b - t := by linarith
  have hprod : (1:ℝ)/4000000 ≤ (t-a)*(b-t) := by
    rw [← h3]
    exact mul_le_mul h1 h2 hδ.le hpa.le
  have hkey : 1/((t-a)*(b-t)) ≤ 4000000 := by
    rw [div_le_iff₀ (mul_pos hpa hpb)]
    linarith
  linarith

/-- `Kf` vanishes outside `(-1/20, 1/20)`: the two band bumps cannot both be nonzero. -/
lemma Kf_eq_zero_of_support {w : ℝ} (hw : 1/20 ≤ |w|) : Kf w = 0 := by
  rw [Kf]
  have hzero : ∀ y : ℝ, bumpB y * bumpB (w - y) = 0 := by
    intro y
    by_cases hy : (1/40 : ℝ) ≤ |y|
    · rw [bumpB_eq_zero_of_abs_ge hy, zero_mul]
    · have hle : 1/40 ≤ |w - y| := by
        have h := abs_sub_abs_le_abs_sub w y
        linarith
      rw [bumpB_eq_zero_of_abs_ge hle, mul_zero]
  calc ∫ y, bumpB y * bumpB (w - y) = ∫ y, (0 : ℝ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hzero
    _ = 0 := by simp

/-- The `Kf` integrand is measurable. -/
lemma Kf_integrand_measurable (v : ℝ) : Measurable (fun y : ℝ => bumpB y * bumpB (v - y)) :=
  (bump_measurable _ _).mul
    ((bump_measurable _ _).comp (measurable_const.sub measurable_id))

/-- The `Kf` integrand is dominated by the indicator of the band support. -/
lemma Kf_integrand_le_indicator (v y : ℝ) :
    bumpB y * bumpB (v - y) ≤ (Set.Ioo (-1/40:ℝ) (1/40)).indicator (fun _ => (1:ℝ)) y := by
  by_cases hy : y ∈ Set.Ioo (-1/40:ℝ) (1/40)
  · rw [Set.indicator_of_mem hy]
    have h1 : bumpB y ≤ 1 := bump_le_one (-1/40) (1/40) y
    have h2 : bumpB (v-y) ≤ 1 := bump_le_one (-1/40) (1/40) (v-y)
    have h3 : 0 ≤ bumpB y := bump_nonneg (-1/40) (1/40) y
    have h4 : 0 ≤ bumpB (v-y) := bump_nonneg (-1/40) (1/40) (v-y)
    nlinarith
  · rw [Set.indicator_of_notMem hy]
    have hb : bump (-1/40) (1/40) y = 0 :=
      bump_eq_zero_of_not_mem (a := -1/40) (b := 1/40) hy
    rw [show bumpB y = bump (-1/40) (1/40) y from rfl, hb, zero_mul]

/-- The `Kf` integrand is integrable (it is dominated by the band indicator). -/
lemma Kf_integrable (v : ℝ) : Integrable (fun y : ℝ => bumpB y * bumpB (v - y)) := by
  refine Integrable.mono' integrable_band_indicator (Kf_integrand_measurable v).aestronglyMeasurable ?_
  filter_upwards with y
  have hnonneg : 0 ≤ bumpB y * bumpB (v-y) :=
    mul_nonneg (bump_nonneg _ _ _) (bump_nonneg _ _ _)
  rw [Real.norm_of_nonneg hnonneg]
  exact Kf_integrand_le_indicator v y

/-- The lower comparison function used for the positivity of `Kf`. -/
lemma band_lower_integrable :
    Integrable ((Set.Icc (-49/2000:ℝ) (-31/2000)).indicator
      (fun _ => Real.exp (-(8000000:ℝ)))) := by
  have hvol : (volume : Measure ℝ) (Set.Icc (-49/2000:ℝ) (-31/2000)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    simp
  have hIntOn : IntegrableOn (fun _ : ℝ => Real.exp (-(8000000:ℝ)))
      (Set.Icc (-49/2000:ℝ) (-31/2000)) :=
    integrableOn_const hvol (by simp)
  exact hIntOn.integrable_indicator measurableSet_Icc

/-- On the twin-shift range the `Kf` integrand dominates the fixed lower indicator. -/
lemma band_lower_le_Kf (v : ℝ) (hv : v ∈ Set.Icc (-(1/25):ℝ) 0) :
    ∀ y : ℝ, (Set.Icc (-49/2000:ℝ) (-31/2000)).indicator
        (fun _ => Real.exp (-(8000000:ℝ))) y ≤ bumpB y * bumpB (v - y) := by
  intro y
  by_cases hy : y ∈ Set.Icc (-49/2000:ℝ) (-31/2000)
  · rw [Set.indicator_of_mem hy]
    have hy1 : (-49/2000:ℝ) ≤ y := hy.1
    have hy2 : y ≤ (-31/2000:ℝ) := hy.2
    have hv1 : (-(1/25):ℝ) ≤ v := hv.1
    have hv2 : v ≤ 0 := hv.2
    have hb1 : Real.exp (-(4000000:ℝ)) ≤ bumpB y :=
      bump_ge_of_margin (a := -1/40) (b := 1/40) (t := y) (δ := 1/2000)
        (by norm_num) (by linarith) (by linarith) (by norm_num)
    have hb2 : Real.exp (-(4000000:ℝ)) ≤ bumpB (v - y) :=
      bump_ge_of_margin (a := -1/40) (b := 1/40) (t := v - y) (δ := 1/2000)
        (by norm_num) (by linarith) (by linarith) (by norm_num)
    have hprod : Real.exp (-(4000000:ℝ)) * Real.exp (-(4000000:ℝ)) ≤
        bumpB y * bumpB (v - y) :=
      mul_le_mul hb1 hb2 (le_of_lt (Real.exp_pos _)) (bump_nonneg _ _ _)
    have hexp : Real.exp (-(8000000:ℝ)) =
        Real.exp (-(4000000:ℝ)) * Real.exp (-(4000000:ℝ)) := by
      rw [← Real.exp_add]
      norm_num
    rw [hexp]
    exact hprod
  · rw [Set.indicator_of_notMem hy]
    exact mul_nonneg (bump_nonneg _ _ _) (bump_nonneg _ _ _)

/-- Uniform lower bound for `Kf` on the twin-shift range. -/
lemma Kf_lower (v : ℝ) (hv : v ∈ Set.Icc (-(1/25):ℝ) 0) :
    Real.exp (-(8000000:ℝ)) * (9/1000) ≤ Kf v := by
  have hf_int : Integrable (fun y : ℝ => bumpB y * bumpB (v - y)) := Kf_integrable v
  have hg_int : Integrable ((Set.Icc (-49/2000:ℝ) (-31/2000)).indicator
      (fun _ => Real.exp (-(8000000:ℝ)))) := band_lower_integrable
  have hmono : ∫ y, (Set.Icc (-49/2000:ℝ) (-31/2000)).indicator
        (fun _ => Real.exp (-(8000000:ℝ))) y ≤ ∫ y, bumpB y * bumpB (v - y) :=
    integral_mono hg_int hf_int (band_lower_le_Kf v hv)
  have hgval : ∫ y, (Set.Icc (-49/2000:ℝ) (-31/2000)).indicator
        (fun _ => Real.exp (-(8000000:ℝ))) y =
      Real.exp (-(8000000:ℝ)) * (9/1000) := by
    rw [integral_indicator_const (Real.exp (-(8000000:ℝ))) measurableSet_Icc,
      Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]
    ring
  rw [Kf]
  linarith

/-- The band kernel has a uniform positive lower bound on the twin-shift range. -/
theorem kernelLowerBound : KernelLowerBound := by
  refine ⟨Real.exp (-(8000000:ℝ)) * 9/2000, by positivity, ?_⟩
  intro v hv
  have hv1 : -(1/25) ≤ v := hv.1
  have hv2 : v ≤ 0 := hv.2
  have hz1 : Kf (v - 1/5) = 0 := by
    apply Kf_eq_zero_of_support
    have hneg : v - 1/5 ≤ 0 := by linarith
    rw [abs_of_nonpos hneg]
    linarith
  have hz2 : Kf (v + 1/5) = 0 := by
    apply Kf_eq_zero_of_support
    have hpos : 0 ≤ v + 1/5 := by linarith
    rw [abs_of_nonneg hpos]
    linarith
  have hlow := Kf_lower v hv
  rw [H, hz1, hz2]
  simp only [zero_div, sub_zero]
  linarith


/-! ## TP-0014: the signed two-moment margin from the kernel and the window mass -/

/-- The arithmetic window twin-mass input yields the moment form of the input:
on the fixed relative core both `W` values are at least `exp (-40000)`, so the moment
weights dominate `exp (-40000) * (100/101) * Λ(n)Λ(n+2)/X`. -/
theorem windowMomentGrowth_of_arithmetic (h : WindowTwinMassLinear) : WindowMomentGrowth := by
  obtain ⟨c, hcpos, hc⟩ := h
  refine ⟨Real.exp (-(40000:ℝ)) * (100/101) * c, by positivity, ?_⟩
  intro B
  obtain ⟨X, hBX, hX1000, hcX⟩ := hc B
  refine ⟨X, hBX, hX1000, ?_⟩
  have hXpos : (0:ℝ) < (X:ℝ) := by
    have : 0 < X := by omega
    exact_mod_cast this
  have hKpos : (0:ℝ) < Real.exp (-(40000:ℝ)) * (100/101) := by positivity
  have hc_le : c ≤ (coreBox X).sum v / (X:ℝ) := by
    rw [le_div_iff₀ hXpos]
    linarith [hcX]
  have hstep1 : Real.exp (-(40000:ℝ)) * (100/101) * c ≤
      Real.exp (-(40000:ℝ)) * (100/101) * ((coreBox X).sum v / (X:ℝ)) :=
    mul_le_mul_of_nonneg_left hc_le hKpos.le
  have hstep2 : Real.exp (-(40000:ℝ)) * (100/101) * ((coreBox X).sum v / (X:ℝ)) =
      (coreBox X).sum (fun n => Real.exp (-(40000:ℝ)) * (100/101) * (v n / (X:ℝ))) := by
    rw [Finset.sum_div, Finset.mul_sum]
  have hstep3 : (coreBox X).sum (fun n => Real.exp (-(40000:ℝ)) * (100/101) * (v n / (X:ℝ)))
      ≤ (coreBox X).sum (fun n => u X n * u X (n+2)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact uu_ge_of_box hX1000 hn
  have hstep4 : (coreBox X).sum (fun n => u X n * u X (n+2)) ≤
      (core X).sum (fun n => u X n * u X (n+2)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _
    exact mul_nonneg (u_nonneg X i) (u_nonneg X (i+2))
  linarith [hstep1, hstep2, hstep3, hstep4]

/-- The frozen signed moment margin follows from the identity, a positive lower
bound for the band kernel, and a positive window moment mass on unbounded scales. -/
theorem signedMomentMargin_of_momentGrowth
    (h : TwoMomentIdentityHyp ∧ KernelLowerBound ∧ WindowMomentGrowth) : SignedMomentMargin := by
  obtain ⟨hId, hK, hG⟩ := h
  obtain ⟨hb, hbpos, hble⟩ := hK
  obtain ⟨m, hmpos, hmge⟩ := hG
  refine ⟨hb*m/2, by positivity, ?_⟩
  intro B
  obtain ⟨X, hBX, hX1000, hmX⟩ := hmge (max B 999)
  have hBX' : B < X := lt_of_le_of_lt (le_max_left B 999) hBX
  have hXpos0 : 0 < X := by omega
  have hT : (0:ℝ) < T X := T_pos hXpos0
  have hHge : ∀ n ∈ core X, hb ≤ H (fX X n 2 - 2) := by
    intro n hn
    rw [core] at hn
    exact hble _ (fX_sub_two_mem_Icc hX1000 (Finset.mem_filter.mp hn).1
      (Finset.mem_filter.mp hn).2)
  have hnn : ∀ n ∈ core X, 0 ≤ u X n * u X (n+2) :=
    fun n _ => mul_nonneg (u_nonneg X n) (u_nonneg X (n+2))
  have hsum_ge : hb * (core X).sum (fun n => u X n * u X (n+2)) ≤
      (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have h1 : hb ≤ H (fX X n 2 - 2) := hHge n hn
    have h2 : 0 ≤ u X n * u X (n+2) := hnn n hn
    nlinarith [h1, h2]
  have hbig : hb * m ≤ (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2)) := by
    calc hb * m ≤ hb * (core X).sum (fun n => u X n * u X (n+2)) :=
          mul_le_mul_of_nonneg_left hmX hbpos.le
      _ ≤ _ := hsum_ge
  have hm_pos : (0:ℝ) < hb*m := mul_pos hbpos hmpos
  refine ⟨X, hBX', ?_⟩
  calc (hb*m/2) * T X < (hb*m) * T X := by
        apply mul_lt_mul_of_pos_right _ hT
        linarith
    _ ≤ T X * (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2)) := by
        rw [mul_comm (hb*m) (T X)]
        exact mul_le_mul_of_nonneg_left hbig hT.le
    _ = I X 1 - I X (-1) := (hId X hX1000).symm

/-- **TP-0014** (`L-twin-primes-signed-moment-margin`): the frozen target follows from
the three explicit inputs. -/
theorem signedMomentMargin_of_input (h : SignedMomentMarginInput) : SignedMomentMargin := by
  obtain ⟨hId, hK, hW⟩ := h
  exact signedMomentMargin_of_momentGrowth ⟨hId, hK, windowMomentGrowth_of_arithmetic hW⟩

/-! ## TP-0015: from the signed margin to the arithmetic window surplus -/

/-- The frozen implication `signed margin → window surplus`, from the frozen two-moment
identity as the only analytic hypothesis: the uniform upper bound of the band kernel is
proved in this file (`kernelUpperBound`). -/
theorem windowSurplus_of_signedMargin (hId : TwoMomentIdentityHyp) (hS : SignedMomentMargin) :
    WindowSurplus := by
  obtain ⟨δ, hδpos, hmargin⟩ := hS
  obtain ⟨hUv, hUpos, hUle⟩ := kernelUpperBound
  intro K B
  have hm_pos : (0:ℝ) < δ/hUv := div_pos hδpos hUpos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (eventually_mul_e_lt (K := K) (m := δ/hUv) hm_pos)
  obtain ⟨X, hBX, hmargX⟩ := hmargin (max B (max N 999))
  have hle1 : B ≤ max B (max N 999) := le_max_left _ _
  have hle2 : 999 ≤ max B (max N 999) := le_trans (le_max_right N 999) (le_max_right _ _)
  have hle3 : N ≤ max B (max N 999) := le_trans (le_max_left N 999) (le_max_right _ _)
  have hBX' : B < X := lt_of_le_of_lt hle1 hBX
  have hX1000 : 1000 ≤ X := by omega
  have hXpos0 : 0 < X := by omega
  have hT : (0:ℝ) < T X := T_pos hXpos0
  have hHle : ∀ n ∈ core X, H (fX X n 2 - 2) ≤ hUv := by
    intro n hn
    rw [core] at hn
    exact hUle _ (fX_sub_two_mem_Icc hX1000 (Finset.mem_filter.mp hn).1
      (Finset.mem_filter.mp hn).2)
  have hnn : ∀ n ∈ core X, 0 ≤ u X n * u X (n+2) :=
    fun n _ => mul_nonneg (u_nonneg X n) (u_nonneg X (n+2))
  have hSupper : (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2)) ≤
      hUv * (core X).sum (fun n => u X n * u X (n+2)) := by
    calc (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2))
        ≤ (core X).sum (fun n => u X n * u X (n+2) * hUv) := by
          apply Finset.sum_le_sum
          intro n hn
          have h1 : H (fX X n 2 - 2) ≤ hUv := hHle n hn
          have h2 : 0 ≤ u X n * u X (n+2) := hnn n hn
          nlinarith [h1, h2]
      _ = (core X).sum (fun n => u X n * u X (n+2)) * hUv := by rw [Finset.sum_mul]
      _ = hUv * (core X).sum (fun n => u X n * u X (n+2)) := by ring
  have huu_le : (core X).sum (fun n => u X n * u X (n+2)) ≤ M X := by
    rw [M, core]
    calc ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => u X n * u X (n+2))
        ≤ ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => v n / (X:ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          exact uu_le_v_div hX1000 (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
      _ = ((w X).filter (fun n => n+2 ∈ w X)).sum v / (X:ℝ) := by rw [Finset.sum_div]
      _ ≤ (w X).sum v / (X:ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => v_nonneg i)
  have hbound : δ < hUv * M X := by
    have h1 : δ * T X < T X * (hUv * M X) := by
      calc δ * T X < I X 1 - I X (-1) := hmargX
        _ = T X * (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2)) :=
            hId X hX1000
        _ ≤ T X * (hUv * M X) := by
            apply mul_le_mul_of_nonneg_left _ hT.le
            calc (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2))
                ≤ hUv * (core X).sum (fun n => u X n * u X (n+2)) := hSupper
              _ ≤ hUv * M X := mul_le_mul_of_nonneg_left huu_le hUpos.le
    have h2 : T X * δ < T X * (hUv * M X) := by
      calc T X * δ = δ * T X := by ring
        _ < T X * (hUv * M X) := h1
    exact (mul_lt_mul_iff_right₀ hT).mp h2
  have hMeq : δ/hUv < M X := by
    rw [div_lt_iff₀ hUpos]
    calc δ < hUv * M X := hbound
      _ = M X * hUv := by ring
  have heK : K * e X < δ/hUv := hN X (le_of_lt (lt_of_le_of_lt hle3 hBX))
  exact ⟨X, hBX', lt_trans heK hMeq⟩

/-- **TP-0015** (`L-twin-primes-moment-to-window`), machine-checked conditional form:
the frozen two-moment identity entails the frozen implication. -/
theorem momentToWindow_of_twoMomentIdentityHyp (hId : TwoMomentIdentityHyp)
    (hS : SignedMomentMargin) : WindowSurplus :=
  windowSurplus_of_signedMargin hId hS

/-- The full chain: the two-moment identity together with the two TP-0014 inputs gives
the frozen TP-0015 conclusion (`WindowSurplus`) over those inputs. -/
theorem windowSurplus_of_all (hId : TwoMomentIdentityHyp) (hLo : KernelLowerBound)
    (hW : WindowTwinMassLinear) : WindowSurplus :=
  momentToWindow_of_twoMomentIdentityHyp hId (signedMomentMargin_of_input ⟨hId, hLo, hW⟩)

/-- TP-0014's kernel input is proved in this file, so the frozen signed moment margin
follows from the two-moment identity and the arithmetic twin-mass input alone. -/
theorem signedMomentMargin_of_twoMomentIdentityHyp_and_arithmetic
    (hId : TwoMomentIdentityHyp) (hW : WindowTwinMassLinear) : SignedMomentMargin :=
  signedMomentMargin_of_input ⟨hId, kernelLowerBound, hW⟩

/-- The full chain with both kernel bounds discharged. -/
theorem windowSurplus_of_twoMomentIdentityHyp_and_arithmetic
    (hId : TwoMomentIdentityHyp) (hW : WindowTwinMassLinear) : WindowSurplus :=
  windowSurplus_of_all hId kernelLowerBound hW



/-! ## A weaker one-sided bridge suffices

The derivation above uses the frozen two-moment identity only through its upper half:
`I X 1 - I X (-1) ≤ T X * h * M X` at every admissible scale.  That one-sided
inequality is weaker than the frozen identity and is recorded here as
`MomentUpperBridge`.  It follows from the identity plus the kernel upper bound
(`momentUpperBridge_of_twoMomentIdentityHyp`), and it already entails the frozen
implication (`momentToWindow_of_momentUpperBridge`), so a one-sided Fourier-isolation
estimate is enough to close TP-0015. -/

/-- The upper half of the frozen two-moment identity: the signed moment difference is
bounded above by a constant multiple of `T X * M X` at all admissible scales. -/
def MomentUpperBridge : Prop :=
  ∃ h : ℝ, 0 < h ∧ ∀ X : ℕ, 1000 ≤ X → I X 1 - I X (-1) ≤ T X * h * M X

/-- The frozen two-moment identity yields the one-sided bridge. -/
theorem momentUpperBridge_of_twoMomentIdentityHyp (hId : TwoMomentIdentityHyp) :
    MomentUpperBridge := by
  obtain ⟨hUv, hUpos, hUle⟩ := kernelUpperBound
  refine ⟨hUv, hUpos, ?_⟩
  intro X hX1000
  have hXpos0 : 0 < X := by omega
  have hT : (0:ℝ) < T X := T_pos hXpos0
  have hHle : ∀ n ∈ core X, H (fX X n 2 - 2) ≤ hUv := by
    intro n hn
    rw [core] at hn
    exact hUle _ (fX_sub_two_mem_Icc hX1000 (Finset.mem_filter.mp hn).1
      (Finset.mem_filter.mp hn).2)
  have hnn : ∀ n ∈ core X, 0 ≤ u X n * u X (n+2) :=
    fun n _ => mul_nonneg (u_nonneg X n) (u_nonneg X (n+2))
  have hSupper : (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2)) ≤
      hUv * (core X).sum (fun n => u X n * u X (n+2)) := by
    calc (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2))
        ≤ (core X).sum (fun n => u X n * u X (n+2) * hUv) := by
          apply Finset.sum_le_sum
          intro n hn
          have h1 : H (fX X n 2 - 2) ≤ hUv := hHle n hn
          have h2 : 0 ≤ u X n * u X (n+2) := hnn n hn
          nlinarith [h1, h2]
      _ = (core X).sum (fun n => u X n * u X (n+2)) * hUv := by rw [Finset.sum_mul]
      _ = hUv * (core X).sum (fun n => u X n * u X (n+2)) := by ring
  have huu_le : (core X).sum (fun n => u X n * u X (n+2)) ≤ M X := by
    rw [M, core]
    calc ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => u X n * u X (n+2))
        ≤ ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => v n / (X:ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          exact uu_le_v_div hX1000 (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
      _ = ((w X).filter (fun n => n+2 ∈ w X)).sum v / (X:ℝ) := by rw [Finset.sum_div]
      _ ≤ (w X).sum v / (X:ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => v_nonneg i)
  calc I X 1 - I X (-1) = T X * (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2)) :=
        hId X hX1000
    _ ≤ T X * (hUv * M X) := by
        apply mul_le_mul_of_nonneg_left _ hT.le
        calc (core X).sum (fun n => u X n * u X (n+2) * H (fX X n 2 - 2))
            ≤ hUv * (core X).sum (fun n => u X n * u X (n+2)) := hSupper
          _ ≤ hUv * M X := mul_le_mul_of_nonneg_left huu_le hUpos.le
    _ = T X * hUv * M X := by ring

/-- The one-sided bridge already entails the frozen implication. -/
theorem momentToWindow_of_momentUpperBridge (hU : MomentUpperBridge)
    (hS : SignedMomentMargin) : WindowSurplus := by
  obtain ⟨hUv, hUpos, hUle⟩ := hU
  obtain ⟨δ, hδpos, hmargin⟩ := hS
  intro K B
  have hm_pos : (0:ℝ) < δ/hUv := div_pos hδpos hUpos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (eventually_mul_e_lt (K := K) (m := δ/hUv) hm_pos)
  obtain ⟨X, hBX, hmargX⟩ := hmargin (max B (max N 999))
  have hle1 : B ≤ max B (max N 999) := le_max_left _ _
  have hle3 : N ≤ max B (max N 999) := le_trans (le_max_left N 999) (le_max_right _ _)
  have hBX' : B < X := lt_of_le_of_lt hle1 hBX
  have hX1000 : 1000 ≤ X := by omega
  have hXpos0 : 0 < X := by omega
  have hT : (0:ℝ) < T X := T_pos hXpos0
  have hbridge : I X 1 - I X (-1) ≤ T X * hUv * M X := hUle X hX1000
  have hbound : δ < hUv * M X := by
    have h1 : T X * δ < T X * (hUv * M X) := by
      calc T X * δ = δ * T X := by ring
        _ < I X 1 - I X (-1) := hmargX
        _ ≤ T X * hUv * M X := hbridge
        _ = T X * (hUv * M X) := by ring
    exact (mul_lt_mul_iff_right₀ hT).mp h1
  have hMeq : δ/hUv < M X := by
    rw [div_lt_iff₀ hUpos]
    calc δ < hUv * M X := hbound
      _ = M X * hUv := by ring
  have heK : K * e X < δ/hUv := hN X (le_of_lt (lt_of_le_of_lt hle3 hBX))
  exact ⟨X, hBX', lt_trans heK hMeq⟩


end

end TwinPrimes


namespace PEqualNP.Outside

/-- The end-to-end statement over the frozen registry texts: the frozen TP-0013
statement entails the frozen TP-0015 statement.  Both `let`-chains below are the
registry text verbatim (`twin-primes.gaps`). -/
theorem L_twin_primes_moment_to_window_of_two_moment_identity :
(let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0
 let W := bump 1 (51/50)
 let b := bump (-1/40) (1/40)
 let K := fun (v : ℝ) => ∫ u : ℝ, b u * b (v-u)
 let H := fun (v : ℝ) => K v / 2 - K (v-1/5)/4 - K (v+1/5)/4
 let k := fun (t : ℝ) => ∫ v : ℝ, b v * Real.cos (2*Real.pi*v*t)
 let l := fun (t : ℝ) => Real.sin (Real.pi*t/5)*k t
 let T := fun (X : ℕ) => 2*Real.pi*(X:ℝ)
 let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
 let u := fun (X n : ℕ) => ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n
 let P := fun (X : ℕ) (t : ℝ) =>
   (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ)))
 let I := fun (X : ℕ) (σ : ℝ) =>
   ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2
 let f := fun (x n j : ℝ) => x * Real.log (1+j/n)
 ∀ X : ℕ, 1000 ≤ X →
   I X 1 - I X (-1) =
     T X * ((w X).filter (fun n => n+2 ∈ w X)).sum
       (fun n => u X n*u X (n+2)*H (f X n 2 - 2)))
    →
(let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0
 let W := bump 1 (51/50)
 let b := bump (-1/40) (1/40)
 let k := fun (t : ℝ) => ∫ v : ℝ, b v * Real.cos (2*Real.pi*v*t)
 let l := fun (t : ℝ) => Real.sin (Real.pi*t/5)*k t
 let T := fun (X : ℕ) => 2*Real.pi*(X:ℝ)
 let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
 let u := fun (X n : ℕ) => ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n
 let P := fun (X : ℕ) (t : ℝ) =>
   (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ)))
 let I := fun (X : ℕ) (σ : ℝ) =>
   ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2
 (∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ δ*T X < I X 1-I X (-1)) →
   (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
    let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)
    let M := fun (X : ℕ) => (w X).sum v / (X : ℝ)
    let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X
    ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X)) := by
  intro hId
  exact TwinPrimes.momentToWindow_of_twoMomentIdentityHyp hId

end PEqualNP.Outside

theorem PEqualNP.Outside.L_twin_primes_two_moment_identity :
    let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0; let W := bump 1 (51/50); let b := bump (-1/40) (1/40); let K := fun (v : ℝ) => ∫ u : ℝ, b u * b (v-u); let H := fun (v : ℝ) => K v / 2 - K (v-1/5)/4 - K (v+1/5)/4; let k := fun (t : ℝ) => ∫ v : ℝ, b v * Real.cos (2*Real.pi*v*t); let l := fun (t : ℝ) => Real.sin (Real.pi*t/5)*k t; let T := fun (X : ℕ) => 2*Real.pi*(X:ℝ); let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let u := fun (X n : ℕ) => ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n; let P := fun (X : ℕ) (t : ℝ) => (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ))); let I := fun (X : ℕ) (σ : ℝ) => ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2; let f := fun (x n j : ℝ) => x * Real.log (1+j/n); ∀ X : ℕ, 1000 ≤ X → I X 1 - I X (-1) = T X * ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => u X n*u X (n+2)*H (f X n 2 - 2)) := TwinPrimes.twoMomentIdentity

theorem PEqualNP.Outside.L_twin_primes_moment_to_window :
    (let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0; let W := bump 1 (51/50); let b := bump (-1/40) (1/40); let k := fun (t : ℝ) => ∫ v : ℝ, b v * Real.cos (2*Real.pi*v*t); let l := fun (t : ℝ) => Real.sin (Real.pi*t/5)*k t; let T := fun (X : ℕ) => 2*Real.pi*(X:ℝ); let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let u := fun (X n : ℕ) => ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n; let P := fun (X : ℕ) (t : ℝ) => (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ))); let I := fun (X : ℕ) (σ : ℝ) => ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2; ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ δ*T X < I X 1-I X (-1)) → (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X)
  := by
  intro hS
  exact TwinPrimes.momentToWindow_of_twoMomentIdentityHyp TwinPrimes.twoMomentIdentity hS
