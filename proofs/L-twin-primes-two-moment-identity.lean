import Mathlib

/-!
# Twin primes TP-0013 — the two-moment expansion and the finite-sum exchange

This file machine-checks the *expansion/exchange* half of the frozen gap
`L-twin-primes-two-moment-identity` (TP-0013) of `claim-work-tp/research/problems.json`.

Deliverables (all unconditional except for one explicit integrability input):

* `I_one_sub_neg_one` — the cancellation of the `1` in `1 ± cos`: under integrability of
  the two signed integrands,
  `I X 1 - I X (-1) = 2 ∫_{t>0} l(t/T)² cos(4πt/T) ‖P X t‖² dt`.
* `norm_sq_P` — the finite-square expansion
  `‖P X t‖² = Σ_{n∈w X} Σ_{m∈w X} u X n u X m cos(t(log n - log m))` (pure finite algebra).
* `integral_cos_weighted_normSq_eq_sum` — exchange of the finite double sum with the
  integral (Fubini in the finite case), giving the cosine-weighted energy as a double sum
  of `u u` times the band integrals.
* `twoMomentExpansionInput_of_integrable` — the interface theorem:
  `TwoMomentExpansionInput` follows from the single analytic input
  `ExpansionIntegrable : ∀ X ≥ 1000, IntegrableOn (fun t => (l (t/T X))²) (Ioi 0)`
  (which is the decay of `k = b̂` on the half-line, i.e. `l ∈ L²(0,∞)`).
* `bandIntegral_eq_T_mul_pairKernel` — the substitution `u = t/T` (i.e. `dt = T du`):
  `bandIntegral X n m = T X * pairKernel (X (log m - log n))` where
  `pairKernel v = 2 ∫_{u>0} l(u)² cos(4πu) cos(2πv u) du`.

The support/decay discussion (why `k` is *not* compactly supported but the kernel in `v`
*is*) is recorded in `notes/open/twin-tm-c.md`; the analytic input isolated there is
`PairKernelFormula`, and the finite-sum collapse theorem
`twoMomentIdentity_of_pairKernel` turns it into the frozen target.

The frozen data is repeated verbatim from `open/twin/twin-conditional-A.lean`
(§Frozen data) under the same namespace, so this file splices into that development after
removing one copy of the duplicated definitions.
-/

namespace TwinPrimes

noncomputable section

open MeasureTheory

/-! ## Frozen data (verbatim from the frozen statement of TP-0013) -/

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

/-! ## Elementary window and trig facts -/

/-- The frozen narrow window is contained in `Ioi X`. -/
lemma mem_window_bounds {X n : ℕ} (hn : n ∈ w X) : X < n ∧ 50*n < 51*X := by
  rw [w] at hn
  exact (Finset.mem_filter.mp hn).2

/-- `T X` is positive for positive `X`. -/
lemma T_pos {X : ℕ} (hX : 0 < X) : 0 < T X := by
  have hx : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
  rw [T]
  positivity

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

end

end TwinPrimes

theorem PEqualNP.Outside.L_twin_primes_two_moment_identity :
    let bump := fun (a b t : ℝ) => if a < t ∧ t < b then Real.exp (-1/((t-a)*(b-t))) else 0; let W := bump 1 (51/50); let b := bump (-1/40) (1/40); let K := fun (v : ℝ) => ∫ u : ℝ, b u * b (v-u); let H := fun (v : ℝ) => K v / 2 - K (v-1/5)/4 - K (v+1/5)/4; let k := fun (t : ℝ) => ∫ v : ℝ, b v * Real.cos (2*Real.pi*v*t); let l := fun (t : ℝ) => Real.sin (Real.pi*t/5)*k t; let T := fun (X : ℕ) => 2*Real.pi*(X:ℝ); let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let u := fun (X n : ℕ) => ArithmeticFunction.vonMangoldt n * W ((n:ℝ)/X) / Real.sqrt n; let P := fun (X : ℕ) (t : ℝ) => (w X).sum (fun n => (u X n : ℂ)*Complex.exp (-Complex.I*(t:ℂ)*(Real.log n : ℂ))); let I := fun (X : ℕ) (σ : ℝ) => ∫ t in Set.Ioi (0:ℝ), (l (t/T X))^2*(1+σ*Real.cos (4*Real.pi*t/T X))*‖P X t‖^2; let f := fun (x n j : ℝ) => x * Real.log (1+j/n); ∀ X : ℕ, 1000 ≤ X → I X 1 - I X (-1) = T X * ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => u X n*u X (n+2)*H (f X n 2 - 2)) := TwinPrimes.twoMomentIdentity
