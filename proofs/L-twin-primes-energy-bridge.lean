import Mathlib

private lemma dft_sum_mul {N : ℕ} [NeZero N] (A B : ZMod N → ℂ) :
    ∑ k : ZMod N, ZMod.dft A k * ZMod.dft B k
      = (N : ℂ) * ∑ j : ZMod N, A j * B (-j) := by
  classical
  have hstd_sum : ∀ b : ZMod N,
      (∑ k : ZMod N, ZMod.stdAddChar (k * b)) = if b = 0 then (N:ℂ) else 0 := by
    intro b
    rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar N)]
    simp only [ZMod.card]
    split_ifs <;> push_cast <;> ring
  have hexp : ∀ k : ZMod N, ZMod.dft A k * ZMod.dft B k
      = ∑ j : ZMod N, ∑ l : ZMod N,
          (A j * B l) * (ZMod.stdAddChar (-(j*k)) * ZMod.stdAddChar (-(l*k))) := by
    intro k
    rw [ZMod.dft_apply, ZMod.dft_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [smul_eq_mul]
    ring
  calc ∑ k : ZMod N, ZMod.dft A k * ZMod.dft B k
      = ∑ k : ZMod N, ∑ j : ZMod N, ∑ l : ZMod N,
          (A j * B l) * (ZMod.stdAddChar (-(j*k)) * ZMod.stdAddChar (-(l*k))) :=
        Finset.sum_congr rfl fun k _ => hexp k
    _ = ∑ j : ZMod N, ∑ l : ZMod N, ∑ k : ZMod N,
          (A j * B l) * (ZMod.stdAddChar (-(j*k)) * ZMod.stdAddChar (-(l*k))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
    _ = ∑ j : ZMod N, ∑ l : ZMod N,
          (A j * B l) * (∑ k : ZMod N,
            ZMod.stdAddChar (-(j*k)) * ZMod.stdAddChar (-(l*k))) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
    _ = ∑ j : ZMod N, ∑ l : ZMod N,
          (A j * B l) * (∑ k : ZMod N, ZMod.stdAddChar (k * (-(j+l)))) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
    _ = ∑ j : ZMod N, ∑ l : ZMod N,
          (A j * B l) * (if (-(j+l)) = 0 then (N:ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        rw [hstd_sum]
    _ = (N : ℂ) * ∑ j : ZMod N, A j * B (-j) := by
        calc ∑ j : ZMod N, ∑ l : ZMod N,
              (A j * B l) * (if (-(j+l)) = 0 then (N:ℂ) else 0)
            = ∑ j : ZMod N, (N:ℂ) * (A j * B (-j)) := by
                apply Finset.sum_congr rfl
                intro j _
                rw [Finset.sum_eq_single (-j)]
                · have h0 : -(j + (-j)) = 0 := by ring
                  rw [h0, if_pos rfl]
                  ring
                · intro l _ hl
                  have hcond : ¬ (-(j+l) = 0) := by
                    intro h
                    apply hl
                    have h' : j + l = 0 := neg_eq_zero.mp h
                    rw [eq_neg_iff_add_eq_zero, add_comm]
                    exact h'
                  rw [if_neg hcond, mul_zero]
                · intro hmem
                  exact absurd (Finset.mem_univ _) hmem
          _ = (N : ℂ) * ∑ j : ZMod N, A j * B (-j) := by rw [Finset.mul_sum]

private lemma cosine_plancherel :
    ∀ (N : ℕ) [NeZero N] (f : ZMod N → ℝ), (∑ k : ZMod N, (ZMod.stdAddChar (N:=N) (2*k)).re * ‖ZMod.dft (fun j => (f j : ℂ)) k‖^2) = (N:ℝ)*∑ j : ZMod N, f j*f (j+2) := by
  intro N _inst f
  classical
  let Φ : ZMod N → ℂ := fun j => (f j : ℂ)
  let F : ZMod N → ℂ := ZMod.dft Φ
  let χ : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  have hΦre : ∀ j : ZMod N, (Φ j).re = f j := by
    intro j; simp [Φ]
  have hΦim : ∀ j : ZMod N, (Φ j).im = 0 := by
    intro j; simp [Φ]
  have hconjΦ : ∀ j : ZMod N, (starRingEnd ℂ) (Φ j) = Φ j := by
    intro j; simp [Φ]
  have hconjχ : ∀ x : ZMod N, (starRingEnd ℂ) (χ x) = χ (-x) := by
    intro x
    simp only [χ]
    rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
      ← AddChar.map_neg_eq_inv (ZMod.toCircle (N:=N)) x]
    rfl
  have hFapp : ∀ k : ZMod N, F k = ∑ j : ZMod N, χ (-(j*k)) * Φ j := by
    intro k
    simp only [F, ZMod.dft_apply, smul_eq_mul, χ]
  have hconjF : ∀ k : ZMod N, (starRingEnd ℂ) (F k) = F (-k) := by
    intro k
    have hk := hFapp k
    have hnk := hFapp (-k)
    rw [hk, hnk]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, hconjχ, hconjΦ]
    rw [show -(-(j*k)) = -(j*(-k)) by ring]
  have hshift : ∀ k : ZMod N, ZMod.dft (fun j => Φ (j+2)) k = χ (2*k) * F k := by
    intro k
    calc ZMod.dft (fun j => Φ (j+2)) k
        = ∑ j : ZMod N, χ (-(j*k)) * Φ (j+2) := by
            rw [ZMod.dft_apply]; simp only [smul_eq_mul, χ]
      _ = ∑ j : ZMod N, χ (-((j-2)*k)) * Φ j := by
            refine Fintype.sum_equiv (Equiv.addRight (2 : ZMod N))
              (fun j : ZMod N => χ (-(j*k)) * Φ (j+2))
              (fun j : ZMod N => χ (-((j-2)*k)) * Φ j) ?_
            intro j
            rw [show (Equiv.addRight (2 : ZMod N)) j = j + 2 from rfl]
            rw [show (j + 2 - 2 : ZMod N) = j by ring]
      _ = ∑ j : ZMod N, χ (2*k) * (χ (-(j*k)) * Φ j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [show -((j-2)*k) = 2*k + -(j*k) by ring]
            rw [AddChar.map_add_eq_mul]
            ring
      _ = χ (2*k) * ∑ j : ZMod N, χ (-(j*k)) * Φ j := by rw [Finset.mul_sum]
      _ = χ (2*k) * F k := by rw [hFapp]
  have hBdft : ∀ k : ZMod N, ZMod.dft (fun j => Φ (-j)) k = F (-k) := by
    intro k
    have h := congrFun (ZMod.dft_comp_neg (N:=N) (E:=ℂ) Φ) k
    simpa [F] using h
  have hH : ∑ k : ZMod N, χ (2*k) * (F k * (starRingEnd ℂ) (F k))
      = (N:ℂ) * ∑ j : ZMod N, Φ j * Φ (j+2) := by
    calc ∑ k : ZMod N, χ (2*k) * (F k * (starRingEnd ℂ) (F k))
        = ∑ k : ZMod N, χ (2*k) * (F k * F (-k)) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hconjF k]
      _ = ∑ k : ZMod N, ZMod.dft (fun j => Φ (j+2)) k
            * ZMod.dft (fun j => Φ (-j)) k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hshift k, hBdft k]
            ring
      _ = (N:ℂ) * ∑ j : ZMod N, (fun j => Φ (j+2)) j * (fun j => Φ (-j)) (-j) :=
            dft_sum_mul (fun j => Φ (j+2)) (fun j => Φ (-j))
      _ = (N:ℂ) * ∑ j : ZMod N, Φ j * Φ (j+2) := by
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            simp only [neg_neg]
            ring
  have hLHS : (∑ k : ZMod N, (χ (2*k)).re * ‖F k‖^2)
      = (∑ k : ZMod N, χ (2*k) * (F k * (starRingEnd ℂ) (F k))).re := by
    have h1 : (∑ k : ZMod N, χ (2*k) * (F k * (starRingEnd ℂ) (F k))).re
        = ∑ k : ZMod N, (χ (2*k) * (F k * (starRingEnd ℂ) (F k))).re := by
      simpa using map_sum Complex.reAddGroupHom
        (fun k : ZMod N => χ (2*k) * (F k * (starRingEnd ℂ) (F k))) Finset.univ
    rw [h1]
    apply Finset.sum_congr rfl
    intro k _
    have hzc : F k * (starRingEnd ℂ) (F k) = ((‖F k‖^2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact Complex.mul_conj (F k)
    rw [hzc, Complex.mul_re]
    rw [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hRHS : ((N:ℂ) * ∑ j : ZMod N, Φ j * Φ (j+2)).re
      = (N:ℝ) * ∑ j : ZMod N, f j * f (j+2) := by
    rw [Complex.mul_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    have h1 : (∑ j : ZMod N, Φ j * Φ (j+2)).re
        = ∑ j : ZMod N, (Φ j * Φ (j+2)).re := by
      simpa using map_sum Complex.reAddGroupHom
        (fun j : ZMod N => Φ j * Φ (j+2)) Finset.univ
    rw [h1]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.mul_re]
    simp [hΦre, hΦim]
  change (∑ k : ZMod N, (χ (2*k)).re * ‖F k‖^2)
      = (N:ℝ) * ∑ j : ZMod N, f j * f (j+2)
  calc ∑ k : ZMod N, (χ (2*k)).re * ‖F k‖^2
      = (∑ k : ZMod N, χ (2*k) * (F k * (starRingEnd ℂ) (F k))).re := hLHS
    _ = ((N:ℂ) * ∑ j : ZMod N, Φ j * Φ (j+2)).re := by rw [hH]
    _ = (N:ℝ) * ∑ j : ZMod N, f j * f (j+2) := hRHS

theorem PEqualNP.Outside.L_twin_primes_energy_bridge :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let N := fun (X : ℕ) => 2*X+5; let f := fun (X n : ℕ) => if n ∈ w X ∧ n.Prime then Real.log n else 0; let energy := fun (X : ℕ) => letI : NeZero (N X) := ⟨by dsimp [N]; omega⟩; ∑ k : ZMod (N X), (ZMod.stdAddChar (N:=N X) (2*k)).re * ‖ZMod.dft (fun j : ZMod (N X) => ((f X j.val:ℝ):ℂ)) k‖^2; ∀ B : ℕ, ∃ X : ℕ, B<X ∧ 0<energy X) → (∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ (p+2).Prime) := by
  intro H B
  obtain ⟨X, hXB, hE⟩ := H (max B 9)
  have hXB' : B < X := lt_of_le_of_lt (le_max_left B 9) hXB
  let w : ℕ → Finset ℕ := fun X => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
  let N : ℕ := 2*X+5
  let f : ℕ → ℝ := fun n => if n ∈ w X ∧ n.Prime then Real.log n else 0
  let g : ZMod N → ℝ := fun j => f j.val
  letI : NeZero N := ⟨by dsimp [N]; omega⟩
  have hE' : 0 < ∑ k : ZMod N, (ZMod.stdAddChar (N:=N) (2*k)).re * ‖ZMod.dft (fun j : ZMod N => ((g j:ℝ):ℂ)) k‖^2 := by
    simpa [w, N, f, g] using hE
  have henergy_eq : (∑ k : ZMod N, (ZMod.stdAddChar (N:=N) (2*k)).re * ‖ZMod.dft (fun j : ZMod N => ((g j:ℝ):ℂ)) k‖^2) = (N:ℝ) * ∑ j : ZMod N, g j * g (j+2) :=
    cosine_plancherel (N := N) g
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have hN0 : 0 < N := by dsimp [N]; omega
    exact_mod_cast hN0
  have hSpos : 0 < ∑ j : ZMod N, g j * g (j+2) := by
    have h := hE'
    rw [henergy_eq] at h
    nlinarith
  have hg_nonneg : ∀ j : ZMod N, 0 ≤ g j := by
    intro j
    simp only [g, f]
    split_ifs with h
    · apply Real.log_nonneg
      have h1 : (1:ℕ) ≤ j.val := h.2.one_lt.le
      exact_mod_cast h1
    · exact le_rfl
  have hterm_nonneg : ∀ j ∈ (Finset.univ : Finset (ZMod N)), 0 ≤ g j * g (j+2) := by
    intro j _
    exact mul_nonneg (hg_nonneg j) (hg_nonneg (j+2))
  obtain ⟨j, -, hj⟩ := (Finset.sum_pos_iff_of_nonneg hterm_nonneg).mp hSpos
  have hgj : 0 < g j := by
    rcases lt_or_ge 0 (g j) with h | h
    · exact h
    · have h0 : g j = 0 := le_antisymm h (hg_nonneg j)
      rw [h0, zero_mul] at hj
      exact absurd hj (lt_irrefl 0)
  have hgq : 0 < g (j+2) := by
    rcases lt_or_ge 0 (g (j+2)) with h | h
    · exact h
    · have h0 : g (j+2) = 0 := le_antisymm h (hg_nonneg (j+2))
      rw [h0, mul_zero] at hj
      exact absurd hj (lt_irrefl 0)
  have hfj : 0 < f j.val := by simpa [g] using hgj
  have hfq : 0 < f (j+2).val := by simpa [g] using hgq
  have hcondj : j.val ∈ w X ∧ j.val.Prime := by
    by_contra hc
    have hzero : f j.val = 0 := by simp [f, hc]
    rw [hzero] at hfj
    exact lt_irrefl 0 hfj
  have hcondq : (j+2).val ∈ w X ∧ (j+2).val.Prime := by
    by_contra hc
    have hzero : f (j+2).val = 0 := by simp [f, hc]
    rw [hzero] at hfq
    exact lt_irrefl 0 hfq
  have hjlt : j.val < 2*X+1 := Finset.mem_range.mp (Finset.mem_filter.mp hcondj.1).1
  have hjvalN : j.val + 2 < N := by dsimp [N]; omega
  have hqval : (j+2).val = j.val + 2 := by
    have hq_eq : (j + 2) = ((j.val + 2 : ℕ) : ZMod N) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val j]
      conv_rhs => rw [Nat.cast_add, Nat.cast_ofNat]
    rw [hq_eq, ZMod.val_natCast_of_lt hjvalN]
  have hXlt : X < j.val := (Finset.mem_filter.mp hcondj.1).2.1
  exact ⟨j.val, by omega, hcondj.2, by rw [← hqval]; exact hcondq.2⟩
