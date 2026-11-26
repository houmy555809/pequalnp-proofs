import Mathlib

private lemma sfp_aux (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun n => f (n+2)) k = ZMod.stdAddChar (N:=N) (2*k) * ZMod.dft f k := by
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  have hL : (∑ j : ZMod N, ZMod.stdAddChar (-(j * k)) • f (j + 2))
      = ∑ j : ZMod N, f j * ZMod.stdAddChar (-((j - 2) * k)) := by
    refine Fintype.sum_bijective (fun x : ZMod N => x + 2) ?_ _ _ ?_
    · refine ⟨fun a b hab => ?_, fun y => ⟨y - 2, by simp⟩⟩
      exact add_right_cancel hab
    · intro x
      rw [smul_eq_mul]
      rw [show x + 2 - 2 = x by simp]
      exact mul_comm _ _
  have hR : (∑ j : ZMod N, ZMod.stdAddChar (2*k) * (ZMod.stdAddChar (-(j * k)) • f j))
      = ∑ j : ZMod N, f j * ZMod.stdAddChar (-((j - 2) * k)) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul]
    rw [show (2:ZMod N) * k + -(j * k) = -((j - 2) * k) by ring]
    exact mul_comm _ _
  rw [hL, hR]

theorem PEqualNP.Outside.L_twin_primes_shift_fourier_phase :
    ∀ (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (k : ZMod N), ZMod.dft (fun n => f (n+2)) k = ZMod.stdAddChar (N:=N) (2*k) * ZMod.dft f k := by
  intro N _ f k
  exact sfp_aux N f k
