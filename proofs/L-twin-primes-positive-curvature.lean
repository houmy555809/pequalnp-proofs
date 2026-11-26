import Mathlib

theorem PEqualNP.Outside.L_twin_primes_positive_curvature :
    ∀ u c : ℝ, 0 < c → c < u → 1/(u+c)+1/(u-c)-2/u = 2*c^2/(u*(u^2-c^2)) ∧ 0 < 1/(u+c)+1/(u-c)-2/u := by

  intro u c hc hcu
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