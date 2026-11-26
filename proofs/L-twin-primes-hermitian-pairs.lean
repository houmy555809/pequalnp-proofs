import Mathlib

theorem PEqualNP.Outside.L_twin_primes_hermitian_pairs :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℂ), (∀ i j, A j i = star (A i j)) → ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2) |>.sum (fun z => A z.1 z.2)).im = 0 := by

  intro n A h
  set S : ℂ := ∑ z ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2), A z.1 z.2 with hS
  change S.im = 0
  have hprod : (Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2)
      = ((Finset.univ : Finset (Fin n)).product Finset.univ).filter (fun z => z.1 ≠ z.2) := by
    ext z
    simp
  have hS' : S = ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then A i j else 0) := by
    rw [hS, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have hcomm : star S = S := by
    rw [hS', star_sum]
    have h1 : (∑ i : Fin n, star (∑ j : Fin n, (if i ≠ j then A i j else 0)))
        = ∑ i : Fin n, ∑ j : Fin n, star (if i ≠ j then A i j else 0) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [star_sum]
    rw [h1]
    have h2 : (∑ i : Fin n, ∑ j : Fin n, star (if i ≠ j then A i j else 0))
        = ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then A j i else 0) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hij : i ≠ j <;> simp [hij, h i j]
    rw [h2]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact if_congr ne_comm rfl rfl
  exact Complex.conj_eq_iff_im.mp hcomm