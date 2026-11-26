import Mathlib

private lemma isUnit_prod_iff {R S : Type*} [Monoid R] [Monoid S] (x : R × S) :
    IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2 := by
  constructor
  · intro h
    exact ⟨h.map (MonoidHom.fst R S), h.map (MonoidHom.snd R S)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨u1, hu1⟩ := h1
    obtain ⟨u2, hu2⟩ := h2
    have hv1 : x.1 * (↑(u1⁻¹) : R) = 1 := by rw [← hu1]; simp
    have hv2 : x.2 * (↑(u2⁻¹) : S) = 1 := by rw [← hu2]; simp
    have hv1' : (↑(u1⁻¹) : R) * x.1 = 1 := by rw [← hu1]; simp
    have hv2' : (↑(u2⁻¹) : S) * x.2 = 1 := by rw [← hu2]; simp
    refine ⟨⟨x, ((↑(u1⁻¹) : R), (↑(u2⁻¹) : S)), ?_, ?_⟩, rfl⟩
    · ext <;> simp [hv1, hv2]
    · ext <;> simp [hv1', hv2']

private lemma cm_range_zmod (q : ℕ) [NeZero q] :
    ((Finset.range q).filter (fun n => Nat.Coprime n q ∧ Nat.Coprime (n+2) q)).card
      = (Finset.univ.filter (fun x : ZMod q => IsUnit x ∧ IsUnit (x + 2))).card := by
  refine Finset.card_bij (fun (n : ℕ) (_ : n ∈ (Finset.range q).filter (fun n => Nat.Coprime n q ∧ Nat.Coprime (n+2) q)) => (n : ZMod q)) ?_ ?_ ?_
  · intro n hn
    have hpq := (Finset.mem_filter.mp hn).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rw [ZMod.isUnit_iff_coprime]
      exact hpq.1
    · have hc : ((n : ZMod q) + 2) = ((n + 2 : ℕ) : ZMod q) := by push_cast; ring
      rw [hc, ZMod.isUnit_iff_coprime]
      exact hpq.2
  · intro n hn m hm h
    have hnlt : n < q := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hmlt : m < q := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
    have hval := congrArg ZMod.val h
    rwa [ZMod.val_cast_of_lt hnlt, ZMod.val_cast_of_lt hmlt] at hval
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    have hv : ((x.val : ZMod q)) = x := ZMod.natCast_zmod_val x
    have hmem : x.val ∈ (Finset.range q).filter (fun n => Nat.Coprime n q ∧ Nat.Coprime (n+2) q) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt x, ?_, ?_⟩
      · have h : IsUnit ((x.val : ZMod q)) := by rw [hv]; exact hx'.1
        rwa [ZMod.isUnit_iff_coprime] at h
      · have hc : ((x.val + 2 : ℕ) : ZMod q) = (x.val : ZMod q) + 2 := by push_cast; ring
        have h : IsUnit (((x.val + 2 : ℕ) : ZMod q)) := by rw [hc, hv]; exact hx'.2
        rwa [ZMod.isUnit_iff_coprime] at h
    exact ⟨x.val, hmem, hv⟩

private lemma cm_crt (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a*b)] (hab : Nat.Coprime a b) :
    (Finset.univ.filter (fun x : ZMod (a*b) => IsUnit x ∧ IsUnit (x + 2))).card
      = (Finset.univ.filter (fun x : ZMod a => IsUnit x ∧ IsUnit (x + 2))).card
        * (Finset.univ.filter (fun x : ZMod b => IsUnit x ∧ IsUnit (x + 2))).card := by
  let e := ZMod.chineseRemainder hab
  have hset : (Finset.univ.filter (fun y : ZMod a × ZMod b =>
      IsUnit y.1 ∧ IsUnit (y.1 + 2) ∧ IsUnit y.2 ∧ IsUnit (y.2 + 2)))
      = (Finset.univ.filter (fun x : ZMod a => IsUnit x ∧ IsUnit (x + 2)))
        ×ˢ (Finset.univ.filter (fun x : ZMod b => IsUnit x ∧ IsUnit (x + 2))) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    tauto
  have hcard : (Finset.univ.filter (fun x : ZMod (a*b) => IsUnit x ∧ IsUnit (x + 2))).card
      = (Finset.univ.filter (fun y : ZMod a × ZMod b =>
          IsUnit y.1 ∧ IsUnit (y.1 + 2) ∧ IsUnit y.2 ∧ IsUnit (y.2 + 2))).card := by
    refine Finset.card_bij (fun (x : ZMod (a*b)) (_ : x ∈ Finset.univ.filter (fun x : ZMod (a*b) => IsUnit x ∧ IsUnit (x + 2))) => e x) ?_ ?_ ?_
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      have h1 : IsUnit (e x) := hx'.1.map e.toRingHom
      have h2 : IsUnit (e x + 2) := by
        have h := hx'.2.map e.toRingHom
        have h2' : e.toRingHom (x + 2) = e x + 2 := by
          rw [map_add, map_ofNat]
          rfl
        rwa [h2'] at h
      obtain ⟨h1a, h1b⟩ := (isUnit_prod_iff (e x)).mp h1
      obtain ⟨h2a, h2b⟩ := (isUnit_prod_iff (e x + 2)).mp h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h1a, h2a, h1b, h2b⟩
    · intro x _ y _ hxy
      exact e.injective hxy
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      have huy : IsUnit y := (isUnit_prod_iff y).mpr ⟨hy'.1, hy'.2.2.1⟩
      have huy2 : IsUnit (y + 2) := (isUnit_prod_iff (y + 2)).mpr ⟨hy'.2.1, hy'.2.2.2⟩
      refine ⟨e.symm y, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact huy.map e.symm.toRingHom
      · have h := huy2.map e.symm.toRingHom
        have hsplit : e.symm.toRingHom (y + 2) = e.symm y + 2 := by
          rw [map_add, map_ofNat]
          rfl
        rwa [hsplit] at h
  rw [hcard, hset, Finset.card_product]

theorem PEqualNP.Outside.L_twin_primes_crt_mask :
    let A := fun (q : ℕ) => ((Finset.range q).filter (fun n => Nat.Coprime n q ∧ Nat.Coprime (n+2) q)).card; ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → A (a*b) = A a*A b := by
  dsimp only
  intro a b ha hb hab
  haveI : NeZero a := ⟨by omega⟩
  haveI : NeZero b := ⟨by omega⟩
  haveI : NeZero (a*b) := ⟨(Nat.mul_pos ha hb).ne'⟩
  rw [cm_range_zmod (a*b), cm_range_zmod a, cm_range_zmod b]
  exact cm_crt a b hab
