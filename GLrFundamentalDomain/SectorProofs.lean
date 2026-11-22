import GLrFundamentalDomain.ApartmentReduction

/-!
# The two sector lemmas

* `apartment_to_sector` : every pointed chamber `[diag(ϖ^d) · w]` of the standard apartment is
  moved into the standard sector by a permutation matrix `σ ∈ GL_r(F) ⊆ GL_r(F[t])`.
  The vertices of `[diag(ϖ^d) · w]` are `[diag(ϖ^{d + ε_i ∘ w}) O^r]`, where `ε_i` is the
  exponent vector of the `i`-th lattice of the standard chain (`stdChain_vtx`).  Left
  multiplication by `σ` reorders the exponents to `(d + ε_i ∘ w) ∘ σ`; choosing `σ` to sort the
  integer keys `r d_j + w(j)` makes all these exponent vectors monotone at once
  (`sort_key_mono`), i.e. puts every vertex in the sector (`diagPow_smul_mem_stdSector`).
* `stdVertex_orbit_unique` : distinct sector vertices are not `GL_r(F[t])`-equivalent.  If
  `γ · [d(m) O^r] = [d(n) O^r]`, then `d(n)⁻¹ γ d(m) = x · h` with `x ∈ K^×`, `h ∈ GL_r(O)`
  (`vertexStabR_eq_stabilizer`).  There is `σ ∈ S_r` with `h_{i,σ(i)} ∈ O^×`
  (`exists_perm_isUnit_GLO`); comparing valuations of the `(i, σ(i))` entries and of the
  determinants gives `∑ v_∞(γ_{i,σ(i)}) = 0`, so all these valuations vanish and
  `m_{σ(i)} = n_i - v_∞(x)`; since `m, n` are sorted with a zero entry, `m = n`
  (`eq_of_perm_shift`).
-/

open Matrix Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

open Classical

variable {F : Type*} [Field F] {r : ℕ}

/-! ### Diagonal and permutation matrices -/

lemma coe_diagPow (d : Fin r → ℤ) :
    ((diagPow (F := F) d : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) =
      Matrix.diagonal fun j => (((unifUnit (F := F)) ^ d j : (Kt F)ˣ) : Kt F) := rfl

lemma diagPow_add (a b : Fin r → ℤ) :
    diagPow (F := F) (a + b) = diagPow a * diagPow b := by
  ext : 1
  simp only [coe_diagPow, Units.val_mul, Matrix.diagonal_mul_diagonal, Pi.add_apply]
  congr 1
  funext i
  rw [_root_.zpow_add, Units.val_mul]

lemma diagPow_const (c : ℤ) :
    diagPow (F := F) (fun _ : Fin r => c) = scalarGL (unifUnit ^ c) := by
  ext : 1
  rw [coe_diagPow, coe_scalarGL, Matrix.scalar_apply]

lemma permGL_mul_diagPow (w : Equiv.Perm (Fin r)) (d : Fin r → ℤ) :
    permGL r (Kt F) w * diagPow d = diagPow (d ∘ w) * permGL r (Kt F) w := by
  ext i j : 2
  simp [coe_diagPow, permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs with h <;> simp [h]

lemma permGL_smul_stdVertex₀ (w : Equiv.Perm (Fin r)) :
    permGL r (Kt F) w • stdVertex₀ F r = stdVertex₀ F r := by
  have : permGL r (Kt F) w = GLOr F r (permGL r (PowerSeries F) w) := by
    ext i j; simp [GLOr, permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  rw [this, stdVertex₀, smul_vtx, GLOr_smul_stdLattice]

/-- Exponent vector of the `i`-th lattice of the standard chain. -/
def chainExp (r : ℕ) (i : Fin r) : Fin r → ℤ := fun j => if r - (i : ℕ) ≤ j then 1 else 0

lemma stdChain_vtx (i : Fin r) :
    (stdChain F r i).vtx = diagPow (F := F) (chainExp r i) • stdVertex₀ F r := by
  suffices h : stdChain F r i = diagPow (F := F) (chainExp r i) • stdLattice F r by
    rw [h, stdVertex₀, smul_vtx]
  have hD : ∀ j, (((unifUnit (F := F)) ^ chainExp r i j : (Kt F)ˣ) : Kt F) =
      if r - (i : ℕ) ≤ j then unif F else 1 := by
    intro j; unfold chainExp; split_ifs <;> simp [unifUnit]
  apply Lattice.ext
  ext x
  simp only [smul_carrier, Submodule.mem_map, glLin_apply, coe_diagPow]
  show x ∈ latOf (stdW r i) ↔ _
  rw [mem_latOf]
  constructor
  · rintro ⟨hx, hred⟩
    have h0 : ∀ j : Fin r, r - (i : ℕ) ≤ j → ∃ b ∈ intRing F, unif F * b = x j :=
      fun j hj => exists_unif_mul_of_coeff_zero (hx j) (hred j hj)
    choose! b hb hbx using h0
    refine ⟨fun j => if r - (i : ℕ) ≤ j then b j else x j, fun j => ?_, ?_⟩
    · dsimp only
      split_ifs with h
      exacts [hb j h, hx j]
    · funext j
      simp only [hD, Matrix.mulVec_diagonal]
      split_ifs with h
      exacts [hbx j h, one_mul _]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · simp only [hD, Matrix.mulVec_diagonal]
      split_ifs
      exacts [(intRing F).mul_mem unif_mem_intRing (hy j), by simpa using hy j]
    · simp only [redV, hD, Matrix.mulVec_diagonal, if_pos hj]
      rw [coeff_zero_mul_of_mem unif_mem_intRing (hy j)]
      simp [unif]

/-- A vertex `[diag(ϖ^{e}) O^r]` with `e` monotone lies in the standard sector. -/
lemma diagPow_smul_mem_stdSector [NeZero r] {e : Fin r → ℤ} (he : Monotone e) :
    diagPow (F := F) e • stdVertex₀ F r ∈ stdSector F r := by
  have hr := NeZero.pos r
  set c := e ⟨r - 1, by omega⟩ with hc
  have hle : ∀ j, e j ≤ c := fun j => he (Fin.mk_le_mk.2 (by omega))
  refine ⟨⟨fun j => (c - e j).toNat, fun i j hij => ?_, ⟨r - 1, by omega⟩, ?_⟩, ?_⟩
  · have := he hij
    simp only
    omega
  · simp [← hc]
  · have hd : (fun j => -(((c - e j).toNat : ℕ) : ℤ)) = e + fun _ => -c := by
      funext j
      have := hle j
      simp only [Pi.add_apply]
      omega
    show diagPow (fun j => -(((c - e j).toNat : ℕ) : ℤ)) • stdVertex₀ F r = _
    rw [hd, diagPow_add, diagPow_const, SemigroupAction.mul_smul, scalarGL_smul_vtx]

/-! ### Sorting -/

lemma sort_key_mono (d : Fin r → ℤ) (w : Equiv.Perm (Fin r)) (i : Fin r) {a b : Fin r}
    (hab : (r : ℤ) * d a + (w a : ℕ) ≤ (r : ℤ) * d b + (w b : ℕ)) :
    d a + chainExp r i (w a) ≤ d b + chainExp r i (w b) := by
  have ha := (w a).2
  have hb := (w b).2
  have hd : d a ≤ d b := by
    by_contra h
    push_neg at h
    have : (r : ℤ) * d b + r ≤ (r : ℤ) * d a := by nlinarith
    omega
  unfold chainExp
  rcases hd.lt_or_eq with h | h
  · split_ifs <;> omega
  · rw [h] at hab ⊢
    split_ifs <;> omega

/-- **From the apartment to the sector.**  Every pointed chamber of the standard apartment is
moved into the standard sector by some `γ ∈ GL_r(F[t])` (in fact a permutation matrix). -/
theorem apartment_to_sector [NeZero r] (d : Fin r → ℤ) (w : Equiv.Perm (Fin r)) :
    ∃ γ : GL (Fin r) F[X], (GLAr F r γ • (apartmentPC d w : PChamber F r)).InSector := by
  set κ : Fin r → ℤ := fun j => (r : ℤ) * d j + (w j : ℕ) with hκ
  set σ := Tuple.sort κ
  refine ⟨permGL r F[X] σ, ?_⟩
  intro v hv
  rw [GLAr_permGL, apartmentPC, MulAction.Quotient.smul_mk, PChamber.toFinset_mk] at hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
  have hmat : permGL r (Kt F) σ * (diagPow d * permGL r (Kt F) w) * diagPow (chainExp r i) =
      diagPow ((d + chainExp r i ∘ w) ∘ σ) * (permGL r (Kt F) σ * permGL r (Kt F) w) := by
    calc permGL r (Kt F) σ * (diagPow d * permGL r (Kt F) w) * diagPow (chainExp r i)
        = permGL r (Kt F) σ * (diagPow d * (permGL r (Kt F) w * diagPow (chainExp r i))) := by
          simp only [mul_assoc]
      _ = permGL r (Kt F) σ * (diagPow d * (diagPow (chainExp r i ∘ w) * permGL r (Kt F) w)) := by
          rw [permGL_mul_diagPow]
      _ = (permGL r (Kt F) σ * diagPow (d + chainExp r i ∘ w)) * permGL r (Kt F) w := by
          rw [diagPow_add]; simp only [mul_assoc]
      _ = (diagPow ((d + chainExp r i ∘ w) ∘ σ) * permGL r (Kt F) σ) * permGL r (Kt F) w := by
          rw [permGL_mul_diagPow]
      _ = _ := mul_assoc _ _ _
  rw [smul_eq_mul]
  rw [stdChain_vtx, smul_smul, hmat, SemigroupAction.mul_smul, SemigroupAction.mul_smul,
    permGL_smul_stdVertex₀, permGL_smul_stdVertex₀]
  refine diagPow_smul_mem_stdSector fun a b hab => ?_
  exact sort_key_mono d w i (Tuple.monotone_sort κ hab)

/-! ### Uniqueness -/

lemma diagPow_zero : diagPow (F := F) (0 : Fin r → ℤ) = 1 := by
  ext : 1
  simp [coe_diagPow]

/-- In a local ring, if a finite sum is a unit then one of its terms is a unit. -/
lemma exists_isUnit_of_isUnit_sum {R ι : Type*} [CommRing R] [IsLocalRing R] (s : Finset ι)
    (f : ι → R) (h : IsUnit (∑ i ∈ s, f i)) : ∃ i ∈ s, IsUnit (f i) := by
  induction s using Finset.induction_on with
  | empty => simp at h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at h
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
    · exact ⟨a, Finset.mem_insert_self a s, h⟩
    · obtain ⟨i, hi, hu⟩ := ih h
      exact ⟨i, Finset.mem_insert_of_mem hi, hu⟩

/-- **Unit permutation lemma.** If `h = (a_{ij}) ∈ GL_r(O)`, there is a permutation `σ ∈ S_r`
with `a_{i,σ(i)} ∈ O^×` for all `i`. -/
lemma exists_perm_isUnit_GLO (k : GL (Fin r) (PowerSeries F)) :
    ∃ σ : Equiv.Perm (Fin r), ∀ i, IsUnit ((k : Matrix (Fin r) (Fin r) (PowerSeries F)) i (σ i)) := by
  have hdet : IsUnit (k : Matrix (Fin r) (Fin r) (PowerSeries F)).det :=
    (Matrix.GeneralLinearGroup.det k).isUnit
  rw [Matrix.det_apply] at hdet
  obtain ⟨τ, -, hτ⟩ := exists_isUnit_of_isUnit_sum _ _ hdet
  rw [Units.smul_def, zsmul_eq_mul] at hτ
  have hp := IsUnit.prod_iff.1 (isUnit_of_mul_isUnit_right hτ)
  refine ⟨τ⁻¹, fun i => ?_⟩
  have := hp (τ⁻¹ i) (Finset.mem_univ _)
  rwa [show τ (τ⁻¹ i) = i from Equiv.apply_symm_apply τ i] at this

lemma vInf_prod {ι : Type*} (s : Finset ι) (f : ι → Kt F) :
    vInf F (∏ i ∈ s, f i) = ∑ i ∈ s, vInf F (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [vInf, HahnSeries.orderTop_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, vInf_mul, ih]

lemma vInf_det_diagPow (d : Fin r → ℤ) :
    vInf F ((diagPow (F := F) d : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)).det =
      ((∑ i, d i : ℤ) : WithTop ℤ) := by
  rw [coe_diagPow, Matrix.det_diagonal, vInf_prod, WithTop.coe_sum]
  simp only [vInf_zpow_unifUnit]

/-- The final combinatorial step: if `m, n ∈ ℕ^r` are antitone with a zero entry and
`m ∘ σ = n - e` for a permutation `σ` and `e ∈ ℤ`, then `m = n`. -/
lemma eq_of_perm_shift {m n : Fin r → ℕ} (hm : Antitone m) (hn : Antitone n)
    (hm0 : ∃ i, m i = 0) (hn0 : ∃ i, n i = 0) (σ : Equiv.Perm (Fin r)) (e : ℤ)
    (h : ∀ i, (m (σ i) : ℤ) = n i - e) : m = n := by
  obtain ⟨j0, hj0⟩ := hm0
  obtain ⟨i0, hi0⟩ := hn0
  have h1 := h (σ.symm j0)
  have h2 := h i0
  rw [Equiv.apply_symm_apply, hj0] at h1
  rw [hi0] at h2
  have he : e = 0 := by omega
  have hmn : m ∘ σ = n := funext fun i => by have := h i; simp only [Function.comp]; omega
  let f : Fin r → ℕᵒᵈ := fun i => OrderDual.toDual (m i)
  have key := Tuple.unique_monotone (f := f) (σ := σ) (τ := 1)
    (fun a b hab => by
      show OrderDual.toDual (m (σ a)) ≤ OrderDual.toDual (m (σ b))
      exact OrderDual.toDual_le_toDual.2 (by
        have := hn hab; rw [← hmn] at this; exact this))
    (fun a b hab => OrderDual.toDual_le_toDual.2 (hm hab))
  rw [← hmn]
  funext i
  have := congrFun key i
  exact (OrderDual.toDual.injective this).symm

/-- **Uniqueness.**  If `γ ∈ GL_r(F[t])` maps the sector vertex `stdVertex m` to the sector
vertex `stdVertex n`, then `m = n`. -/
theorem stdVertex_orbit_unique (γ : GL (Fin r) F[X]) (m n : SectorIdx r)
    (h : GLAr F r γ • stdVertex F m = stdVertex F n) : m = n := by
  obtain ⟨m, hm, hm0⟩ := m
  obtain ⟨n, hn, hn0⟩ := n
  set g := diagPow (F := F) (fun j => (n j : ℤ)) * GLAr F r γ *
    diagPow (fun j => -(m j : ℤ)) with hg
  -- `g = d(n) γ d(m)⁻¹` fixes `[O^r]`, hence lies in `K^× · GL_r(O)`
  have hstab : g ∈ vertexStabR F r := by
    rw [vertexStabR_eq_stabilizer, MulAction.mem_stabilizer_iff, hg, SemigroupAction.mul_smul,
      SemigroupAction.mul_smul]
    change diagPow _ • (GLAr F r γ • stdVertex F ⟨m, hm, hm0⟩) = _
    rw [h, stdVertex, smul_smul, ← diagPow_add]
    have h0 : ((fun j => (n j : ℤ)) + fun j => -((n j : ℕ) : ℤ)) = 0 := by
      funext j; simp
    show diagPow ((fun j => (n j : ℤ)) + fun j => -((n j : ℕ) : ℤ)) • stdVertex₀ F r = _
    rw [h0, diagPow_zero, one_smul]
  obtain ⟨c, k, hck⟩ := hstab
  obtain ⟨σ, hσ⟩ := exists_perm_isUnit_GLO k
  obtain ⟨e, he⟩ : ∃ e : ℤ, vInf F (c : Kt F) = e := by
    cases hv : vInf F (c : Kt F) with
    | top => exact absurd ((vInf_eq_top_iff F _).1 hv) c.ne_zero
    | coe a => exact ⟨a, rfl⟩
  have hentry : ∀ i j, (g : Matrix (Fin r) (Fin r) (Kt F)) i j =
      (((unifUnit (F := F)) ^ (n i : ℤ) : (Kt F)ˣ) : Kt F) * polyEmb F (γ i j) *
        (((unifUnit (F := F)) ^ (-(m j : ℤ)) : (Kt F)ˣ) : Kt F) := by
    intro i j
    rw [hg, Units.val_mul, Units.val_mul, coe_diagPow, coe_diagPow, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    rfl
  -- the valuations of the entries `γ_{i, σ(i)}`
  have hrow : ∀ i, ∃ a : ℤ, a ≤ 0 ∧ (n i : ℤ) + a - m (σ i) = e := by
    intro i
    have h1 := congrFun (congrFun hck i) (σ i)
    rw [hentry] at h1
    have h2 := congrArg (vInf F) h1
    rw [Matrix.smul_apply, smul_eq_mul, vInf_mul, vInf_mul, vInf_mul, vInf_zpow_unifUnit,
      vInf_zpow_unifUnit, he,
      show (GLOr F r k : Matrix (Fin r) (Fin r) (Kt F)) i (σ i) =
        HahnSeries.ofPowerSeries ℤ F ((k : Matrix (Fin r) (Fin r) (PowerSeries F)) i (σ i))
        from rfl, vInf_ofPowerSeries_isUnit F (hσ i)] at h2
    have hne : γ i (σ i) ≠ 0 := by
      intro h0
      rw [h0, map_zero, (vInf_eq_top_iff F 0).2 rfl] at h2
      simp at h2
    have hle := vInf_polyEmb_nonpos F (γ i (σ i)) hne
    obtain ⟨a, ha⟩ : ∃ a : ℤ, vInf F (polyEmb F (γ i (σ i))) = a := by
      cases hv : vInf F (polyEmb F (γ i (σ i))) with
      | top => rw [hv] at hle; simp at hle
      | coe a => exact ⟨a, rfl⟩
    rw [ha] at h2 hle
    refine ⟨a, by exact_mod_cast hle, ?_⟩
    norm_cast at h2
    omega
  -- the valuation of the determinant
  have hdet : (∑ i, (n i : ℤ)) + (∑ i, -(m i : ℤ)) = r * e := by
    have h1 := congrArg (fun M => vInf F M.det) hck
    simp only at h1
    have hL : vInf F (g : Matrix (Fin r) (Fin r) (Kt F)).det =
        (((∑ i, (n i : ℤ)) + ∑ i, -(m i : ℤ) : ℤ) : WithTop ℤ) := by
      have : g = diagPow (fun j => (n j : ℤ)) *
          (GLAr F r γ * diagPow (fun j => -(m j : ℤ)) * GLOr F r 1) := by
        rw [map_one, mul_one, hg, mul_assoc]
      rw [this, Units.val_mul, Matrix.det_mul, vInf_mul, vInf_det_GLAr_mul_mul_GLOr,
        vInf_det_diagPow, vInf_det_diagPow]
      norm_cast
    have hk : vInf F (GLOr F r k : Matrix (Fin r) (Fin r) (Kt F)).det = 0 := by
      have : (GLOr F r k : Matrix (Fin r) (Fin r) (Kt F)).det =
          HahnSeries.ofPowerSeries ℤ F
            ((Matrix.GeneralLinearGroup.det k : (PowerSeries F)ˣ) : PowerSeries F) := by
        simp [GLOr, RingHom.map_det]
      rw [this, vInf_ofPowerSeries_unit]
    have hc : vInf F ((c : Kt F) ^ r) = ((r * e : ℤ) : WithTop ℤ) := by
      rw [← Fintype.card_fin r, ← Finset.card_univ, ← Finset.prod_const, vInf_prod]
      simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_cast
    rw [hL, Matrix.det_smul, vInf_mul, Fintype.card_fin, hc, hk, add_zero] at h1
    exact_mod_cast h1
  choose a ha0 hae using hrow
  have hsum : ∑ i, a i = 0 := by
    have h1 : ∑ i, ((n i : ℤ) + a i - m (σ i)) = ∑ _i : Fin r, e := Finset.sum_congr rfl
      fun i _ => hae i
    have h2 : ∑ i, (m (σ i) : ℤ) = ∑ i, (m i : ℤ) := Equiv.sum_comp σ (fun j => (m j : ℤ))
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_neg_distrib] at h1 hdet
    linarith
  have ha : ∀ i, a i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonpos fun i _ => ha0 i).1 hsum i (Finset.mem_univ _)
  have := eq_of_perm_shift hm hn hm0 hn0 σ e fun i => by have := hae i; rw [ha i] at this; omega
  subst this
  rfl

end GLrBuilding
