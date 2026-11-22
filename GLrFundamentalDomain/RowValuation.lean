import GLrFundamentalDomain.Sector

/-!
# Row valuations and the elementary operations of the reduction

For a matrix `M = (a_{ij})_{0 ≤ i, j ≤ r-1}` over `K = F((1/t))`:
* `rowVal M i = v_i(M) = min_j v_∞(a_{ij})` (the valuation of row `i`);
* `pivotCol M i = j_i(M)`: the *first* column `j` with `v_∞(a_{ij}) = v_i(M)`; thus
  `v_∞(a_{ij}) > v_i(M)` for `j < j_i(M)` and `v_∞(a_{ij}) ≥ v_i(M)` for `j > j_i(M)`;
* `rowValSum M = ∑_i v_i(M)`; we have `rowValSum M ≤ v_∞(det M)` (`rowValSum_le_vInf_det`), and
  `v_∞(det M)` is unchanged by `M ↦ γ M κ` with `γ ∈ GL_r(F[t])`, `κ ∈ GL_r(O)`.
* `IsMonoRow M i n j`: row `i` of `M` is `ϖ^n e_j`.

We also set up the three kinds of operations used in the reduction, and how they affect the
row valuations:
* `C_l` (`exists_clearRow`): right multiplication by an element of the Iwahori subgroup `I`
  turning row `l` into `ϖ^{v_l} e_{j_l}`; it does not change the rows with a `0` in column `j_l`.
  Right multiplication by `GL_r(O)` does not change any `v_i` (`rowVal_mul_GLOr`).
* `R_{kl}` (`rowVal_lex_lt_transv`): left multiplication by the elementary matrix
  `u'_{k,l}(-c t^{n_l - v_k}) ∈ GL_r(F[t])`, which kills the leading term of the pivot entry of
  row `k` using the monomial row `l = ϖ^{n_l} e_{j_k}`, when `v_k ≤ n_l`.  It increases
  `(v_k, j_k)` lexicographically.
* left multiplication by a permutation matrix permutes the `v_i` (`rowVal_permGL_mul`).
-/

open Matrix Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

open Classical

variable {F : Type*} [Field F] {r : ℕ}


/-! ### Row valuations and pivot columns -/

/-- `v_i(M) = min_j v_∞(M_{ij})`, the valuation of row `i`. -/
def rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) (i : Fin r) : WithTop ℤ :=
  Finset.univ.inf fun j => vInf F (M i j)

lemma pivotCol_nonempty (M : Matrix (Fin r) (Fin r) (Kt F)) (i : Fin r) :
    (Finset.univ.filter fun j => vInf F (M i j) = rowVal M i).Nonempty := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf (Finset.univ : Finset (Fin r))
    ⟨i, Finset.mem_univ _⟩ fun j => vInf F (M i j)
  exact ⟨j, by simp [rowVal, hj]⟩

/-- `j_i(M)`: the first column in which row `i` attains its valuation `v_i(M)`. -/
def pivotCol (M : Matrix (Fin r) (Fin r) (Kt F)) (i : Fin r) : Fin r :=
  (Finset.univ.filter fun j => vInf F (M i j) = rowVal M i).min' (pivotCol_nonempty M i)

lemma vInf_pivotCol (M : Matrix (Fin r) (Fin r) (Kt F)) (i : Fin r) :
    vInf F (M i (pivotCol M i)) = rowVal M i := by
  have := Finset.min'_mem _ (pivotCol_nonempty M i)
  simpa using this

lemma rowVal_le_vInf (M : Matrix (Fin r) (Fin r) (Kt F)) (i j : Fin r) :
    rowVal M i ≤ vInf F (M i j) :=
  Finset.inf_le (Finset.mem_univ j)

lemma rowVal_lt_vInf_of_lt_pivotCol (M : Matrix (Fin r) (Fin r) (Kt F)) (i j : Fin r)
    (hj : j < pivotCol M i) : rowVal M i < vInf F (M i j) := by
  refine lt_of_le_of_ne (rowVal_le_vInf M i j) fun h => ?_
  have : pivotCol M i ≤ j := Finset.min'_le _ _ (by simp [h])
  exact absurd hj (not_lt.mpr this)

/-- `∑_i v_i(M)`. -/
def rowValSum (M : Matrix (Fin r) (Fin r) (Kt F)) : WithTop ℤ := ∑ i, rowVal M i

/-- Row `i` of `M` is `ϖ^n e_j`. -/
def IsMonoRow (M : Matrix (Fin r) (Fin r) (Kt F)) (i : Fin r) (n : ℤ) (j : Fin r) : Prop :=
  ∀ j', M i j' = if j' = j then (((unifUnit (F := F)) ^ n : (Kt F)ˣ) : Kt F) else 0

/-! ### Basic facts about the valuations -/

/-- An invertible matrix has no zero row, so `v_i(M) ≠ ⊤`. -/
lemma rowVal_ne_top (M : GL (Fin r) (Kt F)) (i : Fin r) :
    rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) i ≠ ⊤ := by
  intro h
  have h0 : ∀ j, (M : Matrix (Fin r) (Fin r) (Kt F)) i j = 0 := fun j =>
    (vInf_eq_top_iff F _).mp (top_le_iff.mp (h ▸ rowVal_le_vInf _ i j))
  exact (Matrix.GeneralLinearGroup.det M).ne_zero
    (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact Matrix.det_eq_zero_of_row_eq_zero i h0)

lemma rowValSum_ne_top (M : GL (Fin r) (Kt F)) :
    rowValSum (M : Matrix (Fin r) (Fin r) (Kt F)) ≠ ⊤ := by
  rw [rowValSum, Ne, WithTop.sum_eq_top]
  push_neg
  exact fun i _ => rowVal_ne_top M i

/-- **Determinant bound.** `∑_i v_i(M) ≤ v_∞(det M)`. -/
theorem rowValSum_le_vInf_det (M : Matrix (Fin r) (Fin r) (Kt F)) :
    rowValSum M ≤ vInf F M.det := by
  -- a lower bound for the valuation of a product
  have hprod : ∀ (s : Finset (Fin r)) (f : Fin r → Kt F) (c : Fin r → WithTop ℤ),
      (∀ i, c i ≤ vInf F (f i)) → ∑ i ∈ s, c i ≤ vInf F (∏ i ∈ s, f i) := by
    intro s f c hc
    induction s using Finset.induction_on with
    | empty => simp [vInf, HahnSeries.orderTop_one]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, vInf_mul]
      exact add_le_add (hc a) ih
  rw [Matrix.det_apply]
  refine Finset.sum_induction _ (fun x => rowValSum M ≤ vInf F x) ?_ ?_ ?_
  · intro a b ha hb
    exact le_trans (le_min ha hb) (HahnSeries.min_orderTop_le_orderTop_add)
  · simp [vInf]
  · intro σ _
    have h1 : rowValSum M ≤ vInf F (∏ i, M (σ i) i) := by
      have := hprod Finset.univ (fun i => M (σ i) i) (fun i => rowVal M (σ i))
        (fun i => rowVal_le_vInf M (σ i) i)
      rwa [Equiv.sum_comp σ (rowVal M)] at this
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simpa [h] using h1
    · simpa [h, vInf, HahnSeries.orderTop_neg] using h1

/-- `v_∞(det)` is invariant under `M ↦ γ M κ`, `γ ∈ GL_r(F[t])`, `κ ∈ GL_r(O)`. -/
theorem vInf_det_GLAr_mul_mul_GLOr (γ : GL (Fin r) F[X]) (M : GL (Fin r) (Kt F))
    (κ : GL (Fin r) (PowerSeries F)) :
    vInf F ((GLAr F r γ * M * GLOr F r κ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)).det
      = vInf F (M : Matrix (Fin r) (Fin r) (Kt F)).det := by
  have hγ : ((GLAr F r γ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)).det =
      polyEmb F ((Matrix.GeneralLinearGroup.det γ : (Polynomial F)ˣ) : Polynomial F) := by
    simp [GLAr, RingHom.map_det]
  have hκ : ((GLOr F r κ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)).det =
      HahnSeries.ofPowerSeries ℤ F
        ((Matrix.GeneralLinearGroup.det κ : (PowerSeries F)ˣ) : PowerSeries F) := by
    simp [GLOr, RingHom.map_det]
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul,
    Matrix.det_mul, vInf_mul, vInf_mul, hγ, hκ, vInf_polyEmb_unit, vInf_ofPowerSeries_unit,
    zero_add, add_zero]


/-! ### Valuations of sums -/

lemma le_vInf_sum {ι : Type*} (s : Finset ι) (f : ι → Kt F) (c : WithTop ℤ)
    (h : ∀ i ∈ s, c ≤ vInf F (f i)) : c ≤ vInf F (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp [vInf]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) ?_
    exact HahnSeries.min_orderTop_le_orderTop_add

lemma vInf_zpow_unifUnit (n : ℤ) :
    vInf F ((((unifUnit (F := F)) ^ n : (Kt F)ˣ) : Kt F)) = n := by
  rw [Units.val_zpow_eq_zpow_val]
  change vInf F (unif F ^ n) = n
  rw [unif_zpow]
  exact HahnSeries.orderTop_single one_ne_zero

/-! ### Right multiplication by `GL_r(O)` does not change the row valuations -/

lemma rowVal_le_rowVal_mul_map (M : Matrix (Fin r) (Fin r) (Kt F))
    (K : Matrix (Fin r) (Fin r) (PowerSeries F)) (i : Fin r) :
    rowVal M i ≤ rowVal (M * K.map (HahnSeries.ofPowerSeries ℤ F)) i := by
  refine Finset.le_inf fun j _ => ?_
  rw [Matrix.mul_apply]
  refine le_vInf_sum _ _ _ fun m _ => ?_
  rw [vInf_mul, Matrix.map_apply]
  simpa using add_le_add (rowVal_le_vInf M i m) (vInf_ofPowerSeries_nonneg F (K m j))

/-- **`C_l` and, more generally, right multiplication by `GL_r(O)` do not change any `v_i`.** -/
theorem rowVal_mul_GLOr (M : GL (Fin r) (Kt F)) (κ : GL (Fin r) (PowerSeries F)) (i : Fin r) :
    rowVal ((M * GLOr F r κ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) i =
      rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) i := by
  have e1 : ((M * GLOr F r κ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) =
      (M : Matrix (Fin r) (Fin r) (Kt F)) *
        (κ : Matrix _ _ (PowerSeries F)).map (HahnSeries.ofPowerSeries ℤ F) := by
    rw [Matrix.GeneralLinearGroup.coe_mul]; rfl
  rw [e1]
  refine le_antisymm ?_ (rowVal_le_rowVal_mul_map _ _ i)
  have h := rowVal_le_rowVal_mul_map ((M : Matrix (Fin r) (Fin r) (Kt F)) *
        (κ : Matrix _ _ (PowerSeries F)).map (HahnSeries.ofPowerSeries ℤ F))
    ((κ⁻¹ : GL (Fin r) (PowerSeries F)) : Matrix _ _ (PowerSeries F)) i
  have he : (M : Matrix (Fin r) (Fin r) (Kt F)) *
        (κ : Matrix _ _ (PowerSeries F)).map (HahnSeries.ofPowerSeries ℤ F) *
      ((κ⁻¹ : GL (Fin r) (PowerSeries F)) : Matrix _ _ (PowerSeries F)).map
        (HahnSeries.ofPowerSeries ℤ F) = (M : Matrix (Fin r) (Fin r) (Kt F)) := by
    rw [Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv]
    simp
  rwa [he] at h

/-! ### Permutation matrices -/

lemma permGL_mul_apply {R : Type*} [CommRing R] (w : Equiv.Perm (Fin r))
    (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    ((permGL r R w : GL (Fin r) R) * M : Matrix (Fin r) (Fin r) R) i j = M (w i) j := by
  simp [permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]

lemma GLAr_permGL (w : Equiv.Perm (Fin r)) : GLAr F r (permGL r F[X] w) = permGL r (Kt F) w := by
  ext i j; simp [GLAr, permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

/-- **Left multiplication by a permutation matrix permutes the `v_i`.** -/
theorem rowVal_permGL_mul (w : Equiv.Perm (Fin r)) (M : GL (Fin r) (Kt F)) (i : Fin r) :
    rowVal ((permGL r (Kt F) w * M : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) i =
      rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) (w i) := by
  simp only [rowVal, Matrix.GeneralLinearGroup.coe_mul, permGL_mul_apply]

theorem rowValSum_permGL_mul (w : Equiv.Perm (Fin r)) (M : GL (Fin r) (Kt F)) :
    rowValSum ((permGL r (Kt F) w * M : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) =
      rowValSum (M : Matrix (Fin r) (Fin r) (Kt F)) := by
  simp only [rowValSum, rowVal_permGL_mul]
  exact Equiv.sum_comp w _

/-- Left multiplication by a permutation matrix permutes the pivot columns `j_i`. -/
theorem pivotCol_permGL_mul (w : Equiv.Perm (Fin r)) (M : GL (Fin r) (Kt F)) (i : Fin r) :
    pivotCol ((permGL r (Kt F) w * M : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) i =
      pivotCol (M : Matrix (Fin r) (Fin r) (Kt F)) (w i) := by
  simp only [pivotCol, rowVal, Matrix.GeneralLinearGroup.coe_mul, permGL_mul_apply]

/-! ### Monomial rows -/

lemma IsMonoRow.rowVal {M : Matrix (Fin r) (Fin r) (Kt F)} {i : Fin r} {n : ℤ} {j : Fin r}
    (h : IsMonoRow M i n j) : rowVal M i = n := by
  refine le_antisymm ?_ (Finset.le_inf fun j' _ => ?_)
  · have := rowVal_le_vInf M i j
    rwa [h j, if_pos rfl, vInf_zpow_unifUnit] at this
  · rw [h j']
    split_ifs
    · rw [vInf_zpow_unifUnit]
    · simp [vInf]

lemma IsMonoRow.pivotCol {M : Matrix (Fin r) (Fin r) (Kt F)} {i : Fin r} {n : ℤ} {j : Fin r}
    (h : IsMonoRow M i n j) : pivotCol M i = j := by
  have h1 := vInf_pivotCol M i
  rw [h.rowVal, h (GLrBuilding.pivotCol M i)] at h1
  by_contra hne
  rw [if_neg hne] at h1
  simp [vInf] at h1

/-- Two rows of an invertible matrix cannot be monomial in the same column. -/
lemma IsMonoRow.eq_of_col_eq {M : GL (Fin r) (Kt F)} {i i' : Fin r} {n n' : ℤ} {j : Fin r}
    (h : IsMonoRow (M : Matrix (Fin r) (Fin r) (Kt F)) i n j)
    (h' : IsMonoRow (M : Matrix (Fin r) (Fin r) (Kt F)) i' n' j) : i = i' := by
  by_contra hne
  have hdet := Matrix.det_updateRow_add_smul_self (M : Matrix (Fin r) (Fin r) (Kt F))
    (Ne.symm hne) (-((((unifUnit (F := F)) ^ (n' - n) : (Kt F)ˣ) : Kt F)))
  have hrow : (M : Matrix (Fin r) (Fin r) (Kt F)) i' +
      (-((((unifUnit (F := F)) ^ (n' - n) : (Kt F)ˣ) : Kt F))) •
        (M : Matrix (Fin r) (Fin r) (Kt F)) i = 0 := by
    funext j'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, h j', h' j']
    split_ifs
    · rw [neg_mul, ← Units.val_mul, ← _root_.zpow_add, sub_add_cancel, add_neg_cancel]
    · simp
  rw [hrow, Matrix.det_eq_zero_of_row_eq_zero i' (fun j => by simp)] at hdet
  exact (Matrix.GeneralLinearGroup.det M).ne_zero
    (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet.symm)


/-! ### The operation `C_l`: clearing a row by right multiplication by `I` -/

/-- The identity matrix with row `p` replaced by `c`. -/
def rowRepl {R : Type*} [CommRing R] (p : Fin r) (c : Fin r → R) : Matrix (Fin r) (Fin r) R :=
  (1 : Matrix (Fin r) (Fin r) R).updateRow p c

lemma det_rowRepl {R : Type*} [CommRing R] (p : Fin r) (c : Fin r → R) :
    (rowRepl p c).det = c p := by
  have h := Matrix.det_updateRow_sum (1 : Matrix (Fin r) (Fin r) R) p c
  have hc : (∑ k, c k • (1 : Matrix (Fin r) (Fin r) R) k) = c := by
    funext j; simp [Matrix.one_apply]
  rw [hc] at h
  simpa [rowRepl] using h

lemma mul_rowRepl_apply {R : Type*} [CommRing R] (M : Matrix (Fin r) (Fin r) R) (p : Fin r)
    (c : Fin r → R) (i j : Fin r) :
    (M * rowRepl p c) i j = M i p * c j + if j = p then 0 else M i j := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  simp only [rowRepl, Matrix.updateRow_self]
  congr 1
  rw [Finset.sum_congr rfl fun m hm => by
    rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hm)]]
  by_cases hj : j = p
  · subst hj
    simp only [if_true]
    refine Finset.sum_eq_zero fun m hm => ?_
    simp [Finset.ne_of_mem_erase hm]
  · rw [if_neg hj, Finset.sum_eq_single_of_mem j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)]
    · simp
    · intro m _ hm; simp [hm]

lemma map_rowRepl {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : Fin r)
    (c : Fin r → R) : (rowRepl p c).map f = rowRepl p (f ∘ c) := by
  ext i j
  simp only [rowRepl, Matrix.map_apply, Matrix.updateRow_apply, Function.comp_apply]
  split_ifs <;> simp [Matrix.one_apply]

/-- `rowRepl p c` as an element of `GL_r(O)` when `c p` is a unit. -/
def rowReplGL (p : Fin r) (c : Fin r → PowerSeries F) (hu : IsUnit (c p)) :
    GL (Fin r) (PowerSeries F) :=
  Matrix.GeneralLinearGroup.mk'' (rowRepl p c) (by rw [det_rowRepl]; exact hu)

/-- `rowRepl p c ∈ I` when `c p` is a unit and `c j ∈ ϖ O` for `j < p`.  (It is the product of
`d_p(c_p)` and the `u_{p,j}(c_j)`, `l_{p,j}(c_j)`.) -/
lemma rowReplGL_mem_iwahoriR (p : Fin r) (c : Fin r → PowerSeries F) (hu : IsUnit (c p))
    (hlow : ∀ j, j < p → PowerSeries.constantCoeff (c j) = 0) :
    rowReplGL p c hu ∈ iwahoriR F r := by
  intro i j hji
  change (rowRepl p c).map PowerSeries.constantCoeff i j = 0
  rw [map_rowRepl]
  simp only [rowRepl, Matrix.updateRow_apply, Function.comp_apply]
  split_ifs with h
  · subst h; exact hlow j hji
  · have hij : i ≠ j := fun he => by subst he; exact lt_irrefl _ hji
    simp [hij]

lemma vInf_div_eq (x y : Kt F) (n m : ℤ) (hx : vInf F x = n) (hy : vInf F y = m) :
    vInf F (x / y) = ((n - m : ℤ) : WithTop ℤ) := by
  have hy0 : y ≠ 0 := by rintro rfl; simp [vInf] at hy
  have hx0 : x ≠ 0 := by rintro rfl; simp [vInf] at hx
  have h := vInf_div_add F x y hy0
  have hne : vInf F (x / y) ≠ ⊤ := by
    rw [Ne, vInf_eq_top_iff]; exact div_ne_zero hx0 hy0
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hz]
  rw [← hz, hx, hy] at h
  have : z + m = n := by exact_mod_cast h
  congr 1; omega

/-- **The operation `C_l`.**  Right multiplication by an element `κ` of the Iwahori subgroup turns
row `l` into `ϖ^{v_l} e_{j_l}` (where `j_l` is the first column where row `l` attains its
valuation `v_l`), and leaves unchanged every row having a `0` in column `j_l`. -/
theorem exists_clearRow (M : GL (Fin r) (Kt F)) (l : Fin r) (n : ℤ)
    (hn : rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) l = n) :
    ∃ κ ∈ iwahoriR F r,
      IsMonoRow ((M * GLOr F r κ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) l n
        (pivotCol (M : Matrix (Fin r) (Fin r) (Kt F)) l) ∧
      ∀ i, (M : Matrix (Fin r) (Fin r) (Kt F)) i (pivotCol (M : Matrix (Fin r) (Fin r) (Kt F)) l)
          = 0 → ∀ j, ((M * GLOr F r κ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) i j =
            (M : Matrix (Fin r) (Fin r) (Kt F)) i j := by
  set A := (M : Matrix (Fin r) (Fin r) (Kt F))
  set p := pivotCol A l
  set a := A l p
  have ha : vInf F a = n := by rw [vInf_pivotCol, hn]
  have ha0 : a ≠ 0 := by rintro h; rw [h] at ha; simp [vInf] at ha
  set u : Kt F := (((unifUnit (F := F)) ^ n : (Kt F)ˣ) : Kt F)
  have hu : vInf F u = n := vInf_zpow_unifUnit n
  have hu0 : u ≠ 0 := Units.ne_zero _
  let x : Fin r → Kt F := fun j => if j = p then u / a else -(A l j / a)
  have hx : ∀ j, 0 ≤ vInf F (x j) := by
    intro j
    by_cases hj : j = p
    · simp only [x, if_pos hj, vInf_div_eq u a n n hu ha, sub_self]; exact le_rfl
    · simp only [x, if_neg hj]
      exact vInf_neg_div_nonneg _ _ ha0 (by rw [ha, ← hn]; exact rowVal_le_vInf A l j)
  have hx1 : ∀ j, j < p → 1 ≤ vInf F (x j) := by
    intro j hj
    simp only [x, if_neg (ne_of_lt hj)]
    exact vInf_neg_div_one_le _ _ (by rw [ha, ← hn]; exact rowVal_lt_vInf_of_lt_pivotCol A l j hj)
  choose c hc using fun j => exists_powerSeries_of_nonneg F (x j) (hx j)
  have hlow : ∀ j, j < p → PowerSeries.constantCoeff (c j) = 0 := by
    intro j hj
    obtain ⟨q, hq⟩ := exists_powerSeries_of_one_le F (x j) (hx1 j hj)
    have : c j = PowerSeries.X * q := HahnSeries.ofPowerSeries_injective (by rw [hc, hq])
    simp [this]
  have hunit : IsUnit (c p) := by
    obtain ⟨d, hd⟩ := exists_powerSeries_of_nonneg F (a / u)
      (by rw [vInf_div_eq a u n n ha hu, sub_self]; exact le_rfl)
    have h1 : HahnSeries.ofPowerSeries ℤ F (c p * d) = HahnSeries.ofPowerSeries ℤ F 1 := by
      rw [map_mul, hc, hd, map_one]
      simp only [x, if_pos rfl]
      field_simp
    exact isUnit_iff_exists_inv.mpr ⟨d, HahnSeries.ofPowerSeries_injective h1⟩
  refine ⟨rowReplGL p c hunit, rowReplGL_mem_iwahoriR p c hunit hlow, ?_⟩
  have hK : ((M * GLOr F r (rowReplGL p c hunit) : GL (Fin r) (Kt F)) :
      Matrix (Fin r) (Fin r) (Kt F)) = A * rowRepl p x := by
    rw [Matrix.GeneralLinearGroup.coe_mul]
    change A * (rowRepl p c).map (HahnSeries.ofPowerSeries ℤ F) = _
    rw [map_rowRepl]
    congr 2
    funext j; exact hc j
  rw [hK]
  refine ⟨fun j => ?_, fun i hi j => ?_⟩
  · rw [mul_rowRepl_apply]
    by_cases hj : j = p
    · simp only [x, if_pos hj, add_zero]
      exact mul_div_cancel₀ u ha0
    · simp only [x, if_neg hj]
      rw [mul_neg, mul_div_cancel₀ _ ha0, neg_add_cancel]
  · rw [mul_rowRepl_apply, hi, zero_mul, zero_add]
    split_ifs with hj
    · rw [hj, hi]
    · rfl

/-! ### The operation `R_{kl}`: an elementary row operation in `GL_r(F[t])` -/

/-- The elementary matrix `u'_{k,l}(P) = 1 + P e_{kl} ∈ GL_r(F[t])` (`k ≠ l`). -/
def transvGL (k l : Fin r) (hkl : k ≠ l) (P : F[X]) : GL (Fin r) F[X] :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.transvection k l P)
    (by rw [Matrix.det_transvection_of_ne k l hkl]; exact isUnit_one)

lemma GLAr_transvGL_mul_apply (k l : Fin r) (hkl : k ≠ l) (P : F[X]) (M : GL (Fin r) (Kt F))
    (i j : Fin r) :
    ((GLAr F r (transvGL k l hkl P) * M : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) i j =
      if i = k then (M : Matrix (Fin r) (Fin r) (Kt F)) k j +
          polyEmb F P * (M : Matrix (Fin r) (Fin r) (Kt F)) l j
      else (M : Matrix (Fin r) (Fin r) (Kt F)) i j := by
  have h : ((GLAr F r (transvGL k l hkl P) : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) =
      Matrix.transvection k l (polyEmb F P) := by
    change (Matrix.transvection k l P).map (polyEmb F) = _
    ext a b
    simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp_all
  rw [Matrix.GeneralLinearGroup.coe_mul, h]
  split_ifs with hi
  · subst hi; rw [Matrix.transvection_mul_apply_same]
  · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hi]

lemma lt_vInf_sub_single (x : Kt F) (v : ℤ) (hx : vInf F x = v) :
    (v : WithTop ℤ) < vInf F (x - HahnSeries.single v (x.coeff v)) := by
  have h : ((v + 1 : ℤ) : WithTop ℤ) ≤ vInf F (x - HahnSeries.single v (x.coeff v)) := by
    rw [vInf, HahnSeries.le_orderTop_iff_forall]
    intro j hj
    have hj' : j ≤ v := by have := WithTop.coe_lt_coe.mp hj; omega
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rcases hj'.lt_or_eq with hlt | heq
    · rw [if_neg (ne_of_lt hlt), HahnSeries.coeff_eq_zero_of_lt_orderTop]
      · simp
      · change (j : WithTop ℤ) < vInf F x; rw [hx]; exact_mod_cast hlt
    · rw [if_pos heq, heq, sub_self]
  exact lt_of_lt_of_le (by exact_mod_cast Int.lt_succ v) h

/-- If row `k` of `M'` agrees with row `k` of `M` except in the pivot column `j_k(M)`, where the
valuation went up, then `(v_k, j_k)` increased lexicographically. -/
lemma rowVal_pivotCol_lex (M M' : Matrix (Fin r) (Fin r) (Kt F)) (k : Fin r)
    (hrow : ∀ j, j ≠ pivotCol M k → M' k j = M k j)
    (hp : rowVal M k < vInf F (M' k (pivotCol M k))) :
    rowVal M k < rowVal M' k ∨ (rowVal M' k = rowVal M k ∧ pivotCol M k < pivotCol M' k) := by
  have hle : rowVal M k ≤ rowVal M' k := by
    refine Finset.le_inf fun j _ => ?_
    by_cases hj : j = pivotCol M k
    · rw [hj]; exact le_of_lt hp
    · rw [hrow j hj]; exact rowVal_le_vInf M k j
  rcases hle.lt_or_eq with h | h
  · exact Or.inl h
  refine Or.inr ⟨h.symm, ?_⟩
  have hq := vInf_pivotCol M' k
  rw [← h] at hq
  have hne : pivotCol M' k ≠ pivotCol M k := by
    intro he; rw [he] at hq; rw [hq] at hp; exact lt_irrefl _ hp
  refine lt_of_le_of_ne (not_lt.mp fun hlt => ?_) hne.symm
  have := rowVal_lt_vInf_of_lt_pivotCol M k _ hlt
  rw [← hrow _ hne, hq] at this
  exact lt_irrefl _ this

/-- **The operation `R_{kl}`.**  Suppose row `l ≠ k` of `M` is `ϖ^{n_l} e_{j_k(M)}` and
`v_k(M) ≤ n_l`.  Let `c` be the leading coefficient of the pivot entry `a_{k,j_k}` (so
`a_{k,j_k} = c ϖ^{v_k} + ⋯`).  Then `γ = u'_{k,l}(-c t^{n_l - v_k}) ∈ GL_r(F[t])` changes only row
`k`, and increases `(v_k, j_k)` lexicographically. -/
theorem rowVal_lex_lt_transv (M : GL (Fin r) (Kt F)) (k l : Fin r) (hkl : k ≠ l) (nl : ℤ)
    (hl : IsMonoRow (M : Matrix (Fin r) (Fin r) (Kt F)) l nl
      (pivotCol (M : Matrix (Fin r) (Fin r) (Kt F)) k))
    (v : ℤ) (hv : rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) k = v) (hvl : v ≤ nl) :
    ∃ γ : GL (Fin r) F[X],
      (∀ i, i ≠ k → ∀ j, ((GLAr F r γ * M : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) i j
        = (M : Matrix (Fin r) (Fin r) (Kt F)) i j) ∧
      (rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) k <
          rowVal ((GLAr F r γ * M : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) k ∨
        (rowVal ((GLAr F r γ * M : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) k =
            rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) k ∧
          pivotCol (M : Matrix (Fin r) (Fin r) (Kt F)) k <
            pivotCol ((GLAr F r γ * M : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) k)) := by
  set A := (M : Matrix (Fin r) (Fin r) (Kt F)) with hA
  set p := pivotCol A k
  set c := (A k p).coeff v
  refine ⟨transvGL k l hkl (Polynomial.C (-c) * Polynomial.X ^ (nl - v).toNat), fun i hi j => ?_,
    rowVal_pivotCol_lex _ _ k (fun j hj => ?_) ?_⟩
  · rw [GLAr_transvGL_mul_apply, if_neg hi]
  · rw [GLAr_transvGL_mul_apply, if_pos rfl, ← hA, hl j, if_neg hj, mul_zero, add_zero]
  · rw [GLAr_transvGL_mul_apply, if_pos rfl, ← hA, hl p, if_pos rfl, polyEmb_C_mul_X_pow,
      Units.val_zpow_eq_zpow_val]
    change _ < vInf F (A k p + HahnSeries.single _ (-c) * unif F ^ nl)
    rw [unif_zpow, HahnSeries.single_mul_single, mul_one]
    have he : -((nl - v).toNat : ℤ) + nl = v := by omega
    rw [he, hv]
    have hs : HahnSeries.single v (-c) = -HahnSeries.single v c := by
      ext m; simp [HahnSeries.coeff_single]
    rw [hs, ← sub_eq_add_neg]
    exact lt_vInf_sub_single _ v (by rw [vInf_pivotCol, hv])

end GLrBuilding
