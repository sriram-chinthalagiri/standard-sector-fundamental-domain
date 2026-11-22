import GLrFundamentalDomain.RowValuation

/-!
# Reduction of a pointed chamber to the standard apartment

We prove `exists_apartment_reduction`: for every `g ∈ GL_r(K)` there is `γ ∈ GL_r(F[t])` such that
`γ · [g]` is a pointed chamber `[diag(ϖ^{n₀}, …, ϖ^{n_{r-1}}) · w]` of the standard apartment.
The notation `v_i`, `j_i`, `IsMonoRow` and the operations `C_l`, `R_{kl}` are set up in
`RowValuation.lean`.

## The induction

`RedInv k M` (the hypothesis `I_k`) says that there are `n : Fin r → ℤ` and `σ : Fin r → Fin r`
with
* for `k ≤ i ≤ r-1`, row `i` of `M` is `ϖ^{n_i} e_{σ(i)}` (so `σ(i) = j_i(M)`);
* for `k ≤ i < i'`: `n_i < n_{i'}`, or `n_i = n_{i'}` and `σ(i) < σ(i')`.
The rows `0, …, k-1` are arbitrary.

* Start (`exists_redInv_top`, the step `I_{r-1}`): apply `C_{r-1}` on the right.
* Step (`redInv_step`, `I_{k+1} ⟹ I_k`).  Let `g` be the current matrix (rows `> k` monomial,
  `p = j_k(g)`, `v = v_k(g)`):
  - (Q1) If no block row `l > k` has its `ϖ^{n_l}` in column `p`, then `σ_k · g · C_k(g)` satisfies
    `I_k`: `C_k` does not touch the block rows (they have `0` in column `p`), and a permutation
    `σ_k` of the rows `k, …, r-1` sorts them.  Stop.
  - Otherwise let `l` be that block row.
    - (Q2) If `v ≤ n_l`: replace `g` by `R_{kl}(g) · g`, where
      `R_{kl}(g) = u'_{k,l}(-c t^{n_l - v})` and `c` is the leading coefficient of `a_{kp}`.
      Only row `k` changes, and `(v_k, j_k)` increases lexicographically.  Go to (Q1).
    - (Q3) If `v > n_l`: replace `g` by `(k l) · g · C_l((k l) · g)` (`q3_step`).  After the
      transposition, row `l` is the old row `k`, and `C_l((k l) · g)` clears it to `ϖ^{v} e_p`;
      among the rows `> k` it changes only row `l` (the other block rows have `0` in column `p`).
      The new row `k` is the old row `l` times an Iwahori matrix, so it has valuation `n_l < v`
      and still has pivot column `p` (`pivotCol_mul_GLOr_of_isMonoRow`).  `∑ v_i` and `j_k` are
      unchanged.  Go to (Q1).  There row `l` is `ϖ^{v} e_p` with `p = j_k` and `v_k = n_l < v`,
      so the next step is always (Q2) with the same `l`.
* Termination: the pair `(∑_i v_i, j_k)` increases lexicographically along each of the two loops
  (Q1) → (Q2) → (Q1) (`q2_step`) and (Q1) → (Q2) → (Q3) → (Q1) → (Q2) → (Q1) (`q3_step`, then
  `q2_step`).  It is bounded: `∑_i v_i ≤ v_∞(det g)` and `j_k ≤ r - 1`.
* End (`redInv_zero_eq`): `RedInv 0 M` means `M = diag(ϖ^{n₀}, …, ϖ^{n_{r-1}}) · P_σ`, where `σ`
  is a permutation (it is injective because `det M ≠ 0`), and `P_σ` has its `1`s at `(i, σ(i))`.
-/

open Matrix Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

open Classical

variable {F : Type*} [Field F] {r : ℕ}

/-! ### The induction hypothesis `I_k` -/

/-- The induction hypothesis `I_k` for `M`: rows `k, …, r-1` are `ϖ^{n_i} e_{σ(i)}`, sorted
by `n_k ≤ ⋯ ≤ n_{r-1}`, with ties broken by `σ`.  Rows `0, …, k-1` are arbitrary. -/
def RedInv (k : ℕ) (M : GL (Fin r) (Kt F)) : Prop :=
  ∃ (n : Fin r → ℤ) (σ : Fin r → Fin r),
    (∀ i : Fin r, k ≤ (i : ℕ) → IsMonoRow (M : Matrix (Fin r) (Fin r) (Kt F)) i (n i) (σ i)) ∧
    (∀ i i' : Fin r, k ≤ (i : ℕ) → i < i' → n i < n i' ∨ (n i = n i' ∧ σ i < σ i'))

/-- The rows `> k` are monomial (without ordering). -/
def BlockMono (k : ℕ) (M : GL (Fin r) (Kt F)) : Prop :=
  ∃ (n : Fin r → ℤ) (σ : Fin r → Fin r),
    ∀ i : Fin r, k < (i : ℕ) → IsMonoRow (M : Matrix (Fin r) (Fin r) (Kt F)) i (n i) (σ i)

/-! ### Integer-valued row valuations -/

/-- `v_i(M)` as an integer (`M` is invertible, so no row is zero). -/
def rv (M : GL (Fin r) (Kt F)) (i : Fin r) : ℤ :=
  (rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) i).untop (rowVal_ne_top M i)

lemma coe_rv (M : GL (Fin r) (Kt F)) (i : Fin r) :
    (rv M i : WithTop ℤ) = rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) i :=
  WithTop.coe_untop _ _

lemma rv_eq_iff (M N : GL (Fin r) (Kt F)) (i j : Fin r) :
    rv M i = rv N j ↔ rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) i =
      rowVal (N : Matrix (Fin r) (Fin r) (Kt F)) j := by
  rw [← coe_rv, ← coe_rv, WithTop.coe_inj]

lemma rv_le_iff (M N : GL (Fin r) (Kt F)) (i j : Fin r) :
    rv M i ≤ rv N j ↔ rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) i ≤
      rowVal (N : Matrix (Fin r) (Fin r) (Kt F)) j := by
  rw [← coe_rv, ← coe_rv, WithTop.coe_le_coe]

lemma rv_lt_iff (M N : GL (Fin r) (Kt F)) (i j : Fin r) :
    rv M i < rv N j ↔ rowVal (M : Matrix (Fin r) (Fin r) (Kt F)) i <
      rowVal (N : Matrix (Fin r) (Fin r) (Kt F)) j := by
  rw [← coe_rv, ← coe_rv, WithTop.coe_lt_coe]

lemma rv_of_isMonoRow {M : GL (Fin r) (Kt F)} {i : Fin r} {n : ℤ} {j : Fin r}
    (h : IsMonoRow (M : Matrix (Fin r) (Fin r) (Kt F)) i n j) : rv M i = n := by
  have := h.rowVal
  rw [← coe_rv] at this
  exact_mod_cast this

/-- `∑_i v_i(M)` as an integer. -/
def rvSum (M : GL (Fin r) (Kt F)) : ℤ := ∑ i, rv M i

lemma rowValSum_eq_rvSum (M : GL (Fin r) (Kt F)) :
    rowValSum (M : Matrix (Fin r) (Fin r) (Kt F)) = (rvSum M : WithTop ℤ) := by
  simp only [rowValSum, rvSum, WithTop.coe_sum, coe_rv]

lemma IsMonoRow.permGL_mul {M : GL (Fin r) (Kt F)} {w : Equiv.Perm (Fin r)} {i : Fin r} {n : ℤ}
    {j : Fin r} (h : IsMonoRow (M : Matrix (Fin r) (Fin r) (Kt F)) (w i) n j) :
    IsMonoRow ((permGL r (Kt F) w * M : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) i n j :=
  fun j' => by rw [Matrix.GeneralLinearGroup.coe_mul, permGL_mul_apply]; exact h j'

/-! ### The operation (Q3): `g ↦ (k l) · g · C_l((k l) · g)` -/

/-- **The operation (Q3)** `g ↦ (k l) · g · C_l((k l) · g)`.  Suppose row `l ≠ k` of `g` is
`ϖ^{n_l} e_p` with `p = j_k(g)`, and `n_l < v_k(g)`.  Put `g₁ = (k l) · g` and let `κ` be the
Iwahori matrix `C_l(g₁)` that clears row `l` of `g₁` (which is the old row `k`).  Then, for
`g' = g₁ · κ`:
* row `l` of `g'` is `ϖ^{v_k(g)} e_p`;
* every row `i ≠ k, l` of `g` with `a_{ip} = 0` is unchanged;
* `v_i(g') = v_{(k l)(i)}(g)` for all `i`, so `∑_i v_i(g') = ∑_i v_i(g)`;
* `v_k(g') = n_l < v_k(g)`: the valuation of row `k` strictly **decreases**. -/
theorem q3_step (N : GL (Fin r) (Kt F)) (k l : Fin r) (nl : ℤ)
    (hmonol : IsMonoRow (N : Matrix (Fin r) (Fin r) (Kt F)) l nl
      (pivotCol (N : Matrix (Fin r) (Fin r) (Kt F)) k))
    (hlt : nl < rv N k) :
    ∃ κ ∈ iwahoriR F r,
      IsMonoRow ((permGL r (Kt F) (Equiv.swap k l) * N * GLOr F r κ : GL (Fin r) (Kt F)) :
        Matrix (Fin r) (Fin r) (Kt F)) l (rv N k) (pivotCol (N : Matrix (Fin r) (Fin r) (Kt F)) k) ∧
      (∀ i, i ≠ k → i ≠ l →
        (N : Matrix (Fin r) (Fin r) (Kt F)) i (pivotCol (N : Matrix (Fin r) (Fin r) (Kt F)) k) = 0 →
        ∀ j, ((permGL r (Kt F) (Equiv.swap k l) * N * GLOr F r κ : GL (Fin r) (Kt F)) :
          Matrix (Fin r) (Fin r) (Kt F)) i j = (N : Matrix (Fin r) (Fin r) (Kt F)) i j) ∧
      (∀ i, rv (permGL r (Kt F) (Equiv.swap k l) * N * GLOr F r κ) i = rv N (Equiv.swap k l i)) ∧
      rvSum (permGL r (Kt F) (Equiv.swap k l) * N * GLOr F r κ) = rvSum N ∧
      rv (permGL r (Kt F) (Equiv.swap k l) * N * GLOr F r κ) k = nl ∧
      rv (permGL r (Kt F) (Equiv.swap k l) * N * GLOr F r κ) k < rv N k := by
  set w := Equiv.swap k l
  set N1 := permGL r (Kt F) w * N
  have hrow : ∀ i j, (N1 : Matrix (Fin r) (Fin r) (Kt F)) i j =
      (N : Matrix (Fin r) (Fin r) (Kt F)) (w i) j := fun i j => by
    simp only [N1, Matrix.GeneralLinearGroup.coe_mul, permGL_mul_apply]
  have hv1 : rowVal (N1 : Matrix (Fin r) (Fin r) (Kt F)) l = rv N k := by
    rw [rowVal_permGL_mul, coe_rv]; simp [w]
  have hp1 : pivotCol (N1 : Matrix (Fin r) (Fin r) (Kt F)) l =
      pivotCol (N : Matrix (Fin r) (Fin r) (Kt F)) k := by
    rw [pivotCol_permGL_mul]; simp [w]
  -- `κ = C_l((k l) · g)`
  obtain ⟨κ, hκ, hmk, hfix⟩ := exists_clearRow N1 l (rv N k) hv1
  rw [hp1] at hmk hfix
  have hrv : ∀ i, rv (N1 * GLOr F r κ) i = rv N (w i) := fun i =>
    (rv_eq_iff _ _ _ _).mpr (by rw [rowVal_mul_GLOr, rowVal_permGL_mul])
  have hk : rv (N1 * GLOr F r κ) k = nl := by
    rw [hrv]; simp only [w, Equiv.swap_apply_left]; exact rv_of_isMonoRow hmonol
  refine ⟨κ, hκ, hmk, fun i hik hil h0 j => ?_, hrv, ?_, hk, hk ▸ hlt⟩
  · have hwi : w i = i := Equiv.swap_apply_of_ne_of_ne hik hil
    rw [hfix i (by rw [hrow, hwi]; exact h0) j, hrow, hwi]
  · unfold rvSum
    simp only [hrv]
    exact Equiv.sum_comp w (rv N)

/-! ### Sorting the block (the permutation `σ_k`) -/

/-- A permutation of the rows, preserving the rows `≥ k`, which sorts the rows `≥ k` by
`(n_i, σ(i))` lexicographically (given that `σ` is injective on the rows `≥ k`). -/
lemma exists_sort_block (k : ℕ) (n : Fin r → ℤ) (σ : Fin r → Fin r)
    (hinj : ∀ i i' : Fin r, k ≤ (i : ℕ) → k ≤ (i' : ℕ) → σ i = σ i' → i = i') :
    ∃ w : Equiv.Perm (Fin r), (∀ i : Fin r, k ≤ (i : ℕ) → k ≤ (w i : ℕ)) ∧
      ∀ i i' : Fin r, k ≤ (i : ℕ) → i < i' →
        n (w i) < n (w i') ∨ (n (w i) = n (w i') ∧ σ (w i) < σ (w i')) := by
  let f : Fin r → Bool ×ₗ (ℤ ×ₗ Fin r) :=
    fun i => toLex (decide (k ≤ (i : ℕ)), toLex (n i, σ i))
  set w := Tuple.sort f
  have hmono : Monotone (f ∘ w) := Tuple.monotone_sort f
  have hle : ∀ a b : Fin r, a ≤ b → (decide (k ≤ (w a : ℕ)) < decide (k ≤ (w b : ℕ)) ∨
      (decide (k ≤ (w a : ℕ)) = decide (k ≤ (w b : ℕ)) ∧
        toLex (n (w a), σ (w a)) ≤ toLex (n (w b), σ (w b)))) :=
    fun a b hab => Prod.Lex.toLex_le_toLex.mp (hmono hab)
  have hblock : ∀ i : Fin r, k ≤ (i : ℕ) → k ≤ (w i : ℕ) := by
    intro i hi
    by_contra hlt
    push_neg at hlt
    have hall : ∀ a : Fin r, a ≤ i → (w a : ℕ) < k := by
      intro a ha
      by_contra h
      push_neg at h
      have e1 : decide (k ≤ (w a : ℕ)) = true := by simpa using h
      have e2 : decide (k ≤ (w i : ℕ)) = false := by simpa using hlt
      rcases hle a i ha with h1 | h1
      · rw [e1, e2] at h1; exact absurd h1 (by decide)
      · rw [e1, e2] at h1; exact absurd h1.1 (by decide)
    have hcard := Finset.card_le_card_of_injOn (fun a : Fin r => (w a : ℕ))
      (s := Finset.Iic i) (t := Finset.range k)
      (fun a ha => by simpa using hall a (by simpa using ha))
      (fun a _ b _ h => w.injective (Fin.ext h))
    rw [Fin.card_Iic, Finset.card_range] at hcard
    omega
  refine ⟨w, hblock, fun i i' hi hii' => ?_⟩
  have hi' : k ≤ (i' : ℕ) := le_trans hi (le_of_lt hii')
  rcases hle i i' (le_of_lt hii') with h1 | ⟨-, h1⟩
  · simp [hblock i hi, hblock i' hi'] at h1
  rcases Prod.Lex.toLex_le_toLex.mp h1 with h2 | ⟨h2, h3⟩
  · exact Or.inl h2
  refine Or.inr ⟨h2, lt_of_le_of_ne h3 fun he => ?_⟩
  exact absurd (w.injective (hinj _ _ (hblock i hi) (hblock i' hi') he)) (ne_of_lt hii')

/-- If the rows `≥ k` of `M` are monomial, a permutation `σ_k` of the rows `≥ k` gives `I_k`. -/
lemma redInv_of_mono (k : ℕ) (M : GL (Fin r) (Kt F)) (n : Fin r → ℤ) (σ : Fin r → Fin r)
    (h : ∀ i : Fin r, k ≤ (i : ℕ) → IsMonoRow (M : Matrix (Fin r) (Fin r) (Kt F)) i (n i) (σ i)) :
    ∃ w : Equiv.Perm (Fin r), RedInv k (permGL r (Kt F) w * M) := by
  obtain ⟨w, hw, hsort⟩ := exists_sort_block k n σ
    fun i i' hi hi' he => IsMonoRow.eq_of_col_eq (h i hi) (he ▸ h i' hi')
  exact ⟨w, n ∘ w, σ ∘ w, fun i hi => (h (w i) (hw i hi)).permGL_mul, hsort⟩

/-! ### Start and end of the induction -/

/-- **Start of the induction** (the step `I_{r-1}`): applying `C_{r-1}` on the right makes the last
row `ϖ^{v_{r-1}} e_{j_{r-1}}`. -/
theorem exists_redInv_top (hr : 0 < r) (g : GL (Fin r) (Kt F)) :
    ∃ κ ∈ iwahoriR F r, RedInv (r - 1) (g * GLOr F r κ) := by
  set l : Fin r := ⟨r - 1, by omega⟩
  obtain ⟨κ, hκ, hmono, -⟩ := exists_clearRow g l (rv g l) (coe_rv g l).symm
  refine ⟨κ, hκ, fun _ => rv g l, fun _ => pivotCol (g : Matrix (Fin r) (Fin r) (Kt F)) l,
    fun i hi => ?_, fun i i' hi hii' => ?_⟩
  · have : i = l := Fin.ext (by have := i.isLt; simp [l]; omega)
    rw [this]; exact hmono
  · exfalso; have := i'.isLt; have : (i : ℕ) < i' := hii'; omega

/-- **End of the induction**: `I_0(M)` means `M = diag(ϖ^{n₀}, …, ϖ^{n_{r-1}}) · P_w` for a
permutation `w` (with `w(i) = j_i(M)`). -/
theorem redInv_zero_eq (M : GL (Fin r) (Kt F)) (hM : RedInv 0 M) :
    ∃ (d : Fin r → ℤ) (w : Equiv.Perm (Fin r)), M = diagPow d * permGL r (Kt F) w := by
  obtain ⟨n, σ, hmono, -⟩ := hM
  have hinj : Function.Injective σ := fun i i' he =>
    IsMonoRow.eq_of_col_eq (hmono i (Nat.zero_le _)) (he ▸ hmono i' (Nat.zero_le _))
  set w := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
  refine ⟨n, w, Units.ext (Matrix.ext fun i j => ?_)⟩
  have h1 : ((diagPow n * permGL r (Kt F) w : GL (Fin r) (Kt F)) :
      Matrix (Fin r) (Fin r) (Kt F)) i j =
        if w i = j then (((unifUnit (F := F)) ^ n i : (Kt F)ˣ) : Kt F) else 0 := by
    simp [diagPow, permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  rw [h1, hmono i (Nat.zero_le _) j]
  simp only [w, Equiv.ofBijective_apply, eq_comm]

/-! ### The pivot column after right multiplication by the Iwahori subgroup -/

/-- Elements of `ϖ O` have valuation `≥ 1`. -/
lemma one_le_vInf_ofPowerSeries {x : PowerSeries F} (hx : PowerSeries.constantCoeff x = 0) :
    1 ≤ vInf F (HahnSeries.ofPowerSeries ℤ F x) := by
  obtain ⟨y, rfl⟩ := PowerSeries.X_dvd_iff.mpr hx
  rw [map_mul, vInf_mul, HahnSeries.ofPowerSeries_X]
  have h1 : vInf F (HahnSeries.single (1 : ℤ) (1 : F)) = 1 := vInf_unif F
  rw [h1]
  calc (1 : WithTop ℤ) = 1 + 0 := by simp
    _ ≤ _ := add_le_add le_rfl (vInf_ofPowerSeries_nonneg F y)

/-- If row `l` of `M` is `ϖ^n e_p` and `κ ∈ I`, then row `l` of `M κ` is `ϖ^n` times row `p` of
`κ`, whose entries left of the diagonal lie in `ϖ O` and whose diagonal entry is a unit.  So the
pivot column of row `l` is still `p`. -/
lemma pivotCol_mul_GLOr_of_isMonoRow (M : GL (Fin r) (Kt F)) {κ : GL (Fin r) (PowerSeries F)}
    (hκ : κ ∈ iwahoriR F r) {l : Fin r} {n : ℤ} {p : Fin r}
    (h : IsMonoRow (M : Matrix (Fin r) (Fin r) (Kt F)) l n p) :
    pivotCol ((M * GLOr F r κ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) l = p := by
  set B := ((M * GLOr F r κ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F))
  have hentry : ∀ j, B l j = (((unifUnit (F := F)) ^ n : (Kt F)ˣ) : Kt F) *
      HahnSeries.ofPowerSeries ℤ F ((κ : Matrix (Fin r) (Fin r) (PowerSeries F)) p j) := by
    intro j
    simp only [B, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single p]
    · rw [h p, if_pos rfl]; rfl
    · intro m _ hm; rw [h m, if_neg hm, zero_mul]
    · simp
  have hval : ∀ j, vInf F (B l j) = n + vInf F (HahnSeries.ofPowerSeries ℤ F
      ((κ : Matrix (Fin r) (Fin r) (PowerSeries F)) p j)) := fun j => by
    rw [hentry, vInf_mul, vInf_zpow_unifUnit]
  have hrv : rowVal B l = n := by
    simp only [B]; rw [rowVal_mul_GLOr, h.rowVal]
  -- the diagonal entry `κ_{pp}` is a unit
  have hdiag : PowerSeries.constantCoeff ((κ : Matrix (Fin r) (Fin r) (PowerSeries F)) p p) ≠ 0 := by
    have hdet := Matrix.det_of_upperTriangular (M := ((Matrix.GeneralLinearGroup.map
      (PowerSeries.constantCoeff (R := F)) κ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) hκ
    have hne := (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map
      (PowerSeries.constantCoeff (R := F)) κ)).ne_zero
    intro h0
    apply hne
    change Matrix.det _ = 0
    rw [hdet]
    exact Finset.prod_eq_zero (Finset.mem_univ p) h0
  have hu : IsUnit ((κ : Matrix (Fin r) (Fin r) (PowerSeries F)) p p) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hdiag)
  have hp : vInf F (B l p) = rowVal B l := by
    rw [hval, hrv, ← hu.unit_spec, vInf_ofPowerSeries_unit, add_zero]
  refine le_antisymm (Finset.min'_le _ _ (by simp [hp])) (not_lt.mp fun hlt => ?_)
  have h1 := vInf_pivotCol B l
  rw [hval, hrv] at h1
  have h0 : PowerSeries.constantCoeff
      ((κ : Matrix (Fin r) (Fin r) (PowerSeries F)) p (pivotCol B l)) = 0 := hκ (i := p) hlt
  have h2 := one_le_vInf_ofPowerSeries h0
  generalize vInf F (HahnSeries.ofPowerSeries ℤ F
      ((κ : Matrix (Fin r) (Fin r) (PowerSeries F)) p (pivotCol B l))) = a at h1 h2
  induction a with
  | top => simp at h1
  | coe a =>
    have h1' : n + a = n := by exact_mod_cast h1
    have h2' : (1 : ℤ) ≤ a := by exact_mod_cast h2
    omega

/-! ### The operation (Q2) and the measure `(∑_i v_i, j_k)` -/

/-- **The operation (Q2)** `R_{kl}`, in terms of the measure `(∑_i v_i, j_k)`: if row `l ≠ k` is
`ϖ^{n_l} e_{j_k}` and `v_k ≤ n_l`, then `R_{kl}` changes only row `k`, and either `∑_i v_i`
strictly increases, or it stays the same and `j_k` strictly increases. -/
theorem q2_step (N : GL (Fin r) (Kt F)) (k l : Fin r) (hkl : k ≠ l) (nl : ℤ)
    (hl : IsMonoRow (N : Matrix (Fin r) (Fin r) (Kt F)) l nl
      (pivotCol (N : Matrix (Fin r) (Fin r) (Kt F)) k))
    (hvl : rv N k ≤ nl) :
    ∃ γ : GL (Fin r) F[X],
      (∀ i, i ≠ k → ∀ j, ((GLAr F r γ * N : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) i j
        = (N : Matrix (Fin r) (Fin r) (Kt F)) i j) ∧
      (rvSum N < rvSum (GLAr F r γ * N) ∨
        (rvSum (GLAr F r γ * N) = rvSum N ∧
          pivotCol (N : Matrix (Fin r) (Fin r) (Kt F)) k <
            pivotCol ((GLAr F r γ * N : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) k)) := by
  obtain ⟨γ, hfix, hlex⟩ := rowVal_lex_lt_transv N k l hkl nl hl (rv N k) (coe_rv N k).symm hvl
  have hrow : ∀ i, i ≠ k → rv (GLAr F r γ * N) i = rv N i := fun i hi =>
    (rv_eq_iff _ _ _ _).mpr (by unfold rowVal; congr 1; funext j; rw [hfix i hi j])
  have hsum : rvSum (GLAr F r γ * N) - rvSum N = rv (GLAr F r γ * N) k - rv N k := by
    unfold rvSum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
      ← Finset.add_sum_erase _ (rv N) (Finset.mem_univ k),
      Finset.sum_congr rfl fun i hi => hrow i (Finset.ne_of_mem_erase hi)]
    ring
  refine ⟨γ, hfix, ?_⟩
  rcases hlex with h | ⟨h1, h2⟩
  · left
    have := (rv_lt_iff N (GLAr F r γ * N) k k).mpr h
    omega
  · right
    have h1' := (rv_eq_iff (GLAr F r γ * N) N k k).mpr h1
    exact ⟨by omega, h2⟩

/-! ### The induction step -/

/-- **Induction step** `I_{k+1} ⟹ I_k`, by the algorithm (Q1)–(Q3) of the module docstring.
Termination uses the measure `(∑_i v_i, j_k)`: a (Q2)-pass raises it lexicographically
(`q2_step`), and a (Q3)-pass is always immediately followed by a (Q2)-pass, the two together again
raising it. -/
theorem redInv_step {k : ℕ} (hk : k < r) (M : GL (Fin r) (Kt F)) (hM : RedInv (k + 1) M) :
    ∃ γ : GL (Fin r) F[X], ∃ κ ∈ iwahoriR F r, RedInv k (GLAr F r γ * M * GLOr F r κ) := by
  set kk : Fin r := ⟨k, hk⟩
  -- the goal, and its transfer along `N ↦ γ' N κ'`
  let Goal : GL (Fin r) (Kt F) → Prop := fun N =>
    ∃ γ : GL (Fin r) F[X], ∃ κ ∈ iwahoriR F r, RedInv k (GLAr F r γ * N * GLOr F r κ)
  have transfer : ∀ (N : GL (Fin r) (Kt F)) (γ' : GL (Fin r) F[X]) (κ' : GL (Fin r) (PowerSeries F)),
      κ' ∈ iwahoriR F r → Goal (GLAr F r γ' * N * GLOr F r κ') → Goal N := by
    rintro N γ' κ' hκ' ⟨γ, κ, hκ, h⟩
    refine ⟨γ * γ', κ' * κ, (iwahoriR F r).mul_mem hκ' hκ, ?_⟩
    simpa [map_mul, mul_assoc] using h
  -- the invariant integer `D = v_∞(det M)`
  obtain ⟨D, hD⟩ : ∃ D : ℤ, vInf F (M : Matrix (Fin r) (Fin r) (Kt F)).det = D :=
    (WithTop.ne_top_iff_exists.mp (by
      rw [Ne, vInf_eq_top_iff]; exact (Matrix.GeneralLinearGroup.det M).ne_zero)).imp
      fun _ h => h.symm
  have hSD : ∀ N : GL (Fin r) (Kt F), vInf F (N : Matrix (Fin r) (Fin r) (Kt F)).det = D →
      rvSum N ≤ D := fun N hN => by
    have := rowValSum_le_vInf_det (N : Matrix (Fin r) (Fin r) (Kt F))
    rwa [rowValSum_eq_rvSum, hN, WithTop.coe_le_coe] at this
  -- induction on the measure `(∑_i v_i, j_k)`, bounded by `(D, r - 1)`
  suffices key : ∀ a c : ℕ, ∀ N : GL (Fin r) (Kt F),
      vInf F (N : Matrix (Fin r) (Fin r) (Kt F)).det = D → BlockMono k N →
      (D - rvSum N).toNat = a →
      r - (pivotCol (N : Matrix (Fin r) (Fin r) (Kt F)) kk : ℕ) = c → Goal N by
    obtain ⟨n, σ, hn, -⟩ := hM
    exact key _ _ M hD ⟨n, σ, fun i hi => hn i hi⟩ rfl rfl
  intro a
  induction a using Nat.strong_induction_on with
  | _ a iha =>
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  intro N hdet hblk ha hc
  -- continuing the loop from `N' = γ' N κ'`, if the measure `(∑_i v_i, j_k)` went up
  have recurse : ∀ (γ' : GL (Fin r) F[X]) (κ' : GL (Fin r) (PowerSeries F)), κ' ∈ iwahoriR F r →
      BlockMono k (GLAr F r γ' * N * GLOr F r κ') →
      (rvSum N < rvSum (GLAr F r γ' * N * GLOr F r κ') ∨
        (rvSum (GLAr F r γ' * N * GLOr F r κ') = rvSum N ∧
          pivotCol (N : Matrix (Fin r) (Fin r) (Kt F)) kk <
            pivotCol ((GLAr F r γ' * N * GLOr F r κ' : GL (Fin r) (Kt F)) :
              Matrix (Fin r) (Fin r) (Kt F)) kk)) → Goal N := by
    intro γ' κ' hκ' hblk' hlt
    refine transfer N γ' κ' hκ' ?_
    set N' := GLAr F r γ' * N * GLOr F r κ'
    have hdet' : vInf F (N' : Matrix (Fin r) (Fin r) (Kt F)).det = D := by
      rw [vInf_det_GLAr_mul_mul_GLOr, hdet]
    have hS := hSD N hdet
    have hS' := hSD N' hdet'
    rcases hlt with h | ⟨h1, h2⟩
    · exact iha _ (by omega) _ N' hdet' hblk' rfl rfl
    · have := (pivotCol ((N' : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) kk).isLt
      exact ihc _ (by omega) N' hdet' hblk' (by rw [h1, ha]) rfl
  obtain ⟨n, σ, hmono⟩ := hblk
  set A := (N : Matrix (Fin r) (Fin r) (Kt F)) with hA
  set p := pivotCol A kk
  set v := rv N kk
  by_cases hQ1 : ∃ l : Fin r, k < (l : ℕ) ∧ σ l = p
  · obtain ⟨l, hl, hσl⟩ := hQ1
    have hkl : kk ≠ l := fun h => by rw [← h] at hl; exact lt_irrefl _ hl
    have hmonol : IsMonoRow A l (n l) p := hσl ▸ hmono l hl
    by_cases hvl : v ≤ n l
    · -- (Q2): the operation `R_{kl}`
      obtain ⟨γ, hfix, hlt⟩ := q2_step N kk l hkl (n l) hmonol hvl
      have e : GLAr F r γ * N * GLOr F r 1 = GLAr F r γ * N := by simp
      refine recurse γ 1 (iwahoriR F r).one_mem ?_ ?_
      · rw [e]
        refine ⟨n, σ, fun i hi j => ?_⟩
        have hik : i ≠ kk := fun h => by rw [h] at hi; exact lt_irrefl _ hi
        rw [hfix i hik j]; exact hmono i hi j
      · rw [e]; exact hlt
    · -- (Q3): the transposition `(k l)`, then `C_l((k l) · g)`; after it, (Q1) and (Q2) apply
      -- with the same `l`, so we perform that (Q2) step `R_{kl}` right away
      push_neg at hvl
      obtain ⟨κ, hκ, hmk, hfix, -, hsum, hk1, -⟩ := q3_step N kk l (n l) hmonol hvl
      set w := Equiv.swap kk l
      set N1 := permGL r (Kt F) w * N * GLOr F r κ with hN1
      -- `j_k` is unchanged by (Q3)
      have hp1 : pivotCol (N1 : Matrix (Fin r) (Fin r) (Kt F)) kk = p := by
        have hm : IsMonoRow A (w kk) (n l) p := by
          simp only [w, Equiv.swap_apply_left]; exact hmonol
        exact pivotCol_mul_GLOr_of_isMonoRow _ hκ hm.permGL_mul
      have hmk' : IsMonoRow (N1 : Matrix (Fin r) (Fin r) (Kt F)) l v
          (pivotCol (N1 : Matrix (Fin r) (Fin r) (Kt F)) kk) := by
        rw [hp1]; exact hmk
      -- the (Q2) step `R_{kl}` on `N1`
      obtain ⟨γ2, hfix2, hlt2⟩ := q2_step N1 kk l hkl v hmk' (by rw [hk1]; exact le_of_lt hvl)
      have e : GLAr F r (γ2 * permGL r F[X] w) * N * GLOr F r κ = GLAr F r γ2 * N1 := by
        rw [map_mul, GLAr_permGL]; simp only [N1, mul_assoc]
      refine recurse (γ2 * permGL r F[X] w) κ hκ ?_ ?_
      · rw [e]
        refine ⟨Function.update n l v, Function.update σ l p, fun i hi j => ?_⟩
        have hik : i ≠ kk := fun h => by rw [h] at hi; exact lt_irrefl _ hi
        rw [hfix2 i hik j]
        by_cases hil : i = l
        · subst hil
          simp only [Function.update_self]
          exact hmk j
        · simp only [Function.update_of_ne hil]
          have h0 : A i p = 0 := by
            rw [hmono i hi p, if_neg]
            intro hp
            exact hil (IsMonoRow.eq_of_col_eq (hp ▸ hmono i hi) hmonol)
          rw [hfix i hik hil h0 j]; exact hmono i hi j
      · rw [e]
        rcases hlt2 with h | ⟨h1, h2⟩
        · left; rw [← hsum]; exact h
        · right; rw [hp1] at h2; exact ⟨h1.trans hsum, h2⟩
  · -- (Q1) answered "no": `C_k`, then sort the rows `≥ k`
    push_neg at hQ1
    obtain ⟨κ, hκ, hmk, hfix⟩ := exists_clearRow N kk v (coe_rv N kk).symm
    have hmono' : ∀ i : Fin r, k ≤ (i : ℕ) →
        IsMonoRow ((N * GLOr F r κ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) i
          (Function.update n kk v i) (Function.update σ kk p i) := by
      intro i hi
      by_cases hik : i = kk
      · subst hik; simpa using hmk
      · have hi' : k < (i : ℕ) := lt_of_le_of_ne hi fun h => hik (Fin.ext h.symm)
        rw [Function.update_of_ne hik, Function.update_of_ne hik]
        have h0 : A i p = 0 := by
          rw [hmono i hi' p, if_neg]
          intro hp; exact hQ1 i hi' hp.symm
        intro j
        rw [hfix i h0 j]; exact hmono i hi' j
    obtain ⟨w, hw⟩ := redInv_of_mono k _ _ _ hmono'
    refine ⟨permGL r F[X] w, κ, hκ, ?_⟩
    rw [GLAr_permGL, mul_assoc]
    exact hw

/-- **The descending induction**: for every `g ∈ GL_r(K)` there are `γ ∈ GL_r(F[t])` and `κ ∈ I`
with `I_0(γ g κ)`. -/
theorem exists_redInv_zero (g : GL (Fin r) (Kt F)) :
    ∃ γ : GL (Fin r) F[X], ∃ κ ∈ iwahoriR F r, RedInv 0 (GLAr F r γ * g * GLOr F r κ) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact ⟨1, 1, (iwahoriR F 0).one_mem, fun _ => 0, fun i => i, fun i => i.elim0,
      fun i => i.elim0⟩
  suffices H : ∀ j : ℕ, j < r → ∃ γ : GL (Fin r) F[X], ∃ κ ∈ iwahoriR F r,
      RedInv (r - 1 - j) (GLAr F r γ * g * GLOr F r κ) by
    simpa using H (r - 1) (by omega)
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨κ, hκ, h⟩ := exists_redInv_top hr g
    exact ⟨1, κ, hκ, by simpa using h⟩
  | succ j ih =>
    intro hj
    obtain ⟨γ, κ, hκ, h⟩ := ih (by omega)
    have hk : r - 1 - (j + 1) + 1 = r - 1 - j := by omega
    obtain ⟨γ', κ', hκ', h'⟩ := redInv_step (k := r - 1 - (j + 1)) (by omega) _ (hk ▸ h)
    refine ⟨γ' * γ, κ * κ', (iwahoriR F r).mul_mem hκ hκ', ?_⟩
    simpa [map_mul, mul_assoc] using h'

/-- The Iwahori subgroup lies in the stabilizer `K^× · I` of the standard pointed chamber. -/
lemma GLOr_mem_chamberStab {κ : GL (Fin r) (PowerSeries F)} (hκ : κ ∈ iwahoriR F r) :
    GLOr F r κ ∈ chamberStab F r :=
  ⟨1, κ, hκ, by simp⟩

/-- **Reduction to the standard apartment.**  For every pointed chamber `c` there is
`γ ∈ GL_r(F[t])` such that `γ c` lies in the standard apartment. -/
theorem exists_apartment_reduction (c : PChamber F r) :
    ∃ (γ : GL (Fin r) F[X]) (d : Fin r → ℤ) (w : Equiv.Perm (Fin r)),
      GLAr F r γ • c = apartmentPC d w := by
  induction c using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨γ, κ, hκ, h0⟩ := exists_redInv_zero g
    obtain ⟨d, w, hdw⟩ := redInv_zero_eq _ h0
    refine ⟨γ, d, w, ?_⟩
    rw [apartmentPC, ← hdw, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa [mul_assoc] using GLOr_mem_chamberStab hκ

end GLrBuilding
