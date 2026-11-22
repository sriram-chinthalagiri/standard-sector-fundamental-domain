import GLrFundamentalDomain.ApartmentReduction

/-!
# An example where step (Q3) lowers `v_k`

For `r = 2`, `k = 0`, take
`g = [[ϖ, ϖ²], [1, 0]]` (with `ϖ = t⁻¹`).
* `I_1(g)` holds: row `1` is `ϖ⁰ e_0`.
* Row `0` has `v_0(g) = 1` and pivot column `j_0(g) = 0`. That is the column of the block row
  `l = 1`, so (Q1) passes to (Q2)/(Q3). Since `v_0(g) = 1 > 0 = n_1`, this is case (Q3).
* (Q3), `g ↦ (0 1) · g · C_1((0 1) · g)`, gives a matrix with `v_0 = 0 < 1`, and `∑ v_i` stays
  the same.

So during a pass Q1 → Q2 → Q3, neither `v_k` nor `∑_i v_i` has to strictly increase.  In fact
`∑_i v_i` is never changed by (Q3) (`rvSum_swap_mul_GLOr`).

# An example where a (Q3) step followed by a (Q2) step keeps `∑_i v_i`

`loop_example`: for `g = [[ϖ, ϖ], [1, 0]]`, the loop (Q3) then (Q2) ends at `[[0, 1], [ϖ, 0]]`
(up to the sign of a row), with the same `∑_i v_i`; only `j_0` increases.  So the measure that
increases along every loop is `(∑_i v_i, j_k)` lexicographically, not `∑_i v_i` alone.
-/

open Matrix Polynomial

noncomputable section

namespace GLrBuilding



variable {F : Type*} [Field F]

/-- `ϖ^n` as an element of `K = F((1/t))`. -/
abbrev unifPow (F : Type*) [Field F] (n : ℤ) : Kt F := (((unifUnit (F := F)) ^ n : (Kt F)ˣ) : Kt F)

/-- The matrix `[[ϖ, ϖ²], [1, 0]] ∈ GL_2(K)`. -/
def q3Example : GL (Fin 2) (Kt F) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![unifPow F 1, unifPow F 2; unifPow F 0, 0]
    (by
      simp only [Matrix.det_fin_two_of, mul_zero, zero_sub, neg_ne_zero]
      exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))

lemma q3Example_coe : ((q3Example (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) =
    !![unifPow F 1, unifPow F 2; unifPow F 0, 0] := rfl

lemma rowVal_q3Example :
    rowVal ((q3Example (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 0 = 1 := by
  apply le_antisymm
  · refine (rowVal_le_vInf _ 0 0).trans_eq ?_
    rw [q3Example_coe]; exact vInf_zpow_unifUnit 1
  · refine Finset.le_inf fun j _ => ?_
    rw [q3Example_coe]
    fin_cases j
    · exact (vInf_zpow_unifUnit (F := F) 1).ge
    · exact le_trans (by decide) (vInf_zpow_unifUnit (F := F) 2).ge

lemma rv_q3Example : rv (q3Example (F := F)) 0 = 1 := by
  have := coe_rv (q3Example (F := F)) 0
  rw [rowVal_q3Example] at this; exact_mod_cast this

lemma pivotCol_q3Example :
    pivotCol ((q3Example (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 0 = 0 := by
  apply le_antisymm _ (Fin.zero_le _)
  apply Finset.min'_le
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, rowVal_q3Example]
  rw [q3Example_coe]; exact vInf_zpow_unifUnit 1

lemma isMonoRow_q3Example :
    IsMonoRow ((q3Example (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 1 0 0 := by
  intro j; rw [q3Example_coe]; fin_cases j <;> simp

/-- **Step (Q3) can lower `v_k`.**  For `g = [[ϖ, ϖ²], [1, 0]]` and `k = 0`:
* `I_1(g)` holds;
* row `l = 1` is `ϖ^{n_1} e_{j_0(g)}` with `n_1 = 0 < v_0(g)`, so the step goes to case (Q3);
* for `g' = (0 1) · g · C_1((0 1) · g)`, `v_0(g') < v_0(g)` and `∑ v_i(g') = ∑ v_i(g)`. -/
theorem q3_lowers_rowVal_example :
    RedInv 1 (q3Example (F := F)) ∧
    IsMonoRow ((q3Example (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 1 0
      (pivotCol ((q3Example (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 0) ∧
    0 < rv (q3Example (F := F)) 0 ∧
    ∃ κ ∈ iwahoriR F 2,
      rv (permGL 2 (Kt F) (Equiv.swap 0 1) * (q3Example (F := F)) * GLOr F 2 κ) 0 <
        rv (q3Example (F := F)) 0 ∧
      rvSum (permGL 2 (Kt F) (Equiv.swap 0 1) * (q3Example (F := F)) * GLOr F 2 κ) =
        rvSum (q3Example (F := F)) := by
  have hmono : IsMonoRow ((q3Example (F := F) : GL (Fin 2) (Kt F)) :
      Matrix (Fin 2) (Fin 2) (Kt F)) 1 0
      (pivotCol ((q3Example (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 0) := by
    rw [pivotCol_q3Example]; exact isMonoRow_q3Example
  have hlt : (0 : ℤ) < rv (q3Example (F := F)) 0 := by rw [rv_q3Example]; norm_num
  refine ⟨⟨fun _ => 0, fun _ => 0, fun i hi => ?_, fun i i' hi hii' => ?_⟩, hmono, hlt, ?_⟩
  · have : i = 1 := by fin_cases i <;> simp_all
    subst this; exact isMonoRow_q3Example
  · exfalso
    have := i'.isLt
    have : (i : ℕ) < i' := hii'
    omega
  · obtain ⟨κ, hκ, -, -, -, hsum, -, hdec⟩ := q3_step q3Example 0 1 0 hmono hlt
    exact ⟨κ, hκ, hdec, hsum⟩

/-- **(Q3) never changes `∑_i v_i`**, whatever the clearing matrix `κ ∈ GL_r(O)` is: for every `g`,
`∑_i v_i((k l) · g · κ) = ∑_i v_i(g)`.  So for a matrix `g` at stage (Q1) that goes
(Q1) → (Q2) → (Q3) and becomes `g''` at stage (Q3), `∑_i v_i(g) < ∑_i v_i(g'')` is impossible.
(`q3_lowers_rowVal_example` shows that such a `g` exists.) -/
theorem rvSum_swap_mul_GLOr {r : ℕ} (g : GL (Fin r) (Kt F)) (k l : Fin r)
    (κ : GL (Fin r) (PowerSeries F)) :
    rvSum (permGL r (Kt F) (Equiv.swap k l) * g * GLOr F r κ) = rvSum g := by
  have h := rowValSum_eq_rvSum (permGL r (Kt F) (Equiv.swap k l) * g * GLOr F r κ)
  have h2 : rowValSum (((permGL r (Kt F) (Equiv.swap k l) * g * GLOr F r κ : GL (Fin r) (Kt F))) :
      Matrix (Fin r) (Fin r) (Kt F)) = rowValSum (g : Matrix (Fin r) (Fin r) (Kt F)) := by
    simp only [rowValSum, rowVal_mul_GLOr]
    exact rowValSum_permGL_mul _ _
  rw [h2, rowValSum_eq_rvSum, WithTop.coe_inj] at h
  exact h.symm

lemma unifPow_mul_unifPow (a b : ℤ) : unifPow F a * unifPow F b = unifPow F (a + b) := by
  simp [unifPow, _root_.zpow_add]

lemma polyEmb_X_mul_unifPow_one : polyEmb F X * unifPow F 1 = 1 := by
  have h : polyEmb F X = unifPow F (-1) := by
    have := polyEmb_C_mul_X_pow (F := F) 1 1
    simp only [map_one, one_mul, pow_one] at this
    rw [this, unifPow, Units.val_zpow_eq_zpow_val]
    change _ = unif F ^ (-1 : ℤ)
    rw [unif_zpow]; simp
  rw [h, unifPow_mul_unifPow]; simp [unifPow]

/-- `[[ϖ, ϖ], [1, 0]]`. -/
def loopStart : GL (Fin 2) (Kt F) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![unifPow F 1, unifPow F 1; unifPow F 0, 0]
    (by
      simp only [Matrix.det_fin_two_of, mul_zero, zero_sub, neg_ne_zero]
      exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))

/-- `[[0, 1], [ϖ, 0]]`. -/
def loopEnd : GL (Fin 2) (Kt F) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, unifPow F 0; unifPow F 1, 0]
    (by
      simp only [Matrix.det_fin_two_of, zero_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))

/-- `[[t, -1], [1, 0]] ∈ GL_2(F[t])`: the transposition `(0 1)` followed by `R_{01}`. -/
def loopGamma : GL (Fin 2) F[X] :=
  Matrix.GeneralLinearGroup.mk'' !![X, -1; 1, 0] (by simp [Matrix.det_fin_two_of])

/-- `[[1, -1], [0, 1]] ∈ I`: the clearing matrix `C_1`. -/
def loopKappa : GL (Fin 2) (PowerSeries F) :=
  Matrix.GeneralLinearGroup.mk'' !![1, -1; 0, 1] (by simp [Matrix.det_fin_two_of])

lemma loopKappa_mem : loopKappa (F := F) ∈ iwahoriR F 2 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [loopKappa, Matrix.GeneralLinearGroup.map]

lemma loopEnd_eq : loopEnd (F := F) = GLAr F 2 loopGamma * loopStart * GLOr F 2 loopKappa := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hX : polyEmb F X * (unifUnit (F := F) : Kt F) = 1 := by
    simpa using polyEmb_X_mul_unifPow_one (F := F)
  fin_cases i <;> fin_cases j <;>
    simp [loopEnd, loopStart, loopGamma, loopKappa, GLAr, GLOr, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.GeneralLinearGroup.map, hX]

lemma loopStart_coe : ((loopStart (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) =
    !![unifPow F 1, unifPow F 1; unifPow F 0, 0] := rfl

lemma loopEnd_coe : ((loopEnd (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) =
    !![0, unifPow F 0; unifPow F 1, 0] := rfl

lemma rowVal_loopStart :
    rowVal ((loopStart (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 0 = 1 := by
  apply le_antisymm
  · refine (rowVal_le_vInf _ 0 0).trans_eq ?_
    rw [loopStart_coe]; exact vInf_zpow_unifUnit 1
  · refine Finset.le_inf fun j _ => ?_
    rw [loopStart_coe]
    fin_cases j
    · exact (vInf_zpow_unifUnit (F := F) 1).ge
    · exact (vInf_zpow_unifUnit (F := F) 1).ge

lemma pivotCol_loopStart :
    pivotCol ((loopStart (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 0 = 0 := by
  apply le_antisymm _ (Fin.zero_le _)
  apply Finset.min'_le
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, rowVal_loopStart]
  rw [loopStart_coe]; exact vInf_zpow_unifUnit 1

lemma isMonoRow_loopStart_one :
    IsMonoRow ((loopStart (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 1 0 0 := by
  intro j; rw [loopStart_coe]; fin_cases j <;> simp

lemma isMonoRow_loopEnd_zero :
    IsMonoRow ((loopEnd (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 0 0 1 := by
  intro j; rw [loopEnd_coe]; fin_cases j <;> simp

lemma isMonoRow_loopEnd_one :
    IsMonoRow ((loopEnd (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 1 1 0 := by
  intro j; rw [loopEnd_coe]; fin_cases j <;> simp

/-- **A full loop (Q3) then (Q2) can keep `∑ v_i` fixed.**  For `g = [[ϖ, ϖ], [1, 0]]` and `k = 0`:
* `I_1(g)` holds, row `l = 1` is `ϖ^0 e_{j_0(g)}` and `n_1 = 0 < 1 = v_0(g)`, so (Q1) → (Q2) → (Q3);
* (Q3) gives `g'' = (0 1) · g · κ = [[1, -1], [ϖ, 0]]` with `κ = C_1((0 1) · g) = [[1, -1], [0, 1]] ∈ I`;
* back at (Q1), row `1` of `g''` is `ϖ e_0` and `v_0(g'') = 0 ≤ 1`, so (Q2) applies `R_{01}`
  (row `0` minus `t` times row `1`), giving `[[0, -1], [ϖ, 0]]`; we also flip the sign of row `0`,
  which changes no `v_i`;
* the result `[[0, 1], [ϖ, 0]] = γ g κ` (with `γ = [[t, -1], [1, 0]]`) has the same `∑ v_i = 1`
  as `g`, while `j_0` moved from `0` to `1`. -/
theorem loop_example :
    RedInv 1 (loopStart (F := F)) ∧
    IsMonoRow ((loopStart (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 1 0
      (pivotCol ((loopStart (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 0) ∧
    0 < rv (loopStart (F := F)) 0 ∧
    loopEnd (F := F) = GLAr F 2 loopGamma * loopStart * GLOr F 2 loopKappa ∧
    loopKappa (F := F) ∈ iwahoriR F 2 ∧
    rvSum (loopEnd (F := F)) = rvSum (loopStart (F := F)) ∧
    pivotCol ((loopStart (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 0 <
      pivotCol ((loopEnd (F := F) : GL (Fin 2) (Kt F)) : Matrix (Fin 2) (Fin 2) (Kt F)) 0 := by
  have hrv0 : rv (loopStart (F := F)) 0 = 1 := by
    have := coe_rv (loopStart (F := F)) 0
    rw [rowVal_loopStart] at this; exact_mod_cast this
  refine ⟨⟨fun _ => 0, fun _ => 0, fun i hi => ?_, fun i i' hi hii' => ?_⟩,
    by rw [pivotCol_loopStart]; exact isMonoRow_loopStart_one, by rw [hrv0]; norm_num,
    loopEnd_eq, loopKappa_mem, ?_, ?_⟩
  · have : i = 1 := by fin_cases i <;> simp_all
    subst this; exact isMonoRow_loopStart_one
  · exfalso
    have := i'.isLt
    have : (i : ℕ) < i' := hii'
    omega
  · simp only [rvSum, Fin.sum_univ_two, hrv0, rv_of_isMonoRow isMonoRow_loopStart_one,
      rv_of_isMonoRow isMonoRow_loopEnd_zero, rv_of_isMonoRow isMonoRow_loopEnd_one]
    norm_num
  · rw [pivotCol_loopStart, isMonoRow_loopEnd_zero.pivotCol]; decide

end GLrBuilding
