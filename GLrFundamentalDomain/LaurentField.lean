module

public import Mathlib

/-!
# The local field `K = F((1/t))` and its valuation

We model the local field `K = F((1/t))` as the field of Laurent series `LaurentSeries F`
in the uniformizer `ϖ = 1/t` (called `unif F` below).  Its valuation ring
`O = F[[1/t]]` is the image of `PowerSeries F`, and the polynomial ring `F[t]` sits inside
`K` via `t ↦ ϖ⁻¹`.  The valuation `v_∞ : K → ℤ ∪ {⊤}` is the order of a Laurent series.

Everything here works over an arbitrary field `F` (in particular for `F = 𝔽_q`).
-/

@[expose] public section

open HahnSeries Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

variable (F : Type*) [Field F]

/-- The local field `F((1/t))`, realised as Laurent series in the uniformizer `ϖ = 1/t`. -/
abbrev Kt := LaurentSeries F

/-- The uniformizer `ϖ = 1/t` of `F((1/t))`. -/
def unif : Kt F := single 1 1

/-- The embedding `F[t] → F((1/t))`, sending `t ↦ ϖ⁻¹`. -/
def polyEmb : Polynomial F →+* Kt F := Polynomial.eval₂RingHom HahnSeries.C (unif F)⁻¹

/-- The valuation ring `O = F[[1/t]]` inside `F((1/t))`. -/
def intRing : Subring (Kt F) := (HahnSeries.ofPowerSeries ℤ F).range

/-- The valuation `v_∞` on `F((1/t))` (with `v_∞(ϖ) = 1`, `v_∞(t) = -1`, `v_∞(0) = ⊤`). -/
def vInf (x : Kt F) : WithTop ℤ := x.orderTop

lemma unif_ne_zero : unif F ≠ 0 := by simp [unif]

lemma unif_zpow (n : ℤ) : unif F ^ n = single n 1 := by
  rw [unif]; exact (RatFunc.single_zpow n).symm

/-! ### Basic properties of `v_∞` -/

lemma vInf_mul (x y : Kt F) : vInf F (x * y) = vInf F x + vInf F y := orderTop_mul x y

lemma vInf_eq_top_iff (x : Kt F) : vInf F x = ⊤ ↔ x = 0 := orderTop_eq_top

lemma vInf_unif : vInf F (unif F) = 1 := orderTop_single one_ne_zero

/-- Elements of `O = F[[1/t]]` have nonnegative valuation. -/
lemma vInf_ofPowerSeries_nonneg (x : PowerSeries F) : 0 ≤ vInf F (ofPowerSeries ℤ F x) := by
  have key : ∀ i : ℤ, i < 0 → (ofPowerSeries ℤ F x).coeff i = 0 := by
    intro i hi
    rw [ofPowerSeries_apply]
    apply embDomain_notin_range
    rintro ⟨n, hn⟩
    simp at hn
    omega
  by_cases hx : ofPowerSeries ℤ F x = 0
  · simp [vInf, hx]
  rw [vInf, zero_le_orderTop_iff]
  by_contra h
  push_neg at h
  exact (coeff_order_eq_zero.not.mpr hx) (key _ h)

/-- Units of `O = F[[1/t]]` have valuation `0`. -/
lemma vInf_ofPowerSeries_unit (u : (PowerSeries F)ˣ) :
    vInf F (ofPowerSeries ℤ F (u : PowerSeries F)) = 0 := by
  have h1 := vInf_ofPowerSeries_nonneg F (u : PowerSeries F)
  have h2 := vInf_ofPowerSeries_nonneg F ((u⁻¹ : (PowerSeries F)ˣ) : PowerSeries F)
  have h : vInf F (ofPowerSeries ℤ F (u : PowerSeries F)) +
      vInf F (ofPowerSeries ℤ F ((u⁻¹ : (PowerSeries F)ˣ) : PowerSeries F)) = 0 := by
    rw [← vInf_mul, ← map_mul, Units.mul_inv, map_one, vInf, orderTop_one]
  generalize vInf F (ofPowerSeries ℤ F (u : PowerSeries F)) = a at h1 h
  generalize vInf F (ofPowerSeries ℤ F ((u⁻¹ : (PowerSeries F)ˣ) : PowerSeries F)) = b at h2 h
  induction a <;> induction b <;> simp_all
  norm_cast at *
  omega

/-- A unit of `O` has valuation `0` (stated for `IsUnit`). -/
lemma vInf_ofPowerSeries_isUnit {u : PowerSeries F} (hu : IsUnit u) :
    vInf F (ofPowerSeries ℤ F u) = 0 := by
  obtain ⟨u, rfl⟩ := hu
  exact vInf_ofPowerSeries_unit F u

/-- Units of `F[t]` (the nonzero constants) have valuation `0`. -/
lemma vInf_polyEmb_unit (u : (Polynomial F)ˣ) : vInf F (polyEmb F (u : Polynomial F)) = 0 := by
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.mp u.isUnit
  rw [← hru, polyEmb, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, HahnSeries.C_apply, vInf,
    orderTop_single hr.ne_zero]
  rfl

/-- `C a · tᵏ ∈ F[t]` is the Laurent series `a ϖ^{-k}`. -/
lemma polyEmb_C_mul_X_pow (a : F) (k : ℕ) :
    polyEmb F (C a * X ^ k) = single (-(k : ℤ)) a := by
  have hm : (unif F)⁻¹ = single (-1 : ℤ) (1 : F) := by
    rw [unif, RatFunc.single_zpow (-1), _root_.zpow_neg_one]
  simp only [polyEmb, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow, hm, HahnSeries.single_pow, HahnSeries.C_apply, single_mul_single]
  simp

/-- `F[t] ⊆ K` has nonpositive valuation: `v_∞(p) ≤ 0` for every polynomial `p`
(here `v_∞(0) = ⊤`, so we need `p ≠ 0`). -/
lemma vInf_polyEmb_nonpos (p : F[X]) (hp : p ≠ 0) : vInf F (polyEmb F p) ≤ 0 := by
  have hsum : polyEmb F p = ∑ k ∈ Finset.range (p.natDegree + 1),
      single (-(k : ℤ)) (p.coeff k) := by
    conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => polyEmb_C_mul_X_pow _ _ _
  have hc : (polyEmb F p).coeff (-(p.natDegree : ℤ)) ≠ 0 := by
    rw [hsum, HahnSeries.coeff_sum, Finset.sum_eq_single p.natDegree]
    · simpa using hp
    · intro k _ hk
      rw [coeff_single, if_neg (by omega)]
    · intro h; simp at h
  refine le_trans (HahnSeries.orderTop_le_of_coeff_ne_zero hc) ?_
  exact_mod_cast (by omega : -(p.natDegree : ℤ) ≤ 0)

/-! ### Elements of `O` and of `ϖ O` -/

/-- An element of `K` of nonnegative valuation lies in `O = F[[1/t]]`. -/
lemma exists_powerSeries_of_nonneg (x : Kt F) (hx : 0 ≤ vInf F x) :
    ∃ p : PowerSeries F, ofPowerSeries ℤ F p = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  have hord : (0 : ℤ) ≤ x.order := by
    have : vInf F x = (x.order : WithTop ℤ) := by
      rw [vInf, HahnSeries.order_eq_orderTop_of_ne_zero h0]
    rw [this] at hx; exact_mod_cast hx
  refine ⟨PowerSeries.X ^ x.order.toNat * x.powerSeriesPart, ?_⟩
  exact LaurentSeries.X_order_mul_powerSeriesPart (Int.toNat_of_nonneg hord)

/-- An element of `K` of valuation `≥ 1` lies in `ϖ O`. -/
lemma exists_powerSeries_of_one_le (x : Kt F) (hx : 1 ≤ vInf F x) :
    ∃ p : PowerSeries F, ofPowerSeries ℤ F (PowerSeries.X * p) = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  have hord : (1 : ℤ) ≤ x.order := by
    have : vInf F x = (x.order : WithTop ℤ) := by
      rw [vInf, HahnSeries.order_eq_orderTop_of_ne_zero h0]
    rw [this] at hx; exact_mod_cast hx
  refine ⟨PowerSeries.X ^ (x.order.toNat - 1) * x.powerSeriesPart, ?_⟩
  have hn : x.order.toNat = (x.order.toNat - 1) + 1 := by omega
  rw [← mul_assoc, ← pow_succ']
  rw [← hn]
  exact LaurentSeries.X_order_mul_powerSeriesPart (Int.toNat_of_nonneg (by omega))

/-- `v_∞(x / y) = v_∞(x) - v_∞(y)` in the form `v_∞(x / y) + v_∞(y) = v_∞(x)`, `y ≠ 0`. -/
lemma vInf_div_add (x y : Kt F) (hy : y ≠ 0) : vInf F (x / y) + vInf F y = vInf F x := by
  rw [← vInf_mul, div_mul_cancel₀ x hy]

variable {F} in
/-- If `v_∞(y) ≤ v_∞(x)` and `y ≠ 0` then `-x/y ∈ O`. -/
lemma vInf_neg_div_nonneg (x y : Kt F) (hy : y ≠ 0) (h : vInf F y ≤ vInf F x) :
    0 ≤ vInf F (-(x / y)) := by
  have h' := vInf_div_add F x y hy
  have hneg : vInf F (-(x / y)) = vInf F (x / y) := orderTop_neg
  rw [hneg]
  have hne : vInf F y ≠ ⊤ := by rwa [Ne, vInf_eq_top_iff]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hn] at h' h
  generalize vInf F (x / y) = z at h' ⊢
  rw [← h'] at h
  induction z with
  | top => exact le_top
  | coe z =>
    norm_cast at h ⊢
    omega

variable {F} in
/-- If `v_∞(y) < v_∞(x)` then `-x/y ∈ ϖ O`. -/
lemma vInf_neg_div_one_le (x y : Kt F) (h : vInf F y < vInf F x) :
    1 ≤ vInf F (-(x / y)) := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [(vInf_eq_top_iff F 0).mpr rfl] at h
    exact not_top_lt h
  have h' := vInf_div_add F x y hy
  have hneg : vInf F (-(x / y)) = vInf F (x / y) := orderTop_neg
  rw [hneg]
  have hne : vInf F y ≠ ⊤ := by rwa [Ne, vInf_eq_top_iff]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hn] at h' h
  generalize vInf F (x / y) = z at h' ⊢
  rw [← h'] at h
  induction z with
  | top => exact le_top
  | coe z =>
    norm_cast at h ⊢
    omega

end GLrBuilding

end

end
