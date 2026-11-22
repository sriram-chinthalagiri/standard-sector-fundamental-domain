import GLrFundamentalDomain.Lattice

/-!
# Vertices and pointed chambers as cosets of `GL_r(K)`

* `stdLattice F r` : the standard lattice `O^r`, and `stdVertex₀ = [O^r]`.
* `vertexStabR F r` : `K^× · GL_r(O)`, the stabilizer of `[O^r]`
  (`vertexStabR_eq_stabilizer`, proved in `PointedChambers.lean`).
* `iwahoriR F r` : the Iwahori subgroup of `GL_r(O)`, matrices that are upper triangular
  modulo `ϖ`; `chamberStab F r = K^× · I`.
* `PChamber F r = GL_r(K) / (K^× · I)` : pointed chambers.  The identification with pairs
  `(C, v)` of a chamber and a vertex, and hence the vertices, underlying chamber and base point
  of a coset, are given by the equivariant bijection `pchamberEquiv` (`Chambers.lean`); see
  `PointedChambers.lean`.  The class of `g` is the chamber with vertices `[g · stdChain i]`,
  pointed at `[g O^r]`.
-/

open Matrix

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

open Classical

variable (F : Type*) [Field F] (r : ℕ)

/-! ### Embeddings of `GL_r(O)` and `GL_r(F[t])` into `GL_r(K)` -/

/-- `GL_r(O) → GL_r(K)`. -/
def GLOr : GL (Fin r) (PowerSeries F) →* GL (Fin r) (Kt F) :=
  Matrix.GeneralLinearGroup.map (HahnSeries.ofPowerSeries ℤ F)

/-- `GL_r(F[t]) → GL_r(K)`. -/
def GLAr : GL (Fin r) (Polynomial F) →* GL (Fin r) (Kt F) :=
  Matrix.GeneralLinearGroup.map (polyEmb F)

/-! ### Diagonal and permutation matrices -/

variable {F r} in
/-- The diagonal matrix `diag(ϖ^{d₁}, …, ϖ^{d_r}) ∈ GL_r(K)` for `d ∈ ℤ^r`.
Note `t = ϖ⁻¹`, so `diagPow (-n) = diag(t^{n₁}, …, t^{n_r})`. -/
def diagPow (d : Fin r → ℤ) : GL (Fin r) (Kt F) :=
  Units.map (Matrix.diagonalRingHom (Fin r) (Kt F)).toMonoidHom
    (MulEquiv.piUnits.symm fun j => unifUnit ^ d j)

/-- The permutation matrix of `w ∈ S_r`, in `GL_r(R)`. -/
def permGL (R : Type*) [CommRing R] (w : Equiv.Perm (Fin r)) : GL (Fin r) R :=
  Matrix.GeneralLinearGroup.mk'' (w.permMatrix R) (by
    rw [Matrix.det_permutation]
    exact ((Equiv.Perm.sign w).map (Int.castRingHom R).toMonoidHom).isUnit)

/-! ### The standard lattice and the vertex stabilizer -/

/-- The standard lattice `O^r ⊆ K^r` as an `O`-submodule. -/
def stdCarrier : Submodule (intRing F) (Fin r → Kt F) where
  carrier := {x | ∀ i, x i ∈ intRing F}
  add_mem' hx hy i := (intRing F).add_mem (hx i) (hy i)
  zero_mem' _ := (intRing F).zero_mem
  smul_mem' c _ hx i := (intRing F).mul_mem c.2 (hx i)

lemma isLattice_stdCarrier : IsLattice F r (stdCarrier F r) := by
  have hsingle : ∀ i, (Pi.single i 1 : Fin r → Kt F) ∈ stdCarrier F r := by
    intro i j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have heq : stdCarrier F r =
      Submodule.span (intRing F) (Set.range fun i => (Pi.single i 1 : Fin r → Kt F)) := by
    apply le_antisymm
    · intro x hx
      have : x = ∑ i, (⟨x i, hx i⟩ : intRing F) • (Pi.single i 1 : Fin r → Kt F) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
      rw [this]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hsingle i
  refine ⟨⟨(Finset.univ.image fun i => (Pi.single i 1 : Fin r → Kt F)), ?_⟩, ?_⟩
  · rw [heq, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  · rw [eq_top_iff]
    intro x _
    have : x = ∑ i, x i • (Pi.single i 1 : Fin r → Kt F) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (hsingle i))

/-- The standard lattice `O^r`. -/
def stdLattice : Lattice F r := ⟨stdCarrier F r, isLattice_stdCarrier F r⟩

/-- The standard vertex `[O^r]`. -/
def stdVertex₀ : Vertex F r := (stdLattice F r).vtx

/-- `K^× · GL_r(O)`, the stabilizer of the standard vertex `[O^r]`
(see `vertexStabR_eq_stabilizer`). -/
def vertexStabR : Subgroup (GL (Fin r) (Kt F)) where
  carrier := {g | ∃ c : (Kt F)ˣ, ∃ k : GL (Fin r) (PowerSeries F),
    (g : Matrix (Fin r) (Fin r) (Kt F)) = (c : Kt F) • (GLOr F r k : Matrix (Fin r) (Fin r) (Kt F))}
  one_mem' := ⟨1, 1, by simp⟩
  mul_mem' := by
    rintro g h ⟨c, k, hg⟩ ⟨d, l, hh⟩
    refine ⟨c * d, k * l, ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_mul, hg, hh, map_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.val_mul]
  inv_mem' := by
    rintro g ⟨c, k, hg⟩
    refine ⟨c⁻¹, k⁻¹, ?_⟩
    rw [Matrix.coe_units_inv]
    apply Matrix.inv_eq_right_inv
    rw [hg, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.GeneralLinearGroup.coe_mul,
      ← map_mul, mul_inv_cancel, map_one, Units.mul_inv]
    simp

/-! ### The Iwahori subgroup and pointed chambers -/

/-- The upper triangular (Borel) subgroup of `GL_r(F)`. -/
def borelR : Subgroup (GL (Fin r) F) where
  carrier := {g | (g : Matrix (Fin r) (Fin r) F).BlockTriangular id}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' hg hh := Matrix.BlockTriangular.mul hg hh
  inv_mem' := by
    intro g hg
    have : Invertible (g : Matrix (Fin r) (Fin r) F) := Matrix.invertibleOfIsUnitDet _
      (Matrix.isUnits_det_units g)
    simp only [Set.mem_setOf_eq, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

/-- The Iwahori subgroup `I ⊆ GL_r(O)`: matrices whose reduction modulo `ϖ` is upper
triangular. -/
def iwahoriR : Subgroup (GL (Fin r) (PowerSeries F)) :=
  (borelR F r).comap (Matrix.GeneralLinearGroup.map (PowerSeries.constantCoeff (R := F)))

/-- `K^× · I`, the stabilizer of the standard pointed chamber. -/
def chamberStab : Subgroup (GL (Fin r) (Kt F)) where
  carrier := {g | ∃ c : (Kt F)ˣ, ∃ k ∈ iwahoriR F r,
    (g : Matrix (Fin r) (Fin r) (Kt F)) = (c : Kt F) • (GLOr F r k : Matrix (Fin r) (Fin r) (Kt F))}
  one_mem' := ⟨1, 1, (iwahoriR F r).one_mem, by simp⟩
  mul_mem' := by
    rintro g h ⟨c, k, hk, hg⟩ ⟨d, l, hl, hh⟩
    refine ⟨c * d, k * l, (iwahoriR F r).mul_mem hk hl, ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_mul, hg, hh, map_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.val_mul]
  inv_mem' := by
    rintro g ⟨c, k, hk, hg⟩
    refine ⟨c⁻¹, k⁻¹, (iwahoriR F r).inv_mem hk, ?_⟩
    rw [Matrix.coe_units_inv]
    apply Matrix.inv_eq_right_inv
    rw [hg, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.GeneralLinearGroup.coe_mul,
      ← map_mul, mul_inv_cancel, map_one, Units.mul_inv]
    simp

/-- Pointed chambers of the building, as the coset space `GL_r(K) / (K^× · I)`. -/
abbrev PChamber := GL (Fin r) (Kt F) ⧸ chamberStab F r

instance : MulAction (GL (Fin r) (Kt F)) (PChamber F r) :=
  MulAction.quotient (GL (Fin r) (Kt F)) (chamberStab F r)

end GLrBuilding
