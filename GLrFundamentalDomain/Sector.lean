import GLrFundamentalDomain.PointedChambers

/-!
# The standard sector and the key lemmas

* `SectorIdx r` : vectors `n = (n₁, …, n_r) ∈ ℕ^r` with `n₁ ≥ n₂ ≥ ⋯ ≥ n_r` and some
  (equivalently the last) entry `0`.
* `stdVertex n = [diag(t^{n₁}, …, t^{n_r}) O^r]`; the standard sector `stdSector` is the set of
  these vertices, a sector (Weyl chamber) of the standard apartment based at `[O^r]`.
* `InSector σ` : all vertices of the simplex `σ` lie in the sector, i.e. `σ` is a simplex
  of the sector (viewed as a subcomplex of the building).  `PChamber.InSector c` : all vertices
  of the pointed chamber `c` (`PChamber.toFinset`, defined through `pchamberEquiv`) lie in the
  sector.
* `apartmentPC d w` : the pointed chamber `[diag(ϖ^{d}) · w]` of the standard apartment.

Key lemmas (inputs of the fundamental domain theorems in `FundamentalDomain.lean`):
* `exists_apartment_reduction` (in `ApartmentReduction.lean`) : every pointed chamber is
  `GL_r(F[t])`-equivalent to a pointed chamber of the standard apartment (the reduction by
  `GL_r(F[t])` on the left and the Iwahori subgroup on the right, Böckle's method);
* `apartment_to_sector` (in `SectorProofs.lean`) : every pointed chamber of the standard apartment is moved into the
  standard sector by a permutation matrix (an element of `GL_r(F) ⊆ GL_r(F[t])`);
* `stdVertex_orbit_unique` (in `SectorProofs.lean`) : distinct vertices of the sector are not `GL_r(F[t])`-equivalent.
-/

open Matrix Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

open Classical

variable {F : Type*} [Field F] {r : ℕ}

variable (r) in
/-- Index set of the vertices of the standard sector: `n ∈ ℕ^r` with
`n₁ ≥ n₂ ≥ ⋯ ≥ n_r` and some entry equal to `0` (so `n_r = 0`). -/
def SectorIdx := {n : Fin r → ℕ // Antitone n ∧ ∃ i, n i = 0}

variable (F) in
/-- The vertex `[diag(t^{n₁}, …, t^{n_r}) O^r]` of the standard sector. -/
def stdVertex (n : SectorIdx r) : Vertex F r :=
  (diagPow (F := F) fun j => -(n.1 j : ℤ)) • stdVertex₀ F r

variable (F r) in
/-- The standard sector: the vertices `[diag(t^{n₁}, …, t^{n_r}) O^r]`,
`n₁ ≥ ⋯ ≥ n_r = 0`. -/
def stdSector : Set (Vertex F r) := Set.range (stdVertex F)

/-- A simplex lies in the standard sector if all of its vertices do. -/
def InSector (σ : Finset (Vertex F r)) : Prop := ∀ v ∈ σ, v ∈ stdSector F r

/-- A pointed chamber lies in the standard sector if all of its vertices do. -/
def PChamber.InSector [NeZero r] (c : PChamber F r) : Prop := GLrBuilding.InSector c.toFinset

/-- The pointed chamber `[diag(ϖ^{d₁}, …, ϖ^{d_r}) · w]` of the standard apartment, for
`d ∈ ℤ^r` and a permutation matrix `w`. -/
def apartmentPC (d : Fin r → ℤ) (w : Equiv.Perm (Fin r)) : PChamber F r :=
  QuotientGroup.mk (diagPow d * permGL r (Kt F) w)

end GLrBuilding
