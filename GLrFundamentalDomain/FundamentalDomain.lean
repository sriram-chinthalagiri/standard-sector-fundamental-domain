import GLrFundamentalDomain.SectorProofs

/-!
# The standard sector is a fundamental domain for `GL_r(F[t])`

Let `K = F((1/t))`, `O = F[[1/t]]`, `A = F[t]` and `r ≥ 2`.  The group `GL_r(A)` acts on the
Bruhat–Tits building of `GL_r(K)` through `GLAr F r`.  The standard sector is the set of vertices
`[diag(t^{n₁}, …, t^{n_r}) O^r]`, `n₁ ≥ ⋯ ≥ n_r = 0`, together with the simplices all of whose
vertices are among them.

Main statements:
* `vertex_fundamental_domain` : every vertex is `GL_r(A)`-equivalent to exactly one vertex of
  the sector;
* `simplex_fundamental_domain` : every simplex is `GL_r(A)`-equivalent to exactly one simplex
  of the sector;
* `pchamber_fundamental_domain` : every pointed chamber is `GL_r(A)`-equivalent to exactly one
  pointed chamber of the sector;
* `standard_sector_fundamental_domain` : the sector is a subcomplex, and the conjunction of the
  above.

The proofs here only combine the key lemmas of `Sector.lean` with the description of pointed
chambers in `PointedChambers.lean`.

## Attribution

The method of proof is due to Gebhard Böckle (University of Heidelberg), and is carried out for
the Bruhat–Tits building of `GL_r` in the PhD thesis of Sriram Chinthalagiri Venkata.
-/

open Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

open Classical

variable {F : Type*} [Field F] {r : ℕ}

/-- Every pointed chamber can be moved into the standard sector by `GL_r(F[t])`. -/
theorem pchamber_exists_sector [NeZero r] (c : PChamber F r) :
    ∃ γ : GL (Fin r) F[X], (GLAr F r γ • c).InSector := by
  obtain ⟨γ, d, w, h⟩ := exists_apartment_reduction c
  obtain ⟨δ, hδ⟩ := apartment_to_sector (F := F) d w
  refine ⟨δ * γ, ?_⟩
  rw [map_mul, mul_smul, h]
  exact hδ

/-- If two elements of `GL_r(F[t])` both move a vertex `v` into the sector, they move it to
the same vertex. -/
lemma smul_eq_of_mem_stdSector (v : Vertex F r) (γ δ : GL (Fin r) F[X])
    (hγ : GLAr F r γ • v ∈ stdSector F r) (hδ : GLAr F r δ • v ∈ stdSector F r) :
    GLAr F r γ • v = GLAr F r δ • v := by
  obtain ⟨m, hm⟩ := hγ
  obtain ⟨n, hn⟩ := hδ
  have : n = m := stdVertex_orbit_unique (γ * δ⁻¹) n m (by
    rw [hn, hm, map_mul, mul_smul, ← mul_smul (GLAr F r δ⁻¹), ← map_mul, inv_mul_cancel,
      map_one, one_smul])
  rw [← hm, ← hn, this]

/-- Every vertex of the building is `GL_r(F[t])`-equivalent to exactly one vertex
`[diag(t^{n₁}, …, t^{n_r}) O^r]` (`n₁ ≥ ⋯ ≥ n_r = 0`) of the standard sector. -/
theorem vertex_fundamental_domain [NeZero r] (v : Vertex F r) :
    ∃! n : SectorIdx r, ∃ γ : GL (Fin r) F[X], GLAr F r γ • v = stdVertex F n := by
  have hex : ∃ n : SectorIdx r, ∃ γ : GL (Fin r) F[X], GLAr F r γ • v = stdVertex F n := by
    obtain ⟨g, rfl⟩ := exists_smul_stdVertex₀ F r v
    obtain ⟨γ, hγ⟩ := pchamber_exists_sector (QuotientGroup.mk g : PChamber F r)
    obtain ⟨n, hn⟩ := hγ _ (PChamber.basePoint_mem _)
    rw [PChamber.basePoint_smul, PChamber.basePoint_mk] at hn
    exact ⟨n, γ, hn.symm⟩
  obtain ⟨n, γ, hγ⟩ := hex
  refine ⟨n, ⟨γ, hγ⟩, fun m ⟨δ, hδ⟩ => stdVertex_orbit_unique (γ * δ⁻¹) m n ?_⟩
  rw [← hδ, map_mul, mul_smul, ← mul_smul (GLAr F r δ⁻¹), ← map_mul, inv_mul_cancel,
    map_one, one_smul, hγ]

/-- Every pointed chamber is `GL_r(F[t])`-equivalent to exactly one pointed chamber of the
standard sector. -/
theorem pchamber_fundamental_domain [NeZero r] (c : PChamber F r) :
    ∃! c' : PChamber F r, c'.InSector ∧ ∃ γ : GL (Fin r) F[X], GLAr F r γ • c = c' := by
  obtain ⟨γ, hγ⟩ := pchamber_exists_sector c
  refine ⟨GLAr F r γ • c, ⟨hγ, γ, rfl⟩, ?_⟩
  rintro c' ⟨hc', δ, rfl⟩
  refine PChamber.smul_eq_smul_of_forall _ _ c fun v hv => ?_
  have hmem : ∀ g : GL (Fin r) (Kt F), g • v ∈ (g • c).toFinset := fun g => by
    rw [PChamber.toFinset_smul]; exact Finset.mem_image_of_mem _ hv
  exact smul_eq_of_mem_stdSector _ δ γ (hc' _ (hmem _)) (hγ _ (hmem _))

/-- **Reduction of the simplex statement to the vertex and pointed-chamber statements.**
Assume that every simplex lies in a pointed chamber (`hsup`), that the vertex statement holds
(`hvert`, i.e. `vertex_fundamental_domain`) and that the pointed-chamber statement holds
(`hpc`, i.e. `pchamber_fundamental_domain`).  Then every simplex is `GL_r(F[t])`-equivalent to
exactly one simplex of the standard sector.

Existence: put `σ` in a pointed chamber `c` and move `c` into the sector; `σ` moves along with
it.  Uniqueness: if `σ` is moved to two different sector simplices `γ σ ≠ δ σ`, some vertex
`x ∈ σ` has `γ x ≠ δ x`, two distinct but equivalent sector vertices, contradicting `hvert`. -/
theorem simplex_fundamental_domain_of_vertex_pchamber [NeZero r]
    (hsup : ∀ σ : Finset (Vertex F r), IsSimplex σ → ∃ c : PChamber F r, σ ⊆ c.toFinset)
    (hvert : ∀ v : Vertex F r,
      ∃! n : SectorIdx r, ∃ γ : GL (Fin r) F[X], GLAr F r γ • v = stdVertex F n)
    (hpc : ∀ c : PChamber F r,
      ∃! c' : PChamber F r, c'.InSector ∧ ∃ γ : GL (Fin r) F[X], GLAr F r γ • c = c')
    (σ : Finset (Vertex F r)) (hσ : IsSimplex σ) :
    ∃! τ : Finset (Vertex F r), IsSimplex τ ∧ InSector τ ∧
      ∃ γ : GL (Fin r) F[X], smulSet (GLAr F r γ) σ = τ := by
  -- Existence: a pointed chamber `c ⊇ σ`, moved into the sector by `γ`.
  obtain ⟨c, hc⟩ := hsup σ hσ
  obtain ⟨c₀, ⟨hc₀, γ, hγ⟩, -⟩ := hpc c
  have hin : InSector (smulSet (GLAr F r γ) σ) := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    refine hc₀ _ ?_
    rw [← hγ, PChamber.toFinset_smul]
    exact Finset.mem_image_of_mem _ (hc hu)
  refine ⟨smulSet (GLAr F r γ) σ, ⟨hσ.smul _, hin, γ, rfl⟩, ?_⟩
  -- Uniqueness: otherwise some vertex has two distinct equivalent images in the sector.
  rintro τ ⟨-, hτ, δ, rfl⟩
  by_contra hne
  obtain ⟨x, hx, hxne⟩ : ∃ x ∈ σ, GLAr F r δ • x ≠ GLAr F r γ • x := by
    by_contra h
    push_neg at h
    exact hne (Finset.image_congr h)
  obtain ⟨m, hm⟩ := hτ _ (Finset.mem_image_of_mem _ hx)
  obtain ⟨n, hn⟩ := hin _ (Finset.mem_image_of_mem _ hx)
  have hmn : m = n := (hvert x).unique ⟨δ, hm.symm⟩ ⟨γ, hn.symm⟩
  exact hxne (by rw [← hm, ← hn, hmn])

/-- Every simplex of the building is `GL_r(F[t])`-equivalent to exactly one simplex of the
standard sector.  Deduced from `vertex_fundamental_domain` and `pchamber_fundamental_domain`
(together with `exists_pchamber_superset`) via
`simplex_fundamental_domain_of_vertex_pchamber`. -/
theorem simplex_fundamental_domain [NeZero r] (σ : Finset (Vertex F r)) (hσ : IsSimplex σ) :
    ∃! τ : Finset (Vertex F r), IsSimplex τ ∧ InSector τ ∧
      ∃ γ : GL (Fin r) F[X], smulSet (GLAr F r γ) σ = τ :=
  simplex_fundamental_domain_of_vertex_pchamber (fun _ h => exists_pchamber_superset h)
    vertex_fundamental_domain pchamber_fundamental_domain σ hσ

/-- **The standard sector is a fundamental domain** for the action of `GL_r(F[t])` on the
Bruhat–Tits building of `GL_r(F((1/t)))`, `r ≥ 2`:
1. the simplices of the sector form a subcomplex (faces of sector simplices are sector
   simplices);
2. every vertex is equivalent to exactly one vertex of the sector;
3. every simplex is equivalent to exactly one simplex of the sector;
4. every pointed chamber is equivalent to exactly one pointed chamber of the sector.

(The hypothesis `2 ≤ r` is the one from the statement; the proof only uses `r ≥ 1`.) -/
theorem standard_sector_fundamental_domain (hr : 2 ≤ r) :
    haveI : NeZero r := ⟨by omega⟩
    (∀ σ τ : Finset (Vertex F r), IsSimplex σ → InSector σ → τ ⊆ σ → τ.Nonempty →
      IsSimplex τ ∧ InSector τ) ∧
    (∀ v : Vertex F r, ∃! n : SectorIdx r, ∃ γ : GL (Fin r) F[X], GLAr F r γ • v = stdVertex F n) ∧
    (∀ σ : Finset (Vertex F r), IsSimplex σ → ∃! τ : Finset (Vertex F r),
      IsSimplex τ ∧ InSector τ ∧ ∃ γ : GL (Fin r) F[X], smulSet (GLAr F r γ) σ = τ) ∧
    (∀ c : PChamber F r, ∃! c' : PChamber F r,
      c'.InSector ∧ ∃ γ : GL (Fin r) F[X], GLAr F r γ • c = c') := by
  haveI : NeZero r := ⟨by omega⟩
  exact ⟨fun σ τ hσ hσs hτσ hτ => ⟨hσ.mono hτσ hτ, fun v hv => hσs v (hτσ hv)⟩,
    vertex_fundamental_domain, simplex_fundamental_domain, pchamber_fundamental_domain⟩

end GLrBuilding
