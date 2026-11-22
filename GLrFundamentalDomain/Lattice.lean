import GLrFundamentalDomain.LaurentField

/-!
# The Bruhat–Tits building of `GL_r(F((1/t)))`: lattices, vertices and simplices

Let `K = F((1/t))` (`Kt F`), with valuation ring `O = F[[1/t]]` (`intRing F`)
and uniformizer `ϖ = 1/t` (`unif F`).  Fix `r : ℕ`.

* `Lattice F r` : an `O`-lattice in `K^r`, i.e. a finitely generated `O`-submodule of `K^r`
  that spans `K^r` over `K`.
* `GL_r(K)` acts on lattices (`g • L = g L`), and so does `K^×` through scalar matrices
  (`scalarGL`).
* `Vertex F r` : the vertices of the building, the homothety classes `[L]` of lattices,
  i.e. the orbits of the scalar matrices.  `GL_r(K)` acts on them.
* `IsSimplex σ` : a finite set `σ` of vertices is a simplex of the building iff it is the set
  of classes of a chain of lattices `L₀ ⊋ L₁ ⊋ ⋯ ⊋ L_k ⊋ ϖ L₀`.
-/

open Matrix

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

open Classical

variable (F : Type*) [Field F] (r : ℕ)

/-- An `O`-submodule `M ⊆ K^r` is a lattice if it is finitely generated and spans `K^r`
over `K`. -/
def IsLattice (M : Submodule (intRing F) (Fin r → Kt F)) : Prop :=
  M.FG ∧ Submodule.span (Kt F) (M : Set (Fin r → Kt F)) = ⊤

/-- An `O`-lattice in `K^r`. -/
@[ext]
structure Lattice where
  /-- The underlying `O`-submodule of `K^r`. -/
  carrier : Submodule (intRing F) (Fin r → Kt F)
  /-- It is a lattice. -/
  isLattice : IsLattice F r carrier

variable {F r}

/-- The `O`-linear map `K^r → K^r` given by `g ∈ GL_r(K)`. -/
def glLin (g : GL (Fin r) (Kt F)) : (Fin r → Kt F) →ₗ[intRing F] (Fin r → Kt F) :=
  (Matrix.mulVecLin (g : Matrix (Fin r) (Fin r) (Kt F))).restrictScalars (intRing F)

@[simp] lemma glLin_apply (g : GL (Fin r) (Kt F)) (x : Fin r → Kt F) :
    glLin g x = (g : Matrix (Fin r) (Fin r) (Kt F)) *ᵥ x := rfl

lemma IsLattice.map (g : GL (Fin r) (Kt F)) {M : Submodule (intRing F) (Fin r → Kt F)}
    (hM : IsLattice F r M) : IsLattice F r (M.map (glLin g)) := by
  refine ⟨hM.1.map _, ?_⟩
  have h1 : ((M.map (glLin g) : Submodule (intRing F) (Fin r → Kt F)) : Set (Fin r → Kt F)) =
      (Matrix.mulVecLin (g : Matrix (Fin r) (Fin r) (Kt F))) '' (M : Set (Fin r → Kt F)) := by
    rfl
  rw [h1, Submodule.span_image, hM.2, Submodule.map_top, LinearMap.range_eq_top]
  intro y
  refine ⟨(g⁻¹ : GL (Fin r) (Kt F)) *ᵥ y, ?_⟩
  simp [Matrix.mulVec_mulVec]

/-- The map `x ↦ g x` is injective. -/
lemma glLin_injective (g : GL (Fin r) (Kt F)) : Function.Injective (glLin g) := by
  intro x y h
  have := congrArg (fun z => ((g⁻¹ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) *ᵥ z) h
  simpa [Matrix.mulVec_mulVec] using this

/-- `GL_r(K)` acts on lattices: `g • L = g L`. -/
instance : SMul (GL (Fin r) (Kt F)) (Lattice F r) where
  smul g L := ⟨L.carrier.map (glLin g), L.isLattice.map g⟩

@[simp] lemma smul_carrier (g : GL (Fin r) (Kt F)) (L : Lattice F r) :
    (g • L).carrier = L.carrier.map (glLin g) := rfl

instance : MulAction (GL (Fin r) (Kt F)) (Lattice F r) where
  one_smul L := by
    ext x
    simp
  mul_smul g h L := by
    ext x
    simp only [smul_carrier, Submodule.mem_map, glLin_apply, Units.val_mul]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨y, hy, rfl⟩, by simp [Matrix.mulVec_mulVec]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp [Matrix.mulVec_mulVec]⟩

/-- The scalar matrix `a · 1 ∈ GL_r(K)` for `a ∈ K^×`. -/
def scalarGL : (Kt F)ˣ →* GL (Fin r) (Kt F) :=
  Units.map (Matrix.scalar (Fin r) : Kt F →+* Matrix (Fin r) (Fin r) (Kt F)).toMonoidHom

@[simp] lemma coe_scalarGL (a : (Kt F)ˣ) :
    ((scalarGL a : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) =
      Matrix.scalar (Fin r) (a : Kt F) := rfl

lemma scalarGL_commute (a : (Kt F)ˣ) (g : GL (Fin r) (Kt F)) :
    scalarGL a * g = g * scalarGL a := by
  ext : 1
  simp only [Units.val_mul, coe_scalarGL]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

/-- Two lattices are homothetic, `L ∼ L'`, iff `L' = a L` for some `a ∈ K^×`. -/
def IsHomothetic (L L' : Lattice F r) : Prop := ∃ a : (Kt F)ˣ, scalarGL (r := r) a • L = L'

/-- The homothety relation as a setoid. -/
def homothetic : Setoid (Lattice F r) where
  r := IsHomothetic
  iseqv := by
    refine ⟨fun L => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro L L' ⟨a, ha⟩
      subst ha
      exact ⟨a⁻¹, by rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
    · rintro L L' L'' ⟨a, ha⟩ ⟨b, hb⟩
      subst ha hb
      exact ⟨b * a, by rw [map_mul, SemigroupAction.mul_smul]⟩

variable (F r) in
/-- The vertices of the Bruhat–Tits building of `GL_r(K)`: homothety classes of
`O`-lattices in `K^r`. -/
abbrev Vertex := Quotient (homothetic (F := F) (r := r))

/-- The vertex `[L]` of a lattice `L`. -/
abbrev Lattice.vtx (L : Lattice F r) : Vertex F r := Quotient.mk _ L

lemma smul_homothetic (g : GL (Fin r) (Kt F)) {L L' : Lattice F r}
    (h : IsHomothetic L L') : IsHomothetic (g • L) (g • L') := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a, by rw [smul_smul, scalarGL_commute, SemigroupAction.mul_smul]⟩

/-- `GL_r(K)` acts on vertices. -/
instance : MulAction (GL (Fin r) (Kt F)) (Vertex F r) where
  smul g := Quotient.map (g • ·) (fun _ _ h => smul_homothetic g h)
  one_smul v := by
    induction v using Quotient.inductionOn
    exact congrArg (Quotient.mk _) (one_smul _ _)
  mul_smul g h v := by
    induction v using Quotient.inductionOn
    exact congrArg (Quotient.mk _) (SemigroupAction.mul_smul _ _ _)

@[simp] lemma smul_vtx (g : GL (Fin r) (Kt F)) (L : Lattice F r) :
    g • L.vtx = (g • L).vtx := rfl

/-- The uniformizer `ϖ = 1/t` as a unit of `K`. -/
def unifUnit : (Kt F)ˣ := Units.mk0 (unif F) (by simp [unif])

/-- A finite set `σ` of vertices is a *simplex* of the Bruhat–Tits building iff
`σ = {[L₀], …, [L_k]}` for a chain of lattices `L₀ ⊋ L₁ ⊋ ⋯ ⊋ L_k ⊋ ϖ L₀`. -/
def IsSimplex (σ : Finset (Vertex F r)) : Prop :=
  ∃ (k : ℕ) (L : Fin (k + 1) → Lattice F r),
    StrictAnti (fun i => (L i).carrier) ∧
    (scalarGL (r := r) (unifUnit (F := F)) • L 0).carrier < (L (Fin.last k)).carrier ∧
    σ = Finset.univ.image (fun i => (L i).vtx)

/-- A chamber is a maximal simplex; these are the simplices with exactly `r` vertices. -/
def IsChamber (σ : Finset (Vertex F r)) : Prop := IsSimplex σ ∧ σ.card = r

/-- `GL_r(K)` acts on finite sets of vertices. -/
def smulSet (g : GL (Fin r) (Kt F)) (σ : Finset (Vertex F r)) : Finset (Vertex F r) :=
  σ.image (g • ·)

/-- `GL_r(K)` maps simplices to simplices. -/
lemma IsSimplex.smul (g : GL (Fin r) (Kt F)) {σ : Finset (Vertex F r)} (hσ : IsSimplex σ) :
    IsSimplex (smulSet g σ) := by
  obtain ⟨k, L, hL, hlast, rfl⟩ := hσ
  have hmono := Submodule.map_strictMono_of_injective (glLin_injective g)
  refine ⟨k, fun i => g • L i, fun i j hij => hmono (hL hij), ?_, ?_⟩
  · have : scalarGL (r := r) (unifUnit (F := F)) • (g • L 0) =
        g • (scalarGL (r := r) (unifUnit (F := F)) • L 0) := by
      rw [smul_smul, scalarGL_commute, SemigroupAction.mul_smul]
    rw [this]
    exact hmono hlast
  · simp [smulSet, Finset.image_image, Function.comp_def]

/-- A nonempty subset of a simplex is a simplex (its faces). -/
lemma IsSimplex.mono {σ τ : Finset (Vertex F r)} (hσ : IsSimplex σ) (hτσ : τ ⊆ σ)
    (hτ : τ.Nonempty) : IsSimplex τ := by
  obtain ⟨k, L, hL, hlast, rfl⟩ := hσ
  set S : Finset (Fin (k + 1)) := Finset.univ.filter fun i => (L i).vtx ∈ τ with hSdef
  have hS : S.Nonempty := by
    obtain ⟨v, hv⟩ := hτ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hτσ hv)
    exact ⟨i, by simp [hSdef, hv]⟩
  have hcard : S.card = (S.card - 1) + 1 := (Nat.succ_pred_eq_of_pos hS.card_pos).symm
  set e := S.orderEmbOfFin hcard
  refine ⟨S.card - 1, fun j => L (e j), hL.comp_strictMono e.strictMono, ?_, ?_⟩
  · calc (scalarGL (r := r) (unifUnit (F := F)) • L (e 0)).carrier
        ≤ (scalarGL (r := r) (unifUnit (F := F)) • L 0).carrier :=
          Submodule.map_mono (hL.antitone (Fin.zero_le _))
      _ < (L (Fin.last k)).carrier := hlast
      _ ≤ (L (e (Fin.last _))).carrier := hL.antitone (Fin.le_last _)
  · ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hτσ hv)
      have hi : i ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]; simp [hSdef, hv]
      obtain ⟨j, hj⟩ := hi
      exact ⟨j, by rw [hj]⟩
    · rintro ⟨j, rfl⟩
      have := Finset.orderEmbOfFin_mem S hcard j
      simp only [hSdef, Finset.mem_filter] at this
      exact this.2

end GLrBuilding
