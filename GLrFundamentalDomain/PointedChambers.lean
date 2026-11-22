import GLrFundamentalDomain.Chambers

/-!
# Pointed chambers as cosets, via `pchamberEquiv`

The coset space `PChamber F r = GL_r(K) / (K^× · I)` is identified with the pointed chambers
`(C, v)` of the building (`PChamber' F r`) by the `GL_r(K)`-equivariant bijection
`pchamberEquiv : [g] ↦ g • (C₀, v₀)` of `Chambers.lean`.  All the geometric data of a coset are
defined through this bijection:

* `PChamber.toChamber c` : the underlying chamber;
* `PChamber.toFinset c` : its set of vertices; for `c = [g]` these are the vertices
  `[g · stdChain i]`, `i = 0, …, r-1` (`PChamber.toFinset_mk`);
* `PChamber.basePoint c` : the vertex at which it is pointed; `[g O^r]` for `c = [g]`.

Main results:
* `PChamber.ext_iff_toFinset` : a pointed chamber is determined by its vertex set and its base
  point;
* `PChamber.smul_eq_smul_of_forall` : two group elements which agree on the vertices of `c`
  agree on `c`;
* `exists_pchamber_of_complete_chain` : every complete chain of lattices is the vertex set of
  a pointed chamber (consequence of transitivity, `PChamber'.exists_smul_eq`);
* `exists_pchamber_superset` : every simplex is a face of a chamber;
* `vertexStabR_eq_stabilizer`, `exists_smul_stdVertex₀`, `VertexC.toVertex_bijective` : the
  analogous statements for vertices, `GL_r(K) / (K^× · GL_r(O)) ≃ Vertex F r`.
-/

open Matrix Module

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

open Classical

variable {F : Type*} [Field F] {r : ℕ}

/-! ### Vertices as cosets -/

variable (F r) in
/-- `GL_r(K)` acts transitively on lattices, hence on vertices. -/
lemma exists_smul_stdVertex₀ (v : Vertex F r) :
    ∃ g : GL (Fin r) (Kt F), v = g • stdVertex₀ F r := by
  induction v using Quotient.inductionOn with
  | h L =>
    obtain ⟨g, hg⟩ := exists_smul_stdLattice L
    exact ⟨g, by rw [stdVertex₀, smul_vtx, hg]⟩

/-- `GL_r(O)` fixes the standard lattice `O^r`. -/
lemma GLOr_smul_stdLattice (k : GL (Fin r) (PowerSeries F)) :
    GLOr F r k • stdLattice F r = stdLattice F r := by
  apply Lattice.ext
  show (stdCarrier F r).map (glLin (GLOr F r k)) = stdCarrier F r
  rw [← latOf_top, map_latOf_GLOr, Submodule.map_top, LinearMap.range_eq_top.2]
  intro v
  refine ⟨((redGL k)⁻¹ : GL (Fin r) F) *ᵥ v, ?_⟩
  simp [Matrix.mulVec_mulVec]

variable (F r) in
/-- `K^× · GL_r(O)` is exactly the stabilizer of `[O^r]` in `GL_r(K)`. -/
lemma vertexStabR_eq_stabilizer :
    vertexStabR F r = MulAction.stabilizer (GL (Fin r) (Kt F)) (stdVertex₀ F r) := by
  have key : ∀ (c : (Kt F)ˣ) (k : GL (Fin r) (PowerSeries F)),
      ((scalarGL c * GLOr F r k : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) =
        (c : Kt F) • (GLOr F r k : Matrix (Fin r) (Fin r) (Kt F)) := fun c k => by
    rw [Units.val_mul, coe_scalarGL, Matrix.smul_eq_diagonal_mul]; rfl
  ext g
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨c, k, hg⟩
    have : g = scalarGL c * GLOr F r k := Units.ext (by rw [key, hg])
    rw [this, SemigroupAction.mul_smul, scalarGL_smul_vtx, stdVertex₀, smul_vtx,
      GLOr_smul_stdLattice]
  · intro hv
    obtain ⟨a, ha⟩ := Quotient.exact hv
    rw [← SemigroupAction.mul_smul] at ha
    obtain ⟨k, hk⟩ := exists_GLOr_of_smul_stdLattice ha
    refine ⟨a⁻¹, k, ?_⟩
    rw [← key, hk, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

variable (F r) in
/-- The vertices as the coset space `GL_r(K) / (K^× · GL_r(O))`. -/
abbrev VertexC := GL (Fin r) (Kt F) ⧸ vertexStabR F r

instance : MulAction (GL (Fin r) (Kt F)) (VertexC F r) :=
  MulAction.quotient (GL (Fin r) (Kt F)) (vertexStabR F r)

/-- The map `GL_r(K) / (K^× · GL_r(O)) → Vertex F r`, `[g] ↦ [g O^r]`. -/
def VertexC.toVertex : VertexC F r → Vertex F r :=
  Quotient.lift (fun g => g • stdVertex₀ F r) (fun g h hgh => by
    have hgh : g⁻¹ * h ∈ vertexStabR F r := QuotientGroup.leftRel_apply.mp hgh
    rw [vertexStabR_eq_stabilizer, MulAction.mem_stabilizer_iff,
      SemigroupAction.mul_smul] at hgh
    calc g • stdVertex₀ F r = g • (g⁻¹ • h • stdVertex₀ F r) := by rw [hgh]
      _ = h • stdVertex₀ F r := smul_inv_smul g _)

@[simp] lemma VertexC.toVertex_mk (g : GL (Fin r) (Kt F)) :
    VertexC.toVertex (QuotientGroup.mk g : VertexC F r) = g • stdVertex₀ F r := rfl

lemma VertexC.toVertex_smul (g : GL (Fin r) (Kt F)) (v : VertexC F r) :
    VertexC.toVertex (g • v) = g • VertexC.toVertex v := by
  induction v using QuotientGroup.induction_on with
  | H h => exact SemigroupAction.mul_smul g h _

/-- The two models of the vertex set agree:
`GL_r(K) / (K^× · GL_r(O)) ≃ {homothety classes of lattices}`. -/
lemma VertexC.toVertex_bijective : Function.Bijective (VertexC.toVertex (F := F) (r := r)) := by
  refine ⟨fun c d hcd => ?_, fun v => ?_⟩
  · induction c using QuotientGroup.induction_on with
    | H g =>
    induction d using QuotientGroup.induction_on with
    | H h =>
    apply QuotientGroup.eq.2
    rw [vertexStabR_eq_stabilizer, MulAction.mem_stabilizer_iff, SemigroupAction.mul_smul]
    simp only [toVertex_mk] at hcd
    rw [← hcd, inv_smul_smul]
  · obtain ⟨g, rfl⟩ := exists_smul_stdVertex₀ F r v
    exact ⟨QuotientGroup.mk g, rfl⟩

/-- The vertices `[M 0], …, [M (r-1)]` of a complete chain are pairwise distinct. -/
lemma IsCompleteChain.vtx_injective {M : Fin r → Lattice F r} (hM : IsCompleteChain M) :
    Function.Injective fun i => (M i).vtx := by
  intro i j h
  have hr : 0 < r := i.pos
  obtain ⟨a, ha⟩ := Quotient.exact h
  have hc := congrArg Lattice.carrier ha
  rw [smul_carrier] at hc
  have h0 : (⟨0, by omega⟩ : Fin r) ≤ i := Fin.mk_le_mk.2 (Nat.zero_le _)
  have h0' : (⟨0, by omega⟩ : Fin r) ≤ j := Fin.mk_le_mk.2 (Nat.zero_le _)
  exact hM.1.injective (eq_of_homothetic_of_mem_Ioc (hM.2 _ i) (hM.1.antitone h0)
    (hM.2 _ j) (hM.1.antitone h0') a hc)

/-- The vertex set of a chamber is a simplex with exactly `r` vertices. -/
lemma Chamber.isChamber [NeZero r] (C : Chamber F r) : IsChamber C.verts := by
  obtain ⟨M, hM, hC⟩ := C.exists_chain
  have hr := NeZero.pos r
  refine ⟨⟨r - 1, fun i => M ⟨i, by omega⟩, fun i j hij => hM.1 (Fin.mk_lt_mk.2 hij), ?_, ?_⟩, ?_⟩
  · rw [Lattice.smul_unif_carrier]; exact hM.2 _ _
  · rw [hC]
    ext v
    simp only [chainVerts, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨⟨i, by omega⟩, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
  · rw [hC, chainVerts, Finset.card_image_of_injective _ hM.vtx_injective, Finset.card_univ,
      Fintype.card_fin]

/-! ### The chamber, vertices and base point of a coset `[g] ∈ GL_r(K) / (K^× · I)` -/

section PChamber

variable [NeZero r]

/-- The chamber underlying the pointed chamber `c`, via `pchamberEquiv`. -/
def PChamber.toChamber (c : PChamber F r) : Chamber F r := (pchamberEquiv c).1.1

/-- The (unpointed) chamber of `c` as its set of `r` vertices. -/
def PChamber.toFinset (c : PChamber F r) : Finset (Vertex F r) := c.toChamber.verts

/-- The vertex at which `c` is pointed. -/
def PChamber.basePoint (c : PChamber F r) : Vertex F r := (pchamberEquiv c).1.2

lemma PChamber.basePoint_mem (c : PChamber F r) : c.basePoint ∈ c.toFinset := (pchamberEquiv c).2

lemma PChamber.toFinset_smul (g : GL (Fin r) (Kt F)) (c : PChamber F r) :
    (g • c).toFinset = smulSet g c.toFinset := by
  simp [PChamber.toFinset, PChamber.toChamber, pchamberEquiv_smul]

lemma PChamber.basePoint_smul (g : GL (Fin r) (Kt F)) (c : PChamber F r) :
    (g • c).basePoint = g • c.basePoint := by
  simp [PChamber.basePoint, pchamberEquiv_smul]

/-- The vertices of the pointed chamber `[g]` are the `[g · stdChain i]`. -/
lemma PChamber.toFinset_mk (g : GL (Fin r) (Kt F)) :
    PChamber.toFinset (QuotientGroup.mk g : PChamber F r) =
      Finset.univ.image fun i => g • (stdChain F r i).vtx := by
  simp [PChamber.toFinset, PChamber.toChamber, stdPChamber', stdChamber, smulSet, chainVerts,
    Finset.image_image, Function.comp_def]

/-- The pointed chamber `[g]` is pointed at `[g O^r]`. -/
@[simp] lemma PChamber.basePoint_mk (g : GL (Fin r) (Kt F)) :
    PChamber.basePoint (QuotientGroup.mk g : PChamber F r) = g • stdVertex₀ F r := rfl

/-- A pointed chamber is determined by its vertex set and its base point. -/
lemma PChamber.ext_iff_toFinset {c d : PChamber F r} :
    c = d ↔ c.toFinset = d.toFinset ∧ c.basePoint = d.basePoint := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => pchamberEquiv.injective ?_⟩
  exact Subtype.ext (Prod.ext (Chamber.ext h1) h2)

/-- Two elements of `GL_r(K)` which agree on the vertices of `c` agree on `c`. -/
lemma PChamber.smul_eq_smul_of_forall (g h : GL (Fin r) (Kt F)) (c : PChamber F r)
    (H : ∀ v ∈ c.toFinset, g • v = h • v) : g • c = h • c := by
  rw [PChamber.ext_iff_toFinset, PChamber.toFinset_smul, PChamber.toFinset_smul,
    PChamber.basePoint_smul, PChamber.basePoint_smul]
  exact ⟨Finset.image_congr H, H _ c.basePoint_mem⟩

/-- The vertices of a pointed chamber form a chamber of the building. -/
lemma PChamber.isChamber_toFinset (c : PChamber F r) : IsChamber c.toFinset :=
  c.toChamber.isChamber

/-- Every pointed chamber `(C, v)` comes from a coset. -/
lemma PChamber.exists_of_chamber (C : Chamber F r) {v : Vertex F r} (hv : v ∈ C.verts) :
    ∃ c : PChamber F r, c.toChamber = C ∧ c.basePoint = v :=
  ⟨pchamberEquiv.symm ⟨(C, v), hv⟩, by
    simp [PChamber.toChamber, PChamber.basePoint]⟩

/-- A complete chain of lattices `M₀ ⊋ M₁ ⊋ ⋯ ⊋ M_{r-1} ⊋ ϖ M₀` (all quotients
one-dimensional) is the vertex set of a pointed chamber (pointed at `[M₀]`). -/
lemma exists_pchamber_of_complete_chain (M : Fin r → Lattice F r)
    (hM : StrictAnti fun i => (M i).carrier)
    (hlast : unifMul (M 0).carrier < (M ⟨r - 1, by have := NeZero.pos r; omega⟩).carrier) :
    ∃ c : PChamber F r, c.toFinset = Finset.univ.image fun i => (M i).vtx := by
  have hc : IsCompleteChain M := by
    refine ⟨hM, fun i j => ?_⟩
    calc unifMul (M i).carrier ≤ unifMul (M 0).carrier :=
          unifMul_mono (hM.antitone (Fin.zero_le i))
      _ < _ := hlast
      _ ≤ (M j).carrier := hM.antitone (Fin.mk_le_mk.2 (by have := j.2; omega))
  let C : Chamber F r := ⟨chainVerts M, M, hc, rfl⟩
  obtain ⟨c, hcC, -⟩ := PChamber.exists_of_chamber C
    (v := (M 0).vtx) (Finset.mem_image_of_mem _ (Finset.mem_univ 0))
  exact ⟨c, by rw [PChamber.toFinset, hcC]; rfl⟩

/-- Every chamber of the building (a simplex with `r` vertices), pointed at any of its vertices,
comes from a pointed chamber. -/
lemma PChamber.exists_of_isChamber {σ : Finset (Vertex F r)} (hσ : IsChamber σ) {v : Vertex F r}
    (hv : v ∈ σ) : ∃ c : PChamber F r, c.toFinset = σ ∧ c.basePoint = v := by
  obtain ⟨⟨k, L, hL, hlast, rfl⟩, hcard⟩ := hσ
  rw [Lattice.smul_unif_carrier] at hlast
  have hlow : ∀ i, unifMul (L 0).carrier < (L i).carrier := fun i =>
    hlast.trans_le (hL.antitone (Fin.le_last i))
  have hinj : Function.Injective fun i => (L i).vtx := by
    intro i j h
    obtain ⟨a, ha⟩ := Quotient.exact h
    have hc := congrArg Lattice.carrier ha
    rw [smul_carrier] at hc
    exact hL.injective (eq_of_homothetic_of_mem_Ioc (hlow i) (hL.antitone (Fin.zero_le i))
      (hlow j) (hL.antitone (Fin.zero_le j)) a hc)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
  subst hcard
  have hc : IsCompleteChain L := ⟨hL, fun i j =>
    (unifMul_mono (hL.antitone (Fin.zero_le i))).trans_lt
      (hlast.trans_le (hL.antitone (Fin.le_last j)))⟩
  obtain ⟨c, hcC, hcv⟩ := PChamber.exists_of_chamber (⟨chainVerts L, L, hc, rfl⟩ : Chamber F _) hv
  exact ⟨c, by rw [PChamber.toFinset, hcC]; rfl, hcv⟩

end PChamber

/-! ### Every simplex is a face of a chamber -/

/-- Every simplex is a face of a chamber: deduced from the correspondence (1), the refinement of
flags (2), `finrank_red` and `exists_pchamber_of_complete_chain`. -/
theorem exists_pchamber_superset [NeZero r] {σ : Finset (Vertex F r)} (hσ : IsSimplex σ) :
    ∃ c : PChamber F r, σ ⊆ c.toFinset := by
  obtain ⟨k, L, hL, hlast, rfl⟩ := hσ
  rw [Lattice.smul_unif_carrier] at hlast
  obtain ⟨hfdim, hdim⟩ := finrank_red (L 0)
  set L0 := (L 0).carrier with hL0
  have hr := NeZero.pos r
  let e := iccEquivSubspace L0
  have hmem : ∀ i, (L i).carrier ∈ Set.Icc (unifMul L0) L0 := fun i =>
    ⟨hlast.le.trans (hL.antitone (Fin.le_last i)), hL.antitone (Fin.zero_le i)⟩
  -- the flag `Lᵢ / ϖ L₀` attached to the simplex, via (1)
  let W : Fin (k + 1) → Submodule F (Red L0) := fun i => e ⟨_, hmem i⟩
  have hc : IsChain (· ≤ ·) (Set.range W) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    rcases le_total i j with h | h
    · exact Or.inr (e.monotone (Subtype.mk_le_mk.2 (hL.antitone h)))
    · exact Or.inl (e.monotone (Subtype.mk_le_mk.2 (hL.antitone h)))
  -- (2) refine it to a maximal flag
  obtain ⟨f, hf, hfd, hcf⟩ := exists_maximal_flag_refinement hc
  have hf0 : f ⟨0, by omega⟩ = ⊥ := by
    rw [← Submodule.finrank_eq_zero (R := F)]; exact hfd _
  have hftop : f ⟨r, by omega⟩ = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hfd]; exact hdim.symm)
  -- back to lattices via (1)
  let N : Fin r → Lattice F r := fun i =>
    ⟨(e.symm (f ⟨r - i, by omega⟩) : Submodule (intRing F) (Fin r → Kt F)),
      isLattice_of_mem_Icc (L 0).isLattice (e.symm _).2⟩
  have hN : StrictAnti fun i => (N i).carrier := by
    intro i j hij
    have : f ⟨r - j, by omega⟩ < f ⟨r - i, by omega⟩ :=
      hf (Fin.mk_lt_mk.2 (by have := i.2; have := j.2; have : (i : ℕ) < j := hij; omega))
    exact Subtype.coe_lt_coe.2 (e.symm.strictMono this)
  have hN0 : (N 0).carrier = L0 := by
    show (e.symm (f ⟨r - 0, _⟩) : Submodule (intRing F) (Fin r → Kt F)) = L0
    simp only [Nat.sub_zero]
    rw [hftop]; exact iccEquivSubspace_symm_top L0
  have hNlast : unifMul (N 0).carrier < (N ⟨r - 1, by omega⟩).carrier := by
    rw [hN0]
    show unifMul L0 < (e.symm (f ⟨r - (r - 1), _⟩) : Submodule (intRing F) (Fin r → Kt F))
    refine lt_of_eq_of_lt (iccEquivSubspace_symm_bot L0).symm ?_
    rw [← hf0]
    exact Subtype.coe_lt_coe.2 (e.symm.strictMono (hf (Fin.mk_lt_mk.2 (by omega))))
  obtain ⟨c, hcN⟩ := exists_pchamber_of_complete_chain N hN hNlast
  refine ⟨c, ?_⟩
  rw [hcN]
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨m, hm⟩ := hcf ⟨i, rfl⟩
  have hWi : (e.symm (W i) : Submodule (intRing F) (Fin r → Kt F)) = (L i).carrier := by
    simp [W]
  have hm0 : (m : ℕ) ≠ 0 := by
    intro h0
    have : W i = ⊥ := by rw [← hm, ← hf0]; congr 1; exact Fin.ext h0
    rw [this, iccEquivSubspace_symm_bot] at hWi
    exact (lt_of_lt_of_le hlast (hL.antitone (Fin.le_last i))).ne hWi
  have hmr : (m : ℕ) ≤ r := by have := m.2; omega
  refine Finset.mem_image.2 ⟨⟨r - m, by omega⟩, Finset.mem_univ _, ?_⟩
  have hNi : N ⟨r - m, by omega⟩ = L i := by
    apply Lattice.ext
    rw [← hWi, ← hm]
    show (e.symm (f ⟨r - (r - m), _⟩) : Submodule (intRing F) (Fin r → Kt F)) = _
    congr 3
    exact Fin.ext (by simp only; omega)
  rw [hNi]

end GLrBuilding
