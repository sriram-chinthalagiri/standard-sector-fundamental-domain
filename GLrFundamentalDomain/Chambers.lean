import GLrFundamentalDomain.Flags
import GLrFundamentalDomain.FlagBasis

/-!
# Chambers as complete chains of lattices, and pointed chambers

* `IsCompleteChain M` : `M 0 ⊋ M 1 ⊋ ⋯ ⊋ M (r-1) ⊋ ϖ M 0`, a complete chain of lattices.
* `Chamber F r` : a *chamber* is a set of vertices of the form `{[M 0], …, [M (r-1)]}` for a
  complete chain `M`.  `GL_r(K)` acts on chambers.
* `PChamber' F r` : pairs `(C, v)` with `C` a chamber and `v ∈ C` a vertex.  `GL_r(K)` acts on
  them.
* `stdChain i = {x ∈ O^r | x_j ∈ ϖ O for j ≥ r - i}`; the standard chamber `C₀` is the chamber of
  this chain, and `v₀ = [O^r]`; `stdPChamber' = (C₀, v₀)`.

Main results:
* `PChamber'.exists_smul_eq` : `GL_r(K)` acts transitively on `PChamber' F r`.
* `PChamber'.stabilizer_std` : the stabilizer of `(C₀, v₀)` is `K^× · I` (`chamberStab F r`).
* `pchamberEquiv` : consequently `GL_r(K)/(K^× · I) ≃ PChamber' F r`, `[g] ↦ g • (C₀, v₀)`,
  a `GL_r(K)`-equivariant bijection.
-/

open Matrix Module

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

open Classical

variable {F : Type*} [Field F] {r : ℕ}

/-! ### Chambers and pointed chambers -/

/-- A complete chain of lattices `M 0 ⊋ M 1 ⊋ ⋯ ⊋ M (r-1) ⊋ ϖ M 0`. -/
def IsCompleteChain (M : Fin r → Lattice F r) : Prop :=
  StrictAnti (fun i => (M i).carrier) ∧ ∀ i j, unifMul (M i).carrier < (M j).carrier

/-- The set of vertices `{[M 0], …, [M (r-1)]}` of a chain of lattices. -/
def chainVerts (M : Fin r → Lattice F r) : Finset (Vertex F r) :=
  Finset.univ.image fun i => (M i).vtx

variable (F r) in
/-- A *chamber* of the building: the vertex set of a complete chain of lattices. -/
@[ext]
structure Chamber where
  /-- The vertices of the chamber. -/
  verts : Finset (Vertex F r)
  exists_chain : ∃ M : Fin r → Lattice F r, IsCompleteChain M ∧ verts = chainVerts M

lemma unifMul_map_glLin (g : GL (Fin r) (Kt F)) (M : Submodule (intRing F) (Fin r → Kt F)) :
    unifMul (M.map (glLin g)) = (unifMul M).map (glLin g) := by
  unfold unifMul
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, glLin_apply, mulVec_mulVec, ← Units.val_mul, scalarGL_commute]

lemma IsCompleteChain.smul (g : GL (Fin r) (Kt F)) {M : Fin r → Lattice F r}
    (hM : IsCompleteChain M) : IsCompleteChain fun i => g • M i := by
  have hmono := Submodule.map_strictMono_of_injective (glLin_injective g)
  refine ⟨fun i j hij => hmono (hM.1 hij), fun i j => ?_⟩
  simp only [smul_carrier, unifMul_map_glLin]
  exact hmono (hM.2 i j)

lemma smulSet_chainVerts (g : GL (Fin r) (Kt F)) (M : Fin r → Lattice F r) :
    smulSet g (chainVerts M) = chainVerts fun i => g • M i := by
  simp [smulSet, chainVerts, Finset.image_image, Function.comp_def]

instance : SMul (GL (Fin r) (Kt F)) (Chamber F r) where
  smul g C := ⟨smulSet g C.verts, by
    obtain ⟨M, hM, hC⟩ := C.exists_chain
    exact ⟨_, hM.smul g, by rw [hC, smulSet_chainVerts]⟩⟩

@[simp] lemma Chamber.smul_verts (g : GL (Fin r) (Kt F)) (C : Chamber F r) :
    (g • C).verts = smulSet g C.verts := rfl

instance : MulAction (GL (Fin r) (Kt F)) (Chamber F r) where
  one_smul C := by ext1; simp [smulSet]
  mul_smul g h C := by
    ext1
    simp [smulSet, Finset.image_image, Function.comp_def, SemigroupAction.mul_smul]

variable (F r) in
/-- *Pointed chambers* (second model): pairs `(C, v)` of a chamber `C` and a vertex `v ∈ C`. -/
def PChamber' := {p : Chamber F r × Vertex F r // p.2 ∈ p.1.verts}

instance : SMul (GL (Fin r) (Kt F)) (PChamber' F r) where
  smul g p := ⟨(g • p.1.1, g • p.1.2), by
    simpa [smulSet] using Finset.mem_image_of_mem (g • ·) p.2⟩

@[simp] lemma PChamber'.smul_val (g : GL (Fin r) (Kt F)) (p : PChamber' F r) :
    (g • p).1 = (g • p.1.1, g • p.1.2) := rfl

instance : MulAction (GL (Fin r) (Kt F)) (PChamber' F r) where
  one_smul p := Subtype.ext (by simp)
  mul_smul g h p := Subtype.ext (by simp [SemigroupAction.mul_smul])

/-! ### Reduction modulo `ϖ` on `O^r` and the standard chamber -/

/-- The constant terms `x ↦ (x_j mod ϖ)_j`, `K^r → F^r` (meaningful on `O^r`). -/
def redV (x : Fin r → Kt F) : Fin r → F := fun j => (x j).coeff 0

lemma coeff_zero_ofPowerSeries (p : PowerSeries F) :
    (HahnSeries.ofPowerSeries ℤ F p).coeff 0 = PowerSeries.constantCoeff p := by
  have h := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) p 0
  simp only [Nat.cast_zero] at h
  rw [h]; simp

lemma coeff_zero_mul_of_mem {a b : Kt F} (ha : a ∈ intRing F) (hb : b ∈ intRing F) :
    (a * b).coeff 0 = a.coeff 0 * b.coeff 0 := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  rw [← map_mul, coeff_zero_ofPowerSeries, coeff_zero_ofPowerSeries, coeff_zero_ofPowerSeries,
    map_mul]

lemma unif_eq_ofPowerSeries_X : unif F = HahnSeries.ofPowerSeries ℤ F PowerSeries.X := by
  rw [HahnSeries.ofPowerSeries_X]; rfl

/-- An element of `O` with vanishing constant term is divisible by `ϖ` in `O`. -/
lemma exists_unif_mul_of_coeff_zero {a : Kt F} (ha : a ∈ intRing F) (h0 : a.coeff 0 = 0) :
    ∃ b ∈ intRing F, unif F * b = a := by
  obtain ⟨p, rfl⟩ := ha
  rw [coeff_zero_ofPowerSeries] at h0
  obtain ⟨q, rfl⟩ := PowerSeries.X_dvd_iff.2 h0
  exact ⟨_, ⟨q, rfl⟩, by rw [unif_eq_ofPowerSeries_X, map_mul]⟩

lemma C_mem_intRing (c : F) : HahnSeries.C c ∈ intRing F :=
  ⟨PowerSeries.C c, HahnSeries.ofPowerSeries_C c⟩

lemma redV_add (x y : Fin r → Kt F) : redV (x + y) = redV x + redV y := by
  ext j; simp [redV]

lemma redV_sub (x y : Fin r → Kt F) : redV (x - y) = redV x - redV y := by
  ext j; simp [redV]

lemma redV_smul (o : intRing F) {x : Fin r → Kt F} (hx : ∀ j, x j ∈ intRing F) :
    redV (o • x) = (o : Kt F).coeff 0 • redV x := by
  ext j
  simp only [redV, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
  exact coeff_zero_mul_of_mem o.2 (hx j)

/-- The constant vector `(C v_j)_j ∈ O^r` lifting `v ∈ F^r`. -/
def constVec (v : Fin r → F) : Fin r → Kt F := fun j => HahnSeries.C (v j)

lemma constVec_mem (v : Fin r → F) (j : Fin r) : constVec v j ∈ intRing F := C_mem_intRing _

lemma redV_constVec (v : Fin r → F) : redV (constVec v) = v := by
  ext j; simp [redV, constVec]

/-- The lattice `{x ∈ O^r | (x mod ϖ) ∈ W}` attached to a subspace `W ⊆ F^r`. -/
def latOf (W : Submodule F (Fin r → F)) : Submodule (intRing F) (Fin r → Kt F) where
  carrier := {x | (∀ j, x j ∈ intRing F) ∧ redV x ∈ W}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨fun j => (intRing F).add_mem (hx j) (hy j), ?_⟩
    have : redV (x + y) = redV x + redV y := by ext j; simp [redV]
    rw [this]; exact W.add_mem hx' hy'
  zero_mem' := ⟨fun _ => (intRing F).zero_mem, by
    have : redV (0 : Fin r → Kt F) = 0 := by ext j; simp [redV]
    rw [this]; exact W.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨fun j => (intRing F).mul_mem c.2 (hx j), ?_⟩
    rw [redV_smul c hx]; exact W.smul_mem _ hx'

lemma latOf_top : latOf (⊤ : Submodule F (Fin r → F)) = stdCarrier F r := by
  ext x; simp [latOf, stdCarrier]

lemma mem_latOf {W : Submodule F (Fin r → F)} {x : Fin r → Kt F} :
    x ∈ latOf W ↔ (∀ j, x j ∈ intRing F) ∧ redV x ∈ W := Iff.rfl

lemma latOf_bot : latOf (⊥ : Submodule F (Fin r → F)) = unifMul (stdCarrier F r) := by
  ext x
  rw [mem_latOf, mem_unifMul, Submodule.mem_bot]
  constructor
  · rintro ⟨hx, h0⟩
    have h0' : ∀ j, (x j).coeff 0 = 0 := fun j => congrFun h0 j
    choose b hb hbx using fun j => exists_unif_mul_of_coeff_zero (hx j) (h0' j)
    exact ⟨b, hb, funext fun j => by simp [unifO, Subring.smul_def, hbx j]⟩
  · rintro ⟨y, hy, rfl⟩
    have hu := unif_mem_intRing (F := F)
    refine ⟨fun j => (intRing F).mul_mem hu (hy j), ?_⟩
    rw [redV_smul _ hy]
    have : ((unifO F : intRing F) : Kt F).coeff 0 = 0 := by
      simp [unifO, unif]
    rw [this, zero_smul]

lemma latOf_le_latOf_iff {W W' : Submodule F (Fin r → F)} : latOf W ≤ latOf W' ↔ W ≤ W' := by
  constructor
  · intro h v hv
    have := (h ⟨constVec_mem v, by rwa [redV_constVec]⟩).2
    rwa [redV_constVec] at this
  · rintro h x ⟨hx, hx'⟩
    exact ⟨hx, h hx'⟩

lemma latOf_lt_latOf_iff {W W' : Submodule F (Fin r → F)} : latOf W < latOf W' ↔ W < W' := by
  simp only [lt_iff_le_not_ge, latOf_le_latOf_iff]

lemma latOf_strictMono : StrictMono (latOf (F := F) (r := r)) :=
  fun _ _ h => lt_of_le_not_ge (latOf_le_latOf_iff.2 h.le) (fun h' => h.not_ge
    (latOf_le_latOf_iff.1 h'))

lemma latOf_mem_Icc (W : Submodule F (Fin r → F)) :
    latOf W ∈ Set.Icc (unifMul (stdCarrier F r)) (stdCarrier F r) := by
  rw [← latOf_bot, ← latOf_top]
  exact ⟨latOf_le_latOf_iff.2 bot_le, latOf_le_latOf_iff.2 le_top⟩

lemma isLattice_latOf (W : Submodule F (Fin r → F)) : IsLattice F r (latOf W) :=
  isLattice_of_mem_Icc (isLattice_stdCarrier F r) (latOf_mem_Icc W)

/-- Every `O`-submodule between `ϖ O^r` and `O^r` is `latOf W` for a subspace `W ⊆ F^r`. -/
lemma exists_eq_latOf {M : Submodule (intRing F) (Fin r → Kt F)}
    (hM : M ∈ Set.Icc (unifMul (stdCarrier F r)) (stdCarrier F r)) :
    ∃ W : Submodule F (Fin r → F), latOf W = M := by
  have hO : ∀ x ∈ M, ∀ j, x j ∈ intRing F := fun x hx => hM.2 hx
  let W : Submodule F (Fin r → F) :=
    { carrier := redV '' M
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, M.add_mem hx hy, redV_add x y⟩
      zero_mem' := ⟨0, M.zero_mem, by ext j; simp [redV]⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        refine ⟨constO F c • x, M.smul_mem _ hx, ?_⟩
        rw [redV_smul _ (hO x hx)]
        congr 1
        show (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C c)).coeff 0 = c
        rw [coeff_zero_ofPowerSeries]; simp }
  refine ⟨W, le_antisymm ?_ fun x hx => ⟨hO x hx, x, hx, rfl⟩⟩
  rintro x ⟨hx, m, hm, hmx⟩
  have hxm : x - m ∈ latOf ⊥ := by
    refine ⟨fun j => (intRing F).sub_mem (hx j) (hO m hm j), ?_⟩
    rw [redV_sub, hmx, sub_self]; exact Submodule.zero_mem _
  rw [latOf_bot] at hxm
  have := M.add_mem (hM.1 hxm) hm
  rwa [sub_add_cancel] at this

variable (F r) in
/-- The standard complete chain `stdChain i = {x ∈ O^r | x_j ∈ ϖ O for j ≥ r - i}`,
`O^r = stdChain 0 ⊋ stdChain 1 ⊋ ⋯ ⊋ stdChain (r-1) ⊋ ϖ O^r`. -/
def stdChain (i : Fin r) : Lattice F r := ⟨latOf (stdW r i), isLattice_latOf _⟩

lemma stdW_strictAnti : StrictAnti fun i : Fin r => stdW (F := F) r i := by
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  refine lt_of_le_of_ne (fun v hv k hk => hv k (by omega)) fun h => ?_
  have hmem : (Pi.single (⟨r - j, by omega⟩ : Fin r) (1 : F)) ∈ stdW (F := F) r i := by
    intro k hk
    rw [Pi.single_apply, if_neg]
    intro hk'
    subst hk'
    simp at hk
    omega
  simp only at h
  rw [← h] at hmem
  have := hmem ⟨r - j, by omega⟩ le_rfl
  simp at this

lemma bot_lt_stdW (i : Fin r) : ⊥ < stdW (F := F) r i := by
  have hi := i.2
  rw [bot_lt_iff_ne_bot]
  intro h
  have hmem : (Pi.single (⟨0, by omega⟩ : Fin r) (1 : F)) ∈ stdW (F := F) r i := by
    intro k hk
    rw [Pi.single_apply, if_neg]
    intro hk'
    subst hk'
    simp at hk
    omega
  rw [h, Submodule.mem_bot] at hmem
  have := congrFun hmem ⟨0, by omega⟩
  simp at this

lemma unifMul_mono {M N : Submodule (intRing F) (Fin r → Kt F)} (h : M ≤ N) :
    unifMul M ≤ unifMul N := Submodule.map_mono h

lemma isCompleteChain_stdChain : IsCompleteChain (stdChain F r) := by
  refine ⟨fun i j hij => latOf_strictMono (stdW_strictAnti hij), fun i j => ?_⟩
  show unifMul (latOf _) < latOf _
  calc unifMul (latOf (stdW (F := F) r i)) ≤ unifMul (stdCarrier F r) :=
        unifMul_mono (latOf_mem_Icc _).2
    _ = latOf ⊥ := latOf_bot.symm
    _ < latOf (stdW r j) := latOf_strictMono (bot_lt_stdW j)

lemma stdChain_zero [NeZero r] : stdChain F r 0 = stdLattice F r := by
  apply Lattice.ext
  show latOf _ = stdCarrier F r
  rw [← latOf_top]
  congr 1
  ext v
  simp only [Submodule.mem_top, iff_true]
  intro j hj
  simp at hj
  omega

variable (F r) in
/-- The standard chamber `C₀ = {[stdChain 0], …, [stdChain (r-1)]}`. -/
def stdChamber : Chamber F r := ⟨chainVerts (stdChain F r), _, isCompleteChain_stdChain, rfl⟩

variable (F r) in
/-- The standard pointed chamber `(C₀, v₀)`, `v₀ = [O^r]`. -/
def stdPChamber' [NeZero r] : PChamber' F r :=
  ⟨(stdChamber F r, stdVertex₀ F r), by
    refine Finset.mem_image.2 ⟨0, Finset.mem_univ _, ?_⟩
    rw [stdChain_zero]; rfl⟩

/-! ### Transitivity -/

lemma scalarGL_smul_vtx (a : (Kt F)ˣ) (v : Vertex F r) : scalarGL (r := r) a • v = v := by
  induction v using Quotient.inductionOn with
  | h L =>
    exact Quotient.sound ⟨a⁻¹, by rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩


/-- `GL_r(K)` acts transitively on lattices. -/
lemma exists_smul_stdLattice (L : Lattice F r) : ∃ g : GL (Fin r) (Kt F), g • stdLattice F r = L := by
  set M := L.carrier
  haveI : Module.Finite (intRing F) M := Module.Finite.iff_fg.2 L.isLattice.1
  haveI : Module.IsTorsionFree (intRing F) M := isTorsionFree_sub M
  haveI : Module.Free (intRing F) M := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis (intRing F) M
  have hcard := card_basis_lattice L b
  let b' := b.reindex (Fintype.equivFinOfCardEq hcard)
  obtain ⟨-, hli⟩ := span_linearIndependent_basis_lattice L b'
  let A : Matrix (Fin r) (Fin r) (Kt F) := Matrix.of fun a l => (b' l : Fin r → Kt F) a
  have hU : IsUnit A := Matrix.linearIndependent_cols_iff_isUnit.1 hli
  have hA : ∀ x : Fin r → Kt F, A *ᵥ x = ∑ l, x l • (b' l : Fin r → Kt F) := fun x => by
    ext a
    simp [Matrix.mulVec, dotProduct, A, Finset.sum_apply, mul_comm]
  refine ⟨hU.unit, Lattice.ext ?_⟩
  rw [smul_carrier]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [glLin_apply, IsUnit.unit_spec, hA]
    refine Submodule.sum_mem _ fun l _ => ?_
    have := M.smul_mem (⟨x l, hx l⟩ : intRing F) (b' l).2
    rwa [Subring.smul_def] at this
  · intro hy
    have h2 := congrArg Subtype.val (b'.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def] at h2
    refine ⟨fun l => (b'.repr ⟨y, hy⟩ l : Kt F), fun l => (b'.repr _ l).2, ?_⟩
    rw [glLin_apply, IsUnit.unit_spec, hA]
    exact h2

lemma Fin.val_add_of_lt' {i j : Fin r} (h : (i : ℕ) + j < r) : ((i + j : Fin r) : ℕ) = i + j := by
  rw [Fin.val_add, Nat.mod_eq_of_lt h]

lemma Fin.val_add_of_ge' {i j : Fin r} (h : r ≤ (i : ℕ) + j) : ((i + j : Fin r) : ℕ) = i + j - r := by
  rw [Fin.val_add, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

/-- `ϖ L` as a lattice. -/
abbrev Lattice.unifSmul (L : Lattice F r) : Lattice F r := scalarGL (r := r) (unifUnit (F := F)) • L

lemma unifMul_strictMono : StrictMono (unifMul (F := F) (r := r)) :=
  Submodule.map_strictMono_of_injective (glLin_injective _)

/-- The rotation `M j ⊋ ⋯ ⊋ M (r-1) ⊋ ϖ M 0 ⊋ ⋯ ⊋ ϖ M (j-1)` of a complete chain `M`. -/
def rotateChain (M : Fin r → Lattice F r) (j : Fin r) (i : Fin r) : Lattice F r :=
  if (i : ℕ) + j < r then M (i + j) else (M (i + j)).unifSmul

lemma rotateChain_vtx (M : Fin r → Lattice F r) (j i : Fin r) :
    (rotateChain M j i).vtx = (M (i + j)).vtx := by
  unfold rotateChain
  split_ifs
  · rfl
  · rw [← smul_vtx, scalarGL_smul_vtx]

/-- Rotating a complete chain so that it starts at `M j`. -/
lemma IsCompleteChain.exists_rotate {M : Fin r → Lattice F r} (hM : IsCompleteChain M)
    (j : Fin r) : ∃ M' : Fin r → Lattice F r, IsCompleteChain M' ∧ chainVerts M' = chainVerts M ∧
      ∃ h : 0 < r, M' ⟨0, h⟩ = M j := by
  have hr : 0 < r := Fin.pos j
  refine ⟨rotateChain M j, ⟨fun i i' hii' => ?_, fun a b => ?_⟩, ?_, hr, ?_⟩
  · have hii'' : (i : ℕ) < i' := hii'
    simp only [rotateChain]
    by_cases h1 : (i : ℕ) + j < r <;> by_cases h2 : (i' : ℕ) + j < r
    · rw [if_pos h1, if_pos h2]
      exact hM.1 (show ((i + j : Fin r) : ℕ) < (i' + j : Fin r) by
        rw [Fin.val_add_of_lt' h1, Fin.val_add_of_lt' h2]; omega)
    · rw [if_pos h1, if_neg h2]
      exact hM.2 _ _
    · omega
    · rw [if_neg h1, if_neg h2]
      exact unifMul_strictMono (hM.1 (show ((i + j : Fin r) : ℕ) < (i' + j : Fin r) by
        rw [Fin.val_add_of_ge' (by omega), Fin.val_add_of_ge' (by omega)]; omega))
  · simp only [rotateChain]
    by_cases h1 : (a : ℕ) + j < r <;> by_cases h2 : (b : ℕ) + j < r
    · rw [if_pos h1, if_pos h2]
      exact hM.2 _ _
    · rw [if_pos h1, if_neg h2]
      exact unifMul_strictMono (hM.1 (show ((b + j : Fin r) : ℕ) < (a + j : Fin r) by
        rw [Fin.val_add_of_lt' h1, Fin.val_add_of_ge' (by omega)]; omega))
    · rw [if_neg h1, if_pos h2]
      exact lt_of_le_of_lt (unifMul_le _) (hM.2 _ _)
    · rw [if_neg h1, if_neg h2]
      exact unifMul_strictMono (hM.2 _ _)
  · ext v
    simp only [chainVerts, Finset.mem_image, Finset.mem_univ, true_and, rotateChain_vtx]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨k, rfl⟩
      haveI : NeZero r := ⟨hr.ne'⟩
      exact ⟨k - j, by rw [sub_add_cancel]⟩
  · have h0 : (0 : ℕ) + j < r := by simp
    simp only [rotateChain]
    rw [if_pos h0]
    congr 1
    ext
    rw [Fin.val_add_of_lt' h0]; simp

/-- The reduction of `k ∈ GL_r(O)` modulo `ϖ`, in `GL_r(F)`. -/
def redGL (k : GL (Fin r) (PowerSeries F)) : GL (Fin r) F :=
  Matrix.GeneralLinearGroup.map (PowerSeries.constantCoeff (R := F)) k

lemma redV_mulVec {A : Matrix (Fin r) (Fin r) (Kt F)} (hA : ∀ i j, A i j ∈ intRing F)
    {x : Fin r → Kt F} (hx : ∀ j, x j ∈ intRing F) :
    redV (A *ᵥ x) = (A.map fun a => a.coeff 0) *ᵥ redV x := by
  ext i
  simp only [redV, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [HahnSeries.coeff_sum]
  exact Finset.sum_congr rfl fun j _ => coeff_zero_mul_of_mem (hA i j) (hx j)

lemma mulVec_mem_of_mem {A : Matrix (Fin r) (Fin r) (Kt F)} (hA : ∀ i j, A i j ∈ intRing F)
    {x : Fin r → Kt F} (hx : ∀ j, x j ∈ intRing F) (i : Fin r) : (A *ᵥ x) i ∈ intRing F := by
  simp only [Matrix.mulVec, dotProduct]
  exact (intRing F).sum_mem fun j _ => (intRing F).mul_mem (hA i j) (hx j)

lemma GLOr_apply_mem (k : GL (Fin r) (PowerSeries F)) (i j : Fin r) :
    (GLOr F r k : Matrix (Fin r) (Fin r) (Kt F)) i j ∈ intRing F :=
  ⟨k i j, rfl⟩

lemma map_coeff_GLOr (k : GL (Fin r) (PowerSeries F)) :
    ((GLOr F r k : Matrix (Fin r) (Fin r) (Kt F)).map fun a => a.coeff 0) =
      (redGL k : Matrix (Fin r) (Fin r) F) := by
  ext i j
  show (HahnSeries.ofPowerSeries ℤ F (k i j)).coeff 0 = _
  rw [coeff_zero_ofPowerSeries]; rfl

lemma map_latOf_GLOr_le (k : GL (Fin r) (PowerSeries F)) (W : Submodule F (Fin r → F)) :
    (latOf W).map (glLin (GLOr F r k)) ≤
      latOf (W.map (Matrix.mulVecLin (redGL k : Matrix (Fin r) (Fin r) F))) := by
  rintro _ ⟨x, ⟨hx, hx'⟩, rfl⟩
  refine ⟨mulVec_mem_of_mem (GLOr_apply_mem k) hx, ?_⟩
  rw [glLin_apply, redV_mulVec (GLOr_apply_mem k) hx, map_coeff_GLOr]
  exact ⟨_, hx', rfl⟩

/-- `k ∈ GL_r(O)` maps `latOf W` to `latOf (k̄ W)`. -/
lemma map_latOf_GLOr (k : GL (Fin r) (PowerSeries F)) (W : Submodule F (Fin r → F)) :
    (latOf W).map (glLin (GLOr F r k)) =
      latOf (W.map (Matrix.mulVecLin (redGL k : Matrix (Fin r) (Fin r) F))) := by
  refine le_antisymm (map_latOf_GLOr_le k W) fun y hy => ?_
  have h1 := map_latOf_GLOr_le k⁻¹ (W.map (Matrix.mulVecLin (redGL k : Matrix (Fin r) (Fin r) F)))
  have hW : (W.map (Matrix.mulVecLin (redGL k : Matrix (Fin r) (Fin r) F))).map
      (Matrix.mulVecLin (redGL k⁻¹ : Matrix (Fin r) (Fin r) F)) = W := by
    rw [← Submodule.map_comp]
    convert Submodule.map_id W
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, LinearMap.id_apply]
    rw [← Units.val_mul]
    simp only [redGL, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  rw [hW] at h1
  refine ⟨(GLOr F r k⁻¹ : Matrix (Fin r) (Fin r) (Kt F)) *ᵥ y, h1 ⟨y, hy, rfl⟩, ?_⟩
  rw [glLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Matrix.one_mulVec]

/-- The embedding `GL_r(F) → GL_r(O)` by constants; it is a section of `redGL`. -/
def constGL : GL (Fin r) F →* GL (Fin r) (PowerSeries F) :=
  Matrix.GeneralLinearGroup.map (PowerSeries.C (R := F))

lemma redGL_constGL (h : GL (Fin r) F) : redGL (constGL h) = h := by
  ext i j; simp [redGL, constGL]

/-! ### The stabilizer -/

lemma glLin_scalarGL_apply (a : (Kt F)ˣ) (x : Fin r → Kt F) :
    glLin (scalarGL (r := r) a) x = (a : Kt F) • x := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal, Finset.sum_ite_eq]

lemma mem_intRing_of_order_nonneg {a : Kt F} (ha : 0 ≤ a.order) : a ∈ intRing F := by
  refine ⟨PowerSeries.X ^ a.order.toNat * a.powerSeriesPart, ?_⟩
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow, Int.toNat_of_nonneg ha]
  exact LaurentSeries.single_order_mul_powerSeriesPart a

lemma map_scalar_le {N : Submodule (intRing F) (Fin r → Kt F)} {c : (Kt F)ˣ}
    (hc : (c : Kt F) ∈ intRing F) : N.map (glLin (scalarGL (r := r) c)) ≤ N := by
  rintro _ ⟨x, hx, rfl⟩
  rw [glLin_scalarGL_apply]
  exact N.smul_mem ⟨_, hc⟩ hx

lemma map_scalar_le_unifMul {N L : Submodule (intRing F) (Fin r → Kt F)} (hNL : N ≤ L)
    {c : (Kt F)ˣ} (hc : 0 < (c : Kt F).order) : N.map (glLin (scalarGL (r := r) c)) ≤ unifMul L := by
  have hcO := mem_intRing_of_order_nonneg hc.le
  obtain ⟨b, hb, hbc⟩ := exists_unif_mul_of_coeff_zero hcO (HahnSeries.coeff_eq_zero_of_lt_order hc)
  rintro _ ⟨x, hx, rfl⟩
  rw [glLin_scalarGL_apply]
  refine mem_unifMul.2 ⟨(⟨b, hb⟩ : intRing F) • x, L.smul_mem _ (hNL hx), ?_⟩
  rw [smul_smul]
  ext i
  simp [unifO, Subring.smul_def, ← hbc]

lemma order_inv_units (a : (Kt F)ˣ) : ((a⁻¹ : (Kt F)ˣ) : Kt F).order = -(a : Kt F).order := by
  have h := HahnSeries.order_mul (a⁻¹ : (Kt F)ˣ).ne_zero a.ne_zero
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, HahnSeries.order_one] at h
  omega

lemma map_scalar_map_scalar_inv (a : (Kt F)ˣ) (M : Submodule (intRing F) (Fin r → Kt F)) :
    (M.map (glLin (scalarGL (r := r) a))).map (glLin (scalarGL (r := r) a⁻¹)) = M := by
  rw [← Submodule.map_comp]
  convert Submodule.map_id M
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, glLin_apply, Matrix.mulVec_mulVec, LinearMap.id_apply,
    ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

/-- Homothetic lattices strictly between `ϖ L` and `L` (half-open) are equal. -/
lemma eq_of_homothetic_of_mem_Ioc {L M M' : Submodule (intRing F) (Fin r → Kt F)}
    (hM : unifMul L < M) (hML : M ≤ L) (hM' : unifMul L < M') (hM'L : M' ≤ L) (a : (Kt F)ˣ)
    (h : M.map (glLin (scalarGL a)) = M') : M = M' := by
  have h' : M'.map (glLin (scalarGL (r := r) a⁻¹)) = M := by
    rw [← h, map_scalar_map_scalar_inv]
  rcases lt_trichotomy (a : Kt F).order 0 with hn | hn | hn
  · have hinv : 0 < ((a⁻¹ : (Kt F)ˣ) : Kt F).order := by rw [order_inv_units]; omega
    exact absurd (h' ▸ map_scalar_le_unifMul hM'L hinv) (not_le_of_gt hM)
  · have ha := mem_intRing_of_order_nonneg hn.ge
    have hinv := mem_intRing_of_order_nonneg (a := ((a⁻¹ : (Kt F)ˣ) : Kt F))
      (by rw [order_inv_units]; omega)
    exact le_antisymm (h' ▸ map_scalar_le hinv) (h ▸ map_scalar_le ha)
  · exact absurd (h ▸ map_scalar_le_unifMul hML hn) (not_le_of_gt hM')

lemma GL_apply_mem_of_smul_stdLattice {g : GL (Fin r) (Kt F)}
    (hg : g • stdLattice F r = stdLattice F r) (i j : Fin r) :
    (g : Matrix (Fin r) (Fin r) (Kt F)) i j ∈ intRing F := by
  have hstd : (Pi.single j 1 : Fin r → Kt F) ∈ stdCarrier F r := by
    intro l
    by_cases h : l = j
    · subst h; simp
    · simp [h]
  have hmem : glLin g (Pi.single j 1) ∈ (g • stdLattice F r).carrier :=
    Submodule.mem_map_of_mem hstd
  rw [hg] at hmem
  simpa [Matrix.mulVec_single_one] using hmem i

/-- An element of `GL_r(K)` fixing the lattice `O^r` lies in `GL_r(O)`. -/
lemma exists_GLOr_of_smul_stdLattice {g : GL (Fin r) (Kt F)} (hg : g • stdLattice F r = stdLattice F r) :
    ∃ k : GL (Fin r) (PowerSeries F), GLOr F r k = g := by
  have hg' : g⁻¹ • stdLattice F r = stdLattice F r := by
    rw [inv_smul_eq_iff, hg]
  choose A hA using GL_apply_mem_of_smul_stdLattice hg
  choose B hB using GL_apply_mem_of_smul_stdLattice hg'
  let φ := (HahnSeries.ofPowerSeries ℤ F).mapMatrix (m := Fin r)
  have hinj : Function.Injective φ := Matrix.map_injective HahnSeries.ofPowerSeries_injective
  have hφA : φ (Matrix.of A) = g := Matrix.ext fun i j => hA i j
  have hφB : φ (Matrix.of B) = ((g⁻¹ : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) :=
    Matrix.ext fun i j => hB i j
  have h1 : Matrix.of A * Matrix.of B = 1 := hinj (by
    rw [map_mul, hφA, hφB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : Matrix.of B * Matrix.of A = 1 := hinj (by
    rw [map_mul, hφA, hφB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨Matrix.of A, Matrix.of B, h1, h2⟩, Units.ext ?_⟩
  exact hφA

/-- `k ∈ GL_r(O)` whose reduction preserves the standard flag lies in the Iwahori subgroup. -/
lemma mem_iwahoriR_of_forall {k : GL (Fin r) (PowerSeries F)}
    (hk : ∀ i : Fin r, (stdW (F := F) r i).map
      (Matrix.mulVecLin (redGL k : Matrix (Fin r) (Fin r) F)) = stdW r i) : k ∈ iwahoriR F r := by
  show (redGL k : Matrix (Fin r) (Fin r) F).BlockTriangular id
  intro l j hjl
  simp only [id] at hjl
  have hj : (j : ℕ) < r := j.2
  have hmem : (Pi.single j 1 : Fin r → F) ∈ stdW (F := F) r (⟨r - 1 - j, by omega⟩ : Fin r) := by
    intro m hm
    rw [Pi.single_apply, if_neg]
    rintro rfl
    simp at hm
    omega
  have := hk ⟨r - 1 - j, by omega⟩ ▸ Submodule.mem_map_of_mem
    (f := Matrix.mulVecLin (redGL k : Matrix (Fin r) (Fin r) F)) hmem
  have hl := this l (by have : (j : ℕ) < l := hjl; simp; omega)
  simpa [Matrix.mulVec_single_one] using hl

/-- Upper triangular matrices preserve the standard flag. -/
lemma map_stdW_le_of_blockTriangular {h : Matrix (Fin r) (Fin r) F} (hh : h.BlockTriangular id)
    (i : ℕ) : (stdW (F := F) r i).map (Matrix.mulVecLin h) ≤ stdW r i := by
  rintro _ ⟨v, hv, rfl⟩ l hl
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : r - i ≤ (m : ℕ)
  · rw [hv m hm, mul_zero]
  · rw [hh (show m < l by show (m : ℕ) < l; omega), zero_mul]

/-- Upper triangular matrices preserve the standard flag. -/
lemma map_stdW_of_mem_borelR {h : GL (Fin r) F} (hh : h ∈ borelR F r) (i : ℕ) :
    (stdW (F := F) r i).map (Matrix.mulVecLin (h : Matrix (Fin r) (Fin r) F)) = stdW r i := by
  refine le_antisymm (map_stdW_le_of_blockTriangular hh i) ?_
  have h2 := map_stdW_le_of_blockTriangular ((borelR F r).inv_mem hh) i
  intro v hv
  refine ⟨_, h2 ⟨v, hv, rfl⟩, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mulVec]

lemma mem_chamberStab_iff {g : GL (Fin r) (Kt F)} :
    g ∈ chamberStab F r ↔ ∃ c : (Kt F)ˣ, ∃ k ∈ iwahoriR F r, g = scalarGL c * GLOr F r k := by
  have key : ∀ (c : (Kt F)ˣ) (k : GL (Fin r) (PowerSeries F)),
      ((scalarGL c * GLOr F r k : GL (Fin r) (Kt F)) : Matrix (Fin r) (Fin r) (Kt F)) =
        (c : Kt F) • (GLOr F r k : Matrix (Fin r) (Fin r) (Kt F)) := fun c k => by
    rw [Units.val_mul, coe_scalarGL, Matrix.smul_eq_diagonal_mul]; rfl
  constructor
  · rintro ⟨c, k, hk, hg⟩
    exact ⟨c, k, hk, Units.ext (by rw [key, hg])⟩
  · rintro ⟨c, k, hk, rfl⟩
    exact ⟨c, k, hk, key c k⟩

lemma GLOr_smul_stdChain (k : GL (Fin r) (PowerSeries F)) (i : Fin r) :
    (GLOr F r k • stdChain F r i).carrier =
      latOf ((stdW (F := F) r i).map (Matrix.mulVecLin (redGL k : Matrix (Fin r) (Fin r) F))) := by
  rw [smul_carrier]; exact map_latOf_GLOr k _

lemma smul_stdChain_vtx_of_mem {g : GL (Fin r) (Kt F)} (hg : g ∈ chamberStab F r) (i : Fin r) :
    g • (stdChain F r i).vtx = (stdChain F r i).vtx := by
  obtain ⟨c, k, hk, rfl⟩ := mem_chamberStab_iff.1 hg
  rw [SemigroupAction.mul_smul, scalarGL_smul_vtx, smul_vtx]
  have : GLOr F r k • stdChain F r i = stdChain F r i := Lattice.ext (by
    rw [GLOr_smul_stdChain, map_stdW_of_mem_borelR (h := redGL k) hk]; rfl)
  rw [this]

lemma mulVecLin_GL_injective (h : GL (Fin r) F) :
    Function.Injective (Matrix.mulVecLin (h : Matrix (Fin r) (Fin r) F)) := by
  intro x y hxy
  have := congrArg (fun z => ((h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *ᵥ z) hxy
  simpa [Matrix.mulVec_mulVec] using this

lemma latOf_injective : Function.Injective (latOf (F := F) (r := r)) :=
  fun _ _ h => le_antisymm (latOf_le_latOf_iff.1 h.le) (latOf_le_latOf_iff.1 h.ge)

lemma unifMul_std_lt_latOf {W : Submodule F (Fin r → F)} (hW : ⊥ < W) :
    unifMul (stdCarrier F r) < latOf W := by
  rw [← latOf_bot]; exact latOf_strictMono hW

lemma strictMono_eq_id {σ : Fin r → Fin r} (hσ : StrictMono σ) : σ = id := by
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective hσ.injective
  exact (StrictMono.range_inj hσ strictMono_id).1 (by
    rw [hsurj.range_eq, Set.range_id])

/-- **Stabilizer.** The stabilizer of the standard pointed chamber `(C₀, v₀)` is `K^× · I`. -/
theorem PChamber'.stabilizer_std [NeZero r] :
    MulAction.stabilizer (GL (Fin r) (Kt F)) (stdPChamber' F r) = chamberStab F r := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    have hC : smulSet g (chainVerts (stdChain F r)) = chainVerts (stdChain F r) :=
      congrArg (fun p : PChamber' F r => p.1.1.verts) hg
    have hv : g • stdVertex₀ F r = stdVertex₀ F r := congrArg (fun p : PChamber' F r => p.1.2) hg
    obtain ⟨a, ha⟩ := Quotient.exact hv
    rw [← SemigroupAction.mul_smul] at ha
    obtain ⟨k, hk⟩ := exists_GLOr_of_smul_stdLattice ha
    -- `g` permutes the vertices of the standard chamber
    have hperm : ∀ i : Fin r, ∃ j : Fin r, (stdW (F := F) r j) =
        (stdW (F := F) r i).map (Matrix.mulVecLin (redGL k : Matrix (Fin r) (Fin r) F)) := by
      intro i
      have hmem : g • (stdChain F r i).vtx ∈ chainVerts (stdChain F r) := by
        rw [← hC]; exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hmem
      refine ⟨j, ?_⟩
      have hj' : (stdChain F r j).vtx = (GLOr F r k • stdChain F r i).vtx := by
        rw [hj, hk, SemigroupAction.mul_smul, ← smul_vtx, ← smul_vtx, scalarGL_smul_vtx]
      obtain ⟨b, hb⟩ := Quotient.exact hj'
      have hb' := congrArg Lattice.carrier hb
      rw [smul_carrier, GLOr_smul_stdChain] at hb'
      have hbot : ⊥ < (stdW (F := F) r i).map
          (Matrix.mulVecLin (redGL k : Matrix (Fin r) (Fin r) F)) := by
        rw [← Submodule.map_bot (Matrix.mulVecLin (redGL k : Matrix (Fin r) (Fin r) F))]
        exact Submodule.map_strictMono_of_injective (mulVecLin_GL_injective _) (bot_lt_stdW i)
      exact latOf_injective (eq_of_homothetic_of_mem_Ioc
        (unifMul_std_lt_latOf (bot_lt_stdW j)) (latOf_mem_Icc _).2
        (unifMul_std_lt_latOf hbot) (latOf_mem_Icc _).2 b hb')
    choose σ hσ using hperm
    have hσmono : StrictMono σ := by
      intro i i' hii'
      by_contra hcon
      have h1 := (stdW_strictAnti (F := F) (r := r)).antitone (not_lt.1 hcon)
      simp only at h1
      rw [hσ, hσ] at h1
      exact (Submodule.map_strictMono_of_injective (mulVecLin_GL_injective _)
        (stdW_strictAnti hii')).not_ge h1
    have hσid := strictMono_eq_id hσmono
    have hkI : k ∈ iwahoriR F r := mem_iwahoriR_of_forall fun i => by
      have := hσ i; rw [hσid] at this; exact this.symm
    refine mem_chamberStab_iff.2 ⟨a⁻¹, k, hkI, ?_⟩
    rw [hk, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  · intro hg
    apply Subtype.ext
    refine Prod.ext (Chamber.ext ?_) ?_
    · show smulSet g (chainVerts (stdChain F r)) = chainVerts (stdChain F r)
      simp only [smulSet, chainVerts, Finset.image_image, Function.comp_def,
        smul_stdChain_vtx_of_mem hg]
    · show g • stdVertex₀ F r = stdVertex₀ F r
      have := smul_stdChain_vtx_of_mem hg 0
      rwa [stdChain_zero] at this

/-! ### Transitivity of the action on pointed chambers -/

/-- **Transitivity.** `GL_r(K)` acts transitively on pointed chambers `(C, v)`. -/
theorem PChamber'.exists_smul_eq [NeZero r] (p : PChamber' F r) :
    ∃ g : GL (Fin r) (Kt F), g • stdPChamber' F r = p := by
  obtain ⟨⟨C, v⟩, hv⟩ := p
  obtain ⟨M, hM, hC⟩ := C.exists_chain
  -- `v = [M j]` for some `j`
  have hv' : v ∈ chainVerts M := hC ▸ hv
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv'
  -- rotate the chain so that it starts at `M j`
  obtain ⟨M', hM', hverts, hr, hM'0⟩ := hM.exists_rotate j
  have h0eq : (⟨0, hr⟩ : Fin r) = 0 := Fin.ext (by simp)
  rw [h0eq] at hM'0
  -- step 1: `g₀ O^r = M' 0`; translate the chain by `g₀⁻¹`, so that it starts at `O^r`
  obtain ⟨g0, hg0⟩ := exists_smul_stdLattice (M' 0)
  let N : Fin r → Lattice F r := fun i => g0⁻¹ • M' i
  have hN : IsCompleteChain N := hM'.smul g0⁻¹
  have hN0 : N 0 = stdLattice F r := by
    simp only [N]; rw [← hg0, inv_smul_smul]
  -- step 2: the chain lies between `ϖ O^r` and `O^r`, so it is a complete flag in `F^r`
  have hmem : ∀ i, (N i).carrier ∈ Set.Icc (unifMul (stdCarrier F r)) (stdCarrier F r) :=
    fun i => ⟨by have := (hN.2 0 i).le; rwa [hN0] at this,
      by have := hN.1.antitone (Fin.zero_le i); rwa [hN0] at this⟩
  choose W hW using fun i => exists_eq_latOf (hmem i)
  have hWanti : StrictAnti W := fun i i' h =>
    latOf_lt_latOf_iff.1 (show latOf (W i') < latOf (W i) by rw [hW, hW]; exact hN.1 h)
  have hW0 : W 0 = ⊤ := latOf_injective (by rw [hW, hN0, latOf_top]; rfl)
  have hWbot : ∀ i, ⊥ < W i := fun i =>
    latOf_lt_latOf_iff.1 (show latOf ⊥ < latOf (W i) by rw [hW, latOf_bot]; have := hN.2 0 i; rwa [hN0] at this)
  -- step 3: `h ∈ GL_r(F) ⊆ GL_r(O)` moves the standard flag to this flag
  obtain ⟨h, hh⟩ := exists_GL_flag W hWanti hW0 hWbot
  let H := GLOr F r (constGL h)
  have hHN : ∀ i, H • stdChain F r i = N i := fun i => Lattice.ext (by
    rw [GLOr_smul_stdChain, redGL_constGL, hh, hW])
  -- `g = g₀ h` moves `(C₀, v₀)` to `(C, v)`
  refine ⟨g0 * H, Subtype.ext (Prod.ext (Chamber.ext ?_) ?_)⟩
  · show smulSet (g0 * H) (chainVerts (stdChain F r)) = C.verts
    rw [hC, ← hverts, smulSet_chainVerts]
    congr 1
    funext i
    rw [SemigroupAction.mul_smul, hHN]
    simp only [N, smul_inv_smul]
  · show (g0 * H) • stdVertex₀ F r = (M j).vtx
    rw [stdVertex₀, smul_vtx, SemigroupAction.mul_smul, ← stdChain_zero, hHN, ← hM'0]
    simp only [N, smul_inv_smul]

/-! ### The canonical bijection with `GL_r(K) / (K^× · I)` -/

/-- **Orbit–stabilizer.** The map `GL_r(K)/(K^× · I) → PChamber' F r`, `[g] ↦ g • (C₀, v₀)`. -/
def PChamber.toPChamber' [NeZero r] : PChamber F r → PChamber' F r :=
  Quotient.lift (fun g => g • stdPChamber' F r) (fun g h hgh => by
    have hgh : g⁻¹ * h ∈ chamberStab F r := QuotientGroup.leftRel_apply.mp hgh
    rw [← PChamber'.stabilizer_std, MulAction.mem_stabilizer_iff, SemigroupAction.mul_smul] at hgh
    calc g • stdPChamber' F r = g • (g⁻¹ • h • stdPChamber' F r) := by rw [hgh]
      _ = h • stdPChamber' F r := smul_inv_smul g _)

@[simp] lemma PChamber.toPChamber'_mk [NeZero r] (g : GL (Fin r) (Kt F)) :
    PChamber.toPChamber' (QuotientGroup.mk g : PChamber F r) = g • stdPChamber' F r := rfl

lemma PChamber.toPChamber'_smul [NeZero r] (g : GL (Fin r) (Kt F)) (c : PChamber F r) :
    PChamber.toPChamber' (g • c) = g • PChamber.toPChamber' c := by
  induction c using QuotientGroup.induction_on with
  | H h => exact SemigroupAction.mul_smul g h _

lemma PChamber.toPChamber'_bijective [NeZero r] :
    Function.Bijective (PChamber.toPChamber' (F := F) (r := r)) := by
  refine ⟨fun c d hcd => ?_, fun p => ?_⟩
  · induction c using QuotientGroup.induction_on with
    | H g =>
    induction d using QuotientGroup.induction_on with
    | H h =>
    apply QuotientGroup.eq.2
    rw [← PChamber'.stabilizer_std, MulAction.mem_stabilizer_iff, SemigroupAction.mul_smul]
    simp only [toPChamber'_mk] at hcd
    rw [← hcd, inv_smul_smul]
  · obtain ⟨g, hg⟩ := PChamber'.exists_smul_eq p
    exact ⟨QuotientGroup.mk g, hg⟩

/-- The canonical `GL_r(K)`-equivariant bijection `GL_r(K)/(K^× · I) ≃ PChamber' F r`. -/
def pchamberEquiv [NeZero r] : PChamber F r ≃ PChamber' F r :=
  Equiv.ofBijective _ PChamber.toPChamber'_bijective

@[simp] lemma pchamberEquiv_mk [NeZero r] (g : GL (Fin r) (Kt F)) :
    pchamberEquiv (QuotientGroup.mk g : PChamber F r) = g • stdPChamber' F r := rfl

/-- The bijection `pchamberEquiv` is `GL_r(K)`-equivariant. -/
lemma pchamberEquiv_smul [NeZero r] (g : GL (Fin r) (Kt F)) (c : PChamber F r) :
    pchamberEquiv (g • c) = g • pchamberEquiv c :=
  PChamber.toPChamber'_smul g c

end GLrBuilding
