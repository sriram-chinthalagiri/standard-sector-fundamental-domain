import GLrFundamentalDomain.Cosets
import GLrFundamentalDomain.FlagRefinement

/-!
# Simplices through a vertex and flags in `L₀ / ϖ L₀`

Let `O = F[[1/t]]`, `ϖ = 1/t` and let `L₀` be an `O`-lattice in `K^r`.

* `Red L₀ = L₀ / ϖ L₀`.  It is an `O`-module killed by `ϖ`, hence an `F`-vector space
  (through the constants `F ⊆ O`), and its `O`-submodules are exactly its `F`-subspaces
  (`oSubmoduleEquivSubspace`).
* **(1) Correspondence.**  `iccEquivSubspace L₀` : the `O`-submodules `M` with `ϖ L₀ ⊆ M ⊆ L₀`
  are in order-preserving bijection with the `F`-subspaces of `L₀ / ϖ L₀`
  (`M ↦ M / ϖ L₀`); all such `M` are lattices (`isLattice_of_mem_Icc`).  Thus a chain
  `L₀ ⊋ L₁ ⊋ ⋯ ⊋ L_d ⊋ ϖ L₀` (a simplex through `[L₀]`) is the same as a flag of
  `F`-subspaces `L₀/ϖL₀ ⊋ L₁/ϖL₀ ⊋ ⋯ ⊋ L_d/ϖL₀ ⊋ 0`.
* **(2) Refinement** is `exists_maximal_flag_refinement` (`FlagRefinement.lean`).
* `finrank_red` : `dim_F (L₀ / ϖ L₀) = r`.

These are the inputs of `exists_pchamber_superset` (every simplex is a face of a chamber),
which is proved in `PointedChambers.lean`.
-/

open Matrix Module

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GLrBuilding

open Classical

variable {F : Type*} [Field F] {r : ℕ}

/-! Shortcut instances (instance search through `intRing F` is otherwise very slow). -/

instance instModuleIntRingVec : Module (intRing F) (Fin r → Kt F) := inferInstance

instance instModuleIntRingSub (L : Submodule (intRing F) (Fin r → Kt F)) :
    Module (intRing F) L := L.module

/-! ### Multiplication by `ϖ` -/

lemma unif_mem_intRing : unif F ∈ intRing F :=
  ⟨PowerSeries.X, by simp [unif, HahnSeries.ofPowerSeries_X]⟩

variable (F) in
/-- `ϖ` as an element of `O`. -/
def unifO : intRing F := ⟨unif F, unif_mem_intRing⟩

/-- `ϖ M`, the image of `M` under the scalar matrix `ϖ · 1`. -/
def unifMul (M : Submodule (intRing F) (Fin r → Kt F)) : Submodule (intRing F) (Fin r → Kt F) :=
  M.map (glLin (scalarGL (r := r) (unifUnit (F := F))))

lemma glLin_unif_apply (x : Fin r → Kt F) :
    glLin (scalarGL (r := r) (unifUnit (F := F))) x = unifO F • x := by
  ext i
  simp [unifUnit, unifO, Subring.smul_def, Matrix.mulVec, dotProduct, Matrix.scalar_apply,
    Matrix.diagonal, Finset.sum_ite_eq]

lemma Lattice.smul_unif_carrier (L : Lattice F r) :
    (scalarGL (r := r) (unifUnit (F := F)) • L).carrier = unifMul L.carrier := rfl

lemma mem_unifMul {M : Submodule (intRing F) (Fin r → Kt F)} {x : Fin r → Kt F} :
    x ∈ unifMul M ↔ ∃ y ∈ M, unifO F • y = x := by
  simp only [unifMul, Submodule.mem_map, glLin_unif_apply]

lemma unifMul_le (M : Submodule (intRing F) (Fin r → Kt F)) : unifMul M ≤ M := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_unifMul.1 hx
  exact M.smul_mem _ hy

/-! ### The reduction `L₀ / ϖ L₀` and its `F`-structure -/

/-- `ϖ L₀` as a submodule of `L₀`. -/
def redSub (L : Submodule (intRing F) (Fin r → Kt F)) : Submodule (intRing F) L :=
  (unifMul L).comap L.subtype

/-- The reduction `L₀ / ϖ L₀` (a type synonym for the quotient module). -/
def Red (L : Submodule (intRing F) (Fin r → Kt F)) := L ⧸ redSub L

instance (L : Submodule (intRing F) (Fin r → Kt F)) : AddCommGroup (Red L) :=
  inferInstanceAs (AddCommGroup (L ⧸ redSub L))

instance (L : Submodule (intRing F) (Fin r → Kt F)) : Module (intRing F) (Red L) :=
  inferInstanceAs (Module (intRing F) (L ⧸ redSub L))

/-- The reduction map `L₀ → L₀ / ϖ L₀`. -/
def redMk (L : Submodule (intRing F) (Fin r → Kt F)) : L →ₗ[intRing F] Red L := (redSub L).mkQ

lemma redMk_surjective (L : Submodule (intRing F) (Fin r → Kt F)) :
    Function.Surjective (redMk L) := Submodule.mkQ_surjective _

lemma ker_redMk (L : Submodule (intRing F) (Fin r → Kt F)) :
    LinearMap.ker (redMk L) = redSub L := Submodule.ker_mkQ _

lemma redMk_eq_zero {L : Submodule (intRing F) (Fin r → Kt F)} {y : L} :
    redMk L y = 0 ↔ (y : Fin r → Kt F) ∈ unifMul L := by
  rw [← LinearMap.mem_ker, ker_redMk]; rfl

variable (F) in
/-- The constants `F → O`. -/
def constO : F →+* intRing F :=
  (HahnSeries.ofPowerSeries ℤ F).rangeRestrict.comp PowerSeries.C

/-- `L₀ / ϖ L₀` is an `F`-vector space through the constants `F ⊆ O`. -/
instance (L : Submodule (intRing F) (Fin r → Kt F)) : Module F (Red L) :=
  Module.compHom _ (constO F)

lemma const_smul_red {L : Submodule (intRing F) (Fin r → Kt F)} (c : F) (x : Red L) :
    c • x = constO F c • x := rfl

lemma unifO_smul_red {L : Submodule (intRing F) (Fin r → Kt F)} (x : Red L) :
    unifO F • x = 0 := by
  obtain ⟨y, rfl⟩ := redMk_surjective L x
  rw [← map_smul, redMk_eq_zero]
  exact mem_unifMul.2 ⟨y, y.2, rfl⟩

lemma intRing_decomp (p : PowerSeries F) :
    (⟨HahnSeries.ofPowerSeries ℤ F p, ⟨p, rfl⟩⟩ : intRing F) =
      unifO F * ⟨HahnSeries.ofPowerSeries ℤ F
        (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) p), ⟨_, rfl⟩⟩ +
      constO F (PowerSeries.constantCoeff p) := by
  apply Subtype.ext
  have h1 : ((constO F (PowerSeries.constantCoeff p) : intRing F) : Kt F) =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (PowerSeries.constantCoeff p)) := rfl
  have h2 : ((unifO F : intRing F) : Kt F) = HahnSeries.ofPowerSeries ℤ F PowerSeries.X := by
    rw [HahnSeries.ofPowerSeries_X]; rfl
  rw [Subring.coe_add, Subring.coe_mul, h1, h2, ← map_mul, ← map_add,
    ← PowerSeries.eq_X_mul_shift_add_const p]

/-- Every element `o ∈ O` acts on `L₀/ϖL₀` as a constant `c ∈ F` (its constant term). -/
lemma exists_smul_red_eq_const (o : intRing F) :
    ∃ c : F, ∀ {L : Submodule (intRing F) (Fin r → Kt F)} (x : Red L), o • x = c • x := by
  obtain ⟨p, hp⟩ := o.2
  have ho : o = ⟨HahnSeries.ofPowerSeries ℤ F p, ⟨p, rfl⟩⟩ := Subtype.ext hp.symm
  refine ⟨PowerSeries.constantCoeff p, fun x => ?_⟩
  rw [ho, intRing_decomp, add_smul, mul_comm]
  have h0 : ∀ a : intRing F, (a * unifO F) • x = 0 := fun a => by
    rw [SemigroupAction.mul_smul, unifO_smul_red, smul_zero]
  rw [h0, zero_add, const_smul_red]

/-- The `O`-submodules of `L₀/ϖL₀` are exactly its `F`-subspaces. -/
def oSubmoduleEquivSubspace (L : Submodule (intRing F) (Fin r → Kt F)) :
    Submodule (intRing F) (Red L) ≃o Submodule F (Red L) where
  toFun P :=
    { carrier := P
      add_mem' := P.add_mem
      zero_mem' := P.zero_mem
      smul_mem' := fun c _ hx => P.smul_mem (constO F c) hx }
  invFun W :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun o x hx => by
        obtain ⟨c, hc⟩ := exists_smul_red_eq_const (r := r) o
        rw [hc]
        exact W.smul_mem _ hx }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp] lemma mem_oSubmoduleEquivSubspace {L : Submodule (intRing F) (Fin r → Kt F)}
    (P : Submodule (intRing F) (Red L)) (x : Red L) :
    x ∈ oSubmoduleEquivSubspace L P ↔ x ∈ P := Iff.rfl

/-! ### (1) Lattices between `ϖ L₀` and `L₀` ↔ subspaces of `L₀/ϖL₀` -/

/-- `M ↦ M / ϖ L₀`. -/
def toRed (L M : Submodule (intRing F) (Fin r → Kt F)) : Submodule (intRing F) (Red L) :=
  (M.comap L.subtype).map (redMk L)

/-- The preimage in `L₀` of a submodule of `L₀ / ϖ L₀`. -/
def ofRed (L : Submodule (intRing F) (Fin r → Kt F)) (P : Submodule (intRing F) (Red L)) :
    Submodule (intRing F) (Fin r → Kt F) :=
  (P.comap (redMk L)).map L.subtype

lemma ofRed_mem_Icc (L : Submodule (intRing F) (Fin r → Kt F))
    (P : Submodule (intRing F) (Red L)) : ofRed L P ∈ Set.Icc (unifMul L) L := by
  constructor
  · intro x hx
    refine ⟨⟨x, unifMul_le L hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap,
      (redMk_eq_zero (y := ⟨x, unifMul_le L hx⟩)).2 hx]
    exact P.zero_mem
  · rintro _ ⟨y, _, rfl⟩
    exact y.2

lemma ofRed_toRed {L M : Submodule (intRing F) (Fin r → Kt F)}
    (hM : M ∈ Set.Icc (unifMul L) L) : ofRed L (toRed L M) = M := by
  unfold ofRed toRed
  rw [Submodule.comap_map_eq, ker_redMk, sup_eq_left.2, Submodule.map_comap_subtype,
    inf_eq_right.2 hM.2]
  intro x hx
  exact hM.1 hx

lemma toRed_ofRed (L : Submodule (intRing F) (Fin r → Kt F))
    (P : Submodule (intRing F) (Red L)) : toRed L (ofRed L P) = P := by
  unfold ofRed toRed
  rw [Submodule.comap_map_eq_of_injective (Submodule.injective_subtype L),
    Submodule.map_comap_eq_of_surjective (redMk_surjective L)]

/-- The `O`-submodules `M` with `ϖ L₀ ⊆ M ⊆ L₀` correspond to the `O`-submodules of `L₀/ϖL₀`,
via `M ↦ M / ϖ L₀`. -/
def iccEquivOSubmodule (L : Submodule (intRing F) (Fin r → Kt F)) :
    Set.Icc (unifMul L) L ≃o Submodule (intRing F) (Red L) :=
  Equiv.toOrderIso
    { toFun := fun M => toRed L M
      invFun := fun P => ⟨ofRed L P, ofRed_mem_Icc L P⟩
      left_inv := fun M => Subtype.ext (ofRed_toRed M.2)
      right_inv := fun P => toRed_ofRed L P }
    (fun _ _ h => Submodule.map_mono (Submodule.comap_mono h))
    (fun _ _ h => Submodule.map_mono (Submodule.comap_mono h))

/-- **(1)** The `O`-submodules `M` with `ϖ L₀ ⊆ M ⊆ L₀` are in order-preserving bijection with
the `F`-subspaces of `L₀/ϖL₀`, via `M ↦ M / ϖ L₀`. -/
def iccEquivSubspace (L : Submodule (intRing F) (Fin r → Kt F)) :
    Set.Icc (unifMul L) L ≃o Submodule F (Red L) :=
  (iccEquivOSubmodule L).trans (oSubmoduleEquivSubspace L)

lemma iccEquivSubspace_symm_bot (L : Submodule (intRing F) (Fin r → Kt F)) :
    ((iccEquivSubspace L).symm ⊥ : Submodule (intRing F) (Fin r → Kt F)) = unifMul L := by
  show ofRed L ((oSubmoduleEquivSubspace L).symm ⊥) = _
  rw [OrderIso.map_bot]
  unfold ofRed
  rw [Submodule.comap_bot, ker_redMk, redSub, Submodule.map_comap_subtype,
    inf_eq_right.2 (unifMul_le L)]

lemma iccEquivSubspace_symm_top (L : Submodule (intRing F) (Fin r → Kt F)) :
    ((iccEquivSubspace L).symm ⊤ : Submodule (intRing F) (Fin r → Kt F)) = L := by
  show ofRed L ((oSubmoduleEquivSubspace L).symm ⊤) = _
  rw [OrderIso.map_top]
  unfold ofRed
  rw [Submodule.comap_top, Submodule.map_subtype_top]

instance : IsNoetherianRing (intRing F) :=
  isNoetherianRing_of_ringEquiv (PowerSeries F)
    (RingEquiv.ofBijective (HahnSeries.ofPowerSeries ℤ F).rangeRestrict
      ⟨fun _ _ h => HahnSeries.ofPowerSeries_injective (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩)

/-- Every `O`-submodule between `ϖ L₀` and `L₀` is a lattice. -/
lemma isLattice_of_mem_Icc {L M : Submodule (intRing F) (Fin r → Kt F)} (hL : IsLattice F r L)
    (hM : M ∈ Set.Icc (unifMul L) L) : IsLattice F r M := by
  haveI : IsNoetherian (intRing F) L := isNoetherian_of_fg_of_noetherian L hL.1
  refine ⟨?_, ?_⟩
  · have hfg : (M.comap L.subtype).FG := IsNoetherian.noetherian _
    have := hfg.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hM.2] at this
  · have h := (IsLattice.map (scalarGL (r := r) (unifUnit (F := F))) hL).2
    rw [eq_top_iff, ← h]
    exact Submodule.span_mono hM.1

/-! ### `dim_F (L₀ / ϖ L₀) = r` -/

lemma exists_unif_pow_mul_mem (x : Kt F) : ∃ N : ℕ, unif F ^ N * x ∈ intRing F := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ((-x.order).toNat : ℤ) = m + (-x.order) :=
    ⟨((-x.order).toNat + x.order).toNat, by omega⟩
  refine ⟨(-x.order).toNat, PowerSeries.X ^ m * x.powerSeriesPart, ?_⟩
  rw [map_mul, LaurentSeries.ofPowerSeries_powerSeriesPart, HahnSeries.ofPowerSeries_X_pow,
    ← mul_assoc, HahnSeries.single_mul_single, one_mul, ← hm]
  simp [unif, HahnSeries.single_pow]

lemma constO_eq_unifO_mul {c : F} {o : intRing F} (h : constO F c = unifO F * o) : c = 0 := by
  obtain ⟨p, hp⟩ := o.2
  have h' := congrArg Subtype.val h
  have h1 : ((constO F c : intRing F) : Kt F) = HahnSeries.ofPowerSeries ℤ F (PowerSeries.C c) := rfl
  have h2 : ((unifO F : intRing F) : Kt F) = HahnSeries.ofPowerSeries ℤ F PowerSeries.X := by
    rw [HahnSeries.ofPowerSeries_X]; rfl
  rw [h1, Subring.coe_mul, h2, ← hp, ← map_mul] at h'
  have := congrArg PowerSeries.constantCoeff (HahnSeries.ofPowerSeries_injective h')
  simpa using this

instance : IsPrincipalIdealRing (intRing F) :=
  IsPrincipalIdealRing.of_surjective (HahnSeries.ofPowerSeries ℤ F).rangeRestrict
    (RingHom.rangeRestrict_surjective _)

lemma isTorsionFree_sub (M : Submodule (intRing F) (Fin r → Kt F)) :
    Module.IsTorsionFree (intRing F) M := by
  refine ⟨fun o ho x y hxy => ?_⟩
  have hne : (o : Kt F) ≠ 0 := fun h0 => ho.ne_zero (Subtype.ext h0)
  apply Subtype.ext
  have := congrArg (Subtype.val : M → Fin r → Kt F) hxy
  simp only [Submodule.coe_smul, Subring.smul_def] at this
  exact smul_right_injective _ hne this

set_option maxHeartbeats 1000000 in
/-- A basis of the lattice `L` over `O` is a basis of `K^r` over `K`: it spans and is linearly
independent over `K`. -/
lemma span_linearIndependent_basis_lattice (L : Lattice F r) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (intRing F) L.carrier) :
    ⊤ ≤ Submodule.span (Kt F) (Set.range fun i => (b i : Fin r → Kt F)) ∧
      LinearIndependent (Kt F) (fun i => (b i : Fin r → Kt F)) := by
  classical
  let w : ι → Fin r → Kt F := fun i => (b i : Fin r → Kt F)
  have hspan : ⊤ ≤ Submodule.span (Kt F) (Set.range w) := by
    rw [← L.isLattice.2]
    refine Submodule.span_le.2 fun y hy => ?_
    have h2 := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def] at h2
    rw [SetLike.mem_coe, ← h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (Kt F) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose N hN using fun j => exists_unif_pow_mul_mem (g j)
    let N0 := Finset.univ.sup N
    have hmem : ∀ j, unif F ^ N0 * g j ∈ intRing F := fun j => by
      have hle : N j ≤ N0 := Finset.le_sup (Finset.mem_univ j)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
      exact (intRing F).mul_mem ((intRing F).pow_mem unif_mem_intRing _) (hN j)
    obtain ⟨o, hodef⟩ : ∃ o : ι → intRing F, ∀ j, (o j : Kt F) = unif F ^ N0 * g j :=
      ⟨fun j => ⟨_, hmem j⟩, fun j => rfl⟩
    have ho : ∑ j, (o j • b j : L.carrier) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def, Submodule.coe_zero, hodef]
      simp only [← smul_smul, ← Finset.smul_sum]
      rw [hg, smul_zero]
    have := Fintype.linearIndependent_iff.1 b.linearIndependent o ho i
    have h0 : unif F ^ N0 * g i = 0 := by rw [← hodef, this]; rfl
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ (unif_ne_zero F))
  exact ⟨hspan, hli⟩

/-- A basis of the lattice `L` over `O` is a basis of `K^r` over `K`; hence it has `r`
elements. -/
lemma card_basis_lattice (L : Lattice F r) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (intRing F) L.carrier) : Fintype.card ι = r := by
  obtain ⟨hspan, hli⟩ := span_linearIndependent_basis_lattice L b
  have := Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)
  rw [Module.finrank_fin_fun] at this
  exact this.symm

set_option maxHeartbeats 1000000 in
/-- `dim_F (L₀ / ϖ L₀) = r` for every lattice `L₀`. -/
lemma finrank_red (L : Lattice F r) : FiniteDimensional F (Red L.carrier) ∧
    finrank F (Red L.carrier) = r := by
  set M := L.carrier with hMdef
  haveI : Module.Finite (intRing F) M := Module.Finite.iff_fg.2 L.isLattice.1
  haveI : Module.IsTorsionFree (intRing F) M := isTorsionFree_sub M
  haveI : Module.Free (intRing F) M := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis (intRing F) M
  let v : Module.Free.ChooseBasisIndex (intRing F) M → Red M := fun i => redMk M (b i)
  have hli : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hsum : ∑ j, c j • v j = redMk M (∑ j, (constO F (c j) • b j : M)) := by
      rw [map_sum]; simp only [map_smul]; rfl
    rw [hsum, redMk_eq_zero] at hc
    obtain ⟨z, hz, hzeq⟩ := mem_unifMul.1 hc
    have hM : (∑ j, (constO F (c j) • b j : M)) = (unifO F • (⟨z, hz⟩ : M) : M) :=
      Subtype.ext (by rw [Submodule.coe_smul]; exact hzeq.symm)
    have h1 : b.repr (∑ j, (constO F (c j) • b j : M)) i = constO F (c i) := by
      simp [Finsupp.single_apply]
    have h2 : b.repr (unifO F • (⟨z, hz⟩ : M)) i = unifO F * b.repr ⟨z, hz⟩ i := by
      rw [map_smul]; rfl
    have key : constO F (c i) = unifO F * b.repr ⟨z, hz⟩ i := by rw [← h1, hM, h2]
    exact constO_eq_unifO_mul key
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    rintro x -
    obtain ⟨y, rfl⟩ := redMk_surjective M x
    rw [← b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    obtain ⟨c, hc⟩ := exists_smul_red_eq_const (r := r) (b.repr y i)
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bF := Module.Basis.mk hli hsp
  exact ⟨Module.Basis.finiteDimensional_of_finite bF,
    (Module.finrank_eq_card_basis bF).trans (card_basis_lattice L b)⟩

end GLrBuilding
