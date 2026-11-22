module

public import Mathlib

/-!
# Complete flags in `F^r` are conjugate under `GL_r(F)`

* `stdW r i = span(e_j : j < r - i) ⊆ F^r`, the standard flag
  `F^r = stdW r 0 ⊋ stdW r 1 ⊋ ⋯ ⊋ stdW r (r-1) ⊋ 0`.
* `exists_GL_flag` : every complete flag `F^r = W 0 ⊋ W 1 ⊋ ⋯ ⊋ W (r-1) ⊋ 0` is the image of the
  standard flag under some `h ∈ GL_r(F)` (existence of a basis adapted to the flag).
-/

public section

open Module

namespace GLrBuilding

variable {F : Type*} [Field F] {r : ℕ}

variable (r) in
/-- The standard flag: `stdW r i = span(e_j : j < r - i) ⊆ F^r`. -/
def stdW (i : ℕ) : Submodule F (Fin r → F) where
  carrier := {v | ∀ j : Fin r, r - i ≤ j.val → v j = 0}
  add_mem' hv hw j hj := by simp [hv j hj, hw j hj]
  zero_mem' _ _ := rfl
  smul_mem' c _ hv j hj := by simp [hv j hj]

lemma stdW_eq_span (i : ℕ) :
    stdW (F := F) r i = Submodule.span F
      ((fun l : Fin r => (Pi.single l (1 : F) : Fin r → F)) '' {l : Fin r | (l : ℕ) < r - i}) := by
  apply le_antisymm
  · intro v hv
    have hv' : v = ∑ l, v l • (Pi.single l (1 : F) : Fin r → F) := by
      ext j; simp [Pi.single_apply]
    rw [hv']
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l : ℕ) < r - i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hl, rfl⟩)
    · rw [hv l (by omega), zero_smul]; exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩ j hj
    show (Pi.single l (1 : F) : Fin r → F) j = 0
    rw [Pi.single_apply, if_neg]
    rintro rfl
    simp at hl
    omega

lemma finrank_sup_span_singleton {W : Submodule F (Fin r → F)} {v : Fin r → F} (hv : v ∉ W) :
    finrank F ↥(W ⊔ F ∙ v) = finrank F W + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ W.zero_mem)
  have hinf : W ⊓ (F ∙ v) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxv⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxv
    rw [Submodule.mem_bot]
    by_contra hc
    have hc' : c ≠ 0 := fun h => hc (by simp [h])
    exact hv (by simpa [smul_smul, inv_mul_cancel₀ hc'] using W.smul_mem c⁻¹ hxW)
  have := Submodule.finrank_sup_add_finrank_inf_eq W (F ∙ v)
  rw [hinf, finrank_bot, finrank_span_singleton hv0] at this
  omega

/-- A strictly decreasing sequence of `r + 1` naturals from `r` takes the values `r, r-1, …`. -/
lemma eq_sub_of_strictAnti {f : ℕ → ℕ} (hf : ∀ n < r, f (n + 1) < f n) (h0 : f 0 = r) :
    ∀ n ≤ r, f n = r - n := by
  have hup : ∀ n ≤ r, f n + n ≤ r := by
    intro n
    induction n with
    | zero => intro _; omega
    | succ n ih => intro hn; have := hf n (by omega); have := ih (by omega); omega
  have hlow : ∀ m ≤ r, m ≤ f (r - m) := by
    intro m
    induction m with
    | zero => intro _; omega
    | succ m ih =>
      intro hm
      have h1 := hf (r - (m + 1)) (by omega)
      rw [show r - (m + 1) + 1 = r - m by omega] at h1
      have := ih (by omega); omega
  intro n hn
  have := hup n hn
  have := hlow (r - n) (by omega)
  rw [show r - (r - n) = n by omega] at this
  omega

/-- **Complete flags are conjugate.**  A complete flag `F^r = W 0 ⊋ W 1 ⊋ ⋯ ⊋ W (r-1) ⊋ 0` is
the image of the standard flag under some `h ∈ GL_r(F)`. -/
theorem exists_GL_flag [NeZero r] (W : Fin r → Submodule F (Fin r → F)) (hW : StrictAnti W)
    (h0 : W 0 = ⊤) (hbot : ∀ i, ⊥ < W i) :
    ∃ h : GL (Fin r) F, ∀ i : Fin r,
      (stdW r (i : ℕ)).map (Matrix.mulVecLin (h : Matrix (Fin r) (Fin r) F)) = W i := by
  let Wx : ℕ → Submodule F (Fin r → F) := fun n => if hn : n < r then W ⟨n, hn⟩ else ⊥
  have hWx : ∀ n < r, Wx (n + 1) < Wx n := by
    intro n hn
    by_cases hn1 : n + 1 < r
    · simp only [Wx, dif_pos hn, dif_pos hn1]; exact hW (Fin.mk_lt_mk.2 (Nat.lt_succ_self n))
    · simp only [Wx, dif_pos hn, dif_neg hn1]; exact hbot _
  have hWx0 : Wx 0 = ⊤ := by simp only [Wx, dif_pos (NeZero.pos r)]; exact h0
  have hWxr : Wx r = ⊥ := by simp [Wx]
  have hWxi : ∀ i : Fin r, Wx i = W i := fun i => by simp [Wx]
  have hdim : ∀ n ≤ r, finrank F (Wx n) = r - n :=
    eq_sub_of_strictAnti (f := fun n => finrank F (Wx n))
      (fun n hn => Submodule.finrank_lt_finrank_of_lt (hWx n hn))
      (by show finrank F (Wx 0) = r; rw [hWx0, finrank_top, finrank_fin_fun])
  have hex : ∀ m : Fin r, ∃ v, v ∈ Wx (r - (m + 1)) ∧ v ∉ Wx (r - m) := by
    intro m
    have := hWx (r - (m + 1)) (by omega)
    rw [show r - (m + 1) + 1 = r - m by omega] at this
    obtain ⟨v, hv, hv'⟩ := SetLike.exists_of_lt this
    exact ⟨v, hv, hv'⟩
  choose v hv hv' using hex
  have hspan : ∀ m ≤ r, Submodule.span F (v '' {l : Fin r | (l : ℕ) < m}) = Wx (r - m) := by
    intro m
    induction m with
    | zero => intro _; simp [hWxr]
    | succ m ih =>
      intro hm
      have hset : {l : Fin r | (l : ℕ) < m + 1} =
          insert ⟨m, by omega⟩ {l : Fin r | (l : ℕ) < m} := by
        ext l; simp [Fin.ext_iff]; omega
      rw [hset, Set.image_insert_eq, Submodule.span_insert, ih (by omega), sup_comm]
      have hvm := hv ⟨m, by omega⟩
      have hvm' := hv' ⟨m, by omega⟩
      simp only at hvm hvm'
      have hle1 : Wx (r - m) ≤ Wx (r - (m + 1)) := by
        have := (hWx (r - (m + 1)) (by omega)).le
        rwa [show r - (m + 1) + 1 = r - m by omega] at this
      have hle : Wx (r - m) ⊔ F ∙ v ⟨m, by omega⟩ ≤ Wx (r - (m + 1)) :=
        sup_le hle1 ((Submodule.span_singleton_le_iff_mem _ _).2 hvm)
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [finrank_sup_span_singleton hvm', hdim _ (by omega), hdim _ (by omega)]
      omega
  have hall : Submodule.span F (Set.range v) = ⊤ := by
    have := hspan r le_rfl
    rw [Nat.sub_self, hWx0] at this
    rw [← this, ← Set.image_univ]
    congr 2
    ext l; simp
  have hli : LinearIndependent F v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hall.ge (by simp)
  let A : Matrix (Fin r) (Fin r) F := Matrix.of fun a l => v l a
  have hAcol : A.col = v := rfl
  have hU : IsUnit A := Matrix.linearIndependent_cols_iff_isUnit.1 (hAcol ▸ hli)
  refine ⟨hU.unit, fun i => ?_⟩
  rw [IsUnit.unit_spec, stdW_eq_span, Submodule.map_span, Set.image_image]
  have : (fun l : Fin r => A.mulVecLin (Pi.single l 1)) = v := by
    funext l; rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]; rfl
  rw [this, hspan _ (by omega), show r - (r - (i : ℕ)) = i by omega, hWxi]

end GLrBuilding
