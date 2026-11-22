module

public import Mathlib

/-!
# Refining flags of subspaces to maximal flags

Let `V` be a finite-dimensional vector space over a field `k` (for instance `k = 𝔽_q` and
`V = 𝔽_q^r`).  A *flag* of subspaces is a chain of subspaces (any two are comparable).

* `IsMaxChain.exists_mem_finrank_eq` : a maximal chain of subspaces contains a subspace of every
  dimension `0, 1, …, dim V`.
* `exists_maximal_flag_refinement` : every flag of subspaces of `V` can be refined to a maximal
  flag `0 = V₀ ⊊ V₁ ⊊ ⋯ ⊊ V_n = V` (`n = dim V`), i.e. one with `dim Vᵢ = i`, so that consecutive
  members differ by exactly one dimension.
-/

public section

namespace GLrBuilding

open Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Two comparable subspaces of the same dimension are equal. -/
lemma Submodule.eq_of_comparable_of_finrank_eq {X Y : Submodule k V} (h : X ≤ Y ∨ Y ≤ X)
    (hd : finrank k X = finrank k Y) : X = Y := by
  rcases h with h | h
  · exact Submodule.eq_of_le_of_finrank_eq h hd
  · exact (Submodule.eq_of_le_of_finrank_eq h hd.symm).symm

/-- A maximal chain of subspaces of a finite-dimensional space contains a subspace of every
dimension `n ≤ dim V`. -/
theorem IsMaxChain.exists_mem_finrank_eq {M : Set (Submodule k V)}
    (hM : IsMaxChain (· ≤ ·) M) {n : ℕ} (hn : n ≤ finrank k V) :
    ∃ X ∈ M, finrank k X = n := by
  -- any subspace comparable with every member of `M` belongs to `M`
  have hins : ∀ X : Submodule k V, (∀ Y ∈ M, X ≤ Y ∨ Y ≤ X) → X ∈ M := by
    intro X hX
    have hch : IsChain (· ≤ ·) (insert X M) := hM.1.insert fun Y hY _ => hX Y hY
    have := hM.2 hch (Set.subset_insert X M)
    rw [this]; exact Set.mem_insert X M
  induction n with
  | zero =>
    exact ⟨⊥, hins ⊥ fun Y _ => Or.inl bot_le, finrank_bot k V⟩
  | succ n ih =>
    obtain ⟨A, hAM, hA⟩ := ih (by omega)
    have htop : (⊤ : Submodule k V) ∈ M := hins ⊤ fun Y _ => Or.inr le_top
    have hAtop : A < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => ?_
      rw [h, finrank_top] at hA; omega
    -- the members of `M` strictly above `A`
    let T : Set (Submodule k V) := {X | X ∈ M ∧ A < X}
    have hT : ((fun X : Submodule k V => finrank k X) '' T).Nonempty := ⟨_, ⊤, ⟨htop, hAtop⟩, rfl⟩
    obtain ⟨B, ⟨hBM, hAB⟩, hBmin⟩ := Nat.sInf_mem hT
    have hBle : ∀ Y ∈ T, finrank k B ≤ finrank k Y := fun Y hY => by
      have := Nat.sInf_le (Set.mem_image_of_mem (fun X : Submodule k V => finrank k X) hY)
      simp only at hBmin this; omega
    have hAB' : finrank k A < finrank k B := Submodule.finrank_lt_finrank_of_lt hAB
    by_cases hBn : finrank k B = n + 1
    · exact ⟨B, hBM, hBn⟩
    -- otherwise insert a subspace `X = A + k v` with `v ∈ B \ A`
    obtain ⟨v, hvB, hvA⟩ := SetLike.exists_of_lt hAB
    set X := A ⊔ k ∙ v with hXdef
    have hAX : A < X := by
      refine lt_of_le_of_ne le_sup_left fun h => hvA ?_
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
    have hXB : X ≤ B := sup_le hAB.le ((Submodule.span_singleton_le_iff_mem _ _).2 hvB)
    have hXd : finrank k X = n + 1 := by
      have h1 := Submodule.finrank_lt_finrank_of_lt hAX
      have h2 : finrank k X ≤ finrank k A + finrank k (k ∙ v) :=
        Submodule.finrank_add_le_finrank_add_finrank A _
      have h3 : finrank k (k ∙ v) ≤ 1 := by
        simpa using finrank_span_le_card (R := k) ({v} : Set V)
      omega
    refine ⟨X, hins X fun Y hY => ?_, hXd⟩
    rcases hM.1.total hAM hY with hAY | hYA
    · rcases eq_or_lt_of_le hAY with rfl | hAY
      · exact Or.inr hAX.le
      · have hYT : Y ∈ T := ⟨hY, hAY⟩
        rcases hM.1.total hBM hY with hBY | hYB
        · exact Or.inl (hXB.trans hBY)
        · have := Submodule.eq_of_le_of_finrank_le hYB (hBle Y hYT)
          subst this
          exact Or.inl hXB
    · exact Or.inr (hYA.trans hAX.le)

/-- **Refinement of flags.**  Every flag (chain) `c` of subspaces of a finite-dimensional vector
space `V` can be refined to a maximal flag `V₀ ⊊ V₁ ⊊ ⋯ ⊊ V_n`, `n = dim V`, with
`dim Vᵢ = i` (so `V₀ = 0`, `V_n = V`, and consecutive members differ by one dimension). -/
theorem exists_maximal_flag_refinement {c : Set (Submodule k V)} (hc : IsChain (· ≤ ·) c) :
    ∃ f : Fin (finrank k V + 1) → Submodule k V,
      StrictMono f ∧ (∀ i, finrank k (f i) = i) ∧ c ⊆ Set.range f := by
  obtain ⟨M, hM, hcM⟩ := hc.exists_maxChain
  have hex : ∀ i : Fin (finrank k V + 1), ∃ X ∈ M, finrank k X = i := fun i =>
    IsMaxChain.exists_mem_finrank_eq hM (by omega)
  choose f hfM hfd using hex
  have hcomp : ∀ i j, f i ≤ f j ∨ f j ≤ f i := fun i j => by
    by_cases h : i = j
    · subst h; exact Or.inl le_rfl
    · exact hM.1 (hfM i) (hfM j) (fun h' => h (Fin.ext (by rw [← hfd i, ← hfd j, h'])))
  refine ⟨f, fun i j hij => ?_, hfd, fun X hX => ?_⟩
  · rcases hcomp i j with h | h
    · refine lt_of_le_of_ne h fun h' => ?_
      have := congrArg (fun X : Submodule k V => finrank k X) h'
      simp only [hfd] at this
      exact absurd (Fin.ext this) hij.ne
    · have := Submodule.finrank_mono h
      rw [hfd, hfd] at this
      exact absurd this (not_le.2 hij)
  · have hXV : finrank k X < finrank k V + 1 := Nat.lt_succ_of_le (Submodule.finrank_le X)
    refine ⟨⟨finrank k X, hXV⟩, ?_⟩
    exact Submodule.eq_of_comparable_of_finrank_eq (hM.1.total (hfM _) (hcM hX)) (hfd _)

end GLrBuilding
