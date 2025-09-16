import Matroids.Verification.Basic
import Matroids.Buckets
import Matroids.Verification.Relabelling
import Matroids.Verification.Count
import Matroids.Verification.Miscellaneous

open PartialMatroid


lemma groupByFirstInvariant_lawful (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (groupByFirstInvariant A).Forall
    (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) := by
  unfold groupByFirstInvariant
  apply forall_groupByValue
  apply List.forall_mergeSort
  apply hA

lemma groupBySecondInvariant_lawful (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (llA.map groupBySecondInvariant).flatten.Forall
    fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid) := by
  unfold groupBySecondInvariant
  apply List.Forall.flatten
  rw [List.forall_iff_forall_mem]
  intro llB hllB
  rw[List.mem_map] at hllB
  obtain ⟨lB, hlB⟩ := hllB
  obtain ⟨hlB1, hlB2⟩ := hlB
  rw [←hlB2] at *
  apply forall_groupByValue
  rw [List.forall_iff_forall_mem]
  intro C hC
  rw [List.mem_mergeSort] at hC
  rw [List.forall_iff_forall_mem] at *
  apply hllA at hlB1
  rw [List.forall_iff_forall_mem] at hlB1
  apply hlB1 at hC
  apply hC

lemma groupByThirdInvariant_lawful (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (llA.map groupByThirdInvariant).flatten.Forall
    fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid) := by
  unfold groupByThirdInvariant
  apply List.Forall.flatten
  rw [List.forall_iff_forall_mem]
  intro llB hllB
  rw[List.mem_map] at hllB
  obtain ⟨lB, hlB⟩ := hllB
  obtain ⟨hlB1, hlB2⟩ := hlB
  rw [←hlB2] at *
  apply forall_groupByValue
  rw [List.forall_iff_forall_mem]
  intro C hC
  rw [List.mem_mergeSort] at hC
  rw [List.forall_iff_forall_mem] at *
  apply hllA at hlB1
  rw [List.forall_iff_forall_mem] at hlB1
  apply hlB1 at hC
  apply hC


/-- If `A` is a list of `PartialMatroid`s, all of which are valid (n, r)-sparse paving matroids,
then when the `groupByBucket` operation is performed, every `PartialMatroid` in the the resulting
list of list of partial matroids is still a valid (n, r)-sparse paving matroids. -/
lemma groupByBucket_lawful (lA : List PartialMatroid)
    (hA : lA.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (groupByBucket lA).Forall
    (fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) := by
  unfold groupByBucket
  apply groupByThirdInvariant_lawful
  apply groupBySecondInvariant_lawful
  apply groupByFirstInvariant_lawful
  apply hA

lemma groupByFirstInvariant_vamosLike (lA : List PartialMatroid)
    (hlA : lA.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (groupByFirstInvariant lA).Forall
    (fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) := by
   unfold groupByFirstInvariant
   apply forall_groupByValue
   apply List.forall_mergeSort
   apply hlA


lemma groupBySecondInvariant_vamosLike (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (llA.map groupBySecondInvariant).flatten.Forall
    fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid) := by
  unfold groupBySecondInvariant
  apply List.Forall.flatten
  rw [List.forall_iff_forall_mem]
  intro llB hllB
  rw[List.mem_map] at hllB
  obtain ⟨lB, hlB⟩ := hllB
  obtain ⟨hlB1, hlB2⟩ := hlB
  rw [←hlB2] at *
  apply forall_groupByValue
  rw [List.forall_iff_forall_mem]
  intro C hC
  rw [List.mem_mergeSort] at hC
  rw [List.forall_iff_forall_mem] at *
  apply hllA at hlB1
  rw [List.forall_iff_forall_mem] at hlB1
  apply hlB1 at hC
  apply hC

lemma groupByThirdInvariant_vamosLike (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (llA.map groupByThirdInvariant).flatten.Forall
    fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid) := by
  unfold groupByThirdInvariant
  apply List.Forall.flatten
  rw [List.forall_iff_forall_mem]
  intro llB hllB
  rw[List.mem_map] at hllB
  obtain ⟨lB, hlB⟩ := hllB
  obtain ⟨hlB1, hlB2⟩ := hlB
  rw [←hlB2] at *
  apply forall_groupByValue
  rw [List.forall_iff_forall_mem]
  intro C hC
  rw [List.mem_mergeSort] at hC
  rw [List.forall_iff_forall_mem] at *
  apply hllA at hlB1
  rw [List.forall_iff_forall_mem] at hlB1
  apply hlB1 at hC
  apply hC

lemma groupByBucket_vamosLike (lA : List PartialMatroid)
    (hlA : lA.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (groupByBucket lA).Forall
    (fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) := by
    unfold groupByBucket
    apply groupByThirdInvariant_vamosLike
    apply groupBySecondInvariant_vamosLike
    apply groupByFirstInvariant_vamosLike
    apply hlA





-- lemma groupByBucket_mem {lA : List PartialMatroid} {A : PartialMatroid}
--     (hA : )


lemma mem_of_groupByFirstInvariant {A :PartialMatroid} {lA lB: List PartialMatroid}
    (h1 : A ∈ lA)
    (h2 : lA ∈  PartialMatroid.groupByFirstInvariant lB) :
    A ∈ lB := by
  unfold PartialMatroid.groupByFirstInvariant at h2
  have := mem_of_groupByValue h1 h2
  rw [List.mem_mergeSort] at this
  exact this


lemma mem_of_groupBySecondInvariant {A :PartialMatroid} {lA lB: List PartialMatroid}
    (h1 : A ∈ lA)
    (h2 : lA ∈  PartialMatroid.groupBySecondInvariant lB) :
    A ∈ lB := by
  unfold PartialMatroid.groupBySecondInvariant at h2
  have := mem_of_groupByValue h1 h2
  rw [List.mem_mergeSort] at this
  exact this

lemma mem_of_groupByThirdInvariant {A :PartialMatroid} {lA lB: List PartialMatroid}
    (h1 : A ∈ lA)
    (h2 : lA ∈  PartialMatroid.groupByThirdInvariant lB) :
    A ∈ lB := by
  unfold PartialMatroid.groupByThirdInvariant at h2
  have := mem_of_groupByValue h1 h2
  rw [List.mem_mergeSort] at this
  exact this



lemma mem_of_groupByBucket {A :PartialMatroid} {lA lB: List PartialMatroid}
    (h1 : A ∈ lA)
    (h2 : lA ∈ PartialMatroid.groupByBucket lB) :
    A ∈ lB := by
    unfold PartialMatroid.groupByBucket at h2
    rw [List.mem_flatten] at h2
    obtain ⟨ l₁, hl1, hla1⟩ := h2
    rw[List.mem_map] at hl1
    obtain ⟨ l₂, hl2, hla2⟩ := hl1
    rw [List.mem_flatten] at hl2
    obtain ⟨ l₃ , hl3, hla3⟩ := hl2
    simp at hl3
    obtain ⟨ l₄ , hl4, hla4⟩ := hl3
    rw[<- hla2] at hla1
    rw[<- hla4] at hla3
    have := mem_of_groupByThirdInvariant h1 hla1
    have := mem_of_groupBySecondInvariant this hla3
    have := mem_of_groupByFirstInvariant this hl4
    exact this


-----prove group by bucket_nonisomorphic


lemma invariant1_of_sameUpTolabelling {M₁ M₂ : PartialMatroid} {f : ℕ → ℕ} (ha : f ∈ permutation 8)
  (hb : sameUpToRelabelling M₁.matroid M₂.matroid f) : invariant1 M₁ = invariant1 M₂ := by
  unfold sameUpToRelabelling at hb
  simp at hb
  unfold invariant1
  have h := @count_of_relabelling M₂.matroid f ha
  rw[hb] at h
  rw[sort_flatten_sort] at h
  rw[sort_flatten_map_sort] at h
  apply h
  -- hopefully follows from count_of_relabelling?


lemma invariant1_of_isomorphic (M₁ M₂ : PartialMatroid) (h : permutationsComparison 8 M₁.matroid M₂.matroid) :
    invariant1 M₁ = invariant1 M₂ := by
  unfold permutationsComparison at h
  simp at h
  obtain ⟨ f, ha,hb ⟩  := h
  apply invariant1_of_sameUpTolabelling ha hb


lemma nonisomorphic_groupByFirstInvariant (A : List PartialMatroid) :
    (groupByFirstInvariant A).Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ ¬ permutationsComparison 8 M₁.matroid M₂.matroid := by

    unfold groupByFirstInvariant
    rw [List.pairwise_iff_get]
    intro i j h
    rw[List.forall_iff_forall_mem]
    intro x hx
    rw[List.forall_iff_forall_mem]
    intro y hy
    suffices h : invariant1 x ≠ invariant1 y by
      contrapose! h
      apply invariant1_of_isomorphic
      exact h
    exact ne_of_groupByValue h.ne hx hy

---Invariant 2


lemma pairs_map {f : α → β}:
    ((List.pairs) ∘ fun B => List.map f B) = List.map (fun x ↦ List.map f x) ∘ (List.pairs) := by

  sorry



lemma count_of_relabelling_pairs {L : List (List Nat)} {f : ℕ → ℕ} (ha : f ∈ permutation 8) :
    count (List.sort (List.flatten (List.sort (List.map List.sort (List.map (List.pairs) (relabelling L f))))))
    = count (List.sort (List.flatten (List.map (List.pairs) L))) := by
  rw[sort_flatten_sort]
  rw[sort_flatten_map_sort]
  unfold relabelling
  simp
  -- rw[Function.comp_assoc]
  rw[pairs_map]
  rw[<- List.map_comp_map]
  rw[Function.comp]
  have hf := permutation_bijective 8
  specialize hf f ha
  have h_mapf : (fun x => List.map f x).Bijective := by
   simp
   exact hf
  convert count_of_sort_map (List.map (List.pairs) L) h_mapf




lemma invariant2_of_sameUpTolabelling {M₁ M₂ : PartialMatroid} {f : ℕ → ℕ} (ha : f ∈ permutation 8)
  (hb : sameUpToRelabelling M₁.matroid M₂.matroid f) : invariant2 M₁ = invariant2 M₂ := by
  unfold sameUpToRelabelling at hb
  simp at hb
  unfold invariant2
  unfold pairing
  simp
  -- rw[<- sort_flatten_map_sort]
  -- rw[map_pairs_sort M₁.matroid]

  have h := @count_of_relabelling_pairs M₂.matroid f ha
  rw[<- h]
  rw[<- sort_flatten_map_sort]
  rw[sort_flatten_sort] at h ⊢
  -- congr 1
  rw[sort_flatten_map_sort]
  rw[sort_flatten_map_sort]

  sorry
  -- hopefully follows from count_of_relabelling?



lemma invariant2_of_isomorphic (M₁ M₂ : PartialMatroid) (h : permutationsComparison 8 M₁.matroid M₂.matroid) :
    invariant2 M₁ = invariant2 M₂ := by
  unfold permutationsComparison at h
  simp at h
  obtain ⟨ f, ha,hb ⟩  := h
  apply invariant2_of_sameUpTolabelling ha hb


lemma nonisomorphic_groupBySecondInvariant (A : List PartialMatroid) :
    (groupBySecondInvariant A).Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ ¬ permutationsComparison 8 M₁.matroid M₂.matroid := by

    unfold groupBySecondInvariant
    rw [List.pairwise_iff_get]
    intro i j h
    rw[List.forall_iff_forall_mem]
    intro x hx
    rw[List.forall_iff_forall_mem]
    intro y hy
    suffices h : invariant2 x ≠ invariant2 y by
      contrapose! h
      apply invariant2_of_isomorphic
      exact h
    exact ne_of_groupByValue h.ne hx hy






--Invariant 3 non_isomorphic

lemma invariant3_of_sameUpTolabelling {M₁ M₂ : PartialMatroid} {f : ℕ → ℕ} (ha : f ∈ permutation 8)
  (hb : sameUpToRelabelling M₁.matroid M₂.matroid f) : invariant3 M₁ = invariant3 M₂ := by
  unfold sameUpToRelabelling at hb
  simp at hb
  unfold invariant3
  unfold pairing
  simp
  -- rw[<- sort_flatten_map_sort]
  -- rw[map_pairs_sort M₁.matroid]

  have h := @count_of_relabelling_pairs (complement M₂.matroid) f ha
  rw[<- h]
  rw[<- sort_flatten_map_sort]
  rw[sort_flatten_sort] at h ⊢
  -- congr 1
  rw[sort_flatten_map_sort]
  rw[sort_flatten_map_sort]

  sorry



lemma invariant3_of_isomorphic (M₁ M₂ : PartialMatroid) (h : permutationsComparison 8 M₁.matroid M₂.matroid) :
    invariant3 M₁ = invariant3 M₂ := by
  unfold permutationsComparison at h
  simp at h
  obtain ⟨ f, ha,hb ⟩  := h
  apply invariant3_of_sameUpTolabelling ha hb



lemma nonisomorphic_groupByThirdInvariant (A : List PartialMatroid) :
    (groupByThirdInvariant A).Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ ¬ permutationsComparison 8 M₁.matroid M₂.matroid := by
  unfold groupByThirdInvariant
  rw [List.pairwise_iff_get]
  intro i j h
  rw[List.forall_iff_forall_mem]
  intro x hx
  rw[List.forall_iff_forall_mem]
  intro y hy
  suffices h : invariant3 x ≠ invariant3 y by
    contrapose! h
    apply invariant3_of_isomorphic
    exact h
  exact ne_of_groupByValue h.ne hx hy




/- Lemma for countBuckets (related to Theorem 1): If the input is an list partial matroids
(order does matter, for both the lishfts and for the members) with range i < n and lenght = r, then
the output will be a lawful sparse paving matroid -/
/- After rethinking, we might not need to prove anything about countBuckets since it is not used
directly in the main computation.-/

/-- For all partial matroids in a bucket, they do not exist in other buckets even as permutations of
partial matroids.
(will probably get used for Theorem 3) -/

/-
should need mem_of_invariants-/


lemma pairwise_trans'{P : α → α → Prop}
    {f: List α → List (List α)}
    (hf : ∀ A : List α, (f A).Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ P M₁ M₂)
    {L : List (List α)}
    (hL : L.Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ P M₁ M₂)
    (hf_mem : ∀ A L: List α , ∀ a : α , a ∈ L → L ∈ f A → a ∈ A )  :
    ((List.map f L).flatten).Pairwise fun L₁ L₂ ↦ L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ P M₁ M₂ := by

  match L with
  | [] => simp
  | a :: L =>
    simp at hL ⊢
    rw[List.pairwise_append]
    constructor
    · specialize hf a
      exact hf
    · constructor
      exact pairwise_trans' hf hL.2 hf_mem
      have hL := hL.1
      intro M₁ hM₁ M₂ hM₂
      rw[List.forall_iff_forall_mem]
      simp at hM₂
      contrapose! hL
      obtain ⟨x, hx , hMM ⟩ := hL
      obtain ⟨ l, hl, hM₂ ⟩ := hM₂
      use l
      constructor
      exact hl
      rw[List.forall_iff_forall_mem] at hMM ⊢
      simp at hMM ⊢
      use x
      constructor
      exact hf_mem a M₁ x hx hM₁
      rw[List.forall_iff_forall_mem] at ⊢
      simp at ⊢
      obtain ⟨y, hy, hMM⟩ := hMM
      use y
      constructor
      exact hf_mem l M₂ y hy hM₂
      exact hMM


lemma pairwise_trans {P : α → α → Prop}
    {f₁ f₂ : List α → List (List α)}
    (hf₁ : ∀ A : List α, (f₁ A).Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ P M₁ M₂)
    (hf₂ : ∀ A : List α, (f₂ A).Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ P M₁ M₂)
    (hf₂_mem : ∀ A L : List α ,∀ a : α , a ∈ L → L ∈ f₂ A  → a ∈ A)  :
    ∀ A : List α, ((List.map f₂ (f₁ A)).flatten).Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ P M₁ M₂  := by
  intro A
  specialize hf₁ A
  apply pairwise_trans' hf₂ hf₁ hf₂_mem



lemma nonisomorphic_groupByinvariant1_2 (A : List PartialMatroid) :
    (((groupByFirstInvariant A).map) (groupBySecondInvariant)).flatten.Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ ¬ permutationsComparison 8 M₁.matroid M₂.matroid := by
  have := pairwise_trans nonisomorphic_groupByFirstInvariant nonisomorphic_groupBySecondInvariant
  apply this
  exact fun A L a a_1 a_2 => mem_of_groupBySecondInvariant a_1 a_2



lemma nonisomorphic_groupByBucket (A : List PartialMatroid) :
    (groupByBucket A).Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ ¬ permutationsComparison 8 M₁.matroid M₂.matroid := by

  -- use theorem `nonisomorphic_groupByFirstInvariant` and similar for other invariants
  unfold groupByBucket
  have := pairwise_trans nonisomorphic_groupByinvariant1_2 nonisomorphic_groupByThirdInvariant
  apply this
  exact fun A L a a_1 a_2 => mem_of_groupByThirdInvariant a_1 a_2
