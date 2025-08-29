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
    (llA.map groupBySecondInvariant).join.Forall
    fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid) := by
  unfold groupBySecondInvariant
  apply List.Forall.join
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
    (llA.map groupByThirdInvariant).join.Forall
    fun l ↦ l.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid) := by
  unfold groupByThirdInvariant
  apply List.Forall.join
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

lemma groupByFirstInvariant_normalized (lA : List PartialMatroid)
    (hlA : lA.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (groupByFirstInvariant lA).Forall
    (fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) := by
   unfold groupByFirstInvariant
   apply forall_groupByValue
   apply List.forall_mergeSort
   apply hlA


lemma groupBySecondInvariant_normalized (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (llA.map groupBySecondInvariant).join.Forall
    fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid) := by
  unfold groupBySecondInvariant
  apply List.Forall.join
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

lemma groupByThirdInvariant_normalized (llA : List (List PartialMatroid))
    (hllA : llA.Forall fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (llA.map groupByThirdInvariant).join.Forall
    fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid) := by
  unfold groupByThirdInvariant
  apply List.Forall.join
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

lemma groupByBucket_normalized (lA : List PartialMatroid)
    (hlA : lA.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (groupByBucket lA).Forall
    (fun l ↦ l.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) := by
    unfold groupByBucket
    apply groupByThirdInvariant_normalized
    apply groupBySecondInvariant_normalized
    apply groupByFirstInvariant_normalized
    apply hlA





-- lemma groupByBucket_mem {lA : List PartialMatroid} {A : PartialMatroid}
--     (hA : )




-----prove group by bucket_nonisomorphic


lemma invariant1_of_sameUpTolabelling {M₁ M₂ : PartialMatroid} {f : ℕ → ℕ} (ha : f ∈ permutation 8)
  (hb : sameUpToRelabelling M₁.matroid M₂.matroid f) : invariant1 M₁ = invariant1 M₂ := by
  unfold sameUpToRelabelling at hb
  simp at hb
  unfold invariant1
  have h := @count_of_relabelling M₂.matroid f ha
  rw[hb] at h
  rw[sort_join_sort] at h
  rw[sort_join_map_sort] at h
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

  -- Fin (List.length (groupByValue (List.mergeSort (fun l1 l2 => invariant1 l1 < invariant1 l2) A) invariant1))
  -- Fin (List.length (groupByValue (List.mergeSort (fun x x_1 => invariant1 x < invariant1 x_1) A) invariant1))

/- Lemma for countBuckets (related to Theorem 1): If the input is an list partial matroids
(order does matter, for both the lishfts and for the members) with range i < n and lenght = r, then
the output will be a lawful sparse paving matroid -/
/- After rethinking, we might not need to prove anything about countBuckets since it is not used
directly in the main computation.-/

/-- For all partial matroids in a bucket, they do not exist in other buckets even as permutations of
partial matroids.
(will probably get used for Theorem 3) -/
lemma nonisomorphic_groupByBucket (A : List PartialMatroid) :
    (groupByBucket A).Pairwise fun L₁ L₂ ↦
      L₁.Forall fun M₁ ↦ L₂.Forall fun M₂ ↦ ¬ permutationsComparison 8 M₁.matroid M₂.matroid := by

  -- use theorem `nonisomorphic_groupByFirstInvariant` and similar for other invariants

  sorry




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
    rw [List.mem_join] at h2
    obtain ⟨ l₁, hl1, hla1⟩ := h2
    rw[List.mem_map] at hl1
    obtain ⟨ l₂, hl2, hla2⟩ := hl1
    rw [List.mem_join] at hl2
    obtain ⟨ l₃ , hl3, hla3⟩ := hl2
    simp at hl3
    obtain ⟨ l₄ , hl4, hla4⟩ := hl3
    rw[<- hla2] at hla1
    rw[<- hla4] at hla3
    have := mem_of_groupByThirdInvariant h1 hla1
    have := mem_of_groupBySecondInvariant this hla3
    have := mem_of_groupByFirstInvariant this hl4
    exact this
