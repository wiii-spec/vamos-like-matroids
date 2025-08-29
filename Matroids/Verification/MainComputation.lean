import Matroids.Verification.AllPossibilities
import Matroids.Verification.Vamos
import Matroids.Verification.Buckets
import Matroids.Verification.Relabelling
import Matroids.MainComputation

/-! # Verifying that the main computation has the desired properties -/

/-! ## Main argument -/

lemma augmentedVamos_lawful (i : ℕ) :
    (augmentedVamos i).Forall fun L ↦ L.Forall fun M ↦ LawfulSparsePavingMatroid 8 4 M.matroid := by
  unfold augmentedVamos
  apply groupByBucket_lawful
  apply augmentationsFinal_lawful
  · apply vamos_lawful
  · apply vamos_remainingOptions_mem_range
  · apply vamos_remainingOptions_length_eq_rank
  · apply vamos_remainingOptions_sorted_of_mem
  · apply vamos_remainingOptions_not_nearlySame


lemma augmentedVamos_vamosLike (i : ℕ) :
    (augmentedVamos i).Forall fun L ↦ L.Forall fun M ↦ List.NormalizedVamosLike M.matroid := by
  unfold augmentedVamos
  apply groupByBucket_vamosLike
  apply augmentationsFinal_vamosLike
  · apply vamos_vamosLike
  · apply vamos_remainingOptions_does_not_contain

lemma prunedVamos_lawful (i : ℕ) :
    (prunedVamos i).Forall fun L ↦ L.Forall fun M ↦ LawfulSparsePavingMatroid 8 4 M.matroid := by
  rw [prunedVamos_def]
  rw [List.forall_map_iff]
  apply List.Forall.imp pruning_lawful
  apply augmentedVamos_lawful

lemma prunedVamos_vamosLike (i : ℕ) :
    (prunedVamos i).Forall fun L ↦ L.Forall fun M ↦ List.NormalizedVamosLike M.matroid := by
  rw [prunedVamos_def]
  rw [List.forall_map_iff]
  apply List.Forall.imp pruning_vamosLike
  apply augmentedVamos_vamosLike

lemma flattenedPrunedVamos_lawful :
    flattenedPrunedVamos.Forall fun M ↦ LawfulSparsePavingMatroid 8 4 M.matroid := by
  unfold flattenedPrunedVamos
  apply List.Forall.flatten
  rw [List.forall_map_iff]
  rw [List.forall_iff_forall_mem]
  intro i _
  apply List.Forall.flatten
  apply prunedVamos_lawful

lemma flattenedPrunedVamos_vamosLike :
    flattenedPrunedVamos.Forall fun M ↦ List.NormalizedVamosLike M.matroid := by
  unfold flattenedPrunedVamos
  apply List.Forall.flatten
  rw [List.forall_map_iff]
  rw [List.forall_iff_forall_mem]
  intro i _
  apply List.Forall.flatten
  apply prunedVamos_vamosLike


/-- In each of the pruned "buckets", `l`, in the list of `i`-augmentations of the Vamos matroid,
all the partial matroids in `l` are different.

Note: we expect that `l` has only one entry, so one possible method of proof is to notice this,
then point out to Lean that a list of length 1 has no repeats.

But another method of proof is to notice that the pruning process removes repeats. -/
theorem forall_nonisomorphic_prunedVamos (i : ℕ) :
    (prunedVamos i).Forall fun l ↦ l.Pairwise fun A₁ A₂ ↦ ¬permutationsComparison 8 A₁.matroid A₂.matroid := by
  rw [prunedVamos_def]
  rw [List.forall_iff_forall_mem]
  intro l hl
  simp at hl
  have ⟨ a, ha, hal⟩ := hl
  subst hal
  clear hl ha
  apply nonisomorphic_pruning


/-- For a natural number `i`, partial matroids `A` and `B` drawn from *different* pruned
buckets of the `i`-augmentations of the Vamos matroid, then they are different. -/
theorem forall_forall_nonisomorphic_prunedVamos (i : ℕ) :
    (prunedVamos i).Pairwise fun l₁ l₂ ↦
    l₁.Forall fun A ↦ l₂.Forall fun B ↦ ¬permutationsComparison 8 A.matroid B.matroid := by
  rw [prunedVamos_def]
  unfold augmentedVamos
  let L := PartialMatroid.groupByBucket (PartialMatroid.augmentationsFinal i Vamos)
  let P (L1 L2) : Prop := ¬ permutationsComparison 8 L1 L2
  have h := nonisomorphic_groupByBucket (PartialMatroid.augmentationsFinal i Vamos)
  change List.Pairwise
    (fun L₁ L₂ =>
      List.Forall (fun M₁ => List.Forall (fun M₂ => P M₁.matroid M₂.matroid) L₂) L₁)
    L at h
  change List.Pairwise (fun l₁ l₂ =>
    List.Forall (fun A => List.Forall (fun B => P A.matroid B.matroid) l₂) l₁)
    (List.map pruning L)
  rw[List.pairwise_map]
  apply List.Pairwise.imp _ h
  intro l₁ l₂ hl
  rw [List.forall_iff_forall_mem]
  intro x hx
  rw [List.forall_iff_forall_mem]
  intro y hy
  apply mem_of_mem_pruning at hx
  apply mem_of_mem_pruning at hy
  rw[List.forall_iff_forall_mem] at hl
  specialize hl x hx
  rw[List.forall_iff_forall_mem] at hl
  specialize hl y hy
  exact hl


-- lemma mem_of_groupByValue




theorem length_augmentedVamos {i : ℕ} {A : PartialMatroid} {lA' : List PartialMatroid}
    (hlA' : lA' ∈ augmentedVamos i)
    (hA : A ∈ lA') :
    A.matroid.length = 5 + i := by
  rw [augmentedVamos] at hlA'
  have := mem_of_groupByBucket hA hlA'
  apply length_augmentationsFinal at this
  simp at this
  omega



theorem length_prunedVamos {i : ℕ} {A : PartialMatroid} {lA' : List PartialMatroid}
    (hlA' : lA' ∈ prunedVamos i)
    (hA : A ∈ lA') :
    A.matroid.length = 5 + i := by
  rw [prunedVamos_def] at hlA'
  simp at hlA'
  obtain ⟨lp, q⟩ := hlA'
  obtain ⟨ q1, q2⟩ := q
  subst q2
  apply length_augmentedVamos
  apply q1
  apply mem_of_mem_pruning
  apply hA

/- to prove this, need some lemmas about being non-isomorphic in different situations
  * after applying `pruning`, everything in a list is non-isomorphic
  * after applying `groupByBucket`, everything in different buckets is non-isomorphic
  * augmenting by different numbers of quadrangles cannot be isomorphic -/
lemma nonisomorphic_flattenedPrunedVamos :
    flattenedPrunedVamos.Pairwise (fun A₁ A₂ ↦ ¬ permutationsComparison 8 A₁.matroid A₂.matroid) := by
  unfold flattenedPrunedVamos
  rw [List.pairwise_flatten]
  constructor
  · intro lA hlA
    rw[List.mem_map] at hlA
    obtain ⟨ i, hi1, hi2⟩ := hlA
    rw [←hi2]
    clear hi2 lA
    rw [List.pairwise_flatten]
    constructor
    · rw [← List.forall_iff_forall_mem]
      apply forall_nonisomorphic_prunedVamos
    · simp_rw [← List.forall_iff_forall_mem]
      apply forall_forall_nonisomorphic_prunedVamos
  · rw [List.pairwise_map]
    apply List.pairwise_range
    intro i j hij A hA B hB
    rw [List.mem_flatten] at hA hB
    obtain ⟨ lA', hlA', hA⟩ := hA
    obtain ⟨ lB', hlB', hB⟩ := hB
    apply nonisomorphic_of_length
    have hAi:= length_prunedVamos hlA' hA
    rw [hAi]
    have hBj:= length_prunedVamos hlB' hB
    rw [hBj]
    omega

/-- info: 'length_prunedVamos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms length_prunedVamos

/-- info: 'nonisomorphic_of_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nonisomorphic_of_length

/-- info: 'List.forall_iff_forall_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms List.forall_iff_forall_mem

-- not done yet
#print axioms forall_forall_nonisomorphic_prunedVamos


/-- The main computation produces only `List (List ℕ)` objects which are valid ("lawful") sparse
paving matroids.
Informally: Theorem 1 -/
theorem mainComputation_lawful : mainComputation.Forall (LawfulSparsePavingMatroid 8 4) := by
  unfold mainComputation
  rw [List.forall_map_iff]
  apply flattenedPrunedVamos_lawful

/-- info: 'mainComputation_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mainComputation_lawful


/-- The main computation produces only `List (List ℕ)` objects which are "normalized Vámos-like".
Informally: Theorem 2 -/
theorem mainComputation_vamosLike: mainComputation.Forall List.NormalizedVamosLike := by
  unfold mainComputation
  rw [List.forall_map_iff]
  apply flattenedPrunedVamos_vamosLike

/--
info: 'mainComputation_vamosLike' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mainComputation_vamosLike

/-- The list of `List (List ℕ)` objects provided by the main computation are mutually
non-isomorphic (up to permutation of 0, 1, 2, ... 7).
Informally: Theorem 3 -/
theorem nonisomorphic_mainComputation :
    mainComputation.Pairwise (fun l₁ l₂ ↦ ¬ permutationsComparison 8 l₁ l₂) := by
  unfold mainComputation
  rw [List.pairwise_map]
  apply nonisomorphic_flattenedPrunedVamos

/-- Any "normalized Vámos-like" `List (List ℕ)` object which is valid as an (8, 4) sparse paving
matroid is isomorphic to one of the objects on the list provided by the main computation.
Informally: Theorem 4 -/
theorem mainComputation_exhausts {l : List (List ℕ)} (hl₁ : LawfulSparsePavingMatroid 8 4 l)
    (hl₂ : l.NormalizedVamosLike) :
    ∃ l' ∈ mainComputation, permutationsComparison 8 l l' := by
  sorry
