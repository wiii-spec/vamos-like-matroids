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


lemma augmentedVamos_normalized (i : ℕ) :
    (augmentedVamos i).Forall fun L ↦ L.Forall fun M ↦ List.NormalizedVamosLike M.matroid := by
  unfold augmentedVamos
  apply groupByBucket_normalized
  apply augmentationsFinal_normalized
  · apply vamos_normalized
  · apply vamos_remainingOptions_does_not_contain

lemma prunedVamos_lawful (i : ℕ) :
    (prunedVamos i).Forall fun L ↦ L.Forall fun M ↦ LawfulSparsePavingMatroid 8 4 M.matroid := by
  rw [prunedVamos_def]
  rw [List.forall_map_iff]
  apply List.Forall.imp pruning_lawful
  apply augmentedVamos_lawful

lemma prunedVamos_normalized (i : ℕ) :
    (prunedVamos i).Forall fun L ↦ L.Forall fun M ↦ List.NormalizedVamosLike M.matroid := by
  rw [prunedVamos_def]
  rw [List.forall_map_iff]
  apply List.Forall.imp pruning_normalized
  apply augmentedVamos_normalized

lemma joinedPrunedVamos_lawful :
    joinedPrunedVamos.Forall fun M ↦ LawfulSparsePavingMatroid 8 4 M.matroid := by
  unfold joinedPrunedVamos
  apply List.Forall.join
  rw [List.forall_map_iff]
  rw [List.forall_iff_forall_mem]
  intro i _
  apply List.Forall.join
  apply prunedVamos_lawful

lemma joinedPrunedVamos_normalized :
    joinedPrunedVamos.Forall fun M ↦ List.NormalizedVamosLike M.matroid := by
  unfold joinedPrunedVamos
  apply List.Forall.join
  rw [List.forall_map_iff]
  rw [List.forall_iff_forall_mem]
  intro i _
  apply List.Forall.join
  apply prunedVamos_normalized


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


lemma mem_of_groupByValueAux {A : PartialMatroid} {lA lB : List PartialMatroid} {f : PartialMatroid → List ℕ}
    (h1 : A ∈ lA)
    (h2 : lA = (groupByValueAux f lB).1 ∨ lA ∈ (groupByValueAux f lB).2) :
    A ∈ lB := by
  unfold groupByValueAux at h2
  match lB with
  | [] =>
    simp at h2
    rw[h2] at h1
    exact h1
  | [a] =>
    simp at h2
    rw[h2] at h1
    exact h1
  | a :: b :: l =>
    simp at h2
    split_ifs at h2
    · simp at h2
      obtain h2 | h2 := h2
      subst h2
      simp at h1
      obtain h1 | h1 := h1
      · rw[h1]
        simp
      · rw [List.mem_cons]
        right
        apply mem_of_groupByValueAux (lB := b ::l) (lA := (groupByValueAux f (b :: l)).1)
        · exact h1
        · left
          rfl
      -- ·
      rw [List.mem_cons]
      right
      apply mem_of_groupByValueAux (lB := b ::l) ( lA := lA) (f := f)
      · exact h1
      · right
        exact h2
    · simp at h2
      obtain h2 | h2 | h2 := h2
      · subst h2
        simp at h1
        rw[h1]
        simp
      · rw [List.mem_cons]
        right
        apply mem_of_groupByValueAux (lB := b ::l) (lA := (groupByValueAux f (b :: l)).1)
        · subst h2
          exact h1
        · left
          rfl
      · rw [List.mem_cons]
        right
        apply mem_of_groupByValueAux (lB := b ::l) ( lA := lA) (f := f)
        · exact h1
        · right
          exact h2


lemma mem_of_groupByValue {A :PartialMatroid} {lA lB: List PartialMatroid} {f : PartialMatroid → List Nat}
    (h1 : A ∈ lA)
    (h2 : lA ∈  groupByValue lB f) :
    A ∈ lB := by
  unfold groupByValue at h2
  simp at h2
  exact mem_of_groupByValueAux h1 h2


lemma mem_of_groupByFirstInvariant {A :PartialMatroid} {lA lB: List PartialMatroid}
    (h1 : A ∈ lA)
    (h2 : lA ∈  PartialMatroid.groupByFirstInvariant lB) :
    A ∈ lB := by
  unfold PartialMatroid.groupByFirstInvariant at h2
  have := mem_of_groupByValue h1 h2
  exact List.reverse_mem_mergeSort _ this


lemma mem_of_groupBySecondInvariant {A :PartialMatroid} {lA lB: List PartialMatroid}
    (h1 : A ∈ lA)
    (h2 : lA ∈  PartialMatroid.groupBySecondInvariant lB) :
    A ∈ lB := by
  unfold PartialMatroid.groupBySecondInvariant at h2
  have := mem_of_groupByValue h1 h2
  exact List.reverse_mem_mergeSort _ this

lemma mem_of_groupByThirdInvariant {A :PartialMatroid} {lA lB: List PartialMatroid}
    (h1 : A ∈ lA)
    (h2 : lA ∈  PartialMatroid.groupByThirdInvariant lB) :
    A ∈ lB := by
  unfold PartialMatroid.groupByThirdInvariant at h2
  have := mem_of_groupByValue h1 h2
  exact List.reverse_mem_mergeSort _ this



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




lemma length_augmentations {A A' : PartialMatroid}
    (hA: A ∈ PartialMatroid.augmentations A') :
    A.matroid.length = A'.matroid.length + 1 := by
  unfold PartialMatroid.augmentations at hA
  unfold PartialMatroid.augment at hA
  simp at hA
  obtain ⟨a, _, ha2⟩ := hA
  rw[<- ha2]
  simp
  unfold List.sort
  simp

lemma length_augmentationsFinal{n : ℕ} {A A' : PartialMatroid}:
    A ∈ PartialMatroid.augmentationsFinal n A' -> A.matroid.length = A'.matroid.length + n := by
  induction n generalizing A A' with
  | zero =>
    intro hA
    unfold PartialMatroid.augmentationsFinal at hA
    simp at hA
    rw[ hA]
    simp
  | succ n ih =>
    intro hA
    unfold PartialMatroid.augmentationsFinal at hA
    simp at hA
    obtain ⟨a,ih1,ih2⟩ := hA
    have ih1 := length_augmentations ih1
    apply ih at ih2
    rw[ih1] at ih2
    omega



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
lemma nonisomorphic_joinedPrunedVamos :
    joinedPrunedVamos.Pairwise (fun A₁ A₂ ↦ ¬ permutationsComparison 8 A₁.matroid A₂.matroid) := by
  unfold joinedPrunedVamos
  rw [List.pairwise_join]
  constructor
  · intro lA hlA
    rw[List.mem_map] at hlA
    obtain ⟨ i, hi1, hi2⟩ := hlA
    rw [←hi2]
    clear hi2 lA
    rw [List.pairwise_join]
    constructor
    · rw [← List.forall_iff_forall_mem]
      apply forall_nonisomorphic_prunedVamos
    · simp_rw [← List.forall_iff_forall_mem]
      apply forall_forall_nonisomorphic_prunedVamos
  · rw [List.pairwise_map]
    apply List.pairwise_range
    intro i j hij A hA B hB
    rw [List.mem_join] at hA hB
    obtain ⟨ lA', hlA', hA⟩ := hA
    obtain ⟨ lB', hlB', hB⟩ := hB
    apply nonisomorphic_of_length
    have hAi:= length_prunedVamos hlA' hA
    rw [hAi]
    have hBj:= length_prunedVamos hlB' hB
    rw [hBj]
    omega

#print axioms length_prunedVamos
#print axioms nonisomorphic_of_length
#print axioms List.forall_iff_forall_mem
#print axioms forall_forall_nonisomorphic_prunedVamos


/-- The main computation produces only `List (List ℕ)` objects which are valid ("lawful") sparse
paving matroids.
Informally: Theorem 1 -/
theorem mainComputation_lawful : mainComputation.Forall (LawfulSparsePavingMatroid 8 4) := by
  unfold mainComputation
  rw [List.forall_map_iff]
  apply joinedPrunedVamos_lawful

/-- The main computation produces only `List (List ℕ)` objects which are "normalized Vámos-like".
Informally: Theorem 2 -/
theorem mainComputation_normalizedVamosLike: mainComputation.Forall List.NormalizedVamosLike := by
  unfold mainComputation
  rw [List.forall_map_iff]
  apply joinedPrunedVamos_normalized

/-- The list of `List (List ℕ)` objects provided by the main computation are mutually
non-isomorphic (up to permutation of 0, 1, 2, ... 7).
Informally: Theorem 3 -/
theorem nonisomorphic_mainComputation :
    mainComputation.Pairwise (fun l₁ l₂ ↦ ¬ permutationsComparison 8 l₁ l₂) := by
  unfold mainComputation
  rw [List.pairwise_map]
  apply nonisomorphic_joinedPrunedVamos

/-- Any "normalized Vámos-like" `List (List ℕ)` object which is valid as an (8, 4) sparse paving
matroid is isomorphic to one of the objects on the list provided by the main computation.
Informally: Theorem 4 -/
theorem mainComputation_exhausts {l : List (List ℕ)} (hl₁ : LawfulSparsePavingMatroid 8 4 l)
    (hl₂ : l.NormalizedVamosLike) :
    ∃ l' ∈ mainComputation, permutationsComparison 8 l l' := by
  sorry


#print axioms mainComputation_normalizedVamosLike
