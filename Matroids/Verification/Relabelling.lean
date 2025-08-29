import Matroids.Verification.Basic
import Matroids.Relabelling
import Matroids.Verification.Count



lemma mem_of_mem_pruning {lA : List (PartialMatroid)} {A : PartialMatroid}
    (hA : A ∈ pruning lA) :
    A ∈ lA := by
  induction lA with
  | nil =>
    rw[pruning] at hA
    apply hA
  | cons h t IH =>
    simp[pruning] at hA
    split_ifs at hA
    · simp
      apply IH at hA
      right
      apply hA
    · simp
      apply IH at hA
      right
      apply hA
    · simp
      simp at hA
      obtain hAA | hAAA := hA
      left
      apply hAA
      right
      apply IH hAAA

-- not currently used 2025-08-28
lemma mem_pruning  (lA : List (PartialMatroid)):
    List.Sublist (pruning lA) lA := by
  sorry

/-- If `A` is a list of `PartialMatroid`s, all of which are valid (n, r)-sparse paving matroids,
then when the `pruning` operation is performed, every `PartialMatroid` in the the resulting
list of partial matroids is still a valid (n, r)-sparse paving matroids. -/
lemma pruning_lawful (lA : List PartialMatroid)
    (hA : lA.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (pruning lA).Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid) := by
  induction lA with
  | nil => simp
  | cons h t IH =>
    simp at hA
    obtain ⟨h_ok, t_ok⟩ := hA
    apply IH at t_ok
    simp [pruning]
    split_ifs
    · exact t_ok
    · exact t_ok
    · simp
      constructor
      · exact h_ok
      · exact t_ok


lemma pruning_normalized (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (pruning A).Forall (fun M ↦ List.NormalizedVamosLike M.matroid) := by
  induction A with
  | nil => simp
  | cons h t IH =>
    simp at hA
    obtain ⟨h_ok, t_ok⟩ := hA
    apply IH at t_ok
    simp [pruning]
    split_ifs
    · exact t_ok
    · exact t_ok
    · simp
      constructor
      · exact h_ok
      · exact t_ok

theorem nonisomorphic_pruning {a : List PartialMatroid} :
    List.Pairwise (fun A₁ A₂ => ¬permutationsComparison 8 A₁.matroid A₂.matroid = true) (pruning a) := by
  unfold pruning
  match a with
  | [] => simp
  | h :: l =>
    simp
    have induct_h := @nonisomorphic_pruning l
    simp at induct_h
    split
    · apply induct_h
    · split
      · apply induct_h
      · case inr.inr ha =>
        rw [List.pairwise_cons]
        constructor
        · simp at ha
          exact ha
        · apply induct_h

-- not currently used 2025-08-28, we think that it will be used in theorem 4
/-- If `A` is a list of `PartialMatroid`s, then when the `pruning` operation is performed, every
`PartialMatroid` in `A` is isomorphic (up to permutation of 0, 1, 2, ... n - 1) to one of the
`PartialMatroid`s in the pruned list. -/
theorem permutationsComparison_mem_pruning_of_mem (A : List PartialMatroid) :
    A.Forall fun M ↦ ∃ M' ∈ pruning A, permutationsComparison n M.matroid M'.matroid := by
  induction A with
  | nil => simp[pruning]
  | cons h t IH =>
    rw [List.forall_iff_forall_mem]
    intro p hp
    rw [List.forall_iff_forall_mem] at IH
    simp at hp

    obtain hp1 | hp2 := hp
    · subst hp1
      unfold pruning
      clear IH
      simp
      split_ifs with h
      obtain ⟨ q, hq ⟩ := h
      obtain ⟨ a, ha ⟩ := hq
      unfold specialPermutationsComparison at ha
      use q
      constructor
      apply a
      unfold permutationsComparison

      sorry
      sorry
      sorry
    sorry



lemma sort_of_length [LinearOrder X] {A : List X}:
    (A.sort).length = A.length := by
  refine (List.Perm.length_eq ?p).symm
  unfold List.sort
  exact List.Perm.symm (List.perm_mergeSort (fun x x_1 => x < x_1) A)

lemma map_of_length {A : List α} {g : α → β }:
    (A.map g).length = A.length := by
  exact List.length_map A g

theorem foo_sameUpToRelabelling {A B : List (List Nat)} {g : Nat → Nat}
    {h : sameUpToRelabelling A B g} : A.length = B.length := by
  unfold sameUpToRelabelling at h
  simp at h
  have hA1 := @sort_of_length (List Nat) inferInstance (List.map List.sort A)
  have hB1 := @sort_of_length (List Nat) inferInstance (List.map List.sort (relabelling B g))
  rw[map_of_length] at hA1 hB1
  conv at hB1 =>
    · rhs
      unfold relabelling
      rw[map_of_length]
  rw[<- hA1, <- hB1]
  exact congrArg List.length (id h.symm)

  -- unfold List.sort at h

theorem length_eq_of_permutationsComparison {A B : List (List Nat)}
    {h : permutationsComparison 8 A B} : A.length = B.length := by
  unfold permutationsComparison at h
  rw [List.any_eq_true] at h
  obtain ⟨g, hg⟩ := h
  obtain ⟨_, h⟩ := hg
  apply foo_sameUpToRelabelling at h
  apply h

-- now?
theorem nonisomorphic_of_length {A B : List (List Nat)} (h : A.length ≠ B.length) :
    ¬ permutationsComparison 8 A B := by
  intro h₁
  apply h
  clear h
  apply length_eq_of_permutationsComparison
  apply h₁



----TODO: not difficult
lemma list_prop (P : β → Prop) (l : List α) (f : α → β ) (hp : ∀a ∈ l, P (f a)):
    ∀g ∈ List.map f l, P g := by
  intro g hg
  rw [@List.mem_map] at hg
  obtain ⟨a, ha, hfa⟩ := hg
  specialize hp a ha
  rw[hfa] at hp
  exact hp



lemma List.relabelling_mem_mul (l₁ l₂ : List (Nat → Nat)) (hg : g ∈ l₁ * l₂) :
    ∃ g₁ ∈ l₁, ∃ g₂ ∈ l₂, g = g₁ ∘ g₂ := by
  change g ∈ (l₁.product l₂).map (Function.uncurry Function.comp) at hg
  rw[@List.mem_map] at hg
  simp at hg
  obtain ⟨a, b, hab, habg⟩ := hg
  rw [@pair_mem_product] at hab
  use a
  constructor
  · exact hab.1
  · use b
    · constructor
      · exact hab.2
      · rw[habg]


lemma permutation_bijective (n : ℕ):
    ∀ f ∈ permutation n, Function.Bijective f := by
  match n with
  | 0 =>
    unfold permutation
    simp
    exact Function.bijective_id
  | k + 1 =>
    have induction_h := permutation_bijective k
    unfold permutation
    simp
    intro g hg
    -- apply list_prop Function.Bijective (List.range (k+1)) (Equiv.swapCore k)
    -- simp at hg
    apply List.relabelling_mem_mul at hg
    obtain ⟨ g₁, hg1, g₂ , hg2, hgg⟩ := hg
    specialize induction_h g₂ hg2
    rw[hgg]
    have : Function.Bijective g₁ := by
      apply list_prop Function.Bijective (List.range (k+1)) (Equiv.swapCore k)
      · intro a _
        apply Function.Involutive.bijective
        intro x
        exact Equiv.swapCore_swapCore x k a
      · exact hg1
    exact Function.Bijective.comp this induction_h




lemma join_of_relabelling {L : List (List Nat)} {f : ℕ → ℕ} :
  List.join (relabelling L f) = List.map f (List.join L) := by
  unfold relabelling
  simp

lemma count_of_relabelling {L : List (List Nat)} {f : ℕ → ℕ} (ha : f ∈ permutation 8) :
  count (List.sort (List.join (List.sort (List.map List.sort (relabelling L f)))))
  = count (List.sort (List.join L)) := by
  rw[sort_join_sort]
  rw[sort_join_map_sort]
  rw[join_of_relabelling]
  simp
  have hf := permutation_bijective 8
  specialize hf f ha
  have dummy := count_of_sort_map L hf
  convert dummy
