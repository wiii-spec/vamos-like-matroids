import Matroids.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Sort


open List


lemma List.not_mem_mergeSort (r : α → α → Bool) {l : List α} (h : a ∉ l) :
    a ∉ l.mergeSort r := by
  rw [List.Perm.mem_iff]
  · apply h
  · apply List.mergeSort_perm

lemma List.forall_mergeSort (r : α → α → Bool) {l : List α} {P : α → Prop }
    (h1 : l.Forall P) : (l.mergeSort (r)).Forall P := by
  rw [List.forall_iff_forall_mem]
  intro i hi
  rw [List.forall_iff_forall_mem] at h1
  apply h1
  rw [List.Perm.mem_iff]
  apply hi
  apply List.Perm.symm
  apply List.mergeSort_perm




lemma sort_map_sort {L : List X} [LinearOrder X] {f: X → X}:
    List.sort ( List.map f L.sort) = List.sort (List.map f L) := by
  sorry

lemma sort_flatten_sort {X :Type} [LinearOrder X] (L : List (List X)) :
    List.sort (List.flatten (List.sort L)) = List.sort (List.flatten (L)) := by
  match L with
  | [] => simp [List.sort]
  | a :: ll =>
    simp
    have h := sort_flatten_sort ll
    match a with
    |[] =>
      simp
      sorry
    |c :: l =>
      sorry
-- proof idea: consider number of occurence in each list, should be the same

lemma sort_flatten_map_sort {X : Type} [LinearOrder X] (L : List (List X)):
    List.sort (List.flatten (List.map List.sort L)) = List.sort (List.flatten (L)) := by
  sorry


-- look up `List.eq_of_perm_of_sorted`
lemma mergeSort_of_perm_eq {L₁ L₂ : List X} (P : X → X → Bool) (hL : L₁.Perm L₂) :
    List.mergeSort L₁ P = List.mergeSort L₂ P :=
  sorry


lemma mergeSort_sorted_list_X_Nat [LinearOrder X] (l : List (X × Nat)) :
    (l.mergeSort (fun (x1, n1) (x2, n2) ↦ x1 ≤ x2)).Sorted (fun (x1, _) (x2, _) ↦ x1 ≤ x2) := by
  sorry
