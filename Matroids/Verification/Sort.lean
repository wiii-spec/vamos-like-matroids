import Matroids.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Sort


open List

/--mergeSort with the less than relation has no duplicates-/ -- Wrong lemma, counterexample below
lemma List.mergeSort_no_duplicates [PartialOrder α] {l : List α} [DecidableRel ((· : α) < ·)]:
   Nodup (mergeSort (· < ·) l) :=

  sorry

#eval mergeSort (· < ·) [1,1,2]



lemma List.split_of_sublist {α : Type*} {l : List α} :
    List.Sublist (l.split).1 l ∧ List.Sublist (l.split).2 l:= by
  match l with
  | [] => simp
  | a :: l =>
    unfold split
    simp
    have ih := List.split_of_sublist (l := l)
    constructor
    · exact ih.2
    · apply List.sublist_cons_of_sublist
      exact ih.1


/- Paused for the moment, we will focus on proving sorted_mergeSort for the less than relationship-/
lemma List.mergeSort_lt_eq_mergeSort_le [LinearOrder α] {l : List α}
    (h_nodup : l.Nodup):
    mergeSort (· < ·) l = mergeSort (· ≤ ·) l  := by
  match l with
  | [] => simp
  | [a] => simp
  | a :: b :: l =>
    unfold mergeSort
    simp
    have ha1 : List.Sublist (a :: (split l).1) (a :: b :: l) := by
      apply List.Sublist.cons_cons
      apply List.sublist_cons_of_sublist
      apply List.split_of_sublist.1
    have hb2 : List.Sublist (b :: (split l).2) (a :: b :: l) := by
      apply List.sublist_cons_of_sublist
      apply List.Sublist.cons_cons
      apply List.split_of_sublist.2
    have ha := List.Nodup.sublist ha1 h_nodup
    have hb := List.Nodup.sublist hb2 h_nodup
    -- have iha := List.mergeSort_lt_eq_mergeSort_le ha
    -- have ihb := List.mergeSort_lt_eq_mergeSort_le hb
    -- simp_rw[iha,ihb]
    -- unfold merge
    -- have : (split l = ((split l).1, (split l).2)) := by simp
    -- have := perm_split this

    -- simp at h_nodup
    -- obtain ⟨hab, _, _⟩ := h_nodup
    -- rw[or_iff_not_and_not] at hab
    -- simp at hab
    -- match mergeSort (fun x x_1 => x ≤ x_1) (a :: (split l).1), mergeSort (fun x x_1 => x ≤ x_1) (b :: (split l).2) with
    -- | [], [] => simp
    -- | [], l' => simp
    -- | a :: l, [] => simp
    -- | (x1 :: l1 as full1), (x2 :: l2 as full2)=>
    --   simp

    -- conv =>
    --   lhs
    --   arg 6
    --   intro x1 x2 x3 x4
      -- rw[lt_iff_le_and_ne (a := x1) (b := x3)]

    sorry

lemma List.mergeSort_lt_eq_mergeSort_le' [LinearOrder α] {l : List α}:
    mergeSort (· < ·) l = mergeSort (· ≤ ·) l  := by
  sorry

lemma List.not_mem_mergeSort (r : α → α → Prop) [h: DecidableRel r] {l : List α} (h : a ∉ l) :
    a ∉ l.mergeSort r := by
  rw [List.Perm.mem_iff]
  · apply h
  · apply List.perm_mergeSort

lemma List.forall_mergeSort (r : α → α → Prop) [h: DecidableRel r] {l : List α} {P : α → Prop }
    (h1 : l.Forall P) : (l.mergeSort (r)).Forall P := by
  rw [List.forall_iff_forall_mem]
  intro i hi
  rw [List.forall_iff_forall_mem] at h1
  apply h1
  rw [List.Perm.mem_iff]
  apply hi
  apply List.Perm.symm
  apply List.perm_mergeSort



/- PENDING theorem: If you have two different sorted lists and you run merge on them,
then the result has to be sorted. Take a look at theorem Sorted.merge-/


theorem sorted_mergeSort_lt [PartialOrder α] {l : List α} [DecidableRel ((· : α) < ·)] :
    ∀ l : List α, Sorted (· < ·) (mergeSort (· < ·) l)
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: l => by
    simp [mergeSort]

    sorry



lemma sort_map_sort {L : List X} [LinearOrder X] {f: X → X}:
    List.sort ( List.map f L.sort) = List.sort (List.map f L) := by
  sorry

lemma sort_join_sort {X :Type} [LinearOrder X] (L : List (List X)) :
    List.sort (List.join (List.sort L)) = List.sort (List.join (L)) := by
  match L with
  | [] => simp [List.sort]
  | a :: ll =>
    simp
    have h := sort_join_sort ll
    match a with
    |[] =>
      simp
      sorry
    |c :: l =>
      sorry
-- proof idea: consider number of occurence in each list, should be the same

lemma sort_join_map_sort {X : Type} [LinearOrder X] (L : List (List X)):
    List.sort (List.join (List.map List.sort L)) = List.sort (List.join (L)) := by
  sorry


lemma mergeSort_of_perm_eq {L₁ L₂ : List X} (P : X → X → Prop) [DecidableRel P] (hL : L₁.Perm L₂) :
    List.mergeSort P L₁ = List.mergeSort P L₂ := by
  sorry


/- existing lemma in mathlib-/
theorem List.mergeSort_perm {α : Type u_1} (l : List α) (le : α → α → Prop) [DecidableRel le]:
    (l.mergeSort le).Perm l := by
  sorry


lemma mergeSort_sorted_list_X_Nat [LinearOrder X] (l : List (X × Nat)) :
    (l.mergeSort (fun (x1, n1) (x2, n2) ↦ x1 < x2)).Sorted (fun (x1, _) (x2, _) ↦ x1 ≤ x2) := by sorry



lemma mergeSort_lt_le_eq_List_X_Nat [LinearOrder X] (l : List (X × Nat)) :
    l.mergeSort (fun (x1, n1) (x2, n2) ↦ x1 < x2) = l.mergeSort (fun (x1, n1) (x2, n2) ↦ x1 ≤ x2) := by
  sorry
