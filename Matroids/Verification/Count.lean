import Matroids.Verification.Basic
import Matroids.Count
import Matroids.PartialMatroid

/- Lemma for count (related to Theorem 1):  If the input is an list of partial matroids
(order does matter, for both the lists and for the members) with range i < n and lenght = r, then
the output will be a list of natural numbers that counts the single ocurrences of lawful sparse
paving matroids-/

lemma forall_groupByValueAux (f : α → List ℕ) (A : List α) (hA : A.Forall P) :
    (groupByValueAux f A).1.Forall P ∧ (groupByValueAux f A).2.Forall (fun l ↦ l.Forall P) := by
  match A with
  | [] => simp [groupByValueAux]
  | [pm] =>
    simp [groupByValueAux]
    apply hA
  | a :: b :: t =>
    simp [groupByValueAux]
    simp at hA
    obtain ⟨h_ok, t_ok⟩ := hA
    obtain ⟨th_ok, tt_ok⟩ := t_ok
    have H := forall_groupByValueAux f (b :: t) (P := P)
    have tt_ok1 : List.Forall P (b :: t)
    · simp
      constructor
      · exact th_ok
      · exact tt_ok
    apply H at tt_ok1
    obtain ⟨tth_ok1, ttt_ok1⟩ := tt_ok1
    constructor
    . split_ifs
      · simp
        constructor
        · exact h_ok
        · apply tth_ok1
      · simp
        exact h_ok
    · split_ifs
      · simp
        exact ttt_ok1
      · simp
        constructor
        · apply tth_ok1
        · exact ttt_ok1


/- If the operation `groupByValue` is performed on a list of objects of type `α`, all of which have
a certain property `P`, then the objects of type `α`'s in the output list of lists will all have
poperty `P`.
(will probably get used for Theorem 1) -/
lemma forall_groupByValue (f : α → List ℕ) (A : List α) (hA : A.Forall P) :
    (groupByValue A f).Forall (fun l ↦ l.Forall P) := by
  unfold groupByValue
  simp
  apply forall_groupByValueAux
  exact hA



--

lemma sort_join_sort {X :Type} [LinearOrder X] (L : List (List X)) :
    List.sort (List.join (List.sort L)) = List.sort (List.join (L)) := by
  match L with
  |[] => simp
  |a :: ll =>
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

-- TODO generalize codomain of `f` to arbitrary linear order output
-- apparently some `BEq` bug
theorem ne_of_groupByValue {A : List PartialMatroid} {f: PartialMatroid → List Nat}
    {i j : Fin (groupByValue (A.mergeSort (f · < f ·)) f).length}
    (h : i ≠ j) {x y : PartialMatroid}
    (hx : x ∈ (groupByValue (A.mergeSort (f · < f ·)) f).get i)
    (hy : y ∈ (groupByValue (A.mergeSort (f · < f ·)) f).get j) :
    f x ≠ f y := by
  sorry


lemma countAux_of_map {L : List Nat} {f : ℕ → ℕ} (ha : f.Bijective):
    countAux L = countAux (L.map f):= by
  unfold countAux
  match L with
  | [] => simp
  | [a] => simp
  | a :: b :: l =>
    simp
    have induction_h := @countAux_of_map (b::l) f ha
    by_cases hab : a = b
    · rw[hab]
      simp
      rw[induction_h]
      simp
    · rw [if_neg hab]
      have : f a ≠ f b := ha.injective.ne hab
      rw[if_neg this]
      simp
      rw[induction_h]
      simp

lemma count_of_map {L : List Nat} {f : ℕ → ℕ} (ha : f.Bijective):
    count L = count (L.map f):= by
  unfold count
  rw[countAux_of_map ha]


--- sticking part for proofing count_of_sort_map
def Sticking (L : List X) [LinearOrder X]: Prop :=
    (check_stick L).Pairwise ( · ≠ · )


/-Everything in check_stick is in the original list-/
lemma check_stick_included (L : List X) [LinearOrder X] :
    ∀ x ∈ check_stick L, x ∈ L := by
  unfold check_stick
  match L with
  | [] => simp
  | [a] => simp
  | a :: b :: l =>
    have induct_h := check_stick_included (b :: l)
    by_cases hab : a = b
    · rw[hab]
      simp
      simp at induct_h
      exact induct_h
    · simp
      rw[if_neg hab]
      simp at induct_h
      simp
      intro x hx
      specialize induct_h x hx
      exact
        (Relation.reflGen_iff (fun a x => x = b ∨ x ∈ l) a x).mp (Relation.ReflGen.single induct_h)



/-If L is sorted by ≤ , check_stick L is also Sorted by < -/
lemma check_stick_sorted {L : List X} [LinearOrder X] (h : L.Sorted ( · ≤ · )) :
    (check_stick L).Pairwise ( · < · ) := by
  unfold check_stick
  match L with
  | [] => simp
  | [a] => simp
  | a :: b :: l =>
    simp
    have hbl : (b :: l).Sorted ( · ≤ · ) := by
      unfold List.Sorted at h
      simp at h
      refine List.sorted_cons.mpr ?_
      obtain ⟨h1, h2, h3⟩ := h
      unfold List.Sorted
      exact ⟨h2, h3⟩
    have induct_h := check_stick_sorted hbl
    by_cases hab : a = b
    · rw[hab]
      simp
      exact induct_h
    · rw [if_neg hab]
      simp
      constructor
      · intro x hx
        have h_le := check_stick_included (b :: l)
        specialize h_le x hx
        unfold List.Sorted at h
        simp at h
        obtain ⟨ h1, h2⟩ := h
        simp at h_le
        have hbx : b ≤ x := by
          cases h_le with
          | inl hxb =>
            exact Eq.ge hxb
          | inr hxl =>
            obtain ⟨ h3, h4 ⟩ := h2
            specialize h3 x hxl
            exact h3
        obtain ⟨ h_a_le_b, dummy⟩ := h1
        exact lt_of_lt_of_le (lt_of_le_of_ne h_a_le_b hab) hbx
      · apply induct_h


lemma sort_stick (L : List X) [LinearOrder X]:
    Sticking (L.sort) := by
  unfold Sticking
  -- have h := check_stick_sorted L
  --probabily need to change L.sort into ≤, because I need to use L.sort (<) is Sorted (≤) here
  --proof is simple, just need syntax to change < to ≠
  sorry


lemma count_of_sort_map {L : List (List ℕ)} {f : ℕ → ℕ} (ha : f.Bijective) :
    count (List.sort (List.join (List.map (List.map f) L))) = count (List.sort (List.join L)) := by
  rw [← List.map_join]
  -- unfold count
  -- simp [-List.map_join]
  -- congr! 3
  sorry
