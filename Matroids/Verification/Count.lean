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

lemma sort_join_sort {α :Type} [LinearOrder α] (L : List (List α)) :
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

lemma sort_join_map_sort (L : List (List Nat)) :
  List.sort (List.join (List.map List.sort L)) = List.sort (List.join (L)) := by
  sorry

-- TODO generalize codomain of `f` to arbitrary linear order output
-- apparently some `BEq` bug
theorem ne_of_groupByValue {A : List PartialMatroid} {f: PartialMatroid → List ℕ} --[LinearOrder X]
    {i j : Fin (groupByValue (A.mergeSort (f · < f ·)) f).length}
    (h : i ≠ j) {x y : PartialMatroid}
    (hx : x ∈ (groupByValue (A.mergeSort (f · < f ·)) f).get i)
    (hy : y ∈ (groupByValue (A.mergeSort (f · < f ·)) f).get j) :
    f x ≠ f y := by
  sorry


lemma countAux_of_relabelling {L : List Nat} {f : ℕ → ℕ} (ha : f.Bijective):
  countAux L = countAux (L.map f):= by
  unfold countAux
  match L with
  | [] => simp
  | [a] => simp
  | a :: b :: l =>
    simp
    have induction_h := @countAux_of_relabelling (b::l) f ha
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
