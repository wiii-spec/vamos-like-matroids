import Matroids.Verification.Basic
import Matroids.Verification.Miscellaneous
import Matroids.Count
import Matroids.PartialMatroid
import Mathlib.Data.List.Destutter

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

/- If the operation `groupByValue` is performed on a list of objects of type `α`, all of which have
a certain property `P`, then the objects of type `α`'s in the output list of lists will all have
poperty `P`.
(will probably get used for Theorem 1) -/
lemma mem_groupByValue (P : α → Prop) (f : α → List ℕ) (A : List α) (hA : ∀ a ∈ A, P a) :
    ∀ l ∈ (groupByValue A f), ∀ a ∈ l, P a := by
  have H := forall_groupByValue (P := P) f A
  simp [List.forall_iff_forall_mem] at H
  exact H hA

--

lemma sort_map_sort {L : List X} [LinearOrder X] {f: X → X}:
    List.sort ( List.map f L.sort) = List.sort (List.map f L) := by
  sorry

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

--UPDATE: Not needed as all 3 invariant are PartialMatroid → ℕ

theorem ne_of_groupByValue' {A : List PartialMatroid} {f: PartialMatroid → X} [LinearOrder X]
    {i j : Fin (groupByValue (A.mergeSort (f · < f ·)) f).length}
    (h : i ≠ j) {x y : PartialMatroid}
    (hx : x ∈ (groupByValue (A.mergeSort (f · < f ·)) f).get i)
    (hy : y ∈ (groupByValue (A.mergeSort (f · < f ·)) f).get j) :
    f x ≠ f y := by
  contrapose! h
  -- unfold groupByValue at hx hy
  -- simp at hx hy
  sorry

-- this should be a simple consequence of the above but there are BEq issues, skip for now
theorem ne_of_groupByValue {A : List PartialMatroid} {f: PartialMatroid → List Nat}
    {i j : Fin (groupByValue (A.mergeSort (f · < f ·)) f).length}
    (h : i ≠ j) {x y : PartialMatroid}
    (hx : x ∈ (groupByValue (A.mergeSort (f · < f ·)) f).get i)
    (hy : y ∈ (groupByValue (A.mergeSort (f · < f ·)) f).get j) :
    f x ≠ f y := by
  -- apply ne_of_groupByValue' h hx hy
  sorry

lemma countAux_of_map {L : List X} [LinearOrder X] {f : X → X} (ha : f.Bijective):
    countAux L = countAux (L.map f):= by
  unfold countAux
  match L with
  | [] => simp
  | [a] => simp
  | a :: b :: l =>
    simp
    have induction_h := @countAux_of_map X (b :: l) (inferInstance) f ha
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

lemma count_of_map {L : List X} [LinearOrder X] {f : X → X} (ha : f.Bijective):
    count L = count (L.map f):= by
  unfold count
  unfold countAux'
  rw[countAux_of_map ha]
  simp

theorem check_stick_eq_destutter (L : List X) [LinearOrder X] :
    check_stick L = L.destutter Ne := by
  match L with
  | [] => simp [check_stick]
  | [a] => simp [check_stick]
  | a :: b :: l =>
    rw [check_stick]
    dsimp [List.destutter]
    rw [List.destutter', check_stick_eq_destutter (b :: l)]
    simp [List.destutter]
    split_ifs with H
    · rw [H]
    · rfl

/-Everything in check_stick is in the original list-/
lemma check_stick_included (L : List X) [DecidableEq X] : ∀ x ∈ L.destutter Ne, x ∈ L :=
  fun _ ↦ (L.destutter_sublist Ne).mem

/-If L is sorted by ≤ , check_stick L is also Sorted by < -/
lemma check_stick_sorted {L : List X} [LinearOrder X] (h : L.Sorted ( · ≤ · )) :
    (L.destutter Ne).Pairwise ( · < · ) := by
  rw [← check_stick_eq_destutter]
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
      rw [← check_stick_eq_destutter] at induct_h
      exact induct_h
    · rw [if_neg hab]
      simp
      constructor
      · intro x hx
        have h_le := check_stick_included (b :: l)
        rw [← check_stick_eq_destutter] at h_le
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
      · rw [← check_stick_eq_destutter] at induct_h
        apply induct_h


lemma sort_stick (L : List X) [LinearOrder X]:
    Sticking (L.sort) := by
  unfold Sticking
  -- have h := check_stick_sorted L
  --probabily need to change L.sort into ≤, because I need to use L.sort (<) is Sorted (≤) here
  --proof is simple, just need syntax to change < to ≠
  sorry

lemma empty_stick {L : List X} [LinearOrder X] (hl : L = []):
    Sticking L := by
  rw[hl]
  unfold Sticking
  unfold check_stick
  simp


-- lemma tail_stick {L : List X} [LinearOrder X] (hl : Sticking L):
--     Sticking L.tail := by
--   unfold List.tail
--   match L with
--   | [] =>
--     simp
--     exact hl
--   | a :: l1 =>
--     simp
--     unfold Sticking at hl
--     unfold check_stick at hl
--     match l1 with
--     | [] =>
--       apply empty_stick
--       simp
--     | b :: l =>
--       sorry

lemma map_stick_stick {L : List X} [LinearOrder X] (hl : Sticking L) {f : X → X} (hf: f.Bijective):
    Sticking (L.map f) := by
  match L with
  |[] => exact hl
  |[a] =>
    simp
    unfold Sticking
    unfold check_stick
    simp
  | a :: b :: l =>
    --need b::l sticking, should be simple
    -- have inductive_hl := map_stick_stick (@tail_stick X (a :: b :: l))
    sorry


-- need additional condition: all element in second list is nonzero (h_nonzero)
theorem destutter_expand [DecidableEq X] (l : List (X × Nat)) (h : List.Chain' Ne (l.map Prod.fst))
  (h_nonzero : List.Forall (fun p => p ≠ 0) (l.map Prod.snd)):
    List.destutter Ne (expand l) = l.map Prod.fst := by
  unfold expand
  match l with
  |[] =>
    simp
  | (x , n) :: l =>
    have h1 :=  List.Chain'.tail h
    simp at h1
    simp at h_nonzero
    have ⟨ n_nonzero, hl⟩ := h_nonzero
    rw[<-List.forall_map_iff] at hl
    have induction_hl := destutter_expand l h1 hl
    simp
    unfold List.destutter
    unfold List.Chain' at h
    simp at h
    induction n with
    | zero =>
      trivial
    | succ n ih1 =>
      induction n with
      | zero =>
        simp
        unfold List.destutter'
        match l with
        | [] =>
          simp
        | (y, m) :: l =>
          simp
          simp at hl
          have hm := Nat.exists_eq_succ_of_ne_zero hl.1
          obtain ⟨ k, hk⟩ := hm
          rw[hk]
          simp
          simp at h
          rw[if_neg h.1]
          simp
          unfold expand List.destutter at induction_hl
          rw[hk] at induction_hl
          simp at induction_hl
          exact induction_hl
      | succ k _ =>
        simp at ih1
        simp
        rw[<-List.forall_map_iff] at ih1
        exact ih1 hl



theorem sticking_expand_iff_pairwise_ne [LinearOrder X] (l : List (X × Nat))
  (hl : List.Chain' Ne (List.map Prod.fst l))
  (h_nonzero : List.Forall (fun p => p ≠ 0) (l.map Prod.snd)):
    Sticking (expand l) ↔ (l.map Prod.fst).Pairwise Ne := by
  unfold Sticking
  rw [check_stick_eq_destutter]
  rw [destutter_expand ]
  exact hl
  exact h_nonzero

theorem countAux'_expand [DecidableEq X] (l : List (X × Nat)) (h : List.Chain' Ne (l.map Prod.fst))
  (h_nonzero : List.Forall (fun p => p ≠ 0) (l.map Prod.snd)) :
    countAux' (expand l) = l.map Prod.snd := by

  unfold expand
  match l with
  |[] =>
    unfold countAux'
    simp
  | (x , n) :: l =>
    have h1 :=  List.Chain'.tail h
    simp at h1
    simp at h_nonzero
    have ⟨ n_nonzero, hl⟩ := h_nonzero
    rw[<-List.forall_map_iff] at hl
    have induction_hl := countAux'_expand l h1 hl
    simp
    unfold countAux'
    unfold List.Chain' at h
    simp at h
    induction n with
    | zero =>
      trivial
    | succ n ih1 =>
      induction n with
      | zero =>
        simp
        unfold countAux
        match l with
        | [] =>
          simp
        | (y, m) :: l =>
          simp
          simp at hl
          have hm := Nat.exists_eq_succ_of_ne_zero hl.1
          obtain ⟨ k, hk⟩ := hm
          rw[hk]
          simp
          simp at h
          rw[if_neg h.1]
          simp
          unfold expand countAux' at induction_hl
          rw[hk] at induction_hl
          simp at induction_hl
          exact induction_hl
      | succ k _ =>
        simp at ih1
        simp
        rw[<-List.forall_map_iff] at ih1
        apply ih1 at hl
        unfold countAux
        simp
        exact hl

theorem expand_destutter_countAux' [DecidableEq X] (l : List X) :
    expand (List.zip (l.destutter Ne) (countAux' l)) = l := by
  unfold expand countAux'

  simp
  match l with
  | [] =>
    simp
  | [a] =>
    simp
  | a :: b :: l =>
    have ih := expand_destutter_countAux' ( b :: l)
    rw[List.destutter_cons_cons l (Ne)]
    by_cases h : a = b
    · rw[h]
      unfold countAux
      unfold expand at ih
      simp at ih
      simp
      -- simp
      sorry
    · unfold countAux
      simp
      rw[if_neg h]
      rw[if_neg h]
      dsimp
      exact congrArg (List.cons a) ih

lemma destutter_countAux'_length_eq  [DecidableEq X] (L : List X) :
    (L.destutter Ne).length = (countAux' L).length := by
  match L with
  | [] =>
    unfold countAux'
    simp
  | [a] =>
    unfold countAux'
    unfold countAux
    simp
  | a :: b :: l =>
    have := destutter_countAux'_length_eq (b :: l)
    by_cases h : a = b
    · rw[h]
      unfold List.destutter countAux'
      simp
      unfold List.destutter countAux' at this
      simp at this
      unfold countAux
      simp
      exact this
    · unfold List.destutter countAux' List.destutter'
      simp
      rw[if_neg h]
      simp
      unfold countAux
      simp
      rw[if_neg h]
      simp
      unfold List.destutter countAux' at this
      simp at this
      exact this

lemma countAux'_non_zero [DecidableEq X] (L : List X) :
     (countAux' L).Forall (fun p => p ≠ 0):= by
  match L with
  | [] =>
    simp
  | [a] =>
    simp
  | a :: b :: l =>
    by_cases h : a = b
    · have ih := countAux'_non_zero ( b :: l)
      unfold countAux'
      simp
      unfold countAux
      simp
      rw[if_pos h]
      simp
      unfold countAux' at ih
      simp at ih
      exact ih.2
    · have ih := countAux'_non_zero ( b :: l)
      unfold countAux'
      simp
      unfold countAux
      simp
      rw[if_neg h]
      simp
      unfold countAux' at ih
      simp at ih
      exact ih


theorem List.exists_eq_expand [DecidableEq X] (L : List X) :
    ∃ l : List (X × Nat), L = expand l ∧ Chain' Ne (l.map Prod.fst)
  ∧ List.Forall (fun p => p ≠ 0) (List.map Prod.snd l) := by
  -- used in expand_destutter_countAux'
  use List.zip (L.destutter Ne) (countAux' L)
  constructor
  · rw[ expand_destutter_countAux' L]
  · rw[ @List.map_fst_zip X Nat (destutter Ne L) (countAux' L)]
    · constructor
      · apply List.destutter_is_chain'
      · rw[List.map_snd_zip]
        · apply countAux'_non_zero
        · rw[destutter_countAux'_length_eq]
    · rw[destutter_countAux'_length_eq]

-- we think we don't need a side condition here?
theorem sort_expand [LinearOrder X] (l : List (X × Nat)) :
    List.sort (X := X) (expand L) = expand (l.mergeSort (fun (x1, n1) (x2, n2) ↦ x1 < x2)) := by
  sorry

-- theorem
--main difficulty
/-
Sticking l:
check_stick l = perm f check_stick L.sort
and
countAux L = f countAux sort L
-/




lemma countAux_perm_of_stick {L : List X} [LinearOrder X] (hL : Sticking L) :
    (countAux' L).Perm (countAux' (List.sort L)) := by
  obtain ⟨l, rfl, hl, hne0⟩ := L.exists_eq_expand
  have h_perm : List.Perm (List.mergeSort (fun x x_1 => x.1 < x_1.1) l) l
  · apply List.perm_mergeSort
  rw [sort_expand l]
  dsimp
  rw [countAux'_expand]
  rw [countAux'_expand]
  · symm
    -- idea should be in
    -- apply List.perm_mergeSort
    apply List.Perm.map
    exact h_perm
  · rw [sticking_expand_iff_pairwise_ne _ hl] at hL
    apply List.Pairwise.chain'
    apply List.Pairwise.perm hL
    · apply List.Perm.map
      exact id (List.Perm.symm h_perm)
    · tauto
    -- should follow from these three
    -- List.Pairwise.chain'
    -- List.Pairwise.perm
    -- List.perm_mergeSort
    exact hne0
  · simp
    simp at hne0
    apply List.Forall.perm h_perm.symm hne0
  exact hl
  exact hne0



lemma count_of_stick {L : List X} [LinearOrder X] (hl : Sticking L) :
    count L = count (List.sort L) := by
  unfold count
  unfold List.sort
  have := countAux_perm_of_stick hl
  -- since mergeSort is a permutation of the original list,
  -- LHS and RHS are permutations of each other too
  -- since they are also both sorted they must be the same
  apply mergeSort_of_perm_eq
  exact this

-- #check Tuple.comp_sort_eq_iff_monotone

lemma count_of_sort_map (L : List (List X)) {f : X → X} (hf : f.Bijective) [LinearOrder X]:
    count (List.sort (List.join (List.map (List.map f) L))) = count (List.sort (List.join L)) := by
  rw [← List.map_join]
  rw[← sort_map_sort]
  have h2 := map_stick_stick (sort_stick L.join) hf
  rw[← count_of_stick h2]
  rw[← count_of_map hf]
  -- unfold count
  -- simp [-List.map_join]
  -- congr! 3
