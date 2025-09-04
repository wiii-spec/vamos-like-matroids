import Matroids.Verification.Basic
import Matroids.Verification.Miscellaneous
import Matroids.Verification.Sort
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
    have tt_ok1 : List.Forall P (b :: t) := by
      simp
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


theorem lt_of_groupByValueAux_Sorted {X : Type u_1} {A : List PartialMatroid} {f : PartialMatroid → X} [inst : LinearOrder X]
    {i j : Fin (List.length ((groupByValueAux f A).1 :: (groupByValueAux f A).2))} (h : i < j) {x y : PartialMatroid}
    (hx : x ∈ List.get ((groupByValueAux f A).1 :: (groupByValueAux f A).2) i)
    (hy : y ∈ List.get ((groupByValueAux f A).1 :: (groupByValueAux f A).2) j)
    (hA : List.Sorted (fun x1 x2 => f x1 ≤ f x2) A) : f x < f y := by
  simp at hx hy
  match A with
  | [] =>
    unfold groupByValueAux at hx
    simp at hx
  | [a] =>
    simp at i j
    change Fin (1) at i
    change Fin (1) at j
    have hij : i = j := Subsingleton.elim i j
    have h := h.ne
    contradiction
    -- change x ∈ ([a] :: [])[↑i] at hx
    -- set P := groupByValueAux f [a] with hP
  | a :: b :: A =>
    sorry
    -- unfold groupByValueAux at hx hy
    -- let P := (f a == f b) = true
    -- have H : P = true := sorry
    -- change Fin (List.length (List.cons (Prod.fst (ite P _ _)) (Prod.snd (ite P _ _)))) at i
    -- change Fin (List.length (List.cons (Prod.fst (ite _ _ _)) (Prod.snd (ite _ _ _)))) at j
    -- simp at hx hy
    -- simp_rw [← beq_iff_eq (a := f a) (b := f b)] at hx hy
    -- -- split_ifs at i with hab
    -- clear_value P
    -- subst P
    -- subst H
    -- by_cases hab : (f a == f b) = true
    -- -- <;> split at i <;> split at j <;> rename_i hab' hab'' <;> rw [beq_iff_eq] at hab' hab'' <;> try tauto
    -- · simp_rw [if_pos hab] at hx hy
    --   have ih := lt_of_groupByValueAux_Sorted (X := X) (A := ( b :: A))
    --   sorry
    -- · simp_rw [if_neg hab] at hx hy
    --   sorry

#check List.Sorted.get_strictMono



lemma groupByValue_nonempty {A : List PartialMatroid} {f: PartialMatroid → X} [LinearOrder X]
    {i : Fin (groupByValue A f).length}
    (hA : A ≠ []):
    (groupByValue A f)[i] ≠ [] := by sorry


lemma groupByValue_nonempty' {A : List PartialMatroid} {f: PartialMatroid → X} [LinearOrder X]
    {a : List PartialMatroid}
    (ha : a ∈ groupByValue A f)
    (hA : A ≠ []):
    a ≠ [] := by sorry


lemma groupByValue_head (A : List PartialMatroid) {f: PartialMatroid → X} [LinearOrder X]
    {i : Fin (groupByValue A f).length}
    {x : PartialMatroid}
    (hx : x ∈ (groupByValue A f).get i)
    (hA : A ≠ []):
    f ((groupByValue A f)[i].head (groupByValue_nonempty hA))= f x := by
  simp
  match A with
  | [] =>
    contradiction
  | [a] =>
    simp
    unfold groupByValue at ⊢ hx
    simp at ⊢ hx
    simp_rw[groupByValueAux ] at ⊢ hx
    simp at ⊢ hx
    exact congrArg f (id (Eq.symm hx))
  | a :: b :: l =>
    sorry


-- lemma groupByValue_Sorted (A : List PartialMatroid) {f: PartialMatroid → X} [LinearOrder X]
--     (hA : A ≠ []):

--     List.Sorted (· < · ) (List.map (f ∘ (List.head _ (groupByValue_nonempty' hA))) (groupByValue (X := X) A f) ) := by sorry


theorem lt_of_groupByValue_Sorted {A : List PartialMatroid} {f: PartialMatroid → X} [LinearOrder X]
    {i j : Fin (groupByValue A f).length}
    (h : i < j) {x y : PartialMatroid}
    (hx : x ∈ (groupByValue A f).get i)
    (hy : y ∈ (groupByValue A f).get j)
    (hA : A.Sorted (fun x1 x2 => (f x1) ≤ (f x2))):
    f x < f y := by
  unfold groupByValue at hx hy
  simp at hx hy
  exact lt_of_groupByValueAux_Sorted h hx hy hA

--UPDATE: Not needed as all 3 invariant are PartialMatroid → ℕ
theorem ne_of_groupByValue'_Sorted {A : List PartialMatroid} {f: PartialMatroid → X} [LinearOrder X]
    {i j : Fin (groupByValue A f).length}
    (h : i ≠ j) {x y : PartialMatroid}
    (hx : x ∈ (groupByValue A f).get i)
    (hy : y ∈ (groupByValue A f).get j)
    (hA : A.Sorted (fun x1 x2 => (f x1) ≤ (f x2))):
    f x ≠ f y := by
  contrapose! h
  obtain hij | hij | hij := (lt_trichotomy i j)
  · have := lt_of_groupByValue_Sorted hij hx hy hA
    have := this.ne
    contradiction
  · exact hij
  · have := lt_of_groupByValue_Sorted hij hy hx hA
    have := this.ne.symm
    contradiction


theorem ne_of_groupByValue {A : List PartialMatroid} {f: PartialMatroid → X} [LinearOrder X]
    {i j : Fin (groupByValue (A.mergeSort (f · ≤  f ·)) f).length}
    (h : i ≠ j) {x y : PartialMatroid}
    (hx : x ∈ (groupByValue (A.mergeSort (f · ≤  f ·)) f).get i)
    (hy : y ∈ (groupByValue (A.mergeSort (f · ≤  f ·)) f).get j) :
    f x ≠ f y := by
  apply ne_of_groupByValue'_Sorted
  · exact h
  · exact hx
  · exact hy
  apply sorted_mergeSort_general'




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
      obtain ⟨_, h2, h3⟩ := h
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
            obtain ⟨ h3, _ ⟩ := h2
            specialize h3 x hxl
            exact h3
        obtain ⟨ h_a_le_b, _⟩ := h1
        exact lt_of_lt_of_le (lt_of_le_of_ne h_a_le_b hab) hbx
      · rw [← check_stick_eq_destutter] at induct_h
        apply induct_h


lemma sort_stick (L : List X) [LinearOrder X]:
    Sticking (L.sort) := by
  unfold Sticking
  unfold List.sort
  rw[check_stick_eq_destutter]
  have := List.sorted_mergeSort' (l := L) (r := LE.le)
  have := check_stick_sorted this
  have hh := @ne_of_lt X inferInstance
  apply List.Pairwise.imp hh this
  -- have h := check_stick_sorted L
  --probabily need to change L.sort into ≤, because I need to use L.sort (<) is Sorted (≤) here
  --proof is simple, just need syntax to change < to ≠

lemma empty_stick {L : List X} [LinearOrder X] (hl : L = []):
    Sticking L := by
  rw[hl]
  unfold Sticking
  unfold check_stick
  simp

lemma mem_of_check_stick {α : X }{L : List X} [LinearOrder X] :
    α ∈ L ↔ α ∈ check_stick L := by
  unfold check_stick
  match L with
  | [] => simp
  | [a] => simp
  | a :: b :: l =>
    have ih := @mem_of_check_stick X α (b :: l) inferInstance
    by_cases h : a = b
    · rw[h]
      simp
      simp at ih
      exact ih
    · simp
      rw[if_neg h]
      constructor
      · intro h
        obtain h | h | h := h
        · rw[h]
          simp
        · simp
          right
          rw[<-ih, h]
          simp
        · simp
          right
          rw[<-ih]
          simp
          right
          exact h
      · intro h
        simp at h
        obtain h | h := h
        · rw[h]
          simp
        · rw[<- ih] at h
          simp at h
          exact Or.inr h


lemma tail_stick {a : X}{L : List X} [LinearOrder X]:
    Sticking (a :: L) → Sticking L := by
  intro h
  unfold Sticking at h
  unfold check_stick at h
  match L with
  |[] =>
    apply empty_stick
    simp
  | b :: l =>
    by_cases hab : a = b
    · rw[hab] at h
      simp at h
      exact h
    · simp at h
      rw[if_neg hab] at h
      simp at h
      exact h.2


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
    have hbl := @tail_stick X a ( b :: l) inferInstance hl
    have inductive_hl := map_stick_stick (L := b :: l) hbl hf
    unfold Sticking
    unfold check_stick
    simp
    split_ifs with h
    · exact inductive_hl
    · simp
      constructor
      · unfold Sticking at hl
        unfold check_stick at hl
        rw [if_neg] at hl
        · simp at hl
          simp_rw [<- mem_of_check_stick]
          have hl := hl.1
          simp_rw [<- mem_of_check_stick] at hl
          rw [← List.map_cons]
          suffices f a ∉ List.map f (b :: l) by
            rintro x hx rfl
            exact this hx
          rw[List.mem_map_of_injective ]
          intro ha
          simpa using hl a ha
          exact Function.Bijective.injective hf
        · simp
          exact fun a_1 => h (congrArg f a_1)
      · exact inductive_hl

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
          show dite _ _ _ = _
          simp at h
          rw[dif_neg h.1]
          simp
          unfold expand List.destutter at induction_hl
          rw[hk] at induction_hl
          simp at induction_hl
          exact induction_hl
      | succ k _ =>
        simp [List.replicate_succ] at ih1
        simp [List.replicate_succ]
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
          show Prod.fst (ite _ _ _) = _ ∧ Prod.snd (ite _ _ _) = _
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
        show Prod.fst (ite _ _ _) = _ ∧ Prod.snd (ite _ _ _) = _
        simp
        exact hl

lemma expand_add_one [DecidableEq X]{a : X} {n : Nat} {l : List (X × Nat) }:
    expand ((a,n + 1) :: l) = a :: expand ((a,n) :: l) := by
  unfold expand
  unfold List.replicate
  simp
  match n with
  | 0 => simp
  | n + 1 => simp [List.replicate_succ]


lemma mem_destutter' (R : X → X → Prop) [DecidableRel R] (l : List X) (b : X):
    ∃ m : List X, List.destutter' R b l = b :: m := by
  match l with
  | [] => simp
  | a :: l =>
    unfold List.destutter'
    by_cases h :R b a
    · rw[if_pos h]
      simp
    · rw[if_neg h]
      have ih := mem_destutter' R l b
      exact ih


lemma destuttter_destutter' (R : X → X → Prop) [DecidableRel R] (l : List X) (b : X) :
    List.destutter R ( b :: l) = List.destutter' R b l := by
  unfold List.destutter
  simp

theorem expand_destutter_countAux' [DecidableEq X] (l : List X) :
    expand (List.zip (l.destutter Ne) (countAux' l)) = l := by
  unfold countAux'

  simp
  match l with
  | [] =>
    unfold expand
    simp
  | [a] =>
    unfold expand
    simp [countAux]
  | a :: b :: l =>
    have ih := expand_destutter_countAux' ( b :: l)
    rw[List.destutter_cons_cons l (Ne)]
    by_cases h : a = b
    · rw[h]
      unfold countAux
      unfold countAux' at ih
      simp at ih
      simp
      rw[destuttter_destutter'] at ih
      have h := mem_destutter' Ne l b
      obtain ⟨ m, hm⟩ := h
      rw[hm]
      rw[hm] at ih
      simp
      simp at ih
      rw[ expand_add_one, ih]
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
    simp [countAux']
  | [_] =>
    simp [countAux', countAux]
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


lemma sorted_expand_sorted [LinearOrder X] {l : List (X × Nat)} (l_sorted : l.Sorted (fun (x1, _) (x2, _) ↦ x1 ≤ x2)):
    (expand l).Sorted (· ≤ ·):= by
  match l with
  | [] =>
    unfold expand
    simp
  | (a, n) :: l =>
    unfold List.Sorted at l_sorted
    simp at l_sorted
    have ih1 := sorted_expand_sorted l_sorted.2
    unfold expand
    simp
    induction n with
    | zero =>
      simp
      exact ih1
    | succ n ih2 =>
      simp [List.replicate_succ]
      constructor
      · intro b hb
        obtain hb | hb := hb
        · rw[hb.2]
        · obtain ⟨ l₁, hl₁, hbl₁⟩ := hb
          obtain ⟨ c, m, hcm ⟩ := hl₁
          have l_sorted := l_sorted.1
          specialize l_sorted c m hcm.1
          rw[<- hcm.2] at hbl₁
          rw[List.mem_replicate] at hbl₁
          rw[<- hbl₁.2] at l_sorted
          exact l_sorted
      exact ih2


lemma perm_expand {l₁ l₂ : List ( X × Nat)} (hl : l₁.Perm l₂) :
    (expand l₁).Perm (expand l₂) := by
  unfold expand
  apply List.Perm.flatten
  apply List.Perm.map
  apply hl


-- I (HM) think this can be proved using only `expand`, not `count` or `Sticking` etc


theorem sort_expand [LinearOrder X] (l : List (X × Nat)) :
    List.sort (X := X) (expand l) = expand (l.mergeSort (fun (x1, _) (x2, _) ↦ x1 ≤ x2)) := by
  simp
  have := mergeSort_sorted_list_X_Nat l
  simp at this
  have lhs_sorted := sorted_expand_sorted this
  unfold List.sort
  have rhs_sorted := (expand l).sorted_mergeSort' (α := X) (r := LE.le)
  have  := List.mergeSort_perm l (fun x x_1 => x.1 ≤ x_1.1)
  have perm_rhs_lhs := perm_expand this
  have := List.mergeSort_perm (expand l) (· ≤ · )
  apply List.Perm.symm at this
  have perm_rhs_lhs := List.Perm.trans perm_rhs_lhs this
  have h := List.eq_of_perm_of_sorted perm_rhs_lhs lhs_sorted rhs_sorted
  rw[h]

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
  have h_perm : List.Perm (List.mergeSort l (fun x x_1 => x.1 ≤ x_1.1)) l := by
    apply List.mergeSort_perm
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
    count (List.sort (List.flatten (List.map (List.map f) L))) = count (List.sort (List.flatten L)) := by
  rw [← List.map_flatten]
  rw[← sort_map_sort]
  have h2 := map_stick_stick (sort_stick L.flatten) hf
  rw[← count_of_stick h2]
  rw[← count_of_map hf]
  -- unfold count
  -- simp [-List.map_flatten]
  -- congr! 3


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
