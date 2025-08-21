import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Notation

open List
variable {α β : Type*}

@[simp] theorem Matrix.cons_val_three {α : Type*} {m : ℕ} (x : α) (u : Fin m.succ.succ.succ → α) :
    vecCons x u 3 = vecHead (vecTail (vecTail u)) :=
  rfl

/-- Map a partially-defined (i.e. dependent) function `f` over a list, if the dependency is
satisfied for every element of the list. -/
def List.dependentMap {P : α → Prop} (f : ∀ a, P a → β) : ∀ (l : List α), l.Forall P → List β
  | [], _ => []
  | h :: t, hl =>
    let hl' : _ ∧ _ := (List.forall_cons _ _ _).1 hl
    f h hl'.1 :: dependentMap f t hl'.2


lemma List.forall_append_iff {L1 L2 : List α} {P : α → Prop} :
     List.Forall P (L1 ++ L2) ↔ (List.Forall P L1) ∧ (List.Forall P L2) := by
  induction L1 with
  | nil =>
    simp
  | cons h t IH =>
    simp
    constructor
    · intro h1
      obtain ⟨th1, hh1⟩ := h1
      obtain ⟨IH1, _⟩ := IH
      apply IH1 at hh1
      obtain ⟨thh1, hhh1⟩ := hh1
      constructor
      · constructor
        · exact th1
        · exact thh1
      · exact hhh1
    · intro h1
      obtain ⟨th1, hh1⟩ := h1
      obtain ⟨_, IH2⟩ := IH
      obtain ⟨tth1, hth1⟩ := th1
      constructor
      · exact tth1
      · apply IH2
        constructor
        · exact hth1
        · exact hh1


lemma List.Forall.join {L : List (List α)} {P : α → Prop} (hl : L.Forall fun l ↦ l.Forall P) :
    L.join.Forall P := by
  unfold join
  match L with
  | []      => simp [join]
  | a :: as =>
    simp [join]
    have IH := List.Forall.join (L := as) (P := P)
    have h1 : Forall (fun l => Forall P l) as
    · simp at hl
      obtain ⟨th1, hh1⟩ := hl
      exact hh1
    apply IH at h1
    simp at hl
    obtain ⟨th1, hh1⟩ := hl
    rw [forall_append_iff]
    constructor
    · exact th1
    · exact h1

lemma List.mem_mergeSort (r : α → α → Prop) [h: DecidableRel r] {l : List α} (h : a ∈ l) :
    a ∈ l.mergeSort r := by
  rw [List.Perm.mem_iff]
  · apply h
  · apply List.perm_mergeSort

lemma List.reverse_mem_mergeSort (r : α → α → Prop) [h: DecidableRel r] {l : List α} (h : a ∈ l.mergeSort r) :
    a ∈ l := by
  rw [List.Perm.mem_iff]
  · apply h
  · apply List.Perm.symm
    apply List.perm_mergeSort

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


lemma List.split_of_sublist {l : List α} :
    List.Sublist (l.split).1 l ∧ List.Sublist (l.split).2 l:= by
  match l with
  | [] => simp
  | a :: l =>
    unfold split
    simp
    have ih := @List.split_of_sublist l
    constructor
    · apply List.Sublist.cons_cons
      exact ih.2
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

#check List.Nodup.sublist
#check List.split
#check lt_iff_le_and_ne

/--mergeSort with the less than relation has no duplicates-/ -- Wrong lemma, counterexample below
lemma List.mergeSort_no_duplicates [PartialOrder α] {l : List α} [DecidableRel ((· : α) < ·)]:
   Nodup (mergeSort (· < ·) l) :=

  sorry

#eval mergeSort (· < ·) [1,1,2]


theorem List.pairwise_range {R : ℕ → ℕ → Prop} (H : ∀ i j, i < j → R i j) :
    List.Pairwise R (List.range n) := by
  apply @List.Pairwise.imp Nat (fun a b => a < b) R
  · apply H
  · exact pairwise_lt_range n

/- PENDING theorem: If you have two different sorted lists and you run merge on them,
then the result has to be sorted. Take a look at theorem Sorted.merge-/


theorem sorted_mergeSort_lt [PartialOrder α] {l : List α} [DecidableRel ((· : α) < ·)] :
    ∀ l : List α, Sorted (· < ·) (mergeSort (· < ·) l)
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: l => by
    simp [mergeSort]

    sorry

-- in the file Init.Data.List.Sublist
-- added in https://github.com/leanprover/lean4/pull/5053, August 2024
theorem List.Sublist.mem {α : Type*} {l₁ : List α} {a : α} {l₂ : List α} (hx : a ∈ l₁)
    (hl : l₁.Sublist l₂) :
    a ∈ l₂ :=
  sorry


lemma List.Forall.perm {L₁ L₂ :List X} {P : X → Prop } (hL : L₁.Perm L₂)
    (hp: L₁.Forall P) :
    L₂.Forall P := by
  -- apply?
  sorry


lemma mergeSort_of_perm_eq {L₁ L₂ : List X} (P : X → X → Prop) [DecidableRel P] (hL : L₁.Perm L₂) :
    List.mergeSort P L₁ = List.mergeSort P L₂ := by
  sorry
