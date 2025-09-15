import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Notation

open List
variable {α β : Type*}

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
    simp [-forall_append]
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


lemma List.Forall.flatten {L : List (List α)} {P : α → Prop} (hl : L.Forall fun l ↦ l.Forall P) :
    L.flatten.Forall P := by
  unfold List.flatten
  match L with
  | []      => simp
  | a :: as =>
    simp
    have IH := List.Forall.flatten (L := as) (P := P)
    have h1 : Forall (fun l => Forall P l) as := by
      simp at hl
      obtain ⟨th1, hh1⟩ := hl
      exact hh1
    apply IH at h1
    simp at hl
    obtain ⟨th1, hh1⟩ := hl
    constructor
    · exact th1
    · exact h1

theorem List.pairwise_range {R : ℕ → ℕ → Prop} (H : ∀ i j, i < j → R i j) :
    List.Pairwise R (List.range n) := by
  apply @List.Pairwise.imp Nat (fun a b => a < b) R
  · apply H
  · exact pairwise_lt_range


lemma List.Forall.perm {L₁ L₂ : List X} {P : X → Prop } (hL : L₁.Perm L₂)
    (hp: L₁.Forall P) :
    L₂.Forall P := by
  -- apply?
  sorry

theorem List.get_mem_zip {X Y : Type*} {L : List X} {M : List Y} (h : L.length = M.length)
    (i : Fin M.length) :
    (L[i], M[i]) ∈ L.zip M := by
  have := List.length_zip (l₁ := L) (l₂ := M)
  rw[h] at this
  simp
  rw[<- List.getElem_zip (l := L) ( l' := M) (i := i)]
  · refine getElem_mem ?_
    rw[this]
    simp
