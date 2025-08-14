import Matroids.NearlySame
import Matroids.Verification.Basic
import Matroids.Verification.Miscellaneous


lemma nsame.comm {l₁ l₂ : List Nat} :
    nsame l₁ l₂ = nsame l₂ l₁ := by
  unfold nsame
  match l₁, l₂ with
  |[], [] => simp
  | [], _ :: l₂' => simp
  | _ :: l₁', [] => simp
  | i :: a, j :: b =>
    simp
    obtain h | h | h := lt_trichotomy i j
    · rw [if_neg, if_neg, if_neg, if_pos]
      have := @nsame.comm a (j :: b)
      rw[this]
      all_goals omega
    · rw[if_pos, if_pos]
      rw[ @nsame.comm a b]
      all_goals omega
    · rw[if_neg, if_pos, if_neg, if_neg]
      rw[ @nsame.comm (i :: a) b]
      all_goals omega
      termination_by _ l1 l2 => l1.length + l2.length



lemma NearlySame.comm {l₁ l₂ : List Nat} :
    NearlySame l₁ l₂ = NearlySame l₂ l₁ := by
  unfold NearlySame
  simp_rw[nsame.comm]
