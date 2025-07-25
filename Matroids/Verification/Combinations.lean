import Matroids.Combinations
import Std

/-- Every list appearing in the list-of-lists `combinations n k` has length `k`. -/
theorem combinations_entries_lengths (n k : Nat) :
    (combinations n k).all (fun l ↦ l.length = k) := by
  unfold combinations
  match n, k with
  | _, 0 => simp [combinations]
  | 0, _ + 1 => simp [combinations]
  | n + 1, k + 1 =>
    simp [combinations]
    intro l hl
    obtain hl1 | hl2 := hl
    -- Prove by strong induction
    · have H := combinations_entries_lengths n (k + 1) -- inductive hypothesis
      simp at H
      -- exact H l hl1
      apply H
      apply hl1
    · obtain ⟨l2, hl2, hl3⟩ := hl2
      rw [← hl3]
      simp
      have H := combinations_entries_lengths n k -- inductive hypothesis
      simp at H
      apply H
      apply hl2

/-- Every entry in each of the lists in `combinations n k` is less than n. -/
theorem combinations_entries_bounds (n k : Nat) :
    (combinations n k).all (fun l ↦ l.all (fun i ↦ i < n)) := by
    match n, k with
    | _, 0 => simp [combinations]
    | 0, _ + 1 => simp [combinations]
    | n + 1, k + 1 =>
      simp [combinations]
      intro l ha x h4
      obtain h1 | h2 := ha
      -- inductive hypothesis
      · have H := combinations_entries_bounds n (k + 1)
        simp at H
        specialize H l h1 x h4
        omega
      · have H := combinations_entries_bounds n k
        simp at H
        obtain ⟨ a,hx, hy⟩:= h2
        rw[<- hy] at h4
        simp at h4
        obtain h5|h6 := h4
        · specialize H a hx x h5
          omega
        · omega
