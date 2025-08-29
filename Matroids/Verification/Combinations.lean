import Matroids.Combinations
import Batteries

/-- Every list appearing in the list-of-lists `combinations n k` has length `k`. -/
theorem combinations_entries_lengths (n k : Nat) :
    (combinations n k).all (fun l ↦ l.length = k) := by
  unfold combinations
  match n, k with
  | _, 0 => simp
  | 0, _ + 1 => simp
  | n + 1, k + 1 =>
    simp
    constructor
    -- Prove by strong induction
    · intro l hl1
      have H := combinations_entries_lengths n (k + 1) -- inductive hypothesis
      simp at H
      apply H
      apply hl1
    · intro l hl2
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
      constructor
      · intro l h1 x h4
        have H := combinations_entries_bounds n (k + 1)
        simp at H
        specialize H l h1 x h4
        omega
      · intro l h4 a ha
        have H := combinations_entries_bounds n k
        simp at H
        specialize H l h4 a ha
        omega
