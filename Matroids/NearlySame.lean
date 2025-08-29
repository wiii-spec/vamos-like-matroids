
/-! # Code to ---

This file provides functions to identify within a list of list of natural numbers whether or not
there is a list of natural numbers with

## Main definitions

* `NearlySameAux`: checks if there is more than one different element between two lists.
* `NearlySame`: returns a boolean on whether or not there is more than one different element between
two lists
* `elimNearlySame`: Looks at a list of lists of natural numbers and see if there are any existing
lists in the list of lists that has at most one different element between them and eliminates items
from the list of lists that have a most one different element between it and the new list.
-/

def nsameAux : Nat → List Nat -> List Nat -> Nat
  | 0, _, _ => 0
  | _ + 1, [], b => b.length
  | _ + 1, _ :: a, [] => a.length + 1
  | k + 1, i :: a, j :: b =>
    if i = j then nsameAux k a b
    else if i > j then 1 + nsameAux k (i :: a) b
    else 1 + nsameAux k a (j :: b)

def nsame' (l1 l2 : List Nat) := nsameAux (l1.length + l2.length) l1 l2

-- assume the list are sorted
-- this implementation is better for reasoning with, but it is a well-founded recursion rather than
-- a structural recursion, so we use `nsame'` in definitions.
def nsame : List Nat -> List Nat -> Nat
  | [], b => b.length
  | _ :: a, [] => a.length + 1
  | i :: a, j :: b =>
    if i = j then nsame a b
    else if i > j then 1 + nsame (i :: a) b
    else 1 + nsame a (j :: b)

theorem nsame_eq_nsameAux :
    ∀ l1 l2 : List Nat, ∀ k ≥ l1.length + l2.length, nsame l1 l2 = nsameAux k l1 l2
  | [], b, k => by cases k <;> cases b <;> simp [nsame, nsameAux]
  | _ :: a, [], k => by cases k <;> simp [nsame, nsameAux]
  | i :: a, j :: b, 0 => by
    simp [nsame, nsameAux]
  | i :: a, j :: b, k + 1 => by
    simp [nsame, nsameAux]
    split
    · have := nsame_eq_nsameAux a b k
      omega
    split
    · have := nsame_eq_nsameAux (i :: a) b k
      simp at this
      omega
    · have := nsame_eq_nsameAux a (j :: b) k
      simp at this
      omega

theorem nsame_eq_nsame' (l1 l2 : List Nat) : nsame l1 l2 = nsame' l1 l2 := by
  apply nsame_eq_nsameAux
  exact Nat.le_refl ..

def NearlySame (l1 : List Nat) (l2 : List Nat) : Bool :=
  Nat.ble (nsame' l1 l2 ) 2

-- `NearlySame` has a weird definition to avoid well-founded recursion
-- use this theorem to convert to an alternative definition which is better for reasoning
theorem nearlySame_eq (l1 l2 : List Nat) : NearlySame l1 l2 = Nat.ble (nsame l1 l2) 2 := by
  rw [NearlySame, nsame_eq_nsame']

def elimNearlySame (l : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | h1 :: t1 =>
    if (NearlySame l h1) then
      elimNearlySame l t1
    else
      h1 :: elimNearlySame l t1
