
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



-- assume the list are sorted
def nsame : List Nat -> List Nat -> Nat
  | [], b => b.length
  | _ :: a, [] => a.length + 1
  | i :: a, j :: b =>
    if i = j then nsame a b
    else if i > j then 1 + nsame (i :: a) b
    else 1 + nsame a (j :: b)

def NearlySame (l1 : List Nat) (l2 : List Nat) : Bool :=
  Nat.ble ( nsame l1 l2 ) 2


def elimNearlySame (l : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | h1 :: t1 =>
    if (NearlySame l h1) then
      elimNearlySame l t1
    else
      h1 :: elimNearlySame l t1
