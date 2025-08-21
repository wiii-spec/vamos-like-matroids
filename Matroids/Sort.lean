import Mathlib.Data.List.Sort
-- import Mathlib.Data.List.Lex

-- variable {X : Type*} [LT X] [DecidableRel ((·:X) < · )] [BEq X ]
/-- Function that sorts, outside PartialMatroid namespace. It will sort lists by dtermining which
list is greater. Its criteria for determining the greater list is whichever list generates a greater
number first-/
def List.sort {X : Type*} [LinearOrder X] (l : List X) : List X :=
   l.mergeSort (· < · )
