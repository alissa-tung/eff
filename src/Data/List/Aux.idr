module Data.List.Aux

import Data.List

%default total

namespace SubElem
  public export
  data SubElem : a -> List a -> Type where
    Z : SubElem x (x :: xs)
    S : SubElem x xs -> SubElem x (x' :: xs)

namespace SubList
  public export
  data SubList : (xs, ys : List a) -> Type where
    ||| Vacuous truth.
    Nil : SubList [] ys
    Cons : SubElem x ys -> SubList xs ys -> SubList (x :: xs) ys

public export
Uninhabited (SubElem x []) where
  uninhabited Z     impossible
  uninhabited (S _) impossible
