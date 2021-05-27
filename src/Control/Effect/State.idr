module Control.Effect.State

import Control.Effect.Effect

%default total

||| ADT for state management.
public export
data State : Effect where
  ||| @ Get takes no arguments. It has a resource of type `a`, which is not
  |||       updated, and running the `Get` operation returns something of type
  |||       `a`.
  Get : sig State a a
  ||| @ Put takes an element of type `b` as its argument. It has a resource of
  |||       type `a` on input, which is updated to a resource of type `b`.
  |||       Running the `Put` operation returns the unit.
  Put : b -> sig State () a b

public export
{m : _} -> Handler State m where
  handle inRes eff k = case eff of
    Get => k inRes inRes
    Put y => k () y

||| Effect for state management.
|||
||| @ Get takes no arguments. It has a resource of type `a`, which is not
|||       updated, and running the `Get` operation returns something of type
|||       `a`.
||| @ Put takes an element of type `b` as its argument. It has a resource of
|||       type `a` on input, which is updated to a resource of type `b`.
|||       Running the `Put` operation returns the unit.
public export
STATE : (a : Type) -> EFFECT
STATE a = MkEff a State
