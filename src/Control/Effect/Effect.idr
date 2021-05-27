-----------------------------------------------------------------
-- The Resource-dependent Algebraic Effects Library of Idris2. --
-----------------------------------------------------------------

module Control.Effect.Effect

import Data.List.Elem
import Data.List.Aux

%default total

------------------
-- Effects Core --
------------------

||| The type Effect itself is a type synonym, namely, a function that can
||| compute types.
|||
||| The function takes:
||| @ a      The return type of an effectful computation, where `(x : a)` is
|||          the corresponding result.
|||
||| Each effect is associated with a resource, which is initialised before an
||| effectful program can be run.
|||
||| @ inEff  The available input effects, where `(inRes : inEff)` is the
|||          corresponding input resources.
|||
||| @ outEff The function which computes the available output effects, where
|||          `(outRes : outEff)` is the corresponding function which computes
|||          the output resources. The output effects and resources may or may
|||          not dependents on the result of an effectful computation.
public export
Effect : Type
Effect = (a : Type) -> (inEff : Type) -> (outEff : a -> Type) -> Type

||| Side effects are described using the `EFFECT` type, which will be referred
||| to these as concrete effects for it describes how to promote the effect
||| description into a concrete effect.
|||
||| @ MkEff The constructor `MkEff` constructs an `EFFECT` by taking the
|||         resource type and the effect signature.
public export
record EFFECT where
  constructor MkEff -- MkEff : Type -> Effect -> EFFECT
  effTyp : Type
  effSig : Effect

-- The function family 'sig' gives a signature to an effect.
-- Four versions are depending on whether there is
-- 1.) no resource needed
-- 2.) no state change
-- 3.) a non-dependent change
-- 4.) a dependent change
-- They are easily disambiguated by their types so we use namespaces to deal with.

namespace NoResEff
  public export %inline
  sig : Effect -> (a : Type) -> Type
  sig eff a = eff a () (const ())

namespace NoUpdEff
  public export %inline
  sig : Effect -> (a, inEff : Type) -> Type
  sig eff a inEff = eff a inEff (const inEff)

namespace UpdEff
  public export %inline
  sig : Effect -> (a, inEff, outEff : Type) -> Type
  sig eff a inEff outEff = eff a inEff (const outEff)

namespace DepUpdEff
  public export %inline
  sig : Effect -> (a, inEff : Type) -> (outEff : a -> Type) -> Type
  sig = id

||| To find out the resource type of an effect if necessary (for example if we
||| want to initialise a resource explicitiy with `runInit` rather than using a
||| default value with `run`), we can run the function at the Idris REPL.
public export
resTyp : EFFECT -> Type
resTyp (MkEff typ _) = typ

||| An instance of `Handler e m` means that the effect declared with signature
||| `e` can be run in computation context `m`. There is no need for the type
||| `m` to be a monad.
public export
interface Handler (e : Effect) (m : Type -> Type) where
  ||| The function takes:
  ||| @ inRes The resource on input.
  |||
  ||| @ eff   The effectful operation.
  |||
  ||| @ k     A continuation, which we conventionally call `k`, and should be
  |||         passed the result value of the operation, and an updated resource.
  |||
  |||         There are two reasons for taking a continuation here:
  |||
  |||           Firstly, this is neater because there are multiple return values
  |||           (a new resource and the result of the operation);
  |||
  |||           Secondly, and more importantly, the continuation can be called
  |||           zero or more times.
  handle : (inRes : inEff)
        -> (eff : e a inEff outEff)
        -> (k : (x : a) -> outEff x -> m a)
        -> m a

-----------------
-- Environment --
-----------------

namespace Env
  ||| In general, to run an effectful program, we use one of the functions
  ||| `run`, `runWith`, `runPure` and so on, instantiating an environment of
  ||| the type `Env m es` with resources corresponding to each effect.
  |||
  ||| @ m  The computation context.
  |||      There is no need for the type `m` to be a monad.
  ||| @ es The environment must contain resources corresponding exactly to the
  |||      effects in `es`.
  public export
  data Env : (m : Type -> Type) -> (es : List EFFECT) -> Type where
    ||| The empty environment.
    Nil : Env m Nil
    ||| A non-empty environment, consisting of a head resource and the rest of
    ||| the environment.
    (::) : Handler e m => (x : a) -> (xs : Env m es) -> Env m (MkEff a e :: es)

----------------------
-- Labelled Effects --
----------------------

infix 5 ::=, ::-, ::@, =::, -::, @::

||| Effects can be labelled so that they can be referred to explicitly by a
||| particular name. This allows multiple effects of the same type to be included.
public export
data LRes : lbl -> (eff : Type) -> Type where
  ||| Initialise a resource for a labelled effect.
  ||| Resources for labelled effects are intialised using the `::=` operator
  ||| (reminisicent of assignment in an imperative language).
  (::=) : (l : lbl) -> eff -> LRes l eff

||| Flipped version of `::=`. Initialise a resource for a labelled effect.
||| Resources for labelled effects are intialised using the `=::` operator
||| (reminisicent of assignment in an imperative language).
public export %inline
(=::) : eff -> (l : lbl) -> LRes l eff
res =:: l = l ::= res

||| Convert an effect to a labelled effect.
||| The `::@` operator allows an arbitrary label to be given to an effect. This
||| label can be any type --- it is simply used to identify an effect uniquely.
public export
(::@) : lbl -> EFFECT -> EFFECT
l ::@ (MkEff typ sig) = MkEff (LRes l typ) sig

||| Flipped version of `::@`. Convert an effect to a labelled effect.
||| The `@::` operator allows an arbitrary label to be given to an effect. This
||| label can be any type --- it is simply used to identify an effect uniquely.
public export %inline
(@::) : EFFECT -> lbl -> EFFECT
(@::) = flip (::@)

-----------------------------------------
-- Embedded DSL for Effects Management --
-----------------------------------------

public export
updResTyp : {outEff : a -> Type} -> (x : a)
         -> (es : List EFFECT)
         -> (prf : Elem (MkEff inEff eff) es) -- TODO: linear
         -> eff a inEff outEff -> List EFFECT
updResTyp x (MkEff inEff eff :: es) Here prog = MkEff (outEff x) eff :: es
updResTyp x (e :: es) (There prf) prog = e :: updResTyp x es prf prog

public export
updAt : (SubElem x xs) -> Type -> List EFFECT -> List EFFECT
updAt Z     inEff [] = []
updAt Z     inEff (MkEff outEff eff :: es) = (MkEff inEff eff) :: es
updAt (S n) inEff [] = []
updAt (S n) inEff (e :: es) = e :: updAt n inEff es

public export
updWith : (xs, ys : List EFFECT) -> SubList zs ys -> List EFFECT
updWith [] ys p = ys
updWith (x :: xs) ys Nil = ys
updWith (MkEff inEff eff :: xs) ys (Cons ix zs) = updAt ix inEff (updWith xs ys zs)

||| Internal definition of a language that describe effectful programs.
|||
||| @ m   The computation context.
|||       There is no need for the type `m` to be a monad.
|||
||| @ a   The return type of an effectful computation, where `(x : a)` is
|||       the corresponding result.
|||
||| @ es  The list of input effects. The environment must contain resources
|||       corresponding exactly to the effects in `es`.
|||
||| @ es' The list of output effects. The environment must contain resources
|||       corresponding exactly to the effects in `es'`.
export
data EffM : (m : Type -> Type)
         -> (a : Type)
         -> (es : List EFFECT)
         -> (es' : a -> List EFFECT)
         -> Type where
  Value : (val : a) -> EffM m a (es val) es

  EBind : EffM m a es es'
       -> (k : (x : a) -> EffM m b (es' x) es'')
       -> EffM m b es es''

  CallP : {auto prf : Elem (MkEff inEff e) es}
       -> (eff : e a inEff outEff)
       -> EffM m a es (\v => updResTyp v es prf eff)

  LiftP : {auto prf : SubList xs ys}
       -> EffM m a xs xs' -> EffM m a ys (\v => updWith (xs' v) ys prf)

  NewP : Handler e' m => (e : EFFECT) -> a
      -> {auto prf : e = MkEff a e'}
      -> EffM m a' (e :: es) (const (e :: es))
      -> EffM m a' es (const es)

  Mod : (l : lbl)
     -> EffM m a [e] es'
     -> EffM m a [l ::@ e] (Prelude.map (l ::@) . es')

||| Convert an effectful operation to a labelled effectful operation, then
||| operate on the given resource explicitly by the particular name.
public export %inline
(::-) : (l : lbl)
     -> EffM m a [e] es'
     -> EffM m a [l ::@ e] (Prelude.map (l ::@) . es')
(::-) = Mod

||| Flipped version of `::-`.
||| Convert an effectful operation to a labelled effectful operation, then
||| operate on the given resource explicitly by the particular name.
public export %inline
(-::) : EffM m a [e] es'
     -> (l : lbl)
     -> EffM m a [l ::@ e] (Prelude.map (l ::@) . es')
res -:: l = Mod l res

namespace SimplEff
  public export
  Eff : (a : Type) -> (es : List EFFECT) -> Type
  Eff a es = {m : Type -> Type} -> EffM m a es (const es)

  public export
  EffT : (m : Type -> Type) -> (a : Type) -> (es : List EFFECT) -> Type
  EffT m a es = EffM m a es (const es)

namespace TransEff
  public export
  Eff : (a : Type) -> (es, es' : List EFFECT) -> Type
  Eff a es es' = {m : Type -> Type} -> EffM m a es (const es')

  public export
  EffT : (m : Type -> Type) -> (a : Type) -> (es, es' : List EFFECT) -> Type
  EffT m a es es' = EffM m a es (const es')

namespace DepEff
  public export
  Eff : (a : Type) -> (es : List EFFECT) -> (es' : a -> List EFFECT) -> Type
  Eff a es es' = {m : Type -> Type} -> EffM m a es es'

  public export
  EffT : (m : Type -> Type) -> (a : Type) -> (es : List EFFECT) -> (es' : a -> List EFFECT) -> Type
  EffT m a es es' = EffM m a es es'

-------------
-- Monadic --
-------------

namespace Monadic

  public export %inline
  pure : a -> EffM m a es (const es)
  pure = Value

  public export %inline
  pureM : (x : a) -> EffM m a (es x) es
  pureM = Value

  public export %inline
  (>>=) : EffM m a es es' -> (k : (x : a) -> EffM m b (es' x) es'') -> EffM m b es es''
  (>>=) = EBind

  public export %inline
  staticEff : EffM m a es (const es) -> EffM m a es (const es)
  staticEff = id

  public export
  (<*>) : EffM m (a -> b) es (const es)
       -> EffM m  a       es (const es)
       -> EffM m  b       es (const es)
  fs <*> xs = let (>>=) = Monadic.(>>=)
                  pure  = Monadic.pure
               in do pure $ !fs !xs

public export
call : {inEff, outEff : _} -> {e : Effect}
    -> (eff : e a inEff outEff)
    -> {auto prf : Elem (MkEff inEff e) es}
    -> EffM m a es (\v => updResTyp v es prf eff)
call eff = CallP eff -- TODO: re _P

public export
runInit : Applicative f => (env : Env m es) -> (prog : EffM m a es es') -> m a
runInit env prog = ?eff env prog (id . const)
