module Control.Effect.StdIO

import Control.Effect.Effects

%default total

export
data StdIO : Effect where
  GetChar : sig StdIO Char
  GetStr : sig StdIO String
  PutChar : Char -> sig StdIO ()
  PutStr : String -> sig StdIO ()

public export
Handler StdIO IO where
  handle () io k = case io of
    GetChar => getChar >>= flip k ()
    GetStr => getLine >>= flip k ()
    PutChar c => putChar c *> k () ()
    PutStr s => putStr s *> k () ()

public export
STDIO : EFFECT
STDIO = MkEff () StdIO

public export
putStr : String -> Eff () [STDIO]
putStr s = call {e = StdIO} (PutStr s)

-- public export
-- putStrLn : String -> Eff () [STDIO]
-- putStrLn s = putStr (s ++ "\n")
