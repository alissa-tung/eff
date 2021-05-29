module Control.Effect.Default

%default total

interface Default a where
  initVal : a

[viaNum] Num a => Default a where
  initVal = fromInteger 0

[viaMonoid] Monoid a => Default a where
  initVal = neutral

[viaAlternative] Alternative f => Default (f a) where
  initVal = empty
