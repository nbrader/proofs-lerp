#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package mtl-2.2.2

-- Linearly interpolates between x0 and x1 by t.
lerp :: Fractional a => a -> a -> a -> a
lerp x0 x1 t = x0 * (1 - t) + x1 * t
{- 
  lerp x0 x1 0 == x0
  lerp x0 x1 1 == x1
  a * linearLerp t0 + b * linearLerp t1 == linearLerp (a * t0 + b * t1)
      where linearLerp t = lerp x0 x1 t - lerp x0 x1 0
-}

-- Calculates the interpolation factor t for a value x in the range from x0 to x1.
inverseLerp :: (Eq a, Fractional a) => a -> a -> a -> a
inverseLerp x0 x1 x
  | x0 /= x1 = (x - x0) / (x1 - x0)
  | otherwise = 0.0
{- 
  inverseLerp x0 x1 x0 == 0
  inverseLerp x0 x1 x1 == 1
  a * linearInverseLerp x2 + b * linearInverseLerp x3 == linearInverseLerp (a * x2 + b * x3)
      where linearInverseLerp x = inverseLerp x0 x1 (x + x0)
-}

-- Maps a value x from one range [x0, x1] to another range [y0, y1].
affineMap :: (Eq a, Fractional a) => a -> a -> a -> a -> a -> a
affineMap x0 x1 y0 y1 x = lerp y0 y1 $ inverseLerp x0 x1 x
{- 
  affineMap x0 x1 y0 y1 x0 == y0
  affineMap x0 x1 y0 y1 x1 == y1
  a * linearAffineMap1 x2 + b * linearAffineMap1 x3 == linearAffineMap1 (a * x2 + b * x3)
      where linearAffineMap1 x = affineMap x0 x1 y0 y1 (x + x0) - affineMap x0 x1 y0 y1 x0
-}
