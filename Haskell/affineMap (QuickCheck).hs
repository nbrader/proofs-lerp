#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck-2.14.2 --package linear-1.21.10

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}

import Test.QuickCheck
import Linear.Vector hiding (lerp)

newtype Affine f a = Affine { fromAffine :: a }
  deriving (Eq, Show, Ord, Functor)

instance (Arbitrary a, Fractional a) => Arbitrary (Affine f a) where
    arbitrary = toAffine <$> arbitrary

toAffine :: a -> Affine f a
toAffine = Affine

instance (Fractional a) => Num (Affine f a) where
  (+) (Affine a) (Affine b) = toAffine (a + b)
  (-) (Affine a) (Affine b) = toAffine (a - b)
  (*) (Affine a) (Affine b) = toAffine (a * b)
  abs (Affine a) = toAffine (abs a)
  signum (Affine a) = toAffine (signum a)
  fromInteger i = toAffine (fromInteger i)

instance (Fractional a) => Fractional (Affine f a) where
  fromRational r = toAffine (fromRational r)
  recip (Affine a) = toAffine (recip a)
  (/) (Affine a) (Affine b) = toAffine (a / b)

-- Linearly interpolates between x0 and x1 by t.
lerp :: (Fractional a) => Affine f a -> Affine f a -> a -> Affine f a
lerp (Affine x0) (Affine x1) t = toAffine $ (1 - t) * x0 + t * x1

lerpHomog0 :: (Fractional a) => Affine f a -> Affine f a -> a -> Affine f a
lerpHomog0 x0 x1 t = lerp x0 x1 t - lerp x0 x1 0

-- Calculates the interpolation factor t for a value x in the range from x0 to x1.
inverseLerp :: (Fractional a, Eq a) => Affine f a -> Affine f a -> Affine f a -> a
inverseLerp x0' x1' x' = if x0 /= x1 then (x - x0) / (x1 - x0) else 0.0
  where x0 = fromAffine x0'
        x1 = fromAffine x1'
        x = fromAffine x'

inverseLerpHomog0 :: (Fractional a, Eq a) => Affine f a -> Affine f a -> Affine f a -> a
inverseLerpHomog0 x0 x1 x = inverseLerp x0 x1 (toAffine $ (fromAffine x) + (fromAffine x0))

-- Maps a value x from one range [x0, x1] to another range [y0, y1].
affineMap :: (Fractional a, Eq a) => Affine f1 a -> Affine f1 a -> Affine f2 a -> Affine f2 a -> Affine f1 a -> Affine f2 a
affineMap x0 x1 y0 y1 x = lerp y0 y1 . inverseLerp x0 x1 $ x

affineMapHomog :: (Fractional a, Eq a) => Affine f1 a -> Affine f1 a -> Affine f2 a -> Affine f2 a -> Affine f1 a -> Affine f2 a
affineMapHomog x0 x1 y0 y1 x = 
  affineMap x0 x1 y0 y1 (x + x0) - affineMap x0 x1 y0 y1 x0


-- Helper function for approximate equality
approxEqual :: Double -> Double -> Double -> Property
approxEqual tolerance a b = property $ comp tolerance a b
  where comp 0         a b = a == b
        comp tolerance a b = abs (a - b) < tolerance

approxEqualAffine :: Double -> Affine f Double -> Affine f Double -> Property
approxEqualAffine tolerance (Affine a) (Affine b) = approxEqual tolerance a b

-- lerp properties
prop_lerp_LAW_IMPLEMENTATION :: Affine f Double -> Affine f Double -> Double -> Property
prop_lerp_LAW_IMPLEMENTATION x0 x1 t =
  approxEqualAffine 0 (lerp x0 x1 t) (toAffine $ (1 - t) * fromAffine x0 + t * fromAffine x1)

prop_lerp_LAW_ZERO :: Affine f Double -> Affine f Double -> Property
prop_lerp_LAW_ZERO x0 x1 =
  approxEqualAffine 0 (lerp x0 x1 0) x0

prop_lerp_LAW_UNIT :: Affine f Double -> Affine f Double -> Property
prop_lerp_LAW_UNIT x0 x1 =
  approxEqualAffine 0 (lerp x0 x1 1) x1

prop_lerpHomog0_LAW_DEF_1 :: Affine f Double -> Affine f Double -> Double -> Property
prop_lerpHomog0_LAW_DEF_1 x0 x1 t =
  approxEqualAffine 0 (lerpHomog0 x0 x1 t) (lerp x0 x1 t - lerp x0 x1 0)

prop_lerpHomog0_LAW_DEF_2 :: Affine f Double -> Affine f Double -> Double -> Property
prop_lerpHomog0_LAW_DEF_2 x0 x1 t =
  approxEqualAffine 0 (lerpHomog0 x0 x1 t) (lerp x0 x1 t - x0)

prop_lerpHomog0_LAW_ZERO :: Affine f Double -> Affine f Double -> Property
prop_lerpHomog0_LAW_ZERO x0 x1 =
  approxEqualAffine 0 (lerpHomog0 x0 x1 0) 0

prop_lerpHomog0_LAW_LINEAR :: Affine f Double -> Affine f Double -> Double -> Double -> Double -> Double -> Property
prop_lerpHomog0_LAW_LINEAR x0 x1 t0 t1 a b =
  approxEqualAffine 1e-7    (lerpHomog0 x0 x1 (a*t0 + b*t1))
                         (a*^(lerpHomog0 x0 x1 t0) + b*^(lerpHomog0 x0 x1 t1))

prop_lerpHomog0_LAW_AFFINE :: Double -> Affine f Double -> Affine f Double -> Affine f Double -> Double -> Property
prop_lerpHomog0_LAW_AFFINE a y0 y1 b x =
  approxEqualAffine 1e-8    (lerpHomog0 (a*^y0+b) (a*^y1+b) x)
                        (a*^(lerpHomog0 y0 y1 x))

prop_lerpHomog0_LAW_DEF_5 :: Affine f Double -> Affine f Double -> Property
prop_lerpHomog0_LAW_DEF_5 x0 x1 =
  approxEqualAffine 0 (lerpHomog0 x0 x1 1) (x1 - x0)

prop_lerpHomog0_LAW_DEF_6 :: Affine f Double -> Affine f Double -> Double -> Property
prop_lerpHomog0_LAW_DEF_6 x0 x1 c =
  approxEqualAffine 1e-7 (lerpHomog0 x0 x1 c)
                     (c*^(lerpHomog0 x0 x1 1))

prop_lerpHomog0_LAW_IMPLEMENTATION :: Affine f Double -> Affine f Double -> Double -> Property
prop_lerpHomog0_LAW_IMPLEMENTATION x0 x1 c =
  approxEqualAffine 1e-6 (lerpHomog0 x0 x1 c) (c*^(x1 - x0))

-- inverseLerp properties
prop_inverseLerp_LAW_IMPLEMENTATION :: Affine f1 (Affine f2 Double) -> Affine f1 (Affine f2 Double) -> Affine f1 (Affine f2 Double) -> Property
prop_inverseLerp_LAW_IMPLEMENTATION x0 x1 x =
  approxEqualAffine 0 (inverseLerp x0 x1 x) 
                      (if x0 /= x1 then (fromAffine x - fromAffine x0) / (fromAffine x1 - fromAffine x0) else 0)

prop_inverseLerp_LAW_ZERO :: Affine f Double -> Affine f Double -> Property
prop_inverseLerp_LAW_ZERO x0 x1 =
  approxEqual 0 (inverseLerp x0 x1 x0) 0

prop_inverseLerp_LAW_UNIT :: Affine f Double -> Affine f Double -> Property
prop_inverseLerp_LAW_UNIT x0 x1 = x0 /= x1 ==>
  approxEqual 0 (inverseLerp x0 x1 x1) 1

prop_inverseLerp_LAW_LINEAR :: Affine f Double -> Affine f Double -> Affine f Double -> Affine f Double -> Affine f Double -> Property
prop_inverseLerp_LAW_LINEAR a b x0 x1 x = a /= 0 ==>
  approxEqual 1e-6 (inverseLerp (a*x0+b) (a*x1+b) (a*x+b)) 
                   (inverseLerp x0 x1 x)

prop_inverseLerpHomog0_LAW_DEF :: Affine f Double -> Affine f Double -> Affine f Double -> Property
prop_inverseLerpHomog0_LAW_DEF x0 x1 x =
  approxEqual 0 (inverseLerpHomog0 x0 x1 x) 
       (inverseLerp x0 x1 (x + x0))

prop_inverseLerpHomog0_LAW_LINEAR :: Affine f Double -> Affine f Double -> Double -> Double -> Affine f Double -> Affine f Double -> Property
prop_inverseLerpHomog0_LAW_LINEAR x0 x1 a b x2 x3 =
  approxEqual 1e-6
    (inverseLerpHomog0 x0 x1 (a*^x2 + b*^x3)) 
    (a*inverseLerpHomog0 x0 x1 x2 + b*inverseLerpHomog0 x0 x1 x3)

-- inverse properties
prop_lerp_inverseLerp_rightInverse :: Affine f Double -> Affine f Double -> Double -> Property
prop_lerp_inverseLerp_rightInverse x0 x1 t = (x0 /= x1 && t >= 0 && t <= 1) ==> 
  approxEqual 1e-6 (inverseLerp x0 x1 (lerp x0 x1 t)) t

prop_inverseLerp_lerp_leftInverse :: Affine f Double -> Affine f Double -> Affine f Double -> Property
prop_inverseLerp_lerp_leftInverse x0 x1 x = (x0 /= x1 && x >= x0 && x <= x1) ==>
  approxEqualAffine 1e-6 (lerp x0 x1 (inverseLerp x0 x1 x)) x

-- affineMap properties
prop_affineMap_LAW_1_a :: Affine f Double -> Affine f Double -> Affine f Double -> Affine f Double -> Property
prop_affineMap_LAW_1_a x0 x1 y0 y1 =
  (x0 /= x1) ==> approxEqualAffine 0 (affineMap x0 x1 y0 y1 x0) y0

prop_affineMap_LAW_1_b :: Affine f1 Double -> Affine f1 Double -> Affine f Double -> Affine f Double -> Property
prop_affineMap_LAW_1_b x0 x1 y0 y1 =
  (x0 /= x1) ==> approxEqualAffine 0 (affineMap x0 x1 y0 y1 x1) y1

prop_affineMap_LAW_2 :: Affine f1 Double -> Affine f1 Double -> Affine f2 Double -> Affine f2 Double -> Double -> Property
prop_affineMap_LAW_2 x0 x1 y0 y1 x = (x0 /= x1) ==>
  let affineMapped = affineMap x0 x1 y0 y1 (toAffine x)
      t = inverseLerp x0 x1 (toAffine x)
      lerpResult = lerp y0 y1 t
  in approxEqualAffine 0 affineMapped lerpResult

prop_affineMap_LAW_3 :: Affine f2 Double -> Affine f2 Double -> Affine f3 Double -> Affine f3 Double -> Affine f Double -> Affine f Double -> Affine f2 Double -> Property
prop_affineMap_LAW_3 x0 x1 y0 y1 z0 z1 x = (x0 /= x1) ==>
  approxEqualAffine 1e-6
    (affineMap y0 y1 z0 z1 (affineMap x0 x1 y0 y1 x)) 
    (affineMap x0 x1 z0 z1 x)

prop_affineMap_LAW_4 :: Affine f1 Double -> Affine f1 Double -> Affine f1 Double -> Affine f1 Double -> Affine f Double -> Affine f Double -> Affine f1 Double -> Property
prop_affineMap_LAW_4 a b x0 x1 y0 y1 x = (x0 /= x1) && (a /= 0) ==>
  approxEqualAffine 1e-6
    (affineMap (a*x0+b) (a*x1+b) y0 y1 (a*x+b)) 
    (affineMap x0 x1 y0 y1 x)

-- LAW 5: (x0 /= x1 => (affineMap x0 x1 (a*y0+b) (a*y1+b)) x == a*((affineMap x0 x1 y0 y1) x) + b)
prop_affineMap_LAW_5 :: Affine f1 Double -> Affine f1 Double -> Affine f Double -> Affine f Double -> Affine f Double -> Affine f Double -> Affine f1 Double -> Property
prop_affineMap_LAW_5 x0 x1 y0 y1 a b x = (x0 /= x1) ==>
  approxEqualAffine 1e-6
    (affineMap x0 x1 (a*y0+b) (a*y1+b) x)
    (a * (affineMap x0 x1 y0 y1 x) + b)

prop_affineMap_LAW_7 :: Affine f1 Double -> Affine f1 Double -> Affine f Double -> Affine f Double -> Affine f1 Double -> Affine f1 Double -> Property
prop_affineMap_LAW_7 x0 x1 y0 y1 x x' =
  (x0 /= x1 && x' /= x1) ==>
    approxEqualAffine 1e-6
      (affineMap x0 x1 y0 y1 x)
      (affineMap x' x1 (affineMap x0 x1 y0 y1 x') y1 x)

prop_affineMap_LAW_8 :: Affine f1 Double -> Affine f1 Double -> Affine f Double -> Affine f Double -> Affine f1 Double -> Affine f1 Double -> Property
prop_affineMap_LAW_8 x0 x1 y0 y1 x x' =
  (x0 /= x1 && x0 /= x') ==>
    approxEqualAffine 1e-6
      (affineMap x0 x1 y0 y1 x)
      (affineMap x0 x' y0 (affineMap x0 x1 y0 y1 x') x)

-- For a chosen mapping [x0, x1] to [y0, y1], calculate a and b
calculateCoefficients :: Fractional b => b -> b -> b -> b -> (b, b)
calculateCoefficients x0 x1 y0 y1 = 
    let a = (y1 - y0) / (x1 - x0)
        b = y0 - a * x0
    in (a, b)

prop_affineMap_LAW_9 :: Affine f Double -> Affine f Double -> Affine f Double -> Affine f Double -> Affine f Double -> Property
prop_affineMap_LAW_9 x0 x1 y0 y1 x = (x0 /= x1) ==>
    let (a, b) = calculateCoefficients x0 x1 y0 y1
        affineResult = affineMap x0 x1 y0 y1 x
        expected = a*x + b
    in approxEqualAffine 1e-9 affineResult expected

prop_affineMap_LAW_10 :: Affine f Double -> Affine f Double -> Affine f Double -> Affine f Double -> Affine f Double -> Property
prop_affineMap_LAW_10 a b x0 x1 x = (x0 /= x1) ==>
  let y0 = a * x0 + b
      y1 = a * x1 + b
      result = affineMap x0 x1 y0 y1 x
      expected = a*x + b
  in approxEqualAffine 1e-9 result expected


main :: IO ()
main = do
  quickCheck prop_lerp_LAW_IMPLEMENTATION
  quickCheck prop_lerp_LAW_ZERO
  quickCheck prop_lerp_LAW_UNIT
  quickCheck prop_lerpHomog0_LAW_DEF_1
  quickCheck prop_lerpHomog0_LAW_DEF_2
  quickCheck prop_lerpHomog0_LAW_ZERO
  quickCheck prop_lerpHomog0_LAW_LINEAR
  quickCheck prop_lerpHomog0_LAW_AFFINE
  quickCheck prop_lerpHomog0_LAW_DEF_5
  quickCheck prop_lerpHomog0_LAW_DEF_6
  quickCheck prop_lerpHomog0_LAW_IMPLEMENTATION
  
  quickCheck prop_inverseLerp_LAW_IMPLEMENTATION
  quickCheck prop_inverseLerp_LAW_ZERO
  quickCheck prop_inverseLerp_LAW_UNIT
  quickCheck prop_inverseLerp_LAW_LINEAR
  quickCheck prop_inverseLerpHomog0_LAW_DEF
  quickCheck prop_inverseLerpHomog0_LAW_LINEAR
  
  quickCheck prop_lerp_inverseLerp_rightInverse
  quickCheck prop_inverseLerp_lerp_leftInverse
  
  quickCheck prop_affineMap_LAW_1_a
  quickCheck prop_affineMap_LAW_1_b
  quickCheck prop_affineMap_LAW_2
  quickCheck prop_affineMap_LAW_3
  quickCheck prop_affineMap_LAW_4
  quickCheck prop_affineMap_LAW_5
  quickCheck prop_affineMap_LAW_7
  quickCheck prop_affineMap_LAW_8
  quickCheck prop_affineMap_LAW_9
  quickCheck prop_affineMap_LAW_10
