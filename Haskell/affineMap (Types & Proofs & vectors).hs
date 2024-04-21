#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package linear-1.21.10

import Data.Functor.Identity
import Linear.Vector hiding (lerp)

newtype Affine vector tag a = Affine {fromAffine :: vector a}
toAffine = Affine

instance Show (vector a) => Show (Affine vector tag a) where
  show = show . fromAffine

instance Num (vector a) => Num (Affine vector tag a) where
  (+) a b = toAffine $ (fromAffine a) + (fromAffine b)
  (-) a b = toAffine $ (fromAffine a) - (fromAffine b)
  (*) a b = toAffine $ (fromAffine a) * (fromAffine b)
  abs a = toAffine $ abs (fromAffine a)
  signum a = toAffine $ signum (fromAffine a)
  fromInteger i = toAffine $ fromInteger i

data Celcius' = Celcius'
type Celcius = Affine Identity Celcius'

data Fahrenheit' = Fahrenheit'
type Fahrenheit = Affine Identity Fahrenheit'

data SI' = SI'
type SI = Affine Identity SI'

data FracOfRange' = FracOfRange'
type FracOfRange = Affine Identity FracOfRange'

data Degrees' = Degrees'
type Degrees = Affine Identity Degrees'

instance Fractional (vector a) => Fractional (Affine vector tag a) where
  fromRational = toAffine . fromRational
  recip = toAffine . recip . fromAffine
  (/) a b = toAffine $ fromAffine a / fromAffine b

-- Linearly interpolates between x0 and x1 by t.
lerp :: (Num (vector a), Functor vector, Fractional a) => Affine vector tag a -> Affine vector tag a -> a -> Affine vector tag a
lerp x0' x1' t = toAffine $ (1 - t)*^x0 + t*^x1
  where x0 = fromAffine x0'
        x1 = fromAffine x1'

-- Linearly interpolates between x0 and x1 by t.
lerp2D :: (Num (vector a), Functor vector, Fractional a) => Affine vector tag a -> Affine vector tag a -> Affine vector tag a -> (a,a) -> Affine vector tag a
lerp2D x0' x1' x2' (t1,t2) = toAffine $ (1 - t1 - t2)*^x0 + t1*^x1 + t2*^x2
  where x0 = fromAffine x0'
        x1 = fromAffine x1'
        x2 = fromAffine x2'

lerpHomog0 x0 x1 t = lerp x0 x1 t - lerp x0 x1 0
{- 
    lerp_LAW_IMPLEMENTATION:
        lerp x0 x1 t == (1 - t)*x0 + t*x1
        Proofs:
            Given:
                lerpHomog0_LAW_DEF_2
                lerpHomog0_LAW_IMPLEMENTATION
            We have:
                lerpHomog0 x0 x1 t == lerp x0 x1 t - x0                                                     [ lerpHomog0_LAW_DEF_2 ]
                lerp x0 x1 t == lerpHomog0 x0 x1 t + x0                                                     [ laws_of_equations ]
                lerp x0 x1 t == t*(x1 - x0) + x0                                                            [ lerpHomog0_LAW_IMPLEMENTATION ]
                lerp x0 x1 t == (1 - t)*x0 + t*x1                                                           [ laws_of_add_and_mult ]
    
    lerp_LAW_ZERO:
        lerp x0 x1 0 == x0
        Proofs:
            Given:
                lerp_LAW_IMPLEMENTATION
            We have:
                lerp x0 x1 t == (1 - t)*x0 + t*x1                                                           [ lerp_LAW_IMPLEMENTATION ]
                lerp x0 x1 0 == (1 - 0)*x0 + 0*x1                                                           [ universal_instantiation ]
                lerp x0 x1 0 == x0                                                                          [ laws_of_add_and_mult ]
    
    lerp_LAW_UNIT:
        lerp x0 x1 1 == x1
        Proofs:
            Given:
                lerp_LAW_IMPLEMENTATION
            We have:
                lerp x0 x1 t == (1 - t)*x0 + t*x1                                                           [ lerp_LAW_IMPLEMENTATION ]
                lerp x0 x1 1 == (1 - 1)*x0 + 1*x1                                                           [ universal_instantiation ]
                lerp x0 x1 1 == x1                                                                          [ laws_of_add_and_mult ]
    
    lerpHomog0_LAW_DEF_1:
        lerpHomog0 x0 x1 t == lerp x0 x1 t - lerp x0 x1 0
        Proofs:
            Given:
                lerp_LAW_IMPLEMENTATION
                lerpHomog0_LAW_IMPLEMENTATION
            We have:
                lerpHomog0 x0 x1 t == c*(x1 - x0)                                                           [ lerpHomog0_LAW_IMPLEMENTATION ]
                lerpHomog0 x0 x1 t == (1 - t)*x0 + t*x1 - (1 - 0)*x0 + 0*x1                                 [ laws_of_add_and_mult ]
                lerpHomog0 x0 x1 t == lerp x0 x1 t - lerp x0 x1 0                                           [ lerp_LAW_IMPLEMENTATION ]
    
    lerpHomog0_LAW_DEF_2:
        lerpHomog0 x0 x1 t == lerp x0 x1 t - x0
        Proofs:
            Given:
                lerp_LAW_ZERO
                lerpHomog0_LAW_DEF_1
            We have:
                lerpHomog0 x0 x1 t == lerp x0 x1 t - lerp x0 x1 0                                           [ lerpHomog0_LAW_DEF_1 ]
                                   == lerp x0 x1 t - x0                                                     [ lerp_LAW_ZERO ]
    
    lerpHomog0_LAW_ZERO:
        lerpHomog0 x0 x1 0 == 0
        Proofs:
            Given:
                lerp_LAW_ZERO
                lerpHomog0_LAW_DEF_2
            We have:
                lerpHomog0 x0 x1 t == lerp x0 x1 t - x0                                                     [ lerpHomog0_LAW_DEF_2 ]
                lerpHomog0 x0 x1 0 == lerp x0 x1 0 - x0                                                     [ universal_instantiation ]
                                   == x0 - x0                                                               [ lerp_LAW_ZERO ]
                                   == 0                                                                     [ laws_of_add_and_mult ]
            Given:
                lerpHomog0_LAW_IMPLEMENTATION
            We have:
                lerpHomog0 x0 x1 c == c*(x1 - x0)                                                           [ lerpHomog0_LAW_IMPLEMENTATION ]
                lerpHomog0 x0 x1 0 == 0*(x1 - x0)                                                           [ universal_instantiation ]
                                   == 0                                                                     [ laws_of_add_and_mult ]
    
    lerpHomog0_LAW_LINEAR:
        lerpHomog0 x0 x1 (a*t0 + b*t1) == a*lerpHomog0 x0 x1 t0 + b*lerpHomog0 x0 x1 t1
        Proofs:
            Given:
                lerpHomog0_LAW_IMPLEMENTATION
            We have:
                lerpHomog0 x0 x1 (a*t0 + b*t1) == (a*t0 + b*t1)*(x1 - x0)                                   [ lerpHomog0_LAW_IMPLEMENTATION ]
                lerpHomog0 x0 x1 (a*t0 + b*t1) == a*t0*(x1 - x0) + b*t1*(x1 - x0)                           [ laws_of_add_and_mult ]
                lerpHomog0 x0 x1 (a*t0 + b*t1) == a*lerpHomog0 x0 x1 t0 + b*lerpHomog0 x0 x1 t1             [ lerpHomog0_LAW_IMPLEMENTATION ]
    
    lerpHomog0_LAW_AFFINE:
        (lerpHomog0 (a*y0+b) (a*y1+b)) x == a*((lerpHomog0 y0 y1) x)
        Proofs:
            Given:
                lerpHomog0_LAW_IMPLEMENTATION
            We have:
                (lerpHomog0 (a*y0+b) (a*y1+b)) x == (lerpHomog0 (a*y0+b) (a*y1+b)) x                        [ reflexity ]
                (lerpHomog0 (a*y0+b) (a*y1+b)) x == x*((a*y1+b) - (a*y0+b))                                 [ lerpHomog0_LAW_IMPLEMENTATION ]
                (lerpHomog0 (a*y0+b) (a*y1+b)) x == a*x*((y1+b) - (y0+b))                                   [ laws_of_add_and_mult ]
                (lerpHomog0 (a*y0+b) (a*y1+b)) x == a*x*(y1 - y0)                                           [ laws_of_add_and_mult ]
                (lerpHomog0 (a*y0+b) (a*y1+b)) x == a*((lerpHomog0 y0 y1) x)                                [ lerpHomog0_LAW_IMPLEMENTATION ]
    
    lerpHomog0_LAW_DEF_5:
        lerpHomog0 x0 x1 1 == x1 - x0
        Proofs:
            Given:
                lerp_LAW_UNIT
                lerpHomog0_LAW_DEF_2
            We have:
                lerpHomog0 x0 x1 t == lerp x0 x1 t - x0                                                     [ lerpHomog0_LAW_DEF_2 ]
                lerpHomog0 x0 x1 1 == lerp x0 x1 1 - x0                                                     [ universal_instantiation ]
                                   == x1 - x0                                                               [ universal_instantiation ]
    
    lerpHomog0_LAW_DEF_6:
        lerpHomog0 x0 x1 c == c*lerpHomog0 x0 x1 1
        Proofs:
            Given:
                lerpHomog0_LAW_LINEAR
            We have:
                lerpHomog0 x0 x1 (a*t0 + b*t1) == a*lerpHomog0 x0 x1 t0 + b*lerpHomog0 x0 x1 t1             [ lerpHomog0_LAW_LINEAR ]
                lerpHomog0 x0 x1 (c*1 + 0*t1) == c*lerpHomog0 x0 x1 1 + 0*lerpHomog0 x0 x1 t1               [ universal_instantiation ]
                lerpHomog0 x0 x1 c == c*lerpHomog0 x0 x1 1                                                  [ laws_of_add_and_mult ]
    
    lerpHomog0_LAW_IMPLEMENTATION:
        lerpHomog0 x0 x1 c == c*(x1 - x0)
        Proofs:
            Given:
                lerpHomog0_LAW_DEF_5
                lerpHomog0_LAW_DEF_6
            We have:
                lerpHomog0 x0 x1 c == c*lerpHomog0 x0 x1 1                                                  [ lerpHomog0_LAW_DEF_6 ]
                                   == c*(x1 - x0)                                                           [ lerpHomog0_LAW_DEF_5 ]
-}

-- Calculates the interpolation factor t for a value x in the range from x0 to x1.
inverseLerp :: (Fractional a, Eq a) => Affine vector tag a -> Affine vector tag a -> Affine vector tag a -> a
inverseLerp x0' x1' x' = undefined --if x0 /= x1 then (x - x0) / (x1 - x0) else 0.0
  where x0 = fromAffine x0'
        x1 = fromAffine x1'
        x = fromAffine x'
{- 
    inverseLerp_LAW_IMPLEMENTATION:
        inverseLerp x0 x1 x == if x0 /= x1 then (x - x0) / (x1 - x0) else 0
        Proofs:
            
    
    inverseLerp_LAW_ZERO:
        inverseLerp x0 x1 x0 == 0
        Proofs:
            Given:
                inverseLerp_LAW_IMPLEMENTATION
            We have:
                inverseLerp x0 x1 x == if x0 /= x1 then (x - x0) / (x1 - x0) else 0                         [ inverseLerp_LAW_IMPLEMENTATION ]
                inverseLerp x0 x1 x0 == if x0 /= x1 then (x0 - x0) / (x1 - x0) else 0                       [ universal_instantiation ]
                inverseLerp x0 x1 x0 == if x0 /= x1 then 0 else 0                                           [ laws_of_add_and_mult ]
                inverseLerp x0 x1 x0 == 0                                                                   [ laws_of_conditional ]
    
    inverseLerp_LAW_UNIT:
        x0 /= x1 => inverseLerp x0 x1 x1 == 1
        Proofs:
            Given:
                inverseLerp_LAW_IMPLEMENTATION
            We have:
                inverseLerp x0 x1 x == if x0 /= x1 then (x - x0) / (x1 - x0) else 0                         [ inverseLerp_LAW_IMPLEMENTATION ]
                x0 /= x1 => inverseLerp x0 x1 x == if x0 /= x1 then (x - x0) / (x1 - x0) else 0             [ weakening ]
                x0 /= x1 => inverseLerp x0 x1 x1 == if x0 /= x1 then (x1 - x0) / (x1 - x0) else 0           [ universal_instantiation ]
                x0 /= x1 => inverseLerp x0 x1 x1 == (x1 - x0) / (x1 - x0)                                   [ laws_of_conditional ]
                x0 /= x1 => inverseLerp x0 x1 x1 == 1                                                       [ laws_of_add_and_mult ]
    
    inverseLerp_LAW_LINEAR:
        a /= 0 => inverseLerp (a*x0+b) (a*x1+b) (a*x+b) == inverseLerp x0 x1 x
        Proofs:
            
    
    inverseLerpHomog0_LAW_DEF:
        inverseLerpHomog0 x0 x1 x == inverseLerp x0 x1 (x + x0)
        Proofs:
            
    
    inverseLerpHomog0_LAW_LINEAR:
        inverseLerpHomog0 x0 x1 (a*x2 + b*x3) == a*inverseLerpHomog0 x0 x1 x2 + b*inverseLerpHomog0 x0 x1 x3
        Proofs:
            
    
    inverseLerpHomog0_LAW_AFFINE:
        inverseLerpHomog0 (a*x0+b) (a*x1+b) x == 
        Proofs:
            
-}

-- Maps a value x from one range [x0, x1] to another range [y0, y1].
affineMap :: (Num (vector a), Functor vector, Fractional a, Eq a) => Affine vector tag1 a -> Affine vector tag1 a -> Affine vector tag2 a -> Affine vector tag2 a -> Affine vector tag1 a -> Affine vector tag2 a
affineMap x0 x1 y0 y1 x = lerp y0 y1 . inverseLerp x0 x1 $ x
{- 
    affineMap_LAW_1:
        (x0 /= x1
            =>
            (affineMap x0 x1 y0 y1 x0 == y0) AND
            (affineMap x0 x1 y0 y1 x1 == y1) AND
            (a * affineMapHomog x2 + b * affineMapHomog x3 == affineMapHomog (a * x2 + b * x3)
                where affineMapHomog x == affineMap x0 x1 y0 y1 (x + x0) - affineMap x0 x1 y0 y1 x0))
            Proofs:
                
    
    affineMap_LAW_2:
        affineMap x0 x1 y0 y1 x == lerp y0 y1 . inverseLerp x0 x1 $ x
            where lerp x0 x1 t == x0 * (1 - t) + x1 * t
                  inverseLerp x0 x1 x == if x0 /= x1 then (x - x0) / (x1 - x0) else 0.0
            Proofs:
                
    
    affineMap_LAW_3:
        (x0 /= x1
            =>
            affineMap y0 y1 z0 z1 . affineMap x0 x1 y0 y1 == affineMap x0 x1 z0 z1)
            Proofs:
                Given:
                    affineMap_LAW_2
                    lerp x0 x1 . inverseLerp x0 x1 == id
                We have:
                    (affineMap y0 y1 z0 z1 . affineMap x0 x1 y0 y1) == (lerp z0 z1 . inverseLerp y0 y1 . lerp y0 y1 . inverseLerp x0 x1)
                                                                    == (lerp z0 z1 . inverseLerp x0 x1)
                                                                    == affineMap x0 x1 z0 z1
    
    affineMap_LAW_4:
        (x0 /= x1
            =>
            a /= 0
                =>
                (affineMap (a*x0+b) (a*x1+b) y0 y1) (a*x+b) == (affineMap x0 x1 y0 y1) x)
            Proofs:
                Given:
                    affineMap_LAW_2
                    inverseLerp_LAW_4
                    lerp x0 x1 . inverseLerp x0 x1 == id
                We have:
                    (affineMap (a*x0+b) (a*x1+b) y0 y1) (a*x+b) == (lerp y0 y1 . inverseLerp (a*x0+b) (a*x1+b)) (a*x+b)
                                                                == lerp y0 y1 (inverseLerp (a*x0+b) (a*x1+b) (a*x+b))
                                                                == lerp y0 y1 (inverseLerp x0 x1 x)
    
    affineMap_LAW_5:
        (x0 /= x1
            =>
            (affineMap x0 x1 (a*y0+b) (a*y1+b)) x == a*((affineMap x0 x1 y0 y1) x) + b)
            Proofs:
                
    
    affineMap_LAW_6:
        (x0 /= x1
            =>
            (affineMap y0 y1 z0 z1) x == (affineMap x0 x1 z0 z1) x)
            Proofs:
                
    
    affineMap_LAW_7:
        (x0 /= x1
            =>
            x' /= x1
                =>
                (affineMap x0 x1 y0 y1) x == (affineMap x' x1 ((affineMap x0 x1 y0 y1) x') y1) x)
            Proofs:
                
    
    affineMap_LAW_8:
        (x0 /= x1
            =>
            x0 /= x'
                =>
                (affineMap x0 x1 y0 y1) x == (affineMap x0 x' y0 ((affineMap x0 x1 y0 y1) x')) x)
            Proofs:
                
    
    affineMap_LAW_9:
        (x0 /= x1
            =>
            there exists unique a, b such that:
                (affineMap x0 x1 y0 y1) x == a*x + b)
            Proofs:
                
    
    affineMap_LAW_10:
        (x0 /= x1
            =>
            there exists x0, x1, y0, y1 such that:
                (affineMap x0 x1 y0 y1) x == a*x + b)
            Proofs:
                
-}

firstScaleStartAngle, firstScaleAngularDisplacement :: Degrees Double
firstScaleStartAngle = -45.0
firstScaleAngularDisplacement = 270.0

firstProngGroupStart, firstProngGroupStep :: FracOfRange Double
firstProngGroupStart = 0.0
firstProngGroupStep = 20.0

currProngGroupStart, currProngGroupStep :: FracOfRange Double
currProngGroupStart = 0.0
currProngGroupStep = 20.0

firstProngGroupNumberStart, firstProngGroupNumberStep :: Celcius Double
firstProngGroupNumberStart = 0.0
firstProngGroupNumberStep = 20.0

currProngGroupNumberStart, currProngGroupNumberStep :: Fahrenheit Double
currProngGroupNumberStart = -440.0
currProngGroupNumberStep = 20.0

firstZeroInSI, firstOneInSI, currZeroInSI, currOneInSI :: SI Double
firstZeroInSI = 273.15
firstOneInSI = 274.15
currZeroInSI = 255.372
currOneInSI = 255.928

fracOfRange0, fracOfRange1 :: FracOfRange Double
fracOfRange0 = 0
fracOfRange1 = 1

fahrenheit0, fahrenheit1 :: Fahrenheit Double
fahrenheit0 = 0
fahrenheit1 = 1

celcius0, celcius1 :: Celcius Double
celcius0 = 0
celcius1 = 1

unitsStart, unitsEnd :: Fahrenheit Double
unitsStart = 0
unitsEnd   = 200

mapFracOfRangeToDegrees :: FracOfRange Double -> Degrees Double
mapFracOfRangeToDegrees
    = affineMap
        fracOfRange0
        fracOfRange1
        firstScaleStartAngle
        (firstScaleStartAngle + firstScaleAngularDisplacement)

mapDegreesToCelcius :: Degrees Double -> Celcius Double
mapDegreesToCelcius
    = affineMap
        (mapFracOfRangeToDegrees firstProngGroupStart)
        (mapFracOfRangeToDegrees (firstProngGroupStart + firstProngGroupStep))
        firstProngGroupNumberStart
        (firstProngGroupNumberStart + firstProngGroupNumberStep)

mapFahrenheitToSI :: Fahrenheit Double -> SI Double
mapFahrenheitToSI
    = affineMap
        fahrenheit0
        fahrenheit1
        currZeroInSI
        currOneInSI

mapSIToCelcius :: SI Double -> Celcius Double
mapSIToCelcius
    = affineMap
        firstZeroInSI
        firstOneInSI
        celcius0
        celcius1

mapCelciusToDegrees :: Celcius Double -> Degrees Double
mapCelciusToDegrees
    = affineMap
        (mapDegreesToCelcius firstScaleStartAngle)
        (mapDegreesToCelcius (firstScaleStartAngle + firstScaleAngularDisplacement))
        firstScaleStartAngle
        (firstScaleStartAngle + firstScaleAngularDisplacement)

mapCelciusToFracOfRange :: Fahrenheit Double -> FracOfRange Double
mapCelciusToFracOfRange = affineMap
    unitsStart
    unitsEnd
    fracOfRange0
    fracOfRange1

currScaleStartAngle = (mapCelciusToDegrees . mapSIToCelcius . mapFahrenheitToSI) unitsStart
currScaleEndAngle = (mapCelciusToDegrees . mapSIToCelcius . mapFahrenheitToSI) unitsEnd

new_curr_prong_group_start           = mapCelciusToFracOfRange  currProngGroupNumberStart
new_curr_prong_group_start_plus_step = mapCelciusToFracOfRange (currProngGroupNumberStart + currProngGroupNumberStep)
