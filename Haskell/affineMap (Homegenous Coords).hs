#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci

import Linear.Matrix -- For matrix operations
import Linear.V2     -- For 2D vectors
import Linear.Vector hiding (lerp)

applyAffineTransformation :: Floating a => M22 a -> V2 a -> V2 a
applyAffineTransformation matrix input = matrix !* input

fahrenheitToSIMatrix :: Floating a => M22 a
fahrenheitToSIMatrix = V2 (V2 0.556 0) (V2 255.372 1)

convertFahrenheitToSI :: Floating a => a -> a
convertFahrenheitToSI fahrenheit = 
  let inputVector = V2 fahrenheit 1
      outputVector = applyAffineTransformation fahrenheitToSIMatrix inputVector
  in case outputVector of
       V2 si _ -> si

main :: IO ()
main = print $ convertFahrenheitToSI 32 -- Example usage


newtype Affine f a = Affine {fromAffine :: a}
toAffine = Affine

instance Show a => Show (Affine f a) where
  show = show . fromAffine

instance (Fractional a) => Num (Affine f a) where
  (+) a b = toAffine $ (fromAffine a) + (fromAffine b)
  (-) a b = toAffine $ (fromAffine a) - (fromAffine b)
  (*) a b = toAffine $ (fromAffine a) * (fromAffine b)
  abs a = toAffine $ abs (fromAffine a)
  signum a = toAffine $ signum (fromAffine a)
  fromInteger i = toAffine $ fromInteger i

data Celcius' = Celcius'
type Celcius = Affine Celcius'

data Fahrenheit' = Fahrenheit'
type Fahrenheit = Affine Fahrenheit'

data SI' = SI'
type SI = Affine SI'

data FracOfRange' = FracOfRange'
type FracOfRange = Affine FracOfRange'

data Degrees' = Degrees'
type Degrees = Affine Degrees'

instance Fractional a => Fractional (Affine f a) where
  fromRational = toAffine . fromRational
  recip = toAffine . recip . fromAffine
  (/) a b = toAffine $ fromAffine a / fromAffine b

lerp :: (Fractional a) => Affine f a -> Affine f a -> a -> Affine f a
lerp x0' x1' t = toAffine $ (1 - t)*x0 + t*x1
  where x0 = fromAffine x0'
        x1 = fromAffine x1'

lerpHomog0 x0 x1 t = lerp x0 x1 t - lerp x0 x1 0

inverseLerp :: (Fractional a, Eq a) => Affine f a -> Affine f a -> Affine f a -> a
inverseLerp x0' x1' x' = if x0 /= x1 then (x - x0) / (x1 - x0) else 0.0
  where x0 = fromAffine x0'
        x1 = fromAffine x1'
        x = fromAffine x'

affineMap :: (Fractional a, Eq a) => Affine f1 a -> Affine f1 a -> Affine f2 a -> Affine f2 a -> Affine f1 a -> Affine f2 a
affineMap x0 x1 y0 y1 x = lerp y0 y1 . inverseLerp x0 x1 $ x

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
        firstProngGroupNumberStart
        (firstProngGroupNumberStart + firstProngGroupNumberStep)
        (mapFracOfRangeToDegrees firstProngGroupStart)
        (mapFracOfRangeToDegrees (firstProngGroupStart + firstProngGroupStep))

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

-- Please change the above to instead express the affine transformations as 2x2 matrices operating on homogeneous coordinates.