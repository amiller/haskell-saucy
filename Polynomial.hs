{-# LANGUAGE DataKinds, FlexibleInstances, MultiParamTypeClasses,
             OverloadedLists, PatternSynonyms
#-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ParallelListComp #-}

module Polynomial where

import Data.List (tails)
import Data.Poly
import Data.Vector (forM,fromList)
import qualified Data.Vector ((++))
import Data.Field.Galois (Prime, toP)
import ProcessIO
import System.Random


type Fq = Prime 53


three :: Fq
three = 3

type PolyFq = VPoly Fq


-- Random field element
randFq :: MonadITM m => m Fq
randFq = getNbits 120 >>= return . toP

-- Build poly from coefficients
polyFromCoeffs :: [Fq] -> PolyFq
polyFromCoeffs = toPoly . fromList

polyZero :: PolyFq
polyZero = polyFromCoeffs []

randomWithZero :: MonadITM m => Int -> Fq -> m PolyFq
randomWithZero t z = do
  -- Random degree t polynomial phi, such that phi(0) = z
  coeffs <- forM (fromList [0..(t-1)]) (\_ -> randFq)
  return $ toPoly $ fromList [z] Data.Vector.++ coeffs


randomDegree :: MonadITM m => Int -> m PolyFq
randomDegree t = forM [0..t] (\_ -> randFq) >>= return . toPoly

testp :: PolyFq
testp = toPoly [1,2,3]

test1 = runITMinIO 120 $ randomDegree 5

-- evalPoly
test2' = runITMinIO 120 $ do
  f <- randomDegree 5
  return $ eval f 0

  
-- Add multiple polys
test3 = testp + testp

-- Interpolate
test4 = eval (polyInterp [(0,2),(1,4)]) three

_t1 :: Fq
_t1 = 2
_t2 :: PolyFq
_t2 = toPoly [1,2,3]
test5 = [_t1] * _t2

-- Lagrange interpolation

-- This is taken from polynomial package,
-- https://hackage.haskell.org/package/polynomial-0.7.3/docs/src/Math-Polynomial-Interpolation.html#polyInterp

-- |Evaluate a polynomial passing through the specified set of points.  The
-- order of the interpolating polynomial will (at most) be one less than 
-- the number of points given.

sclMul :: Fq -> PolyFq -> PolyFq
sclMul y p = (toPoly [y]) * p

polyInterp ::  [(Fq,Fq)] -> PolyFq
polyInterp xys = 
  let (xs,ys) = unzip xys in
  let ps = lagrangeBasis xs in
  foldl1 (+) [sclMul y p | (y,p) <- zip ys ps]

select :: [a] -> [(a,[a])]
select [] = []
select (x:xs) = (x, xs) : [(y, x:ys) | (y, ys) <- select xs]

lagrangeBasis :: [Fq] -> [PolyFq]
lagrangeBasis xs = 
    [ foldl1 ((*) :: PolyFq -> PolyFq -> PolyFq)
        [ if q /= 0
            then toPoly [-x_j / q, 1 / q]
            else error ("lagrangeBasis: duplicate root")
        | x_j <- otherXs
        , let q = x_i - x_j
        ]
    | (x_i, otherXs) <- select xs
    ]

