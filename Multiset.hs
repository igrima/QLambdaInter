-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for paper "Isomorphisms as Equalities" 
--               by Alejandro Díaz-Caro and Pablo E. "Fidel" Martínez López
-- Version: 1.0
-- Developer: Fidel <fidel -at- unq.edu.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2015  Pablo E. Martínez López
-- 
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- You may not change or alter any portion of this comment or credits
-- of supporting developers from this source code or any supporting
-- source code which is considered copyrighted (c) material of the
-- original comment or credit authors.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
-- GNU General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with this program; if not, write to the Free Software
-- Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
-- -----------------------------------------------------------------------------------------------------------//
module Multiset(Multiset, empty, isEmpty, singleton, isSingleton, fromSingleton
                        , union, intersect, occurs, flatten
                        , equals, included, substract
                        , order, foreach, fromList, fromMultiList, fullshow)
 where

 -- They are represented as ordered lists (by element)
 -- This facilitates the combination operations, achieving O(max(n,m)) instead of O(n.m)
newtype Multiset a = MS [(a,Int)]
   deriving (Eq, Ord)
   {- REP.INV.: in MS ans
        - ans is ordered by first component
        - there are no repetitions in first components
        - second components are >0
    -}
unMS (MS m) = m

---------------------------------------------------------
-- Interface
---------------------------------------------------------
empty         :: Multiset s
isEmpty       :: Multiset a -> Bool
singleton     :: a -> Multiset a
isSingleton   :: Multiset a -> Bool
fromSingleton :: Multiset a -> a
union         :: Ord a => Multiset a -> Multiset a -> Multiset a
intersect     :: Ord a => Multiset a -> Multiset a -> Multiset a
occurs        :: Ord a => a -> Multiset a -> Int
flatten       :: Ord a => Multiset (Multiset a) -> Multiset a
equals        :: Ord a => Multiset a -> Multiset a -> Bool
included      :: Ord a => Multiset a -> Multiset a -> Bool
substract     :: Ord a => Multiset a -> Multiset a -> Maybe (Multiset a)
order         :: Ord a => Multiset a -> [(a,Int)]
foreach       :: (Ord a, Ord b) => (a->b) -> Multiset a -> Multiset b
fromList      :: Ord a => [a] -> Multiset a
fromMultiList :: Ord a => [(a,Int)] -> Multiset a

---------------------------------------------------------
-- Implementation
---------------------------------------------------------
empty                     = MS []
isEmpty (MS r)            = null r
singleton  x              = MS (singletonRep x)
multisingleton x n        = MS (multisingletonRep x n)
isSingleton (MS xs)       = isSingletonRep xs
fromSingleton (MS xs)     = fromSingletonRep xs
union     (MS r1) (MS r2) = MS (unionRep r1 r2)
intersect (MS r1) (MS r2) = MS (intersectRep r1 r2)
occurs     x      (MS r)  = occursRep x r
flatten   (MS mr)         = MS (flattenRep mr)
equals    (MS r1) (MS r2) = equalsRep r1 r2
included  (MS r1) (MS r2) = includedRep r1 r2
substract (MS r1) (MS r2) = fmap MS (substractRep r1 r2)
order     (MS r)          = orderRep r
foreach f (MS xs)         = MS (foreachRep f xs)
fromList  xs              = foldr (\x m -> union (singleton x) m) (MS []) xs
fromMultiList xns         = foldr (\(x,n) m -> union (multisingleton x n) m) (MS []) xns

---------------------------------------------------------
-- Functions over representation
---------------------------------------------------------
singletonRep x = [(x,1)]

multisingletonRep x n = [(x,n)]

isSingletonRep [(_,1)] = True
isSingletonRep _       = False

fromSingletonRep [(x,1)] = x
fromSingletonRep _       = error "It is not a singleton!"

unionRep []                ys                = ys
unionRep xs                []                = xs
unionRep xs@(xn@(x,n):xs') ys@(ym@(y,m):ys') =
    if      x == y
    then      (x,n+m):(unionRep xs' ys') 
    else if x < y
    then      xn : unionRep xs' ys
    else      ym : unionRep xs ys'

intersectRep []                _                 = []
intersectRep _                 []                = []
intersectRep xs@(xn@(x,n):xs') ys@(ym@(y,m):ys') =
    if      x == y
    then      (x,min n m):(intersectRep xs' ys') 
    else if x < y
    then      intersectRep xs' ys
    else      intersectRep xs ys'
    
occursRep _ [] = 0
occursRep x ((y,ny):ynys') =
    if      x == y
    then      ny
    else if x < y
    then      0
    else      occursRep x ynys' 

flattenRep :: Ord a => [(Multiset a, Int)] -> [(a,Int)]
flattenRep []         = []
flattenRep ((m,i):ms) = unionRep (map (\(x,n) -> (x,n*i)) (unMS m)) (flattenRep ms)

equalsRep :: Ord a => [(a,Int)] -> [(a,Int)] -> Bool
equalsRep = (==)

includedRep [] _  = True
includedRep xs [] = False
includedRep xs@((x,n):xs') ys@((y,m):ys') =
    if      x == y
    then    n<=m && includedRep xs' ys'  
    else if x < y
    then    False
    else    includedRep xs ys'
	
-- PRECOND: substractRep xs ys, ys is included in xs
substractRep ys []  = Just ys
substractRep [] _   = Nothing
substractRep ys@(ym@(y,m):ys') xs@((x,n):xs') =
    if      x == y
    then    case (compare n m) of
              LT -> fmap ((y,m-n):) (substractRep ys' xs')
              EQ -> substractRep ys' xs'
              GT -> Nothing
    else if x < y
    then    Nothing
    else    fmap (ym :) (substractRep ys' xs)

orderRep = id

foreachRep f xs = normalizeRep (map (\(a,i) -> (f a,i)) xs)

normalizeRep :: Ord a => [(a,Int)] -> [(a,Int)]
-- It orders the output and elminate dupliates. Output satisfies Multisets representation invariant.
normalizeRep = foldr (\an -> unionRep [an]) []

---------------------------------------------------------
-- Show
--  (uses LaTeX macros from z-prelude.tex)
---------------------------------------------------------
instance Show a => Show (Multiset a) where
  show (MS xs) = showRep xs

fullshow (MS xs) = fullShowRep xs

fullShowRep []      = ""
fullShowRep [(x,1)] = showN 1 (show x)
fullShowRep xs      = "\\Tmulti{" ++ showRep xs ++ "}"

showRep []         = ""
showRep [(x,n)]    = showN n (show x)
showRep ((x,n):xs) = showN n (show x) ++ ",\\ " ++ showRep xs  
  
showN 0 sx = ""
showN 1 sx = sx
--showN n sx = sx ++ "^" ++ show n
showN n sx = sx ++ ",\\ " ++ showN (n-1) sx
