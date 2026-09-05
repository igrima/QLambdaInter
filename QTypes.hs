-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for <SOMETHING_HERE>
--               by Alejandro Díaz-Caro, Pablo E. "Fidel" Martínez López and Ignacio D. Grima
-- Version: 1.0
-- Developer: Ignacio D. Grima <nacho -at- fceia.unr.edu.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2017  Ignacio D. Grima, based in code developed by Fidel <fidel -at- unq.edu.ar >
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

-- This is a first order calculus: Functions does not accept functions as a parameter
module QTypes(QType(..), tB, tBn, (|=>), tSup, (|*|), tProd, tailTProd
                       , isLinear, isQBitType, isValidQType
                       , isBaseQBitN, isFunFromQBitN, stripSups, unSup
                       , buildFun, buildSup, buildSups, buildProd
             )
 where

data QType = TB
           | TSup QType
           | TFun QType QType
           | TProd [ QType ]
        deriving (Eq, Ord)
  {- REP.INV.:
       In (Prod qts), len qts >= 2 and its elements do not have Fun on any level.
       In (Fun qt1 qt2), qt1 do not have Fun on any level.
       -- Use functions for construction instead of constructors
       
     OBS.: 
       QBitType   ::= B | S(QBitType) | Prod [ QBitType ]
       ValidQType ::= QBitType | QBitType => ValidQType | S(ValidQType)
  -}
        
isQBitType :: QType -> Bool -- Verifies if it's a value of Phi in the paper (categorical semantics); QBit Types (Q)
isQBitType TB         = True
isQBitType (TFun _ _) = False
isQBitType (TSup t)   = isQBitType t
isQBitType (TProd ts) = (length ts >= 2) && all isQBitType ts
        
isBaseQBitN :: QType -> Bool -- Verifies if it's B^n in the paper (categorical semantics)
isBaseQBitN TB         = True
isBaseQBitN (TProd ts) = (length ts >= 2) && all isBaseQBitN ts
isBaseQBitN _          = False

isValidQType :: QType -> Bool -- Verifies if it's a value of A in the paper (categorical semantics); Types (T)
isValidQType (TSup t)     = isValidQType t
isValidQType (TFun t1 t2) = isQBitType t1 && isValidQType t2
isValidQType t            = isQBitType t

isLinear :: QType -> Bool
isLinear t = not (isBaseQBitN t)

isFunFromQBitN :: QType -> Bool -- Verifies if it's (B^n => A) in the paper
isFunFromQBitN (TFun t _) = isBaseQBitN t
isFunFromQBitN _          = False

---------------------------------------------------------
-- Functions for construction (DO NOT USE DATA CONSTRUCTORS)
---------------------------------------------------------
tB :: QType
tB = TB

-- PRECOND: n>0
tBn :: Int -> QType
tBn 0 = error ("B^0 is not a valid type")
tBn 1 = TB
tBn n = TProd (replicate n tB)

(|=>) :: QType -> QType -> QType
(|=>) t u = buildFun id error t u
buildFun ret rai t u = 
            if (isQBitType t)
             then if (isValidQType u)
                   then ret (TFun t u)
                   else rai ("Result is not a valid QType for |=>: " ++ show u)
             else rai ("Argument is not a QBitType for |=>: " ++ show t)

tSup :: QType -> QType
tSup = buildSups id error 1

buildSups ret rai 0 t          = ret t
buildSups ret rai n t@(TSup _) = ret t
buildSups ret rai n t          = buildSup ret rai t

buildSup ret rai t = if (isValidQType t)
                      then ret (TSup t)
                      else rai ("Argument is not a valid QType for Sup: " ++ show t)

(|*|) :: QType -> QType -> QType
(|*|) = buildProd id error
buildProd :: (QType -> b) -> (String -> b) -> QType -> QType -> b
buildProd ret rai (TProd ts) (TProd ts') = ret (TProd (ts++ts'))
buildProd ret rai (TProd ts) t'          = if isQBitType t'
                                            then ret (TProd (ts++[t']))
                                            else rai ("Invalid type for TProd: " ++ show t')
buildProd ret rai t          (TProd ts') = if isQBitType t
                                            then ret (TProd (t:ts'))
                                            else rai ("Invalid type for TProd: " ++ show t)
buildProd ret rai t          t'          = if (isQBitType t)
                                            then if (isQBitType t')
                                                  then ret (TProd [t,t'])
                                                  else rai ("Invalid type for TProd: " ++ show t')
                                            else rai ("Invalid type for TProd: " ++ show t)

tailTProd :: QType -> QType
tailTProd = tailTP id error
tailTP :: (QType -> b) -> (String -> b) -> QType -> b
tailTP ret _   (TProd [_,t])  = ret t
tailTP ret _   (TProd (_:ts)) = ret (tProd ts)
tailTP _   rai t              = rai ("Invalid type for tailTProd" ++ show t)

-- tProd ts = foldr1 (|*|) ts
tProd :: [ QType ] -> QType
tProd [t]    = t
tProd (t:ts) = t |*| tProd ts

stripSups (TSup t) = (\(n,t)->(n+1, t)) (stripSups t)
stripSups t        = (0, t)

unSup t = snd (stripSups t)
---------------------------------------------------------
-- QTypes Representation Normalization
---------------------------------------------------------
normQT (TSup t)     = tSup (normQT t)
normQT (TFun t1 t2) = normQT t1 |=> normQT t2
normQT (TProd ts)   = tProd (map normQT ts)
normQT t            = t

---------------------------------------------------------
-- Show
--   (uses LaTeX macros from z-preamble)
---------------------------------------------------------
instance Show QType where
  show t = myShowQT t
  
myShowQT TB         = "\\BaseQ"
myShowQT (TSup t)   = "\\TSup{" ++ show t ++ "}"
myShowQT (TFun t u) = "\\TFun{" ++ show t ++ "}{" ++ show u ++ "}"
myShowQT (TProd ts) | all (not . isLinear) ts = "\\BaseQN{" ++ show (length ts) ++ "}"
myShowQT (TProd ts) = myShowListProd ts
myShowQT _          = error "Extend the function in case you extend the type"

myShowListProd [x]    = show x
myShowListProd (x:ts) = show x ++ " \\times " ++ myShowListProd ts
