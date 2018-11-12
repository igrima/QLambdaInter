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
module QTypes(QType(..), tB, tBn, (|=>), tSup, (|*|), tProd
                       , isDuplicable, isQBitType, isValidQType
             )
 where

data QType = TB
           | TSup QType
           | TFun QType QType
           | TProd [ QType ]
        deriving (Eq, Ord)
  {- REP.INV.:
       In (Prod qts), elements of qts do not have Fun on any level.
       In (Fun qt1 qt2), qt1 do not have Fun on any level.
       -- Use functions for construction instead of constructors
       
     OBS.: 
       QBitType   ::= B | S(QBitType) | Prod [ QBitType ]
       ValidQType ::= QBitType | QBitType => ValidQType | S(ValidQType)
  -}
        
isQBitType :: QType -> Bool
isQBitType TB         = True
isQBitType (TFun _ _) = False
isQBitType (TSup t)   = isQBitType t
isQBitType (TProd ts) = all isQBitType ts

isValidQType :: QType -> Bool
isValidQType (TSup t)     = isValidQType t
isValidQType (TFun t1 t2) = isQBitType t1 && isValidQType t2
isValidQType t            = isQBitType t

isDuplicable :: QType -> Bool
isDuplicable TB         = True
isDuplicable (TProd ts) = all isDuplicable ts
isDuplicable _          = False

---------------------------------------------------------
-- Functions for construction (DO NOT USE DATA CONSTRUCTORS)
---------------------------------------------------------
tB :: QType
tB = TB

tBn :: Int -> QType
tBn n = TProd (replicate n tB)

(|=>) :: QType -> QType -> QType
(|=>) t u = if (isQBitType t)
             then if (isValidQType u)
                   then TFun t u
                   else error ("Result is not a valid QType for |=>: " ++ show u)
             else error ("Argument is not a QBitType for |=>: " ++ show t)

tSup :: QType -> QType
tSup t = if (isValidQType t)
         then TSup t
         else error ("Argument is not a valid QType for Sup: " ++ show t)

(|*|) :: QType -> QType -> QType         
(TProd ts) |*| (TProd ts') = TProd (ts++ts')
(TProd ts) |*| t'          = TProd (ts++[t'])
t          |*| (TProd ts') = TProd (t:ts')
t          |*| t'          = TProd [t,t']         

tProd :: [ QType ] -> QType
tProd ts = if (all isQBitType ts) 
           then TProd ts 
           else error ("Some argument is not a QBitType: " ++ show ts)
         
---------------------------------------------------------
-- Show
--   (uses LaTeX macros from z-preamble)
---------------------------------------------------------
instance Show QType where
  show t = myShowQT t
  
myShowQT TB         = "\\BaseQ"
myShowQT (TSup t)   = "\\TSup{" ++ show t ++ "}"
myShowQT (TFun t u) = "\\TFun{" ++ show t ++ "}{" ++ show u ++ "}"
myShowQT (TProd ts) | all isDuplicable ts = "\\BaseQN{" ++ show (length ts) ++ "}"
myShowQT (TProd ts) = myShowListProd ts
myShowQT _          = error "Extend the function in case you extend the type"

myShowListProd [x]    = show x
myShowListProd (x:ts) = show x ++ " \\times " ++ myShowListProd ts
