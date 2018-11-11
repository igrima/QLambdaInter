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
module QTypes where


data QType = B
           | TSup QType
           | Fun QType QType
        deriving (Eq, Ord)

(|->) :: QType -> QType -> QType
(|->) t u = if (isQBitType t)
             then Fun t u
             else error ("Argument is not a QBitType for |->: " ++ show t)

sup :: QType -> QType
sup t = TSup t

baseQ :: QType
baseQ = B

isQBitType :: QType -> Bool
isQBitType B         = True
isQBitType (TSup t)   = isQBitType t
isQBitType (Fun _ _) = False

isProperType :: QType -> Bool
isProperType B         = True
isProperType (TSup _)   = True
isProperType (Fun t _) = isQBitType t

---------------------------------------------------------
-- Show
--   (uses LaTeX macros from z-prelude)
---------------------------------------------------------
instance Show QType where
  show t = myShowQT t
  
myShowQT B                    = "\\BaseQ"
myShowQT (TSup t)              = "\\TSup{" ++ show t ++ "}"
myShowQT (Fun mt@(Fun _ _) t) = "\\Tfun{(" ++ show mt ++ ")}{" ++ show t ++ "}"
myShowQT (Fun mt t)           = "\\Tfun{" ++ show mt ++ "}{" ++ show t ++ "}"
