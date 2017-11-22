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

module QTerms where

import QTypes as QT
import Data.List
--import Error
--import NewVarMonad

type Vble = String
data QBit = KZero | KOne
          deriving (Eq, Ord)
data BaseQT a = Var Vble a
              | Lam Vble QT.QType (BaseQT a) a
              | App (BaseQT a) (BaseQT a) a
              | Base QBit
              | Sup --TODO:NACHO: ACA HAY QUE HACERLO
        deriving (Eq, Ord)

type QTerm       = BaseQT ()
type ChurchQTerm = BaseQT QT.QType

getType :: ChurchQTerm -> QT.QType
getType (Var _ t)     = t
getType (Lam _ _ _ t) = t
getType (App _ _ t)   = t
getType (Base _)      = baseQ

-- PRECOND: the term is ground and well typed 
isValue (App _ _ _) = False
isValue _           = True

isLam (Lam _ _ _ _) = True
isLam _             = False

isGround t = freeVars t == []

freeVars (Var x _) = [x]
freeVars (Lam x _ t _) = freeVars t \\ [x]
freeVars (App t u _) = freeVars t `union` freeVars u
freeVars (Base _)  = []

---------------------------------------------------------
-- Functions for easy construction
---------------------------------------------------------
-- Untyped version
var x     = Var x ()
lam x t e = Lam x t e ()
app r s   = App r s ()
k0, k1 :: QTerm
k0        = Base KZero
k1        = Base KOne

---------------------------------------------------------
-- Show
--  Showing uses LaTeX macros from z-prelude
--  There are 2 versions of show:
--     * one used to pretty display with ovalboxes, etc.
--     * another used to generate Haskell code to build types
---------------------------------------------------------
showQT :: BaseQT a -> String
showQT (Var x _)      = "\\var{" ++ x ++ "}{}"
showQT (Lam x tx r _) = "\\lam{" ++ x ++ "}{" ++ show tx ++ "}{" ++ showQT r ++ "}"
showQT (App r s _)    = "\\app{" ++ showQT r ++ "}{" ++ showQT s ++ "}"
showQT (Base k)       = showBase k


showChQT :: ChurchQTerm -> String  
showChQT (Var x tx)        = "\\chvar{"  ++ x ++ "}{" ++ show tx ++ "}"
showChQT (Lam x tx r tlam) = "\\chlam{"  ++ x ++ "}{" ++ show tx ++ "}{" 
                                         ++ showChQT r    ++ "}{" ++ show tlam ++ "}"
showChQT (App r s tapp)    = "\\chapp{"  ++ showChQT r  ++ "}{" ++ showChQT s  ++ "}{" ++ show tapp ++ "}"
showChQT (Base k)          = showBase k
    
instance Show a => Show (BaseQT a) where
  show (Var x tx)        = showVar x tx
  show (Lam x tx r tlam) = showLam x tx r tlam
  show (App r s tapp)    = showApp r s tapp
  show (Base k)          = showBase k


showVar x tx = "\\chvar{" ++ x ++ "}{" ++ show tx ++ "}"

showLam x tx r tlam = "\\chlamLN{" ++ x      ++ "}{" ++ show tx ++ "}{" 
                                   ++ show r ++ "}{" ++ show tlam ++ "}"

showApp r s tapp = "\\chapp{"  ++ show r  ++ "}{" 
                               ++ show s  ++ "}{" ++ show tapp ++ "}"

showBase KZero = "\\ketZero{}"
showBase KOne  = "\\ketOne{}"


