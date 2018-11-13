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
import QComplex
import Multiset as MS
import Data.List as L
--import Error
--import NewVarMonad

type Vble = String
data QBit = KZero | KOne
          deriving (Eq, Ord, Show)
type LinBQT a = MS.Multiset (QComplex, BaseQT a)
data BaseQT a = 
                -- Constants
                QBit QBit
              | Null a      -- O_S(a)
                -- Base Lambda Calculus
              | Var Vble a
              | Lam Vble QT.QType (BaseQT a) a
              | App (BaseQT a) (BaseQT a) a
                -- Linear combinations
              | LC (LinBQT a) a
                -- Superpositions
              | Prod [ BaseQT a ] a
              | Head (BaseQT a) a
              | Tail (BaseQT a) a
                -- Projections
              | Proj Int (BaseQT a) a
                -- Alternatives
              | QIf (BaseQT a) (BaseQT a) a
                -- Castings (True==Right, False==Left)
              | Up Bool (BaseQT a) a
        deriving (Eq, Ord, Show)
   {-
      Type parameter a is a technique for processing church style typing.
      The type (BaseQT ()) is the type of not-yet-typed terms, and the
      type (BaseQT QT.QType) is the type of typed terms.
      Church terms are annotated with their types (subterms and variables
      are also annotated).
      A valid Church term is only annotated with a type valid according
      the system typing rules.
   -}

type QTerm       = BaseQT ()
type ChurchQTerm = BaseQT QT.QType

asLinCom :: BaseQT a -> LinBQT a
asLinCom (LC mt _) = mt
asLinCom t         = singleton (1, t)

-- Get the type annotated in a Church term.
getType :: ChurchQTerm -> QT.QType
getType (QBit _)      = QT.tB
getType (Null t)      = QT.tSup t
getType (Var _ t)     = t
getType (Lam _ _ _ t) = t
getType (App _ _ t)   = t
getType (LC _ t)      = t
getType (Prod _ t)    = t
getType (Head _ t)    = t
getType (Tail _ t)    = t
getType (Proj _ _ t)  = t
getType (QIf _ _ t)   = t
getType (Up _ _ t)    = t

-- PRECOND: the term is ground and well typed 
isBase :: BaseQT a -> Bool
isBase (QBit _)      = True
isBase (Var _ _)     = True
isBase (Lam _ _ _ _) = True
isBase (Prod ts _)   = all isBase ts
isBase _             = False

isLam :: BaseQT a -> Bool
isLam (Lam _ _ _ _) = True
isLam _             = False

isGround :: Ord a => BaseQT a -> Bool
isGround t = freeVars t == []

freeVars :: Ord a => BaseQT a -> [Vble]
freeVars (Var x _)     = [x]
freeVars (Lam x _ t _) = freeVars t \\ [x]
freeVars (App t u _)   = freeVars t `L.union` freeVars u
freeVars (LC mt _)     = foldMS (\((_,t),_) fvs -> freeVars t `L.union` fvs) [] mt
freeVars (Prod ts _)   = foldr L.union [] (map freeVars ts)
freeVars (Head t _)    = freeVars t
freeVars (Tail t _)    = freeVars t
freeVars (Proj _ t _)  = freeVars t
freeVars (QIf t u _)   = freeVars t `L.union` freeVars u
freeVars (Up _ t _)    = freeVars t
freeVars _             = []

---------------------------------------------------------
-- Functions for easy construction
---------------------------------------------------------
-- Untyped version
k0, k1 :: QTerm
k0        = QBit KZero
k1        = QBit KOne

nullV t   = Null (tSup t)

var x     = Var x ()
lam x t e = Lam x t e ()
app r s   = App r s ()

a .> t    = LC (singleton (a,t)) ()
t <+> u   = LC (MS.union (asLinCom t) (asLinCom u)) ()

t <*> u   = Prod (asList t ++ asList u) ()
  where asList (Prod ts _) = ts 
        asList t           = [t]

qHead t   = Head t ()
qTail t   = Tail t ()
proj j t  = Proj j t ()
qIf t u   = QIf t u ()
upR t     = Up True t ()
upL t     = Up False t ()
        
---------------------------------------------------------
-- Show
--  Showing uses LaTeX macros from z-preamble
--  There are 2 versions of show:
--     * one used to pretty display with ovalboxes, etc.
--     * another used to generate Haskell code to build types
---------------------------------------------------------
showQT :: BaseQT a -> String
showQT (QBit k)       = showBase k
showQT (Null _)       = "\\Null"
showQT (Var x _)      = "\\var{" ++ x ++ "}{}"
showQT (Lam x tx r _) = "\\lam{" ++ x ++ "}{" ++ show tx ++ "}{" ++ showQT r ++ "}"
showQT (App r s _)    = "\\app{" ++ showQT r ++ "}{" ++ showQT s ++ "}"
showQT (LC mxs _)     = "\\LinQT{" ++ showLCSum (order mxs) ++ "}{}"
showQT (Prod xs _)    = "\\Prod{" ++ showProd xs ++ "}{}"
showQT (Head x _)     = "\\Head{" ++ showQT x ++ "}{}"
showQT (Tail x _)     = "\\Tail{" ++ showQT x ++ "}{}"
showQT (Proj i x _)   = "\\Proj{" ++ i ++ "}{" ++ showQT x ++ "}{}"
showQT (QIf x y _)    = "\\Ite{" ++ showQT x ++ "}{" ++ showQT y ++ "}{}"
showQT (Up True x _)  = "\\Cast{r}{" ++ showQT x ++ "}{}"
showQT (Up False x _) = "\\Cast{ell}{" ++ showQT x ++ "}{}"

showChQT :: ChurchQTerm -> String
showChQT (QBit k)          = showBase k
showChQT (Var x tx)        = "\\chvar{" ++ x ++ "}{" ++ show tx ++ "}"
showChQT (Lam x tx r tlam) = "\\chlam{" ++ x ++ "}{" ++ show tx ++ "}{" 
                                        ++ showChQT r    ++ "}{" ++ show tlam ++ "}"
showChQT (App r s tapp)    = "\\chapp{" ++ showChQT r  ++ "}{" ++ showChQT s  ++ "}{" ++ show tapp ++ "}"
showChQT (Null tn)         = "\\Null_{"  ++ show tn ++ "}"
showChQT (LC mxs tlc)      = "\\LinQT{" ++ showChLCSum (order mxs) ++ "}{" ++ show tlc ++ "}"
showChQT (Prod xs tprod)   = "\\Prod{"  ++ showChProd xs ++ "}{" ++ show tlc ++ "}"
showChQT (Head x thead)    = "\\Head{" ++ showChQT x ++ "}{" ++ show thead ++ "}"
showChQT (Tail x ttail)    = "\\Tail{" ++ showChQT x ++ "}{" ++ show ttail ++ "}"
showChQT (Proj j x tproj)  = "\\Proj{" ++ j ++ "}{" ++ showChQT x ++ "}{" ++ show tproj ++ "}"
showChQT (QIf x y tqif)    = "\\Ite{" ++ showChQT x ++ "}{" ++ showChQT y ++ "}{" ++ show tqif ++ "}"
showChQT (Up True x tup)   = "\\Cast{r}{" ++ showChQT x ++ "}{" ++ show tup ++ "}"
showChQT (Up False x tup)  = "\\Cast{ell}{" ++ showChQT x ++ "}{" ++ show tup ++ "}"

-- aux
showList       showElem separator []     = ""
showList       showElem separator [x]    = showElem x
showList       showElem separator (x:xs) = showElem x ++ separator ++ (showList showElem separator xs)

showLCSum                                = showList showLinBQTItem " + "
showChLCSum                              = showList showChLinBQTItem " + "

showProd                                 = showList showQT " \\times "
showChProd                               = showList showChQT " \\times "

showLinBQTItem ((qc,x), 1)   = showQCxQT (qc, tx)
showLinBQTItem ((qc,x), n)   = showQCxQT (qc, tx) ++ " + " ++ showLinBQTItem ((qc,x), n-1)
showChLinBQTItem ((qc,x), 1) = showChQCxQT (qc, tx)
showChLinBQTItem ((qc,x), n) = showChQCxQT (qc, tx) ++ " + " ++ showChLinBQTItem ((qc,x), n-1)

showQCxQT      (1, x)      = showQT x
showQCxQT      (qcomp, x)  = "\\paren{" ++ showNested qcomp ++ " " ++ showQT x ++ "}"
showChQCxQT    (1, x)      = showChQT x
showChQCxQT    (qcomp, x)  = "\\paren{" ++ showNested qcomp ++ " " ++ showChQT x ++ "}"
--
    
--instance Show a => Show (BaseQT a) where
--  show (Var x tx)        = showVar x tx
--  show (Lam x tx r tlam) = showLam x tx r tlam
--  show (App r s tapp)    = showApp r s tapp
--  show (QBit k)          = showBase k


showVar x tx = "\\chvar{" ++ x ++ "}{" ++ show tx ++ "}"

showLam x tx r tlam = "\\chlamLN{" ++ x      ++ "}{" ++ show tx ++ "}{" 
                                   ++ show r ++ "}{" ++ show tlam ++ "}"

showApp r s tapp = "\\chapp{"  ++ show r  ++ "}{" 
                               ++ show s  ++ "}{" ++ show tapp ++ "}"

showBase KZero = "\\ketZero{}"
showBase KOne  = "\\ketOne{}"


