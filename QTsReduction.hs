-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for <SOMETHING_HERE>
--               by Alejandro Díaz-Caro, Pablo E. "Fidel" Martínez López and Ignacio D. Grima
-- Version: 1.0
-- Developer: Ignacio D. Grima <nacho -at- fceia.unr.edu.ar > & Fidel <fidel -at- unq.edu.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2017  Ignacio D. Grima & Fidel
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
module QTsReduction where

import QTerms
import QTypes
import QTMonad
import QTrace

reduce :: ChurchQTerm -> ChurchQTerm
reduce t = let (t', _, _) = runQTM (do setTerm t
                                       reduceCBV t)
            in t'

traceReduce :: ChurchQTerm -> String
traceReduce t = let (_, mem, _) = runQTM (do setTerm t
                                             reduceCBV t)
                 in showTrace $ getReductionTrace mem

reduceCBV :: ChurchQTerm -> QTMonad ChurchQTerm
-- PRECOND: the term is normalizable
reduceCBV t | isNormalForm t = return t
reduceCBV t                  = do t' <- reduceOneStepCBV t
                                  logTerm t'
                                  reduceCBV t'

reduceOne :: ChurchQTerm -> ChurchQTerm
reduceOne t = let (t', _, _) = runQTM (reduceOneStepCBV t)
               in t'

reduceOneStepCBV :: ChurchQTerm -> QTMonad ChurchQTerm
-- PRECOND: the term is ground and well typed 
reduceOneStepCBV (App t u tapp) | isLam t && isValue u = applyBeta t u
reduceOneStepCBV (App t u tapp) | isLam t              = do u' <- reduceOneStepCBV u
                                                            return (App t u' tapp)
reduceOneStepCBV (App t u tapp)                        = do t' <- reduceOneStepCBV t
                                                            return (App t' u tapp)
reduceOneStepCBV v                                     = return v

reduceOneStepCBN :: ChurchQTerm -> QTMonad ChurchQTerm
-- PRECOND: the term is ground and well typed 
reduceOneStepCBN (App t u tapp) | isLam t = applyBeta t u
reduceOneStepCBN (App t u tapp)           = do t' <- reduceOneStepCBN t
                                               return (App t' u tapp)
reduceOneStepCBN v                        = return v


-----------------------------------------------------------------------------
-- Reduction rules
-----------------------------------------------------------------------------
-- PRECOND: the term has the form ((\x:tC.t)u)
-- (beta) (\x:tC.t)u --> t[x:=u]
applyBeta (Lam x _ t _) u = do logReduction "beta"
                               subst t x u

subst :: ChurchQTerm -> Vble -> ChurchQTerm -> QTMonad ChurchQTerm
-- PRECOND: s and the variable z in the term has the same type
subst v@(Var x _)         z u           = return (if (z == x) then u else v)
subst t@(Lam x _ _ _)     z u | z == x  = return t
subst t@(Lam x tx r tlam) z u           = do newr <- subst r z u
                                             return (Lam x tx newr tlam)
subst (App r s tapp)      z u           = do newr <- subst r z u
                                             news <- subst s z u
                                             return (App newr news tapp)
subst t                   _ _           = return t

isNormalForm :: ChurchQTerm -> Bool
-- PRECOND: the term is ground and well typed
inNormalForm (Lam _ _ _ _) = True
isNormalForm (Base _)      = True
isNormalForm _             = False

