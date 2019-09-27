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

import QComplex as QC
import Multiset as MS
import QTerms
import QTypes as QT
import QTMonad
import Error
import QTrace
import QTsTypeInference

reduce :: ChurchQTerm -> ChurchQTerm
reduce t = let (t', _, _) = runQTM (do setTerm t
                                       reduce' t)
            in t'

traceReduce :: ChurchQTerm -> String
traceReduce t = let (_, mem, _) = runQTM (do setTerm t
                                             reduce' t)
                 in showTrace $ getReductionTrace mem

reduce' :: ChurchQTerm -> QTMonad ChurchQTerm
-- PRECOND: the term is normalizable
reduce' t | isNormalForm t = return t
reduce' t                  = do t' <- reduceOneStep t
                                logTerm t'
                                reduce' t'

reduceOne :: ChurchQTerm -> ChurchQTerm
reduceOne t = let (t', _, _) = runQTM (reduceOneStep t)
               in decorate t'

reduceOneStep :: ChurchQTerm -> QTMonad ChurchQTerm
-- PRECOND: the term is ground and well typed 
-- OBS: Rules assoc & comm are given for free by the representation of LC.
reduceOneStep (App t@(Lam _ _ _ _) u tapp) 
  | isBaseQBitN (getType u) =
    if (isBase u)
     then applyBeta t u                                                    --(Beta_b; call by base)
     else reduceAppByContextualRule t u tapp                               --(Contextual rule: Lam)
reduceOneStep (App t@(Lam _ _ _ _) u tapp) 
  | isLinear (getType u)                               = applyBeta t u     --(Beta_n; call by name)
reduceOneStep (App (QIf t f _)     (QBit KOne)   tapp) = return t          --(if_1)
reduceOneStep (App (QIf t f _)     (QBit KZero)  tapp) = return f          --(if_0)
reduceOneStep (App t@(QIf _ _ _)   u             tapp) = reduceAppByContextualRule t u tapp 
                                                                           --(Contextual rule: QIf)
reduceOneStep (App t               (LC maus tlc) tapp)
  | QT.isFunFromQBitN (getType t) = 
    do maus' <- foreachM (\(u,a)-> do ttu <- appType (getType t) (getType u)
                                      return (App t u ttu, a)) maus
       return (LC maus' tapp)                                              --(LinR_+ & LinR_alpha)
reduceOneStep (App t               (Null tnull)  tapp)
  | QT.isFunFromQBitN (getType t) && isBaseQBitN tnull =
    do tnull' <- appType (getType t) tnull -- TODO:NACHO: is this really tnull or S(tnull)???
       return (Null (tSup (QT.unSup tnull')))                              --(LinR_0)
reduceOneStep (App (LC mats tlc)   u             tapp) =
  do mats' <- foreachM (\(t,a)-> do ttu <- appType (getType t) (getType u)
                                    return (App t u ttu, a)) mats
     return (LC mats' tapp)                                                --(LinL_+ & LinL_alpha)
reduceOneStep (App (Null tnull)    u             tapp)
  | QT.isFunFromQBitN tnull =
    do tnull' <- appType tnull (getType u)
       return (Null (tSup (QT.unSup tnull')))                              --(LinL_0)
reduceOneStep (App t u tapp)                           = reduceAppByContextualRule t u tapp
reduceOneStep (LC mats tlc) = reduceLCRules mats tlc                       --(LC Rules)
reduceOneStep (Head (Prod [] _) _)  = raise ("Empty Prod: This cannot happen, something went oddly wrong") 
                                        -- This cannot fail, but added for consistency
reduceOneStep (Head (Prod [_] _) _) = raise ("Singleton Prod: This cannot happen, something went oddly wrong")
                                        -- This cannot fail, but added for consistency
reduceOneStep (Head (Prod (t:ts) tprod) thead)
  | isBase t = return t                                                 --(head)
reduceOneStep (Head t thead) = do t' <- reduceOneStep t
                                  return (Head t' thead)                   --(Contextual rule: head)
reduceOneStep (Tail (Prod [] _) _)  = raise ("Empty Prod: This cannot happen, something went oddly wrong") 
                                        -- This cannot fail, but added for consistency
reduceOneStep (Tail (Prod [_] _) _) = raise ("Singleton Prod: This cannot happen, something went oddly wrong")
                                        -- This cannot fail, but added for consistency
reduceOneStep (Tail (Prod (t:ts) tprod) thead)
  | isBase t = case ts of
                 [u] -> return u                                           --(tail)
                 _   -> return (Prod ts (QT.tailTProd tprod))              --(tail)
reduceOneStep (Tail t ttail) = do t' <- reduceOneStep t
                                  return (Tail t' ttail)                   --(Contextual rule: tail)

reduceOneStep (Up (Prod ts tprod) tup) = reduceUpByProdRules ts tprod tup
reduceOneStep (Up (LC mats tlc)   tup) = 
  return (LC (foreach (\(u,a) -> (Up u undefined, a)) mats) undefined)     --(distPlus_up & distAlpha_up)
reduceOneStep (Up  t              tup) = do t' <- reduceOneStep t
                                            return (Up t' tup)             --(Contextual rule: up)


-- 
reduceOneStep v                                        = return v
-- 

reduceAppByContextualRule :: ChurchQTerm -> ChurchQTerm -> QType -> QTMonad ChurchQTerm
reduceAppByContextualRule t u tapp = do u' <- reduceOneStep u
                                        return (App t u' tapp)

--reduceLCRules :: ChurchQTerm -> QTMonad ChurchQTerm --(Prod & Alpha_dist given by representation)
reduceLCRules mats tlc = 
  let mats'     = MS.filterMS (\(t,a) -> isNull t || a == 0) mats --(Zero & Zero_alpha)
      rmats     = MS.fromMultiList (reduceLCByFactRule (MS.order mats'))
      (t,alpha) = MS.fromSingleton rmats  -- due to Lazy Eval, this is not evaluated until you ask for alpha or t
   in if (MS.isSingleton rmats && alpha == 1)
       then return t                                              --(Unit & Neutral)
       else if (MS.isEmpty rmats)
             then return (Null (QT.unSup tlc))                    --(Neutral & Zero & Zero_S & Zero_alpha)
             else if (rmats /= mats)
                   then return (LC rmats tlc)                     --(Neutral & Zero)
                   else do rmats' <- foreachM (\(t,a) -> 
                                                 do t' <- if (isBase t) 
                                                           then return t
                                                           else reduceOneStep t
                                                    return (t',a))
                                              rmats
                           return (LC rmats' tlc)                 --(Contextual Rule: LC)
-- NACHO: Report notes: The sole definition of .> is implementing Prod and Alpha_dist rules)
--                      Same happens with <+> and Fact2)

-- this rule is used by (sq2 |0> + |0>) (not in the invariant of Multiset)
reduceLCByFactRule :: [((ChurchQTerm,QComplex), Int)] -> [((ChurchQTerm,QComplex), Int)]
reduceLCByFactRule []    = []
reduceLCByFactRule [tan] = [tan]
reduceLCByFactRule (tan@((t,qc),i):tan'@((t',qc'),i'):tans) =
  if (t == t')
   then reduceLCByFactRule (((t,fromInt i * qc + fromInt i' * qc'),1):tans)
   else tan : reduceLCByFactRule (tan':tans)

reduceUpByProdRules :: [ChurchQTerm] -> QType -> QType -> QTMonad ChurchQTerm
reduceUpByProdRules ts tprod _
  | all isBase ts           = return (Prod ts tprod)   --(NeutUp)
reduceUpByProdRules ts tprod _ 
  | any (\x -> isNull x) ts = return (Null tprod)      --(DistNull)
reduceUpByProdRules ts tprod tup = reduceUpByDistRules [] ts tprod

reduceUpByDistRules :: [ChurchQTerm] -> [ChurchQTerm] -> QType -> QTMonad ChurchQTerm
reduceUpByDistRules bs []     tprod = return (Prod (reverse bs) tprod)
reduceUpByDistRules bs (t:ts) tprod =
  if (isBase t)
   then reduceUpByDistRules (t:bs) ts tprod
   else case t of
          LC mats tlc -> return (LC 
                                 (foreach
                                  (\(u,a)-> (Up (Prod (reverse bs ++ [u] ++ ts) undefined) undefined, a))
                                  mats) 
                                 undefined)            --(distPlus & distAlpha)
          _           -> raise "Cannot have something different than an LC on reduceUpByDistRules"
                               -- This cannot fail, but added for completeness on case clause



-----------------------------------------------------------------------------
-- Reduction rules
-----------------------------------------------------------------------------
-- PRECOND: the term has the form ((\x:tC.t)u) and the types are compatible.
-- (beta) (\x:tC.t)u --> t[x:=u]
applyBeta (Lam x _ t _) u = do logReduction "beta"
                               subst t x u

subst :: ChurchQTerm -> Vble -> ChurchQTerm -> QTMonad ChurchQTerm
-- PRECOND: s and the variable z in the term has the same type
subst v@(Var x _)         z u           = return (if (z == x) then u else v)
subst t@(Lam x tx r tlam) z u | z /= x  = do r' <- subst r z u
                                             return (Lam x tx r' tlam)
subst (App r s tapp)      z u           = do r' <- subst r z u
                                             s' <- subst s z u
                                             return (App r' s' tapp)
-- subst (LC mt tlc)         z u           = do mt' <- MS.foreachM (\(a,t) -> do t' <- subst t z u; return (a,t')) mt
subst (LC mt tlc)         z u           = do mt' <- MS.foreachM (\(t,a) -> (\x -> (x,a)) <$> subst t z u) mt
                                             return (LC mt' tlc)
subst (Prod ts tprod)     z u           = do ts' <-  mapM (\t -> subst t z u) ts
                                             return (Prod ts' tprod)
subst (Head t thead)      z u           = do t' <- subst t z u
                                             return (Head t' thead)
subst (Tail t ttail)      z u           = do t' <- subst t z u
                                             return (Tail t' ttail)
subst (Proj n t tproj)    z u           = do t' <- subst t z u
                                             return (Proj n t' tproj)
subst (QIf t f tif)       z u           = do t' <- subst t z u
                                             f' <- subst f z u
                                             return (QIf t' f' tif)
subst (Up t tup)          z u           = do t' <- subst t z u
                                             return (Up t' tup)
subst t                   _ _           = return t

isNormalForm :: ChurchQTerm -> Bool
-- PRECOND: the term is ground and well typed
isNormalForm (QBit _)                = True
isNormalForm (Null _)                = True
isNormalForm (Var _ _)               = True
isNormalForm (Lam _ _ _ _)           = True
isNormalForm (App (Lam _ _ _ _) _ _) = False
isNormalForm (App (QIf _ _ _) _ _)   = False
isNormalForm (App f _ _)             = isNormalForm f 
isNormalForm (LC mt _)               = let tsi = MS.order mt
                                           (_,alpha) = MS.fromSingleton mt
                                        in not (MS.isSingleton mt && alpha == 1)
                                           && all (\t-> isNormalForm t && not (isNull t))
                                               (map (fst . fst) tsi)
isNormalForm (Prod ts _)             = all isNormalForm ts
isNormalForm (QIf _ _ _)             = True
isNormalForm _                       = False

