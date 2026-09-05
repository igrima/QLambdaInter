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
import Data.List (sortBy, groupBy)
--import Data.Tuple.Extra

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
-- There was no contextual rule at all for a bare Prod: any term built with <**> whose
-- elements aren't already reduced (e.g. (App hadamard k0) <**> (App hadamard k1), from
-- Main.hs's own hadamardBoth) could never make progress -- reduceOneStep would just
-- return it unchanged forever, since the final catch-all clause is the only thing that
-- would otherwise match it, causing reduce' to loop until stack overflow. This also
-- silently affected Head/Tail: their own fallback clauses (below) delegate to
-- `reduceOneStep` on the whole Prod when its head element isn't base yet, which hit
-- the exact same missing case.
reduceOneStep (Prod ts tprod) = do ts' <- reduceOneProdElement ts
                                   return (Prod ts' tprod)                 --(Contextual rule: Prod)
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
  return (LC (foreach (\(u,a) -> (Up u tup, a)) mats) tup)     --(distPlus_up & distAlpha_up)
  -- Distributing Up over a sum doesn't change the type of the whole expression (only
  -- its shape), and every summand u shares the same pre-cast type (LC's own typing
  -- invariant), so both the rebuilt LC and each Up u below it keep the SAME `tup`
  -- that the original (undistributed) Up already had -- nothing to recompute.
reduceOneStep (Up  t              tup) = do t' <- reduceOneStep t
                                            return (Up t' tup)             --(Contextual rule: up)

-- PRECOND: Proj occurs, if at all, only as the outermost constructor of the whole
-- program. This is not a restriction of the calculus, but of how we choose to run it:
-- by the "principle of deferred measurement" (Nielsen & Chuang), any computation using
-- intermediate measurements has an equivalent one where every measurement happens last,
-- so it costs us nothing to only support that shape. See the long comment on
-- Scale/Distr in QTerms.hs for why this is what lets us get away with an inexact/
-- irreducible sqrt in the result: nothing downstream will ever try to compute with it.
reduceOneStep (Proj i t tproj) = reduceByProjRules i t tproj

reduceOneStep (Scale n t ts) = do t' <- reduceOneStep t
                                  return (Scale n t' ts)                  --(Contextual rule: Scale)
reduceOneStep (Distr bs ts)  = do bs' <- reduceOneDistrBranch bs
                                  return (Distr bs' ts)                   --(Contextual rule: ||, Fig. TRScontext)

--
reduceOneStep v                                        = return v
  -- OJO(FF): esta regla NO puede estar, porque se supone que reduceOneStep avanza un paso, sí o sí
-- 

-----------------------------------------------------------------------------
-- Reduction rules
-----------------------------------------------------------------------------
-- PRECOND: the term has the form ((\x:tC.t)u) and the types are compatible.
-- (beta) (\x:tC.t)u --> t[x:=u]
applyBeta (Lam x _ t _) u = do logReduction "beta"
                               subst t x u


reduceAppByContextualRule :: ChurchQTerm -> ChurchQTerm -> QType -> QTMonad ChurchQTerm
reduceAppByContextualRule t u tapp = do u' <- reduceOneStep u
                                        return (App t u' tapp)

--reduceLCRules :: ChurchQTerm -> QTMonad ChurchQTerm --(Prod & Alpha_dist given by representation)
reduceLCRules mats tlc = 
  -- NOTE: this predicate was inverted (`isNull t || a == 0`), which KEEPS only the
  -- null/zero-coefficient summands and drops everything else -- so any LC that wasn't
  -- already fully built in normal form (e.g. one assembled by a reduction rule, like
  -- Up's distPlus_up) would collapse straight to Null the moment it needed a further
  -- reduction step. (Zero & Zero_alpha) is supposed to drop the null/zero summands,
  -- not keep only them.
  let mats'     = MS.filterMS (\(t,a) -> not (isNull t) && a /= 0) mats --(Zero & Zero_alpha)
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
reduceLCByFactRule []                                   = []
reduceLCByFactRule [((t,qc),i)]                         = [((t,fromInt i * qc),1)]
reduceLCByFactRule (((t,qc),i):tan'@((t',qc'),i'):tans) =
  if (t == t')
   then reduceLCByFactRule (((t,fromInt i * qc + fromInt i' * qc'),1):tans)
   else ((t, fromInt i * qc), 1) : reduceLCByFactRule (tan':tans)
        -- This ensures that multiplicities are always 1

reduceUpByProdRules :: [ChurchQTerm] -> QType -> QType -> QTMonad ChurchQTerm
reduceUpByProdRules ts tprod _
  | all isBase ts           = return (Prod ts tprod)   --(NeutUp)
reduceUpByProdRules ts _    tup
  | any (\x -> isNull x) ts = return (Null (QT.unSup tup))      --(DistNull)
  -- NOTE: was `Null tprod` (the PRE-cast type); the paper's rdistzr/rdistzl send a
  -- Null to the type of the whole cast expression, i.e. tup here, not tprod. Null's
  -- own convention (getType (Null t) = S t) means we pass unSup tup, not tup itself.
reduceUpByProdRules ts tprod tup = reduceUpByDistRules [] ts tprod tup

-- Scans the tuple left to right (bs = already-scanned, already-base elements, in
-- reverse), looking for the first component that still needs work under the cast:
--  * an LC: distribute Up over it (distPlus_up & distAlpha_up, generalized to n-ary
--    products -- see the NOTE above reduceOneStep's `Up (LC ...)` case);
--  * anything else not yet base: this used to be an error ("Cannot have something
--    different than an LC"), which crashed on e.g. `up (hadamardBoth applied to
--    |0>x|1>)`, because an unreduced App inside the tuple isn't base and isn't an LC
--    either -- it just hasn't been reduced yet. We now reduce it one step and loop
--    (Contextual rule: up, applied inside the Prod), same as every other contextual
--    rule in this file.
reduceUpByDistRules :: [ChurchQTerm] -> [ChurchQTerm] -> QType -> QType -> QTMonad ChurchQTerm
reduceUpByDistRules bs []     tprod _   = return (Prod (reverse bs) tprod)
reduceUpByDistRules bs (t:ts) tprod tup =
  if (isBase t)
   then reduceUpByDistRules (t:bs) ts tprod tup
   else case t of
          LC mats tlc ->
            -- Replacing t (type S(X), the LC's own type) with one summand u (type X)
            -- changes the shape of the surrounding tuple's type, so -- unlike the
            -- `Up (LC ...) tup` case above, where the WHOLE tuple was the LC -- we
            -- can't just reuse tprod here: it has to be recomputed per branch.
            do let before = map getType (reverse bs)
                   after  = map getType ts
               mats' <- foreachM (\(u,a) ->
                            do tprod' <- prodType (before ++ [getType u] ++ after)
                               return (Up (Prod (reverse bs ++ [u] ++ ts) tprod') tup, a))
                          mats
               return (LC mats' tup)                                 --(distPlus & distAlpha)
          _ -> do t' <- reduceOneStep t
                  return (Up (Prod (reverse bs ++ [t'] ++ ts) tprod) tup)
                                                       --(Contextual rule: up, inside Prod)

-- Implements rule (proj) from Figure~TRSproj: measures the first j qubits of a
-- superposition of n-qubit basis terms, grouping the m basis terms into buckets
-- T_k (one per possible j-qubit outcome |k>), and building
--   ||_k {p_k} (|k> x phi_k)
-- where p_k is the total probability of bucket T_k, and phi_k is the (renormalized)
-- leftover superposition of the remaining n-j qubits within that bucket.
-- See the comment on the Scale/Distr constructors in QTerms.hs for why phi_k's
-- renormalizing factor is kept as an unevaluated sqrt (a Scale), and why building
-- a genuine Distr node here (rather than picking one branch, say) is safe despite
-- ChurchQTerm otherwise standing for a single term, not a distribution.
reduceByProjRules :: Int -> ChurchQTerm -> QType -> QTMonad ChurchQTerm
reduceByProjRules j (Null _)    tproj = raise "Cannot project Null vector"
reduceByProjRules j (LC ms tlc) tproj | all (\((ti, _),hi)-> isBaseQBitNTerm ti && hi == 1) (order ms)
                                      = case order ms of
                                          [] -> raise "This cannot happen, you can't have an LC with an empty set"
                                          tsi ->
                                            do let triples    = map (splitProdAt j) tsi -- [([t],[t],alpha)], one per basis term
                                                   nMinusJ     = length (snd3 (head triples))
                                                   totalNormSq = sum [ norm a | (_,_,a) <- triples ] -- sum_r |alpha_r|^2
                                                   buckets     = groupBy eqFst (sortBy compFst triples) -- one group per T_k
                                               branches <- mapM (buildProjBranch nMinusJ totalNormSq) buckets
                                               case branches of
                                                 [(_, onlyTerm)] -> return onlyTerm -- a single outcome is certain (Lambda \subseteq D)
                                                 _               -> return (Distr branches tproj)
reduceByProjRules j t           tproj | isBaseQBitNTerm t
                                      = return t -- t is already a single deterministic basis value: certain outcome
reduceByProjRules j t           tproj = do t' <- reduceOneStep t
                                           return (Proj j t' tproj)  --(Contextual Rule: Proj)

-- Builds one outcome {p_k} (|k> x phi_k) for one T_k bucket (a group of basis terms
-- sharing the same first-j-qubit prefix). nMinusJ==0 means we projected every qubit,
-- so there's no phi_k at all: the branch is just the (fully classical) prefix itself.
buildProjBranch :: Int -> QComplex -> [([ChurchQTerm],[ChurchQTerm],QComplex)] -> QTMonad (QComplex, ChurchQTerm)
buildProjBranch 0 totalNormSq bucket@((prefix,_,_):_) =
  do let bucketNormSq = sum [ norm a | (_,_,a) <- bucket ]
     return (bucketNormSq / totalNormSq, buildQBitTuple prefix)
buildProjBranch nMinusJ totalNormSq bucket@((prefix,_,_):_) =
  do let bucketNormSq = sum [ norm a | (_,_,a) <- bucket ]           -- sum_{i in T_k} |alpha_i|^2
         pk           = bucketNormSq / totalNormSq                    -- exact: a ratio of two sums of |.|^2, no sqrt needed
         phiType      = QT.tSup (QT.tBn nMinusJ)
         phi          = LC (MS.fromMultiList [ ((buildQBitTuple suffix, a), 1) | (_,suffix,a) <- bucket ]) phiType
         branchType   = QT.tProd (replicate (length prefix) QT.tB ++ [phiType])
     return (pk, Prod (prefix ++ [Scale bucketNormSq phi phiType]) branchType)

buildQBitTuple :: [ChurchQTerm] -> ChurchQTerm
buildQBitTuple [t] = t
buildQBitTuple ts  = Prod ts (QT.tBn (length ts))

-- PRECOND: h MUST BE 1
splitProdAt j ((Prod ts _, a), h) = let (ts1,ts2) = splitAt j ts
                                     in (ts1,ts2,a)  -- h must be equal to 1 because of condition in reduceByProjRules
splitProdAt j ((t,        a), h) = ([t],[],a)  -- a single qubit (n==1, so necessarily j==1 too): not wrapped in Prod

compFst (ts1,_,_) (ts1',_,_) = compare ts1 ts1'
eqFst   (ts1,_,_) (ts1',_,_) = ts1 == ts1'
snd3    (_,ts2,_)             = ts2

reduceOneDistrBranch :: [(QComplex,ChurchQTerm)] -> QTMonad [(QComplex,ChurchQTerm)]
-- PRECOND: at least one branch is not yet in normal form (reduceOneStep must always
-- make progress -- see the OJO(FF) note above on reduceOneStep's final clause)
reduceOneDistrBranch ((p,t):rest) | isNormalForm t = do rest' <- reduceOneDistrBranch rest
                                                        return ((p,t):rest')
reduceOneDistrBranch ((p,t):rest)                  = do t' <- reduceOneStep t
                                                        return ((p,t'):rest)
reduceOneDistrBranch []                            = raise ("Empty Distr, or reduceOneStep called " ++
                                                              "on an already normal Distr: this cannot happen")

reduceOneProdElement :: [ChurchQTerm] -> QTMonad [ChurchQTerm]
-- PRECOND: at least one element is not yet in normal form (same as reduceOneDistrBranch)
reduceOneProdElement (t:rest) | isNormalForm t = (t:) <$> reduceOneProdElement rest
reduceOneProdElement (t:rest)                  = do t' <- reduceOneStep t
                                                    return (t':rest)
reduceOneProdElement []                        = raise ("Empty Prod, or reduceOneStep called " ++
                                                          "on an already normal Prod: this cannot happen")
-----------------------------------------------------------------------------
-- Auxiliaries
-----------------------------------------------------------------------------
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
subst (Scale n t ts)      z u           = do t' <- subst t z u
                                             return (Scale n t' ts)
subst (Distr bs ts)       z u           = do bs' <- mapM (\(p,t) -> (\t' -> (p,t')) <$> subst t z u) bs
                                             return (Distr bs' ts)
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
                                           && all (\i-> i == 1) (map snd tsi)
isNormalForm (Prod ts _)             = all isNormalForm ts
isNormalForm (QIf _ _ _)             = True
isNormalForm (Scale _ t _)           = isNormalForm t
isNormalForm (Distr bs _)            = all (isNormalForm . snd) bs
isNormalForm _                       = False

