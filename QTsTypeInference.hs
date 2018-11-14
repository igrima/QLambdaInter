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

module QTsTypeInference where

import Multiset as MS
import QTypes as QT
import QTerms
import QTMonad
import Error
import List
import QEnvironments


---------------------------------------------------------
-- inferType
---------------------------------------------------------
infer r = getResValue (runQTM (inferType emptyEnv r))

inferType env r = do (_,tr) <- deduceType env r
                     return tr

decorate r = getResValue (runQTM (decorateTerm emptyEnv r))

decorateTerm env r = do (chr,_) <- deduceType env r
                        return chr

deduceType :: Environment -> QTerm -> QTMonad (ChurchQTerm, QType)
deduceType env (Null t0)  =        -- rule Ax0
   do checkAllDuplicable env
      t0' <- applyS_iRule t0
      return (Null t0', t0')
deduceType env (QBit b) =         -- rules Ax|0> and Ax|1>
   do checkAllDuplicable env 
      tq <- applyS_iRule QT.tB
      return (QBit b, tq)
deduceType env (Var x _) =        -- rule Ax
   do tx   <- findTypeInEnv x env
      envB <- restrictEnv env x
      checkAllDuplicable envB
      tx'  <- applyS_iRule tx
      return (Var x tx', tx') 
deduceType env (Lam x tx t _) =
   do newEnv    <- updateEnv (x,tx) env
      (cht, tt) <- deduceType newEnv t
      tlam      <- lamType tx tt
      tlam'     <- applyS_iRule tlam
      return (Lam x tx cht tlam', tlam')
deduceType env (App r s _) = -- CAMBIAR!!! HAY QUE CHEQUEAR CUAL DE LAS DOS REGLAS USAR!!!!!
   error "To Do" {- do (r, tr) <- deduceType env r
                       (s, ts) <- deduceType env s
                       tapp    <- appType tr ts
                       return (App r s tapp, tapp)
                 -}
deduceType env (LC mt _) =
    do let tsi = MS.order mt
       (chtsi, tsup) <- deduceTypesForLC env tsi
       tsup' <- applyS_iRule tsup
       return (linCom chtsi tsup', tsup')

-- COMPLETAR

deduceTypesForLC env [((q,t),n)]     = 
    do checkNonDuplication n env (freeVars t)
       (cht', tt') <- deduceType env t
       let stt' = addTSupIfNeeded tt'
       return ([((q,cht'),n)], stt')
deduceTypesForLC env (((q,t),n):ts) = 
    do checkNonDuplication n env (freeVars t)     -- If the term appears more than once, all free variables must be duplicable
       envForTs <- trimEnvWrt env t               -- Remove nonDuplicable variables that corresponds to t
       envForT  <- trimEnvWrt env (linCom ts ())  -- Remove nonDuplicable variables that corresponds to ts
       checkOverlapIsDuplicable envForTs envForT  -- After removing all freeVars, no nonDuplicable variables must be left out
       (chts', stt') <- deduceTypesForLC envForTs ts
       (cht', tt')   <- deduceType envForT t 
       stt''         <- produceCompatibleSupTypeFor tt' stt'
       return ((((q,cht'),n):chts'), stt'')

--------------------------------------------------------------------------------------------
-- Functions to control the proper use of TSups, completing when needed, if TPhS allows it
--------------------------------------------------------------------------------------------
produceCompatibleSupTypeFor t1 t2 = fmap addTSupIfNeeded (produceCompatibleTypeFor t1 t2)

addTSupIfNeeded t@(TSup _)   = t
addTSupIfNeeded t@(TSplus _) = t
addTSupIfNeeded t            = tSup t      

produceCompatibleTypeFor t1@(TSup t1') t2 = 
   case t2 of
     TSup   t2' -> fmap tSup (produceCompatibleTypeFor t1' t2')   -- TSup+TSup     = TSup
     TSplus t2' -> fmap tSup (produceCompatibleTypeFor t1' t2')   -- TSup+TSplus   = TSup
     TSstar t2' -> fmap tSup (produceCompatibleTypeFor t1' t2 )   -- TSup+TSstar   = TSup
     _          -> raiseNonCompatibleTypes t1 t2                  -- TSup+NON-S    = fail
produceCompatibleTypeFor t1@(TSplus t1') t2 = 
   case t2 of
     TSup   t2' -> fmap tSup   (produceCompatibleTypeFor t1' t2') -- TSplus+TSup   = TSup
     TSplus t2' -> fmap tSplus (produceCompatibleTypeFor t1' t2') -- TSplus+TSplus = TSplus
     TSstar t2' -> fmap tSplus (produceCompatibleTypeFor t1' t2 ) -- TSplus+TSstar = TSplus
     _          -> raiseNonCompatibleTypes t1 t2                  -- TSplus+NON-S  = fail
produceCompatibleTypeFor t1@(TSstar t1') t2 = 
   case t2 of
     TSup   t2' -> fmap tSup   (produceCompatibleTypeFor t1  t2') -- TSstar+TSup   = TSup
     TSplus t2' -> fmap tSplus (produceCompatibleTypeFor t1' t2') -- TSstar+TSplus = TSplus
     TSstar t2' -> fmap tPhS   (produceCompatibleTypeFor t1' t2') -- TSstar+TSstar = TSstar
     _          -> produceCompatibleTypeForNoSupTypes t1' t2      -- TSstar+NON-S  = NON-S  (TSstar zero times)
produceCompatibleTypeFor t1 t2 =                
   case t2 of
     TSup   _   -> raiseNonCompatibleTypes t1 t2                  -- NON-S+TSup    = fail
     TSplus _   -> raiseNonCompatibleTypes t1 t2                  -- NON-S+TSplus  = fail
     TSstar t2' -> produceCompatibleTypeForNoSupTypes t1 t2'      -- NON-S+TSstar  = NON-S   (TSstar zero times)
     _          -> produceCompatibleTypeForNoSupTypes t1 t2       -- NON-S+NON-S   = NON-S

-- PRECOND: both arguments are not TSup or TPhS                 
produceCompatibleTypeForNoSupTypes (TFun ta1 tr1) (TFun ta2 tr2) =
   do ta' <- produceCompatibleTypeFor ta1 ta2
      tr' <- produceCompatibleSupTypeFor tr1 tr2
      return (TFun ta' tr')
produceCompatibleTypeForNoSupTypes (TProd _) (TProd _) = error "TO DO: ¿Jano?"
produceCompatibleTypeForNoSupTypes TB TB = return TB
produceCompatibleTypeForNoSupTypes t1 t2 = raiseNonCompatibleTypes t1 t2

   
raiseNonCompatibleTypes t1 t2 = raise ("Types are not compatible for Linear Combinations (" ++ show t1 ++ " --- " ++ show t2 ++ ")")


--------------------------------------------------------------------------------------------
checkNonDuplication 1 _   _  = return ()
checkNonDuplication n env xs = do txs <- sequence (map (\x -> findTypeInEnv x env) xs)
                                  if (all isDuplicable txs)
                                   then return ()
                                   else raise "Non linear use of a variable"
     
---------------------------------------------------------
-- AUXILIARIES to build types inferred
---------------------------------------------------------
-- PRECOND: tr and ts are canonical
lamType tx tr = return (QT.TFun tx tr)

-- PRECOND: tr and ts are canonical
appType (QT.TFun a b) c = if a == c
                           then return b
                           else raise ("Arguments and parameters do not fit: " ++ show a ++ " expected, but " ++ show c ++ " provided")
appType _             _ = raise "Non-function in function position"

applyS_iRule t = return (tPhS t)
