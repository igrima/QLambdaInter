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
deduceType env (Null t)  =        -- rule Ax0
   do checkAllDuplicable env
      return (Null t, t)
deduceType env (QBit b) =         -- rules Ax|0> and Ax|1>
   do checkAllDuplicable env 
      return (QBit b, QT.tB)
deduceType env (Var x _) =        -- rule Ax
   do tx   <- findTypeInEnv x env
      envB <- restrictEnv env x
      checkAllDuplicable envB
      return (Var x tx, tx) 
deduceType env (Lam x tx t _) =
   do newEnv    <- updateEnv (x,tx) env
      (cht, tt) <- deduceType newEnv t
      tlam      <- lamType tx tt
      return (Lam x tx cht tlam, tlam)
deduceType env (App r s _) = -- CAMBIAR!!! HAY QUE CHEQUEAR CUAL DE LAS DOS REGLAS USAR!!!!!
   error "To Do" {- do (r, tr) <- deduceType env r
                       (s, ts) <- deduceType env s
                       tapp    <- appType tr ts
                       return (App r s tapp, tapp)
                 -}
deduceType env (LC mt _) =
    do let tsi = MS.order mt
       (chtsi, tsup) <- deduceTypesForLC env tsi
       return (linCom chtsi tsup, tsup)

-- COMPLETAR

deduceTypesForLC env [((q,t),n)]     = 
    do checkNonDuplication n env (freeVars t)
       (cht', tt') <- deduceType env t
       stt' <- produceCompatibleSupTypeFor tt' tt'
       return ([((q,cht'),n)], stt')
deduceTypesForLC env (((q,t),n):ts) = 
    do checkNonDuplication n env (freeVars t)
       envForTs <- trimEnvWrt env t
       envForT  <- trimEnvWrt env (linCom ts ())
       checkOverlapIsDuplicable envForTs envForT
       (chts', stt') <- deduceTypesForLC envForTs ts
       (cht', tt')   <- deduceType envForT t 
       stt''         <- produceCompatibleSupTypeFor tt' stt'
       return ((((q,cht'),n):chts'), stt'')

       
-- This function is not right!!!!!!!
produceCompatibleSupTypeFor t1@(TSup t1') (TSup t2') = 
    do t' <- produceCompatibleSupTypeFor t1' t2'
       return (tSup t')
produceCompatibleSupTypeFor t1@(TSup t1') t2 =
    if (t1' /= t2)
     then raise ("Types are not compatible for Linear Combinations (" ++ show t1 ++ " --- " ++ show t2 ++ ")")
     else return t1
produceCompatibleSupTypeFor t1 t2@(TSup t2') = 
    if (t1 /= t2')
     then raise ("Types are not compatible for Linear Combinations (" ++ show t1 ++ " --- " ++ show t2 ++ ")")
     else return t2
produceCompatibleSupTypeFor t1 t2 = 
    if (t1 /= t2)
     then raise ("Types are not compatible for Linear Combinations (" ++ show t1 ++ " --- " ++ show t2 ++ ")")
     else return (tSup t1)
     
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


