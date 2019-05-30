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

import Data.List
import Multiset as MS
import QTypes as QT
import QTerms
import QTMonad
import Error
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
      envB <- restrictEnv env x          -- TODO: verify with Jano why tx is not checked
      checkAllDuplicable envB            --       in this checkAll
      return (Var x tx, tx) 
deduceType env (Lam x tx t _) =
   do newEnv    <- updateEnv (x,tx) env  -- TODO: check that tx is Phi (isQBitType)
      (cht, tt) <- deduceType newEnv t
      tlam      <- lamType tx tt
      return (Lam x tx cht tlam, tlam)
deduceType env (App t u _) = -- CAMBIAR!!! HAY QUE CHEQUEAR CUAL DE LAS DOS REGLAS USAR!!!!!
   do envForU <- trimEnvWrt env t
      envForT <- trimEnvWrt env u
      checkOverlapIsDuplicable envForT envForU
      (cht', tt') <- deduceType envForT t
      (chu', tu') <- deduceType envForU u
      tr' <- appType tt' tu'
      return (App cht' chu' tr', tr')
deduceType env (LC mt _) =
   do let tsi = MS.order mt
      (chtsi, tsup) <- deduceTypesForLC env tsi
      return (linCom chtsi tsup, tsup)
deduceType env (Prod [] _)  = raise ("Cannot have an empty Prod")
deduceType env (Prod [_] _) = raise ("Cannot have a singleton Prod")
deduceType env (Prod ts _)  =
   do (chts, tts) <- deduceTypesForProd env ts
      tprod       <- prodType tts
      return (Prod chts tprod, tprod)
deduceType env (Head t _) =
   do (cht, tt) <- deduceType env t
      (thead, _) <- unBnType tt
      return (Head cht thead, thead)
deduceType env (Tail t _) =
   do (cht, tt) <- deduceType env t
      (_, ttail) <- unBnType tt
      return (Tail cht ttail, ttail)
      

deduceType _ _ = raise "TODO"




deduceTypesForLC env [((alpha,t),n)]     = 
   do checkNonDuplication n env (freeVars t)
      (cht', tt') <- deduceType env t
      stt' <- produceCompatibleSupTypeFor tt' tt'  -- Adds a TSup if necessary
                ("This cannot happen, something went oddly wrong") -- This cannot fail, but added for consistency
      return ([((alpha,cht'),n)], stt')
deduceTypesForLC env (((alpha,t),n):ts) = 
   do checkNonDuplication n env (freeVars t)
      envForTs <- trimEnvWrt env t
      envForT  <- trimEnvWrts env ts
      checkOverlapIsDuplicable envForTs envForT
      (chts', stt') <- deduceTypesForLC envForTs ts
      (cht', tt')   <- deduceType envForT t 
      stt''         <- produceCompatibleSupTypeFor tt' stt'
                         ("Types are not compatible for Linear Combinations (" ++ show tt' ++ " --- " ++ show stt' ++ ")")
      return ((((alpha,cht'),n):chts'), stt'')

deduceTypesForProd env [t] = 
   do (cht, tt) <- deduceType env t
      return ([cht], tt)
deduceTypesForProd env (t:ts) = 
   do envForTs <- trimEnvWrt env t
      envForT  <- trimEnvWrts env ts
      checkOverlapIsDuplicable envForTs envForT
      (cht', tt')   <- deduceType envForT t
      (chts', tts') <- deduceTypesForProd envForTs ts
      return (cht':chts', tt':tts')

-- IDEA: this function should be used to replace several uses of rule (S_I)
produceCompatibleSupTypeFor t1 t2 errmsg = 
  do t' <- produceCompatibleTypeFor t1 t2 errmsg
     supType t'

produceCompatibleTypeFor t1 t2 errmsg =
  let (n1, t1') = QT.stripSups t1
      (n2, t2') = QT.stripSups t2
   in if (t1' == t2')
       then return (tSups (max n1 n2) t1')
       else raise errmsg
     
checkNonDuplication 1 _   _  = return ()
checkNonDuplication n env xs = do txs <- sequence (map (\x -> findTypeInEnv x env) xs)
                                  if (all isDuplicable txs)
                                   then return ()
                                   else raise "Non linear use of a variable"


---------------------------------------------------------
-- AUXILIARIES to build types inferred
---------------------------------------------------------
-- PRECOND: arguments are canonical
--lamType tx tr = return (QT.TFun tx tr)  -- This way, it does not verify formation properties
lamType = QT.buildFun return raise
                --return (tx QT.|=> tr) -- This fails with error, instead of raise, like above.

-- PRECOND: arguments are canonical
appType ft tt = let (nf, ft') = QT.stripSups ft
                    (nt, tt') = QT.stripSups tt
                 in case ft' of
                     QT.TFun b a -> do produceCompatibleTypeFor b tt'
                                         ("Arguments and parameters do not fit: " ++ show b ++ " expected, but " ++ show tt' ++ " provided")
                                       return (tSups (max nf nt) a)
                     _           -> raise "Non-function in function position"

supType = QT.buildSups return raise 1

prodType = QT.buildProds return raise

-- PRECOND: argument is canonical
unBnType tt = if (isBaseQBitN tt)
               then case tt of
                      QT.TProd (QT.TB:t':ts) -> 
                           do ts' <- prodType (t':ts)
                              return (QT.tB, ts')
                      QT.TProd (_:_:_)       ->
                           raise ("Argument is not cannonical in unBnType")
                      _                      ->
                           raise ("B^n with n<2 in Head or Tail")
               else raise ("B^n with n<2 in Head or Tail")

