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

deduceType :: Ord a => Environment -> BaseQT a -> QTMonad (ChurchQTerm, QType) -- We add QType at the end
deduceType env (Null t)  =        -- rule Ax0                      -- for easy access in recursive
   do checkAllNonLinear env                                       -- calls. 
      st <- supType t
      return (Null t, st) -- Constructor Null implies a Sup in the type
deduceType env (QBit b) =         -- rules Ax|0> and Ax|1>
   do checkAllNonLinear env 
      return (QBit b, QT.tB)
deduceType env (Var x _) =        -- rule Ax
   do tx   <- findTypeInEnv x env
      envB <- restrictEnv env x          -- envB needs to be non linear because they're not used
      checkAllNonLinear envB            -- in this rule (we can only discard non-linear things)
      return (Var x tx, tx) 
deduceType env (Lam x tx t _) =
   if (not (isQBitType tx)) then raise ("Type " ++ show tx ++ " is not a valid argument type for lambda") else
   do newEnv    <- updateEnv (x,tx) env
      (cht, tt) <- deduceType newEnv t
      tlam      <- lamType tx tt
      return (Lam x tx cht tlam, tlam)
deduceType env (App t u _) = -- appType select which rule to use, through supsType (max nf nt) a
   do envForU <- trimEnvWrt env t
      envForT <- trimEnvWrt env u
      checkOverlapIsNonLinear envForT envForU
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
   do (cht, tt)  <- deduceType env t
      tbns <- unBnType tt
      case tbns of 
        [thead,_] -> return (Head cht thead, thead)
        _         -> raise "Argument is not B^n with n>1 in Head"
deduceType env (Tail t _) =
   do (cht, tt) <- deduceType env t
      tbns      <- unBnType tt
      case tbns of 
        [_,ttail] -> return (Tail cht ttail, ttail)
        _         -> raise "Argument is not B^n with n>1 in Tail"
deduceType env (Proj j t _) = 
   do (cht, tt) <- deduceType env t
      tt'       <- unSupType tt
      if j<=0 then raise "Wrong projection" else
       do tbns      <- splitBnType j tt'
          case tbns of 
            (bj:bnj:[]) -> do sbnj <- supType bnj
                              tr   <- prodType [bj, sbnj]
                              return (Proj j cht tr, tr)
            (bj:[])     -> return (Proj j cht bj, bj)
            _           -> raise "CANNOT HAPPEN: splitBnType has changed?"
deduceType env (QIf t r _) =
   do (cht, tt) <- deduceType env t
      (chr, tr) <- deduceType env r
      ta        <- produceCompatibleTypeFor tt tr 
                     ("Branch Types not compatible in QIf:\n" ++ show tt ++ "\n" ++ show tr)
      tqif      <- qifType ta
      return (QIf cht chr tqif, tqif)
deduceType env (Up t _) =
   do (cht, tt) <- deduceType env t
      tt'       <- unSupType tt
      stt'      <- upType tt'
      return (Up cht stt', stt')

deduceType _ _ = raise "TODO"


deduceTypesForLC env [((t,alpha),n)]     = 
   do checkLinearUse n env (freeVars t)
      (cht', tt') <- deduceType env t
      stt' <- produceCompatibleSupTypeFor tt' tt'  -- Adds a TSup if necessary
                ("This cannot happen, something went oddly wrong") -- This cannot fail, but added for consistency
      return ([((cht',alpha),n)], stt')
deduceTypesForLC env (((t,alpha),n):ts) = 
   do checkLinearUse n env (freeVars t)
      envForTs <- trimEnvWrt env t
      envForT  <- trimEnvWrts env (map (fst . fst) ts)
      checkOverlapIsNonLinear envForTs envForT
      (chts', stt') <- deduceTypesForLC envForTs ts
      (cht', tt')   <- deduceType envForT t 
      stt''         <- produceCompatibleSupTypeFor tt' stt'
                         ("Types are not compatible for Linear Combinations (" ++ show tt' ++ " --- " ++ show stt' ++ ")")
      return ((((cht',alpha),n):chts'), stt'')

deduceTypesForProd env [t] = 
   do (cht, tt) <- deduceType env t
      return ([cht], [tt])
deduceTypesForProd env (t:ts) = 
   do envForTs <- trimEnvWrt env t
      envForT  <- trimEnvWrts env ts
      checkOverlapIsNonLinear envForTs envForT
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
       then supsType (max n1 n2) t1'
       else raise errmsg
     
checkLinearUse 1 _   _  = return ()
checkLinearUse n env xs = do txs <- sequence (map (\x -> findTypeInEnv x env) xs)
                             if (all (not . isLinear) txs)
                              then return ()
                              else raise "Non linear use of a linear variable"


---------------------------------------------------------
-- AUXILIARIES to build types inferred
---------------------------------------------------------
-- PRECOND: arguments are normalized
--lamType tx tr = return (QT.TFun tx tr)  -- This way, it does not verify formation properties
lamType = QT.buildFun return raise
                --return (tx QT.|=> tr) -- This fails with error, instead of raise, like above.

-- PRECOND: arguments are normalized
appType ft tt = let (nf, ft') = QT.stripSups ft
                    (nt, tt') = QT.stripSups tt
                 in case ft' of
                     QT.TFun b a -> do produceCompatibleTypeFor b tt'
                                         ("Arguments and parameters do not fit: " ++ show b ++ " expected, but " ++ show tt' ++ " provided")
                                       supsType (max nf nt) a
                     _           -> raise "Non-function in function position"

supType = QT.buildSups return raise 1
supsType = QT.buildSups return raise

prodType [t]    = return t
prodType (t:ts) = do tp <- prodType ts
                     buildProd return raise t tp
prodType _      = raise "Cannot build an empty product"

qifType ta = QT.buildFun return raise QT.tB ta

-- Argument is normalized
upType (QT.TProd ts) = do ts' <- upTypeRep ts
                          tu  <- prodType ts' 
                          supType tu
upType _             = raise "Cannot lift a non-product term" 

upTypeRep []     = return []
upTypeRep (t:ts) = do t'  <- unSupType t
                      ts' <- upTypeRep ts
                      case t' of 
                        QT.TProd tts -> do tts' <- upTypeRep tts
                                           return (tts'++ts')
                        _            -> return (t':ts')

unSupType tt = return (QT.unSup tt)

-- PRECOND: argument is normalized
unBnType tt = splitBnType 1 tt

splitBnType j tt | j > 0 = 
  if (QT.isBaseQBitN tt)
   then case tt of
         QT.TProd ts -> do (ts1,ts2) <- splitBnTypeRep j ts
                           case ts2 of
                             [] -> return [ QT.tProd ts1 ]
                             _  -> return [ QT.tProd ts1, QT.tProd ts2 ]
         QT.TB       -> if j==1 
                         then return [ QT.TB ]
                         else raise "Attempt to project more dimensions than available"
         _           -> raise "CANNOT HAPPEN: isBaseQBitN has changed?"
   else raise "Argument is not B^n with n>1 in splitBnType"
splitBnType _ _ = raise "Cannot call splitBnType with j<=0"

splitBnTypeRep 0 ts = return ([],ts)
splitBnTypeRep j [] = raise "Attempt to project more dimensions than available"
splitBnTypeRep j (QT.TB:ts') = 
  if j == 1 then return ([QT.tB], ts')
            else do (ts1, ts2) <- splitBnTypeRep (j-1) ts'
                    return (QT.tB:ts1, ts2)
splitBnTypeRep _ _ = raise "Argument isn't normalized in splitBnType" 
