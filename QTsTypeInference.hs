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

import QTypes as QT
import QTerms
import QTMonad
import Error
import List
import QEnviroments


---------------------------------------------------------
-- inferType
---------------------------------------------------------
infer r = getResValue (runQTM (inferType emptyEnv r))

inferType env r = do (_,tr) <- deduceTypes env r
                     return tr

decorate r = getResValue (runQTM (decorateTerm emptyEnv r))

decorateTerm env r = do (chr,_) <- deduceTypes env r
                        return chr

deduceTypes :: Environment -> QTerm -> QTMonad (ChurchQTerm, QType)
deduceTypes env (Null t)  = 
   do checkAllDuplicable env
      return (Null t, t)
deduceTypes env (QBit b) = 
   do checkAllDuplicable env 
      return (QBit b, QT.qB)
deduceTypes env (Var x _) = 
   do tx   <- findTypeInEnv x env
      envB <- restrictEnv env x
      checkAllDuplicable envB
      return (Var x tx, tx) 
deduceTypes env (Lam x tx t _) =
   do newEnv    <- addTypeToEnv (x,tx) env
      (cht, tt) <- deduceTypes newEnv t
      tlam      <- lamType tx tt
      return (Lam x tx cht tlam, tlam)
deduceTypes env (App r s _) = -- CAMBIAR!!! HAY QUE CHEQUEAR CUAL DE LAS DOS REGLAS USAR!!!!!
   do (r, tr) <- deduceTypes env r
      (s, ts) <- deduceTypes env s
      tapp    <- appType tr ts
      return (App r s tapp, tapp)
-- COMPLETAR
---------------------------------------------------------
-- AUXILIARIES to build types inferred
---------------------------------------------------------
-- PRECOND: tr and ts are canonical
lamType tx tr = return (QT.Fun tx tr)

-- PRECOND: tr and ts are canonical
appType (Fun a b) c = if a == c
                       then return b
                       else raise ("Arguments and parameters do not fit: " ++ show a ++ " y el otro " ++ show c)
appType _         _ = raise "Non-function in function position"
                      
---------------------------------------------------------
-- AUXILIARIES to inferType
---------------------------------------------------------
findTypeInEnv x env = 
  case (appEnv env x) of
    Nothing -> raise ("Term has free variable " ++ x)
    Just tx -> return tx

addTypeToEnv (x,tx) env = 
  case (appEnv env x) of
   Just _  -> raise ("Variable " ++ x ++ " already has a type in context")
   Nothing -> return (updateEnv env x tx)

-}