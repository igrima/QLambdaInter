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
--import List(sort)

---------------------------------------------------------
-- Environment
---------------------------------------------------------
newtype Environment = E (Vble -> Maybe QT.QType)

emptyEnv = E (\x -> Nothing)

buildEnv :: [(Vble, QT.QType)] -> Environment
buildEnv vts = E (\v -> lookup v vts)

appEnv :: Environment -> Vble -> Maybe QT.QType
appEnv (E env) x = env x

updateEnv :: Environment -> Vble -> QT.QType -> Environment
updateEnv env x tx = E (\y -> if x==y then Just tx else appEnv env y)
---------------------------------------------------------
-- inferType
---------------------------------------------------------
infer r = let (x, _, _) = runQTM (inferType emptyEnv r) 
           in x

inferType env r = do (_,tr) <- deduceTypes env r
                     return tr

decorate r = let (x, _, _) = runQTM (decorateTerm emptyEnv r) 
              in x

decorateTerm env r = do (chr,_) <- deduceTypes env r
                        return chr

deduceTypes :: Environment -> QTerm -> QTMonad (ChurchQTerm, QType)
deduceTypes env (Var x _) = 
   do tx <- findTypeInEnv x env
      return (Var x tx, tx) 
deduceTypes env (Lam x tx r _) =
   do newEnv    <- addTypeToEnv (x,tx) env
      (chr, tr) <- deduceTypes newEnv r
      tlam      <- lamType tx tr
      return (Lam x tx chr tlam, tlam)
deduceTypes env (App r s _) = 
   do (r, tr) <- deduceTypes env r
      (s, ts) <- deduceTypes env s
      tapp    <- appType tr ts
      return (App r s tapp, tapp)
deduceTypes env (Base k) = return (Base k, B)

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

