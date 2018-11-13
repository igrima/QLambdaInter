-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for <SOMETHING_HERE>
--               by Alejandro Díaz-Caro, Pablo E. "Fidel" Martínez López and Ignacio D. Grima
-- Version: 1.1
-- Developer: Ignacio D. Grima <nacho -at- fceia.unr.edu.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2018  Ignacio D. Grima, based in code developed by Fidel <fidel -at- unq.edu.ar >
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

module QEnvironments(Environment, emptyEnv, buildEnv, updateEnv, appEnv 
                                , trimEnvWrt, restrictEnv
                                , checkAllDuplicable, checkOverlapIsDuplicable
                    )
 where

import QTypes as QT
import QTerms
import QTMonad as QTM
import List

---------------------------------------------------------
-- Environment
---------------------------------------------------------
newtype Environment = E [(Vble, QT.QType)]

emptyEnv                 :: Environment
buildEnv                 :: [(Vble, QT.QType)] -> QTMonad Environment
updateEnv                :: Environment -> Vble -> QT.QType -> QTMonad Environment
appEnv                   :: Environment -> Vble -> Maybe QT.QType
trimEnvWrt               :: Ord a => Environment -> BaseQT a -> QTMonad Environment
restrictEnv              :: Environment -> Vble -> QTMonad Environment
checkAllDuplicable       :: Environment -> QTMonad ()
checkOverlapIsDuplicable :: Environment -> Environment -> QTMonad Bool

emptyEnv                   = E []

buildEnv   xts             = fmap E (buildEnvRep xts)

appEnv    (E xts) x        = lookup x xts

updateEnv (E xts) x tx     = fmap E (addToEnvRep (x,tx) xts)

-- To be used in rules that should split nonduplicable variables
--   (it should remove from the environment all freeVars of t that are NOT duplicable)
trimEnvWrt (E xts) t       = fmap E (trimEnvRep xts (freeVars t))

restrictEnv (E xts) x      = E (restrictEnvRep xts x)

checkAllDuplicable (E xts) = checkAllDuplicableRep xts
                            
-- To be used in rules that should split nonduplicable variables
--  (the overlap of both trims should be duplicable)
-- PRECOND: environments are compatible
checkOverlapIsDuplicable (E xts) (E xts') = 
    do xts'' <- intersectEnvRep xts xts'
       checkAllDuplicableRep xts''

----------------------------------------------
-- Environment representation manipulation
----------------------------------------------
buildEnvRep :: [(Vble, QT.QType)] -> QTMonad [(Vble, QT.QType)]
buildEnvRep []       =  return []
buildEnvRep (xt:xts) =  do xts' <- buildEnvRep xts
                           addToEnvRep xt xts'

addToEnvRep :: (Vble, QT.QType) -> [(Vble, QT.QType)] -> QTMonad [(Vble, QT.QType)]
addToEnvRep (xt@(x,_)) xts = case lookup x xts of
                              Just _ -> raise ("Variable " ++ x ++ " already in the Environment")
                              _      -> return (xt:xts)

-- It removes all the variables in xs from the environment, it their types are nonDuplicable
trimEnvRep xts []     = return xts
trimEnvRep xts (x:xs) = 
  case (lookup x xts) of
    Nothing -> raise ("There is no " ++ x ++ " in the environment")
    Just tx -> if (isDuplicable tx)
                then trimEnvRep xts xs
                else trimEnvRep (restrictEnvRep xts x) xs

-- It removes x from the environment, if its type is nonDuplicable
restrictEnvRep [] _ = []
restrictEnvRep ((xt'@(x', t')):xts) x =
           if x==x' && (not (isDuplicable t'))
            then restrictEnvRep xts x
            else (x',t') : restrictEnvRep xts x

checkAllDuplicableRep []          = return ()
checkAllDuplicableRep ((_,t):xts) = if (isDuplicable t) 
                                     then checkAllDuplicableRep xts
                                     else raise "Nonduplicable variables discarded in environment"
                                       
-- PRECOND: both lists are compatible
intersectEnvRep []           _    = return []
intersectEnvRep ((x,tx):xts) xts' = 
    case (lookup x xts') of 
       Nothing  -> intersectEnvRep xts xts'
       Just tx' -> if (tx==tx') 
                    then fmap ((x,tx):) (intersectEnvRep xts xts')
                    else raise "Environments are not compatible in check"
