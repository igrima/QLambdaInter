-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for <SOMETHING_HERE>
--               by Alejandro Díaz-Caro, Pablo E. "Fidel" Martínez López and Ignacio D. Grima
-- Version: 1.0
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

module QEnvironments where

import QTypes as QT
import QTerms
import QTMonad
import List

---------------------------------------------------------
-- Environment
---------------------------------------------------------
newtype Environment = E [(Vble, QT.QType)]

emptyEnv = E []


buildEnv :: [(Vble, QT.QType)] -> QTMonad Environment
buildEnv xts = do xts' <- buildEnvRep xts
                  return (E xts')

{-
buildEnv :: [(Vble, QT.QType)] -> Maybe Environment
buildEnv xts = fmap E (buildEnvRep xts)
-}

appEnv :: Environment -> Vble -> Maybe QT.QType
appEnv (E xts) x = lookup x xts

updateEnv :: Environment -> Vble -> QT.QType -> QTMonad Environment
updateEnv (E xts) x tx = addToEnvRep (x,tx) xts
                            

{- updateEnv :: Environment -> Vble -> QT.QType -> Maybe Environment
updateEnv (E xts) x tx = fmap E (addToEnvRep (x,tx) xts) -}

-- To be used in rules that should split nonduplicable variables
trimEnvWrt :: Ord a => Environment -> BaseQT a -> Maybe Environment
trimEnvWrt (E xts) t = fmap E (trimEnvRep xts (freeVars t))
                            -- The result of trimEnvRep is a Maybe, 
                            -- that should be lifted with fmap

restrictEnv (E xts) x = E (restrictEnvRep xts x)

checkAllDuplicable (E xts) = checkAllDuplicableRep xts
                            
-- To be used in rules that should split nonduplicable variables
--  (the overlap of both trims should be duplicable)
overlapIsDuplicable :: Environment -> Environment -> Bool
overlapIsDuplicable (E xts) (E xts') = case (intersectEnvRep xts xts') of 
                                        Nothing  -> False       -- When can this happen?
                                        Just xts -> all (isDuplicable . snd) xts
                                        {-
                                        (do xts'' <- intersectEnvRep xts xts'
                                            return (all (isDuplicable . snd) xts'')
                                        ) `mplus` (return False)
                                        -}

-- Environment representation manipulation
--  (addToEnvRep and intersectEnvRep may bew improved to use Error monad...)
buildEnvRep xts = foldr addToMaybeER (Just []) xts

-- TODO:NACHO:THIS HERE IS ALL WRONG!!!!!!
addToEnvRep :: (Vble, QT.QType) -> [(Vble, QT.QType)] -> QTMonad Environment
addToEnvRep xt    xts = do xts' <- addToMaybeER xt (Just xts)
                         return (case xts' of 
                                  Nothing -> {-SOMETHING SHALL BE DONE HERE?-}
                                  Just xts'' -> (E xts''))

{- addToEnvRep xt    xts = addToMaybeER xt (Just xts) -}

addToMaybeER _     Nothing              = Nothing
addToMaybeER xt    (Just [])            = Just [xt]
addToMaybeER (x,t) (Just ((x',t'):xts)) = 
    if (x==x') 
     then Nothing
     else fmap ((x',t') :) (addToEnvRep (x,t) xts)

trimEnvRep xts []     = Just xts
trimEnvRep xts (x:xs) = 
  case (lookup x xts) of
    Nothing -> Nothing
    Just tx -> if (isDuplicable tx)
                then trimEnvRep xts xs
                else trimEnvRep (restrictEnvRep xts x) xs

restrictEnvRep [] _ = []
restrictEnvRep ((x', t'):xts) x =
           if x==x' && (not (isDuplicable t'))
            then restrictEnvRep xts x
            else (x',t') : restrictEnvRep xts x

checkAllDuplicableRep []          = return ()
checkAllDuplicableRep ((_,t):xts) = if (isDuplicable t) 
                                     then checkAllDuplicableRep xts
                                     else raise "Nonduplicable variables discarded in environment"
                                       
            
{-                
intersectEnvRep []           _    = return []
intersectEnvRep ((x,tx):xts) xts' = 
    case (lookup x xts') of 
       Nothing  -> intersectEnvRep xts xts'
       Just tx' -> if (tx==tx') 
                    then do xts'' <- intersectEnvRep xts xts'
                            return ((x,tx) : xts'')
                    else raise "PONER MENSAJE DE ERROR" 
-}                    
                
intersectEnvRep []           _    = Just []
intersectEnvRep ((x,tx):xts) xts' = 
    case (lookup x xts') of 
       Nothing  -> intersectEnvRep xts xts'
       Just tx' -> if (tx==tx') 
                    then fmap ((x,tx) :) (intersectEnvRep xts xts')
                    else Nothing
