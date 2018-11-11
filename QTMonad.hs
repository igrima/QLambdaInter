-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for <SOMETHING_HERE>
--               by Alejandro Díaz-Caro, Pablo E. "Fidel" Martínez López and Ignacio D. Grima
-- Version: 1.0
-- Developer: Ignacio D. Grima <nacho -at- fceia.unr.edu.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2017  Ignacio D. Grima & Fidel <fidel -at- unq.edu.ar >
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
module QTMonad
{-
              (QTMonad, initialState, runQTM
              ,QTState, QConsole    , getResValue, getResLog, getConsole, getReductionTrace
                      , printf      , update     
                      , setTerm     , logTerm    , logReduction
                      , newVar      
-}                      
 where

import Error
import MapList as Map
import QTerms as T
import QTrace

type Variable = String
            -- (X -> NextVarForX, NextFreeVar, Log)
type QTState = (Map Variable Int, Int        , QReductionTrace)
type QConsole = String

-- Monad with state, error and output
newtype QTMonad a = QTM (QTState -> Error (a, QTState, QConsole))

unQTM (QTM f) = f

initialState :: QTState
initialState = (Map.emptyM, 0, [])

runQTM :: QTMonad a -> (a, QTState, QConsole)
runQTM (QTM f) = success (f initialState) error id

getResValue :: (a, QTState, QConsole) -> a
getResValue (x,_,_) = x

getResNext  (_,(_,i,_),_)  = i
getResLog   (_,(_,_,ts),_) = ts

getConsole  (_,_,c) = c


instance Functor QTMonad where
  fmap f (QTM fs) = QTM (\mem -> let xmo = fs mem in fmap (\(x,m,o) -> (f x,m,o)) xmo)

  
-- Only for GHC 
{-
instance Applicative QTMonad where
  pure x = QTM (\mem -> return (x,mem,""))
  (QTM ff) <*> (QTM fx) = QTM (\mem0 -> do (f,mem1,out1) <- ff mem0
                                           (x,mem2,out2) <- fx mem1
                                           return (f x,mem2,out1++out2))
-}                                           

instance Monad QTMonad where
  return x = QTM (\mem -> return (x,mem,""))
  m >>= k = QTM (\mem0 -> do (x,mem1,out1) <- unQTM m mem0
                             (y,mem2,out2) <- unQTM (k x) mem1
                             return (y,mem2,out1++out2))

instance Exception QTMonad where
  raise msg = QTM (\mem -> raise msg)
  failingWithMsg (QTM f) msg = QTM (\mem -> failingWithMsg (f mem) msg)
                             
-- Operations related with the console
printf :: String -> QTMonad ()
printf msg = QTM (\mem -> return ((),mem,msg))

setTerm :: ChurchQTerm -> QTMonad ()
setTerm t = QTM (\mem -> return ((), setTermMem t mem, ""))

logTerm :: ChurchQTerm -> QTMonad ()
logTerm t = QTM (\mem -> return ((), logTermMem t mem, ""))

logReduction :: String -> QTMonad ()
logReduction rule = QTM(\mem -> return ((), logRedMem rule mem, ""))
              
-- Operations related with the generation of fresh variables
newVar x = QTM (\mem -> let (fvar, newmem) = genVarMem mem x
                         in return (fvar,newmem,""))
                          
-- Operations related with the state 
update :: (QTState -> QTState) -> QTMonad ()
update f = QTM (\mem -> return ((),f mem,""))

-- Operations related with the memory
defVar :: Variable -> QTMonad ()
defVar v = update (\mem -> case (lookupMem mem v) of
                             Nothing -> addMem mem v 0
                             Just _  -> error ("Variable " ++ v ++ " already defined!"))

getVar :: Variable -> QTMonad Int
getVar v = QTM (\mem -> case (lookupMem mem v) of
                          Nothing -> raise ("Variable " ++ v ++ " not defined!")
                          Just n  -> return (n, mem, ""))

setVar :: Variable -> Int -> QTMonad ()
setVar v n = update (\mem -> addMem mem v n)

incVar :: Variable -> QTMonad ()
incVar v = do n <- getVar v
              setVar v (n+1)

-- ============================================
-- Operations related with the map part of the state                            
lookupMem :: QTState -> Variable -> Maybe Int
lookupMem (map,_,_) v = lookupM v map

addMem :: QTState -> Variable -> Int -> QTState
addMem (map, i, ts) v n = (addM v n map, i, ts)

-- ============================================
-- Operations related with the generation of fresh variables part of the state
genVarMem (map, next, ts) x = (x  ++ show next, (map, next+1, ts))

-- ============================================
-- Operations related with the trace log
setTermMem t (map, next, _) = (map, next, [("", t)])

logTermMem t (map, next, ls) = (map, next, ("", t):ls)

logRedMem rule (map, next, (_,t):ls) = (map, next, (rule, t):ls)
logRedMem _ _ = error "There's no term set to log a reduction rule"

getReductionTrace (_, _, ls) = reverse ls
