-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for <SOMETHING_HERE>
--               by Alejandro Díaz-Caro, Pablo E. "Fidel" Martínez López and Ignacio D. Grima
-- Version: 1.0
-- Developer: Ignacio D. Grima <nacho -at- fceia.unr.edu.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2017  Ignacio D. Grima
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
module Main where

import Multiset as MS
import QComplex
import QTerms
import QTypes as QT
import QTMonad
import QEnvironments
import QTsTypeInference
--import QTsReduction
--import QTrace

runM m = getResValue (runQTM m)

ejLCBody = k0 <+> var "x"
ejLCWrongBody = var "x" <+> var "x"
ejLCSB = lam "x" (tSup QT.tB) ejLCBody
ejLCB = lam "x" (QT.tB) ejLCBody
ejLCWrong = lam "x" (tSup QT.tB) ejLCWrongBody
envLC = runM (updateEnv ("x", tSup QT.tB) emptyEnv)

ejLC2Fun = lam "x" (QT.tB) (var "x" <+> var "x")
ejLC2 = app ejLC2Fun ejKPlus

ejLCB2 = ejIdB <+> ejLCB
ejLCSB2 = ejSBId <+> ejLCSB

ejZero = k0
ejOne  = k1

ejId  = lam "x" tB (var "x")
ejIdB = lam "b" tB (var "b")

ejIdInZero = app ejIdB ejZero
ejIdInOne  = app ejIdB ejOne

ejSBId = lam "x" (tSup tB) (var "x")

ejHOId = lam "x" (tB |=> tB) (var "x")

ejApply = lam "f" (tB |=> tB) (lam "x" tB (app (var "f") (var "x")))

ejApIdId = lam "t" tB (app (app ejApply ejId) (var "t"))

ejForReduce1 = app (app (lam "x" tB (lam "y" tB (var "x"))) k0) k1

ejForReduce2 = app (app (lam "x" tB (lam "y" (tB |=> tB) (var "x"))) ejForReduce1) ejId

ejCNot = lam "x" tB (var "x" <**> var "x")

ejKPlus = (1 / sq2) .> (ejZero <+> ejOne)

ejMeCNotKPlus = proj 1 (upR (app ejCNot ejKPlus))

--ejReduceOne = reduceOne (decorate ejIdInOne)

--ejReduceMore = 

main = do
--   writeFile "Example/body.tex" (traceReduce $ decorate ejForReduce2)
   writeFile "Example/body.tex" (showChQT (decorate ejForReduce1))
   return ()
