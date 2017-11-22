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

import QTerms
import QTypes
import QTsTypeInference
import QTsReduction
import QTrace

ejZero = k0
ejOne  = k1

ejId = lam "x" baseQ (var "x")
ejIdB = lam "b"baseQ(var "b")

ejIdInZero = app ejIdB ejZero
ejIdInOne  = app ejIdB ejOne

ejHOId = lam "x" (baseQ |-> baseQ) (var "x")

ejApply = lam "f" (baseQ |-> baseQ) (lam "x" baseQ (app (var "f") (var "x")))

ejApIdId = lam "t" baseQ (app (app ejApply ejId) (var "t"))

ejForReduce1 = app (app (lam "x"baseQ(lam "y"baseQ(var "x"))) k0) k1

ejForReduce2 = app (app (lam "x"baseQ(lam "y" (baseQ |-> baseQ) (var "x"))) ejForReduce1) ejId


ejReduceOne = reduceOne (decorate ejIdInOne)

--ejReduceMore = 

main = do
    writeFile "Example/body.tex" (traceReduce $ decorate ejForReduce2)
    return ()