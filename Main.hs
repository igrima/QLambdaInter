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
ejLC2 = app ejLC2Fun kPlus

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

ejPEPE = lam "x" tB (var "x" <**> var "x")

ejMePEPEKPlus = proj 1 (up (app ejPEPE kPlus))

kPlus  = (1 / sq2) .> (k0 <+> k1)
kMinus = (1 / sq2) .> (k0 <+> ((-1) .> k1))

--hadamard |0> = |+>
--hadamard |1> = |->
--hadamard = qIf kMinus kPlus
hadamard = lam "a" tB (app (qIf kMinus kPlus) (var "a"))

ejHadamardK0 = app hadamard k0
ejHadamardK1 = app hadamard k1

qNot = lam "b" tB (app (qIf k0 k1) (var "b"))

h1 =  lam "c" (tBn 2) ((app hadamard (qHead (var "c"))) <**> (qTail (var "c")))

hadamardBoth = lam "d" (tBn 2) ((app hadamard (qHead (var "d"))) <**> (app hadamard (qTail (var "d"))))

-- this cannot be done, since we have a first order calculus
-- oracle = lam "f" (tB |=> tB) 
--            (lam "x" (tBn 2) 
--              ((qHead (var "x")) <**> 
--               (app (qIf 
--                      (app qNot (app (var "f") (qHead (var "x")))) 
--                      (app (var "f") (qHead (var "x")))) 
--                    (qTail (var "x")))))
-- so we have to "cheat", and do this one down here, justifying it with
-- the fact that an oracle is actually a matrix, and we can always build
-- a matrix when we know how f is defined
oracle f = (lam "e" (tBn 2) 
             ((qHead (var "e")) <**> 
              (app (qIf 
                     (app qNot (app f (qHead (var "e")))) 
                     (app f (qHead (var "e")))) 
                   (qTail (var "e")))))

zeroXone      = (k0 <**> k1)
hBothZeroXOne = app hadamardBoth zeroXone
upH0x1        = up hBothZeroXOne

-- as "oracle f" is a license we take, accepting a function as a parameter, just because Uf can be actually represented
-- by a static matrix, we can also write deutsch f without the fear of breaking first order.
deutsch f = proj 1 (up (app h1 (app (oracle f) upH0x1)))
            
---
---
cnot = lam "j" (tBn 2) ((qHead (var "j")) <**> (app (qIf (app qNot (qTail (var "j"))) (qTail (var "j"))) (qHead (var "j"))))

-- CONTINUE HERE: h31 = lam "x" (tBn 3) 




-- TODO:
-- \x:S(B).x+x
-- \x:S(B).2.x
-- \x:B.xx
-- \x:B=>B.xx
-- \x.S(B=>B).xx



main = do
  -- writeFile "Example/body.tex" (traceReduce $ decorate ejForReduce2)
  -- writeFile "Example/body.tex" (showChQT (decorate ejHadamardK1))
  -- THIS IS THE GOOD ONE: 
  writeFile "Example/body.tex" (showChQT (decorate (deutsch (lam "x" tB (var "x")))))
  --writeFile "Example/body.tex" (showChQT (reduce (app (qIf k0 k1) ((3 .> k1) <+> (2 .> k0)) )))
  --writeFile "Example/body.tex" (showChQT (decorate (app (qIf k0 k1) ((3 .> k1) <+> (2 .> k0)) )))
 --  return ()
