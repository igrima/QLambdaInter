-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for <SOMETHING_HERE>
--               by Alejandro Díaz-Caro, Pablo E. "Fidel" Martínez López and Ignacio D. Grima
-- Version: 1.0
-- Developers: Ignacio D. Grima <nacho -at- fceia.unr.edu.ar > & Fidel <fidel -at- unq.edu.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2017  Ignacio D. Grima & Fidel & Alejandro Díaz-Caro
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
module QComplex where
-- Implements Q[sqrt(2), i] numbers, with a restricted division, that does not admit i in the denominator

import Data.Ratio

--                 Q part  |sq2 part|img part|sq2i part
data QComplex = QC Rational Rational Rational Rational

img :: QComplex
img = QC 0 0 1 0

sq2 :: QComplex
sq2 = QC 0 1 0 0

instance Eq QComplex where
  QC r1 s1 i1 si1 == QC r2 s2 i2 si2 = r1  == r2 &&
                                       s1  == s2 &&
                                       i1  == i2 &&
                                       si1 == si2

instance Show QComplex where
  show (QC r s i si) = alsoShowWhenZero (showRationalPart r .++. showSq2Part s .++. showIPart i .++. showSq2IPart si)

alsoShowWhenZero "" = "0"
alsoShowWhenZero s  = s

(.++.) :: String -> String -> String
"" .++. "" = ""
"" .++. s  = s
s  .++. "" = s
s1 .++. s2 = s1 ++ " + " ++ s2

(.%.) :: Integer -> Integer -> QComplex
n .%. m = fromRational (n % m)


showPart 0 _                      = ""
showPart r p | r == 1             = dropWhile (\c->c==' ') p
showPart r p | denominator r == 1 = show (numerator r) ++ p
showPart r ""                     = show r
showPart r p                      = "(" ++ show r ++ ")" ++ p

showRationalPart r = showPart r ""
showSq2Part      r = showPart r " sq2"
showIPart        r = showPart r " i"
showSq2IPart     r = showPart r " sq2 i"

instance Num QComplex where
  fromInteger n = QC (fromInteger n) 0 0 0

  QC r1 s1 i1 si1 + QC r2 s2 i2 si2 = QC (r1 + r2) (s1 + s2) (i1 + i2) (si1 + si2)

  QC r1 s1 i1 si1 - QC r2 s2 i2 si2 = QC (r1 - r2) (s1 - s2) (i1 - i2) (si1 - si2)

  QC r1 s1 i1 si1 * QC r2 s2 i2 si2 = QC (r1 * r2  + 2 * s1 * s2  -     i1 * i2  - 2 * si1 * si2)
                                         (r1 * s2  +     r2 * s1  -     i1 * si2 -     i2  * si1)
                                         (r1 * i2  +     r2 * i1  + 2 * s1 * si2 + 2 * s2  * si1)
                                         (r1 * si2 +     r1 * si1 +     s1 * i2  +     s2  * i1)

  abs qcomp = qcomp

  signum qcomp = 1

instance Fractional QComplex where
  fromRational n = QC n 0 0 0

  QC r1 s1 i1 si1 / QC r2 s2 0 0 = let denom = r2 * r2 - 2 * s2 * s2
                                    in QC ((r1  * r2 - 2 * s1  * s2) / denom) 
                                          ((s1  * r2 -     r1  * s2) / denom)
                                          ((i1  * r2 - 2 * si1 * s2) / denom)
                                          ((si1 * r2 -     i1  * s2) / denom)

  _               / _            = error "This case should never occur, thus we are not making any calculations for it"
