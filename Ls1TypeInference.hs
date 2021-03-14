-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for QLambdaInter
--               by Alejandro Díaz-Caro, Pablo E. "Fidel" Martínez López, Ignacio D. Grima and Nicolás San Martín
-- Version: 1.0
-- Developer: Nicolás San Martín <nsanmartin -at- dc.uba.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2017  Nicolás San Martín
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

module Ls1TypeInference where

import Data.List
import Multiset as MS
import QTypes as QT
import QTerms
import QTMonad
import Error
import QEnvironments
import QTsTypeInference


isValidTypeForQIf :: QType -> Bool
isValidTypeForQIf (TSup _) = False -- TODO: not implemented yet
isValidTypeForQIf x = isBaseQBitN x


canComputeOrthogonality :: BaseQT a -> Bool
canComputeOrthogonality (QBit _)      = True
canComputeOrthogonality (Prod ts _)   = all canComputeOrthogonality ts
canComputeOrthogonality _             = False

areOrthogonal :: Eq a => (BaseQT a) -> (BaseQT a) -> Bool
areOrthogonal (QBit x) (QBit y) = x /= y
areOrthogonal (Prod ts _) (Prod tt _) = ts /= tt
areOrthogonal (LC v _) (LC w _) = True --TODO: implement this!
areOrthogonal (LC mt _) _ = False
areOrthogonal _ (LC mt _) = False
areOrthogonal _ _ = False

---------------------------------------------------------
-- inferType
---------------------------------------------------------
decorateLs1 r = getResValue (runQTM (decorateTermLs1 emptyEnv r))

decorateTermLs1 env r = do
  (chr,_) <- deduceTypeLs1 env r
  return chr

deduceTypeLs1 :: Ord a => Environment -> BaseQT a -> QTMonad (ChurchQTerm, QType)
deduceTypeLs1 env (Null t)  = raise ("There is no Null vector")
deduceTypeLs1 env (QIf t r x) =
   do (cht, tt) <- deduceTypeLs1 env t
      (chr, tr) <- deduceTypeLs1 env r
      if not (isValidTypeForQIf tt) || not (isValidTypeForQIf tr)
        then raise ("Branch Types not compatible in QIf:\n" ++ show tt ++ "\n" ++ show tr)
        else
        do
          if (areOrthogonal cht chr)
            then
            do
              ta <- produceCompatibleTypeFor tt tr 
                    ("Branch Types not compatible in QIf:\n" ++ show tt ++ "\n" ++ show tr)
              tqif <- qifType ta
              return (QIf cht chr tqif, tqif)
            else raise ("Branch Types must be orthogonal")

deduceTypeLs1 a b = deduceType a b
