-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for QLambdaInter
--               by Alejandro Díaz-Caro, Pablo E. "Fidel" Martínez López, Ignacio D. Grima and Nicolás San Martín
-- Version: 1.0
-- Developer: Nicolás San Martín <nsanmartin -at- dc.uba.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2017  Nicolás San Martín based in code developed by Fidel <fidel -at- unq.edu.ar >
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

module LambdaS1TypeInference where

import Data.List
import Multiset as MS
import QTypes as QT
import QTerms
import QTMonad
import Error
import QEnvironments
import QTsTypeInference

---------------------------------------------------------
-- inferType
---------------------------------------------------------
decorateLambdaS1 r = getResValue (runQTM (decorateLambdaS1Term emptyEnv r))

decorateLambdaS1Term env r = do (chr,_) <- deduceLambdaS1Type env r
                                return chr
deduceLambdaS1Type :: Ord a => Environment -> BaseQT a -> QTMonad (ChurchQTerm, QType)

deduceLambdaS1Type = deduceType
