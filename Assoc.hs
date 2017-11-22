-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for paper "Isomorphisms as Equalities" 
--               by Alejandro Díaz-Caro and Pablo E. "Fidel" Martínez López
-- Version: 1.0
-- Developer: Fidel <fidel -at- unq.edu.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2015  Pablo E. Martínez López
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
module Assoc where

data Assoc k v = k := v
key   (k:=v) = k
value (k:=v) = v
templateAssoc k = k := (error "valor de fantasia!")

instance (Eq k) => Eq (Assoc k v) where
  (k := _) == (k' := _) = k == k'

instance (Ord k) => Ord (Assoc k v) where
  (k := _) <= (k' := _) = k <= k' -- This function is also needed. If not, it fails...
  (k := _) <  (k' := _) = k < k'

instance (Show k) => Show (Assoc k v) where
  show (k:=_) = show k

