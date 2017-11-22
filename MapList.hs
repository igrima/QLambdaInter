-- ----------------------------------------------------------------------------------------------------------//
-- Project Name: code for <SOMETHING_HERE>
--               by Alejandro Díaz-Caro, Pablo E. "Fidel" Martínez López and Ignacio D. Grima
-- Version: 1.0
-- Developer: Fidel <fidel -at- unq.edu.ar >
-- License: GNU General Public License, v2
-- License Official Site: http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
-- ---------------------------------------------------------------------------------------------------------- //
-- Copyright (c) 2009  Pablo E. Martínez López
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
module MapList
(Map, emptyM, isEmptyM, addM, lookupM, removeM, domM, renderM) 
where

import Assoc 

-- INTERFACE
emptyM   :: Map clave valor
isEmptyM :: Map clave valor -> Bool
addM     :: Eq clave => clave -> valor 
                              -> Map clave valor 
                              -> Map clave valor
         -- When adding repeated keys, last added prevails
lookupM  :: Eq clave => clave -> Map clave valor 
                              -> Maybe valor
removeM  :: Eq clave => clave -> Map clave valor 
                              -> Map clave valor 
domM     :: Map clave valor  -> [clave]
         -- The resulting list has no duplicates

-- show,
renderM :: Show k => Map k v -> String

-- IMPLEMENTATION
newtype Map k v = M [Assoc k v]

emptyM            = M []
isEmptyM  (M kvs) = null kvs
addM k v  (M kvs) = M (addRep k v kvs)
lookupM k (M kvs) = lookup' (templateAssoc k) kvs
removeM k (M kvs) = M (remove (templateAssoc k) kvs)
domM      (M kvs) = dom kvs

instance (Show k) => Show (Map k v) where
  show m = renderM m

renderM m = show (domM m)

addRep :: Eq k => k -> v -> [Assoc k v] -> [Assoc k v]
addRep k v []             = [k:=v]
addRep k v ((k':=v'):kvs) = if k==k' 
                             then (k':=v) : kvs
                             else (k':=v') : addRep k v kvs

-- Auxiliaries
lookup' k []       = Nothing
lookup' k (k':kvs) = if k==k'
                      then Just (value k')
                      else lookup' k kvs

remove k []      = []
remove k (k':m') = if k==k'
                    then m'
                    else k' : remove k m'

dom []      = []
dom (k:kvs) = key k : dom kvs