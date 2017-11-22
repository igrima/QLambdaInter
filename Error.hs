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
module Error
  ( Error(..), Exception(..), success, value, addErrors, fromSuccess, isError )
 where

data Error a = FatalError String | Error String | Success a 
               deriving (Eq, Show, Read)

instance Functor Error where
   fmap f (Success a)    = Success (f a)
   fmap _ (Error e)      = Error e
   fmap _ (FatalError e) = FatalError e

instance Applicative Error where
   pure = Success
   (Success f)    <*> mx   = fmap f mx
   (Error e)      <*> _   = Error e
   (FatalError e) <*> _   = FatalError e

instance Monad Error where 
   (Success x)    >>= k   = k x
   (Error e)      >>= _   = Error e
   (FatalError e) >>= _   = FatalError e
   return                 = Success
   fail s                 = FatalError s

--instance MonadPlus Error where
mzero                     = Error ""
(FatalError e) `mplus` _  = FatalError e
(Error _)      `mplus` ys = ys
xs             `mplus` _  = xs

class Monad e => Exception e where
    raise :: String -> e a
    failingWithMsg :: e a -> String -> e a

instance Exception Error where
    raise msg = Error msg
    failingWithMsg (Error _) msg = Error msg
    failingWithMsg e         _   = e

isError (Error _) = True
isError _         = False
   
success :: Error a -> (String -> b) -> (a -> b) -> b
success (FatalError e) _   _ = error e
success (Error e)      err _ = err e
success (Success a)    _   f = f a

fromSuccess :: Error a -> (a -> b) -> b
fromSuccess e f = success e (\_->error "Error") f

value e = success e error id

addErrors (Error msg)        (Error msg1) = Error (msg ++ " or " ++ msg1)
addErrors (Error msg)         _           = Error msg
addErrors emsg@(FatalError _) _           = emsg
addErrors (Success _)         emsg        = emsg
