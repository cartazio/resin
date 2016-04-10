{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Resin.Binders.GShift where
--import Data.Typeable(Typeable)
import GHC.Prim(Proxy#,proxy#)
--import Numeric.Natural
import Data.Semigroupoid
import Data.Semigroupoid.Ob
import Data.Groupoid
import Data.Profunctor



type (:-|>) a b = Shift a b

infix 5 :-|>

instance Profunctor Shift where
  dimap _f _g  (Refl _p) = Composite 0 proxy# proxy#
  dimap _f _g  (Composite n _p _q) = Composite n proxy# proxy#

data Shift :: * -> * -> * where
  Refl ::  Proxy# a ->  a :-|> a
  Composite ::  !Integer -> Proxy# from -> Proxy# to -> from :-|> to

instance Ob Shift a where
  semiid = Refl proxy#

instance Groupoid Shift where
 inv (Refl p) = Refl p
 inv (Composite n pf pt) = Composite (negate n) pt pf

instance Semigroupoid Shift where
 o (Refl _p) f = f
 o g (Refl _p) = g
 o (Composite sizeG _gFromProx gtoProx)
   (Composite sizeF fFromProx _ftoProx) = Composite (sizeF+sizeG) fFromProx gtoProx
