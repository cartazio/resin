{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Resin.Binders.GShift(
  type (:-|>)
  ,Shift(Refl) -- | @Refl@ is safe to export
  ) where
--import Data.Typeable(Typeable)
import GHC.Prim(Proxy#,proxy#)
--import Numeric.Natural
import Data.Semigroupoid
import Data.Semigroupoid.Ob
import Data.Groupoid
import Control.Category


type (:-|>) a b = Shift a b

infix 5 :-|>


data Shift :: * -> * -> * where
  Refl ::  !(Proxy# a) ->  a :-|> a
  Composite ::  !Integer -> !(Proxy# from) -> !(Proxy# to) -> from :-|> to

instance Category Shift where
  (.) =  o
  id  = semiid

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
