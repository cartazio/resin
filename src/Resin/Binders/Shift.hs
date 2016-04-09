{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Resin.Binders.Shift where
import Data.Typeable(Typeable)
import GHC.Prim(Proxy#,proxy#)
import Numeric.Natural
import Data.Semigroupoid
import Data.Semigroupoid.Ob

data Shift :: * -> * -> * where
  Refl :: Typeable a =>  Proxy# a -> Shift a a
  Composite :: (Typeable from,Typeable to ) => !Natural -> Proxy# from -> Proxy# to -> Shift from to

{-
The Semigroupoid instance of Shift should have a CPP DEBUG mode
that checks if the tyepables are actually equal

Note: if make the size parameter Integer instead of Natural,
I can trivially define the right notion of Groupoid and thus
get a very very 'natural' inverse operator, though
not sure yet if its a useful idea.
It may wind up being helpful when working with explicit substitutions/contexts
but I'm not sure yet.
 -}

instance Semigroupoid Shift where
 o (Refl _p) f = f
 o g (Refl _p) = g
 o (Composite sizeG _gFromProx gtoProx)
   (Composite sizeF fFromProx _ftoProx) = Composite (sizeF+sizeG) fFromProx gtoProx

instance Typeable a => Ob Shift a where
  semiid = Refl proxy#

