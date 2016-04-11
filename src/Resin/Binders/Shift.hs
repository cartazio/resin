{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Resin.Binders.Shift(
  type (:-|>)
  ,Shift(Refl) -- | @Refl@ is safe to export

  )  where
import Data.Typeable(Typeable)
import GHC.Prim(Proxy#,proxy#)
import Data.Semigroupoid
import Data.Semigroupoid.Ob
import Data.Groupoid

type (:-|>) a b = Shift a b

infix 5 :-|>

data Shift :: * -> * -> * where
  Refl :: Typeable a =>  Proxy# a ->  a :-|> a
  Composite :: (Typeable from,Typeable to ) => !Integer -> Proxy# from -> Proxy# to -> from :-|> to
  deriving(Typeable)
{-
The Semigroupoid instance of Shift should have a CPP DEBUG mode
that checks if the tyepables are actually equal

Note: if make the size parameter Integer instead of Natural,
I can trivially define the right notion of Groupoid and thus
get a very very 'natural' inverse operator, though
not sure yet if its a useful idea.
It may wind up being helpful when working with explicit substitutions/contexts
but I'm not sure yet.

likewise, the typeables may only matter for debugging purposes, if at all


When the 'Shift' datatype is used to represent info in a "TreeShift"
constructor of a Monadic AST, we want to enforce that we can't build an
AST that has sequence (TreeShift (TreeShift ..))
 -}

instance Groupoid Shift where
 inv (Refl p) = Refl p
 inv (Composite n pf pt) = Composite (negate n) pt pf


instance Semigroupoid Shift where
 o (Refl _p) f = f
 o g (Refl _p) = g
 o (Composite sizeG _gFromProx gtoProx)
   (Composite sizeF fFromProx _ftoProx) = Composite (sizeF+sizeG) fFromProx gtoProx

instance Typeable a => Ob Shift a where
  semiid = Refl proxy#

