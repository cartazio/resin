{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Resin.Binders.SymmetricShift(
  type (:-|>)
  -- ^ alias for Shift type
  ,Shift(Refl)
  -- ^ @Refl@ is safe to export
  ) where
--import Data.Typeable(Typeable)
import GHC.Prim(Proxy#,proxy#)
--import Numeric.Natural
import Data.Semigroupoid
import Data.Semigroupoid.Ob
import Data.Groupoid
import Control.Category
import Numeric.Natural

type (:-|>) a b = Shift a b

infix 5 :-|>

data StrictMaybePair a b = NoPair | SMPair !a !b
  deriving(Eq,Ord,Read,Show)

data Shift :: (* -> * )-> * -> * -> * where
--- the idea for this one is that roughly,
--- every shift has count to the left, Refl, some count to the right
--- all we need is the left most tag, count, tag to left of Refl, Refl,
--- tag to right of Refl, count, then rightmost tag
---
      Refl :: Proxy#  a {-t a-} ->  Shift t a a
      Composite :: !(StrictMaybePair (t c) Natural) -> Shift t b b -> Natural -> t a -> Shift t c a
