{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DefaultSignatures #-}

module Resin.Binders.IndexedPath(
  Point(..)
  ,TPath(IdPath)
  ,GSomeIxL(..)
  ,GSomeIxR(..)
  ,GSomeIxBoth(..)
  ,HEq1(..)
  ,HEq2(..)
  ,hoisedHeqL2
  ,hoisedHeqR2
  )
where

import Data.Semigroupoid
import Data.Semigroupoid.Ob
import Data.Groupoid
import Control.Category
import Data.Type.Equality
import Data.Data(Data,Typeable)
import Unsafe.Coerce (unsafeCoerce)


data Point :: ( * -> * ) -> * -> *  where
    TRefl :: forall p {-t-} a . Point p {-t-} a
    TClosedRefl :: forall p {-t-} a  . !(p a)  -> Point p {-t-}  a
  deriving (Typeable,Data)



data TPath :: ( * -> * )  -> * -> *  -> * where
    IdPath :: Point p a  -> TPath p  a a -- equality proof!
    GPath :: Integer -> {- from -} Point p b  -> {- to -} Point p a -> TPath p {--} b a

{-cat b c -> cat a b -> cat a c-}

instance Category (TPath f) where
  (.) =  o
  id  = semiid

instance Ob (TPath f ) a where
  semiid = IdPath TRefl

instance Groupoid (TPath f) where
 inv i@(IdPath _p) =  i
 inv (GPath n pf pt) = GPath (negate n) pt pf

instance Semigroupoid (TPath f) where
  o (IdPath _pt) f = f
  o g (IdPath _pt) = g
  o (GPath sizeG _gFromPt gtoPt)
    (GPath sizeF fFromPt _ftoPt) = GPath (sizeF+sizeG) fFromPt gtoPt

    --GeneralPath ::


--data LCWithLet where

{-
example binders

-}

-- | GSomeIxL existentially hides the left index of a bindexed type
data GSomeIxL :: (k1 ->  k2 -> *) -> k2 -> * where
  GSomeIxL :: forall p a b . !(p a b) -> GSomeIxL p b

data GSomeIxR :: (k1 ->  k2 -> *) -> k1 -> * where
  GSomeIxR :: forall p a b . !(p a b) -> GSomeIxR p a

data GSomeIxBoth ::  (k1 ->  k2 -> *)  -> * where
  GSomeIxBoth :: forall p a b . !(p a b) -> GSomeIxBoth p


class TestEquality f => HEq1 (f :: k -> *) where
  testHEq1 :: forall (a :: k) (b :: k) . f a -> f b -> Maybe (a :~: b)
  default testHEq1 ::  forall (a :: k) (b :: k) . f a -> f b -> Maybe (a :~: b)
  testHEq1 = testEquality
  {-# MINIMAL testHEq1 #-}

instance TestEquality f => HEq1 (f :: k -> *) where
  testHEq1 = testEquality

class HEq2 ( f :: k1 -> k2 -> *) where
  testHEq2 :: forall (a :: k1) (b :: k1)  (c :: k2) (d :: k2).
                  f a c -> f b d -> Maybe ((a :~: b),(c :~: d))
  {-# MINIMAL testHEq2 #-}

hoisedHeqL2 :: Eq (GSomeIxBoth p) => GSomeIxL p a -> GSomeIxL p b ->  Maybe (a :~: b)
hoisedHeqL2 !(GSomeIxL g1) !(GSomeIxL g2) = case (GSomeIxBoth g1) == (GSomeIxBoth g2) of
      True -> Just $! unsafeCoerce Refl
      False -> Nothing

hoisedHeqR2 :: Eq (GSomeIxBoth p) => GSomeIxR p a -> GSomeIxR p b ->  Maybe (a :~: b)
hoisedHeqR2 !(GSomeIxR g1) !(GSomeIxR g2) = case (GSomeIxBoth g1) == (GSomeIxBoth g2) of
      True -> Just $! unsafeCoerce Refl
      False -> Nothing

data BinderLCL = Let | Lambda

data BinderEvd :: BinderLCL -> * -> * where
  LetEv :: BinderEvd 'Let String
  LamEv :: BinderEvd 'Lambda Int

data SomeBinderEvd :: * where
  SomeEvd :: !(BinderEvd bl a) -> SomeBinderEvd

instance Eq (SomeBinderEvd) where
  (SomeEvd LetEv) == (SomeEvd LetEv) = True
  (SomeEvd LetEv) == (SomeEvd _ )    = False
  (SomeEvd LamEv) == (SomeEvd LamEv) = True
  (SomeEvd LamEv) == (SomeEvd _ ) = False

{-
the idea with this example is that we dont care *which*
binder variety we were at, just the representation of its variables
-}
