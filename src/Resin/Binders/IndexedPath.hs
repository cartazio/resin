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
{-# LANGUAGE RankNTypes #-}

module Resin.Binders.IndexedPath(
  --Point(..)
  --,
  TPath(TRefl,IdLoopPoint)
  ,GSomeIxL(..)
  ,GSomeIxR(..)
  ,GSomeIxBoth(..)
  ,HEq1(..)
  ,HEq2(..)
  --- helpers for writing HEq1/TestEquality and Heq2 codes
  ,hoisedHeqL2
  ,hoisedHeqR2
  ,hoistedHeqPair
  ,hoistedGRelation
  ,hoistedGPredicate
  )
where

import Data.Semigroupoid
import Data.Semigroupoid.Ob
import Data.Groupoid
import Control.Category
import Data.Type.Equality
import Data.Data(Typeable)
import Unsafe.Coerce (unsafeCoerce)


--data Point :: ( k -> * ) -> k -> *  where
--    TRefl :: forall p {-t-} a . Point p {-t-} a
--    TClosedRefl :: forall p {-t-} a  . !(p a)  -> Point p {-t-}  a
--  deriving (Typeable,Data)

--hoistPointTypeEquality :: TestEquality p => (Point p a) -> (Point)

data TPath :: ( k -> * )  -> k -> k  -> * where
    TRefl :: TPath p a a
    IdLoopPoint :: !(p a)  -> TPath p  a a -- equality proof!
    GPath :: !Integer -> {- from -} !(p b)  -> {- to -} !(p a) -> TPath p {--} b a
  deriving (Typeable)

{-cat b c -> cat a b -> cat a c-}



instance Category (TPath f) where
  (.) =  o
  id  = semiid

instance Ob (TPath f ) a where
  semiid = TRefl

instance Groupoid (TPath f) where
 inv i@(IdLoopPoint _p) =  i
 inv TRefl = TRefl
 inv (GPath n pf pt) = GPath (negate n) pt pf

instance Semigroupoid (TPath f) where
  o (TRefl) f = f
  o g (TRefl) = g
  o (IdLoopPoint _pt) f = f
  o g (IdLoopPoint _pt) = g
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

--- These names aren't ideal, but ok for now
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


{-

-}
--- if i think they're equal and the indices are hidden, then the
--- indices must be phantom/irrelevant wrt the representations
---
hoisedHeqL2 :: forall (p :: k1 -> k2 -> * )  a b . Eq (GSomeIxBoth p) =>
                             GSomeIxL p a -> GSomeIxL p b ->  Maybe (a :~: b)
hoisedHeqL2 !(GSomeIxL g1) !(GSomeIxL g2) =
  case (GSomeIxBoth g1) == (GSomeIxBoth g2) of
      True -> Just $! unsafeCoerce Refl
      False -> Nothing

hoisedHeqR2 :: forall (p :: k1 -> k2 -> * )  a b . Eq (GSomeIxBoth p) =>
                              GSomeIxR p a -> GSomeIxR p b ->  Maybe (a :~: b)
hoisedHeqR2 !(GSomeIxR g1) !(GSomeIxR g2) =
  case hoistedGRelation (==) g1 g2 of
      True -> Just $! unsafeCoerce Refl
      False -> Nothing

hoistedHeqPair :: forall (p :: k1 -> k2 -> * )  a b c d . Eq (GSomeIxBoth p) =>
          p a b -> p c d -> Maybe (a :~: c , b :~: d )
hoistedHeqPair !p1 !p2 =
  case hoistedGRelation (==) p1 p2 of
    True -> Just (unsafeCoerce Refl, unsafeCoerce Refl)
    False -> Nothing

hoistedGPredicate :: forall x p. (GSomeIxBoth p -> x) -> (forall a b . p a b -> x)
hoistedGPredicate = \ f -> \ p -> f (GSomeIxBoth p)
{-# INLINE hoistedGPredicate #-}

-- | hoistedGPredicate helps with a LOT of boiler plate for building up proof
-- representatives of indexed equality
hoistedGRelation ::  forall x p. (GSomeIxBoth p  -> GSomeIxBoth p-> x) -> (forall a b c d. p a b ->  p c d -> x)
hoistedGRelation = \f -> \ p1 p2 -> f (GSomeIxBoth p1) (GSomeIxBoth p2)
{-# INLINE  hoistedGRelation  #-}

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
