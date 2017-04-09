{-# LANGUAGE FlexibleContexts,FlexibleInstances,GADTs,DataKinds, PolyKinds, KindSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}

module Resin.Binders.Tree where
import Data.Kind
import Numeric.Natural
import Data.Semigroupoid
--import Data.Coerce
import Data.Type.Equality
--import qualified Data.Semigroupoid.Dual as DL


{-
This module models binders which respect scope having a tree shaped topology
or at least it models some ideas about (finite?) paths on  (finite??!) trees

-}


data IxEq :: (k -> Type ) -> k -> k   -> Type where
   PolyRefl :: forall f i .  IxEq f i i
   MonoRefl :: forall f i . f i -> IxEq f i i

--testIxEquality :: TestEquality f => IxEq f a b -> IxEq f b c ->

instance TestEquality f => TestEquality (IxEq f i) where
  testEquality (MonoRefl f1) (MonoRefl f2) = testEquality f1 f2
  testEquality (PolyRefl  )(MonoRefl _f2) = Just Refl
  testEquality (MonoRefl _f1) (PolyRefl  ) = Just Refl
  testEquality (PolyRefl ) (PolyRefl ) = Just Refl

{- | `Inject` is about

-}
data Inject :: (k -> Type ) -> k -> k -> Type where
  InjectRefl :: forall f a b . IxEq f a b->  Inject f a b
  --MonoId :: forall f  i .  (f i) -> Inject f i i
  -- should MonoId be strict in its argument?
  CompactCompose :: forall f i j e. (IxEq f i e) -> (IxEq f  e j  )  -> Natural -> Inject f i j
   -- i is origin/root
   -- j is leaf
  -- compact compose is unsafe for users, but should be exposed in a .Internal
  -- module



instance Semigroupoid (Inject f) where
   --PolyId `o`  PolyId =  PolyId
   (InjectRefl (MonoRefl _p)) `o` (!f) = f
   (InjectRefl (PolyRefl)) `o`  (!f) = f
--
   cc@(CompactCompose _ _ _) `o` (InjectRefl  (MonoRefl)) = cc
   (CompactCompose _cmiddle2 cout sizeleft)
    `o` (CompactCompose cin _cmiddle1 sizeright) = CompactCompose cin cout (sizeright + sizeleft)
      --- TODO is this case to lazy?

-- extract is the dual of Inject
-- aka Data.Semigroupoid.Dual is nearly the exact same type :)
newtype Extract :: (k -> Type ) -> k -> k -> Type where
  Dual :: ((Inject f) b a ) -> Extract f a b
-- not sure if this is the right design vs
  -- :: Inject f b a -> Extract f a b  --- (which has more explicit duality and less newtypery)


instance Semigroupoid (Extract f) where
  o = \ (Dual l)  (Dual r) -> Dual  $  r `o` l


data TreeEq :: (k -> Type ) -> k -> k -> Type where
  TreeInject :: Inject f a b -> TreeEq f a b
  TreeExtract :: Extract f a b -> TreeEq f a b
  TreeRefl :: TreeEq f c c


--- this might limit a,c to being kind (or sort?) * / Type for now, but thats OK ??
treeElimination :: TestEquality f => Inject f a b -> Extract f b c -> {- Maybe Wrapped? -} Maybe (TreeEq f a c)
treeElimination (InjectRefl fa) (Dual  (InjectRefl fb)) =
             case testEquality fa fb of
              -- VARIABLE EQUALITY, are they the same?
              Just Refl -> Just TreeRefl
              Nothing -> Nothing -- THIS SHOULDN"T BE

treeElimination (CompactCompose fa fb1 n1) (Dual (CompactCompose fc fb2 n2)) =
    case testEquality fb1 fb2 of  -- this may be needless
        Nothing -> error "defensive programming explosion of sadness"
        Just Refl -> case (compare n1 n2, max n1 n2 - min n1 n2) of
                        (EQ, _ )-> case _wat fa fc of
                                      Nothing -> Nothing
                                      Just Refl -> Just TreeRefl
                        (GT, m )-> Just $ TreeInject (CompactCompose fa fc  m)
                        (LT, m ) -> Just $ TreeExtract (Dual (CompactCompose fc fa m))
--treeElimination   p@PolyId (Dual (CompactCompose fc fb n))
--        | n == 0 = case testEquality fb fc of
--                      Nothing -> Nothing
--                      Just Refl -> Just TreeRefl
--        | otherwise = Just $ TreeExtract (Dual (CompactCompose fc p n ))
treeElimination   f@(InjectRefl fa) d@(Dual (CompactCompose _ _ _))  =
      treeElimination (CompactCompose fa fa 0) d
treeElimination   c@(CompactCompose _ _ _) (Dual fd@(InjectRefl fc)) =
      treeElimination c (Dual (CompactCompose fc fc 0))

-- FINISH the rest of the cases



{-
is extract literally the same datastructure just with a fresh name?

-}
