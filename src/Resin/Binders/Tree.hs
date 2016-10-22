{-# LANGUAGE FlexibleContexts,FlexibleInstances,GADTs,DataKinds, PolyKinds, KindSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

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


data Inject :: (k -> Type ) -> k -> k -> Type where
  PolyId :: forall f a . Inject f a a
  MonoId :: forall f  i .  (f i) -> Inject f i i
  CompactCompose :: forall f i j . (f i) -> (f j)  -> Natural -> Inject f i j  -- i is origin/root j is leaf
  -- compact compose is unsafe for users, but should be exposed in a .Internal
  -- module

instance Semigroupoid (Inject f) where
   --PolyId `o`  PolyId =  PolyId
   PolyId `o` (!f) = f
   (MonoId _g) `o` (!f) = f
   cc@(CompactCompose _ _ _) `o` (MonoId _) = cc
   cc@(CompactCompose _ _ _) `o` PolyId = cc
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
treeElimination (MonoId fa) (Dual  (MonoId fb)) = case testEquality fa fb of
                                                          Just Refl -> Just TreeRefl
                                                          Nothing -> Nothing
treeElimination   PolyId (Dual PolyId)                      = Just TreeRefl
treeElimination   (MonoId _fa) (Dual PolyId)                = Just TreeRefl
treeElimination   PolyId (Dual (MonoId _fc))                = Just TreeRefl
treeElimination   PolyId (Dual (CompactCompose _ _ _))      = error "finish tree elim"
treeElimination   (MonoId _) (Dual (CompactCompose _ _ _))  = error "finish tree elim"
treeElimination   (CompactCompose _ _ _) (Dual (MonoId _)) = error "finish tree elim"
treeElimination   (CompactCompose _ _ _) (Dual (CompactCompose _ _ _)) = error "finish tree elim"
treeElimination   (CompactCompose _ _ _) (Dual PolyId) = error "finish tree elimi "
-- FINISH the rest of the cases



{-
is extract literally the same datastructure just with a fresh name?

-}
