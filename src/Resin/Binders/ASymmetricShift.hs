{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds#-}

module Resin.Binders.ASymmetricShift(TRefl(..),TPath(IdPath)) where




data TRefl :: (k -> * -> * ) ->(* -> *) -> * -> *  -> * where
    Refl :: forall p t a . TRefl p t a a
    ClosedRefl :: forall p t a ix . p ix a  -> TRefl p t a a


data TPath :: (k -> * -> * ) ->(* -> *) -> * -> *  -> * where
    IdPath :: TRefl p t a a  -> TPath p t  a a
    GPath ::  {- from -} TRefl p t a a -> Integer ->  {- to -} TRefl p t b b -> TPath p t b a




    --GeneralPath ::


--data LCWithLet where

data BinderLCL = Let | Lambda

data BinderEvd :: BinderLCL -> * -> * where
  LetEv :: BinderEvd 'Let String
  LamEv :: BinderEvd 'Lambda Int
