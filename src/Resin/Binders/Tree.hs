{-# LANGUAGE Trustworty#-}
module Resin.Binders.Tree(
  -- | the safe subset of the api... I think
  IxEq(..)
  ,Inject(InjectRefl)
  ,Extract -- Extract is just a newtype wrapper .. for now
  ,TreeEq(..)
  ,treeElimination
  ,rightExtendInject
  ,leftExtendExtract
  ,jumpDepthInject -- not sure if this operation is safe
  ,jumpDepthExtract -- not sure if thats safe too
    )
 where
import Resin.Binders.Tree.Internal
