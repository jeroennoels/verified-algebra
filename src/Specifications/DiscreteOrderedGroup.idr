module Specifications.DiscreteOrderGroup

import public Abbrev
import Specifications.Group
import Specifications.Order
import Specifications.TranslationInvariance
import Specifications.OrderedGroup

%default total
%access public export

isDiscreteOrder : Binop s -> Rel s -> s -> s -> Type
isDiscreteOrder (+) (<=) zero unit = (x : _) ->
  Not (x = zero) -> x <= zero -> unit + x <= zero


data DiscreteOrderedGroupSpec : Binop s -> s -> (s -> s) -> Rel s -> s -> Type
  where
  MkDiscreteOrderedGroup :
    OrderedGroupSpec add zero neg leq ->
    isAbelian add ->
    isDiscreteOrder add leq zero unit ->
    DiscreteOrderedGroupSpec add zero neg leq unit


orderedGroup : DiscreteOrderedGroupSpec add zero neg leq _ ->
  OrderedGroupSpec add zero neg leq
orderedGroup (MkDiscreteOrderedGroup g _ _) = g

partiallyOrderedGroup : DiscreteOrderedGroupSpec add zero neg leq _ ->
  PartiallyOrderedGroupSpec add zero neg leq
partiallyOrderedGroup spec = partiallyOrderedGroup (orderedGroup spec)

group : DiscreteOrderedGroupSpec add zero neg _ _ -> GroupSpec add zero neg
group spec = group (partiallyOrderedGroup spec)


discreteOrder : DiscreteOrderedGroupSpec add zero _ leq unit ->
  isDiscreteOrder add leq zero unit
discreteOrder (MkDiscreteOrderedGroup _ _ d) = d

totalOrder : DiscreteOrderedGroupSpec _ _ _ leq _ -> TotalOrderSpec leq
totalOrder (MkDiscreteOrderedGroup p _ _) = totalOrder p