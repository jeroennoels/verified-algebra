module Specifications.DiscreteOrderGroup

import public Abbrev
import Specifications.Group
import Specifications.Order
import Specifications.TranslationInvariance

%default total
%access public export

isDiscreteOrder : Binop s -> Rel s -> s -> s -> Type
isDiscreteOrder (+) (<=) zero unit = (x : _) ->
  Not (x = zero) -> x <= zero -> unit + x <= zero


data DiscreteOrderedGroupSpec : Binop s -> s -> (s -> s) -> Rel s -> s -> Type
  where
  MkDiscreteOrderedGroupSpec :
    PartiallyOrderedGroupSpec add zero neg leq ->
    isAbelian add ->
    isTotalOrder leq ->
    isDiscreteOrder add leq zero unit ->
    DiscreteOrderedGroupSpec add zero neg leq unit


orderedGroup : DiscreteOrderedGroupSpec add zero neg leq _ ->
  PartiallyOrderedGroupSpec add zero neg leq
orderedGroup (MkDiscreteOrderedGroupSpec g _ _ _) = g

discreteOrder : DiscreteOrderedGroupSpec add zero _ leq unit ->
  isDiscreteOrder add leq zero unit
discreteOrder (MkDiscreteOrderedGroupSpec _ _ _ d) = d

totalOrder : DiscreteOrderedGroupSpec _ _ _ leq _ -> TotalOrderSpec leq
totalOrder (MkDiscreteOrderedGroupSpec p _ t _) =
  MkTotalOrder (order (invariantOrder p)) t
