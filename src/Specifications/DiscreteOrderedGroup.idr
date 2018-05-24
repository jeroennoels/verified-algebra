||| In a discrete ordered group, distinct elements are at least a
||| fixed `unit` distance apart.  The group is assumed to be abelian.
module Specifications.DiscreteOrderGroup

import public Specifications.OrderedGroup

%default total
%access public export

||| specification
isDiscreteOrder : Binop s -> Binrel s -> s -> s -> Type
isDiscreteOrder (+) (<=) zero unit = (x : _) ->
  Not (x = zero) -> x <= zero -> unit + x <= zero

||| composed specification
data DiscreteOrderedGroupSpec : 
       Binop s -> s -> (s -> s) -> Binrel s -> s -> Type where
  MkDiscreteOrderedGroup :
    OrderedGroupSpec add zero neg leq ->
    isAbelian add ->
    isDiscreteOrder add leq zero unit ->
    DiscreteOrderedGroupSpec add zero neg leq unit

||| forget
orderedGroup : DiscreteOrderedGroupSpec add zero neg leq _ ->
  OrderedGroupSpec add zero neg leq
orderedGroup (MkDiscreteOrderedGroup g _ _) = g

||| forget
partiallyOrderedGroup : DiscreteOrderedGroupSpec add zero neg leq _ ->
  PartiallyOrderedGroupSpec add zero neg leq
partiallyOrderedGroup spec = partiallyOrderedGroup (orderedGroup spec)

||| forget more
group : DiscreteOrderedGroupSpec add zero neg _ _ -> GroupSpec add zero neg
group spec = group (partiallyOrderedGroup spec)

||| forget
discreteOrder : DiscreteOrderedGroupSpec add zero _ leq unit ->
  isDiscreteOrder add leq zero unit
discreteOrder (MkDiscreteOrderedGroup _ _ d) = d

||| forget
totalOrder : DiscreteOrderedGroupSpec _ _ _ leq _ -> TotalOrderSpec leq
totalOrder (MkDiscreteOrderedGroup p _ _) = totalOrder p

||| forget
abelian : DiscreteOrderedGroupSpec add _ _ _ _ -> isAbelian add
abelian (MkDiscreteOrderedGroup _ a _) = a
