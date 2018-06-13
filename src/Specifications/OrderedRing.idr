module Specifications.OrderedRing

import public Specifications.Ring
import public Specifications.TranslationInvariance
import public Specifications.DiscreteOrderedGroup

%default total
%access public export

||| composed specification
||| todo: multiplication of positive elements is positive
data PartiallyOrderedRingSpec :
  Binop s -> s -> (s -> s) -> Binop s -> Binrel s -> Type
  where MkPartiallyOrderedRing :
    RingSpec add zero neg mul ->
    PartiallyOrderedMagmaSpec add leq ->
    PartiallyOrderedRingSpec add zero neg mul leq

||| forget
ring : PartiallyOrderedRingSpec add zero neg mul _ -> RingSpec add zero neg mul
ring (MkPartiallyOrderedRing r _) = r

||| forget
partiallyOrderedGroup : PartiallyOrderedRingSpec add zero neg _ leq ->
  PartiallyOrderedGroupSpec add zero neg leq
partiallyOrderedGroup (MkPartiallyOrderedRing r o) =
  MkPartiallyOrderedGroup (group (abelianGroup r)) o

||| composed specification
data OrderedRingSpec :
  Binop s -> s -> (s -> s) -> Binop s -> Binrel s -> Type
  where MkOrderedRing :
    PartiallyOrderedRingSpec add zero neg mul leq ->
    isTotalOrder leq ->
    OrderedRingSpec add zero neg mul leq

namespace ForgetOrder
  ring : OrderedRingSpec add zero neg mul _ -> RingSpec add zero neg mul
  ring (MkOrderedRing r _) = ring r

||| forget
orderedGroup : OrderedRingSpec add zero neg _ leq ->
  OrderedGroupSpec add zero neg leq
orderedGroup (MkOrderedRing r t) = MkOrderedGroup (partiallyOrderedGroup r) t

||| composed specification
data DiscreteOrderedRingSpec :
  Binop s -> s -> (s -> s) -> Binop s -> Binrel s -> s -> Type
  where MkDiscreteOrderedRing :
    OrderedRingSpec add zero neg mul leq ->
    isDiscreteOrder add leq zero one ->
    isNeutralL mul one ->
    isNeutralR mul one ->
    DiscreteOrderedRingSpec add zero neg mul leq one

||| forget
discreteOrderedGroup : DiscreteOrderedRingSpec add zero neg _ leq one ->
  DiscreteOrderedGroupSpec add zero neg leq one
discreteOrderedGroup (MkDiscreteOrderedRing r d _ _) =
  MkDiscreteOrderedGroup (orderedGroup r) (abelian (abelianGroup (ring r))) d

||| forget
unitalRing : DiscreteOrderedRingSpec add zero neg mul _ one ->
  UnitalRingSpec add zero neg mul one
unitalRing (MkDiscreteOrderedRing or _ l r) = MkUnitalRing (ring or) l r
