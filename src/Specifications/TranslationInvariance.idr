module Specifications.TranslationInvariance

import public Abbrev
import Specifications.Group
import Specifications.Order

%default total
%access public export

infixl 8 #

isTranslationInvariantL : Binop s -> Rel s -> Type
isTranslationInvariantL (#) (<=) = (x,y,a : _) -> x <= y -> a # x <= a # y

isTranslationInvariantR : Binop s -> Rel s -> Type
isTranslationInvariantR (#) (<=) = (x,y,a : _) -> x <= y -> x # a <= y # a

data PartiallyOrderedMagmaSpec : Binop s -> Rel s -> Type where
  MkPartiallyOrderedMagma :
    PartialOrderSpec leq ->
    isTranslationInvariantL op leq ->
    isTranslationInvariantR op leq ->
    PartiallyOrderedMagmaSpec op leq

order : PartiallyOrderedMagmaSpec _ leq -> PartialOrderSpec leq
order (MkPartiallyOrderedMagma o _ _) = o

translationInvariantL : PartiallyOrderedMagmaSpec op leq ->
  isTranslationInvariantL op leq
translationInvariantL (MkPartiallyOrderedMagma _ l _) = l

translationInvariantR : PartiallyOrderedMagmaSpec op leq ->
  isTranslationInvariantR op leq
translationInvariantR (MkPartiallyOrderedMagma _ _ r) = r


data PartiallyOrderedGroupSpec : Binop s -> s -> (s -> s) -> Rel s -> Type where
  MkPartiallyOrderedGroup :
    GroupSpec op inv e ->
    PartiallyOrderedMagmaSpec op leq ->
    PartiallyOrderedGroupSpec op inv e leq

invariantOrder : PartiallyOrderedGroupSpec op _ _ leq ->
  PartiallyOrderedMagmaSpec op leq
invariantOrder (MkPartiallyOrderedGroup _ m) = m

group : PartiallyOrderedGroupSpec op e inv _ -> GroupSpec op e inv
group (MkPartiallyOrderedGroup g _) = g


isDiscreteOrder : Binop s -> Rel s -> s -> s -> Type
isDiscreteOrder (+) (<=) zero unit = (x : _) -> 
  Not (x = zero) -> x <= zero -> unit + x <= zero

data DiscreteOrderedGroupSpec : (Binop s, s, s -> s) -> Rel s -> s -> Type
  where
  MkDiscreteOrderedGroupSpec :
    PartiallyOrderedGroupSpec add zero neg leq ->
    isAbelian add ->
    isTotalOrder leq ->
    isDiscreteOrder add leq zero unit ->
    DiscreteOrderedGroupSpec (add, zero, neg) leq unit

orderedGroup : DiscreteOrderedGroupSpec (add, zero, neg) leq _ ->
  PartiallyOrderedGroupSpec add zero neg leq
orderedGroup (MkDiscreteOrderedGroupSpec g _ _ _) = g
