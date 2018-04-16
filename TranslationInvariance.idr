module TranslationInvariance

import public Abbrev
import Group
import Order

%default total
%access export

infixl 8 #

public export
isTranslationInvariantL : Binop s -> Rel s -> Type
isTranslationInvariantL (#) (<=) = (x,y,a : _) -> x <= y -> a # x <= a # y

public export
isTranslationInvariantR : Binop s -> Rel s -> Type
isTranslationInvariantR (#) (<=) = (x,y,a : _) -> x <= y -> x # a <= y # a

public export
data PartiallyOrderedGroupSpec : Binop s -> s -> (s -> s) -> Rel s -> Type where
  MkPartiallyOrderedGroup : 
    GroupSpec op e inv -> 
    PartialOrderSpec leq ->
    isTranslationInvariantL op leq ->
    isTranslationInvariantR op leq ->
    PartiallyOrderedGroupSpec op e inv leq

group : PartiallyOrderedGroupSpec op e inv _ -> GroupSpec op e inv
group (MkPartiallyOrderedGroup g _ _ _) = g

order : PartiallyOrderedGroupSpec _ _ _ leq -> PartialOrderSpec leq
order (MkPartiallyOrderedGroup _ o _ _) = o

translationInvariantL : PartiallyOrderedGroupSpec op _ _ leq -> 
  isTranslationInvariantL op leq
translationInvariantL (MkPartiallyOrderedGroup _ _ l _) = l

translationInvariantR : PartiallyOrderedGroupSpec op _ _ leq -> 
  isTranslationInvariantR op leq
translationInvariantR (MkPartiallyOrderedGroup _ _ _ r) = r
