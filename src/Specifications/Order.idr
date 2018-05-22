module Specifications.Order

import public Common.Abbrev

%default total
%access public export

isReflexive : Binrel s -> Type
isReflexive rel = (x : _) -> rel x x

isTransitive : Binrel s -> Type
isTransitive rel = (x,y,z : _) -> rel x y -> rel y z -> rel x z

isAntisymmetric : Binrel s -> Type
isAntisymmetric rel = (x,y : _) -> rel x y -> rel y x -> x = y

data PartialOrderSpec : Binrel s -> Type where
  MkPartialOrder : isReflexive rel -> isTransitive rel -> isAntisymmetric rel ->
    PartialOrderSpec rel

reflexive : PartialOrderSpec rel -> isReflexive rel
reflexive (MkPartialOrder r _ _) = r

transitive : PartialOrderSpec rel -> isTransitive rel
transitive (MkPartialOrder _ t _) = t

antisymmetric : PartialOrderSpec rel -> isAntisymmetric rel
antisymmetric (MkPartialOrder _ _ a) = a

isTotalOrder : Binrel s -> Type
isTotalOrder rel = (x,y : _) -> Either (rel x y) (rel y x)


data TotalOrderSpec : Binrel s -> Type where
  MkTotalOrder : PartialOrderSpec rel -> isTotalOrder rel -> TotalOrderSpec rel

partialOrder : TotalOrderSpec rel -> PartialOrderSpec rel
partialOrder (MkTotalOrder p _) = p

totalOrder : TotalOrderSpec rel -> isTotalOrder rel
totalOrder (MkTotalOrder _ t) = t


data Between : Binrel s -> s -> (s,s) -> Type where
  MkBetween : rel a x -> rel x b -> Between rel x (a,b)

betweenL : Between rel x (a,b) -> rel a x
betweenL (MkBetween l _) = l

betweenR : Between rel x (a,b) -> rel x b
betweenR (MkBetween _ r) = r

