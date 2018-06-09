module Specifications.Order

import public Common.Abbrev

%default total
%access public export

||| specification
isReflexive : Binrel s -> Type
isReflexive rel = (x : _) -> rel x x

||| specification
isTransitive : Binrel s -> Type
isTransitive rel = (x,y,z : _) -> rel x y -> rel y z -> rel x z

||| specification
isAntisymmetric : Binrel s -> Type
isAntisymmetric rel = (x,y : _) -> rel x y -> rel y x -> x = y

||| composed specification
data PartialOrderSpec : Binrel s -> Type where
  MkPartialOrder : isReflexive rel -> isTransitive rel -> isAntisymmetric rel ->
    PartialOrderSpec rel

||| forget
reflexive : PartialOrderSpec rel -> isReflexive rel
reflexive (MkPartialOrder r _ _) = r

||| forget
transitive : PartialOrderSpec rel -> isTransitive rel
transitive (MkPartialOrder _ t _) = t

||| forget
antisymmetric : PartialOrderSpec rel -> isAntisymmetric rel
antisymmetric (MkPartialOrder _ _ a) = a

||| specification
isTotalOrder : Binrel s -> Type
isTotalOrder rel = (x,y : _) -> Either (rel x y) (rel y x)

||| composed specification
data TotalOrderSpec : Binrel s -> Type where
  MkTotalOrder : PartialOrderSpec rel -> isTotalOrder rel -> TotalOrderSpec rel

||| forget
partialOrder : TotalOrderSpec rel -> PartialOrderSpec rel
partialOrder (MkTotalOrder p _) = p

||| forget
totalOrder : TotalOrderSpec rel -> isTotalOrder rel
totalOrder (MkTotalOrder _ t) = t


||| A proof that `x` is between `a` and `b` relative to a certain
||| order relation.
data Between : Binrel s -> (s,s) -> s -> Type where
  MkBetween : rel a x -> rel x b -> Between rel (a,b) x

||| about the left side of the interval
betweenL : Between rel (a,b) x -> rel a x
betweenL (MkBetween l _) = l

||| about the right side of the interval
betweenR : Between rel (a,b) x -> rel x b
betweenR (MkBetween _ r) = r
