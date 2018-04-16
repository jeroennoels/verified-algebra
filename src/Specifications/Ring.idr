module Specifications.Ring

import public Abbrev
import Specifications.Semigroup
import Specifications.Monoid
import Specifications.Group

%default total
%access export

public export
isDistributativeL : Binop s -> Binop s -> Type
isDistributativeL (+) (*) = (a,x,y : _) -> a * (x + y) = a * x + a * y

public export
isDistributativeR : Binop s -> Binop s -> Type
isDistributativeR (+) (*) = (a,x,y : _) -> (x + y) * a = x * a + y * a

data PreRingSpec : Binop s -> Binop s -> Type where
  MkPreRing : isDistributativeL add mul -> isDistributativeR add mul ->
    isAbelian add -> PreRingSpec add mul

distributativeL : PreRingSpec add mul -> isDistributativeL add mul
distributativeL (MkPreRing l _ _) = l

distributativeR : PreRingSpec add mul -> isDistributativeR add mul
distributativeR (MkPreRing _ r _) = r

abelian : PreRingSpec add _ -> isAbelian add
abelian (MkPreRing _ _ a) = a


data RingSpec : (Binop s, s, s -> s) -> Binop s -> Type where
  MkRing : PreRingSpec add mul ->
    GroupSpec add zero neg ->
    isAssociative mul ->
    RingSpec (add, zero, neg) mul

additiveGroup : RingSpec (add, zero, neg) _ -> AbelianGroupSpec add zero neg
additiveGroup (MkRing preRing group _) = MkAbelianGroup group (abelian preRing)


data UnitalRingSpec : (Binop s, s, s -> s) -> (Binop s, s) -> Type where
  MkUnitalRing : RingSpec additive mul ->
    isNeutralL mul one -> isNeutralR mul one ->
    UnitalRingSpec additive (mul, one)
