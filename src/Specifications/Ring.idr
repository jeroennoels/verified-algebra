module Specifications.Ring

import public Specifications.Group

%default total
%access public export

||| specification
isDistributativeL : Binop s -> Binop s -> Type
isDistributativeL (+) (*) = (a,x,y : _) -> a * (x + y) = a * x + a * y

||| specification
isDistributativeR : Binop s -> Binop s -> Type
isDistributativeR (+) (*) = (x,y,a : _) -> (x + y) * a = x * a + y * a

||| composed specification
data PreRingSpec : Binop s -> Binop s -> Type where
  MkPreRing : isDistributativeL add mul -> isDistributativeR add mul ->
    isAbelian add -> PreRingSpec add mul

||| forget
abelian : PreRingSpec add _ -> isAbelian add
abelian (MkPreRing _ _ a) = a

||| composed specification
data RingSpec : Binop s -> s -> (s -> s) -> Binop s -> Type where
  MkRing : PreRingSpec add mul ->
    GroupSpec add zero neg ->
    isAssociative mul ->
    RingSpec add zero neg mul

||| forget
distributativeL : RingSpec add _ _ mul -> isDistributativeL add mul
distributativeL (MkRing (MkPreRing l _ _) _ _) = l

||| forget
distributativeR : RingSpec add _ _ mul -> isDistributativeR add mul
distributativeR (MkRing (MkPreRing _ r _) _ _) = r

||| forget
abelianGroup : RingSpec add zero neg _ -> AbelianGroupSpec add zero neg
abelianGroup (MkRing preRing g _) = MkAbelianGroup g (abelian preRing)

||| forget
group : RingSpec add zero neg _ -> GroupSpec add zero neg
group (MkRing preRing g _) = g

||| composed specification
data UnitalRingSpec : Binop s -> s -> (s -> s) -> Binop s -> s -> Type where
  MkUnitalRing : RingSpec add zero neg mul ->
    isNeutralL mul one ->
    isNeutralR mul one ->
    UnitalRingSpec add zero neg mul one

||| forget
ring : UnitalRingSpec add zero neg mul _ -> RingSpec add zero neg mul
ring (MkUnitalRing r _ _) = r

||| forget
multiplicativeMonoid : UnitalRingSpec _ _ _ mul one -> MonoidSpec mul one
multiplicativeMonoid (MkUnitalRing (MkRing _ _ assoc) l r) = MkMonoid assoc l r
