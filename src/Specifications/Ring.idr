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
distributativeL : PreRingSpec add mul -> isDistributativeL add mul
distributativeL (MkPreRing l _ _) = l

||| forget
distributativeR : PreRingSpec add mul -> isDistributativeR add mul
distributativeR (MkPreRing _ r _) = r

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
abelianGroup : RingSpec add zero neg _ -> AbelianGroupSpec add zero neg
abelianGroup (MkRing preRing group _) = MkAbelianGroup group (abelian preRing)

||| composed specification
data UnitalRingSpec : Binop s -> s -> (s -> s) -> Binop s -> s -> Type where
  MkUnitalRing : RingSpec add zero neg mul ->
    isNeutralL mul one ->
    isNeutralR mul one ->
    UnitalRingSpec add zero neg mul one

||| forget
ring : UnitalRingSpec add zero neg mul _ -> RingSpec add zero neg mul
ring (MkUnitalRing r _ _) = r
