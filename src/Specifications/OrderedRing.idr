module Specifications.OrderedRing

import public Specifications.Ring
import public Specifications.TranslationInvariance

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
