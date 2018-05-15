module Specifications.OrderedRing

import public Abbrev

import public Specifications.Ring
import public Specifications.TranslationInvariance

%default total
%access public export

-- todo multiplication of positive elements
data PartiallyOrderedRingSpec : 
  Binop s -> s -> (s -> s) -> Binop s -> Rel s -> Type
  where MkPartiallyOrderedRing :
    RingSpec add zero neg mul ->
    PartiallyOrderedMagmaSpec add leq ->
    PartiallyOrderedRingSpec add zero neg mul leq

ring : PartiallyOrderedRingSpec add zero neg mul _ -> RingSpec add zero neg mul
ring (MkPartiallyOrderedRing r _) = r 
