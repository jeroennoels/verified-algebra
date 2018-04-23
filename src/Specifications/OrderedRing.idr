module Specifications.Ring

import public Abbrev

import Specifications.Ring
import Specifications.TranslationInvariance

%default total
%access public export

-- todo multiplication of positive elements
data PartiallyOrderedRingSpec : (Binop s, s, s -> s) -> Binop s -> Rel s -> Type
  where MkPartiallyOrderedRing :
    RingSpec (add, neg, zero) mul ->
    PartiallyOrderedMagmaSpec add leq ->
    PartiallyOrderedRingSpec (add, inv, zero) mul leq
