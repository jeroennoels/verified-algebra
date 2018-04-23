module Specifications.Ring

import public Abbrev

import Specifications.Ring
import Specifications.TranslationInvariance

%default total
%access public export


data PartiallyOrderedRingSpec : (Binop s, s, s -> s) -> Binop s -> Rel s -> Type
  where MkPartiallyOrderedRing :
    RingSpec (op, inv, e) mul ->
    PartiallyOrderedMagmaSpec op leq ->
    PartiallyOrderedRingSpec (op, inv, e) mul leq

