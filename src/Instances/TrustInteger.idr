module Instances.TrustInteger

import public Data.So

import Specifications.Group
import Specifications.Ring
import Specifications.Order
import Specifications.OrderedRing
import Specifications.TranslationInvariance

%default total
%access public export

IntegerLeq : Integer -> Integer -> Type
IntegerLeq a b = So (a <= b)

postulate integerPartiallyOrderedRing :
  PartiallyOrderedRingSpec (+) 0 negate (*) IntegerLeq

integerRing : RingSpec (+) 0 negate (*)
integerRing = ring integerPartiallyOrderedRing
