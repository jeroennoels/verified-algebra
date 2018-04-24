module Instances.TrustInteger

import public Data.So

import Specifications.Group
import Specifications.Ring
import Specifications.Order
import Specifications.OrderedRing
import Specifications.TranslationInvariance

%default total
%access public export

data IntegerLeq : Integer -> Integer -> Type where
  CheckLeq : So (a <= b) -> IntegerLeq a b
  CheckNotLeq : So (not (a <= b)) -> IntegerLeq b a

postulate integerPartiallyOrderedRing : 
  PartiallyOrderedRingSpec ((+), 0, negate) (*) IntegerLeq

integerRing : RingSpec ((+), 0, negate) (*)
integerRing = ring integerPartiallyOrderedRing
