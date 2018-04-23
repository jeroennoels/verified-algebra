module TrustInteger

import public Data.So

import Specifications.Group
import Specifications.Order
import Specifications.TranslationInvariance
import Specifications.Ring
import Specifications.OrderedRing

import Proofs.GroupCancelationLemmas
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory

%default total
%access public export

data IntegerLeq : Integer -> Integer -> Type where
  CheckLeq : So (a <= b) -> IntegerLeq a b
  CheckNotLeq : So (not (a <= b)) -> IntegerLeq b a

postulate integerPartiallyOrderedRing : 
  PartiallyOrderedRingSpec ((+), 0, negate) (*) IntegerLeq

integerRing : RingSpec ((+), 0, negate) (*)
integerRing = ring integerPartiallyOrderedRing
