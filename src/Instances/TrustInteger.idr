module Instances.TrustInteger

import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Specifications.OrderedRing
import Instances.Notation

%default total
%access public export

data IntegerLeq : Integer -> Integer -> Type where
  CheckIntegerLeq : So (intToBool (prim__slteBigInt a b)) -> IntegerLeq a b

soIntegerLeq : IntegerLeq a b -> So (intToBool (prim__slteBigInt a b))
soIntegerLeq (CheckIntegerLeq so) = so

decideLeq : (a,b : Integer) -> Dec (IntegerLeq a b)
decideLeq a b = case isItSo (intToBool (prim__slteBigInt a b)) of
  Yes oh => Yes (CheckIntegerLeq oh)
  No contra => No (contra . soIntegerLeq)


implementation AdditiveGroup Integer where
  (+) = prim__addBigInt
  Ng = prim__subBigInt 0
  Zero = 0

implementation Multiplicative Integer where
  (*) = prim__mulBigInt

implementation Unital Integer where
  One = 1

implementation Decidable [Integer, Integer] IntegerLeq where
  decide = decideLeq

postulate integerDiscreteOrderedRing :
  specifyDiscreteOrderedRing {leq = IntegerLeq}

integerDiscreteOrderedGroup : specifyDiscreteOrderedGroup {leq = IntegerLeq}
integerDiscreteOrderedGroup = discreteOrderedGroup integerDiscreteOrderedRing

integerPartiallyOrderedGroup : specifyPartiallyOrderedGroup {leq = IntegerLeq}
integerPartiallyOrderedGroup = partiallyOrderedGroup integerDiscreteOrderedGroup
