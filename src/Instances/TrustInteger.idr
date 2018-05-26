module Instances.TrustInteger

import public Data.So
import public Data.Vect
import public Data.Rel
import public Decidable.Decidable
import public Common.Abbrev
import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
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

implementation Unital Integer where
  One = 1

implementation Decidable [Integer, Integer] IntegerLeq where
  decide = decideLeq

postulate integerDiscreteOrderedGroup : 
  specifyDiscreteOrderedGroup {leq = IntegerLeq}
