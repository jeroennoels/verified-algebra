module Instances.TrustInteger

import public Data.So
import public Abbrev
import Util
import Specifications.OrderedRing

%default total
%access public export

data IntegerLeq : Integer -> Integer -> Type where
  CheckIntegerLeq : So (intToBool (prim__slteBigInt a b)) -> IntegerLeq a b  

soIntegerLeq : IntegerLeq a b -> So (intToBool (prim__slteBigInt a b))
soIntegerLeq (CheckIntegerLeq so) = so

decideLeq : decisionProcedure IntegerLeq
decideLeq a b = case isItSo (intToBool (prim__slteBigInt a b)) of
  Yes oh => Yes (CheckIntegerLeq oh)
  No contra => No (contra . soIntegerLeq)


private
example : Type
example = PartiallyOrderedRingSpec 
            prim__addBigInt 0 (prim__subBigInt 0) prim__mulBigInt IntegerLeq
