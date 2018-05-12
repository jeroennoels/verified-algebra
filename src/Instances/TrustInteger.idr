module Instances.TrustInteger

import public Data.So
import public Abbrev
import Util
import Specifications.OrderedRing

%default total
%access public export

IntegerLeq : Integer -> Integer -> Type
IntegerLeq a b = So (intToBool (prim__slteBigInt a b))

decideLeq : decisionProcedure IntegerLeq
decideLeq a b = isItSo (intToBool (prim__slteBigInt a b))

private
example : Type
example = PartiallyOrderedRingSpec 
            prim__addBigInt 0 (prim__subBigInt 0) prim__mulBigInt IntegerLeq
