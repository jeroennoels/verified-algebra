module Applications.Example

import public Data.So
import public Decidable.Decidable

import Util
import Specifications.Order
import Specifications.TranslationInvariance
import Specifications.OrderedGroup
import Proofs.OrderTheory
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory
import Instances.TrustInteger

%default total
%access public export

orderedGroupSpec : Neg s => Rel s -> Type
orderedGroupSpec {s} leq = OrderedGroupSpec {s} (+) 0 negate leq

absoluteValue : Neg s => (leq : Rel s) -> (decide : decisionProcedure leq) ->
  orderedGroupSpec {s} leq -> s -> (a ** leq 0 a)
absoluteValue {s} leq decide spec a =
  case decide a 0 of
    Yes prf => (negate a ** invertNegative (partiallyOrderedGroup spec) a prf)
    No contra => let (positive, _) = orderContra (totalOrder spec) a 0 contra 
                 in (a ** positive)

postulate integerOrderedGroup : OrderedGroupSpec (+) 0 negate IntegerLeq

test : Integer -> Integer
test x = fst $ absoluteValue IntegerLeq decideLeq integerOrderedGroup x
