module Applications.Example

import public Data.So
import public Decidable.Decidable

import Util
import Specifications.OrderedGroup
import Proofs.OrderTheory
import Proofs.GroupTheory
import Proofs.GroupCancelationLemmas
import Proofs.TranslationInvarianceTheory
import Instances.TrustInteger

%default total
%access public export

-- An experiment of using the Neg interface to get a succint additive
-- notation for groups

orderedGroupSpec : Neg s => Rel s -> Type
orderedGroupSpec {s} leq = OrderedGroupSpec {s} (+) 0 negate leq

absoluteValue : Neg s => (leq : Rel s) -> (decide : decisionProcedure leq) ->
  .orderedGroupSpec {s} leq -> s -> (a ** leq 0 a)
absoluteValue {s} leq decide spec a =
  case decide a 0 of
    Yes prf => (negate a ** invertNegative (partiallyOrderedGroup spec) a prf)
    No contra => let (positive, _) = orderContra (totalOrder spec) a 0 contra 
                 in (a ** positive)

postulate integerOrderedGroup : OrderedGroupSpec (+) 0 negate IntegerLeq

testAbsoluteValue : Integer -> Integer
testAbsoluteValue x = fst $
  absoluteValue IntegerLeq decideLeq integerOrderedGroup x


additiveGroup : Neg a => Type
additiveGroup {a} = GroupSpec {s = a} (+) 0 negate


-- In additive terminology we can "double" an element x of a group, and
-- accompany the result with a proof of "double x - x = x"

double : Neg a => .{spec : additiveGroup {a}} ->
  (x : a) -> (y ** y + negate x = x)
double {spec} x = 
  let y = x + x
  in (y ** groupCancel3bis spec x x)

testDouble : Integer -> Integer
testDouble x = fst $ double {spec} x 
  where spec = group (partiallyOrderedGroup integerOrderedGroup)
