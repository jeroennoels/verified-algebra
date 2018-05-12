module Main

import Util

import Specifications.Group
import Specifications.Order
import Specifications.TranslationInvariance
import Specifications.DiscreteOrderedGroup

import Proofs.GroupCancelationLemmas
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory
import Proofs.Interval
import Proofs.DiscreteOrderTheory

import Instances.TrustInteger
import Instances.ZZ

import Applications.Example

-- Here we bring in the Neg interface to get a succint additive
-- notation for groups
additiveGroup : Neg a => Type
additiveGroup {a} = GroupSpec {s = a} (+) 0 negate

-- In additive terminology we can "double" an element x of a group, and
-- accompany the result with a proof of "double x - x = x"
double : Neg a => .{spec : additiveGroup {a}} ->
  (x : a) -> (y ** y + negate x = x)
double {spec} x = 
  let y = x + x
  in (y ** groupCancel3bis spec x x)


additiveDiscreteOrderedGroup : Neg a => Rel a -> Type
additiveDiscreteOrderedGroup leq = DiscreteOrderedGroupSpec (+) 0 negate leq 1

postulate integerDiscreteOrderedGroup : additiveDiscreteOrderedGroup IntegerLeq
 -- DiscreteOrderedGroupSpec (+) 0 (prim__subBigInt 0) IntegerLeq 1


-- Now we actually compute something, at run time!  :^)
testDouble : Integer -> Integer
testDouble x = fst (double {spec = group integerDiscreteOrderedGroup} x)


testSeparation : Integer -> Integer -> Bool
testSeparation a b = case 
  separate integerDiscreteOrderedGroup decideLeq a b of
    EraseL _ => True
    EraseR _ => False

showEE : EitherErased a b -> String
showEE (EraseL _) = "left"
showEE _ = "right"

testPivot : Integer -> Integer -> Integer -> Integer -> String
testPivot p a b x = 
  case decideBetween {leq = IntegerLeq} decideLeq x a b of
    Yes axb => showEE $ 
      pivot integerDiscreteOrderedGroup decideLeq p x axb
    No _ => "error"
  

main : IO ()
main = do printLn (testPivot 5 1 9 3)

