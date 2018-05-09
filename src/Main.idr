module Main

import Util

import Specifications.Group
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
additiveGroup {a} = GroupSpec {s = a} (+) (fromInteger 0) negate

-- In additive terminology we can "double" an element x of a group, and
-- accompany the result with a proof of "double x - x = x"
double : Neg a => .{spec : additiveGroup {a}} ->
  (x : a) -> (y ** y + negate x = x)
double {spec} x = 
  let y = x + x
  in (y ** groupCancel3bis spec x x)

postulate integerDiscreteOrderedGroup : 
  DiscreteOrderedGroupSpec (+) 0 negate IntegerLeq 1

-- Now we actually compute something, at run time!  :^)
testDouble : Integer -> Integer
testDouble x = fst (double {spec = group integerDiscreteOrderedGroup} x)


testSeparation : Integer -> Integer -> Bool
testSeparation a b = case 
  separate {neg = negate} integerDiscreteOrderedGroup decideLeq a b of
    LeftE _ => True
    RightE _ => False
    

main : IO ()
main = do printLn (testSeparation 4 5)
          printLn (testSeparation 5 5)
          printLn (testSeparation 6 5)
