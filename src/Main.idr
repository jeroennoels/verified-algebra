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


testDouble : Integer -> Integer
testDouble x = fst (double {spec = group integerDiscreteOrderedGroup} x)

testSeparation : Integer -> Integer -> String
testSeparation a b = show $ separate integerDiscreteOrderedGroup decideLeq a b


pivot : (x : Integer) -> .Between IntegerLeq x (a,b) -> 
  Integer -> String
pivot x axb p = show $ 
  decidePivot integerDiscreteOrderedGroup decideLeq p x axb 

partition3 : (x : Integer) -> .Between IntegerLeq x (a,b) -> 
  Integer -> Integer -> String
partition3 x axb p q = show $ 
  decidePartition3 integerDiscreteOrderedGroup decideLeq p q x axb 

test : Integer -> Integer -> Integer -> Integer -> Integer -> String
test a p q b x = 
  case decideBetween {leq = IntegerLeq} decideLeq x a b of
    Yes axb => partition3 x axb p q
    No _ => "Error"
  
main : IO ()
main = printLn $ map (test 0 3 7 10) [(-1)..11]
