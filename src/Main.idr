module Main

import Util
import Specifications.DiscreteOrderedGroup

import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory
import Proofs.DiscreteOrderTheory
import Proofs.Interval

import Instances.TrustInteger
import Instances.ZZ

import Applications.Example

integerDiscreteOrderedGroupSpec : Type
integerDiscreteOrderedGroupSpec = DiscreteOrderedGroupSpec
  prim__addBigInt 0 (prim__subBigInt 0) IntegerLeq 1

postulate integerDiscreteOrderedGroup : Main.integerDiscreteOrderedGroupSpec


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
