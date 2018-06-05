module Main

import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory
import Proofs.DiscreteOrderTheory
import Proofs.Interval
import Instances.Notation
import Instances.TrustInteger
import Instances.ZZ
import Applications.Example
import Applications.ExactReal.Carry

%default total

testAbsoluteValue : Integer -> Integer
testAbsoluteValue x = fst $
  absoluteValue (orderedGroup integerDiscreteOrderedGroup) x

testAbsoluteValueZZ : ZZ -> ZZ
testAbsoluteValueZZ x = fst $ absoluteValue zzOrderedGroup x

testSeparation : Integer -> Integer -> String
testSeparation a b = show $ separate integerDiscreteOrderedGroup a b


partition3 : (x : Integer) -> .Between IntegerLeq x (a,b) ->
  Integer -> Integer -> String
partition3 x axb p q = show $
  decidePartition3 integerDiscreteOrderedGroup p q x axb


testPartition3 : Integer -> Integer -> Integer -> Integer -> Integer -> String
testPartition3 a p q b x =
  case decideBetween {leq = IntegerLeq} x a b of
    Yes axb => partition3 x axb p q
    No _ => "Error"


testCarry : Integer -> String
testCarry x =
  case decideBetween {leq = IntegerLeq} x (-18) 18 of
    Yes inRange => show $ value $
      computeCarry integerDiscreteOrderedGroup 9 x (CheckIntegerLeq Oh) inRange
    No _ => "Error"


testCarryZZ : ZZ -> String
testCarryZZ x =
  case decideBetween {leq = LTEZ} x (-18) 18 of
    Yes inRange => show $ value $
      computeCarry zzDiscreteOrderedGroup 9 x bound inRange
    No _ => "Error"
  where
    bound : LTEZ 1 8
    bound = LtePosPos (LTESucc LTEZero)

main : IO ()
main = do printLn $ map (testPartition3 0 3 7 10) [(-1)..11]
          printLn $ map testAbsoluteValue [(-5)..5]   
          printLn $ map testAbsoluteValueZZ (map fromInteger [(-10)..10])   
          printLn $ map testCarry [(-20)..20]
          printLn $ map testCarryZZ (map fromInteger [(-21)..21])

test1 : testCarryZZ (-15) = testCarry (-15)
test1 = Refl

test2 : testCarryZZ 12 = "(P, 2)"
test2 = Refl
