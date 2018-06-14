module Main

import Data.Combinators

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
import Applications.ExactReal.Addition

%default total

testAbsoluteValue : Integer -> Integer
testAbsoluteValue x = fst $
  absoluteValue (orderedGroup integerDiscreteOrderedGroup) x

testAbsoluteValueZZ : ZZ -> ZZ
testAbsoluteValueZZ x = fst $ absoluteValue zzOrderedGroup x

testCarry : Integer -> String
testCarry x =
  case decideBetween {leq = IntegerLeq} (-18) 18 x of
    Yes inRange => show $ value $
      computeCarry integerDiscreteOrderedGroup 9 (CheckIntegerLeq Oh) x inRange
    No _ => "Error"

testCarryZZ : ZZ -> String
testCarryZZ x =
  case decideBetween {leq = LTEZ} (-18) 18 x of
    Yes inRange => show $ value $
      computeCarry zzDiscreteOrderedGroup 9 bound x inRange
    No _ => "Error"
  where
    bound : LTEZ 1 8
    bound = LtePosPos (LTESucc LTEZero)

integerDigits : Vect n Integer -> Maybe (Vect n (Digit IntegerLeq Ng 9))
integerDigits = maybeDigits {leq = IntegerLeq} Ng 9 

decimalAdd : OuterBinop (Maybe . Vect n . Digit IntegerLeq Ng) 9 9 18
decimalAdd = liftA2 (addPairwise integerPartiallyOrderedGroup)

test : Vect n Integer -> Maybe (Vect n Integer)
test xs = liftA (map fst) (reflex decimalAdd (integerDigits xs))

main : IO ()
main = do printLn $ map testAbsoluteValue [(-5)..5]   
          printLn $ map testAbsoluteValueZZ (map fromInteger [(-10)..10])   
          printLn $ map testCarry [(-20)..20]
          printLn $ map testCarryZZ (map fromInteger [(-21)..21])
          printLn $ test [-2,4,1,4,-9,0,5]

||| compile time test
test1 : testCarryZZ (-15) = testCarry (-15)
test1 = Refl

||| compile time test
test2 : testCarryZZ 12 = "(P, 2)"
test2 = Refl
