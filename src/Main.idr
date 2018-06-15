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
    Yes inRange => show $ result $
      computeCarry integerDiscreteOrderedGroup 9 (CheckIntegerLeq Oh) x inRange
    No _ => "Error"

testCarryZZ : ZZ -> String
testCarryZZ x =
  case decideBetween {leq = LTEZ} (-18) 18 x of
    Yes inRange => show $ result $
      computeCarry zzDiscreteOrderedGroup 9 bound x inRange
    No _ => "Error"
  where
    bound : LTEZ 1 8
    bound = LtePosPos (LTESucc LTEZero)

integerDigits : Vect n Integer -> Maybe (Vect n (Digit IntegerLeq Ng 9))
integerDigits = maybeDigits {leq = IntegerLeq} Ng 9

testAddition : Vect n (Digit IntegerLeq Ng 9) -> Vect n (Digit IntegerLeq Ng 9) -> Vect n (Digit IntegerLeq Ng 9)
testAddition = addition integerDiscreteOrderedGroup 9 (CheckIntegerLeq Oh)

main : IO ()
main = do printLn $ map testAbsoluteValue [(-5)..5]
          printLn $ map testAbsoluteValueZZ (map fromInteger [(-10)..10])
          printLn $ map testCarry [(-20)..20]
          printLn $ map testCarryZZ (map fromInteger [(-21)..21])
          printLn $ liftA2 testAddition
            (integerDigits [0,1,0,0,1]) (integerDigits [0,0,9,9,9])

||| compile time test
test1 : testCarryZZ (-15) = testCarry (-15)
test1 = Refl

||| compile time test
test2 : testCarryZZ 12 = "(P, 2)"
test2 = Refl
